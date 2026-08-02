import os
import requests
import random
import time
import argparse
import json
import hashlib
import fcntl
from datetime import datetime, timezone
from itertools import permutations, islice
import math
import asyncio
from eth_account import Account
from mnemonic import Mnemonic
from termcolor import colored
from bip_utils import Bip39SeedGenerator, Bip44, Bip44Coins, Bip44Changes
# BeautifulSoup and re are kept for EVM scraping, but no longer used for Tron
from bs4 import BeautifulSoup
import re

# Optional libraries, check if installed
try:
    from bitcoinlib.keys import Key
except ImportError:
    print(colored("Warning: bitcoinlib Library Not installed. Bitcoin-Function is not available. BTC address Could not be generated..", "red"))
    Key = None

try:
    from tronpy import Tron
    from tronpy.keys import PrivateKey as TronPrivateKey
except ImportError:
    print(colored("Warning: tronpy library Not is installed. Tron-Function is not available.", "yellow"))
    Tron = None
    TronPrivateKey = None

# --- 1. Configuration ---
# !!! ATTENTION !!!
# WORD_POOL must contain real words from the BIP-39 English wordlist (they are —
# derive_addresses() validates every permutation with bip_utils' real Bip39SeedGenerator,
# which enforces the actual BIP-39 checksum). What makes this different from normal
# wallet recovery is the search space: instead of the full 2048-word dictionary, only
# permutations of these exact 12 words are tried — meant for the case where you know
# your words but forgot their order. Only a tiny fraction of orderings will have a
# valid checksum, and finding a *funded* wallet this way (i.e. guessing someone else's
# mnemonic) is still practically impossible — this is for recovering your own phrase.
#
# These two constants are only used to seed WORD_POOLS_FILE the first time it's
# created. After that, the actual queue of pools to work through lives in that
# file — see load_word_pools() below — and these constants are no longer read.
WORD_POOL = [
"unable", "belt", "resource", "zoo", "oil", "annual", "height", "adult", "walnut", "junior", "chuckle", "unveil"




     # Specify your 12 (or more) desired words here.
]
MNEMONIC_LENGTH = 12

# Infura Project ID - No longer used for EVM balance checks, but remains in RPC URLs
INFURA_PROJECT_ID = "e4390055418a474a88ea23824351018c"

COINGECKO_API_BASE = "https://api.coingecko.com/api/v3"

MAX_ATTEMPTS_PER_RUN = 50000
MIN_BALANCE_USD_THRESHOLD = 0.0001

# Cross-run, cross-worker progress tracking for word pools. Lets you see how much
# of a pool's permutation space has been covered so far, and (combined with
# WORD_POOLS_FILE below) lets the scanner auto-advance to the next pool once the
# current one is fully exhausted.
STATE_FILE = "state.json"

# How often (in attempts) a running worker writes its in-progress attempt count
# to state.json, so you can see live progress mid-slice instead of only once the
# whole MAX_ATTEMPTS_PER_RUN-sized slice finishes.
CHECKPOINT_INTERVAL_ATTEMPTS = 200

# Queue of word pools to work through, in order. Auto-created (seeded from
# WORD_POOL/MNEMONIC_LENGTH above) the first time the scanner runs if it doesn't
# exist yet. To queue up more pools, add entries shaped like:
#   {"words": ["word1", "word2", ...], "mnemonic_length": 12}
# to the JSON list in this file. mnemonic_length must be one of 12/15/18/21/24
# and "words" must contain at least that many entries.
WORD_POOLS_FILE = "word_pools.json"

# Network Configurations - API Keys removed from EVM scanners
NETWORK_CONFIGS = {
    "Ethereum": {
        "rpc_url": f"https://mainnet.infura.io/v3/{INFURA_PROJECT_ID}",
        "chain_id": 1,
        "is_poa": False,
        "native_symbol": "ETH",
        "coingecko_id": "ethereum",
        "explorer_url": "https://etherscan.io/address/", # Base URL for scraping
        "bip44_coin": Bip44Coins.ETHEREUM,
        "erc20_tokens": {
            "USDT (ERC-20)": {"address": "0xdAC17F958D2ee523a2206206994597C13D831ec7", "decimals": 6, "coingecko_id": "tether"},
            "USDC (ERC-20)": {"address": "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48", "decimals": 6, "coingecko_id": "usd-coin"},
        }
    },
    "Bitcoin": {
        "native_symbol": "BTC",
        "coingecko_id": "bitcoin",
        # Corrected Blockstream.info API base URL
        "explorer_api": "https://blockstream.info/api/address/",
        "bip44_coin": Bip44Coins.BITCOIN,
    },
    "Solana": {
        "native_symbol": "SOL",
        "coingecko_id": "solana",
        "explorer_api": "https://api.mainnet-beta.solana.com",
        "derivation_path_sol": "m/44'/501'/0'/0'",
        "bip44_coin": Bip44Coins.SOLANA,
    },
    "Tron": {
        "native_symbol": "TRX",
        "coingecko_id": "tron",
        "explorer_api": "https://apilist.tronscan.org/api/account", # Correct API for balance and transactions (uses query param ?address=)
        "explorer_url": "https://tronscan.org/#/address/", # Base URL for direct linking (not used for scraping anymore in this code)
        "transactions_api": "https://apilist.tronscan.org/api/transaction", # Still here for completeness, though account API gives total txs
        "bip44_coin": Bip44Coins.TRON,
        "trc20_tokens": {
            "USDT (TRC-20)": {"address": "TR7NHqjeKQxGTCi8qT8fcTfEPYptx2gCz", "decimals": 6, "coingecko_id": "tether"}
        }
    }
}

# --- 2. Helper Functions ---

def _pool_fingerprint(word_pool: list, mnemonic_length: int, max_attempts_per_run: int) -> str:
    """Identifies a (word_pool, mnemonic_length, max_attempts_per_run) combo.
    Two different word pools (or a changed mnemonic length / batch size) always
    get separate, non-mixing progress entries in state.json."""
    raw = json.dumps([word_pool, mnemonic_length, max_attempts_per_run])
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def mark_worker_slice_complete(worker_id: int, word_pool: list, mnemonic_length: int, max_attempts_per_run: int) -> dict:
    """
    Records that `worker_id` finished its slice of the permutation space for the
    given word pool, then returns the combined progress across every worker
    that has ever completed a slice for this exact pool (deduplicated, so
    re-running the same --worker-id twice doesn't double count).

    Uses flock so concurrent terminals updating state.json at the same time
    don't clobber each other's writes.
    """
    state_path = os.path.join(os.getcwd(), STATE_FILE)
    fingerprint = _pool_fingerprint(word_pool, mnemonic_length, max_attempts_per_run)
    total_permutations = math.perm(len(word_pool), mnemonic_length)

    with open(state_path, "a+", encoding="utf-8") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            f.seek(0)
            raw = f.read()
            state = json.loads(raw) if raw.strip() else {"pools": {}}

            pool_entry = state["pools"].setdefault(fingerprint, {
                "word_pool": word_pool,
                "mnemonic_length": mnemonic_length,
                "max_attempts_per_run": max_attempts_per_run,
                "total_permutations": total_permutations,
                "completed_worker_ids": [],
                "in_progress": {},
            })

            if worker_id not in pool_entry["completed_worker_ids"]:
                pool_entry["completed_worker_ids"].append(worker_id)
                pool_entry["completed_worker_ids"].sort()

            # This worker-id is done, so it's no longer "in progress".
            pool_entry.setdefault("in_progress", {}).pop(str(worker_id), None)

            f.seek(0)
            f.truncate()
            f.write(json.dumps(state, indent=2))
            f.flush()
            os.fsync(f.fileno())
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)

    return pool_entry


def checkpoint_worker_progress(worker_id: int, word_pool: list, mnemonic_length: int,
                                max_attempts_per_run: int, attempts_made: int) -> None:
    """
    Records how far `worker_id` has gotten through its current slice, without
    marking the slice as complete. Called periodically (every
    CHECKPOINT_INTERVAL_ATTEMPTS attempts) during the run so state.json reflects
    live progress instead of only updating once the whole slice finishes.
    """
    state_path = os.path.join(os.getcwd(), STATE_FILE)
    fingerprint = _pool_fingerprint(word_pool, mnemonic_length, max_attempts_per_run)
    total_permutations = math.perm(len(word_pool), mnemonic_length)

    with open(state_path, "a+", encoding="utf-8") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            f.seek(0)
            raw = f.read()
            state = json.loads(raw) if raw.strip() else {"pools": {}}

            pool_entry = state["pools"].setdefault(fingerprint, {
                "word_pool": word_pool,
                "mnemonic_length": mnemonic_length,
                "max_attempts_per_run": max_attempts_per_run,
                "total_permutations": total_permutations,
                "completed_worker_ids": [],
                "in_progress": {},
            })

            pool_entry.setdefault("in_progress", {})[str(worker_id)] = {
                "attempts_made": attempts_made,
                "max_attempts_per_run": max_attempts_per_run,
                "pid": os.getpid(),
                "updated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            }

            f.seek(0)
            f.truncate()
            f.write(json.dumps(state, indent=2))
            f.flush()
            os.fsync(f.fileno())
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def _read_state() -> dict:
    """Read-only, shared-lock read of state.json (empty skeleton if it doesn't exist yet)."""
    state_path = os.path.join(os.getcwd(), STATE_FILE)
    if not os.path.exists(state_path):
        return {"pools": {}}
    with open(state_path, "r", encoding="utf-8") as f:
        fcntl.flock(f, fcntl.LOCK_SH)
        try:
            raw = f.read()
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)
    return json.loads(raw) if raw.strip() else {"pools": {}}


def _is_pool_exhausted(state: dict, word_pool: list, mnemonic_length: int, max_attempts_per_run: int) -> bool:
    fingerprint = _pool_fingerprint(word_pool, mnemonic_length, max_attempts_per_run)
    pool_entry = state.get("pools", {}).get(fingerprint)
    total_permutations = math.perm(len(word_pool), mnemonic_length)
    total_slices_needed = math.ceil(total_permutations / max_attempts_per_run)
    completed = len(pool_entry["completed_worker_ids"]) if pool_entry else 0
    return completed >= total_slices_needed


def load_word_pools() -> list:
    """
    Loads the queue of word pools to work through, in order, from WORD_POOLS_FILE.
    Auto-created on first run, seeded from the WORD_POOL/MNEMONIC_LENGTH constants
    above, so existing setups keep working with zero config changes. Add more
    {"words": [...], "mnemonic_length": N} entries to the file to queue up
    further pools — select_active_pool() below picks the first one that isn't
    fully checked yet.
    """
    queue_path = os.path.join(os.getcwd(), WORD_POOLS_FILE)

    if not os.path.exists(queue_path):
        seed = [{"words": WORD_POOL, "mnemonic_length": MNEMONIC_LENGTH}]
        with open(queue_path, "w", encoding="utf-8") as f:
            json.dump(seed, f, indent=2)
        return seed

    with open(queue_path, "r", encoding="utf-8") as f:
        raw_pools = json.load(f)

    valid_pools = []
    for i, entry in enumerate(raw_pools):
        words = entry.get("words", [])
        mnemonic_length = entry.get("mnemonic_length", MNEMONIC_LENGTH)
        if mnemonic_length not in (12, 15, 18, 21, 24):
            print(colored(f"[!] Skipping {WORD_POOLS_FILE} entry {i}: mnemonic_length must be one of 12/15/18/21/24 (got {mnemonic_length}).", "red"))
            continue
        if len(words) < mnemonic_length:
            print(colored(f"[!] Skipping {WORD_POOLS_FILE} entry {i}: only {len(words)} words, needs at least {mnemonic_length}.", "red"))
            continue
        valid_pools.append({"words": words, "mnemonic_length": mnemonic_length})

    return valid_pools


def select_active_pool(pools: list):
    """Returns (index, pool) for the first pool in the queue that isn't fully
    exhausted yet, or None if every pool in the queue has been completely checked."""
    state = _read_state()
    for i, pool in enumerate(pools):
        if not _is_pool_exhausted(state, pool["words"], pool["mnemonic_length"], MAX_ATTEMPTS_PER_RUN):
            return i, pool
    return None


def derive_addresses(mnemonic_phrase: str, passphrase: str = "") -> dict:
    """
    Derives addresses for various cryptocurrencies from a single mnemonic phrase using bip_utils.
    Returns a dictionary of addresses or an "Error" key with a description if seed derivation fails.
    This function acts as the BIP-39 validation point.
    """
    addresses = {}
    try:
        seed_generator = Bip39SeedGenerator(mnemonic_phrase)
        seed_bytes = seed_generator.Generate(passphrase)
    except Exception as e:
        return {"Error": f"Mnemonic seed generation failed (BIP-39 validation error): {e}"}

    try:
        # EVM (Ethereum, Polygon, BNB Smart Chain use the same derivation path)
        bip44_eth = Bip44.FromSeed(seed_bytes, Bip44Coins.ETHEREUM)
        eth_account = bip44_eth.Purpose().Coin().Account(0).Change(Bip44Changes.CHAIN_EXT).AddressIndex(0)
        addresses["EVM"] = eth_account.PublicKey().ToAddress()
    except Exception as e:
        addresses["EVM"] = f"Error deriving EVM address: {e}"

    if Key: # Bitcoinlib dependency check - BTC
        try:
            bip44_btc = Bip44.FromSeed(seed_bytes, Bip44Coins.BITCOIN)
            btc_account = bip44_btc.Purpose().Coin().Account(0).Change(Bip44Changes.CHAIN_EXT).AddressIndex(0)
            addresses["Bitcoin"] = btc_account.PublicKey().ToAddress()
        except Exception as e:
            addresses["Bitcoin"] = f"Error deriving Bitcoin address: {e}"
    else:
        addresses["Bitcoin"] = colored("bitcoinlib library Not is installed, Bitcoin BTC address Could not be generated.", "red")


    try:
        bip44_sol = Bip44.FromSeed(seed_bytes, Bip44Coins.SOLANA)
        sol_account = bip44_sol.Purpose().Coin().Account(0).Change(Bip44Changes.CHAIN_EXT).AddressIndex(0)
        addresses["Solana"] = sol_account.PublicKey().ToAddress()
    except Exception as e:
        addresses["Solana"] = f"Error deriving Solana address: {e}"

    if TronPrivateKey: # Tronpy dependency check
        try:
            bip44_tron = Bip44.FromSeed(seed_bytes, Bip44Coins.TRON)
            tron_account_obj = bip44_tron.Purpose().Coin().Account(0).Change(Bip44Changes.CHAIN_EXT).AddressIndex(0)

            evm_private_key_bytes = tron_account_obj.PrivateKey().Raw().ToBytes()

            tron_private_key_obj = TronPrivateKey(evm_private_key_bytes)
            addresses["Tron"] = tron_private_key_obj.public_key.to_base58check_address() # Tron's base58 address
        except Exception as e:
            addresses["Tron"] = f"Error deriving Tron address: {e}"

    return addresses

# --- Web Scraping Function for EVM Chains ---
async def get_evm_balance_and_transactions_from_scrape(address, explorer_url, native_symbol):
    """
    Gets native coin balance and checks for transactions by scraping Etherscan-like sites.
    """
    url = f"{explorer_url}{address}"
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36"}

    try:
        response = await asyncio.to_thread(requests.get, url, headers=headers, timeout=15)
        response.raise_for_status()
        soup = BeautifulSoup(response.text, "html.parser")

        native_balance = 0.0
        usd_balance_from_scrape = 0.0
        has_transactions = False

        eth_value_header = soup.find("h4", string=lambda text: text and f"{native_symbol} Value" in text.strip())
        if not eth_value_header:
            eth_value_header = soup.find("h4", string=lambda text: text and "Eth Value" in text.strip())

        if eth_value_header:
            value_div = eth_value_header.find_parent("div")
            if value_div:
                eth_value_text = value_div.text.strip()
                match_usd = re.search(r"\$\d+(\.\d+)?", eth_value_text)
                if match_usd:
                    try:
                        usd_balance_from_scrape = float(match_usd.group().replace('$', ''))
                    except ValueError:
                        pass

                native_balance_span = value_div.find("span", class_="text-dark", string=lambda text: text and native_symbol in text)
                if not native_balance_span:
                    native_balance_span = soup.find("div", class_="row", string=lambda text: text and "Ether Balance" in text.strip())
                    if native_balance_span:
                        native_balance_span = native_balance_span.find("span", class_="text-dark")

                if native_balance_span:
                    balance_text_native = native_balance_span.text.strip().replace(native_symbol, '').replace(',', '')
                    match_native = re.search(r"(\d+(\.\d+)?)", balance_text_native)
                    if match_native:
                        try:
                            native_balance = float(match_native.group(1))
                        except ValueError:
                            pass

        tx_count_span = soup.find("span", class_="d-block d-md-inline-block text-dark fw-medium",
                                   string=lambda text: text and "Transaction Count" in text)
        if tx_count_span:
            tx_count_text = tx_count_span.text.strip().replace(" Transaction Count", "").replace(",", "")
            try:
                tx_count = int(tx_count_text)
                if tx_count > 0:
                    has_transactions = True
            except ValueError:
                pass

        return native_balance, usd_balance_from_scrape, has_transactions, None
    except requests.exceptions.RequestException as e:
        return 0.0, 0.0, False, f"HTTP request error: {e}"
    except Exception as e:
        return 0.0, 0.0, False, f"Scraping error: {e}"

# --- API Based Functions (for non-EVM chains and Coingecko) ---
async def get_crypto_prices_async(coin_ids_list):
    """
    Asynchronously fetches cryptocurrency prices from CoinGecko.
    """
    try:
        ids_str = ",".join(coin_ids_list)
        response = await asyncio.to_thread(requests.get, f"{COINGECKO_API_BASE}/simple/price?ids={ids_str}&vs_currencies=usd", timeout=10)
        response.raise_for_status()
        data = response.json()
        prices = {coin_id: data[coin_id]['usd'] for coin_id in data if 'usd' in data[coin_id]}
        return prices, None
    except requests.exceptions.RequestException as e:
        return None, f"Error getting prices from CoinGecko: {e}"
    except Exception as e:
        return None, f"Unexpected error getting prices: {e}"

async def get_btc_balance_and_transactions(btc_address):
    """
    Asynchronously fetches Bitcoin balance and transaction status from Blockstream.info API.
    Parses JSON response for `chain_stats.funded_txo_sum`, `chain_stats.spent_txo_sum`, and `chain_stats.tx_count`.
    """
    explorer_url = f"{NETWORK_CONFIGS['Bitcoin']['explorer_api']}{btc_address}"

    try:
        response = await asyncio.to_thread(requests.get, explorer_url, timeout=10)
        response.raise_for_status() # Raise for HTTP errors
        data = response.json()

        balance_satoshi = 0
        has_transactions = False

        if 'chain_stats' in data:
            funded_sum = data['chain_stats'].get('funded_txo_sum', 0)
            spent_sum = data['chain_stats'].get('spent_txo_sum', 0)
            balance_satoshi = funded_sum - spent_sum

            tx_count = data['chain_stats'].get('tx_count', 0)
            if tx_count > 0:
                has_transactions = True

        balance_btc = balance_satoshi / (10**8) # Convert satoshi to BTC

        return balance_btc, has_transactions, None
    except requests.exceptions.RequestException as e:
        return None, None, f"HTTP request error for Blockstream.info: {e}"
    except (ValueError, KeyError) as e:
        return None, None, f"Blockstream.info-From data parsing error: {e}"
    except Exception as e:
        return None, None, f"Unexpected error while retrieving BTC balance/transactions: {e}"

async def get_sol_balance_and_transactions(sol_address):
    """
    Asynchronously fetches Solana balance and transaction status from Solana RPC.
    """
    try:
        headers = {"Content-Type": "application/json"}
        payload_balance = {
            "jsonrpc": "2.0", "id": 1, "method": "getBalance", "params": [sol_address]
        }
        payload_tx = {
            "jsonrpc": "2.0", "id": 1, "method": "getConfirmedSignaturesForAddress2",
            "params": [sol_address, {"limit": 1}]
        }

        balance_response = await asyncio.to_thread(requests.post, NETWORK_CONFIGS['Solana']['explorer_api'], headers=headers, json=payload_balance, timeout=10)
        balance_response.raise_for_status()
        balance_data = balance_response.json()

        tx_response = await asyncio.to_thread(requests.post, NETWORK_CONFIGS['Solana']['explorer_api'], headers=headers, json=payload_tx, timeout=10)
        tx_response.raise_for_status()
        tx_data = tx_response.json()

        balance_sol = 0
        if 'result' in balance_data and 'value' in balance_data['result']:
            balance_lamports = balance_data['result']['value']
            balance_sol = balance_lamports / (10**9)

        has_transactions = False
        if 'result' in tx_data and tx_data['result']:
            has_transactions = len(tx_data['result']) > 0

        return balance_sol, has_transactions, None
    except requests.exceptions.RequestException as e:
        return None, None, f"Error getting SOL balance/transactions from Solana RPC: {e}"
    except Exception as e:
        return None, None, f"Unexpected error getting SOL balance/transactions: {e}"


# --- Updated TRX Balance and Transaction check function ---
async def get_trx_balance_and_tokens_and_transactions(trx_address):
    """
    Asynchronously fetches Tron balance and TRC-20 token balances from Tronscan API (public endpoint).
    It does NOT perform web scraping for TRX or USD values from tronscan.org/#/address/.
    USD value for TRX is calculated using CoinGecko price.
    """
    # Corrected API URL as per user's confirmation: https://apilist.tronscan.org/api/account?address={address}
    api_url = f"{NETWORK_CONFIGS['Tron']['explorer_api']}?address={trx_address}"

    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36"
    }

    balance_trx_api = 0.0 # TRX balance from API
    has_transactions = False
    token_balances = {} # TRC-20 token balances from API
    error_message = None

    try:
        # --- API based data retrieval for TRX and TRC-20 balances and transaction count ---
        api_response = await asyncio.to_thread(requests.get, api_url, headers=headers, timeout=10)
        api_response.raise_for_status() # Raise for HTTP errors
        api_data = api_response.json()

        if 'balance' in api_data:
            balance_sun = api_data['balance']
            balance_trx_api = balance_sun / (10**6) # Convert SUN to TRX

        if 'totalTransactionCount' in api_data and api_data['totalTransactionCount'] > 0:
            has_transactions = True

        if 'tokenBalances' in api_data:
            for token_info in api_data['tokenBalances']:
                for token_symbol, config in NETWORK_CONFIGS['Tron']['trc20_tokens'].items():
                    if (token_info.get('tokenId') and token_info['tokenId'].upper() == config['address'].upper()) or \
                       (token_info.get('tokenAbbr') and token_info['tokenAbbr'].upper() == token_symbol.split(' ')[0].upper()):
                        try:
                            raw_balance = int(token_info['balance'])
                            token_balances[token_symbol] = raw_balance / (10 ** config['decimals'])
                        except (ValueError, KeyError):
                            pass

    except requests.exceptions.RequestException as e:
        error_message = f"HTTP request error for Tron API: {e}"
    except Exception as e:
        error_message = f"Tron API data retrieval error: {e}"

    # We now only return data from the API, no scraped values
    return balance_trx_api, token_balances, has_transactions, error_message

# --- 3. Main Logic ---
def parse_args():
    parser = argparse.ArgumentParser(
        description="Multi-chain wallet permutation/balance scanner. "
                     "Run several copies in parallel (one per terminal) by giving each "
                     "a distinct --worker-id so they check disjoint permutation slices."
    )
    parser.add_argument(
        "--worker-id", type=int, default=0,
        help="0-indexed id of this worker (default: 0).",
    )
    parser.add_argument(
        "--num-workers", type=int, default=1,
        help="Total number of workers running in parallel across all terminals (default: 1).",
    )
    args = parser.parse_args()
    if not (0 <= args.worker_id < args.num_workers):
        parser.error(f"--worker-id must be in [0, {args.num_workers}) (got {args.worker_id}).")
    return args


async def main():
    args = parse_args()
    worker_id = args.worker_id
    num_workers = args.num_workers

    print(colored("--- Multi-Chain Wallet Balance Scanner (Custom Word Permutations) ---", "cyan"))

    pools = load_word_pools()
    selection = select_active_pool(pools)
    if selection is None:
        print(colored(
            f"\n[+] Every word pool in {WORD_POOLS_FILE} has been fully checked. "
            f"Add another {{\"words\": [...], \"mnemonic_length\": N}} entry to that file to keep going.",
            "green",
        ))
        return

    pool_index, active_pool = selection
    word_pool = active_pool["words"]
    mnemonic_length = active_pool["mnemonic_length"]
    print(colored(
        f"[INFO] Word pool {pool_index + 1}/{len(pools)} from {WORD_POOLS_FILE} is active "
        f"({len(word_pool)} words, mnemonic length {mnemonic_length}).",
        "cyan",
    ))

    # Each worker gets its own contiguous, non-overlapping slice of the
    # permutation space so running N of these in parallel actually covers
    # N times as much ground instead of N processes redoing the same work.
    slice_start = worker_id * MAX_ATTEMPTS_PER_RUN
    slice_end = slice_start + MAX_ATTEMPTS_PER_RUN
    print(colored(f"[INFO] Worker {worker_id}/{num_workers} — covering permutation indices [{slice_start:,}, {slice_end:,})", "cyan"))

    print(colored("!!! Tron (TRX) balances and transactions are verified via the Tronscan API (public endpoint). !!!", "yellow"))
    print(colored("!!! Bitcoin (BTC) balances and transactions are verified via the Blockstream.info API. !!!", "yellow"))


    print(colored("-" * 60, "white"))

    coin_ids_for_prices = set()
    for net_config in NETWORK_CONFIGS.values():
        if "coingecko_id" in net_config:
            coin_ids_for_prices.add(net_config["coingecko_id"])
        if "erc20_tokens" in net_config:
            for token_info in net_config["erc20_tokens"].values():
                coin_ids_for_prices.add(token_info["coingecko_id"])
        if "trc20_tokens" in net_config:
            for token_info in net_config["trc20_tokens"].values():
                coin_ids_for_prices.add(token_info["coingecko_id"])

    prices, price_error = await get_crypto_prices_async(tuple(coin_ids_for_prices))
    if price_error:
        print(colored(f"[!] Error getting price: {price_error}. USD balance will not be displayed.", "red"))
        prices = {}
    else:
        print(colored("\n[+] Current cryptocurrency prices (USD):", "green"))
        for coin_id, price in prices.items():
            print(f"  - {coin_id.ljust(15)}: ${price:.4f}")
        print(colored("-" * 60, "white"))

    valid_mnemonics_count = 0
    invalid_mnemonics_count = 0
    attempts_made = 0
    wallets_with_balance_count = 0

    print(colored(f"\n[+] Start generating permutations and checking your words ({MAX_ATTEMPTS_PER_RUN} With a limit of attempts)...", "cyan"))
    print(colored("-" * 60, "white"))

    total_permutations = math.perm(len(word_pool), mnemonic_length)
    print(colored(f"[INFO] Total number of possible combinations ({mnemonic_length} Word from {len(word_pool)}): {total_permutations:,}", "blue"))

    for i, perm_words in enumerate(islice(permutations(word_pool, mnemonic_length), slice_start, slice_end)):
        attempts_made += 1
        current_secret_phrase = " ".join(perm_words)

        derived_addresses = derive_addresses(current_secret_phrase)

        if "Error" in derived_addresses:
            invalid_mnemonics_count += 1
            print(colored(f"[-]Invalid mnemonic (BIP-39 check failed) {attempts_made}/{MAX_ATTEMPTS_PER_RUN}: {current_secret_phrase}", "blue"))
            continue

        valid_mnemonics_count += 1
        print(colored(f"\n[+] Valid mnemonics (BIP-39 compliant) {attempts_made}/{MAX_ATTEMPTS_PER_RUN}: {current_secret_phrase}", "light_yellow"))
        for chain, addr in derived_addresses.items():
            # Special handling for error message from derive_addresses for Bitcoin
            if "Error" in str(addr) or "Not installed" in str(addr):
                print(colored(f"    {chain} address: {addr}", "red"))
            else:
                print(colored(f"    {chain} address: {addr}", "light_yellow"))


        all_found_balances_usd = []
        has_any_transactions = False

        # --- Checking balances and transaction history on EVM-compatible networks (using WEB SCRAPING) ---
        for network_name in ["Ethereum"]: # Only for Ethereum
            config = NETWORK_CONFIGS[network_name]
            # Ensure BTC address was successfully derived before checking balance
            if network_name == "Bitcoin" and ("Error" in derived_addresses.get("Bitcoin", "") or "Not installed" in derived_addresses.get("Bitcoin", "")):
                # Skip checking if bitcoinlib is not installed or derivation failed
                continue

            if "EVM" in derived_addresses and "Error" not in derived_addresses["EVM"]:
                evm_address = derived_addresses["EVM"]
                print(colored(f"  [+] Checking {network_name} ...", "cyan"))

                native_balance, usd_balance_from_scrape, has_tx, scrape_error = await get_evm_balance_and_transactions_from_scrape(
                    evm_address, config["explorer_url"], config["native_symbol"]
                )

                if scrape_error:
                    print(colored(f"    [!]Error checking {network_name}: {scrape_error}", "red"))
                else:
                    if usd_balance_from_scrape > 0:
                        print(colored(f"    ✅ The wallet has a balance.: ${usd_balance_from_scrape:.2f} ((abstract meaning)", "green"))
                        all_found_balances_usd.append(usd_balance_from_scrape)
                    elif native_balance > 0:
                        print(colored(f"    [+] {config['native_symbol']} Balance: {native_balance:.6f}", "white"))
                        if config["coingecko_id"] in prices and float(native_balance) > 0:
                            usd_value = float(native_balance) * prices[config["coingecko_id"]]
                            all_found_balances_usd.append(usd_value)
                            print(colored(f"      ~ Approximately ${usd_value:.2f} (calculated using CoinGecko price)", "yellow"))
                    else:
                        print(colored(f"    ❌ Not Balance 0 ({config['native_symbol']})", "red"))

                    if has_tx:
                        print(colored(f"    [+] Transactions found {network_name}!", "green"))
                        has_any_transactions = True
                    else:
                        print(colored(f"    [-] No transactions found on {network_name}.", "red"))

        # --- Checking balances and transaction history on non-EVM networks (using APIs) ---
        # Changed to use Blockstream.info API which handles both balance and transaction count from one endpoint
        if "Bitcoin" in derived_addresses and "Error" not in derived_addresses["Bitcoin"] and "Not installed" not in derived_addresses["Bitcoin"]:
            btc_address = derived_addresses["Bitcoin"]
            print(colored(f"  [+] Checking Bitcoin (BTC)... (using Blockstream.info API)", "cyan"))
            btc_balance, has_btc_transactions, btc_error = await get_btc_balance_and_transactions(btc_address)
            if btc_balance is not None:
                print(colored(f"    [+] BTC Balance: {btc_balance:.8f}", "white"))
                if NETWORK_CONFIGS["Bitcoin"]["coingecko_id"] in prices and float(btc_balance) > 0:
                    usd_value = float(btc_balance) * prices[NETWORK_CONFIGS["Bitcoin"]["coingecko_id"]]
                    all_found_balances_usd.append(usd_value)
                    print(colored(f"      ~About ${usd_value:.2f}", "yellow"))
                if has_btc_transactions:
                    print(colored(f"    [+] Transactions found on Bitcoin!", "green"))
                    has_any_transactions = True
                else:
                    print(colored(f"    [-] No transactions found on Bitcoin.", "red"))
            elif btc_error:
                print(colored(f"    [!] BTC balance/transaction verification error: {btc_error}", "red"))

        if "Solana" in derived_addresses and "Error" not in derived_addresses["Solana"]:
            sol_address = derived_addresses["Solana"]
            print(colored(f"  [+] Solana (SOL) Check...", "cyan"))
            sol_balance, has_sol_transactions, sol_error = await get_sol_balance_and_transactions(sol_address)
            if sol_balance is not None:
                print(colored(f"    [+] SOL Balance: {sol_balance:.8f}", "white"))
                if NETWORK_CONFIGS["Solana"]["coingecko_id"] in prices and float(sol_balance) > 0:
                    usd_value = float(sol_balance) * prices[NETWORK_CONFIGS["Solana"]["coingecko_id"]]
                    all_found_balances_usd.append(usd_value)
                    print(colored(f"      ~ about ${usd_value:.2f}", "yellow"))
                if has_sol_transactions:
                    print(colored(f"    [+] Transactions found on Solana!", "green"))
                    has_any_transactions = True
                else:
                    print(colored(f"    [-] No transactions found on Solana.", "red"))
            elif sol_error:
                print(colored(f"    [!] SOL balance/transaction check error: {sol_error}", "red"))

        if "Tron" in derived_addresses and "Error" not in derived_addresses["Tron"]:
            trx_address = derived_addresses["Tron"]
            # Call the updated get_trx_balance_and_tokens_and_transactions using only API
            print(colored(f"  [+] Checking Tron (TRX)... (using Tronscan API)", "cyan"))
            trx_balance_api, trc20_balances_api, has_trx_transactions, trx_error = await get_trx_balance_and_tokens_and_transactions(trx_address)

            if trx_error:
                print(colored(f"    [!] TRX balance/token/transaction verification error: {trx_error}", "red"))
            elif trx_balance_api is not None: # Check if API call was successful
                if trx_balance_api > 0: # If API TRX balance is found
                    print(colored(f"    [+] TRX Balance (API): {trx_balance_api:.6f}", "white"))
                    if NETWORK_CONFIGS["Tron"]["coingecko_id"] in prices and float(trx_balance_api) > 0:
                        usd_value = float(trx_balance_api) * prices[NETWORK_CONFIGS["Tron"]["coingecko_id"]]
                        all_found_balances_usd.append(usd_value)
                        print(colored(f"     ~ about ${usd_value:.2f} (calculated with CoinGecko price)", "yellow"))
                else:
                    print(colored(f"    ❌ Not Balance 0 (TRX)", "red"))

                # Report TRC-20 balances from API
                for token_symbol, balance in trc20_balances_api.items():
                    if balance > 0: # Only print if token balance is greater than 0
                        print(colored(f"    [+] {token_symbol} Balance (Tron API): {balance:.6f}", "white"))
                        token_config = NETWORK_CONFIGS["Tron"]["trc20_tokens"].get(token_symbol)
                        if token_config and token_config["coingecko_id"] in prices and float(balance) > 0:
                            usd_value = float(balance) * prices[token_config["coingecko_id"]]
                            all_found_balances_usd.append(usd_value)
                            print(colored(f"      ~ About ${usd_value:.2f}", "yellow"))

                if has_trx_transactions:
                    print(colored(f"    [+] Transaction Found Tron!", "green"))
                    has_any_transactions = True
                else:
                    print(colored(f"    [-] Transaction not fount on Tron.", "red"))

        # --- Summarizing results and saving to file ---
        total_sum_usd = sum(all_found_balances_usd)
        print(colored(f"    [=] Estimated total cost (USD): ${total_sum_usd:.2f}", "light_green"))

        if total_sum_usd >= MIN_BALANCE_USD_THRESHOLD or has_any_transactions:
            wallets_with_balance_count += 1
            status_message = ""
            if total_sum_usd >= MIN_BALANCE_USD_THRESHOLD:
                status_message += f"Balance (> ${MIN_BALANCE_USD_THRESHOLD:.2f})"
            if has_any_transactions:
                if status_message:
                    status_message += " and "
                status_message += "Transactions"
            print(colored(f"    [+] wallet found {status_message}!", "green"))

            # Per-worker output file: running several workers in parallel must never
            # let two processes append to the same file, since each hit is written as
            # several separate lines and concurrent appends could interleave them.
            output_path = os.path.join(os.getcwd(), f"found_wallets_worker{worker_id}_pid{os.getpid()}.txt")
            lines = [f"Mnemonic: {current_secret_phrase}\n"]
            for chain, addr in derived_addresses.items():
                # Write only if it's a valid address or explicitly not an error message
                if "Error" not in str(addr) and "Not installed" not in str(addr):
                    lines.append(f"{chain} Address: {addr}\n")
                elif chain == "Bitcoin" and "Not installed" in str(addr):
                    lines.append(f"{chain} Address: {addr}\n") # Still write the warning to file if it occurs
            lines.append(f"Estimated Total Value (USD): ${total_sum_usd:.2f}\n")
            lines.append(f"Transactions Found: {'Yes' if has_any_transactions else 'No'}\n")
            lines.append("-" * 50 + "\n\n")
            with open(output_path, "a", encoding='utf-8') as f:
                f.write("".join(lines))
            print(colored(f"    [+] Information is save in {output_path}", "light_yellow"))
        else:
            print(colored("    ❌ Wallet not have balance and transaction not found.", "red"))

        # Displaying progress
        if attempts_made % 10 == 0 or attempts_made == MAX_ATTEMPTS_PER_RUN:
            print(colored(f"\n[INFO] checking {attempts_made:,} Mnemonic. Valid: {valid_mnemonics_count}, Wallets With balance/Transactions: {wallets_with_balance_count}, wrong (BIP-39 checking is not success): {invalid_mnemonics_count}", "cyan"))

        # Mid-slice checkpoint: lets `state.json` show live progress instead of
        # only updating once the entire MAX_ATTEMPTS_PER_RUN-sized slice finishes.
        if attempts_made % CHECKPOINT_INTERVAL_ATTEMPTS == 0:
            checkpoint_worker_progress(worker_id, word_pool, mnemonic_length, MAX_ATTEMPTS_PER_RUN, attempts_made)

        if attempts_made >= MAX_ATTEMPTS_PER_RUN:
            print(colored(f"\n[INFO] Max Limited success ({MAX_ATTEMPTS_PER_RUN}). Program Stoped.", "yellow"))
            break

        # Delay for web scraping/API calls to avoid rate limits
        time.sleep(0) # 1 second delay for each valid mnemonic check

    print(colored("\n--- Checking Finished ---", "cyan"))
    print(colored(f"Total Checking Mnemonic: {attempts_made}", "light_green"))
    print(colored(f"Found Valid Mnemonic ( BIP-39 Success): {valid_mnemonics_count}", "green"))
    print(colored(f"Found Wallets With Balance/Transactions: {wallets_with_balance_count}", "green"))
    print(colored(f"Wrong Mnemonic Phrase (BIP-39 Wrong Mnemonic): {invalid_mnemonics_count}", "red"))

    # Only credit this worker-id's slice as done if it actually ran to completion
    # (not interrupted partway) — a crashed/killed run should just get retried.
    if attempts_made >= MAX_ATTEMPTS_PER_RUN:
        pool_entry = mark_worker_slice_complete(worker_id, word_pool, mnemonic_length, MAX_ATTEMPTS_PER_RUN)
        total_permutations = pool_entry["total_permutations"]
        completed_slices = len(pool_entry["completed_worker_ids"])
        checked = min(completed_slices * MAX_ATTEMPTS_PER_RUN, total_permutations)
        percent = (checked / total_permutations) * 100
        total_slices_needed = math.ceil(total_permutations / MAX_ATTEMPTS_PER_RUN)

        print(colored(f"\n[STATE] {STATE_FILE} updated — worker-id {worker_id} marked complete for word pool {pool_index + 1}/{len(pools)}.", "cyan"))
        print(colored(
            f"[STATE] Combined progress for this pool: {checked:,} / {total_permutations:,} "
            f"({percent:.6f}%) across {completed_slices:,} / {total_slices_needed:,} worker-id slices.",
            "cyan",
        ))

        if checked >= total_permutations:
            print(colored(
                f"\n[+] Every permutation of word pool {pool_index + 1}/{len(pools)} has been checked. "
                f"The next run will auto-advance to the next unexhausted pool in {WORD_POOLS_FILE} (if any remain).",
                "green",
            ))
        else:
            remaining_slices = total_slices_needed - completed_slices
            print(colored(
                f"[STATE] {remaining_slices:,} more worker-id slices needed to fully exhaust this pool.",
                "yellow",
            ))

if __name__ == "__main__":
    asyncio.run(main())
