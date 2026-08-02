#!/usr/bin/env python3
"""
Mnemonic Converter
-------------------
Converts a BIP39 mnemonic seed phrase (+ optional passphrase) into
private keys and wallet addresses for a chosen coin and derivation path.

Requires: bip_utils
    pip install bip_utils

Examples:
    # Generate a fresh 12-word mnemonic and derive BTC (native segwit) addresses
    python3 mnemonic_converter.py --generate --coin btc --path-type segwit --count 5

    # Convert an existing mnemonic to ETH addresses
    python3 mnemonic_converter.py \\
        --mnemonic "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about" \\
        --coin eth --count 3

    # BTC legacy addresses with a BIP39 passphrase, custom account/change
    python3 mnemonic_converter.py --mnemonic "..." --coin btc --path-type legacy \\
        --passphrase "mysecret" --account 0 --change 0 --count 10
"""

import argparse
import sys

from bip_utils import (
    Bip39MnemonicGenerator,
    Bip39MnemonicValidator,
    Bip39SeedGenerator,
    Bip39WordsNum,
    Bip44,
    Bip44Coins,
    Bip49,
    Bip49Coins,
    Bip84,
    Bip84Coins,
    Bip86,
    Bip86Coins,
    Bip44Changes,
)

# ---------------------------------------------------------------------------
# Coin configuration
# ---------------------------------------------------------------------------
# For coins that support multiple BTC-like address formats, we map
# --path-type to the right BIP class + coin enum. Everything else just
# uses standard BIP44.

BTC_LIKE_PATH_TYPES = {
    "legacy": ("bip44", Bip44Coins.BITCOIN),          # P2PKH   - m/44'/0'/...
    "nested-segwit": ("bip49", Bip49Coins.BITCOIN),   # P2SH-P2WPKH - m/49'/0'/...
    "segwit": ("bip84", Bip84Coins.BITCOIN),          # P2WPKH  - m/84'/0'/...
    "taproot": ("bip86", Bip86Coins.BITCOIN),         # P2TR    - m/86'/0'/...
}

# Simple coins: name -> Bip44Coins enum (standard BIP44 derivation only)
BIP44_ONLY_COINS = {
    "eth": Bip44Coins.ETHEREUM,
    "etc": Bip44Coins.ETHEREUM_CLASSIC,
    "ltc": Bip44Coins.LITECOIN,
    "doge": Bip44Coins.DOGECOIN,
    "bch": Bip44Coins.BITCOIN_CASH,
    "bsv": Bip44Coins.BITCOIN_SV,
    "bnb": Bip44Coins.BINANCE_CHAIN,
    "bsc": Bip44Coins.BINANCE_SMART_CHAIN,
    "matic": Bip44Coins.POLYGON,
    "xrp": Bip44Coins.RIPPLE,
    "sol": Bip44Coins.SOLANA,
    "trx": Bip44Coins.TRON,
    "ton": Bip44Coins.TON,
    "ada": Bip44Coins.CARDANO_BYRON_ICARUS,
}

WORD_COUNT_MAP = {
    12: Bip39WordsNum.WORDS_NUM_12,
    15: Bip39WordsNum.WORDS_NUM_15,
    18: Bip39WordsNum.WORDS_NUM_18,
    21: Bip39WordsNum.WORDS_NUM_21,
    24: Bip39WordsNum.WORDS_NUM_24,
}


def generate_mnemonic(word_count: int) -> str:
    if word_count not in WORD_COUNT_MAP:
        raise ValueError(f"word_count must be one of {sorted(WORD_COUNT_MAP)}")
    return str(Bip39MnemonicGenerator().FromWordsNumber(WORD_COUNT_MAP[word_count]))


def validate_mnemonic(mnemonic: str) -> bool:
    return Bip39MnemonicValidator().IsValid(mnemonic)


def build_context(seed_bytes: bytes, coin_key: str, path_type: str):
    """Returns a Bip44/49/84/86 context object rooted at the coin, ready
    to derive account/change/address_index below it."""
    coin_key = coin_key.lower()

    if coin_key == "btc":
        cls_name, coin_enum = BTC_LIKE_PATH_TYPES[path_type]
        cls = {"bip44": Bip44, "bip49": Bip49, "bip84": Bip84, "bip86": Bip86}[cls_name]
        return cls.FromSeed(seed_bytes, coin_enum)

    if coin_key in BIP44_ONLY_COINS:
        return Bip44.FromSeed(seed_bytes, BIP44_ONLY_COINS[coin_key])

    raise ValueError(
        f"Unsupported coin '{coin_key}'. "
        f"Supported: btc, {', '.join(BIP44_ONLY_COINS)}"
    )


PURPOSE_BY_CLASS = {"Bip44": 44, "Bip49": 49, "Bip84": 84, "Bip86": 86}


def derive_addresses(ctx, account: int, change: int, count: int, start_index: int = 0):
    purpose = PURPOSE_BY_CLASS.get(type(ctx.Purpose()).__name__, 44)
    coin_idx = ctx.CoinConf().CoinIndex() if hasattr(ctx, "CoinConf") else "?"

    acc_ctx = ctx.Purpose().Coin().Account(account)
    change_ctx = acc_ctx.Change(Bip44Changes.CHAIN_EXT if change == 0 else Bip44Changes.CHAIN_INT)

    results = []
    for i in range(start_index, start_index + count):
        addr_ctx = change_ctx.AddressIndex(i)
        path = f"m/{purpose}'/{coin_idx}'/{account}'/{change}/{i}"
        results.append(
            {
                "index": i,
                "path": path,
                "address": addr_ctx.PublicKey().ToAddress(),
                "private_key_wif": _safe_wif(addr_ctx),
                "private_key_hex": addr_ctx.PrivateKey().Raw().ToHex(),
                "public_key_hex": addr_ctx.PublicKey().RawCompressed().ToHex(),
            }
        )
    return results


def _safe_wif(addr_ctx):
    """Not every coin/curve exposes a WIF-formatted key (e.g. ed25519 coins
    like Solana/TON don't). Fall back gracefully."""
    try:
        return addr_ctx.PrivateKey().ToWif()
    except Exception:
        return None


def print_results(mnemonic: str, coin: str, path_type: str, results: list, show_private: bool):
    print("=" * 70)
    print(f"Mnemonic : {mnemonic}")
    print(f"Coin     : {coin.upper()}" + (f" ({path_type})" if coin.lower() == "btc" else ""))
    print("=" * 70)
    for r in results:
        print(f"\n[{r['index']}] Path: {r['path']}")
        print(f"    Address     : {r['address']}")
        if show_private:
            print(f"    Private key (hex): {r['private_key_hex']}")
            if r["private_key_wif"]:
                print(f"    Private key (WIF): {r['private_key_wif']}")
        else:
            print("    Private key : (hidden — pass --show-private to reveal)")


def main():
    parser = argparse.ArgumentParser(
        description="Convert a BIP39 mnemonic into private keys and addresses.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    src = parser.add_mutually_exclusive_group(required=True)
    src.add_argument("--mnemonic", type=str, help="BIP39 mnemonic phrase (quoted).")
    src.add_argument(
        "--generate", action="store_true", help="Generate a new random mnemonic instead."
    )

    parser.add_argument(
        "--words", type=int, default=12, choices=sorted(WORD_COUNT_MAP),
        help="Word count when using --generate (default: 12).",
    )
    parser.add_argument("--passphrase", type=str, default="", help="Optional BIP39 passphrase.")
    parser.add_argument(
        "--coin", type=str, default="btc",
        help=f"Coin to derive for. Options: btc, {', '.join(BIP44_ONLY_COINS)}",
    )
    parser.add_argument(
        "--path-type", type=str, default="legacy", choices=list(BTC_LIKE_PATH_TYPES),
        help="BTC address format (ignored for non-BTC coins). Default: legacy.",
    )
    parser.add_argument("--account", type=int, default=0, help="Account index (default 0).")
    parser.add_argument(
        "--change", type=int, default=0, choices=[0, 1],
        help="0 = external/receiving chain, 1 = internal/change chain.",
    )
    parser.add_argument("--start-index", type=int, default=0, help="First address index.")
    parser.add_argument("--count", type=int, default=1, help="Number of addresses to derive.")
    parser.add_argument(
        "--show-private", action="store_true",
        help="Print private keys. Omitted by default for safety.",
    )
    parser.add_argument(
        "--all-paths", action="store_true",
        help="For BTC: derive one address of each path type (legacy, nested-segwit, segwit, taproot).",
    )

    args = parser.parse_args()

    # --- Mnemonic ---
    if args.generate:
        mnemonic = generate_mnemonic(args.words)
        print(f"Generated mnemonic ({args.words} words):\n  {mnemonic}\n")
    else:
        mnemonic = args.mnemonic.strip()
        if not validate_mnemonic(mnemonic):
            print("ERROR: Invalid BIP39 mnemonic (bad word or checksum).", file=sys.stderr)
            sys.exit(1)

    seed_bytes = Bip39SeedGenerator(mnemonic).Generate(args.passphrase)

    # --- Derivation ---
    try:
        if args.coin.lower() == "btc" and args.all_paths:
            for pt in BTC_LIKE_PATH_TYPES:
                ctx = build_context(seed_bytes, "btc", pt)
                results = derive_addresses(ctx, args.account, args.change, 1, args.start_index)
                print_results(mnemonic, "btc", pt, results, args.show_private)
        else:
            ctx = build_context(seed_bytes, args.coin, args.path_type)
            results = derive_addresses(
                ctx, args.account, args.change, args.count, args.start_index
            )
            print_results(mnemonic, args.coin, args.path_type, results, args.show_private)
    except ValueError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)

    if not args.show_private:
        print("\n(Tip: pass --show-private to also print private keys. "
              "Never share private keys or your mnemonic with anyone.)")


if __name__ == "__main__":
    main()
