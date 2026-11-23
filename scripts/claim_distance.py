#!/usr/bin/env python3
"""Informational distance between the claims of the knowledge base.

Reads every claim from the card headers under a vault folder and compares the
claim texts pairwise with two distances, both from 0 (same) to 1 (unrelated):

  ncd  Normalized compression distance (Cilibrasi and Vitanyi, 2005), the
       computable stand-in for the normalized information distance:
           (C(xy) - min(C(x), C(y))) / max(C(x), C(y))
       where C is the compressed length in bytes. It sees shared strings.

  lin  One minus the information-weighted word overlap (after Lin, 1998):
           1 - I(words in both) / I(words in either)
       where I adds up -log2(df / N) over the words, df being the number of
       claims a word occurs in and N the number of claims. A rare shared word
       counts for more than a common one. It sees shared vocabulary.

Neither reads meaning: two claims that say the same thing in different words
are far apart under both.

Usage:
  claim_distance.py                  nearest pairs across cards, as TSV
  claim_distance.py --top 50         how many pairs to print
  claim_distance.py --by ncd         which distance to rank by (default lin)
  claim_distance.py --same-card      keep pairs from one card as well
  claim_distance.py --validate       test both distances against the atoms
"""

import argparse
import itertools
import math
import random
import re
import sys
import zlib
from pathlib import Path

import yaml

WORD = re.compile(r"[a-z0-9]+")


def header(path):
    """The YAML header of a card, or an empty mapping when it has none."""
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        return {}
    end = text.find("\n---", 3)
    if end < 0:
        return {}
    return yaml.safe_load(text[3:end]) or {}


def read_claims(vault):
    """Every claim under `vault`, each with its address `card#id`."""
    out = []
    for path in sorted(vault.rglob("*.hmd")):
        meta = header(path).get("metadata") or {}
        for k in meta.get("claims") or []:
            out.append({
                "ref": f"{path.stem}#{k['id']}",
                "card": path.stem,
                "text": k["text"],
                "atom": k.get("atom"),
                "holds": k.get("holds", True),
                "credence": k.get("credence"),
                "star": k.get("star"),
            })
    return out


def compressed(data):
    """Length in bytes of `data` under raw DEFLATE, with no container."""
    c = zlib.compressobj(9, zlib.DEFLATED, -15)
    return len(c.compress(data) + c.flush())


def ncd(x, y, cx, cy):
    """Normalized compression distance, averaged over both orders."""
    cxy = (compressed(x + b" " + y) + compressed(y + b" " + x)) / 2
    return (cxy - min(cx, cy)) / max(cx, cy)


def lin(a, b, info):
    """One minus the information-weighted overlap of two word sets."""
    either = sum(info[w] for w in a | b)
    if either == 0:
        return 0.0
    return 1 - sum(info[w] for w in a & b) / either


def all_pairs(claims):
    """Both distances for every pair of claims."""
    raw = [c["text"].lower().encode("utf-8") for c in claims]
    size = [compressed(r) for r in raw]
    words = [set(WORD.findall(c["text"].lower())) for c in claims]
    n = len(claims)
    df = {}
    for ws in words:
        for w in ws:
            df[w] = df.get(w, 0) + 1
    info = {w: -math.log2(d / n) for w, d in df.items()}
    for i, j in itertools.combinations(range(n), 2):
        yield (
            claims[i], claims[j],
            ncd(raw[i], raw[j], size[i], size[j]),
            lin(words[i], words[j], info),
        )


def auc(near, far, rng, draws=200_000):
    """Chance that a pair from `near` is closer than a pair from `far`."""
    if not near or not far:
        return float("nan")
    wins = 0.0
    for _ in range(draws):
        a, b = rng.choice(near), rng.choice(far)
        wins += 1.0 if a < b else 0.5 if a == b else 0.0
    return wins / draws


def validate(rows):
    """Ask whether pairs that should be close are closer than the rest.

    Three reference groups, all of pairs from different cards: the same atom,
    the same north star, and everything else. 0.5 is chance, 1.0 is perfect.
    """
    rng = random.Random(0)
    cross = [r for r in rows if r[0]["card"] != r[1]["card"]]
    same_atom = [r for r in cross if r[0]["atom"] and r[0]["atom"] == r[1]["atom"]]
    same_star = [r for r in cross if r[0]["star"] and r[0]["star"] == r[1]["star"]]
    rest = [r for r in cross
            if not (r[0]["atom"] and r[0]["atom"] == r[1]["atom"])
            and not (r[0]["star"] and r[0]["star"] == r[1]["star"])]
    print("group\tpairs\tncd_mean\tlin_mean\tncd_auc\tlin_auc")
    for name, group in (("same-atom", same_atom), ("same-star", same_star), ("rest", rest)):
        if not group:
            print(f"{name}\t0")
            continue
        ncd_mean = sum(r[2] for r in group) / len(group)
        lin_mean = sum(r[3] for r in group) / len(group)
        if group is rest:
            print(f"{name}\t{len(group)}\t{ncd_mean:.3f}\t{lin_mean:.3f}\t\t")
        else:
            a = auc([r[2] for r in group], [r[2] for r in rest], rng)
            b = auc([r[3] for r in group], [r[3] for r in rest], rng)
            print(f"{name}\t{len(group)}\t{ncd_mean:.3f}\t{lin_mean:.3f}\t{a:.3f}\t{b:.3f}")


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--vault", type=Path,
                   default=Path(__file__).resolve().parent.parent / "knowledge")
    p.add_argument("--top", type=int, default=30)
    p.add_argument("--by", choices=("ncd", "lin"), default="lin")
    p.add_argument("--same-card", action="store_true")
    p.add_argument("--validate", action="store_true")
    args = p.parse_args()

    claims = read_claims(args.vault)
    if not claims:
        sys.exit(f"no claims found under {args.vault}")
    rows = list(all_pairs(claims))

    if args.validate:
        validate(rows)
        return

    if not args.same_card:
        rows = [r for r in rows if r[0]["card"] != r[1]["card"]]
    rows.sort(key=lambda r: r[2 if args.by == "ncd" else 3])
    print("left\tright\tncd\tlin\tsame_atom")
    for a, b, d_ncd, d_lin in rows[:args.top]:
        same = "yes" if a["atom"] and a["atom"] == b["atom"] else ""
        print(f"{a['ref']}\t{b['ref']}\t{d_ncd:.3f}\t{d_lin:.3f}\t{same}")


if __name__ == "__main__":
    main()
