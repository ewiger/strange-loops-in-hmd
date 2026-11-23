#!/usr/bin/env python3
"""Derivation over the atoms of the knowledge base.

The partial logic as a formal system (methodology/derivation.hmd):

  language   atoms `predicate(first, second)`
  axioms     the atoms that claims assert, each with the address of its claim
  rules      the Horn rules in the header of knowledge/meta/knowledge-graph.hmd,
             under `metadata.rules`
  theorems   the atoms a finite derivation ends in

Rules are applied to the asserted atoms until nothing new follows. Denied
atoms are never premises. A derived atom that some claim denies is a
contradiction between named claims, and it stays one: nothing further is
concluded from the fact that it is a contradiction.

Every derivation has a cost, as methodology/distance-to-logic.hmd defines it:
an axiom believed at p costs -log2(p) bits and the costs of the steps add.
The derivation kept for an atom is the cheapest. Two beliefs are read off it:

  product  2^(-cost), the product of the beliefs of its axioms, which assumes
           that the claims hold or fail independently
  bound    1 minus the sum of the doubts of its axioms, never below 0, which
           assumes nothing about how the claims depend on each other

Usage:
  derive.py                       summary, then the sections below
  derive.py --derived             atoms that follow and that no claim states
  derive.py --contradictions      derived atoms that a claim denies, and clashes
  derive.py --prove "is-a(a, b)"  the derivation of one atom, down to claims
"""

import argparse
import math
import re
import sys
from pathlib import Path

from claim_distance import header, read_claims

ATOM = re.compile(r"^\s*([a-z0-9-]+)\(\s*([a-z0-9-]+)\s*,\s*([a-z0-9-]+)\s*\)\s*$")
VARIABLES = {"x", "y", "z"}
# Predicates whose two arguments may be read in either order. Their atoms are
# written with the arguments in alphabetical order (methodology/partial-logic.hmd).
SYMMETRIC = {"same-as", "analogous-to", "inverse-of"}


def canonical(atom):
    """An atom in the one spelling it is written in."""
    if atom[0] in SYMMETRIC and atom[1] > atom[2]:
        return (atom[0], atom[2], atom[1])
    return atom


def parse(text):
    """An atom as (predicate, first, second), or None when it is not one."""
    m = ATOM.match(text)
    return m.groups() if m else None


def show(atom):
    return f"{atom[0]}({atom[1]}, {atom[2]})"


def read_rules(vault):
    """The rules held in the header of the card that describes the graph."""
    meta = header(vault / "meta" / "knowledge-graph.hmd").get("metadata") or {}
    rules = []
    for r in meta.get("rules") or []:
        premises = [parse(p) for p in r["from"]]
        gives = parse(r["gives"]) if "gives" in r else None
        if None in premises or ("gives" in r and gives is None):
            sys.exit(f"rule {r['id']} has a premise or conclusion that is not an atom")
        if not gives and not r.get("clash"):
            sys.exit(f"rule {r['id']} neither gives an atom nor declares a clash")
        rules.append({"id": r["id"], "from": premises, "gives": gives})
    return rules


def match(pattern, atom, binding):
    """Extend `binding` so that `pattern` becomes `atom`, or return None."""
    out = dict(binding)
    for p, a in zip(pattern[1:], atom[1:]):
        if p in VARIABLES:
            if out.setdefault(p, a) != a:
                return None
        elif p != a:
            return None
    return out


def readings(atom):
    """The orders in which an atom's arguments may be read."""
    if atom[0] in SYMMETRIC:
        return (atom, (atom[0], atom[2], atom[1]))
    return (atom,)


def bindings(premises, facts):
    """Every way of matching all `premises` against `facts`.

    Two variables never take the same value: a rule about x, y and z is about
    three things, and `is-a(a, a)` is not a conclusion worth drawing.
    """
    def go(i, binding, used):
        if i == len(premises):
            if len(set(binding.values())) == len(binding):
                yield binding, used
            return
        for fact in facts.get(premises[i][0], ()):
            for reading in readings(fact):
                b = match(premises[i], reading, binding)
                if b is not None:
                    yield from go(i + 1, b, used + [fact])
    yield from go(0, {}, [])


def substitute(pattern, binding):
    return canonical((pattern[0],) + tuple(binding.get(t, t) for t in pattern[1:]))


def close(axioms, rules):
    """Apply the rules to a fixed point, keeping the cheapest derivations.

    `axioms` maps each asserted atom to its cost. Returns the cost of every
    atom that holds, the derivation `atom -> (rule id, premises)` of every
    atom that is not an axiom, and the clashes `(rule id, premises)`.
    """
    cost = dict(axioms)
    why = {}
    clashes = {}
    changed = True
    while changed:
        changed = False
        facts = {}
        for a in sorted(cost):
            facts.setdefault(a[0], []).append(a)
        for rule in rules:
            for binding, used in bindings(rule["from"], facts):
                if rule["gives"] is None:
                    clashes.setdefault((rule["id"], frozenset(used)), used)
                    continue
                atom = substitute(rule["gives"], binding)
                if atom in axioms:
                    continue
                c = sum(cost[p] for p in used)
                if atom not in cost or c < cost[atom] - 1e-12:
                    cost[atom] = c
                    why[atom] = (rule["id"], used)
                    changed = True
    return cost, why, list(clashes.items())


def leaves(atom, why):
    """The axioms a derivation starts from, one entry for each use."""
    if atom not in why:
        return [atom]
    return [leaf for p in why[atom][1] for leaf in leaves(p, why)]


def tree(atom, why, claims, denied, depth=0):
    """The derivation of an atom as indented lines, down to the claims."""
    pad = "  " * depth
    note = "   [also denied by " + ", ".join(denied[atom]) + "]" if atom in denied else ""
    if atom not in why:
        said = ", ".join(f"{ref} at {p}" for ref, p in claims[atom])
        return [f"{pad}{show(atom)}   asserted by {said}{note}"]
    rule, premises = why[atom]
    lines = [f"{pad}{show(atom)}   by {rule}{note}"]
    for p in premises:
        lines += tree(p, why, claims, denied, depth + 1)
    return lines


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--vault", type=Path,
                   default=Path(__file__).resolve().parent.parent / "knowledge")
    p.add_argument("--derived", action="store_true")
    p.add_argument("--contradictions", action="store_true")
    p.add_argument("--prove", metavar="ATOM")
    args = p.parse_args()

    claims, denied, skipped = {}, {}, []
    for k in read_claims(args.vault):
        if not k["atom"]:
            continue
        atom = parse(k["atom"])
        if atom is None:
            skipped.append(k["ref"])
            continue
        atom = canonical(atom)
        if k["holds"]:
            claims.setdefault(atom, []).append((k["ref"], float(k["credence"])))
        else:
            denied.setdefault(atom, []).append(k["ref"])

    # An atom several claims assert is as believable as the surest of them.
    belief = {a: max(p for _, p in said) for a, said in claims.items()}
    axioms = {a: -math.log2(p) for a, p in belief.items()}
    rules = read_rules(args.vault)
    cost, why, clashes = close(axioms, rules)

    def product(atom):
        return 2 ** -cost[atom]

    def bound(atom):
        return max(0.0, 1 - sum(1 - belief[leaf] for leaf in leaves(atom, why)))

    def rests(atom):
        return ", ".join(sorted({ref for leaf in leaves(atom, why) for ref, _ in claims[leaf]}))

    def measure(atom):
        return f"cost {cost[atom]:.3f} bits, belief {product(atom):.3f} as a product, at least {bound(atom):.3f}"

    if args.prove:
        goal = parse(args.prove)
        if goal is None:
            sys.exit(f"not an atom: {args.prove}")
        goal = canonical(goal)
        if goal in cost:
            print("\n".join(tree(goal, why, claims, denied)))
            print(measure(goal))
        elif goal in denied:
            print(f"{show(goal)} is not derivable; it is denied by {', '.join(denied[goal])}")
            sys.exit(1)
        else:
            print(f"{show(goal)} is not derivable: no claim states it and no rule yields it")
            sys.exit(1)
        return

    contradicted = sorted(a for a in why if a in denied)
    stated_both = sorted(a for a in claims if a in denied)
    everything = not (args.derived or args.contradictions)

    if everything:
        print(f"rules\t{len(rules)}")
        print(f"asserted atoms (axioms)\t{len(claims)}")
        print(f"denied atoms\t{len(denied)}")
        print(f"derived atoms no claim states\t{len(why)}")
        print(f"stated contradictions\t{len(stated_both)}")
        print(f"derived contradictions\t{len(contradicted)}")
        print(f"clashes\t{len(clashes)}")
        if skipped:
            print(f"atoms not of the form predicate(a, b)\t{', '.join(skipped)}")
        print()

    if everything or args.contradictions:
        print("# derived contradictions: a derived atom that a claim denies")
        for atom in contradicted:
            print("\n".join(tree(atom, why, claims, denied)))
            print(measure(atom))
            print()
        print("# clashes: premises a rule says cannot hold together")
        for (rule, _), used in sorted(clashes, key=lambda c: (c[0][0], sorted(c[1]))):
            print(f"{rule}: " + " with ".join(show(a) for a in used))
            for a in used:
                print("\n".join(tree(a, why, claims, denied, 1)))
            print()

    if everything or args.derived:
        print("# derived atoms")
        print("atom\trule\tcost_bits\tproduct\tbound\trests_on\tcontested_axioms")
        for atom in sorted(why):
            weak = ", ".join(show(a) for a in sorted(set(leaves(atom, why))) if a in denied)
            print(f"{show(atom)}\t{why[atom][0]}\t{cost[atom]:.3f}\t{product(atom):.3f}\t"
                  f"{bound(atom):.3f}\t{rests(atom)}\t{weak}")


if __name__ == "__main__":
    main()
