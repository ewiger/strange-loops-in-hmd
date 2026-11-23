/// Claims: what a concept card asserts, read from its header, and the numbers
/// that compare what two cards assert. The method these functions implement
/// is described in the `methodology/` folder.
module claims

import core
import doc
from math import abs, ln
from regex import find_all

/// One claim as it is written under `metadata.claims` in a card's header.
/// `atom` is the claim in the partial logic, when it has been put there;
/// `holds: false` says the claim denies its atom; `star` names the north
/// star the claim falls under.
type Claim : Data {
    id       : Int
    text     : String
    evidence : String
    credence : Float
    atom?    : String
    holds?   : Bool
    star?    : String
}

/// A card's metadata when it carries claims.
type Claimed : Data {
    claims : List<Claim>
}

/// The claims written on one card, or none when it carries no claims.
fn claims_of(card: Card) : List<Claim> = match card.metadata {
    Claimed m => m.claims,
    _ => [],
}

/// The probability a claim gives its atom: its credence when it asserts the
/// atom, and one minus its credence when it denies it.
fn belief(k: Claim) : Float = match k.holds.unwrap_or(true) {
    true => k.credence,
    false => 1.0f - k.credence,
}

/// `x * log2(x / m)`, with the convention that it is 0 at `x = 0`.
private fn bits(x: Float, m: Float) : Float = match x <= 0.0f {
    true => 0.0f,
    false => x * ln(x / m) / ln(2.0f),
}

/// The Jensen-Shannon divergence, in bits, between two beliefs in one atom,
/// each read as a coin with that probability. It is 0 when the beliefs are
/// equal and 1 when one is certain the atom holds and the other that it does
/// not.
fn divergence(p: Float, q: Float) : Float {
    m = (p + q) / 2.0f
    (bits(p, m) + bits(1.0f - p, 1.0f - m) + bits(q, m) + bits(1.0f - q, 1.0f - m)) / 2.0f
}

/// The words an atom is made of: its predicate and its arguments.
/// `terms("requires(strange-loop, level-crossing)")` is
/// `["requires", "strange-loop", "level-crossing"]`.
fn terms(atom: String) : List<String> = find_all(atom, "[a-z0-9][a-z0-9-]*")

/// What an atom is about: its arguments, without the predicate.
fn arguments(atom: String) : List<String> = terms(atom) | drop(1)

/// The predicate of an atom: `"requires"` for the atom above.
fn predicate(atom: String) : String = terms(atom) | first | unwrap_or("")

/// What one card says about one atom: the atom, whether the card asserts or
/// denies it, and the belief that follows. `ref` is the address of the claim,
/// the card's name and the claim's `id`: `strange-loop#2`.
type Said = {
    ref     : String
    card    : String
    atom    : String
    asserts : Bool
    belief  : Float
}

/// The claims of one card that carry an atom, each as what the card says
/// about that atom. Claims left in natural language are not in it.
fn said(card: Card) : List<Said> =
    claims_of(card)
    | flat_map(k => match k.atom {
        some(String a) => [Said(ref = fmt("{}#{}", card.name, k.id), card = card.name, atom = a, asserts = k.holds.unwrap_or(true), belief = belief(k))],
        _ => [],
    })

/// Two cards on one atom: how far apart their beliefs are, the same in bits,
/// and whether one asserts what the other denies.
type Compared = {
    atom  : String
    left  : String
    right : String
    gap   : Float
    bits  : Float
    clash : Bool
}

/// What `a` and `b` say about the atom they share, compared.
fn compare(a: Said, b: Said) : Compared = Compared(
    atom = a.atom,
    left = a.ref,
    right = b.ref,
    gap = abs(a.belief - b.belief),
    bits = divergence(a.belief, b.belief),
    clash = a.asserts != b.asserts,
)

/// One claim placed under a north star: the star it names, the card it is
/// written on, and its address.
type Under = {
    star : String
    card : String
    ref  : String
}

/// The claims of one card that name a north star.
fn under(card: Card) : List<Under> =
    claims_of(card)
    | flat_map(k => match k.star {
        some(String s) => [Under(star = s, card = card.name, ref = fmt("{}#{}", card.name, k.id))],
        _ => [],
    })
