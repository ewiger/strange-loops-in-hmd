// status: valid-now
// vault: the root of this repository
// What recurs in the partial logic: each predicate, and each thing the atoms
// are about, with the number of atoms it occurs in and the number of cards
// that use it. A term many cards use is a candidate for a north star, or for
// the centre of one (methodology/north-stars.hmd). Terms used by one card
// only are left out.
from claims import Said, said, arguments, predicate

spoken = cards | flat_map(said) | List

fn tally(pick: (Said) -> List<String>) : List<Data> =
    spoken
    | flat_map(s => pick(s) | distinct | map(t => [t, s.card]))
    | group(by = p => p | first | unwrap_or(""))
    | filter(g => (g.items | map(p => p | last | unwrap_or("")) | distinct | size) > 1)
    | sort(by = g => 0 - (g.items | map(p => p | last | unwrap_or("")) | distinct | size))
    | map(g => {term: g.key, atoms: size(g.items), cards: g.items | map(p => p | last | unwrap_or("")) | distinct | size})
    | List

{
    predicates: tally(s => [predicate(s.atom)]),
    terms: tally(s => arguments(s.atom))
}
