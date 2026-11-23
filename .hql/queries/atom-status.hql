// status: valid-now
// vault: the root of this repository
// The partial logic of the vault, atom by atom. Each atom that some claim
// speaks on is `asserted` (claims assert it and none denies it), `denied`
// (the reverse) or `both` (one claim asserts what another denies). An atom
// that no claim speaks on has the fourth status, unsaid, and is not listed.
// Atoms with the status `both` come first: they are the contradictions.
from claims import Said, said

fn status(yes: Int, no: Int) : String = match yes > 0 and no > 0 {
    true => "both",
    false => match yes > 0 { true => "asserted", false => "denied" },
}

fn yes(xs: List<Said>) : Int = xs | filter(s => s.asserts) | size
fn no(xs: List<Said>) : Int = xs | filter(s => not s.asserts) | size

cards
| flat_map(said)
| group(by = s => s.atom)
| sort(by = g => match status(yes(g.items), no(g.items)) { "both" => "0 " + g.key, _ => "1 " + g.key })
| map(g => {
    atom: g.key,
    status: status(yes(g.items), no(g.items)),
    asserted_by: g.items | filter(s => s.asserts) | map(s => s.ref),
    denied_by: g.items | filter(s => not s.asserts) | map(s => s.ref),
    cards: g.items | map(s => s.card) | distinct | size
})
