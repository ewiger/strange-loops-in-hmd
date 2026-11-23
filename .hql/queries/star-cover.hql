// status: valid-now
// vault: the root of this repository
// Whether the north stars cover the knowledge base (methodology/north-stars.hmd).
// The territory of a star is the set of cards with a claim under it.
//   territories  each star with its cards and its number of claims
//   uncovered    concept cards in no territory: the cover has a hole there
//   dominated    stars whose territory lies inside another's; such a star
//                adds no ground and is a candidate for removal
//   overlaps     pairs of stars sharing cards, with the cards: where two
//                stars meet, and the edges of the story map
//   unknown      stars a claim names that have no star card
//   unclaimed    claims of concept cards under no star, as a count
from claims import Under, under, claims_of

concepts = cards | filter(c => c.metadata.category == "concept") | List
placed = cards | flat_map(under) | List
stars = placed | map(u => u.star) | distinct | sort(by = s => s) | List
declared = cards | filter(c => c.metadata.category == "star") | map(c => c.name) | List

fn territory(star: String) : List<String> =
    placed | filter(u => u.star == star) | map(u => u.card) | distinct | sort(by = n => n) | List

fn shared(a: String, b: String) : List<String> =
    territory(a) | filter(n => contains(territory(b), n))

fn inside(a: String, b: String) : Bool = size(shared(a, b)) == size(territory(a))

{
    territories: stars | map(s => {star: s, cards: territory(s), claims: placed | filter(u => u.star == s) | size}),
    uncovered: concepts
        | map(c => c.name)
        | filter(n => not (placed | any(u => u.card == n)))
        | sort(by = n => n),
    dominated: stars
        | flat_map(a => stars | filter(b => a != b and inside(a, b)) | map(b => {star: a, inside: b})),
    overlaps: stars
        | flat_map(a => stars
            | filter(b => a < b and size(shared(a, b)) > 0)
            | map(b => {a: a, b: b, cards: shared(a, b)})),
    unknown: stars | filter(s => not contains(declared, s)),
    unclaimed: (concepts | flat_map(claims_of) | size) - (concepts | flat_map(under) | size)
}
