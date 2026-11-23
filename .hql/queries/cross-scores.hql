// status: valid-now
// vault: the root of this repository
// The cross score of every link between two cards that both carry claims:
// how much the card at one end disagrees with the card at the other. Four
// numbers, each a different way of measuring it (methodology/cross-scores.hmd):
//   shared        atoms both cards speak on; the three numbers below it are
//                 absent when this is 0, since nothing can then be compared
//   disagreement  mean distance between the two cards' beliefs in a shared
//                 atom, from 0 (same belief) to 1 (opposite certainties)
//   divergence    the same comparison as information, the mean
//                 Jensen-Shannon divergence in bits, from 0 to 1
//   conflicts     shared atoms that one card asserts and the other denies
//   distance      how little the two cards talk about the same things: one
//                 minus the overlap of the arguments of their atoms
// The links that disagree most come first.
from stats import mean
from claims import Said, said, compare, arguments

spoken = cards | flat_map(said) | List

fn about(xs: List<Said>) : List<String> = xs | flat_map(s => arguments(s.atom)) | distinct

fn score(e: Edge) : Data {
    x = spoken | filter(s => s.card == e.source)
    y = spoken | filter(s => s.card == e.target)
    shared = x | join(y, left = a => a.atom, right = b => b.atom, into = compare)
    common = about(x) | filter(t => contains(about(y), t)) | size
    either = size(about(x)) + size(about(y)) - common
    {
        from: e.source,
        to: e.target,
        relation: match e.data.relation { some(String r) => r, _ => "untyped" },
        shared: size(shared),
        disagreement: shared | map(p => p.gap) | mean,
        divergence: shared | map(p => p.bits) | mean,
        conflicts: shared | filter(p => p.clash) | size,
        distance: match either { 0 => none, _ => some(1.0f - float(common) / float(either)) }
    }
}

/// The disagreement of a link, or -1 for one with no shared atom, to sort by.
fn gap(e: Edge) : Float =
    spoken
    | filter(s => s.card == e.source)
    | join(spoken | filter(s => s.card == e.target), left = a => a.atom, right = b => b.atom, into = compare)
    | map(p => p.gap)
    | mean
    | unwrap_or(0.0f - 1.0f)

graph.edges
| filter(e => (spoken | filter(s => s.card == e.source) | size) > 0 and (spoken | filter(s => s.card == e.target) | size) > 0)
| sort(by = e => e.source + " " + e.target)
| sort(by = e => 0.0f - gap(e))
| map(score)
