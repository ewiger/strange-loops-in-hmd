// status: valid-now
// vault: the root of this repository
// Links that contradict each other by direction. `is-a`, `instance-of`,
// `part-of`, `example-of` and `generalizes` run one way: if a is part of b,
// b is not part of a. A pair of cards that declares the same one of these in
// both directions has one of the two written from the wrong side. The schema
// check cannot see it, since both links have a valid signature; it is a
// contradiction between two arrows and not a fault in either.
one_way = ["is-a", "instance-of", "part-of", "example-of", "generalizes"]

fn kind(e: Edge) : String = match e.data.relation { some(String r) => r, _ => "" }

typed = graph.edges | filter(e => contains(one_way, kind(e))) | sort(by = e => e.source + " " + e.target) | List

typed
| filter(e => e.source < e.target and (typed | any(f => f.source == e.target and f.target == e.source and kind(f) == kind(e))))
| map(e => {a: e.source, b: e.target, relation: kind(e)})
