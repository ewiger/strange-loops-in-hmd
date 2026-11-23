// status: proposed
// vault: the root of this repository
// Contradictions between claims that the partial logic cannot see. Today two
// claims are compared only when they carry the same atom, so a claim left in
// natural language is never compared with anything, and neither are two atoms
// that conflict without being the same string. This design compares the
// claims of the two cards at the ends of every link by meaning: a model reads
// each pair and returns whether one entails, contradicts or is independent of
// the other, with the passage that decides it.
//
// What current HQL lacks: the `ai` module with a typed result (`judge` into a
// declared type), and `semantic` over text that was not pinned when the index
// was built.

import future
import ai
from claims import Claim, claims_of

type Verdict {
    relation : "entails" | "contradicts" | "independent"
    because  : String
}

fn stated(name: String) : List<Claim> = cards | filter(c => c.name == name) | flat_map(claims_of) | List

graph.edges
| flat_map(e => stated(e.source) | cross_join(stated(e.target), into = (a, b) => {
    left: fmt("{}#{}", e.source, a.id),
    right: fmt("{}#{}", e.target, b.id),
    near: semantic_distance(a.text, b.text),
    a: a,
    b: b
}))
| filter(p => p.near < 0.35)
| map(p => {
    left: p.left,
    right: p.right,
    verdict: ai.judge(Verdict, "Does the first claim entail the second, contradict it, or neither?", [p.a.text, p.b.text]),
    weight: p.a.credence * p.b.credence
})
| filter(r => r.verdict.relation == "contradicts")
| sort(by = r => 0.0f - r.weight)
