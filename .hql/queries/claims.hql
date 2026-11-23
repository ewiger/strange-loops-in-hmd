// status: valid-now
// vault: the root of this repository
// Every claim of the knowledge base as one list. A claim is addressed by the
// name of its card and its `id` on that card: `strange-loop#2`. `atom` is
// absent for a claim that has been left in natural language.
from claims import claims_of

cards
| sort(by = c => c.name)
| flat_map(c => claims_of(c) | map(k => {
    ref: fmt("{}#{}", c.name, k.id),
    evidence: k.evidence,
    credence: k.credence,
    atom: k.atom,
    denies: not k.holds.unwrap_or(true),
    star: k.star,
    text: k.text
}))
