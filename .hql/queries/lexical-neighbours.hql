// status: valid-now
// vault: the root of this repository
// Word-overlap neighbours of a phrase. A stand-in for the semantic version in
// future/semantic-neighbours.hql, which needs an embedding index and `this`.
cards
| lexical("inference from observations to a hypothesis, tested by deduction")
| take(5)
| map(h => {card: h.value.name, score: h.score})
