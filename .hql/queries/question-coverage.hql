// status: valid-now
// vault: the root of this repository
// For each README question card, the cards that declare they bear on it.
graph.edges
| filter(e => match e.data.relation { some(String r) => r == "answers", _ => false })
| group(by = e => e.target)
| sort(by = g => g.key)
| map(g => {question: g.key, cards: g.items | map(e => e.source) | sort(by = n => n)})
