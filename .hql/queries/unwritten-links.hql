// status: valid-now
// vault: the root of this repository
// The backlog: concepts that cards link to and that have no card yet, with
// the number of cards mentioning each. Names of lens cards are left out:
// they exist, in the future vault, and a link cannot cross into it.
names = cards | map(c => c.name)
lenses = source("future").cards | map(c => c.name)
cards
| flat_map(c => c | uplinks | map(e => e.target))
| filter(t => not contains(names, t) and not contains(lenses, t))
| group(by = t => t)
| sort(by = g => g.key)
| map(g => {concept: g.key, mentions: size(g.items)})
