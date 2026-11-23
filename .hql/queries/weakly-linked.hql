// status: valid-now
// vault: the root of this repository
// Concept cards with fewer than three outgoing links or no incoming link.
// `uplinks` are the links a card makes, `downlinks` the links made to it.
cards
| filter(c => c.metadata.category == "concept")
| filter(c => (c | uplinks | size) < 3 or (c | downlinks | size) < 1)
| map(c => {card: c.name, outgoing: c | uplinks | size, incoming: c | downlinks | size})
