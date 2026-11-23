// status: valid-now
// vault: the root of this repository
// Cards whose term was coined in the discussion and is not established usage.
cards
| filter(c => c.metadata.established == false)
| sort(by = c => c.name)
| map(c => {card: c.name, cluster: c.metadata.cluster})
