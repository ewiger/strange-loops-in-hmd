// status: proposed
// vault: the root of this repository
// Needs: `this`, `semantic` over a question not pinned in the index.
import future

// Cards close in meaning to the current card that it does not link yet:
// relations the net is missing.
linked = this | uplinks | map(e => e.target)
cards
| semantic(this.body)
| filter(h => h.value.name != this.name and not contains(linked, h.value.name))
| take(5)
| map(h => {card: h.value, score: h.score})
