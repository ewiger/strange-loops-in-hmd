// status: proposed
// vault: the root of this repository
// Needs: `this`, the `ai` module, `cached` cells, sections.
import future
import ai

// Each linked card restated in two sentences from the point of view of the
// current card. Meant to run as a `cached` cell, recomputed only when this
// card or the neighbour changes.
summarizer = Agent(@[[summarizer]])
this
| uplinks
| filter(e => e.data.relation != none)
| map(e => {
    card: e.target,
    relation: e.data.relation,
    summary: summarizer | ask(
      Prompt("Restate {target} in two sentences for a reader of {source}, given that the relation is {relation}."),
      Context(source = this.sections["Description"], target = @[[e.target]].sections["Description"], relation = e.data.relation)
    )
  })
