// status: proposed
// vault: the root of this repository
// Needs: `cycles` on a graph, the `ai` module, typed agent results.
import future
import ai

// Which link cycles in this vault are strange loops and which are ordinary
// feedback? A cycle is a candidate only if some card on it describes the
// mechanism that interprets the cycle, that is, if a level is crossed.
type Verdict = {
  crosses_level: Bool,
  object_level: List<Card>,
  meta_level: List<Card>,
  reason: String
}

judge = Agent(@[[level-judge]])
graph
| cycles(max_length = 6)
| map(cycle => {
    cycle: cycle | map(c => c.name),
    verdict: judge | ask(
      Prompt("Using the definitions given, does this cycle of cards cross from object level to meta level and return?"),
      Context(cycle = cycle, definitions = [@[[level-crossing]], @[[object-and-meta-level]], @[[feedback-loop]]])
    ) | validate<Verdict>
  })
| filter(r => r.verdict.crosses_level)
