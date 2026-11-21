// status: proposed
// vault: the root of this repository
// Needs: the `ai` module, typed agent results, `cards` filtered by link.
import future
import ai

// A cognitive operation applied to a passage, as a typed result. The labels
// are the cards that are instances of [[cognitive-operation]], so the
// taxonomy in the vault is the schema of the answer.
type Operation = {
  label: Card,          // one of the operation cards
  evidence: List<String>,
  confidence: Float
}

operations = @[[cognitive-operation]] | downlinks
  | filter(e => e.data.relation == "instance-of")
  | map(e => e.source)

fn classify(passage: String) : Operation =
  Agent(@[[classifier]])
  | ask(
      Prompt("Which cognitive operation does this passage perform? Quote the evidence."),
      Context(passage = passage, labels = operations | map(c => {name: c.name, definition: c.sections["Description"]}))
    )
  | validate<Operation>

// The signatures the discussion proposed, as typed transformations.
fn induce(examples: List<String>) : List<Hypothesis> = ...
fn deduce(theory: Card, premises: List<String>) : List<Conclusion> = ...
fn analogize(a: Card, b: Card) : List<Correspondence> = ...
