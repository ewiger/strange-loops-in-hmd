// status: proposed
// vault: the root of this repository
// Needs: the `ai` module (Agent, Context, Prompt, Tool, run), typed and
// validated agent results, a trait implemented for Agent, and a reference
// into another vault: `@[[agents:base-agent]]` is the card `base-agent` of the
// agents vault, bound in configuration as a namespace.
import future
import ai

// ---- The tools on the base agent's card (these three run today) ----------

fn is_kind(e: Edge, kind: String) : Bool =
    match e.data.relation { some(String r) => r == kind, _ => false }

fn operations() : List<String> =
    @[[cognitive-operation]] | downlinks | filter(e => is_kind(e, "instance-of")) | map(e => e.source) | List

fn definition(name: String) : List<String> =
    cards | filter(c => c.name == name) | map(c => c.body) | List

fn relations(name: String) : List<String> =
    cards | filter(c => c.name == name)
    | flat_map(c => c | uplinks | map(e => match e.data.relation { some(String r) => r + " " + e.target, _ => "links " + e.target }))
    | List

tools = [
    Tool(operations, "The names of all operation cards that exist now"),
    Tool(definition, "The text of one card"),
    Tool(relations, "The declared relations of one card")
]

// ---- The language construct ---------------------------------------------

// An operation is a card, not a function: a card that declares itself an
// instance of cognitive-operation. The set is open. Writing a new such card
// extends every agent that performs operations, with no change to code.
type Operation = Card

// What performing an operation returns. `O` is the operation's output type;
// the rest is the obligation every result carries.
type Performed<O> = {
    operation: Operation,
    input: String,              // the input restated as the operation's input
    output: O,
    support: List<String>,      // evidence, steps, or what was left out
    confidence: String,         // in words that can be acted on
    not_done: List<String>,
    run: Run                    // the whole run, never collapsed to its text
}

// The capability. Any agent that implements it can perform any operation.
trait Performs {
    fn perform<O>(self, operation: Operation, input: Seq<ContextItem>) : Performed<O>
    fn performable(self) : List<Operation>
}

// The base agent is the plain implementation: the operation's card and the
// input go in as context, the agent's own card is the instructions, and the
// answer is validated against the declared shape.
impl Performs for Agent {
    fn perform<O>(self, operation: Operation, input: Seq<ContextItem>) : Performed<O> =
        [operation]
        | Context("operation")
        | concat(input)
        | Prompt("Perform the operation defined in `operation` on `input`.")
        | run(self, tools = tools)
        | validate<Performed<O>>

    fn performable(self) : List<Operation> =
        operations() | map(n => @[[n]])
}

// A user-defined agent extends the base one by a card of its own; the
// capability comes with the type.
base = @[[agents:base-agent]] | Agent

// ---- Typed entry points, one per operation that has a fixed signature ----

type Hypothesis = {statement: String, covers: List<String>, would_refute: String}
type Conclusion = {statement: String, steps: List<String>, checked: Bool}
type Correspondence = {from: String, to: String, relation: String, holds: Bool}

fn induce(a: Agent, examples: List<String>) : Performed<List<Hypothesis>> =
    a.perform(@[[induction]], examples | Context("input"))

fn deduce(a: Agent, theory: Card, premises: List<String>) : Performed<List<Conclusion>> =
    a.perform(@[[deduction]], concat([theory] | Context("theory"), premises | Context("input")))

fn analogize(a: Agent, left: Card, right: Card) : Performed<List<Correspondence>> =
    a.perform(@[[analogy]], [left, right] | Context("input"))

// ---- Use ----------------------------------------------------------------

// One operation.
found = base | induce([
    "A cycle of document, code, output and document again was called feedback.",
    "A thermostat was called feedback.",
    "A recursive function was called not a strange loop."
])

// The reasoning cycle as a pipeline of operations: induce, deduce, evaluate.
tested = base
    | deduce(@[[strange-loop]], found.output | map(h => h.statement))
    | r => base.perform(@[[evaluation]], r.output | Context("input"))

// The agent applied to itself: reflection on a run made under its own card,
// then a proposed revision of that card. Nothing here writes to the vault.
critique = base.perform(@[[reflection]], concat([@[[agents:base-agent]]] | Context("process"), [found.run] | Context("results")))
proposal = base.perform(@[[revision]], concat([@[[agents:base-agent]]] | Context("model"), [critique.output] | Context("evidence")))
proposal.output
