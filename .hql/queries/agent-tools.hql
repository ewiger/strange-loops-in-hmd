// status: valid-now
// vault: the root of this repository
// The three tools listed on the base agent's card, as ordinary functions.
// They only read the vault, so they run today; handing them to a model is the
// part that waits for the `ai` module (see future/perform-operation.hql).

fn is_kind(e: Edge, kind: String) : Bool =
    match e.data.relation { some(String r) => r == kind, _ => false }

/// The names of all operation cards: cards that declare themselves an
/// instance of the cognitive-operation card.
fn operations() : List<String> =
    @[[cognitive-operation]]
    | downlinks
    | filter(e => is_kind(e, "instance-of"))
    | map(e => e.source)
    | List

/// The text of one card, or nothing when the concept has no card yet.
fn definition(name: String) : List<String> =
    cards | filter(c => c.name == name) | map(c => c.body) | List

/// The declared relations of one card, as "kind target".
fn relations(name: String) : List<String> =
    cards
    | filter(c => c.name == name)
    | flat_map(c => c | uplinks | map(e => match e.data.relation { some(String r) => r + " " + e.target, _ => "links " + e.target }))
    | List

// What any agent of this project can perform now.
{available: operations(), relations_of_induction: relations("induction") | take(3)}
