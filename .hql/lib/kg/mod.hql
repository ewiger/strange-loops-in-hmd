/// The knowledge graph as typed data. A card's header is read as nodes and
/// arrows, every arrow has a type, and every type has a signature saying
/// which types of node it may run from and to. The signatures are not written
/// here: they are data, held in the header of the card `knowledge-graph`, and
/// `check` applies them. That card is the article about this graph and is
/// one of its nodes.
module kg

import core
import doc
from claims import Said, said, claims_of, under, arguments, predicate

/// One type of node, as the schema declares it.
type NodeType : Data {
    type : String
    is   : String
}

/// One type of arrow, as the schema declares it: its name, the types of node
/// it may start from and end at, and whether it is written as a `link`
/// between cards, as the `atom` of a claim, or follows from the `header`.
type ArrowType : Data {
    type    : String
    from    : List<String>
    to      : List<String>
    written : String
    is      : String
}

/// The schema of the graph: its types of node and its types of arrow.
type Schema : Data {
    nodes  : List<NodeType>
    arrows : List<ArrowType>
}

/// A card's metadata when it carries a schema.
type Described : Data {
    schema : Schema
}

/// The schema a card carries, or none.
fn schema_of(card: Card) : Option<Schema> = match card.metadata {
    Described m => some(m.schema),
    _ => none,
}

/// A node: a name and the type of thing it names.
type Node = {
    name : String
    type : String
}

/// An arrow from one node to another. `type` is what kind of arrow it is,
/// `written` is where it comes from (`link`, `atom` or `header`), `by` is
/// the card or the claim answerable for it, and `belief` is the probability
/// its claim gives it, or 1 for an arrow that is not a matter of belief.
type Arrow = {
    from    : String
    to      : String
    type    : String
    written : String
    by      : String
    belief  : Float
}

/// The node a card is: its name, typed by its category.
fn node_of(card: Card) : Node = Node(
    name = card.name,
    type = match card.metadata.category { some(String s) => s, _ => "uncategorised" },
)

/// The nodes a card's claims are: one per claim, named by its address.
fn claim_nodes(card: Card) : List<Node> =
    claims_of(card) | map(k => Node(name = fmt("{}#{}", card.name, k.id), type = "claim"))

/// The arrows a card's header gives without any claim being believed: from
/// the card to each of its claims, and from a claim to its north star.
fn header_arrows(card: Card) : List<Arrow> = [
    claims_of(card) | map(k => Arrow(from = card.name, to = fmt("{}#{}", card.name, k.id), type = "claims", written = "header", by = card.name, belief = 1.0f)),
    under(card) | map(u => Arrow(from = u.ref, to = u.star, type = "under", written = "header", by = u.card, belief = 1.0f)),
] | concat_all

/// The arrows a card's claims assert or deny: one per atom, from its first
/// argument to its second, typed by its predicate. A denied atom is still an
/// arrow, with a belief below one half.
fn atom_arrows(card: Card) : List<Arrow> =
    said(card)
    | filter(s => size(arguments(s.atom)) == 2)
    | map(s => Arrow(
        from = arguments(s.atom) | first | unwrap_or(""),
        to = arguments(s.atom) | last | unwrap_or(""),
        type = predicate(s.atom),
        written = "atom",
        by = s.ref,
        belief = s.belief,
    ))

/// The arrow a link between two cards is, typed by its relation. A link with
/// no relation is a `mentions`.
fn link_arrow(e: Edge) : Arrow = Arrow(
    from = e.source,
    to = e.target,
    type = match e.data.relation { some(String r) => r, _ => "mentions" },
    written = "link",
    by = e.source,
    belief = 1.0f,
)

/// The type of the node called `name`: the type it has in `nodes`, or `term`
/// for a name that is no node, the argument of an atom that has no card.
fn type_in(nodes: List<Node>, name: String) : String =
    nodes | filter(n => n.name == name) | map(n => n.type) | first | unwrap_or("term")

/// What is wrong with an arrow under a schema, or none when it conforms: its
/// type is not declared for where it is written, or it starts from or ends at
/// a type of node its signature does not allow.
fn check(schema: Schema, nodes: List<Node>, a: Arrow) : Option<String> =
    match schema.arrows | filter(t => t.type == a.type and t.written == a.written) | first {
        some(t) => match contains(t.from, type_in(nodes, a.from)) {
            false => some(fmt("{} may not start from a {}", a.type, type_in(nodes, a.from))),
            true => match contains(t.to, type_in(nodes, a.to)) {
                false => some(fmt("{} may not end at a {}", a.type, type_in(nodes, a.to))),
                true => none,
            },
        },
        _ => some(fmt("{} is not a declared type of {} arrow", a.type, a.written)),
    }
