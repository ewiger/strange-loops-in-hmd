// status: valid-now
// vault: the root of this repository
// The knowledge graph checked against its own schema. Every card and every
// claim is a node with a type, and every link, every atom and every
// header relation is an arrow with a type. The schema says which types of
// node each type of arrow may run from and to. It is not written in this
// file: it is read from the header of the card `knowledge-graph`, which is
// itself one of the nodes checked.
//   nodes       how many nodes of each type
//   arrows      how many arrows of each type, by where they are written
//   violations  arrows the schema does not allow, each with the reason
//   unused      arrow types the schema declares that no arrow has
from kg import Schema, Node, Arrow, node_of, claim_nodes, header_arrows, atom_arrows, link_arrow, schema_of, check

nodes = [cards | map(node_of) | List, cards | flat_map(claim_nodes) | List] | concat_all
arrows = [
    cards | flat_map(header_arrows) | List,
    cards | flat_map(atom_arrows) | List,
    graph.edges | sort(by = e => e.source + " " + e.target) | map(link_arrow) | List,
] | concat_all

fn report(s: Schema) : Data = {
    nodes: nodes | group(by = n => n.type) | sort(by = g => g.key) | map(g => {type: g.key, count: size(g.items)}),
    arrows: arrows
        | group(by = a => a.written + " " + a.type)
        | sort(by = g => g.key)
        | map(g => {arrow: g.key, count: size(g.items)}),
    violations: arrows
        | filter(a => is_some(check(s, nodes, a)))
        | map(a => {from: a.from, to: a.to, type: a.type, written: a.written, by: a.by, problem: check(s, nodes, a).unwrap_or("")}),
    unused: s.arrows
        | filter(t => not (arrows | any(a => a.type == t.type and a.written == t.written)))
        | map(t => t.written + " " + t.type)
}

match cards | filter(c => c.name == "knowledge-graph") | map(schema_of) | somes | first {
    some(s) => report(s),
    _ => {problem: "the card knowledge-graph carries no schema"},
}
