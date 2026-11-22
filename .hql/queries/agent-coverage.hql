// status: valid-now
// vault: agents (run with `--vault agents --project .` from the repository root)
// What the base agent's card declares it performs, against the operation
// cards that exist in the knowledge base. The two vaults are separate
// namespaces, so the comparison is a join by name and not a link.

fn is_kind(e: Edge, kind: String) : Bool =
    match e.data.relation { some(String r) => r == kind, _ => false }

declared = @[[base-agent]] | uplinks | filter(e => is_kind(e, "performs")) | map(e => e.target) | List

kb = source("knowledge")
available = kb.graph.edges
    | filter(e => e.target == "cognitive-operation" and is_kind(e, "instance-of"))
    | map(e => e.source)
    | sort(by = n => n)
    | List

{
    declared: size(declared),
    available: size(available),
    declared_but_missing: declared | filter(n => not contains(available, n)),
    available_but_undeclared: available | filter(n => not contains(declared, n))
}
