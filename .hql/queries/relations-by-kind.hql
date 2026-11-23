// status: valid-now
// vault: the root of this repository
// How many edges carry each relation; links with no annotation are "untyped".
graph.edges
| group(by = e => match e.data.relation { some(String r) => r, _ => "untyped" })
| sort(by = g => g.key)
| map(g => {relation: g.key, count: size(g.items)})
| Table(columns = ["relation", "count"])
| format(as = Markdown)
