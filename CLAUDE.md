# CLAUDE.md

This repository is a HyperMarkDown (HMD) vault and an HQL project. We design HQL
syntax as we go, so some queries are written for a version of HQL that does not
exist yet.

## Before anything else: read the memories

The project is Strange Loops in HyperMarkdown, **SLH**.

At the start of every session, and before any task, read
`doc/memories/index.hmd` and every memory it lists. They hold what the user
has decided for good: names, conventions and standing instructions. A memory
outranks a habit, and where a memory and this file differ, say so to the
user.

Write a memory only when the user states something meant to hold from now
on, or asks for it to be remembered. The form is in `doc/memories/index.hmd`.

`doc/memories/` is the primary memory of this project. An agent's own
private memory, kept outside the repository by its tool, is secondary:

- Something meant to hold goes into `doc/memories/` first. The private
  memory may keep a short pointer to it and nothing more.
- Where the two disagree, `doc/memories/` is right, and the private entry is
  corrected or deleted.
- The private memory is for what cannot live in the repository.

## Layout

- `doc/memories/` holds the memories described above.

- `.hmd/` marks the root as an HMD vault.
- `.hql/` is the HQL project directory (configuration lives in
  `.hql/config.toml` once we add one).
- `.hql/queries/` is the library of HQL queries.
- `knowledge/` holds the knowledge base: the articles, written as HMD cards.
  It is the default vault (`.hmd/config.toml` points at it). The user writes
  these by hand: do not create or rewrite cards unless asked.
  Two folders in it are not concept cards. `knowledge/stars/` holds the
  north stars (category `star`), and `knowledge/meta/knowledge-graph.hmd`
  (category `meta`) describes the knowledge graph and holds its schema and its
  rules of inference in its header.
- `methodology/` describes the method behind claims, cross scores and north
  stars. It is documentation outside every vault, so its files are not cards.
- `scripts/` holds Python scripts for computations kept outside HQL:
  `derive.py` (derivation over the atoms) and `claim_distance.py` (distance
  between claim texts). They read the card headers directly.
- `scripts/lean/` holds the Lean proofs behind
  `methodology/distance-to-logic.hmd`. Check them with `lake build` in that
  folder. No proof may contain `sorry`.
- `.hql/lib/` holds the project's HQL modules: `claims` (claims read from
  card headers, and the scores) and `kg` (the typed graph and its check).
- `doc/` is a fourth HMD vault (it has its own `.hmd/`), so that its
  documents render and link in the editor. It holds stories, discussions,
  the ledger, proposals, issues and notes. It is not bound as an HQL endpoint.
- `doc/stories/` holds the stories: what the project is inventing, why, and
  how it got to where it is. The naming pattern and the parts of a story are
  in `doc/stories/index.hmd`. When work moves a story forward, bring its
  "So far", "Where it stands" and "Open" parts up to date in the same change.
- `doc/ledger/` is the annals: one entry for each committed change of state,
  with its objectives, what was accomplished, the decisions taken for good
  and the sidetracks. An entry goes into the commit it describes and is not
  edited afterwards. The form is in `doc/ledger/index.hmd`.
- `doc/discussion/` is where parallel sessions talk to each other. Each
  session has a name and writes only in its own file there. If other sessions
  are working in this repository, read `doc/discussion/index.hmd` before you
  change anything, report in the folder of the current discussion, and do not
  stage or commit while a discussion is open.
- `agents/` is a second HMD vault (it has its own `.hmd/`), holding agent
  cards. It is bound to the project as `[endpoint.agents]` in
  `.hql/config.toml` and read with `source("agents")`.
- `future/` is a third HMD vault, holding lens cards: designs that carry
  `import future`. It is bound as `[endpoint.future]` and read with
  `source("future")`. Never render a card in it.
- Links do not cross between vaults. A card that names a card of another vault
  names it, and a query joins the two by name.

## Claims

Each concept card carries its claims in its header, under `metadata.claims`.
The fields, the evidence grades and the rules for atoms are in
`methodology/claims.hmd` and `methodology/partial-logic.hmd`.

- A claim's `id` is never renumbered or reused: `card#id` is its address.
- When a card's text changes what it asserts, change its claims in the same
  edit.
- After changing claims, stars or the schema, run `schema-check.hql`,
  `star-cover.hql` and `atom-status.hql` from the query library.
- After changing atoms or the rules of inference, run `scripts/derive.py`
  and read its contradictions. The method is in `methodology/derivation.hmd`.

## Future queries: `import future`

A query that contains the line

```hql
import future
```

is a **future design**. It uses syntax or features the current HQL version does
not support, and it is expected to break if run.

- Never run a future query, and never run a card or query that imports one.
- Do not "fix" a future query so that it runs today. Its syntax is the design;
  keep it as written unless asked to change the design.
- When generating new queries, add `import future` whenever you use anything the
  current HQL does not support. Only leave it out when the query runs as is.
- When a future query is made to work on current HQL, remove `import future` in
  the same change.
- Before running any `.hql` file, check it for `import future`.

## Running HQL

`hql` runs the HQL implementation from `~/code/ai/hmd/hql` (a shell alias for
`cargo run` in that checkout). HQL docs and examples live in that repo's
`README.md` and `examples/`.
