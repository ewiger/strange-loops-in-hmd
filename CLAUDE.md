# CLAUDE.md

This repository is a HyperMarkDown (HMD) vault and an HQL project. We design HQL
syntax as we go, so some queries are written for a version of HQL that does not
exist yet.

## Layout

- `.hmd/` marks the root as an HMD vault.
- `.hql/` is the HQL project directory (configuration lives in
  `.hql/config.toml` once we add one).
- `.hql/queries/` is the library of HQL queries.
- `wiki/` holds the articles, written as HMD cards. The user writes these by
  hand: do not create or rewrite cards unless asked.
- `agents/` is a second HMD vault (it has its own `.hmd/`), holding agent
  cards. It is bound to the project as `[endpoint.agents]` in
  `.hql/config.toml` and read with `source("agents")`. Links do not cross
  between the two vaults.

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
