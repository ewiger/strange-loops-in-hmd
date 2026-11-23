/// Discussions: the working sessions of several agents, read from the headers
/// of the cards under `doc/discussion/`. The rules of a discussion and the
/// design of these headers are in `doc/discussion/README.hmd`.
module discussions

import core
import doc

/// The header of the observer's brief, the card that opens a discussion.
/// `opened` is `YYYY-MM-DD HH:MM`, read from a clock. `token` is the golden
/// token, absent for the discussions opened before the rule.
type Brief : Data {
    discussion : String
    opened     : String
    topic      : String
    observer   : String
    token?     : String
}

/// The header of a consolidation, the card that closes a discussion.
/// `conclusive` says whether the discussion reached what its brief set out
/// to do, and `outcome` says in one sentence what it came to.
type Closing : Data {
    discussion : String
    closed     : String
    conclusive : Bool
    outcome    : String
}

/// One discussion as the status report shows it.
type Row = {
    discussion : String
    opened     : String
    topic      : String
    status     : String
    conclusive : String
    closed     : String
    agents     : String
    token      : String
    outcome    : String
}

/// The brief a card carries, or none when the card is not a brief.
fn brief(c: Card) : List<Brief> = match c.metadata {
    Brief m => [m],
    _ => [],
}

/// The closing a card carries, or none when the card is not a consolidation.
fn closing(c: Card) : List<Closing> = match c.metadata {
    Closing m => [m],
    _ => [],
}

/// The folder of the discussion a card lies in: the second part of its
/// path, `SLH-D-0001-2026-11-23` for `discussion/SLH-D-0001-2026-11-23/bob.hmd`.
fn folder(c: Card) : String = c.path | split("/") | drop(1) | first | unwrap_or("")

/// When the discussion a brief opens was opened, or the empty string for a
/// card that is not a brief.
fn opened(c: Card) : String = brief(c) | map(m => m.opened) | first | unwrap_or("")

/// The agents that wrote in a discussion: the titles of the cards in its
/// folder, without the consolidation. An agent's file is titled by its name.
fn agents(all: List<Card>, at: String) : List<String> =
    all
    | filter(c => folder(c) == at and size(closing(c)) == 0)
    | map(c => c.title)
    | sort(by = n => n)
    | List

private fn yes_no(b: Bool) : String = match b {
    true => "yes",
    false => "no",
}

/// One brief with the closing of its discussion, if it has one, as a row.
fn row(all: List<Card>, c: Card, m: Brief) : Row {
    k = all | flat_map(closing) | find(k => k.discussion == m.discussion)
    Row(
        discussion = m.discussion,
        opened = m.opened,
        topic = m.topic,
        status = match k { some(x) => "closed", none => "open" },
        conclusive = match k { some(x) => yes_no(x.conclusive), none => "not yet" },
        closed = match k { some(x) => x.closed, none => "" },
        agents = agents(all, folder(c)) | join(", "),
        token = m.token.unwrap_or(""),
        outcome = match k { some(x) => x.outcome, none => "" },
    )
}

/// Every discussion among `all`, in the order they were opened.
fn discussions(all: List<Card>) : List<Row> =
    all
    | filter(c => size(brief(c)) > 0)
    | sort(by = opened)
    | flat_map(c => brief(c) | map(m => row(all, c, m)))
    | List

private fn line(cells: List<String>) : String = fmt("| {} |", cells | join(" | "))

private fn table(head: List<String>, rows: List<List<String>>) : String =
    [[line(head), line(head | map(h => "---"))], rows | map(line) | List]
    | flat_map(part => part)
    | join("\n")

/// The status report as a table: every discussion, in the order opened.
fn status_table(all: List<Card>) : String = table(
    ["Discussion", "Opened", "Topic", "Status", "Conclusive", "Agents"],
    discussions(all) | map(d => [d.discussion, d.opened, d.topic, d.status, d.conclusive, d.agents]) | List,
)

/// The closed discussions as a table: when each closed and what it came to.
fn closed_table(all: List<Card>) : String = table(
    ["Discussion", "Closed", "Outcome"],
    discussions(all) | filter(d => d.status == "closed") | map(d => [d.discussion, d.closed, d.outcome]) | List,
)

/// The open discussions as a table, with the golden token of each.
fn open_table(all: List<Card>) : String = table(
    ["Discussion", "Opened", "Topic", "Golden token", "Agents"],
    discussions(all) | filter(d => d.status == "open") | map(d => [d.discussion, d.opened, d.topic, d.token, d.agents]) | List,
)
