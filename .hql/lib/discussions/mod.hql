/// Discussions: the working sessions of several agents, read from the folders
/// under `doc/discussion/` and from the headers of two cards in each. The
/// design is in `doc/discussion/README.hmd`.
///
/// A discussion is a folder. Its rows are built from the folders, and the
/// headers are joined to them, so a header that does not fit can never make
/// a discussion disappear: the row stays, and `problems` says what is wrong.
module discussions

import core
import doc
from regex import is_match

/// Any header that says what kind of card it is on.
type Tagged : Data {
    category : String
}

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
/// `conclusive` says whether the discussion did what its brief set out to
/// do. `returned` names the workers who returned the golden token.
type Closing : Data {
    discussion : String
    closed     : String
    conclusive : Bool
    outcome    : String
    returned?  : List<String>
}

/// One discussion as the status report shows it. `missing` names the
/// workers of a closed discussion who did not return its token.
type Row = {
    discussion : String
    folder     : String
    opened     : String
    topic      : String
    status     : String
    conclusive : String
    closed     : String
    agents     : String
    token      : String
    outcome    : String
    missing    : String
}

/// Something in the folders or the headers that does not fit the design.
type Problem = {
    at      : String
    problem : String
}

private fn parts(c: Card) : List<String> = c.path | split("/")

/// The folder of the discussion a card lies in, or the empty string for a
/// card that does not lie directly in a discussion's folder.
fn folder(c: Card) : String = match size(parts(c)) == 3 and (parts(c) | first | unwrap_or("")) == "discussion" {
    true => parts(c) | drop(1) | first | unwrap_or(""),
    false => "",
}

/// The name of a card's file without its ending: `bob` for `bob.hmd`.
fn stem(c: Card) : String = parts(c) | last | unwrap_or("") | trim_suffix(".hmd")

/// The name of a discussion, taken from its folder: `SLH-D-0004`.
fn number(f: String) : String = f | slice(0, 10)

/// The category a card's header states, or the empty string.
fn category(c: Card) : String = match c.metadata {
    Tagged m => m.category,
    _ => "",
}

/// The brief a card carries: its header, when the card says it is a
/// discussion and the header has every field a brief needs.
fn brief(c: Card) : List<Brief> = match category(c) == "discussion" {
    true => match c.metadata {
        Brief m => [m],
        _ => [],
    },
    false => [],
}

/// The closing a card carries: its header, when the card says it is a
/// consolidation and the header has every field a closing needs.
fn closing(c: Card) : List<Closing> = match category(c) == "consolidation" {
    true => match c.metadata {
        Closing m => [m],
        _ => [],
    },
    false => [],
}

/// The folders of all discussions, in the order of their numbers.
fn folders(all: List<Card>) : List<String> =
    all
    | map(folder)
    | filter(f => starts_with(f, "SLH-D-"))
    | distinct
    | sort(by = f => f)
    | List

/// The cards that lie directly in the folder `f`.
fn members(all: List<Card>, f: String) : List<Card> = all | filter(c => folder(c) == f) | List

/// The agents of a discussion: one for each file in its folder, named by
/// the file, without the consolidation and without any card whose category
/// is `report`.
fn agents(m: List<Card>) : List<String> =
    m
    | filter(c => category(c) != "report")
    | map(stem)
    | filter(s => s != "consolidation")
    | map(s => capitalize(s))
    | sort(by = n => n)
    | List

private fn yes_no(b: Bool) : String = match b {
    true => "yes",
    false => "no",
}

/// The workers of a closed discussion that has a token who are not named
/// under `returned` in its consolidation.
fn missing(m: List<Card>) : List<String> {
    b = m | flat_map(brief) | List
    k = m | filter(c => stem(c) == "consolidation") | flat_map(closing) | List
    token = b | map(x => x.token.unwrap_or("")) | first | unwrap_or("")
    observer = b | map(x => x.observer) | first | unwrap_or("")
    back = k | flat_map(x => x.returned.unwrap_or([])) | List
    match token != "" and size(m | filter(c => stem(c) == "consolidation")) > 0 {
        true => agents(m) | filter(a => a != observer and not contains(back, a)) | List,
        false => [],
    }
}

/// The folder `f` as a row. A discussion is closed when its folder holds a
/// file `consolidation.hmd`, whatever that file's header says.
fn row(all: List<Card>, f: String) : Row {
    m = members(all, f)
    b = m | flat_map(brief) | List
    closed = size(m | filter(c => stem(c) == "consolidation")) > 0
    k = m | filter(c => stem(c) == "consolidation") | flat_map(closing) | List
    Row(
        discussion = number(f),
        folder = f,
        opened = b | map(x => x.opened) | first | unwrap_or("?"),
        topic = b | map(x => x.topic) | first | unwrap_or("(no brief with a header that fits)"),
        status = match closed { true => "closed", false => "open" },
        conclusive = match closed {
            true => k | map(x => yes_no(x.conclusive)) | first | unwrap_or("?"),
            false => "not yet",
        },
        closed = match closed {
            true => k | map(x => x.closed) | first | unwrap_or("?"),
            false => "",
        },
        agents = agents(m) | join(", "),
        token = b | map(x => x.token.unwrap_or("")) | first | unwrap_or(""),
        outcome = match closed {
            true => k | map(x => x.outcome) | first | unwrap_or("(the header of the consolidation does not fit)"),
            false => "",
        },
        missing = missing(m) | join(", "),
    )
}

/// Every discussion among `all`, in the order of their numbers.
fn discussions(all: List<Card>) : List<Row> = folders(all) | map(f => row(all, f)) | List

private fn is_time(s: String) : Bool = is_match(s, "^[0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}$")

private fn named(f: String) : List<String> = f | split("-")

/// The time a folder's name states, as a header writes it, or the empty
/// string for a folder named before the rule.
fn time_in_name(f: String) : String = match size(named(f)) >= 8 {
    true => fmt(
        "{}-{}-{} {}:{}",
        named(f) | drop(3) | first | unwrap_or(""),
        named(f) | drop(4) | first | unwrap_or(""),
        named(f) | drop(5) | first | unwrap_or(""),
        named(f) | drop(6) | first | unwrap_or("") | slice(0, 2),
        named(f) | drop(6) | first | unwrap_or("") | slice(2, 4),
    ),
    false => "",
}

/// The token a folder's name states, or the empty string.
fn token_in_name(f: String) : String = match size(named(f)) >= 8 {
    true => named(f) | drop(7) | first | unwrap_or(""),
    false => "",
}

private fn when(test: Bool, at: String, problem: String) : List<Problem> = match test {
    true => [Problem(at = at, problem = problem)],
    false => [],
}

/// What is wrong with the folder `f` and the two headers in it.
fn problems_of(all: List<Card>, f: String) : List<Problem> {
    m = members(all, f)
    tagged = m | filter(c => category(c) == "discussion") | List
    b = m | flat_map(brief) | List
    ends = m | filter(c => stem(c) == "consolidation") | List
    k = ends | flat_map(closing) | List
    r = row(all, f)
    [
        when(size(tagged) == 0, f, "no brief: no card in the folder has the category discussion"),
        when(size(tagged) > 0 and size(b) == 0, f, "the brief's header does not fit: it needs discussion, opened, topic and observer, each as text"),
        when(size(b) > 1, f, "more than one brief"),
        b | flat_map(x => when(x.discussion != number(f), f, fmt("the brief says {} and the folder says {}", x.discussion, number(f)))),
        b | flat_map(x => when(not is_time(x.opened), f, fmt("opened is not a date and a time to the minute: {}", x.opened))),
        b | flat_map(x => when(time_in_name(f) != "" and time_in_name(f) != x.opened, f, fmt("the brief says it opened at {} and the folder's name says {}", x.opened, time_in_name(f)))),
        b | flat_map(x => when(time_in_name(f) != "" and token_in_name(f) != x.token.unwrap_or(""), f, fmt("the brief's token is '{}' and the folder's name says '{}'", x.token.unwrap_or(""), token_in_name(f)))),
        when(size(ends) > 0 and size(k) == 0, f, "the consolidation's header does not fit: it needs category consolidation, discussion, closed and outcome as text, and conclusive as true or false"),
        k | flat_map(x => when(x.discussion != number(f), f, fmt("the consolidation says {} and the folder says {}", x.discussion, number(f)))),
        k | flat_map(x => when(not is_time(x.closed), f, fmt("closed is not a date and a time to the minute: {}", x.closed))),
        k | flat_map(x => when(is_time(x.closed) and is_time(r.opened) and x.closed < r.opened, f, "it closed before it opened")),
        when(r.missing != "", f, fmt("closed, but the token was not returned by: {}", r.missing)),
        m | flat_map(c => when(category(c) == "consolidation" and stem(c) != "consolidation", c.path, "has the category consolidation and is not the file consolidation.hmd")),
    ]
    | flat_map(p => p)
    | List
}

/// Everything that does not fit, over all discussions: each folder's own
/// problems, and a token that two discussions use.
fn problems(all: List<Card>) : List<Problem> {
    rows = discussions(all)
    [
        folders(all) | flat_map(f => problems_of(all, f)) | List,
        rows | flat_map(a => when(a.token != "" and size(rows | filter(b => b.token == a.token)) > 1, a.folder, fmt("the token '{}' is used by more than one discussion", a.token))) | List,
        all | flat_map(c => when(folder(c) == "" and (category(c) == "discussion" or category(c) == "consolidation"), c.path, "has the header of a brief or a consolidation and does not lie in a discussion's folder")) | List,
    ]
    | flat_map(p => p)
    | List
}

private fn cell(s: String) : String = s | replace_all("|", "\\|") | replace_all("\n", " ")

private fn line(cells: List<String>) : String = fmt("| {} |", cells | map(cell) | join(" | "))

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
fn open_table(all: List<Card>) : String = match size(discussions(all) | filter(d => d.status == "open")) {
    0 => "No discussion is open.",
    _ => table(
        ["Discussion", "Opened", "Topic", "Golden token", "Agents so far"],
        discussions(all) | filter(d => d.status == "open") | map(d => [d.discussion, d.opened, d.topic, d.token, d.agents]) | List,
    ),
}

/// The counts as a table: all, open, closed, and of the closed the
/// conclusive ones.
fn counts_table(all: List<Card>) : String {
    rows = discussions(all)
    table(
        ["Discussions", "Open", "Closed", "Of the closed, conclusive"],
        [[
            fmt("{}", size(rows)),
            fmt("{}", rows | filter(d => d.status == "open") | size),
            fmt("{}", rows | filter(d => d.status == "closed") | size),
            fmt("{}", rows | filter(d => d.conclusive == "yes") | size),
        ]],
    )
}

/// The problems as a table, or one line saying there are none.
fn problems_table(all: List<Card>) : String = match size(problems(all)) {
    0 => "No problems: every folder and header fits the design.",
    _ => table(["Where", "Problem"], problems(all) | map(p => [p.at, p.problem]) | List),
}
