# Agent policy: what a thread may decide, and what it asks

Status: **direction adopted by Minus, 2026-11-02; the details below are a
draft for his review.** Nothing in it is enforced by tooling yet; each
mechanism has an issue (§8). Until then, threads follow it by reading it,
the way they follow `CLAUDE.md`.

A *thread* here is any agent session working on Heather: a Projects thread
today, a session of Minus's own harness later. The policy is written against
the tracker and the repository, not against either tool, so it holds across
both.

This file owns four things: **when enabling work may start without a
puller** (§1), **how a thread says the foundation is hurting it, and what
happens next** (§2–§4), **how review effort is spent** (§5), and **which
changes merge without review** (§6). It links to the roadmap, the tracker
and the design docs rather than restating them (`issues/README.md`, rule 1).

## Why this exists

Minus's ask (2026-11-02), after a review of how the tracker had grown:

- The roadmap's rule that enabling work waits until a milestone pulls it
  encouraged doing the minimal work a feature needed. The result was
  "working garbage": native code that had to be burned because it had
  accumulated feature-shaped patches on a foundation nobody owned.
- Large PRs are more than 90% good, but reading all of them to find the rest
  costs more time than writing them did.
- An implementation round that hits a weak foundation has no legitimate way
  to say "this sucks without X" and wait for X, so it works around X instead.
- The backlog loses track of itself: on 2026-11-02, 379 of 525 open issues
  served no milestone, most of them in `language`, `kernel` and
  `infrastructure`, with a median of over a month since their last update.
- Requiring a PR for tracker bookkeeping is ceremony with no reviewer.

## 1. Enabling work invests ahead of demand

The enabling areas (`language`, `kernel`, `infrastructure`) are no longer
only pulled. They build, **at their proper general design**, what the
directions predictably need, before a direction is blocked on it.

- **Predicted needs.** An enabling issue is *wanted* when two or more
  directions will clearly need it, or when Minus says so. It carries the
  label `wanted`. Wanted work may be picked up with no direction milestone
  pulling on it.
- **Enabling milestones.** Each enabling area should have milestones of its
  own, judged by what they unlock (an inner loop fast enough to iterate in,
  a layer general enough that clients stop restating it), the way
  `lang-sequencing` and `lang-proof-modularity` already are. Proposing them
  is [enabling-area-directions](../issues/enabling-area-directions.md).
- **The general design, not the minimal one.** A round that builds a
  foundation builds the layer properly, even when its customer needs one
  case of it. A narrower slice is a decision the round records (in its issue
  or design doc), not a default.

Priority still decides how effort splits when it must. It no longer means
"never".

## 2. Dependency requests: "this sucks without X"

When a round finds that a missing or weak foundation is hurting it, it says
so in the tracker rather than working around it silently. A request is a
link from the requesting issue to the issue that would fix it, with one of
three kinds:

| field | kind | meaning |
|---|---|---|
| `blocked-by:` | blocks | The round cannot proceed. (The field already exists.) |
| `degraded-by:` | degrades | The round can proceed, but the result will be worse code: duplicated lemmas, a special case where a general one belongs, a proof that will not survive the next change. |
| `slowed-by:` | slows | Iteration cost is the problem: elaboration, checking or build time is making the round slow to work in. |

The request names the dependency's issue (filing it if none exists) and
logs one line on the requesting issue saying what hurts and why. The
dependency's own issue owns the design; the request owns only the claim
that this round needs it.

Mechanics, validation in `scripts/issue check`, and a `wants` overview are
[dependency-requests](../issues/dependency-requests.md).

## 3. What is decided without Minus

A request is **granted by default** when the dependency is any of:

- **Already wanted**: it serves an open milestone, is labelled `wanted`,
  is starred by Minus, or is listed under an area note's gaps
  ([area-notes-and-roadmap-map](../issues/area-notes-and-roadmap-map.md)).
- **An obvious fix**: small, inside the requesting round's own area, with
  no design question in it (a missing lemma in the module it is working in,
  a diagnostic that lies, a cost the issue already explains).

Granted means the dependency gets worked on next, by this thread or a
separate one, built per §1, and the grant is logged on both issues.

Everything else **asks Minus**: a dependency that is new, crosses into
another area, changes a design doc's decision, or would start a round that
was not planned. The ask is one short entry: what hurts, the dependency,
its kind, and the three options (approve, defer, work around). Until he
answers, the thread proceeds as in §4 with the option that loses the least.

Two guards hold in every case:

- **Depth.** A granted dependency's own requests are granted by default only
  one level down. Past that the thread asks, so that a request cannot turn
  into a rewrite of the project.
- **Capacity.** Granted work counts against the same concurrency Minus has
  set for threads; a grant does not license an extra parallel round.

Widening a default (when Minus approves the same kind of request a third
time) is an edit to this section.

## 4. How a round proceeds while it waits

A round with a granted or pending request picks one of three, and logs
which:

1. **Park.** Stop, record where the round stands in its issue, and resume
   when the dependency merges. Right for `blocks`.
2. **Stack.** Branch on top of the dependency's branch and continue, with
   the PR targeting that branch until it merges, then master. This is
   "waiting on another PR" without stopping, and it keeps both PRs small.
   Right for `degrades` when the dependency's interface is already settled.
3. **Work around, visibly.** Proceed with a workaround, and mark every
   place it lives with a comment naming the issue that would retire it:

   ```
   // workaround: [[real-completeness-interfaces]]
   ```

   (the same `//` comment in Rust and in `.hthr`). A workaround with no
   marker is a defect in review. Markers are counted per area and milestone,
   and a milestone is not marked done while markers point at open issues
   that serve it, unless Minus waives them in the roadmap's log. Tooling is
   [workaround-markers](../issues/workaround-markers.md).

Silent workarounds are what turned native code into working garbage. The
point of the third option is not to forbid workarounds but to give each one
an owner and a visible count.

## 5. Review by trust boundary

Review effort goes where errors can hide. Heather's kernel makes that
sharply uneven:

- **Library proofs** (`lib/`): if the kernel accepts it, the proof is right.
  Review the *statements*: every new or changed theorem, definition
  signature, axiom and class field, for whether it says what was wanted at
  the right generality. Proof bodies are skimmed for style at most.
- **Kernel Rust** (`crates/kernel/`): the trusted base. Read in full.
- **Elaborator and compiler Rust** (`crates/elab/`, `crates/cli/`): the
  kernel or a certificate backstops their output, so a bug costs a refusal,
  not unsoundness. Review the design and the risky hunks; skim the rest.
- **Generated or certified output** (native certificates, generated terms):
  review the generator and its soundness statement, not the copies (the
  principle in `docs/compilation-vision.md`).

A PR description should open with this split: the statements it adds or
changes, the kernel lines it touches, and the rest by kind. A separate
reviewer thread may pre-read a PR and flag the hunks it is least sure of;
its job is to point at the suspect part, not to approve the rest. Tooling
that extracts the statements and collapses proofs is
[review-by-trust-boundary](../issues/review-by-trust-boundary.md).

## 6. What merges without review

The line is **bookkeeping versus decisions**.

**Bookkeeping merges without review**, through an automatically merged PR
or a direct push guarded by a path check ([bookkeeping-auto-merge](../issues/bookkeeping-auto-merge.md)):

- `issues/*.md`: new issues, log entries, status, links, retagging;
- area notes' observations and health fields;
- workaround-marker counts and other generated summaries, if committed.

The suite is not run for these; `CLAUDE.md` already says docs-only and
issue-only changes need none. `scripts/issue check` is run, and must pass.

**Decisions get a look**, batched rather than one PR each where possible:

- design docs (`docs/*-design.md`, proposals, round notes that record a
  choice);
- `docs/roadmap.md`'s tables (priority, tiers, milestones and their "done
  when") and its log;
- this file and `CLAUDE.md`.

A PR that mixes the two is reviewed as a decision. A round that wants its
bookkeeping to land fast puts it in its own commit or PR.

## 7. Automated tracker management

A scheduled gardener pass keeps the tracker tied together. Its actions are
split the same way as §6.

**Applied directly, and listed in its digest:**

- adding wiki links between issues that cite the same files, code
  references or declarations;
- setting `area:` on an open issue when exactly one area fits;
- flagging likely duplicates (a log line on each, not a merge);
- the two checks `issues/README.md` asks for by hand: open issues whose last
  log says landed or done, and open issues nothing links to;
- flagging area notes whose assessment predates closed work in their area.

**Proposed, for Minus to accept in batches:**

- closing an issue, or merging duplicates;
- adding or changing a milestone;
- adding `wanted`;
- marking an issue *intentionally unplaced* (`milestone: [none]`), which
  takes it out of the unplaced count;
- promoting a cluster of related issues into a predicted need.

Batches are grouped by cluster, about twenty issues at a time, so that each
is one decision rather than twenty unrelated ones. The gardener's checks are
[tracker-gardener](../issues/tracker-gardener.md).

## 8. Issues

| issue | owns |
|---|---|
| [dependency-requests](../issues/dependency-requests.md) | `degraded-by:` and `slowed-by:`, their validation, and a view of open requests |
| [workaround-markers](../issues/workaround-markers.md) | the marker form, the check that its slug exists, counts per area and milestone, the done-gate |
| [bookkeeping-auto-merge](../issues/bookkeeping-auto-merge.md) | merging bookkeeping-only changes without review, and its path check |
| [tracker-gardener](../issues/tracker-gardener.md) | the automated checks and proposals of §7 |
| [area-notes-and-roadmap-map](../issues/area-notes-and-roadmap-map.md) | per-area assessed notes and the roadmap map view |
| [review-by-trust-boundary](../issues/review-by-trust-boundary.md) | the PR review view of §5 |
| [enabling-area-directions](../issues/enabling-area-directions.md) | directions and milestones for `language`, `kernel` and `infrastructure` |

## Changing this file

It is a decision file (§6). When a default in §3 is widened or narrowed,
say why in one line here.

## Log

- 2026-11-02: Drafted from Minus's ask; direction adopted, details pending
  his review. The roadmap's enabling-tier rule is changed to point here.
