# CI: known limitations of the lexical checks

## What is and is not a boundary

- **Correctness boundary.** Correctness rests on the kernel replay and the axiom audit
  (D-29). Every proof that reaches `main` is rechecked by the Lean kernel, and its axioms
  are compared with the allowed list (`propext`, `Classical.choice`, `Quot.sound`). No
  script described below replaces either check.
- **Who can be merged automatically.** `.github/workflows/automerge.yml` merges a pull
  request only when its author is listed in `.github/automerge-authors` (D-37, ruling
  10(2)), the CI run for its current head and base is green, and the change is proof-only
  by the classifier below. Changes by anyone else wait for a maintainer.
- **Lexical approximations.** Two scripts read Lean source without running Lean:
  - the forbidden-construct scanner (`scripts/check_forbidden.py`, through
    `scripts/check_proof_pr.py`);
  - the proof-only classifier (`scripts/automerge_classify.py`).

  Both approximate Lean's tokeniser. They are guard rails, not security boundaries. Where
  their reading of a file can differ from Lean's (a *desynchronisation*), text that Lean
  runs as code may look like a comment or a literal to them. The classes found so far are
  listed below.

## Desynchronisation classes found so far

"Refused" means the tool rejects the file, with a reason that names the lexical problem.

| class | what Lean does | scanner | classifier |
|---|---|---|---|
| S1: invalid escape in a string or character literal (`"\q …"`) | reports the escape, abandons the literal and lexes the rest as code | refused | refused |
| S2: `--`, `/-` or a character literal directly after a symbol (`<--`, `//-`, `]'"'`) | lexes the longest token, so the pair can be one token and the rest code | refused | refused |
| S3: a `'` that starts a character literal but fits none (`'-- …`, `+'a" …`) | reports an unterminated literal, skips the next two characters and resumes after them | refused | refused |
| S4: a raw string directly after a numeral (`2r"…"`) | reads the numeral `2` and then the raw string `r"…"` | refused | refused |
| S5: a token declared by the file itself (`notation "(--" …`) | lexes with the new token, which can swallow a comment opener | refused (`notation`, `infix`, … are forbidden) | refused (command keywords are forbidden on changed lines) |
| S6: identifier characters (`2'…'`, `x.1'…'`, `!'…'`, `x²'…'`) | starts a character literal after a numeral, a symbol or a non-Lean letter | refused | refused (Lean's `isIdFirst`/`isIdRest` and numeral rules) |
| S7: a numeral directly after `.` (`.1.e5'"' " -- " …`) | the parser reads a field index `1`, but error recovery reads the number `1.e5` | **known gap** | refused (both readings are checked) |

Earlier findings (a `--` inside `«…»`, code inside an interpolated string `s!"…{…}…"`) are
refused by both tools: `«…»` is copied whole, and a string containing `{` is rejected.

Every class above except S5 gives a Lean error at the point of desynchronisation.
`automerge.yml` needs a successful CI run, and the CI evidence is checked from the API,
not from the pull request's log, so it cannot merge such a file. The danger is
that the hidden code runs while CI builds the pull request.

## Untrusted text in the auto-merge log

This is not a lexer class: it concerns who can be merged. The `decide` step of
`automerge.yml` prints text that comes from the pull request (file names from the
pull-request files listing, and rejection reasons quoting them) to its log. A file name
can contain a newline, so without care a line such as `::set-output name=merge::true`
could reach the runner as a workflow command and forge the step outputs that the `merge`
job trusts. Two measures neutralise this:

- the step first prints `::stop-commands::` with a fresh random token that is never
  printed again, so the runner ignores workflow commands for the rest of the step; the
  outputs are written only to `$GITHUB_OUTPUT`, a file, which is not affected;
- `scripts/automerge_classify.py` prints every `Not merging: …` message with control
  characters escaped (`\n` for a newline), so no line of its output starts with text
  taken from the pull request; `scripts/test_automerge_classify.py` checks this.

## How a new class is handled

A new desynchronisation class found later is added to the table above. It is not treated
as a merge blocker for the workflows unless it does one of these:

- lets a change by an author not listed in `.github/automerge-authors` merge;
- lets pull-request code reach a token with write access.

Either of those is fixed before the workflows run again.

## Cancelled and shared CI runs

- **Cancellation.** A push to a branch other than `main` (today only the integration
  branch) cancels that branch's older CI run, and a new commit of a pull request cancels
  the pull request's older run. Push runs on `main` are never cancelled. An integration
  commit superseded within minutes therefore has no CI result of its own; this is safe
  because the newer commit contains it (or, after a force-push, the old commit is no
  longer on the branch) and the newer commit's run checks the whole tree, and anything
  reaching `main` is checked there again by its own uncancelled run.
- **Integration-branch pull requests reuse the push run.** In a pull request whose head is
  the integration branch of this repository, the jobs `gate` and `kernel-replay` do not
  build: each waits for the same job of the CI push run of the head commit and succeeds
  exactly when that job succeeded (they are never skipped, so a skipped `gate` cannot
  pass for a result). Both runs check out and check the same head commit, and the gate's
  pass or fail does not depend on the base, so the result is the same; only the
  advisory classification (against the previous tip instead of `main`) and the
  `manifest` artifact are taken from the push run instead. If the push run's job is
  re-run, re-run the pull request's job too. The cheap jobs `scripts` and `wiki` still run
  in both. Pull requests from forks, and from any other branch, are unaffected.
- **A waiting job can time out.** The waiting `gate` (or `kernel-replay`) of such a pull
  request has the same 360-minute limit as the push-run job it waits for, which is the
  most a job on a GitHub-hosted runner may run, so it cannot be raised to cover that job's
  queue time as well. If the push run's job is queued long or runs close to its limit, the
  pull request's job times out and fails (never passes). Re-run it after the push run has
  finished; it then reads the finished result at once. While it waits, each such job holds
  a runner without building.
