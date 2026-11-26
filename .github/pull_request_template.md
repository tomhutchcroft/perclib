<!-- Title: begin with the task id ("<task-id>: short description"). Open as a draft to
claim the task; mark ready for review when done. See CONTRIBUTING.md. -->

**Task:** <!-- task id, or the frontier tag / issue this addresses -->

## What was proved

<!-- Declarations added or changed, with their tags; for each, proved or proved modulo
which `…Input` hypotheses. -->

## Checklist

- [ ] Title begins with the task id; branched from `main`; not in an area listed as taken in CONTRIBUTING.md (or coordinated there).
- [ ] Tags added or changed are listed (or "none").
- [ ] Searched-for lemmas listed: what I searched in mathlib and PercLib, and what I found.
- [ ] Gate result: `scripts/gate.sh main` run locally on the stated commit, final lines pasted
      below (the CI workflow `.github/workflows/ci.yml` runs on pull requests once it is
      on `main`; auto-merge is not active and a maintainer merges every pull request; see
      "Running the gate locally" in AGENTS.md).
- [ ] Interface changes listed below: every new or changed `def`, `structure`, `class`,
      `instance`, `abbrev`, notation or tagged statement, and every change outside
      `PercLib/` (or "none (proof-only)").
- [ ] No `sorry`, `admit`, `axiom`, `native_decide`, elaboration-time code,
      `set_option maxHeartbeats` or `set_option linter.*`.
- [ ] No tagged statement, or definition it uses, was narrowed or altered to make a proof close.
- [ ] New files are imported from `PercLib.lean`, start with a module docstring, and their
      headers carry only copyright, provenance and the mathematical reference.
- [ ] The task file is moved from `tasks/open/` to `tasks/done/` (if this completes a task).

## Searched for

## Gate result

<!-- Commit sha, then the final lines of `scripts/gate.sh main` (the `== gate passed on …`
line and any NOTICE line, or the failure). -->

## Interface changes
