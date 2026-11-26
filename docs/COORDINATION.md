# Coordination

**20 November 2026.** Rewritten under D-34, worker rules amended under D-35, which this file summarises and never
overrides. What has been decided is in [DECISIONS.md](DECISIONS.md). The current state,
the package list and anything waiting for Tom are in [STATUS.md](STATUS.md).

## Roles

| Role | Holder | Does |
|---|---|---|
| Mathematical lead | Tom Hutchcroft | Scope, fidelity of a target to its source, corrections to sources, publication. His word is final on everything. |
| ARCHITECT | Claude session | Architecture and `DECISIONS.md`. Escalations listed in D-34. |
| LEAD | One Claude Opus agent | Plans, starts workers, integrates, runs the gate, pushes, keeps `STATUS.md`. Writes no mathematics unless a merge needs a repair. |
| Worker | Claude Opus agent, one package | Prover, auditor, scout or wiki. |

## Rules for every worker

Every brief names the owned files, the exact target, the allowed inputs, the stop
condition and the hand-off (D-35). The rules below bind every package.

1. Work in your own git worktree on branch `work/<package>`, on the files your package
   names. Never edit another package's files, the pins or `STATUS.md`; edit
   `PercLib.lean` only to add the import lines of your own new modules.
2. Definitions go only in files named `Basic.lean` or `Defs.lean` (D-24). Search this
   library and mathlib before defining anything. A second definition of an existing
   notion is rejected whatever depends on it. A definition lands with its basic API:
   evaluation and membership lemmas, `@[simp]` where in normal form, `ext` for
   structures, monotonicity and the trivial case (D-35). If a statement would spell out
   the same predicate or quantity a third time, propose a definition for it as a small
   interface package instead; this is encouraged.
3. Search before writing (D-35): for any lemma that does not mention percolation, search
   mathlib by name and by type (`exact?`, `rg` in `.lake/packages/mathlib`) and search
   `PercLib`, and say in the report what was searched. A private copy of a lemma that
   exists elsewhere in the library is rejected; import it.
4. Generality when it is free (D-35): state a lemma at the generality its proof supports
   when that costs nothing (an arbitrary index type or measure, a general profile, a
   `SimpleGraph`); the wiki-facing form is a corollary. A notion mathlib has is used
   through mathlib's API, never re-encoded as ad hoc hypotheses. A theorem with more
   than ten hypotheses is reported with the reason; a recurring group of hypotheses
   becomes a structure.
5. Names follow mathlib (D-35): the name describes the conclusion, hypotheses are added
   with `_of_`, the namespace is the most specific one that gives dot notation. A tag,
   package or work-item identifier never appears in a declaration name.
6. `Tags/` files are a correspondence layer (D-35): a tagged statement there restates
   library lemmas and adds no mathematics; each conjunct of a tagged conjunction is also
   a named lemma in the area file, and downstream code uses that lemma, never the
   tagged conjunction.
7. Statements are on the bond interface of D-2 and faithful to the wiki assertion or
   the cited source. A tagged statement, or a definition it uses, is never narrowed or
   altered to make a proof close: if it is false, vacuous or needs a hypothesis the
   source lacks, stop and report it with the counterexample. Narrowing is for helper
   lemmas only.
8. No `sorry`, `admit`, `axiom`, `native_decide`, code that runs at elaboration time
   (D-29), `set_option maxHeartbeats` or `set_option linter.*` (D-35). A result of the
   literature is used only as an explicit `…Input` hypothesis listed in
   `docs/CITED_INPUTS.md` (D-4), and a target with such an input is reported as proved
   modulo, never as proved. A tagged `Prop` statement is never a hypothesis; its proof
   carries the same tag (D-16).
9. Build only the modules you changed (`lake build --wfail PercLib.Your.Module`). Do not
   run a full build; LEAD does. Do not kill a build you did not start.
10. Commit when it compiles; what compiles is committed and the rest is described in the
    report.
11. New files begin, after the imports, with a module docstring `/-! # Title … ## Main
    results -/`. File headers carry provenance (source, revision, licence, D-6) and the
    mathematical reference only, never package, issue, agent or decision identifiers;
    those go in the commit message (D-35).
12. Report at the end: branch and commit; declarations added, with tags; every new or
    changed definition and tagged statement; what was searched; what was built and the
    result; what is not done; approaches that failed and why.

Interface audits are binder tables (D-35): for every tagged statement the auditor
classes each binder, including the fields of any project structure it unfolds to, as
SOURCE, TYPING, RULED (a recorded erratum) or EXCESS; any EXCESS fails, and the order of
existential quantifiers is checked against every parameter a constant must not depend on.

## The gate (LEAD)

On the merged tree, before the integration branch moves, from the repository root with
`~/.elan/bin` on `PATH` (corrected 20 November 2026 against `scripts/` and the old CI
workflow; every command below was run on this machine):

```sh
scripts/gate.sh <integration-tip>      # runs, in order, stopping at the first failure:
  lake build --wfail
  lake env lean --run scripts/AxiomAudit.lean          # every constant under PercLib
  python3 scripts/check_import_closure.py PercLib
  python3 scripts/check_forbidden.py PercLib           # D-29/D-35 forbidden-construct scan
  python3 scripts/test_proof_pr.py
  lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json
  python3 scripts/check_d35.py .lake/manifest-raw.json  # D-35 gate additions (i), (iv), (v)
  python3 scripts/check_proof_pr.py --base <tip> --base-raw .lake/gate/<tip>.json
```

`check_d35.py` exempts the files listed in `scripts/legacy_headers.txt` from the header
checks until the header migration has run, and the declarations in
`scripts/d35_exceptions.txt` (tagged statements used as hypotheses) until package
`d35-binders` removes them; both lists only shrink.
`AxiomAudit.lean` allows only `propext`, `Classical.choice` and `Quot.sound` and covers
private declarations (a `sorry` appears as `sorryAx`). `ExtractManifest.lean` is the
declaration extract; it records axioms of tagged declarations only, so it is not the
audit. `check_proof_pr.py` classifies the change against the tip: exit 0 proof-only,
exit 3 interface (needs a fresh auditor's approval, D-34). `gate.sh` saves the extract
of each clean gated commit as `.lake/gate/<sha>.json`, which is what the next
classification compares against. Kernel replay (D-29), before every milestone push,
never alongside a build:

```sh
scripts/kernel_replay.sh        # leanchecker, 12 modules per process
```

`lake env leanchecker PercLib` in one process exceeds 15 GB and is killed; do not use
it. Measured on 20 November 2026 (4 cores, 15 GB): full library build from a warm
mathlib cache 4 min 23 s; axiom audit 52 s; extract 74 s; kernel replay 14 min 9 s
with a peak of about 9.7 GB at 12 modules per batch (use `scripts/kernel_replay.sh 6`
while provers are building); see
`STATUS.md`. Results are recorded in `STATUS.md` with the commit, as local verification.

## Reporting

"Proved" means D-4 `proved` on a named commit that passed the gate. "Proved modulo"
names the inputs. A draft that has not compiled is called an uncompiled draft. Nothing
on the integration branch describes unmerged work as present (D-10).
