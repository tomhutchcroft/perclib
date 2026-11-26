# Review: pull request #5, "lrp-I41-mt: mass-transport identity and cut-off corner" (head `1b29f93`)

Base of the pull request: `d1295a4`. Reviewed by a trial merge into the integration branch
`claude/zen-lovelace-rvlcw2` at `e0ae3ec`.

**Verdict: APPROVE WITH CHANGES** (three required changes, all small; see below).

Thank you for the contribution. The two files are clean, build without warnings, use only
the standard axioms, and follow the library's bond interface instead of introducing a second
model, which is exactly what the port needed.

## What the pull request does

- New `PercLib/Models/LongRange/MassTransportI41.lean` (994 lines, 38 theorems): translation
  of configurations as the push-forward `Sym2.map (· + t) '' ω`, translation invariance of
  the connection and cluster-volume integrands, the Russo triple weight of Lemma I.4.1 of
  *Critical long-range percolation I* (arXiv:2508.18807v1), its mass-transport rewriting
  (`massTransport_russo`, `lintegral_cluster_massTransport`,
  `lintegral_cluster_ball_massTransport`), the cut-off Russo derivatives
  (`hasDerivAt_expectation_cutoff`, `hasDerivAt_expectation_cutoff_cluster`), and the cut-off
  specialisation of Lemma I.2.6 (`rpow_div_le_integral_encard_cluster`).
- New `PercLib/Models/LongRange/CutoffCorner.lean` (529 lines, 20 theorems): one-sided
  derivatives of the cut-off profile of Definition I.1.5 and of the cut-off edge probability
  at the corner `r = ‖x − y‖`, and the absence of a two-sided derivative there.
- `PercLib.lean`: two import lines. `tasks/open/lrp-I41-mt.md` moved to `tasks/done/`.

## Classification

Proof-only, confirmed. The diff adds no `def`, `abbrev`, `structure`, `class`, `instance`,
`inductive` or attribute tag (the only attributes are `@[expose] public section`); every
source definition is written out inline in the statements. No existing file is changed
except the two import lines in `PercLib.lean` and the task file. No file under
`PercLib/Models/LongRange/**/Defs.lean`, `PercLib/Analysis/ModelNorm*` or
`PercLib/Probability/Dispersion/Defs.lean` is touched.

## Provenance

This is a port, not independent work: both headers say the files are adapted from
`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`
(source files `MassTransportI41.lean`, `CountableProduct/MassTransport.lean`,
`Tightness/LemmaI26Cutoff.lean`, `CutoffCorner.lean`, `KernelGeometry.lean`,
`CutoffRusso.lean`), Apache-2.0, upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0`, and they list the modifications. 21 of the 45 source theorem names are kept; the
rest are renamed or replaced by the library's existing notions, as the headers describe. The
header credit is complete. The ported-files register `docs/PORTED_FILES.md` does not yet list
the two files (change 2).

## Build and checks (on the trial merge)

- `lake build --wfail PercLib.Models.LongRange.CutoffCorner PercLib.Models.LongRange.MassTransportI41`:
  success, no warnings.
- `scripts/check_forbidden.py PercLib`: passed (404 files). `scripts/check_import_closure.py
  PercLib`: passed (404 modules).
- `#print axioms` on all 58 new theorems: each depends only on `propext`,
  `Classical.choice`, `Quot.sound`.
- `scripts/gate.sh` on the trial merge (full build, axiom audit, manifest, D-35 checks): passed.
- No `sorry`, `admit`, `axiom`, `native_decide` or `set_option`. Both files have a module
  docstring and section docstrings. No theorem has more than ten hypotheses (the most is
  five). Names follow mathlib conventions.

## Required changes

1. **Rebase onto the current integration branch.** The trial merge has two conflicts.
   `PercLib.lean`: a new import (`PercLib.Models.LongRange.LatticeConvolution`) sits on the
   same line; keep both. `tasks/open/lrp-I41-mt.md`: the integration branch has since moved
   this task to `tasks/claimed/`; please drop the task-file move from the pull request and
   leave the task board to the maintainers.
2. **Register the two files in `docs/PORTED_FILES.md`**, in the table for the critical
   long-range source, with their source paths, "code" in the Taken column and "complete" in
   the Header credit column. The library requires every ported file to be listed there as
   well as credited in its own header.
3. **Fill in the pull-request description** (it is the unfilled template): the source
   revision, the list of statement changes relative to the source (the headers already have
   most of this), and any premise kept as an explicit hypothesis that the paper does not
   state (or a statement that none is kept), so that no theorem is read as a proved result of
   the paper while such a premise remains.

## Suggestions (optional)

- The `CutoffCorner.lean` header names `CutoffRusso.lean` without its theorem names, unlike
  the other source files it lists; adding them would make the credit uniform.
- The paper reference is in the module docstrings; the headers could name it as well.

Merging port work from the outside long-range formalisation waits for the maintainer's
decision under the current long-range collaboration hold, independently of this review.

---
Generated by [Claude Code](https://claude.ai/code)
