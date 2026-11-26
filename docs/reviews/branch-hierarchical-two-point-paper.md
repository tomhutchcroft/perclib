# Review: branch `work/hierarchical-two-point-paper` (head `be2b9df`)

Base of the branch: `main` at `1df822a`. Reviewed against the integration branch
`claude/zen-lovelace-rvlcw2` at `622c846`.

**Verdict: MERGEABLE AFTER CHANGES** (two required changes, both small; see below).

Thank you for the contribution. The triangle recursion is new to the library and is
proved cleanly; the translation-invariant first-exit bounds are correct, but the
integration branch has meanwhile gained the same results in a separate file, so that
part should be dropped rather than merged.

## What the branch does

Two commits, three files (no scripts, no tooling, no pins, no `.github/` changes):

1. New `PercLib/Models/HierarchicalTriangle.lean` (86 lines), standalone algebra over `ℝ`:
   - `hierarchical_triangle_extension`: for a kernel `K` on a finite block `X` with constant
     row and column sums `s`, glued into `b + 1` copies with constant off-block entry `t`,
     the rooted row sum is `s + b M t` and the rooted triangle is
     `∑ K K K + 3 b M s t² + b (b - 1) M² t³` (`M = |X|`).
   - `hierarchical_triangle_geometric`: solving the resulting recursions for a geometric
     profile `c rⁿ`: closed forms for `S N` and `D N` as two geometric sums, including the
     marginal case (no division by `B r - 1`).
2. `PercLib/Models/HierarchicalTwoPointUpper.lean`: the six first-exit theorems
   (`tsum_localConn_ball_eq`, `law_localConn_ball_succ_le`, `tau_le_localConn_ball_add`, and
   the three power-law forms) are re-proved under translation invariance of `J`
   (`hshift : ∀ g e, J (Sym2.map (Equiv.addRight g) e) = J e`) plus a radial majorant
   `J s(a, y) ≤ K (h (y - a))` for `a ≠ y`, under new names with suffix `_of_translation`;
   the old radial names are re-added as one-line corollaries.
3. `PercLib.lean`: one import line.

## 1. Classification: proof-only

- No `def`, `structure`, `instance`, notation or `@[tag]`.
- The six re-added old names have statements textually identical (up to whitespace) to
  their statements at the branch base `1df822a`; their binder order (`J f hJ …`) is
  unchanged (checked with `#check` after the trial merge). Only their proofs changed.
- Six new public theorems and a new module.

So the branch is proof-only in the sense of CONTRIBUTING.md. (Against the integration
branch the old names are spelled with `localConn`; after the respelling in required change 1
they would again match exactly, though change 1 makes the point moot.)

## 2. Trial merge into `claude/zen-lovelace-rvlcw2` (`622c846`)

`git merge --no-commit` reports conflicts in two files:

| File | Hunk | Cause |
|---|---|---|
| `PercLib.lean` | the import block after `HierarchicalSymmetry` | both sides add an import at the same place (`HierarchicalTranslation` on the integration branch, `HierarchicalTriangle` here). Resolution: keep both lines, alphabetical. |
| `HierarchicalTwoPointUpper.lean` | `variable` block (line ~60) | the integration branch removed `setOf_localConn_comm` (replaced by `localConn_comm` in `PercLib/Percolation/Bond/Basic.lean`) and respaced `s(x, y)`; the branch replaces `f`/`hJ` by `hshift` next to it. |
| same | `hPsum` inside `law_localConn_ball_succ_le_of_translation` | the integration branch spells the event `localConn A 0 z`; the branch keeps the unfolded set and calls the renamed lemma. |
| same | end of the old `law_localConn_ball_succ_le_powerLaw` | same respelling against the branch's new proof term. |

Git also auto-merged the respelling into parts of the moved code inconsistently: the
re-added old-name theorems at the end of the file come out half in the unfolded
`{ω | ∃ h0 …, ((openGraph ω).induce S).Reachable …}` form and half in `localConn S x y` form.
The forms are definitionally equal, so it elaborates either way, but the integration branch
spells every such statement with `localConn` (the "localConn fold").

A mechanical resolution exists (variable block with `hshift` only; `hPsum` as
`∑' z, law q (localConn A 0 z)` via `tsum_localConn_ball_eq_of_translation J hshift`; old-name
statements copied from the integration branch). I did this in a scratch worktree only.

## 3. Build and checks (scratch merge, toolchain and mathlib as pinned)

- `lake build --wfail PercLib.Models.HierarchicalTriangle`: **fails on linter warnings
  only**: 15 × `linter.style.whitespace` ("missing space") in the statement of
  `hierarchical_triangle_geometric` (lines 67–70: `n+1`, `B-1`, `B^n`, `c*r^n`, `(B^n)^2` …).
  With those lines respaced as in required change 2, the module builds with no warnings.
- `lake build --wfail PercLib.Models.HierarchicalTwoPointUpper PercLib.Models.HierarchicalTranslation`
  (the only importer of `HierarchicalTwoPointUpper`): elaborates, but **fails on linter
  warnings**: 17 × `linter.style.longLine` (> 100 characters) and 11 × `linter.style.whitespace`
  (`s(a,y)`, `(y-a)`), all on lines the branch adds or changes. `HierarchicalTranslation`
  builds.
- `#print axioms` on all eight new public theorems: only `propext`, `Classical.choice`,
  `Quot.sound`.
- `python3 scripts/check_forbidden.py PercLib`: passed. `check_import_closure.py`: passed.
  The new file has a module docstring and no labels in its header (the D-35 header checks of
  `scripts/check_d35.py` would pass on it).
- The full `scripts/gate.sh` was not run: its first step (`lake build --wfail`) is already
  known to fail on the warnings above, and it rebuilds the whole library.

## 4. Overlap with work already on the integration branch

- **Duplicates.** Since this branch was cut, the integration branch has gained
  `PercLib/Models/HierarchicalTranslation.lean`, which proves the same translation-invariant
  first-exit bounds, with the same majorant hypothesis
  `∀ u v, u ≠ v → J s(u, v) ≤ K (h (v - u))` and the pointwise invariance
  `hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)` (equivalent to `hshift`, see
  `map_addRight_eq_of_translationInvariant`):

  | this branch | already merged |
  |---|---|
  | `tsum_localConn_ball_eq_of_translation` | `tsum_localConn_ball_eq_of_translationInvariant` |
  | `law_localConn_ball_succ_le_of_translation` | `law_localConn_ball_succ_le_of_translationInvariant` |
  | `tau_le_localConn_ball_add_of_translation` | `tau_le_localConn_ball_add_of_translationInvariant` |
  | `law_localConn_ball_succ_le_powerLaw_of_translation` | `law_localConn_ball_succ_le_powerLaw_of_translationInvariant` |
  | `tau_le_localConn_ball_add_powerLaw_of_translation` | `tau_le_localConn_ball_add_powerLaw_of_translationInvariant` (has an extra, unused `α < d`) |
  | `tsum_tau_ball_le_powerLaw_of_translation` | `tsum_tau_ball_le_powerLaw_of_translationInvariant` (has an extra `α < d`) |

  The merged file also has `powerLaw_const_ne_top` and the Prop 2.10 reduction
  `tsum_tau_ball_le_of_translationInvariant`, and Theorem 1.1 of arXiv:2103.17013v1
  (`hierarchicalTwoPointAveraged` in `HierarchicalTwoPointAveraged.lean`) is already
  proved on top of it, with Proposition 2.7 in `HierarchicalRestrictedSusc.lean`.
  The library does not keep two copies of a lemma, so these six should not be merged.
- **New.** The triangle recursion (`HierarchicalTriangle.lean`) has no counterpart in the
  library; nothing else in `PercLib/Models/Hierarchical*` mentions a triangle diagram.
- **Corollary 1.2** (pointwise bounds for radial kernels): the translation-invariant
  generalisation does not help there. The corollary needs the shell average of the
  restricted two-point function, which uses radial symmetry; translation invariance alone
  does not make `τ_n(0, x)` constant on shells. The radial forms already on the integration
  branch are what it would use.

## 5. D-35 hygiene of the new code

- No `sorry`, `admit`, `axiom`, `native_decide`, `set_option`; no code run at elaboration.
- Module docstring present (`/-! # The triangle diagram under one hierarchical block extension`).
- Hypothesis counts: 2 and 4 propositional hypotheses; well under ten.
- No tag, package or issue identifier in names or headers.
- See optional suggestions 2–4 for names, header and docstring points that the linters do not
  enforce.

## Required changes

1. **Drop the changes to `PercLib/Models/HierarchicalTwoPointUpper.lean`** (restore the file
   as it is on the integration branch). The six `_of_translation` theorems duplicate the
   merged `_of_translationInvariant` theorems in `HierarchicalTranslation.lean` (table in §4),
   and the file conflicts with the `localConn` respelling there. Use
   `PercLib.Models.law_localConn_ball_succ_le_of_translationInvariant` and its siblings
   instead.
2. **Fix the whitespace linter warnings in `HierarchicalTriangle.lean`**, lines 67–75
   (statement of `hierarchical_triangle_geometric`), for example:
   ```
       (hsucc : ∀ n, S (n + 1) = S n + (B - 1) * B ^ n * (c * r ^ n))
       (hd : ∀ n, D (n + 1) = D n +
         3 * (B - 1) * B ^ n * S n * (c * r ^ n) ^ 2 +
         (B - 1) * (B - 2) * (B ^ n) ^ 2 * (c * r ^ n) ^ 3) (N : ℕ) :
       S N = U * (B * r) ^ N + v ∧
       D N = D 0 +
         (3 * (B - 1) * U * c ^ 2 + (B - 1) * (B - 2) * c ^ 3) *
           (∑ n ∈ range N, (B ^ 2 * r ^ 3) ^ n) +
         3 * (B - 1) * v * c ^ 2 * (∑ n ∈ range N, (B * r ^ 2) ^ n) := by
   ```
   With exactly this change (proof unchanged) the module builds under `--wfail` with no
   warnings. Then rebase onto current `main` (or the integration branch) and keep both
   import lines in `PercLib.lean` in alphabetical order (`HierarchicalTranslation`, then
   `HierarchicalTriangle`).

After these two changes the branch adds one new module of theorems only and should merge
on a green gate.

## Optional suggestions

1. If you want the restated radial theorems to be corollaries of the general ones (your
   refactor removes about 150 lines of duplicated proof), that is welcome as a separate
   proof-only change against the integration branch: move the general proofs into
   `HierarchicalTwoPointUpper.lean` under the existing `_of_translationInvariant` names and
   `hJt` hypothesis, and derive the radial forms from them, leaving every statement as it is.
   Your observation that `α < d` is not needed in
   `tau_le_localConn_ball_add_powerLaw_of_translationInvariant` is noted for the maintainers;
   dropping it changes a statement, so it is an interface change and would go separately.
2. Names: library convention is that a name describes the conclusion, and a conjunction is
   usually stated as two lemmas. For instance `sum_blockExtension_root_eq` and
   `triangle_blockExtension_root_eq` for the two halves of `hierarchical_triangle_extension`,
   and similar for `hierarchical_triangle_geometric`.
3. Header: other files carry the three-line notice
   (`Copyright (c) 2026 PercLib contributors. All rights reserved.` / `Released under Apache 2.0
   license as described in the file LICENSE.` / `Authors: …`) followed by a short provenance
   comment (new proofs, date, mathematical reference). If the triangle recursion follows a
   published source, citing it there would help readers.
4. The module docstring could end with a `## Main results` list naming the two theorems,
   as the other modules do.
5. Generality: `hierarchical_triangle_extension` goes through verbatim over any commutative
   ring (checked: replacing `ℝ` by `R` with `[CommRing R]`, the same proof compiles), so
   stating it for a `CommRing` costs nothing.

---
Generated by [Claude Code](https://claude.ai/code)
