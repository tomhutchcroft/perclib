/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived definitions; the companion `DegreeCorner` module is proof-only.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definitions I.1.3 and I.1.5.
-/
module

public import PercLib.Models.LongRange.CutoffCorner
public import PercLib.Models.LongRange.CutoffPowerLawAnalytic
public import PercLib.Models.LongRange.PowerLaw

/-!
# Definitions for the expected-degree corner at a positive integer scale

This file contains only definitions (plus the module-level setup); every theorem about them lives
in the proof module `DegreeCorner`.

## Exact mathematical meaning

Throughout `d : ℕ`, `α : ℝ`, `β : ℝ≥0`.  The carrier is `ℤ^d = Fin d → ℤ` with the sup norm
`‖z‖ = max_i |z i|`; this is the sup norm restricted from `ℝ^d`, i.e.
`normSeminorm ℝ (Fin d → ℝ)`, see `normSeminorm_intCast` in `PercLib.Models.LongRange.Defs`.
For `z : ℤ^d` the norm `‖z‖` is a natural number (`natCast_floor_norm`).

* `boxFinset d n = Finset.Icc (fun _ => -n) (fun _ => n) = {z : ℤ^d : ‖z‖ ≤ n}` is the **closed**
  sup-norm box of radius `n`, as a finset (`mem_boxFinset`);
* `ballPt d n = (boxFinset d n).erase 0 = {z : ℤ^d : z ≠ 0 ∧ ‖z‖ ≤ n}` is the same **closed** box
  with the diagonal point removed (a "punctured" box, `mem_ballPt`).  In particular `ballPt` is a
  *closed*-ball object: the right-derivative weights below are indexed by `ballPt d n`, not by the
  open ball `{‖z‖ < n}`;
* `edgeProb d α β r z` is the probability that the pair `{0, z}` is open in the bond percolation
  law on the **whole infinite lattice** `ℤ^d` whose kernel is the cut-off power law of Definition
  I.1.5 at scale `r` with profile `K = powerLawProfile 1 (d + α)`.  Concretely
  `edgeProb d α β r z = 1 - exp (-(β * J_r ‖z‖))` for `z ≠ 0`, where `J_r s = K s - K r` for
  `s ≤ r` and `J_r s = 0` for `r < s`; and `edgeProb d α β r 0 = 0` because the kernel is `0` on
  the diagonal.  This is the open probability of the actual model, not a finite-graph proxy;
* `expDegree d α β r = ∑' z : ℤ^d, edgeProb d α β r z` is the **expected degree** of a vertex of
  that infinite-lattice model at scale `r`.  The `tsum` is over all of `ℤ^d`; it is a finite sum
  only because the summand vanishes off a finite box (`expDegree_eq_sum_ballPt`);
* `localDegree d α β n r = ∑ z ∈ ballPt d n, (1 - exp (-(β * (K ‖z‖ - K r))))` is the finite sum
  that `expDegree d α β ·` agrees with on `[n, n + 1)` (`expDegree_eq_sum_ballPt`).  It is a
  bookkeeping device for differentiating a finite sum, not a different model.

No hypothesis is built into the definitions: `α` and `β` are arbitrary here, and the theorems in
`DegreeCorner` state exactly which hypotheses (`0 < α`, `1 ≤ n`, `β ≠ 0`) they use.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

variable {d : ℕ}

/-! ## The sup-norm box and the punctured box -/

/-- The closed sup-norm box of radius `n` in `ℤ^d`, as a finset:
`{z : ℤ^d : ‖z‖ ≤ n}`. -/
def boxFinset (d n : ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ : Fin d => (n : ℤ))

/-- The nonzero points of the closed sup-norm box of radius `n`: the **closed** ball at radius `n`
with the diagonal removed, `{z : ℤ^d : z ≠ 0 ∧ ‖z‖ ≤ n}`. -/
def ballPt (d n : ℕ) : Finset (Fin d → ℤ) := (boxFinset d n).erase 0

/-! ## The expected degree of the cut-off bond model -/

/-- The open probability of the pair `{0, z}` in the sup-norm power-law cut-off bond model on the
infinite lattice `ℤ^d` at scale `r`: the intensity-profile value
`1 - exp (-(β * J_r ‖z‖))` of Definition I.1.5, with `J_r` the cut-off power law. -/
noncomputable def edgeProb (d : ℕ) (α : ℝ) (β : ℝ≥0) (r : ℝ) (z : Fin d → ℤ) : ℝ :=
  (intensityProfile (cutoffKernel (ModelNorm.ofNorm (Fin d → ℝ))
    (powerLawProfile 1 ((d : ℝ) + α)) r) β s(0, z) : ℝ)

/-- The expected degree of a vertex of the sup-norm power-law cut-off bond model on `ℤ^d` at scale
`r`: the sum over all `z : ℤ^d` of the open probability of the pair `{0, z}`. -/
noncomputable def expDegree (d : ℕ) (α : ℝ) (β : ℝ≥0) (r : ℝ) : ℝ :=
  ∑' z : Fin d → ℤ, edgeProb d α β r z

/-! ## The local model -/

/-- The finite sum over the punctured closed box: the values of the expected degree on the
interval `[n, n + 1)`, written out with the corner resolved into the difference `K ‖z‖ - K r`. -/
noncomputable def localDegree (d : ℕ) (α : ℝ) (β : ℝ≥0) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ z ∈ ballPt d n,
    (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
      powerLawProfile 1 ((d : ℝ) + α) r))))

end PercLib.Models.LongRange
