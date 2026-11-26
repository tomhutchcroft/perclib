/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the diagonal-insensitive row identity of a displacement kernel
(displacement-kernels article). All mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.TranslationInvariant

/-!
# Off-diagonal rows of displacement kernels: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Models.TranslationInvariant`.

## Main results

* `rowSum_eq_and_le_of_offDiagonal_translationInvariant`: if `J x y = k (y - x)` for `x ≠ y`
  on an additive group, the off-diagonal row of `J` at every vertex is
  `∑'_{z ≠ 0} k z ≤ ∑' z, k z` in `ℝ≥0∞`, whatever the diagonal values of `J`.
-/

@[expose] public section
noncomputable section
open scoped ENNReal NNReal

namespace PercLib.Models

variable {G : Type*} [AddGroup G]

open Classical in
/-- On a countable group (written additively), let `k` be a finite nonnegative kernel and
let the kernel `J` on ordered pairs equal `k (y - x)` at every pair `x ≠ y`, its diagonal
values being arbitrary. Then at every vertex the off-diagonal row of `J` equals the kernel
mass away from the identity, as extended nonnegative sums, and so is at most the total mass
of `k`. -/
@[tag "R01V"]
theorem rowSum_eq_and_le_of_offDiagonal_translationInvariant [Countable G]
    (J : G → G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, x ≠ y → J x y = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J v w : ℝ≥0∞)) =
        ∑' z, (if z = 0 then 0 else (k z : ℝ≥0∞)) ∧
      (∑' w, if w = v then 0 else (J v w : ℝ≥0∞)) ≤ ∑' z, (k z : ℝ≥0∞) :=
  ⟨rowSum_eq_of_offDiagonal_translationInvariant J k hJ v,
    rowSum_le_tsum_of_offDiagonal_translationInvariant J k hJ v⟩

end PercLib.Models
