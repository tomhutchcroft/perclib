/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Non-vacuity witness written on 2026-11-20, for the statements of `PercLib.Models.Hierarchical.Defs`.
New proofs; no upstream code is copied and no definition is added.
-/
module

public import PercLib.Models.Hierarchical.Defs
public import PercLib.Models.HierarchicalGeometry

/-! # Non-vacuity of the hierarchical two-point statements

For every `d, L, α` and `0 < c ≤ C`, the exact power-law kernel
`J s(u,v) = c L^{-(d+α) h(v-u)}` (written as a `Sym2.lift` lambda; its value `c` on the
diagonal is irrelevant, since loops are discarded) satisfies every kernel hypothesis of
`HierarchicalTwoPointAveraged` and `HierarchicalTwoPointRadial`: it is translation invariant,
radial, and satisfies both power-law bounds off the diagonal. So the class of kernels quantified
over in both statements is non-empty, and neither statement holds vacuously in `J`.
-/

@[expose] public section
noncomputable section

open scoped NNReal

namespace PercLib.Models

/-- **Non-vacuity witness.** The exact kernel `J s(u,v) = c L^{-(d+α) h(v-u)}` is translation
invariant, radial, and satisfies `c L^{-(d+α) h(v-u)} ≤ J s(u,v) ≤ C L^{-(d+α) h(v-u)}` (here
for all `u, v`, in particular for `u ≠ v`) whenever `0 < c ≤ C`. -/
theorem hierarchicalTwoPoint_kernel_witness (d L : ℕ) (α c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) :
    let J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0 :=
      Sym2.lift ⟨fun u v =>
        (c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))).toNNReal,
        fun u v => by simp only [level_sub_comm u v]⟩
    (∀ x u v, J s(u + x, v + x) = J s(u, v)) ∧
      (∃ f : ℕ → ℝ≥0, ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) ∧
      (∀ u v, u ≠ v →
        c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
          (J s(u, v) : ℝ)) ∧
      (∀ u v, u ≠ v →
        (J s(u, v) : ℝ) ≤
          C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) := by
  intro J
  have hJ : ∀ u v, J s(u, v) =
      (c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))).toNNReal :=
    fun u v => rfl
  have hpos : ∀ u v : ℕ →₀ (Fin d → ZMod L),
      0 ≤ c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) :=
    fun u v => mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg L) _)
  refine ⟨fun x u v => ?_, ⟨fun j => (c * (L : ℝ) ^ (-(((d : ℝ) + α) * (j : ℝ)))).toNNReal,
    fun x y => hJ x y⟩, fun u v _ => ?_, fun u v _ => ?_⟩
  · rw [hJ, hJ, add_sub_add_right_eq_sub]
  · rw [hJ, Real.coe_toNNReal _ (hpos u v)]
  · rw [hJ, Real.coe_toNNReal _ (hpos u v)]
    exact mul_le_mul_of_nonneg_right hcC (Real.rpow_nonneg (Nat.cast_nonneg L) _)

/-- **Non-vacuity, existence form.** For every admissible `(d, L, α, c, C)` some kernel satisfies
all kernel hypotheses of `HierarchicalTwoPointAveraged` and `HierarchicalTwoPointRadial`. -/
theorem exists_hierarchicalTwoPoint_kernel (d L : ℕ) (α c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) :
    ∃ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
      (∀ x u v, J s(u + x, v + x) = J s(u, v)) ∧
      (∃ f : ℕ → ℝ≥0, ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) ∧
      (∀ u v, u ≠ v →
        c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
          (J s(u, v) : ℝ)) ∧
      (∀ u v, u ≠ v →
        (J s(u, v) : ℝ) ≤
          C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) :=
  ⟨_, hierarchicalTwoPoint_kernel_witness d L α c C hc hcC⟩

end PercLib.Models
