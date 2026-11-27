/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the nontrivial-triangle argument in the Fourier bootstrap
of Heydenreich and van der Hofstad (2017).
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.FirstStep
public import PercLib.Percolation.Bond.Lace.Diagrams.FirstWeighted

/-!
# The first-step triangle bound at the origin

The existing nontrivial-triangle comparison gives the factor three halves.
Translation invariance identifies its continuation diagram with the convolution
`J * tau³` at zero. Keeping that argument explicit removes the direct step from
the further first-step expansion, because the actual step kernel vanishes at zero.

## Main results

* `continuation_triangle_eq_step_tau_three`: the exact convolution identity.
* `triangle_le_one_add_three_halves_step_tau_three`: the extended-nonnegative bound.
* `triangle_toReal_le_one_add_three_halves_step_tau_three`: the real convolution bound.
* `triangle_le_one_add_three_halves_two_step_terms`: no direct step term at the origin.
-/

@[expose] public section
noncomputable section

open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The rooted triple convolution is the three-edge connection sum at its
reflected endpoint. This identity needs no summability assumption. -/
theorem tau_three_neg_eq_triangle (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (v : G) :
    (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0)) (0 - v) =
      ∑' s, ∑' t, tau q 0 s * tau q s t * tau q v t := by
  simp only [addRingConvolution_eq_tsum_sub]
  rw [← (Equiv.neg G).tsum_eq]
  apply tsum_congr
  intro s
  change tau q 0 (-s) * (∑' w, tau q 0 w * tau q 0 (0 - v - -s - w)) = _
  rw [← ((Equiv.neg G).trans (Equiv.addRight s)).tsum_eq]
  simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addRight]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro t
  have hs : tau q 0 (-s) = tau q 0 s := by
    calc
      _ = tau q s 0 := by
        simpa only [zero_sub] using (tau_eq_rooted_of_add_right q hq s 0).symm
      _ = _ := tau_comm q s 0
  have ht : tau q 0 (-t + s) = tau q s t := by
    calc
      _ = tau q t s := by
        simpa only [sub_eq_add_neg, add_comm] using
          (tau_eq_rooted_of_add_right q hq t s).symm
      _ = _ := tau_comm q t s
  have he : 0 - v - -s - (-t + s) = t - v := by abel
  rw [hs, ht, he, ← tau_eq_rooted_of_add_right q hq v t]
  ac_rfl

/-- The actual continuation triangle is the step-weighted triple convolution
at the origin, before taking any supremum. -/
theorem continuation_triangle_eq_step_tau_three (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    (∑' s, ∑' t, tau q 0 s *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v t) * tau q s t) =
      (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0 := by
  rw [addRingConvolution_eq_tsum_sub]
  simp only [tau_three_neg_eq_triangle q hq]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  calc
    _ = ∑' s, ∑' v, ∑' t, tau q 0 s *
        (offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v t) * tau q s t := by
      apply tsum_congr
      intro s
      rw [ENNReal.tsum_comm]
    _ = _ := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro v
      apply tsum_congr
      intro s
      apply tsum_congr
      intro t
      ac_rfl

/-- The full triangle is bounded by one plus three halves of the actual
continuation diagram at zero. No finiteness assumption is needed. -/
theorem triangle_le_one_add_three_halves_step_tau_three [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    (∑' s, ∑' t, tau q 0 s * tau q s t * tau q t 0) ≤
      1 + (3 / 2 : ℝ≥0∞) * (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0 := by
  classical
  rw [← ENNReal.tsum_prod' (f := fun p : G × G =>
    tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0),
    ENNReal.tsum_eq_add_tsum_ite (0, 0)]
  simp only [tau_self, mul_one]
  apply add_le_add le_rfl
  have h := (nontrivial_triangle_mass_le_three_halves_initial q).trans
    (mul_le_mul' le_rfl (nontrivial_initial_mass_le_continuation_triangle q))
  rw [continuation_triangle_eq_step_tau_three q hq] at h
  convert h using 1
  apply tsum_congr
  intro p
  by_cases hp : p = (0, 0) <;> simp [hp]

/-- With finite susceptibility and step mass, the origin triangle bound uses
the actual real kernels and mathlib's discrete convolution. -/
theorem triangle_toReal_le_one_add_three_halves_step_tau_three [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hJ : (∑' z, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 z) ≠ ⊤)
    (hchi : chi q 0 ≠ ⊤) :
    let J : G → ℝ := fun z => (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 z).toReal
    let T : G → ℝ := fun z => (tau q 0 z).toReal
    (∑' s, ∑' t, tau q 0 s * tau q s t * tau q t 0).toReal ≤
      1 + (3 / 2 : ℝ) * (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) 0 := by
  let J := offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
  let T := tau q 0
  have hT : (∑' z, T z) ≠ ⊤ := by rwa [chi_eq_tsum_tau] at hchi
  have hT2 : (∑' z, (T ⋆ᵣ₊ T) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hT
  have hT3 : (∑' z, (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hT2
  have hentry := addRingConvolution_ennreal_ne_top hJ hT3 0
  have hconstant : (3 / 2 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.ofNat_ne_top (by norm_num)
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hconstant hentry⟩)
    (triangle_le_one_add_three_halves_step_tau_three q hq)
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.mul_ne_top hconstant hentry)] at h
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofNat] at h
  simp only [toReal_addRingConvolution_ennreal (ENNReal.ne_top_of_tsum_ne_top hJ)
      (ENNReal.ne_top_of_tsum_ne_top hT3),
    toReal_addRingConvolution_ennreal (ENNReal.ne_top_of_tsum_ne_top hT)
      (ENNReal.ne_top_of_tsum_ne_top hT2),
    toReal_addRingConvolution_ennreal (ENNReal.ne_top_of_tsum_ne_top hT)
      (ENNReal.ne_top_of_tsum_ne_top hT)] at h
  exact h

/-- The direct step vanishes at zero, leaving only terms with two step kernels. -/
theorem triangle_le_one_add_three_halves_two_step_terms [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    let J := offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    let T := tau q 0
    (∑' s, ∑' t, tau q 0 s * tau q s t * tau q t 0) ≤
      1 + (3 / 2 : ℝ≥0∞) * ((J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) 0 +
        (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T))) 0 + (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)))) 0) := by
  have h := step_tau_three_le_firstStep_expansion q hq 0
  dsimp only at h ⊢
  simp only [Pi.add_apply, offDiagonal_self, zero_add] at h
  exact (triangle_le_one_add_three_halves_step_tau_three q hq).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl h))

end PercLib.Percolation.Bond.Lace
