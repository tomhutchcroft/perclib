/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs; no upstream code is copied. Used for cut-off derivative interfaces in the remaining
bounded campaign. Sup-norm corner values are natural numbers, so a positive corner condition is
an actual lattice-norm exclusion, not a free consequence of being greater than one.
-/
module

public import PercLib.Models.LongRange.InfiniteVolumeRusso
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm


/-!
# Analytic side conditions for cut-off power-law profiles

Power-law derivatives, the strategy property, continuity and norm-value facts for the cut-off
derivative interface. No unbounded-moment derivative or limit is asserted.
-/
@[expose] public section

noncomputable section

open Filter Set
open scoped NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {d : ℕ}

/-! ### The derivative and its continuity at general exponent -/

/-- Derivative of the power-law profile at general exponent: for `t > 0`,
`d/dt (c t^(-a)) = c * (-a * t^(-a-1))`; written in the `K'` shape used by
`hasDerivAt_integral_cutoff`. -/
theorem hasDerivAt_powerLawProfile (c a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (powerLawProfile c a) (c * (-a * t ^ (-a - 1))) t := by
  have h := (Real.hasDerivAt_rpow_const (p := -a) (Or.inl ht.ne')).const_mul c
  exact h.congr_deriv (by rw [mul_comm])

/-- The derivative formula with the exponent instantiated at `d + α`. -/
theorem hasDerivAt_powerLawProfile_add (c α : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (powerLawProfile c ((d : ℝ) + α))
      (c * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) t :=
  hasDerivAt_powerLawProfile c _ ht

theorem continuousOn_powerLawProfile_deriv (c a : ℝ) :
    ContinuousOn (fun t => c * (-a * t ^ (-a - 1))) (Ioi 0) :=
  continuousOn_const.mul (continuousOn_const.mul
    (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)))

theorem continuousOn_powerLawProfile_deriv_add (c α : ℝ) :
    ContinuousOn (fun t => c * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) (Ioi 0) :=
  continuousOn_powerLawProfile_deriv c _

/-! ### Monotonicity and positivity -/

theorem antitoneOn_powerLawProfile_add {c α : ℝ} (hc : 0 ≤ c) (hαd : 0 ≤ (d : ℝ) + α) :
    AntitoneOn (powerLawProfile c ((d : ℝ) + α)) (Ioi 0) :=
  antitoneOn_powerLawProfile hc hαd

/-- Off the diagonal the power-law kernel is strictly positive (the truncation in
`radialKernel` is inactive). -/
theorem powerLawProfile_add_pos_of_norm {N : ModelNorm (Fin d → ℝ)} {c α : ℝ} (hc : 0 < c)
    {z : Fin d → ℤ} (hz : z ≠ 0) :
    0 < powerLawProfile c ((d : ℝ) + α) (N (Int.cast ∘ z)) :=
  powerLawProfile_pos hc (N.intCast_comp_pos hz)

/-- Untruncated radial kernel value for the power law at general exponent. -/
theorem coe_radialKernel_powerLaw_add {N : ModelNorm (Fin d → ℝ)} {c α : ℝ} (hc : 0 < c)
    {x y : Fin d → ℤ} (h : x ≠ y) :
    (radialKernel N (powerLawProfile c ((d : ℝ) + α)) s(x, y) : ℝ) =
      powerLawProfile c ((d : ℝ) + α) (N (Int.cast ∘ (x - y))) :=
  coe_radialKernel_of_ne h (powerLawProfile_add_pos_of_norm hc (sub_ne_zero.2 h)).le

/-! ### Cut-off values and corners for the sup norm -/

/-- The norm of an integer point is a natural number: the corners of the sup norm are `ℕ`. -/
theorem exists_nat_eq_norm (z : Fin d → ℤ) : ∃ n : ℕ, ‖z‖ = n :=
  ⟨⌊‖z‖⌋₊, (natCast_floor_norm z).symm⟩

/-- The set of values of the sup norm on `ℤ^d` is exactly `{n : ℝ | n ∈ ℕ}`: the corners of the
cut-off derivative theorem are precisely the natural numbers. -/
theorem range_norm_eq_nat (hd : Nonempty (Fin d)) :
    Set.range (fun z : Fin d → ℤ => ‖z‖) = {r : ℝ | ∃ n : ℕ, (n : ℝ) = r} := by
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_eq_norm z
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun _ => (n : ℤ), ?_⟩
    rw [← hn]
    simp

/-- A sup-norm value is a corner exactly when it is a natural number. If `r₀` is not a natural
number, it is automatically a valid sup-norm corner-free scale. -/
theorem corner_of_nat_ne {r₀ : ℝ} (hne : ∀ n : ℕ, (n : ℝ) ≠ r₀) : ∀ z : Fin d → ℤ, ‖z‖ ≠ r₀ := by
  intro z
  obtain ⟨n, hn⟩ := exists_nat_eq_norm z
  rw [hn]
  exact hne n

/-- Every corner-free scale in `(0, R)` has a corner-free neighbourhood there, with an explicit
strict bound. -/
theorem exists_corner_free_interval (N : ModelNorm (Fin d → ℝ)) {r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hr₀R : r₀ < R) (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r₀) :
    ∃ δ > 0, δ < R - r₀ ∧ ∀ r ∈ Ioo (r₀ - δ) (r₀ + δ), ∀ z : Fin d → ℤ,
      N (Int.cast ∘ z) ≠ r := by
  obtain ⟨δ, hδ, hδ0, hδR, hI⟩ := exists_corner_free hr₀ hr₀R hcorner
  refine ⟨min (δ / 2) ((R - r₀) / 2), lt_min (half_pos hδ) (half_pos (sub_pos.2 hr₀R)), ?_, ?_⟩
  · exact (min_lt_iff).2 (Or.inr (half_lt_self (sub_pos.2 hr₀R)))
  · intro r hr z hz
    apply hI z
    have hs : min (δ / 2) ((R - r₀) / 2) < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

end PercLib.Models.LongRange
