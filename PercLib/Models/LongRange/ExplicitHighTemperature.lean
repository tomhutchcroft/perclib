/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
The model is the sup-norm power-law version of the bond law in Definition I.1.3 of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1. The explicit
high-temperature bound is a derived comparison, not a critical-parameter estimate.
-/
module

public import PercLib.Models.LongRange.CappedDerivative
public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Percolation.Bond.PowerLawHighTemp.Threshold

/-!
# Explicit high-temperature bounds in every dimension

For `d ≥ 1` and `α > 0`, the sup-norm power-law row sum is bounded by
`2 d 3^(d-1) (1 + 1/α)`. Consequently `β < [2 d 3^(d-1) (1 + 1/α)]⁻¹` supplies the exact
high-temperature premise of the cluster-moment theorems. A dimension-two witness is provided at
`α = 1` and `β = 1/100`.

The capped cutoff moment at `r₀ = 5/2` is also instantiated there. Nearest-neighbour edges carry
nonzero cutoff and radial derivative weights at this scale, unlike at a radius below one. These
geometric checks do not themselves prove that the total derivative sum is nonzero. No removal of
the cap, small-tail estimate, uncapped derivative or sharpness statement is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### The row sum of the power law, with an explicit constant -/

/-- Off the origin the tail truncation `‖z‖ ≥ 1` is inactive, and at the origin both sides
vanish because the exponent is negative. -/
theorem powerLaw_norm_eq_ite (z : Fin d → ℤ) {α : ℝ} (hα : 0 < α) :
    (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) =
      if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0 := by
  split_ifs with h1
  · rfl
  · have hz : z = 0 := by
      by_contra hz
      exact h1 (one_le_norm_of_ne_zero hz)
    subst hz
    simp only [norm_zero]
    exact Real.zero_rpow (by
      have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith)

/-- At every nonzero lattice point the sup norm is at least `1`, so the power-law row sum is
unchanged by the tail truncation `‖z‖ ≥ r` at `r = 1`. -/
theorem tsum_powerLaw_eq_tsum_tail {α : ℝ} (hα : 0 < α) :
    (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) =
      ∑' z : Fin d → ℤ, (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) :=
  tsum_congr fun z => powerLaw_norm_eq_ite z hα

/-- The power-law row sum is summable in every dimension. -/
theorem summable_powerLaw_rowSum {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) :
    Summable fun z : Fin d → ℤ => (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) := by
  refine ((summable_powerLaw_iff hd α).2 hα).congr fun z => ?_
  have hne : -((d : ℝ) + α) ≠ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  by_cases hz : z = 0
  · subst hz
    simp only [↓reduceIte, norm_zero]
    exact (Real.zero_rpow hne).symm
  · simp only [hz, ite_false]

/-- The truncated power-law row sum is summable in every dimension. -/
theorem summable_powerLaw_tail {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) :
    Summable fun z : Fin d → ℤ => (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) :=
  (summable_powerLaw_rowSum (d := d) hd hα).congr fun z => powerLaw_norm_eq_ite z hα

/-- **Explicit row-sum bound in every dimension.** For `α > 0` the sup-norm power-law row sum is
at most `2 d 3^(d-1) (1 + 1/α)`. -/
theorem tsum_powerLaw_rowSum_le {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) :
    (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) ≤
      ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) := by
  have hnn : ∀ z : Fin d → ℤ,
      0 ≤ (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) := by
    intro z
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hsumm := summable_powerLaw_tail (d := d) hd hα
  have hEnn : ENNReal.ofReal (∑' z : Fin d → ℤ,
        (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0)) =
      ∑' z : Fin d → ℤ, ENNReal.ofReal
        (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) :=
    ENNReal.ofReal_tsum_of_nonneg hnn hsumm
  have htail := tsum_ofReal_powerLaw_tail_le (d := d) hd hα (r := 1) le_rfl
  have hconst : ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * ((1 + 1 / α) * (1 : ℝ) ^ (-α)) =
      ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) := by
    rw [Real.one_rpow, mul_one]
  have hC : (0 : ℝ) ≤ ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) := by
    have : (0 : ℝ) < 1 + 1 / α := by positivity
    positivity
  rw [tsum_powerLaw_eq_tsum_tail (d := d) hα]
  refine (ENNReal.ofReal_le_ofReal_iff hC).1 ?_
  rw [hEnn]
  rwa [hconst] at htail

/-! ### The explicit high-temperature threshold -/

/-- **Explicit threshold.** For `α > 0`, every `β < 1 / (2 d 3^(d-1) (1 + 1/α))` satisfies the
high-temperature hypothesis `β M < 1` in the exact `ℝ≥0∞` shape in which
`chi_cutoffKernel_powerLaw_ne_top` and the derivative interface consume it. -/
theorem beta_mul_rowSum_lt_one_of_lt {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ) < 1 / (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) :
    (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hrow := tsum_powerLaw_rowSum_le (d := d) hd hα
  have hC : (0 : ℝ) < ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) := by
    have h1 : (0 : ℝ) < 1 + 1 / α := by positivity
    have h2 : (0 : ℝ) < ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) := by
      have : 0 < 2 * d * 3 ^ (d - 1) := by
        have : 0 < 2 * d := by omega
        positivity
      exact_mod_cast this
    positivity
  have hM0 : (0 : ℝ) ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) :=
    tsum_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
    NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal _ hM0]
  have h3 : (β : ℝ) * (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) ≤
      (β : ℝ) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) :=
    mul_le_mul_of_nonneg_left hrow β.coe_nonneg
  have h4 : (β : ℝ) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) <
      (1 / (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) *
        (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) :=
    mul_lt_mul_of_pos_right hβ hC
  have h5 : (1 / (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) *
      (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) = 1 :=
    div_mul_cancel₀ 1 hC.ne'
  linarith

/-- The `ℝ≥0∞`-shaped high-temperature hypothesis used by `chi_cutoffKernel_powerLaw_ne_top`
and the derivative interface is the same condition as the real-valued `β M < 1`. -/
theorem beta_mul_rowSum_lt_one_iff {α : ℝ} {β : ℝ≥0} :
    ((β : ℝ≥0∞) * ((Real.toNNReal
        (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) ↔
      ((β : ℝ) * (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) < 1) := by
  have hM0 : (0 : ℝ) ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) :=
    tsum_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
    NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal _ hM0]

/-- **The high-temperature interval with an explicit witness.** This is
`exists_beta_interval_cutoffKernel_powerLaw_pow_ne_top` with the existential `β₀` replaced by the
explicit `1 / (4 d 3^(d-1) (1 + 1/α))`, in every dimension `d ≥ 1`. -/
theorem exists_beta_interval_cutoffKernel_powerLaw_pow_ne_top_explicit {α : ℝ}
    (hd : 1 ≤ d) (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (r : ℝ), 0 < r →
      ∀ (o : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law
          (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ := by
  set C : ℝ := ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) with hCdef
  have hC : 0 < C := by
    have h1 : (0 : ℝ) < 1 + 1 / α := by positivity
    have h2 : (0 : ℝ) < ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) := by
      have h3 : 0 < 2 * d * 3 ^ (d - 1) := by
        have : 0 < 2 * d := by omega
        positivity
      exact_mod_cast h3
    rw [hCdef]
    positivity
  refine ⟨⟨1 / (2 * C), le_of_lt (by positivity)⟩, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < 1 / (2 * C) by positivity)
  · intro β hβ r hr o k
    have hb : (β : ℝ) < 1 / (2 * C) := hβ
    have hle : 1 / (2 * C) ≤ 1 / C := by
      apply one_div_le_one_div_of_le hC
      linarith
    have hβ' : (β : ℝ) < 1 / (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) := by
      rw [← hCdef]
      linarith
    exact lintegral_cutoffKernel_powerLaw_pow_ne_top (d := d) hd hα (r := r)
      (beta_mul_rowSum_lt_one_of_lt (d := d) hd hα hβ') hr o k

/-! ### The physical dimension `d = 2` -/

/-- The `d = 2`, `α = 1` row sum is at most `24` (the explicit constant `2·2·3·2`). -/
theorem d2_rowSum_le_twentyfour :
    (∑' z : Fin 2 → ℤ, (‖z‖ : ℝ) ^ (-(((2 : ℕ) : ℝ) + 1))) ≤ 24 := by
  have h := tsum_powerLaw_rowSum_le (d := 2) (α := 1) (by norm_num) one_pos
  have h24 : ((2 * 2 * 3 ^ (2 - 1) : ℕ) : ℝ) * (1 + 1 / 1) = 24 := by norm_num
  rw [h24] at h
  exact h

/-- The high-temperature hypothesis holds at `d = 2`, `α = 1`, `β = 1/100`. -/
theorem d2_beta_rowSum_lt_one :
    ((1 / 100 : ℝ≥0) : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin 2 → ℤ, (‖z‖ : ℝ) ^ (-(((2 : ℕ) : ℝ) + 1))) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hrow := d2_rowSum_le_twentyfour
  have hM0 : (0 : ℝ) ≤ ∑' z : Fin 2 → ℤ, (‖z‖ : ℝ) ^ (-(((2 : ℕ) : ℝ) + 1)) :=
    tsum_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
    NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal _ hM0]
  have h100 : ((1 / 100 : ℝ≥0) : ℝ) = 1 / 100 := by norm_num
  have h100' : (0 : ℝ) ≤ ((1 / 100 : ℝ≥0) : ℝ) := by norm_num
  have h24 : ((1 / 100 : ℝ≥0) : ℝ) * 24 < 1 := by
    rw [h100]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_left hrow h100', h24]

/-! ### A non-vacuous corner-free scale in `d = 2`: `r₀ = 5/2`, `R = 3` -/

/-- `5/2` is not a sup-norm value on `ℤ^d`, so it is a corner-free scale. -/
theorem ofNorm_intCast_comp_ne_five_halves {d : ℕ} (z : Fin d → ℤ) :
    ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ z) ≠ 5 / 2 := by
  intro hz
  obtain ⟨n, hn⟩ := exists_nat_eq_norm z
  rw [ModelNorm.coe_ofNorm, norm_intCast_comp, hn] at hz
  have h2 : (2 * n : ℕ) = 5 := by
    have : ((2 * n : ℕ) : ℝ) = 5 := by push_cast; linarith
    exact_mod_cast this
  omega

/-- **The `r₀ = 5/2` shell is nonempty and carries weight `1`.** On every nearest-neighbour edge
the shell indicator `1{‖e‖ < 5/2}` equals `1`, and the cut-off kernel there is
`K 1 - K (5/2) > 0`, so the derivative formula of
`hasDerivAt_integral_cutoff_powerLaw_d2_capped_five_halves` is not identically zero. -/
theorem cutoffKernel_powerLaw_five_halves_ne_zero {α : ℝ} (hα : 0 < α) {x y : Fin d → ℤ}
    (hne : x ≠ y) (h1 : ‖x - y‖ = 1) :
    cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) (5 / 2)
      s(x, y) ≠ 0 := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hexp : -((d : ℝ) + α) < 0 := by linarith
  have hval : normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) = ‖x - y‖ := by
    rw [coe_normSeminorm, norm_intCast_comp]
  have hlt : powerLawProfile 1 ((d : ℝ) + α) (5 / 2) < powerLawProfile 1 ((d : ℝ) + α) 1 := by
    simp only [powerLawProfile, one_mul, Real.one_rpow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  rw [cutoffKernel_def, radialKernel_mk]
  simp only [hne, ite_false, hval, h1, cutoffProfile_of_le (by norm_num : (1 : ℝ) ≤ 5 / 2)]
  exact ne_of_gt (Real.toNNReal_pos.2 (sub_pos.2 hlt))

/-- On a nearest-neighbour edge the derivative weight at `r₀ = 5/2` is `1`. -/
theorem radialKernel_shell_five_halves_eq_one {x y : Fin d → ℤ} (hne : x ≠ y)
    (h1 : ‖x - y‖ = 1) :
    radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (fun s => if s < (5 / 2 : ℝ) then 1 else 0) s(x, y) = 1 := by
  rw [radialKernel_mk]
  simp only [hne, ite_false]
  have hval : normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) = ‖x - y‖ := by
    rw [coe_normSeminorm, norm_intCast_comp]
  rw [hval, h1]
  simp only [show (1 : ℝ) < 5 / 2 by norm_num, ite_true]
  norm_num

/-- **A non-vacuous capped derivative in dimension `2`.** At `d = 2`, `α = 1`, `β = 1/100`, every
root `o` and every cap `B`, the capped expected cluster size under the cut-off power law is
differentiable at the corner-free scale `r₀ = 5/2` with `R = 3`, with the production
pivotal-flux derivative formula. This is `hasDerivAt_integral_cutoff` with all premises
instantiated at `d = 2`. -/
theorem hasDerivAt_integral_cutoff_powerLaw_d2_capped_five_halves (o : Fin 2 → ℤ) (B : ℕ) :
    HasDerivAt (fun r : ℝ => ∫ (ω : Config (Fin 2 → ℤ)),
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ)
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
          (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) r) (1 / 100)))
      (∑' (e : Sym2 (Fin 2 → ℤ)),
        ↑(radialKernel (normSeminorm ℝ (Fin 2 → ℝ))
            (fun s => if s < (5 / 2 : ℝ) then 1 else 0) e) *
            (((1 / 100 : ℝ≥0) : ℝ) * ((((2 : ℕ) : ℝ) + 1) *
                (5 / 2 : ℝ) ^ (-(((2 : ℕ) : ℝ) + 1) - 1)) *
              Real.exp (-((1 / 100 : ℝ≥0) : ℝ) *
                ↑(cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
                  (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) (5 / 2) e))) *
          ∫ (ω : Config (Fin 2 → ℤ)),
            (((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) -
              (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ)
            ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
              (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) (5 / 2)) (1 / 100)))
      (5 / 2) := by
  have hda : 0 ≤ (((2 : ℕ) : ℝ) + 1) := by norm_num
  have h := hasDerivAt_integral_cutoff
    (N := ModelNorm.ofNorm (Fin 2 → ℝ))
    (K := powerLawProfile 1 (((2 : ℕ) : ℝ) + 1))
    (K' := fun t => 1 * (-(((2 : ℕ) : ℝ) + 1) * t ^ (-(((2 : ℕ) : ℝ) + 1) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) zero_le_one hda)
    (fun t ht => hasDerivAt_powerLawProfile_add 1 1 ht)
    (continuousOn_powerLawProfile_deriv_add 1 1)
    (1 / 100) (fun n => cap_toNat_abs_le B n) ⟨B, fun n hn => cap_toNat_eq_top B hn⟩ o
    (R := 3) (chi_cutoffKernel_powerLaw_ne_top (d := 2) (by norm_num) (α := 1) one_pos
      d2_beta_rowSum_lt_one (r := 3) (by norm_num) o)
    (r₀ := 5 / 2) (by norm_num) (by norm_num) (fun z => ofNorm_intCast_comp_ne_five_halves z)
  simpa only [one_mul, neg_mul, neg_neg, ModelNorm.toSeminorm_ofNorm] using h

end PercLib.Models.LongRange
