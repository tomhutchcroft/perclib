/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived corollary; no upstream code is copied. This file instantiates the production cut-off
derivative interface `PercLib.Models.LongRange.hasDerivAt_integral_cutoff` for the concrete power
law `powerLawProfile 1 (d + α)` in the sup norm, with the bounded cap envelope
`F_B(n) = min(n, B)`, at `r₀ = 1/2` and `R = 1`, in the high-temperature region `β M < 1`.
No unbounded-moment, parameter-limit or criticality claim is made.
-/
module

public import PercLib.Models.LongRange.CutoffPowerLawAnalytic
public import PercLib.Models.LongRange.CutoffDominatedHighTemp

/-!
# The capped derivative of the cut-off power law at `r₀ = 1/2`, `R = 1`

`hasDerivAt_integral_cutoff` needs: an antitone profile with a continuous derivative, a bounded
envelope `F` that is eventually constant, finite first moment of the cut-off law at scale `R`,
`r₀ ∈ (0, R)`, and `r₀` not a value of the norm on `ℤ^d`.

This file checks all of them for `K = powerLawProfile 1 (d + α)` with `α > 0` in the sup norm
`N = ModelNorm.ofNorm (Fin d → ℝ)`, for the bounded cap envelope `F_B(n) = min(n, B)` (`B : ℕ`),
with `R = 1`, `r₀ = 1/2` and `d ≥ 1`, in the region `β M < 1`:
* antitone, derivative and derivative continuity are the compiled `CutoffPowerLawAnalytic` API at
  exponent `d + α`;
* `|F_B n| ≤ B` and `F_B n = F_B ⊤` for `n ≥ B`;
* `hχ` is `chi_cutoffKernel_powerLaw_ne_top` at radius `1`;
* `1/2` is not a natural number, and every sup-norm value on `ℤ^d` is a natural number
  (`exists_nat_eq_norm`).

The resulting statement is the exact `HasDerivAt` formula of the production lemma.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-! ### The bounded cap envelope `F_B (n) = min (n, B)` -/

/-- The cap envelope is bounded by `B`: `|min(n, B)| ≤ B`. -/
theorem cap_toNat_abs_le (B : ℕ) (n : ℕ∞) :
    |(((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ))| ≤ (B : ℝ) := by
  have h : (n ⊓ (B : ℕ∞)).toNat ≤ B := by
    have h' := ENat.toNat_le_toNat (inf_le_right : n ⊓ (B : ℕ∞) ≤ (B : ℕ∞)) (by simp)
    simpa using h'
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast h

/-- The cap envelope is stable: above `B` it is already at its top value. -/
theorem cap_toNat_eq_top (B : ℕ) {n : ℕ∞} (hn : (B : ℕ∞) ≤ n) :
    ((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) = ((⊤ ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) := by
  rw [inf_eq_right.2 hn, inf_eq_right.2 le_top]

/-! ### `1/2` is not a sup-norm value on `ℤ^d` -/

/-- Sup-norm values on `ℤ^d` are natural numbers, so `1/2` is a corner-free scale. -/
theorem ofNorm_intCast_comp_ne_half {d : ℕ} (z : Fin d → ℤ) :
    ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ z) ≠ 1 / 2 := by
  intro hz
  obtain ⟨n, hn⟩ := exists_nat_eq_norm z
  rw [ModelNorm.coe_ofNorm, norm_intCast_comp, hn] at hz
  have h2 : (2 * n : ℕ) = 1 := by
    have : ((2 * n : ℕ) : ℝ) = 1 := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ### The instantiated derivative -/

/-- **The capped derivative of the cut-off power law at `r₀ = 1/2`, `R = 1`.**

For `d ≥ 1`, `α > 0`, `β M < 1` with `M = ∑_{z ≠ 0} ‖z‖ ^ (-(d + α))`, every root `o` and every
cap `B : ℕ`, the expected capped cluster size
`r ↦ ∫ min(|K_o(ω)|, B) dμ_r` under the cut-off power law at scale `r` is differentiable at
`r₀ = 1/2`, with derivative the infinite pivotal flux `∑' e, c_{1/2}(e) (P_e - P_{∅})` of the
capped cluster size. This is `hasDerivAt_integral_cutoff` with all of its premises instantiated,
at `K = powerLawProfile 1 (d + α)` and `K' t = 1 * (-((d + α) t ^ (-(d + α) - 1)))`.

The displayed derivative is the production formula with the scalar factor `-K' (1/2)` evaluated:
`-(1 * (-(d + α) * (1/2) ^ (-(d + α) - 1))) = (d + α) * (1/2) ^ (-(d + α) - 1)`, and with one
negation pushed inside `Real.exp` (`-(β * x) = -β * x`); the compiled proof performs this rewriting
with `one_mul, neg_mul, neg_neg`, so the statement is the production output up to those ring
identities and no other change. -/
theorem hasDerivAt_integral_cutoff_powerLaw_sup_capped {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (B : ℕ) :
    HasDerivAt (fun r : ℝ => ∫ (ω : Config (Fin d → ℤ)),
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ)
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))
      (∑' (e : Sym2 (Fin d → ℤ)),
        ↑(radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < (1 / 2 : ℝ) then 1 else 0) e) *
            ((β : ℝ) * (((d : ℝ) + α) * (1 / 2 : ℝ) ^ (-((d : ℝ) + α) - 1)) *
              Real.exp (-(β : ℝ) * ↑(cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) (1 / 2) e))) *
          ∫ (ω : Config (Fin d → ℤ)),
            (((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) -
              (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ)
            ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (1 / 2)) β))
      (1 / 2) := by
  have hda : 0 ≤ (d : ℝ) + α := by
    have : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    linarith
  have h := hasDerivAt_integral_cutoff (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) zero_le_one hda)
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add 1 α)
    β (fun n => cap_toNat_abs_le B n) ⟨B, fun n hn => cap_toNat_eq_top B hn⟩ o
    (R := 1) (chi_cutoffKernel_powerLaw_ne_top hd hα hβ (by norm_num) o)
    (r₀ := 1 / 2) (by norm_num) (by norm_num) (fun z => ofNorm_intCast_comp_ne_half z)
  simpa only [one_mul, neg_mul, neg_neg, ModelNorm.toSeminorm_ofNorm] using h

/-! ### Non-vacuity at `d = 1`, `α = 1`, `β = 1/10` -/

/-- Pointwise form of `‖z‖ ^ (-2)` on `ℤ` as a tail summand at radius `1`. -/
private theorem ite_norm_sq_eq (z : Fin 1 → ℤ) :
    (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1)) =
      if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1)) else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp [Real.zero_rpow]
  · simp [one_le_norm_of_ne_zero hz]

/-- At `d = 1`, `α = 1` the row sum is at most `4`: `∑_{z : ℤ} ‖z‖ ^ (-2) ≤ 4`
(this is `PowerLaw.tsum_powerLaw_tail_le` at `r = 1`, with the constant `2 · 1 · 3 ^ 0 · 2`). -/
theorem tsum_powerLaw_sq_le_four :
    (∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))) ≤ 4 := by
  have hsummable : Summable fun z : Fin 1 → ℤ =>
      (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1)) else 0) := by
    have hg := (summable_powerLaw_iff (d := 1) le_rfl 1).2 one_pos
    refine hg.congr fun z => ?_
    by_cases hz : z = 0
    · subst hz
      simp [Real.zero_rpow]
    · simp only [one_le_norm_of_ne_zero hz, ite_eq_left, hz, ite_eq_right, not_false_eq_true]
  have hEnn : ENNReal.ofReal (∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))) =
      ∑' z : Fin 1 → ℤ, ENNReal.ofReal
        (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1)) else 0) := by
    rw [tsum_congr fun z => ite_norm_sq_eq z]
    refine ENNReal.ofReal_tsum_of_nonneg (fun z => ?_) hsummable
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have htail := tsum_ofReal_powerLaw_tail_le (d := 1) (α := 1) le_rfl one_pos (r := 1) le_rfl
  have hconst : ((2 * 1 * 3 ^ (1 - 1) : ℕ) : ℝ) * ((1 + 1 / 1) * (1 : ℝ) ^ (-(1 : ℝ))) = 4 := by
    norm_num
  rw [hconst] at htail
  have h4 : ENNReal.ofReal (∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))) ≤
      ((4 : ℝ≥0) : ℝ≥0∞) := by
    rw [hEnn]
    exact htail.trans_eq (by norm_num)
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 (h4.trans_eq (by norm_num))

/-- The high-temperature hypothesis `β M < 1` holds at `d = 1`, `α = 1`, `β = 1/10`
(indeed `β M ≤ 2/5`). -/
theorem beta_one_tenth_rowSum_lt_one :
    ((1 / 10 : ℝ≥0) : ℝ≥0∞) *
      (((∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))).toNNReal : ℝ≥0) :
        ℝ≥0∞) < 1 := by
  have h4 : ENNReal.ofReal (∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))) ≤
      ((4 : ℝ≥0) : ℝ≥0∞) := by
    have hEq : ((4 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) := by norm_num
    rw [hEq]
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).2 tsum_powerLaw_sq_le_four
  calc ((1 / 10 : ℝ≥0) : ℝ≥0∞) *
        (((∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))).toNNReal : ℝ≥0) : ℝ≥0∞)
      = ((1 / 10 : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (∑' z : Fin 1 → ℤ, (‖z‖ : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1))) := rfl
    _ ≤ ((1 / 10 : ℝ≥0) : ℝ≥0∞) * ((4 : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ < 1 := by
        rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
        norm_num

/-- **Concrete instance**: at `d = 1`, `α = 1` (`K (s) = s⁻²`), `β = 1/10`, every root `o` and
every cap `B`, the capped expected cluster size under the cut-off power law is differentiable at
`r₀ = 1/2`. This is `hasDerivAt_integral_cutoff_powerLaw_sup_capped` at `d = 1`, `α = 1`,
`β = 1/10`, so the high-temperature premise is satisfied at explicit parameters. -/
theorem differentiableAt_capped_cluster_moment_half (o : Fin 1 → ℤ) (B : ℕ) :
    DifferentiableAt ℝ (fun r : ℝ => ∫ (ω : Config (Fin 1 → ℤ)),
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ)
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (powerLawProfile 1 (((1 : ℕ) : ℝ) + 1)) r) (1 / 10))) (1 / 2) :=
  (hasDerivAt_integral_cutoff_powerLaw_sup_capped (d := 1) le_rfl (α := 1) one_pos
    beta_one_tenth_rowSum_lt_one o B).differentiableAt

end PercLib.Models.LongRange
