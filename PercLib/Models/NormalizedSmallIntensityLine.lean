/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface and the intensity family `intensityProfile`. The
statements follow the wiki tag MTYL. No source text or code is copied.
-/
module

public import PercLib.Models.Line
public import PercLib.Models.NormalizedSmallIntensity
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The line example at small intensity (MTYL)

On `ℤ` let `J = 1/2` on nearest-neighbour pairs and `0` elsewhere (the hypothesis `hJ`; no
new definition), `q = intensityProfile J β` and `p = 1 - e^{-β/2}`.

* `tau_eq`: `τ(a,b) = p^{|b-a|}`;
* `chi_eq_div` and `chi_eq`: `χ = (1 + p)/(1 - p) = 2 e^{β/2} - 1`;
* `hasDerivAt_chi`: `d/dβ χ = e^{β/2}` at every `β > 0`;
* `triangle_eq`: `Δ = ∑' u v, τ(0,u) τ(u,v) τ(v,0) = 1 + 6 p² / (1 - p²)²`;
* `deriv_chi_lt` and `eventually_deriv_chi_lt`: `χ' < χ (χ - Δ) / (3 β² Δ²)` for every
  `0 < β < 1/48`, hence for all sufficiently small `β > 0`.

The quantities `χ` and `Δ` in the last item are the real numbers `(χ).toReal` and
`(Δ).toReal`, both finite.
-/

@[expose] public section
noncomputable section

open MeasureTheory PercLib.Probability PercLib.Percolation.Bond Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Models.NormalizedSmallIntensity

/-! ### Two-sided geometric sums -/

/-- The two-step sum `∑' v, P^{|v-n|} P^{|v|}` from a natural point `n`. -/
theorem tsum_pow_natAbs_mul_nat (P : ℝ≥0∞) (n : ℕ) :
    ∑' v : ℤ, P ^ (v - n).natAbs * P ^ (0 - v).natAbs =
      P ^ n * (n + (1 + P ^ 2) * (1 - P ^ 2)⁻¹) := by
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hneg : ∀ k : ℕ, P ^ ((-((k : ℤ) + 1)) - n).natAbs * P ^ (0 - (-((k : ℤ) + 1))).natAbs =
      P ^ n * (P ^ 2) ^ (k + 1) := by
    intro k
    have h1 : ((-((k : ℤ) + 1)) - n).natAbs = n + (k + 1) := by omega
    have h2 : (0 - (-((k : ℤ) + 1))).natAbs = k + 1 := by omega
    rw [h1, h2, pow_add, ← pow_mul, mul_comm (2 : ℕ), pow_mul, mul_assoc]
    ring
  simp_rw [hneg]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
  set f : ℕ → ℝ≥0∞ := fun k => P ^ (((k : ℤ)) - n).natAbs * P ^ (0 - (k : ℤ)).natAbs with hf
  have hsplit : ∑' k, f k = ∑ i ∈ Finset.range n, f i + ∑' i, f (i + n) :=
    (ENNReal.summable.sum_add_tsum_nat_add' (f := f) (k := n)).symm
  rw [hsplit]
  have hlow : ∀ i ∈ Finset.range n, f i = P ^ n := by
    intro i hi
    simp only [hf]
    have hi := Finset.mem_range.1 hi
    have h1 : ((i : ℤ) - n).natAbs = n - i := by omega
    have h2 : (0 - (i : ℤ)).natAbs = i := by omega
    rw [h1, h2, ← pow_add, Nat.sub_add_cancel hi.le]
  have hhigh : ∀ i : ℕ, f (i + n) = P ^ n * (P ^ 2) ^ i := by
    intro i
    simp only [hf]
    have h1 : (((i + n : ℕ) : ℤ) - n).natAbs = i := by omega
    have h2 : (0 - ((i + n : ℕ) : ℤ)).natAbs = i + n := by omega
    rw [h1, h2, pow_add, ← pow_mul]
    ring
  rw [Finset.sum_congr rfl hlow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp_rw [hhigh]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  ring

/-- The two-step sum is even in the starting point. -/
theorem tsum_pow_natAbs_mul_neg (P : ℝ≥0∞) (u : ℤ) :
    ∑' v : ℤ, P ^ (v - (-u)).natAbs * P ^ (0 - v).natAbs =
      ∑' v : ℤ, P ^ (v - u).natAbs * P ^ (0 - v).natAbs := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun v => ?_
  simp only [Equiv.neg_apply]
  congr 2 <;> omega

/-- The closed two-sided geometric triangle, in closed form up to `∑ n rⁿ`. -/
theorem tsum_triangle_pow_natAbs (P : ℝ≥0∞) :
    ∑' u : ℤ, ∑' v : ℤ, P ^ (u - 0).natAbs * P ^ (v - u).natAbs * P ^ (0 - v).natAbs =
      (1 + P ^ 2) * (1 - P ^ 2)⁻¹ + 2 * ∑' n : ℕ, (n : ℝ≥0∞) * (P ^ 2) ^ n +
        2 * ((1 + P ^ 2) * (1 - P ^ 2)⁻¹) * (P ^ 2 * (1 - P ^ 2)⁻¹) := by
  set c := (1 + P ^ 2) * (1 - P ^ 2)⁻¹
  have hinner : ∀ u : ℤ, ∑' v : ℤ, P ^ (u - 0).natAbs * P ^ (v - u).natAbs * P ^ (0 - v).natAbs =
      P ^ u.natAbs * ∑' v : ℤ, P ^ (v - u).natAbs * P ^ (0 - v).natAbs := by
    intro u
    simp_rw [mul_assoc, sub_zero]
    exact ENNReal.tsum_mul_left
  simp_rw [hinner]
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hpos : ∀ n : ℕ, P ^ (n : ℤ).natAbs * ∑' v : ℤ, P ^ (v - n).natAbs * P ^ (0 - v).natAbs =
      (P ^ 2) ^ n * (n + c) := by
    intro n
    rw [tsum_pow_natAbs_mul_nat, Int.natAbs_natCast, ← mul_assoc, ← pow_add, ← pow_mul,
      two_mul]
  have hneg : ∀ n : ℕ, P ^ (-((n : ℤ) + 1)).natAbs *
      ∑' v : ℤ, P ^ (v - (-((n : ℤ) + 1))).natAbs * P ^ (0 - v).natAbs =
      (P ^ 2) ^ (n + 1) * ((n + 1 : ℕ) + c) := by
    intro n
    rw [tsum_pow_natAbs_mul_neg, ← hpos (n + 1)]
    congr 1
  simp_rw [hpos, hneg]
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hS : ∑' n : ℕ, (n : ℝ≥0∞) * (P ^ 2) ^ n = ∑' n : ℕ,
      ((n + 1 : ℕ) : ℝ≥0∞) * (P ^ 2) ^ (n + 1) := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp
  have hsplit : ∑' n : ℕ, (P ^ 2) ^ (n + 1) * (((n + 1 : ℕ) : ℝ≥0∞) + c) =
      ∑' n : ℕ, (n : ℝ≥0∞) * (P ^ 2) ^ n + c * (P ^ 2 * (1 - P ^ 2)⁻¹) := by
    rw [hS, ← ENNReal.tsum_geometric_add_one, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact tsum_congr fun n => by ring
  simp only [pow_zero, CharP.cast_eq_zero, zero_add, one_mul]
  rw [hsplit]
  ring

/-- The series `∑ n yⁿ` for `0 ≤ y < 1`, in `ℝ≥0∞`. -/
theorem tsum_nat_mul_ofReal_pow {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal y ^ n = ENNReal.ofReal (y / (1 - y) ^ 2) := by
  have hn : ‖y‖ < 1 := by rwa [Real.norm_of_nonneg hy0]
  rw [← tsum_coe_mul_geometric_of_norm_lt_one hn,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable]
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow hy0]

/-- `(1 - y)⁻¹` for `y < 1`, in `ℝ≥0∞`. -/
theorem inv_one_sub_ofReal {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (1 - ENNReal.ofReal y)⁻¹ = ENNReal.ofReal (1 / (1 - y)) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hy0, one_div,
    ENNReal.ofReal_inv_of_pos (by linarith)]

/-- **The closed two-sided geometric triangle.** For `0 ≤ x < 1`,
`∑' u v, x^{|u|} x^{|v-u|} x^{|v|} = 1 + 6 x² / (1 - x²)²`. -/
theorem tsum_triangle_ofReal_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' u : ℤ, ∑' v : ℤ, ENNReal.ofReal x ^ (u - 0).natAbs * ENNReal.ofReal x ^ (v - u).natAbs *
      ENNReal.ofReal x ^ (0 - v).natAbs = ENNReal.ofReal (1 + 6 * x ^ 2 / (1 - x ^ 2) ^ 2) := by
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy1 : x ^ 2 < 1 := by nlinarith
  have hd : 0 < 1 - x ^ 2 := by linarith
  rw [tsum_triangle_pow_natAbs, ← ENNReal.ofReal_pow hx0, tsum_nat_mul_ofReal_pow hy0 hy1,
    inv_one_sub_ofReal hy0 hy1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hy0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hy0,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- The real inequality behind the last item, for `0 < β < 1/48`. -/
theorem exp_half_lt_of_small {β : ℝ} (hβ : 0 < β) (hβ' : β < 1 / 48) :
    Real.exp (β / 2) <
      (2 * Real.exp (β / 2) - 1) * ((2 * Real.exp (β / 2) - 1) -
          (1 + 6 * (1 - Real.exp (-(β / 2))) ^ 2 / (1 - (1 - Real.exp (-(β / 2))) ^ 2) ^ 2)) /
        (3 * β ^ 2 *
          (1 + 6 * (1 - Real.exp (-(β / 2))) ^ 2 / (1 - (1 - Real.exp (-(β / 2))) ^ 2) ^ 2) ^
              2) := by
  set x := 1 - Real.exp (-(β / 2)) with hx
  set D := 1 + 6 * x ^ 2 / (1 - x ^ 2) ^ 2 with hD
  set E := Real.exp (β / 2)
  have hE1 : 1 + β / 2 ≤ E := by have := Real.add_one_le_exp (β / 2); linarith
  have hE2 : E ≤ 1 + β := by
    have h := Real.abs_exp_sub_one_le (x := β / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [abs_of_pos (by linarith : 0 < β / 2)] at h
    have := (abs_le.1 h).2
    linarith
  have hx0 : 0 ≤ x := by
    have : Real.exp (-(β / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hxt : x ≤ β / 2 := by have := Real.add_one_le_exp (-(β / 2)); linarith
  have hy : x ^ 2 ≤ β ^ 2 / 4 := by nlinarith
  have hy1 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hden : 9 / 16 ≤ (1 - x ^ 2) ^ 2 := by nlinarith
  have hfrac0 : 0 ≤ 6 * x ^ 2 / (1 - x ^ 2) ^ 2 := by positivity
  have hfrac : 6 * x ^ 2 / (1 - x ^ 2) ^ 2 ≤ 8 / 3 * β ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hD1 : 1 ≤ D := by linarith
  have hD2 : D ≤ 2 := by nlinarith
  have hchi : 1 ≤ 2 * E - 1 := by linarith
  have hgap : β / 2 ≤ (2 * E - 1) - D := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  calc E * (3 * β ^ 2 * D ^ 2) < 2 * (3 * β ^ 2 * 4) := by
        have hD4 : D ^ 2 ≤ 4 := by nlinarith
        have hpos : 0 < 3 * β ^ 2 * D ^ 2 := by positivity
        calc E * (3 * β ^ 2 * D ^ 2) < 2 * (3 * β ^ 2 * D ^ 2) :=
              mul_lt_mul_of_pos_right (by linarith) hpos
          _ ≤ 2 * (3 * β ^ 2 * 4) := by gcongr
    _ ≤ 1 * (β / 2) := by nlinarith
    _ ≤ (2 * E - 1) * ((2 * E - 1) - D) := by
        apply mul_le_mul hchi hgap (by linarith) (by linarith)

/-! ### The model -/

variable (J : Sym2 ℤ → ℝ≥0) (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0)
include hJ

/-- The profile is the nearest-neighbour profile with parameter `q s(0,1)`. -/
theorem line_profile_eq (β : ℝ≥0) (a b : ℤ) (_hab : a ≠ b) :
    intensityProfile J β s(a, b) =
      if |b - a| = 1 then intensityProfile J β s(0, 1) else 0 := by
  split_ifs with h
  · apply Subtype.ext
    change 1 - Real.exp (-(β : ℝ) * (J s(a, b) : ℝ)) = 1 - Real.exp (-(β : ℝ) * (J s(0, 1) : ℝ))
    simp [hJ, h]
  · apply Subtype.ext
    change 1 - Real.exp (-(β : ℝ) * (J s(a, b) : ℝ)) = 0
    simp [hJ, h]

/-- The nearest-neighbour probability is `p = 1 - e^{-β/2}`. -/
theorem line_toNNReal_profile (β : ℝ≥0) :
    (unitInterval.toNNReal (intensityProfile J β s(0, 1)) : ℝ≥0∞) =
      ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2))) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  change 1 - Real.exp (-(β : ℝ) * (J s(0, 1) : ℝ)) = _
  simp only [hJ, show |(1 : ℤ) - 0| = 1 by norm_num, ↓reduceIte]
  congr 2
  push_cast
  ring

/-- **Two-point function.** `τ(a,b) = p^{|b-a|}` with `p = 1 - e^{-β/2}`. -/
theorem line_tau_eq (β : ℝ≥0) (a b : ℤ) :
    tau (intensityProfile J β) a b =
      ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2))) ^ (b - a).natAbs := by
  rw [PercLib.Models.Line.tau_eq_pow _ _ (line_profile_eq J hJ β), line_toNNReal_profile J hJ]

/-- **Susceptibility.** `χ = (1 + p)/(1 - p)`. -/
theorem line_chi_eq_div (β : ℝ≥0) (a : ℤ) :
    chi (intensityProfile J β) a =
      (1 + ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2)))) /
        (1 - ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2)))) := by
  rw [PercLib.Models.Line.chi_eq _ _ (line_profile_eq J hJ β), line_toNNReal_profile J hJ]

/-- **Susceptibility.** `χ = 2 e^{β/2} - 1`. -/
theorem line_chi_eq (β : ℝ≥0) (a : ℤ) :
    chi (intensityProfile J β) a = ENNReal.ofReal (2 * Real.exp ((β : ℝ) / 2) - 1) := by
  have he := Real.exp_pos (-((β : ℝ) / 2))
  have he1 : Real.exp (-((β : ℝ) / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := β.coe_nonneg; linarith)
  rw [line_chi_eq_div J hJ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
    (by linarith), ← ENNReal.ofReal_sub _ (by linarith), ← ENNReal.ofReal_div_of_pos
    (by linarith)]
  congr 1
  rw [Real.exp_neg] at he ⊢
  field_simp
  ring

/-- **Derivative.** `d/dβ χ = e^{β/2}` at every `β > 0`. -/
theorem line_hasDerivAt_chi {β : ℝ} (hβ : 0 < β) (a : ℤ) :
    HasDerivAt (fun b : ℝ => (chi (intensityProfile J b.toNNReal) a).toReal)
      (Real.exp (β / 2)) β := by
  have hf : HasDerivAt (fun b : ℝ => 2 * Real.exp (b / 2) - 1) (Real.exp (β / 2)) β := by
    have h := (((hasDerivAt_id β).div_const 2).exp.const_mul 2).sub_const 1
    simp only [id_eq] at h
    convert h using 1
    ring
  refine hf.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hβ] with b hb
  rw [line_chi_eq J hJ, Real.coe_toNNReal _ hb.le, ENNReal.toReal_ofReal]
  have := Real.add_one_le_exp (b / 2)
  linarith

/-- **Triangle.** `Δ = 1 + 6 p² / (1 - p²)²` with `p = 1 - e^{-β/2}`. -/
theorem line_triangle_eq (β : ℝ≥0) :
    ∑' u, ∑' v, tau (intensityProfile J β) 0 u * tau (intensityProfile J β) u v *
        tau (intensityProfile J β) v 0 =
      ENNReal.ofReal (1 + 6 * (1 - Real.exp (-((β : ℝ) / 2))) ^ 2 /
        (1 - (1 - Real.exp (-((β : ℝ) / 2))) ^ 2) ^ 2) := by
  simp_rw [line_tau_eq J hJ]
  have he := Real.exp_pos (-((β : ℝ) / 2))
  have he1 : Real.exp (-((β : ℝ) / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := β.coe_nonneg; linarith)
  exact tsum_triangle_ofReal_pow (by linarith) (by linarith)

/-- **Last item.** For every `0 < β < 1/48`, `χ' < χ (χ - Δ) / (3 β² Δ²)`, where
`χ` and `Δ` are the (finite) susceptibility and closed triangle at the root `0`, as real
numbers, and `χ'` is the derivative of `β ↦ χ` at `β`. -/
theorem line_deriv_chi_lt {β : ℝ} (hβ : 0 < β) (hβ' : β < 1 / 48) :
    deriv (fun b : ℝ => (chi (intensityProfile J b.toNNReal) 0).toReal) β <
      (chi (intensityProfile J β.toNNReal) 0).toReal *
        ((chi (intensityProfile J β.toNNReal) 0).toReal -
          (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) 0 u *
            tau (intensityProfile J β.toNNReal) u v *
            tau (intensityProfile J β.toNNReal) v 0).toReal) /
        (3 * β ^ 2 * (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) 0 u *
            tau (intensityProfile J β.toNNReal) u v *
            tau (intensityProfile J β.toNNReal) v 0).toReal ^ 2) := by
  rw [(line_hasDerivAt_chi J hJ hβ 0).deriv, line_chi_eq J hJ, line_triangle_eq J hJ,
    Real.coe_toNNReal _ hβ.le, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · exact exp_half_lt_of_small hβ hβ'
  · have he := Real.exp_pos (-(β / 2))
    positivity
  · have := Real.add_one_le_exp (β / 2)
    linarith

/-- **Last item, eventual form.** For all sufficiently small `β > 0`,
`χ' < χ (χ - Δ) / (3 β² Δ²)`. -/
theorem line_eventually_deriv_chi_lt :
    ∀ᶠ β in 𝓝[>] (0 : ℝ),
      deriv (fun b : ℝ => (chi (intensityProfile J b.toNNReal) 0).toReal) β <
        (chi (intensityProfile J β.toNNReal) 0).toReal *
          ((chi (intensityProfile J β.toNNReal) 0).toReal -
            (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) 0 u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v 0).toReal) /
          (3 * β ^ 2 * (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) 0 u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v 0).toReal ^ 2) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 48 by norm_num))] with β hβ hβ'
  exact line_deriv_chi_lt J hJ hβ hβ'

omit hJ in
/-- Non-vacuity: the nearest-neighbour kernel `1/2` exists, so every statement above applies; for
instance at `β = 1/100`. -/
example : ∃ J : Sym2 ℤ → ℝ≥0, (∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0) ∧
    chi (intensityProfile J (1 / 100)) 0 = ENNReal.ofReal
        (2 * Real.exp (((1 / 100 : ℝ≥0) : ℝ) / 2) - 1) ∧
    deriv (fun b : ℝ => (chi (intensityProfile J b.toNNReal) 0).toReal) (1 / 100) <
      (chi (intensityProfile J (1 / 100 : ℝ).toNNReal) 0).toReal *
        ((chi (intensityProfile J (1 / 100 : ℝ).toNNReal) 0).toReal -
          (∑' u, ∑' v, tau (intensityProfile J (1 / 100 : ℝ).toNNReal) 0 u *
            tau (intensityProfile J (1 / 100 : ℝ).toNNReal) u v *
            tau (intensityProfile J (1 / 100 : ℝ).toNNReal) v 0).toReal) /
        (3 * (1 / 100) ^ 2 * (∑' u, ∑' v, tau (intensityProfile J (1 / 100 : ℝ).toNNReal) 0 u *
            tau (intensityProfile J (1 / 100 : ℝ).toNNReal) u v *
            tau (intensityProfile J (1 / 100 : ℝ).toNNReal) v 0).toReal ^ 2) := by
  obtain ⟨J, hJ⟩ := exists_line_kernel
  exact ⟨J, hJ, line_chi_eq J hJ _ 0, line_deriv_chi_lt J hJ (by norm_num) (by norm_num)⟩

end PercLib.Models.NormalizedSmallIntensity
