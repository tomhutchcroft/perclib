/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against the pinned mathlib. Mathematical content: Markov's
inequality applied to the weighted exponential moment `E[X e^{tX}] ≤ a / √(1 - 2tM²)` with the
parameter `t = 1/(2M²) - 1/(2k)` that minimises the resulting bound. No upstream proof is copied,
no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.UniformVolumeTail

/-!
# Optimized exponential cluster tails

Under the two-parameter moment hypothesis `E X^m ≤ (2m-3)!! a M^{2m-2}` (`m ≥ 1`), the
weighted exponential bound `E[X e^{tX}] ≤ a/√(1 - 2tM²)` for `0 ≤ t < (2M²)⁻¹` and Markov's
inequality give `P(X ≥ k) ≤ a e^{-tk} / (k √(1 - 2tM²))`. Choosing `t = 1/(2M²) - 1/(2k)`,
admissible for `k ≥ M²`, gives `P(X ≥ k) ≤ (a/M) √(e/k) e^{-k/(2M²)}`.

For independent bond percolation with `M = ⨆ x, χ(x) < ∞` this is applied to `X = |K_o|`
with `a = χ(o)`; when the susceptibility is the same at every vertex the prefactor is
`√(e/k)`.

## Main results

* `PercLib.Probability.measure_le_le_div_mul_sqrt_exp_div_of_moment_le`: the optimized tail
  under the moment hypothesis.
* `PercLib.Percolation.Bond.law_encard_cluster_ge_le_div_mul_sqrt_exp_div`: the optimized
  cluster-volume tail `P(|K_o| ≥ k) ≤ (χ(o)/M) √(e/k) e^{-k/(2M²)}` for `k ≥ M²`.
* `PercLib.Percolation.Bond.law_encard_cluster_ge_le_sqrt_exp_div_of_chi_eq`: the same with
  constant susceptibility, `P(|K_o| ≥ k) ≤ √(e/k) e^{-k/(2χ²)}` for `k ≥ χ²`.
-/

@[expose] public section

open Real MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {a M : ℝ}

/-- **Optimized exponential tail.** Under the two-parameter moment hypothesis
`E X^m ≤ (2m-3)!! a M^{2m-2}` (`m ≥ 1`), for every real `k ≥ M²`,
`P(X ≥ k) ≤ (a/M) √(e/k) e^{-k/(2M²)}`. The proof applies Markov's inequality to
`X e^{tX}` at `t = 1/(2M²) - 1/(2k)`. -/
theorem measure_le_le_div_mul_sqrt_exp_div_of_moment_le (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {k : ℝ} (hk : M ^ 2 ≤ k) :
    P {ω | k ≤ X ω} ≤
      ENNReal.ofReal (a / M * sqrt (exp 1 / k) * exp (-(k / (2 * M ^ 2)))) := by
  have hM2 : 0 < M ^ 2 := by positivity
  have hk0 : 0 < k := hM2.trans_le hk
  set t := (2 * M ^ 2)⁻¹ - (2 * k)⁻¹ with htdef
  have ht : 0 ≤ t := by
    rw [htdef, sub_nonneg]
    exact inv_anti₀ (by positivity) (by linarith)
  have ht1 : t < (2 * M ^ 2)⁻¹ := by
    rw [htdef]; linarith [inv_pos.2 (by positivity : (0 : ℝ) < 2 * k)]
  have hB := lintegral_mul_exp_le_of_moment_le hX hX0 ha hM hmom ht ht1
  have hz : 1 - 2 * t * M ^ 2 = M ^ 2 / k := by
    rw [htdef]; field_simp; ring
  rw [hz] at hB
  refine (measure_le_ofReal_div (hX.mul (measurable_const.mul hX).exp)
    (mul_pos hk0 (exp_pos (t * k))) (fun ω hω => ?_) hB).trans_eq ?_
  · exact mul_le_mul hω (exp_le_exp.2 (mul_le_mul_of_nonneg_left hω ht)) (exp_pos _).le
      (hX0 ω)
  · congr 1
    have hsk : 0 < sqrt k := sqrt_pos.2 hk0
    have h1 : sqrt (M ^ 2 / k) = M / sqrt k := by
      rw [sqrt_div' _ hk0.le, sqrt_sq hM.le]
    have h2 : sqrt (exp 1 / k) = exp (1 / 2) / sqrt k := by
      rw [sqrt_div' _ hk0.le, ← exp_half, one_div]
    have h3 : t * k = k / (2 * M ^ 2) - 1 / 2 := by
      rw [htdef]; field_simp
    rw [h1, h2, h3, exp_sub, exp_neg]
    have hsq : sqrt k ^ 2 = k := sq_sqrt hk0.le
    generalize exp (k / (2 * M ^ 2)) = E at *
    have hh : 0 < exp (1 / 2) := exp_pos _
    generalize exp (1 / 2) = h at *
    generalize sqrt k = r at *
    subst hsq
    field_simp

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*} [Countable V]

/-- **Optimized cluster-volume tail.** For independent bond percolation with
`M = ⨆ x, χ(x) < ∞`, for every real `k ≥ M²`,
`P(|K_o| ≥ k) ≤ (χ(o)/M) √(e/k) e^{-k/(2M²)}`. -/
theorem law_encard_cluster_ge_le_div_mul_sqrt_exp_div (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {k : ℝ} (hk : (⨆ x, chi q x).toReal ^ 2 ≤ k) :
    law q {ω | ENNReal.ofReal k ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal ((chi q o).toReal / (⨆ x, chi q x).toReal * sqrt (exp 1 / k) *
        exp (-(k / (2 * (⨆ x, chi q x).toReal ^ 2)))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) k).trans
    (measure_le_le_div_mul_sqrt_exp_div_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hk)

/-- **Optimized cluster-volume tail, constant susceptibility.** If `χ(x) = χ(o) < ∞` for
every vertex `x` (for instance on a transitive model), then for every real `k ≥ χ(o)²`,
`P(|K_o| ≥ k) ≤ √(e/k) e^{-k/(2χ(o)²)}`. -/
theorem law_encard_cluster_ge_le_sqrt_exp_div_of_chi_eq (q : Sym2 V → unitInterval) (o : V)
    (hconst : ∀ x, chi q x = chi q o) (hfin : chi q o ≠ ⊤) {k : ℝ}
    (hk : (chi q o).toReal ^ 2 ≤ k) :
    law q {ω | ENNReal.ofReal k ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (sqrt (exp 1 / k) * exp (-(k / (2 * (chi q o).toReal ^ 2)))) := by
  have : Nonempty V := ⟨o⟩
  have hsup : (⨆ x, chi q x) = chi q o := by simp [hconst]
  have hM : (⨆ x, chi q x) ≠ ⊤ := hsup ▸ hfin
  have h := law_encard_cluster_ge_le_div_mul_sqrt_exp_div q o hM (k := k) (by rwa [hsup])
  have hpos : (chi q o).toReal ≠ 0 :=
    (one_pos.trans_le (one_le_toReal_chi_le_toReal_iSup q o hM).1).ne'
  rwa [hsup, div_self hpos, one_mul] at h

/-! ### Non-vacuity -/

/-- The zero profile on `ℤ` has `χ ≡ 1`, so the optimized tail applies with `M = χ(o) = 1`. -/
example (k : ℝ) (hk : 1 ≤ k) :
    law (fun _ : Sym2 ℤ => (0 : unitInterval))
        {ω | ENNReal.ofReal k ≤ ((cluster ω (0 : ℤ)).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (sqrt (exp 1 / k) * exp (-(k / (2 * 1 ^ 2)))) := by
  have h1 : ∀ x : ℤ, chi (fun _ : Sym2 ℤ => (0 : unitInterval)) x = 1 :=
    chi_eq_one_of_offDiagonal_zero _ fun _ _ _ => rfl
  have h := law_encard_cluster_ge_le_sqrt_exp_div_of_chi_eq
    (fun _ : Sym2 ℤ => (0 : unitInterval)) 0 (fun x => by rw [h1, h1]) (by rw [h1]; simp)
    (k := k) (by rw [h1]; simpa using hk)
  rwa [h1, ENNReal.toReal_one] at h

end PercLib.Percolation.Bond
