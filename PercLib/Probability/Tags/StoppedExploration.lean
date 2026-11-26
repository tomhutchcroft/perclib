/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the stopped martingale maximal bound used in the analysis of
stopped cluster explorations. Every statement restates a lemma proved in the imported module;
no new definition is introduced. Mathematical reference: T. Hutchcroft, "Power-law bounds for
critical long-range percolation below the upper-critical dimension" (arXiv:2008.11197v2),
Section 3.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.TruncatedMaximal

/-!
# Stopped explorations: martingale statement forms

Each theorem restates a result proved under its own name in
`PercLib.Probability.TruncatedMaximal`.

## Main results

* `maximal_bound_truncated_predictable_variance`
* `damped_maximum_of_predictable_variance_tail`
-/

@[expose] public section
noncomputable section
open MeasureTheory Finset
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}

/-- Maximal martingale bound with truncated predictable variance: for a real martingale with
`X 0 = 0` and square-integrable values, predictable quadratic variation
`Q n = ∑_{i<n} μ[(X_{i+1} − X_i)² | ℱ i]`, a stopping time `T` with values in
`ℕ∞ = WithTop ℕ`, `Q_T = sup_n Q_{n ∧ T}` and `M_T = sup_{n ≤ T} |X_n|`, every finite `λ ≥ 0`
satisfies `E[M_T² 1{Q_T ≤ λ}] ≤ 4 E[Q_T ∧ λ]`. -/
@[tag "HXNR"]
theorem maximal_bound_truncated_predictable_variance [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) (hX0 : X 0 = 0) (hL2 : ∀ n, MemLp (X n) 2 μ)
    {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T) (l : ℝ≥0) :
    ∫⁻ ω in {ω | (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) ≤ l},
        (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, min (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) (l : ℝ≥0∞) ∂μ :=
  setLIntegral_iSup_abs_sq_le_four_mul_lintegral_min hX hX0 hL2 hT l

/-- Damped martingale maximum from a predictable-variance power tail: under the assumptions of
`maximal_bound_truncated_predictable_variance`, if `μ (Q_T ≥ x) ≤ A x^{-θ}` for every real
`x > 0`, with `A > 0` and `0 ≤ θ < 1/2`, then for every `h > 0`,
`E[(M_T / Q_T)(1 - e^{-h Q_T}) 1{0 < Q_T < ∞}] ≤ C_θ A h^{1/2+θ}`, where
`C_θ = 2 · 2^{(1-θ)/2} / √(1-θ) · (1 / (1 - 2^{-(1/2+θ)}) + 1 / (2^{1/2-θ} - 1))`, and
`C_θ ≤ 32 / (1 - 2θ)`. -/
@[tag "4GBV"]
theorem damped_maximum_of_predictable_variance_tail [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) (hX0 : X 0 = 0) (hL2 : ∀ n, MemLp (X n) 2 μ)
    {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T) {A θ : ℝ} (hA : 0 < A) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1 / 2)
    (htail : ∀ x : ℝ, 0 < x → μ {ω | ENNReal.ofReal x ≤ ⨆ n : ℕ, ENNReal.ofReal
      (stoppedProcess (fun k ω => ∑ i ∈ range k,
        μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)} ≤ ENNReal.ofReal (A * x ^ (-θ)))
    {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω in {ω | 0 < (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) ∧
        (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) < ⊤},
        (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) *
          ENNReal.ofReal ((1 - Real.exp (-(h * (⨆ n : ℕ, ENNReal.ofReal
            (stoppedProcess (fun k ω => ∑ i ∈ range k,
              μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)).toReal))) /
            (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
              μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)).toReal) ∂μ ≤
      ENNReal.ofReal (2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) *
        (1 / (1 - 2 ^ (-(1 / 2 + θ))) + 1 / (2 ^ (1 / 2 - θ) - 1)) * A * h ^ (1 / 2 + θ)) ∧
    2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) *
        (1 / (1 - 2 ^ (-(1 / 2 + θ))) + 1 / (2 ^ (1 / 2 - θ) - 1)) ≤ 32 / (1 - 2 * θ) :=
  ⟨setLIntegral_iSup_abs_mul_one_sub_exp_div_le hX hX0 hL2 hT hA hθ0 hθ htail hh,
    two_mul_rpow_div_sqrt_mul_add_le hθ0 hθ⟩

end PercLib.Probability
