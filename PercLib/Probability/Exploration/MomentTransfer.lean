/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof module, using the scalar transfer adapted from repository `yujinhkim/lrp` at revision
`d5e0763c9187ea85e4877ae4f6a19ab0b58c1c4d`. No new probability model or acceptance of an unproved
probabilistic premise is introduced.
-/
module

public import PercLib.Probability.Exploration.MomentBound
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Integrated polynomial-moment transfer

Lower-integral consequences of the scalar polynomial/exponential comparison, with all
exponential-moment bounds left as explicit hypotheses. The random variable here is nonnegative
real-valued; infinite extended-natural cluster cardinalities are not converted to zero.

This is a new integration lemma built on the migrated scalar bound, not a proof of the
exploration's exponential cluster-moment estimate.
-/

@[expose] public section

open MeasureTheory

namespace PercLib.Probability.ExplorationEnvelope

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m : ℝ}

/-- **`PROOF.md` Lemma 6.1, integrated.** For `λ > 1`, `k ∈ ℕ` and a nonnegative `N : Ω → ℝ`,
`∫⁻ N^k dμ ≤ (k! / (log λ)^k) * ∫⁻ λ^N dμ`.

No measurability of `N` and no condition on `m` is needed: `ENNReal` lower integrals are monotone
for arbitrary functions and the constant factor only has to be finite. -/
theorem lintegral_pow_le_mul_lintegral_rpow {lam : ℝ} (hlam : 1 < lam) (k : ℕ) {N : Ω → ℝ}
    (hN : ∀ ω, 0 ≤ N ω) :
    ∫⁻ ω, ENNReal.ofReal ((N ω) ^ k) ∂μ
      ≤ ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k) *
          ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ := by
  have hC : (0:ℝ) ≤ (k.factorial : ℝ) / (Real.log lam) ^ k := by
    have hlog : (0:ℝ) < (Real.log lam) ^ k := pow_pos (Real.log_pos hlam) k
    have hfac : (0:ℝ) < (k.factorial : ℝ) := by positivity
    positivity
  calc ∫⁻ ω, ENNReal.ofReal ((N ω) ^ k) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k) *
            ENNReal.ofReal (lam ^ N ω) ∂μ := by
        refine lintegral_mono (fun ω => ?_)
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (pow_le_factorial_div_log_mul_rpow hlam k (hN ω))
    _ = ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k) *
          ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **`PROOF.md` Theorem 1 + Lemma 6.1.**  Under the exponential moment hypothesis
`∫⁻ λ^N ≤ 1/m` with `0 < m`, the `k`-th moment is at most `k! / (m (log λ)^k)`.

The hypotheses are exactly `0 < m` (to invert) and `λ > 1` (to take `log`); neither `m < 1` nor
the admissibility of `λ` is used — the latter is only what makes `PROOF.md` Theorem 1 available.
-/
theorem lintegral_pow_le_of_rpow_moment_le {lam : ℝ} (hm : 0 < m) (hlam : 1 < lam) (k : ℕ)
    {N : Ω → ℝ} (hN : ∀ ω, 0 ≤ N ω)
    (hmom : ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ ≤ ENNReal.ofReal (1 / m)) :
    ∫⁻ ω, ENNReal.ofReal ((N ω) ^ k) ∂μ
      ≤ ENNReal.ofReal ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) := by
  have hC : (0:ℝ) ≤ (k.factorial : ℝ) / (Real.log lam) ^ k := by
    have hlog : (0:ℝ) < (Real.log lam) ^ k := pow_pos (Real.log_pos hlam) k
    have hfac : (0:ℝ) < (k.factorial : ℝ) := by positivity
    positivity
  have hEq : (k.factorial : ℝ) / (Real.log lam) ^ k * (1 / m)
      = (k.factorial : ℝ) / (m * (Real.log lam) ^ k) := by
    field_simp
  calc ∫⁻ ω, ENNReal.ofReal ((N ω) ^ k) ∂μ
      ≤ ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k) *
          ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ :=
        lintegral_pow_le_mul_lintegral_rpow hlam k hN
    _ ≤ ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k) * ENNReal.ofReal (1 / m) := by
        gcongr
    _ = ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k * (1 / m)) :=
        (ENNReal.ofReal_mul hC).symm
    _ = ENNReal.ofReal ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) := by rw [hEq]

/-- **Assembled form.**  An admissible `λ` that also satisfies the exponential moment bound
`E[λ^N] ≤ 1/m` gives both the scalar bound of Lemma 6.1 and the uniform `k`-th moment bound
`k! / (m (log λ)^k)`.

The exponential moment hypothesis is exactly the open probabilistic input of `PROOF.md`
Theorem 1; this theorem only records what it yields. -/
theorem exists_lam_and_lintegral_moment_bound (hm : 0 < m) (hm1 : m < 1) (k : ℕ)
    {N : Ω → ℝ} (hN : ∀ ω, 0 ≤ N ω)
    (h : ∃ lam : ℝ, 1 < lam ∧ m * lam ≤ Real.exp (m - 1) ∧
      ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ ≤ ENNReal.ofReal (1 / m)) :
    ∃ lam : ℝ, 1 < lam ∧ m * lam ≤ Real.exp (m - 1) ∧
      (∀ x : ℝ, 0 ≤ x →
        x ^ k ≤ ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) * lam ^ x) ∧
      ∫⁻ ω, ENNReal.ofReal ((N ω) ^ k) ∂μ
        ≤ ENNReal.ofReal ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) := by
  obtain ⟨lam, h1, h2, h3⟩ := h
  exact ⟨lam, h1, h2, moment_bound_of_lt_one hm hm1 h1 k,
    lintegral_pow_le_of_rpow_moment_le hm h1 k hN h3⟩

end PercLib.Probability.ExplorationEnvelope
