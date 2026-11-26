/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Existence and positivity of the constant `A₃` of Proposition I.3.2 of T. Hutchcroft,
*Critical long-range percolation I: High effective dimension*, arXiv:2508.18807v1, §I.3.2,
and the assembly of (I.3.2) and (I.3.3) from the ghost comparison.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file `PercLib/CriticalLRP/Analysis/A3Limit.lean`;
licence Apache-2.0 as declared in that commit's file headers and
`third_party/critical-lrp/NOTICE.md`; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the structure `RVPosData` is unbundled into the hypotheses of
`PercLib/Analysis/RegularVariation/GeneralInverse.lean`; `mean`, `sbMean`, `sizeBiasedLaw`,
`lapDefect`, `A3cand` and `FullLawGhostRatio` are written out, with the constant
`A₁ A₂^{-1/a}` written `A₁ / A₂^{1/a}`; the kernel `kern` (value `0` at `0`) is the kernel
`f_λ` of `PercLib/Probability/SizeBiasLimits.lean` (value `λ` at `0`), which is positive
everywhere, so the hypotheses `Q∞ {0} = 0` (and `Q∞ (-∞, 0) = 0`, which follows from the weak
convergence) are removed; `tendsto_of_relCauchy`, `A3cand_relCauchy` and `A3cand_le_of_tendsto`
are the abstract lemmas `exists_tendsto_atTop_of_forall_le_one_add_mul`,
`forall_le_one_add_mul_of_comparison` and `eventually_le_of_comparison` of
`PercLib/Analysis/VolumeTail/MGFAssembly.lean`; `a3Limit_exists`, `A3cand_le_of_tendsto`,
`a3_pos`, `a3_ne_zero` and `a3_mgf_of_fullLawGhostRatio` are merged into
`exists_tendsto_laplace_div_genInv_of_comparison`; `A3cand_nonneg` is the weak form of
`div_rpow_mul_rpow_neg_mul_integral_laplaceKernel_pos`; the regular variation of the inverse
and the first-moment integrability are derived instead of assumed; hypotheses the proofs do not
use are removed; declarations are renamed; `import Mathlib`, `autoImplicit`, disabled linters and
`#print` lines are removed.
-/
module

public import PercLib.Analysis.VolumeTail.MGFAssembly
public import PercLib.Analysis.VolumeTail.Endpoint

/-! # The constant `A₃` of Proposition I.3.2

Proposition I.3.2 defines `A₃ = (A₁ / A₂^{1/a}) lim_{λ→∞} λ^{-(a-1)/a} ∫ f_λ dQ∞`, an implicitly
convergent limit. Under the uniform ghost comparison of the uncut law with the cut-off laws (the
ratio form of (I.3.5), (I.3.6)), the candidate constants are relatively Cauchy, so the limit
exists; it lies above every candidate on a tail, and the candidates are positive, so `A₃ > 0`.
Without the comparison positivity can fail: for `Q∞ = δ₁` and `a > 1` the candidates tend to
`0`.

## Main results

* `laplaceKernel_pos`, `integral_laplaceKernel_pos`: the kernel `f_λ` and its integrals are
  positive.
* `exists_tendsto_laplace_div_genInv_of_comparison`: `A₃` exists, is positive, and (I.3.2)
  holds with it.
* `exists_tendsto_measure_Ici_div_genInv_of_comparison`: the tail asymptotic (I.3.3) for
  `1 / a ≤ 1`.
* `exists_tendsto_laplace_div_and_tendsto_measure_Ici_div_of_comparison`: (I.3.2) and (I.3.3),
  with `1 / a ≤ 1` derived from the moments.
* `tendsto_div_rpow_mul_rpow_neg_mul_integral_laplaceKernel_dirac_one`: the candidates for
  `Q∞ = δ₁`, `a > 1` tend to `0`.

These assemble Proposition I.3.2 from its hypotheses (1)-(4) and the comparison hypothesis; the
comparison (the ratio form of (I.3.5), (I.3.6)) is an explicit hypothesis, so this is not a
proof of that proposition.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory Real
open scoped Topology ENNReal

namespace PercLib.Analysis

open PercLib.Probability

/-! ### Positivity of the kernel integrals -/

/-- **The kernel `f_λ` is positive** for `λ > 0`: `(1 - e^{-λy}) / y > 0` for `y ≠ 0`, and
`f_λ(0) = λ`. -/
theorem laplaceKernel_pos {lam y : ℝ} (hlam : 0 < lam) :
    0 < if y = 0 then lam else (1 - exp (-(lam * y))) / y := by
  split_ifs with hy
  · exact hlam
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · refine div_pos_of_neg_of_neg ?_ hneg
    have : 1 < exp (-(lam * y)) := one_lt_exp_iff.2 (by nlinarith)
    linarith
  · refine div_pos ?_ hpos
    have : exp (-(lam * y)) < 1 := exp_lt_one_iff.2 (by nlinarith)
    linarith

/-- **The kernel integral is positive**: `∫ f_λ dQ > 0` for a probability law `Q` on
`[0, ∞)` and `λ > 0`. No hypothesis on the atom of `Q` at `0` is needed. -/
theorem integral_laplaceKernel_pos {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ y ∂Q, 0 ≤ y) {lam : ℝ} (hlam : 0 < lam) :
    0 < ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Q := by
  have hint : Integrable (fun y => if y = 0 then lam else (1 - exp (-(lam * y))) / y) Q := by
    refine Integrable.of_bound (continuous_laplaceKernel lam).aestronglyMeasurable lam ?_
    filter_upwards [hQ] with y hy
    have h := laplaceKernel_mem_Icc hlam.le hy
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  rw [integral_pos_iff_support_of_nonneg (fun y => (laplaceKernel_pos hlam).le) hint,
    show Function.support (fun y => if y = 0 then lam else (1 - exp (-(lam * y))) / y) = univ
      from eq_univ_of_forall fun y => (laplaceKernel_pos hlam).ne', measure_univ]
  exact one_pos

/-- **The candidate constants are positive**:
`(A₁ / A₂^{1/a}) λ^{-(a-1)/a} ∫ f_λ dQ > 0` for `A₁, A₂, λ > 0` and `Q` a probability law on
`[0, ∞)`. -/
theorem div_rpow_mul_rpow_neg_mul_integral_laplaceKernel_pos {A₁ A₂ a lam : ℝ} {Q : Measure ℝ}
    [IsProbabilityMeasure Q] (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hQ : ∀ᵐ y ∂Q, 0 ≤ y)
    (hlam : 0 < lam) :
    0 < A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
      ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Q := by
  have := integral_laplaceKernel_pos hQ hlam
  have := Real.rpow_pos_of_pos hA₂ (1 / a)
  have := Real.rpow_pos_of_pos hlam (-((a - 1) / a))
  positivity

/-! ### The constant `A₃` -/

/-- **`A₃` exists, is positive, and gives (I.3.2).** Let `μ_r`, `Q_r`, `Q∞`, `f`, `x₀`,
`A₁ > 0`, `A₂`, `a`, `α` be as in `tendsto_laplace_div_genInv_rpow_mul`, and let `μ∞` satisfy
the ghost comparison: for every `η ∈ (0, 1/2]` there is `Λ > 0` such that for every `λ ≥ Λ`, for
all small `h > 0`, the Laplace defects of `μ∞` and of the cut-off law at
`r_λ(h) = genInv f x₀ (λ / (A₂ h))` compare within the factor `(1 - η)⁻¹`. Then there is
`A₃ > 0` with
* `(A₁ / A₂^{1/a}) λ^{-(a-1)/a} ∫ f_λ dQ∞ → A₃` as `λ → ∞` (the limit defining `A₃`);
* `E_∞[1 - e^{-hX}] / (g(1/h)^α h) → A₃` as `h ↓ 0`, `g = genInv f x₀` (that is, (I.3.2));
* the candidate constants are at most `A₃` for all large `λ`. -/
theorem exists_tendsto_laplace_div_genInv_of_comparison (mu : ℝ → Measure ℝ)
    (muinf : Measure ℝ) (Qinf : Measure ℝ) [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ}
    (hmeas : Measurable f) (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < f x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ a α : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam, Λ ≤ lam →
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h))) ≤
          ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
        ∫ x, (1 - exp (-(h * x))) ∂muinf ≤
          (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) * (1 - η)⁻¹) :
    ∃ A₃ : ℝ, 0 < A₃ ∧
      Tendsto (fun lam => A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
        ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf) atTop (𝓝 A₃) ∧
      Tendsto (fun h : ℝ => (∫ x, (1 - exp (-(h * x))) ∂muinf) / (genInv f x₀ (1 / h) ^ α * h))
        (𝓝[>] 0) (𝓝 A₃) ∧
      ∀ᶠ lam in atTop, A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
        ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf ≤ A₃ := by
  have hρ : 0 < ρ := hρα ▸ mul_pos ha hα
  have hN : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < genInv f x₀ (1 / h) ^ α * h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_pos (Real.rpow_pos_of_pos (hf.genInv_pos hρ hmeas hx₀ _) α) hh
  obtain ⟨A₃, -, hc, hU, hle⟩ := exists_tendsto_of_comparison
    (L := fun lam h => ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) hN
    (fun lam hlam => tendsto_laplace_div_genInv_rpow_mul_rpow_neg mu Qinf hmeas hf hx₀ hpos
      hbdd hmu hEpos hSpos hprob hconv hA₂ ha hα hρα hE hS hlam)
    (fun η hη hη2 => (hG η hη hη2).imp fun _ h => h.2)
  have hQr : ∀ r, ∀ᵐ y ∂(((mu r).withDensity fun x => ENNReal.ofReal (x / ∫ x, x ∂mu r)).map
      fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)), 0 ≤ y := fun r =>
    ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy)
      (map_withDensity_ofReal_div_Iio_zero (mu r) (X := fun x => x) measurable_id
        (ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) (hmu r))) _ (hSpos r)))
  have hQ : ∀ᵐ y ∂Qinf, 0 ≤ y := ae_nonneg_of_tendsto (Q := fun r => (((mu r).withDensity
    fun x => ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
      x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) hQr hconv
  obtain ⟨lam, hlamle, hlam0⟩ := (hle.and (eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨A₃, lt_of_lt_of_le (div_rpow_mul_rpow_neg_mul_integral_laplaceKernel_pos hA₁ hA₂ hQ
    hlam0) hlamle, hc, hU, hle⟩

/-- **The tail asymptotic (I.3.3) from the ghost comparison**, for `1 / a ≤ 1`: under the
hypotheses of `exists_tendsto_laplace_div_genInv_of_comparison`, for a probability law `μ∞` on
`[0, ∞)` there is `A₃ > 0` with `μ∞([x, ∞)) / ((A₃ / Γ(1/a)) g(x)^α / x) → 1`,
`g = genInv f x₀`. -/
theorem exists_tendsto_measure_Ici_div_genInv_of_comparison (mu : ℝ → Measure ℝ)
    (muinf : Measure ℝ) [IsProbabilityMeasure muinf] (hmuinf : muinf (Iio 0) = 0)
    (Qinf : Measure ℝ) [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ}
    (hmeas : Measurable f) (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < f x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ a α : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (ha : 0 < a) (hα : 0 < α) (ha1 : 1 / a ≤ 1)
    (hρα : ρ = a * α)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam, Λ ≤ lam →
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h))) ≤
          ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
        ∫ x, (1 - exp (-(h * x))) ∂muinf ≤
          (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) * (1 - η)⁻¹) :
    ∃ A₃ : ℝ, 0 < A₃ ∧
      Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
        ((A₃ / Gamma (1 / a)) * (genInv f x₀ x ^ α / x))) atTop (𝓝 1) := by
  have hρ : 0 < ρ := hρα ▸ mul_pos ha hα
  obtain ⟨A₃, hA₃, -, hU, -⟩ := exists_tendsto_laplace_div_genInv_of_comparison mu muinf Qinf
    hmeas hf hx₀ hpos hbdd hmu hEpos hSpos hprob hconv hA₁ hA₂ ha hα hρα hE hS hG
  have hg : RegularlyVarying (1 / (a * α)) (genInv f x₀) := by
    rw [← hρα]
    exact hf.regularlyVarying_genInv hρ hmeas hx₀ hpos hbdd
  refine ⟨A₃, hA₃, tendsto_measure_Ici_div_of_tendsto_laplace_div muinf hmuinf ha hα ha1 hg
    hA₃.ne' ?_⟩
  have h := hU.div_const A₃
  rw [div_self hA₃.ne'] at h
  refine h.congr' (Eventually.of_forall fun h => ?_)
  rw [div_div, mul_comm]

/-- **(I.3.2) and (I.3.3) from hypotheses (1)-(4) of Proposition I.3.2 and the ghost
comparison.** Let `μ_r` be probability laws on `[0, ∞)` with `E_r X² < ∞`, and let the other
data be as in `exists_tendsto_laplace_div_genInv_of_comparison`, for a probability law `μ∞` on
`[0, ∞)`. Then `a ≥ 1`, and there is `A₃ > 0` such that the candidate constants tend to `A₃`,
`E_∞[1 - e^{-hX}] / (A₃ g(1/h)^α h) → 1` as `h ↓ 0`, and
`μ∞([x, ∞)) / ((A₃ / Γ(1/a)) g(x)^α / x) → 1` as `x → ∞`, `g = genInv f x₀`. The comparison
hypothesis `hG` (the ratio form of (I.3.5), (I.3.6)) is not proved here. -/
theorem exists_tendsto_laplace_div_and_tendsto_measure_Ici_div_of_comparison
    (mu : ℝ → Measure ℝ) (hmuprob : ∀ r, IsProbabilityMeasure (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r))
    (muinf : Measure ℝ) [IsProbabilityMeasure muinf] (hmuinf : muinf (Iio 0) = 0)
    (Qinf : Measure ℝ) [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ}
    (hmeas : Measurable f) (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < f x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ a α : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam, Λ ≤ lam →
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h))) ≤
          ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
        ∫ x, (1 - exp (-(h * x))) ∂muinf ≤
          (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) * (1 - η)⁻¹) :
    1 ≤ a ∧ ∃ A₃ : ℝ, 0 < A₃ ∧
      Tendsto (fun lam => A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
        ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf) atTop (𝓝 A₃) ∧
      Tendsto (fun h : ℝ => (∫ x, (1 - exp (-(h * x))) ∂muinf) /
        (A₃ * (genInv f x₀ (1 / h) ^ α * h))) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
        ((A₃ / Gamma (1 / a)) * (genInv f x₀ x ^ α / x))) atTop (𝓝 1) := by
  have hS' : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / (A₂ * f r)) atTop
      (𝓝 1) := by
    have h := hS.div_const A₂
    rw [div_self hA₂.ne'] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    rw [div_div, mul_comm]
  have hge : ∀ᶠ r in atTop, (∫ x, x ∂mu r) ≤ (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r :=
    Eventually.of_forall fun r => integral_id_le_integral_sq_div (hint2 r) (hEpos r)
  have hone := one_le_of_tendsto_div_of_tendsto_div hA₁ hA₂ hα (hρα ▸ hf) hge hE hS'
  have ha1 : 1 / a ≤ 1 := by
    rw [div_le_one ha]
    exact hone
  obtain ⟨A₃, hA₃, hc, hU, -⟩ := exists_tendsto_laplace_div_genInv_of_comparison mu muinf Qinf
    hmeas hf hx₀ hpos hbdd hmu hEpos hSpos hprob hconv hA₁ hA₂ ha hα hρα hE hS hG
  have hmain : Tendsto (fun h : ℝ => (∫ x, (1 - exp (-(h * x))) ∂muinf) /
      (A₃ * (genInv f x₀ (1 / h) ^ α * h))) (𝓝[>] 0) (𝓝 1) := by
    have h := hU.div_const A₃
    rw [div_self hA₃.ne'] at h
    refine h.congr' (Eventually.of_forall fun h => ?_)
    rw [div_div, mul_comm]
  have hρ : 0 < ρ := hρα ▸ mul_pos ha hα
  have hg : RegularlyVarying (1 / (a * α)) (genInv f x₀) := by
    rw [← hρα]
    exact hf.regularlyVarying_genInv hρ hmeas hx₀ hpos hbdd
  exact ⟨hone, A₃, hA₃, hc, hmain, tendsto_measure_Ici_div_of_tendsto_laplace_div muinf hmuinf
    ha hα ha1 hg hA₃.ne' hmain⟩

/-- **Non-vacuity of the ghost comparison**: for the constant family `μ_r = μ∞` of a law on
`[0, ∞)`, the comparison hypothesis `hG` of `exists_tendsto_laplace_div_genInv_of_comparison`
holds for every `f`, `x₀` and `A₂`. -/
example (muinf : Measure ℝ) (hmuinf : muinf (Iio 0) = 0) (f : ℝ → ℝ) (x₀ A₂ : ℝ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam, Λ ≤ lam →
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∫ x, (1 - exp (-(h * x))) ∂(fun _ : ℝ => muinf) (genInv f x₀ (lam / (A₂ * h))) ≤
          ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
        ∫ x, (1 - exp (-(h * x))) ∂muinf ≤
          (∫ x, (1 - exp (-(h * x))) ∂(fun _ : ℝ => muinf) (genInv f x₀ (lam / (A₂ * h)))) *
            (1 - η)⁻¹ := by
  intro η hη hη2
  refine ⟨1, one_pos, fun lam _ => ?_⟩
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hD := integral_one_sub_exp_neg_mul_nonneg hmuinf (le_of_lt hh)
  refine ⟨le_rfl, le_mul_of_one_le_right hD ?_⟩
  rw [one_le_inv₀ (by linarith)]
  linarith

/-! ### The positivity boundary -/

/-- **For `Q∞ = δ₁` and `a > 1` the candidate constants tend to `0`**:
`(A₁ / A₂^{1/a}) λ^{-(a-1)/a} ∫ f_λ dδ₁ = (A₁ / A₂^{1/a}) λ^{-(a-1)/a} (1 - e^{-λ}) → 0`. So
positivity of `A₃` is not a consequence of hypotheses (1)-(4) and the existence of the limit;
it comes from the comparison. -/
theorem tendsto_div_rpow_mul_rpow_neg_mul_integral_laplaceKernel_dirac_one {A₁ A₂ a : ℝ}
    (ha : 1 < a) :
    Tendsto (fun lam => A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
      ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Measure.dirac (1 : ℝ))
      atTop (𝓝 0) := by
  have hβ : 0 < (a - 1) / a := div_pos (by linarith) (by linarith)
  have hexp : Tendsto (fun lam : ℝ => 1 - exp (-lam)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_exp_neg_atTop_nhds_zero
  have h := ((tendsto_rpow_neg_atTop hβ).const_mul (A₁ / A₂ ^ (1 / a))).mul hexp
  rw [mul_zero, zero_mul] at h
  refine h.congr' (Eventually.of_forall fun lam => ?_)
  simp

end PercLib.Analysis
