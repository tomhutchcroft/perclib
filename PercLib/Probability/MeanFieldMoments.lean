/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied and no definition is added.
Mathematical reference: mean-field cluster-size moments from a cubic second moment and the
tree-graph upper bounds `E T^k ≤ (2k-3)!! χ^{2k-1}` (Aizenman–Newman 1984; Heydenreich–van der
Hofstad, *Progress in high-dimensional percolation and random graphs*, Ch. 5).
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Moments of a cluster volume with a cubic second moment

Let `T ≥ 1` be a random variable with mean `χ`, second moment at least `α χ³` (`α > 0`)
and the tree-graph moment bounds `E T^k ≤ (2k-3)!! χ^{2k-1}`. Then `T` lies in the band
`[E T² / (2χ), (24 / α²) χ²]` with probability at least `α⁴ / (576 χ)`, and every real moment
`E T^r` (`r ≥ 1`) is comparable to `χ^{2r-1}` with constants depending only on `α` and `r`.

The band bound is proved without size-biasing: a weighted AM–GM inequality
`x² ≤ (t x + x³ / t) / 2` replaces the Paley–Zygmund step, and Markov's inequality controls the
upper tail. The moment upper bound uses the pointwise split
`x^r ≤ χ^{2r-2} x + χ^{2r-2k} x^k` at `x = χ²`.

## Main results

* `measureReal_band_ge_of_moments`: the band bound for a real random variable `X ≥ 0`.
* `le_integral_rpow_of_moments`: the moment lower bound `(α/2)^r α⁴/576 χ^{2r-1} ≤ E X^r`.
* `integral_rpow_le_of_moment_le`: the moment upper bound `E X^r ≤ (1 + D) χ^{2r-1}` from
  `E X^k ≤ D χ^{2k-1}`, `r ≤ k`.
* `measureReal_band_ge_of_tree_graph`: the band bound for a positive integer-valued `T`.
* `integral_rpow_bounds_of_tree_graph`: explicit two-sided moment bounds for such `T`.
* `exists_moment_comparison_of_tree_graph`: `E T^r ≍ χ^{2r-1}` and
  `E T^{r+1} / E T^r ≍ χ²` with constants depending only on `α` and `r`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Nat

namespace PercLib.Probability

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Weighted AM–GM: `x² ≤ (t x + x³ / t) / 2` for `x ≥ 0` and `t > 0`. -/
theorem sq_le_mul_add_cube_div {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    x ^ 2 ≤ (t * x + x ^ 3 / t) / 2 := by
  have h : 0 ≤ x * (x - t) ^ 2 / t := by positivity
  have e : (t * x + x ^ 3 / t) / 2 - x ^ 2 = x * (x - t) ^ 2 / t / 2 := by
    field_simp; ring
  linarith [e ▸ (show 0 ≤ x * (x - t) ^ 2 / t / 2 by positivity)]

/-- **Band bound.** Let `X ≥ 0` have mean `χ > 0`, `α χ³ ≤ E X² ≤ χ³` and `E X³ ≤ 3 χ⁵`, where
`α > 0`. Then `P(E X² / χ / 2 ≤ X ≤ (24/α²) χ²) ≥ α⁴ / (576 χ)`. -/
theorem measureReal_band_ge_of_moments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hi1 : Integrable X μ)
    (hi2 : Integrable (fun ω => X ω ^ 2) μ) (hi3 : Integrable (fun ω => X ω ^ 3) μ)
    {α : ℝ} (hα0 : 0 < α) (hχ : 0 < ∫ ω, X ω ∂μ)
    (h2l : α * (∫ ω, X ω ∂μ) ^ 3 ≤ ∫ ω, X ω ^ 2 ∂μ)
    (h2u : ∫ ω, X ω ^ 2 ∂μ ≤ (∫ ω, X ω ∂μ) ^ 3)
    (h3u : ∫ ω, X ω ^ 3 ∂μ ≤ 3 * (∫ ω, X ω ∂μ) ^ 5) :
    α ^ 4 / (576 * ∫ ω, X ω ∂μ) ≤
      μ.real {ω | (∫ ω, X ω ^ 2 ∂μ) / (∫ ω, X ω ∂μ) / 2 ≤ X ω ∧
        X ω ≤ 24 / α ^ 2 * (∫ ω, X ω ∂μ) ^ 2} := by
  set χ := ∫ ω, X ω ∂μ with hχdef
  set m2 := ∫ ω, X ω ^ 2 ∂μ with hm2
  set m3 := ∫ ω, X ω ^ 3 ∂μ with hm3
  set B := 24 / α ^ 2 with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBχ : 0 < B * χ ^ 2 := mul_pos hB0 (pow_pos hχ 2)
  have hm2nn : 0 ≤ m2 := integral_nonneg fun ω => sq_nonneg _
  set S := {ω | m2 / χ / 2 ≤ X ω} with hSdef
  set H := {ω | B * χ ^ 2 < X ω} with hHdef
  have hS : MeasurableSet S := measurableSet_le measurable_const hXm
  have hH : MeasurableSet H := measurableSet_lt measurable_const hXm
  have hband : {ω | m2 / χ / 2 ≤ X ω ∧ X ω ≤ B * χ ^ 2} = S \ H := by
    ext ω; simp [S, H, not_lt]
  rw [hband]
  -- the second moment carried by `S`
  have h1 : m2 / 2 ≤ ∫ ω in S, X ω ^ 2 ∂μ := by
    have hc : ∫ ω in Sᶜ, X ω ^ 2 ∂μ ≤ ∫ ω in Sᶜ, m2 / χ / 2 * X ω ∂μ := by
      refine setIntegral_mono_on hi2.integrableOn (hi1.const_mul _).integrableOn hS.compl ?_
      intro ω hω
      have : X ω < m2 / χ / 2 := by simpa [S] using hω
      rw [sq]; exact mul_le_mul_of_nonneg_right this.le (hX0 ω)
    have hc2 : ∫ ω in Sᶜ, m2 / χ / 2 * X ω ∂μ ≤ m2 / 2 := by
      rw [integral_const_mul]
      have : ∫ ω in Sᶜ, X ω ∂μ ≤ χ := setIntegral_le_integral hi1 (Eventually.of_forall hX0)
      have hk : 0 ≤ m2 / χ / 2 := div_nonneg (div_nonneg hm2nn hχ.le) zero_le_two
      calc _ ≤ m2 / χ / 2 * χ := mul_le_mul_of_nonneg_left this hk
        _ = m2 / 2 := by field_simp
    have := integral_add_compl hS hi2
    linarith
  -- the first moment carried by `S`
  set t := 6 * χ ^ 2 / α with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have h2 : α ^ 2 * χ / 12 ≤ ∫ ω in S, X ω ∂μ := by
    have hle : ∫ ω in S, X ω ^ 2 ∂μ ≤ ∫ ω in S, (t * X ω + X ω ^ 3 / t) / 2 ∂μ :=
      setIntegral_mono_on hi2.integrableOn
        (((hi1.const_mul t).add (hi3.div_const t)).div_const 2).integrableOn hS
        (fun ω _ => sq_le_mul_add_cube_div (hX0 ω) ht)
    have heq : ∫ ω in S, (t * X ω + X ω ^ 3 / t) / 2 ∂μ =
        (t * ∫ ω in S, X ω ∂μ + (∫ ω in S, X ω ^ 3 ∂μ) / t) / 2 := by
      rw [integral_div, integral_add (hi1.const_mul t).integrableOn
        (hi3.div_const t).integrableOn, integral_const_mul, integral_div]
    rw [heq] at hle
    have h3S : ∫ ω in S, X ω ^ 3 ∂μ ≤ m3 :=
      setIntegral_le_integral hi3 (Eventually.of_forall fun ω => pow_nonneg (hX0 ω) 3)
    have hm3t : m3 / t ≤ α * χ ^ 3 / 2 := by
      rw [div_le_iff₀ ht]
      calc m3 ≤ 3 * χ ^ 5 := h3u
        _ = α * χ ^ 3 / 2 * t := by rw [htdef]; field_simp; ring
    have h3t : (∫ ω in S, X ω ^ 3 ∂μ) / t ≤ m3 / t := div_le_div_of_nonneg_right h3S ht.le
    have key : α * χ ^ 3 / 2 ≤ t * ∫ ω in S, X ω ∂μ := by linarith
    rw [← div_le_iff₀' ht] at key
    calc α ^ 2 * χ / 12 = α * χ ^ 3 / 2 / t := by rw [htdef]; field_simp; ring
      _ ≤ _ := key
  -- Markov bound for the upper tail
  have h3 : ∫ ω in H, X ω ∂μ ≤ α ^ 2 * χ / 24 := by
    calc ∫ ω in H, X ω ∂μ ≤ ∫ ω in H, X ω ^ 2 / (B * χ ^ 2) ∂μ := by
          refine setIntegral_mono_on hi1.integrableOn (hi2.div_const _).integrableOn hH ?_
          intro ω hω
          have : B * χ ^ 2 < X ω := hω
          rw [le_div_iff₀ hBχ, pow_two (X ω)]; exact mul_le_mul_of_nonneg_left this.le (hX0 ω)
      _ ≤ m2 / (B * χ ^ 2) := by
          rw [integral_div]
          exact div_le_div_of_nonneg_right
            (setIntegral_le_integral hi2 (Eventually.of_forall fun ω => sq_nonneg _)) hBχ.le
      _ ≤ χ ^ 3 / (B * χ ^ 2) := div_le_div_of_nonneg_right h2u hBχ.le
      _ = α ^ 2 * χ / 24 := by rw [hB]; field_simp
  -- the first moment carried by the band
  have h4 : α ^ 2 * χ / 24 ≤ ∫ ω in S \ H, X ω ∂μ := by
    have hsplit := integral_inter_add_sdiff hH (hi1.integrableOn (s := S))
    have hmono : ∫ ω in S ∩ H, X ω ∂μ ≤ ∫ ω in H, X ω ∂μ :=
      setIntegral_mono_set hi1.integrableOn (Eventually.of_forall hX0)
        (Eventually.of_forall fun ω hω => hω.2)
    linarith
  have h5 : ∫ ω in S \ H, X ω ∂μ ≤ B * χ ^ 2 * μ.real (S \ H) := by
    calc _ ≤ ∫ ω in S \ H, B * χ ^ 2 ∂μ :=
          setIntegral_mono_on hi1.integrableOn (integrable_const _).integrableOn (hS.diff hH)
            (fun ω hω => not_lt.1 hω.2)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hP : α ^ 2 * χ / 24 / (B * χ ^ 2) ≤ μ.real (S \ H) := by
    rw [div_le_iff₀ hBχ]; linarith
  calc α ^ 4 / (576 * χ) = α ^ 2 * χ / 24 / (B * χ ^ 2) := by rw [hB]; field_simp; ring
    _ ≤ _ := hP

/-- **Moment lower bound.** Under the hypotheses of `measureReal_band_ge_of_moments`, for every
real `r ≥ 0` with `X^r` integrable, `(α/2)^r α⁴/576 · χ^{2r-1} ≤ E X^r`. -/
theorem le_integral_rpow_of_moments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hi1 : Integrable X μ)
    (hi2 : Integrable (fun ω => X ω ^ 2) μ) (hi3 : Integrable (fun ω => X ω ^ 3) μ)
    {α : ℝ} (hα0 : 0 < α) (hχ : 0 < ∫ ω, X ω ∂μ)
    (h2l : α * (∫ ω, X ω ∂μ) ^ 3 ≤ ∫ ω, X ω ^ 2 ∂μ)
    (h2u : ∫ ω, X ω ^ 2 ∂μ ≤ (∫ ω, X ω ∂μ) ^ 3)
    (h3u : ∫ ω, X ω ^ 3 ∂μ ≤ 3 * (∫ ω, X ω ∂μ) ^ 5) {r : ℝ} (hr : 0 ≤ r)
    (hir : Integrable (fun ω => X ω ^ r) μ) :
    (α / 2) ^ r * α ^ 4 / 576 * (∫ ω, X ω ∂μ) ^ (2 * r - 1) ≤ ∫ ω, X ω ^ r ∂μ := by
  have hband := measureReal_band_ge_of_moments hXm hX0 hi1 hi2 hi3 hα0 hχ h2l h2u h3u
  set χ := ∫ ω, X ω ∂μ with hχdef
  set m2 := ∫ ω, X ω ^ 2 ∂μ with hm2
  set A := {ω | m2 / χ / 2 ≤ X ω ∧ X ω ≤ 24 / α ^ 2 * χ ^ 2} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const hXm).inter (measurableSet_le hXm measurable_const)
  have hlow : α * χ ^ 2 / 2 ≤ m2 / χ / 2 := by
    rw [div_le_div_iff_of_pos_right two_pos, le_div_iff₀ hχ]; nlinarith
  have hc0 : 0 ≤ α * χ ^ 2 / 2 := by positivity
  have hsub : (α * χ ^ 2 / 2) ^ r * μ.real A ≤ ∫ ω, X ω ^ r ∂μ := by
    calc (α * χ ^ 2 / 2) ^ r * μ.real A = ∫ ω in A, (α * χ ^ 2 / 2) ^ r ∂μ := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in A, X ω ^ r ∂μ :=
          setIntegral_mono_on (integrable_const _).integrableOn hir.integrableOn hA
            (fun ω hω => rpow_le_rpow hc0 (hlow.trans hω.1) hr)
      _ ≤ ∫ ω, X ω ^ r ∂μ :=
          setIntegral_le_integral hir (Eventually.of_forall fun ω => rpow_nonneg (hX0 ω) r)
  have hpow : (α * χ ^ 2 / 2) ^ r = (α / 2) ^ r * χ ^ (2 * r) := by
    rw [show α * χ ^ 2 / 2 = α / 2 * χ ^ 2 by ring, mul_rpow (by positivity) (by positivity),
      ← rpow_natCast_mul hχ.le]
    norm_num
  have hχr : χ ^ (2 * r - 1) = χ ^ (2 * r) / χ := rpow_sub_one hχ.ne' _
  calc (α / 2) ^ r * α ^ 4 / 576 * χ ^ (2 * r - 1)
      = (α * χ ^ 2 / 2) ^ r * (α ^ 4 / (576 * χ)) := by
        rw [hpow, hχr]; field_simp
    _ ≤ (α * χ ^ 2 / 2) ^ r * μ.real A :=
        mul_le_mul_of_nonneg_left hband (rpow_nonneg hc0 r)
    _ ≤ _ := hsub

/-- Pointwise split at `x = χ²`: `x^r ≤ χ^{2r-2} x + χ^{2r-2k} x^k` for `x ≥ 0`, `χ > 0` and
`1 ≤ r ≤ k`. -/
theorem rpow_le_mul_add_mul_pow {x χ r : ℝ} {k : ℕ} (hx : 0 ≤ x) (hχ : 0 < χ) (hr : 1 ≤ r)
    (hrk : r ≤ k) :
    x ^ r ≤ χ ^ (2 * r - 2) * x + χ ^ (2 * r - 2 * k) * x ^ k := by
  have hsq : ∀ s : ℝ, (χ ^ 2) ^ s = χ ^ (2 * s) := fun s => by
    rw [← rpow_natCast_mul hχ.le]; norm_num
  have h1 : 0 ≤ χ ^ (2 * r - 2) * x := mul_nonneg (rpow_nonneg hχ.le _) hx
  have h2 : 0 ≤ χ ^ (2 * r - 2 * k) * x ^ k := mul_nonneg (rpow_nonneg hχ.le _) (pow_nonneg hx k)
  rcases le_or_gt x (χ ^ 2) with hle | hgt
  · have e : x ^ r = x ^ (r - 1) * x := by
      rw [← rpow_add_one' hx (by linarith)]; ring_nf
    have : x ^ (r - 1) ≤ χ ^ (2 * r - 2) := by
      calc x ^ (r - 1) ≤ (χ ^ 2) ^ (r - 1) := rpow_le_rpow hx hle (by linarith)
        _ = χ ^ (2 * r - 2) := by rw [hsq]; ring_nf
    rw [e]; nlinarith
  · have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hgt.le
    have e : x ^ r = x ^ (r - k) * x ^ k := by
      rw [← rpow_natCast, ← rpow_add hx0]; ring_nf
    have : x ^ (r - k) ≤ χ ^ (2 * r - 2 * k) := by
      calc x ^ (r - k) ≤ (χ ^ 2) ^ (r - k) :=
            rpow_le_rpow_of_nonpos (by positivity) hgt.le (by linarith)
        _ = χ ^ (2 * r - 2 * k) := by rw [hsq]; ring_nf
    rw [e]; nlinarith [pow_nonneg hx k]

/-- **Moment upper bound.** If `X ≥ 0` has mean `χ > 0`, `X^k` is integrable and
`E X^k ≤ D χ^{2k-1}` for some `k ≥ 1`, then for `1 ≤ r ≤ k` the moment `E X^r` is finite and at
most `(1 + D) χ^{2r-1}`. -/
theorem integral_rpow_le_of_moment_le [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hi1 : Integrable X μ) {k : ℕ} (hk : 1 ≤ k)
    (hik : Integrable (fun ω => X ω ^ k) μ) {r : ℝ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (hχ : 0 < ∫ ω, X ω ∂μ) {D : ℝ}
    (hD : ∫ ω, X ω ^ k ∂μ ≤ D * (∫ ω, X ω ∂μ) ^ (2 * k - 1)) :
    Integrable (fun ω => X ω ^ r) μ ∧
      ∫ ω, X ω ^ r ∂μ ≤ (1 + D) * (∫ ω, X ω ∂μ) ^ (2 * r - 1) := by
  set χ := ∫ ω, X ω ∂μ with hχdef
  have hg : Integrable (fun ω => χ ^ (2 * r - 2) * X ω + χ ^ (2 * r - 2 * k) * X ω ^ k) μ :=
    (hi1.const_mul _).add (hik.const_mul _)
  have hpt : ∀ ω, X ω ^ r ≤ χ ^ (2 * r - 2) * X ω + χ ^ (2 * r - 2 * k) * X ω ^ k :=
    fun ω => rpow_le_mul_add_mul_pow (hX0 ω) hχ hr hrk
  have hir : Integrable (fun ω => X ω ^ r) μ := by
    refine hg.mono' (hXm.pow_const r).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (rpow_nonneg (hX0 ω) r)]; exact hpt ω
  refine ⟨hir, ?_⟩
  have hkχ : χ ^ (2 * k - 1) = χ ^ (2 * (k : ℝ) - 1) := by
    rw [← rpow_natCast]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; ring
  have hD0 := hD
  rw [hkχ] at hD0
  calc ∫ ω, X ω ^ r ∂μ ≤ ∫ ω, (χ ^ (2 * r - 2) * X ω + χ ^ (2 * r - 2 * k) * X ω ^ k) ∂μ :=
        integral_mono hir hg hpt
    _ = χ ^ (2 * r - 2) * χ + χ ^ (2 * r - 2 * k) * ∫ ω, X ω ^ k ∂μ := by
        rw [integral_add (hi1.const_mul _) (hik.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ χ ^ (2 * r - 2) * χ + χ ^ (2 * r - 2 * k) * (D * χ ^ (2 * (k : ℝ) - 1)) := by
        gcongr
    _ = (1 + D) * χ ^ (2 * r - 1) := by
        have e1 : χ ^ (2 * r - 2) * χ = χ ^ (2 * r - 1) := by
          rw [← rpow_add_one' hχ.le (ne_of_gt (by linarith))]; ring_nf
        have e2 : χ ^ (2 * r - 2 * k) * χ ^ (2 * (k : ℝ) - 1) = χ ^ (2 * r - 1) := by
          rw [← rpow_add hχ]; ring_nf
        rw [e1, show χ ^ (2 * r - 2 * k) * (D * χ ^ (2 * (k : ℝ) - 1)) =
          D * (χ ^ (2 * r - 2 * k) * χ ^ (2 * (k : ℝ) - 1)) by ring, e2]
        ring

/-- A moment bound in `ℝ≥0∞` for a natural-valued variable gives integrability and the real
bound. -/
theorem integrable_pow_and_integral_le_of_lintegral_le {T : Ω → ℕ} (hT : Measurable T) {k : ℕ}
    {b : ℝ} (hb : 0 ≤ b) (h : ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤ ENNReal.ofReal b) :
    Integrable (fun ω => (T ω : ℝ) ^ k) μ ∧ ∫ ω, (T ω : ℝ) ^ k ∂μ ≤ b := by
  have hmeas : AEMeasurable (fun ω => (T ω : ℝ≥0∞) ^ k) μ :=
    (((measurable_from_nat (f := ((↑) : ℕ → ℝ≥0∞))).comp hT).pow_const k).aemeasurable
  have hne : ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hfun : (fun ω => ((T ω : ℝ≥0∞) ^ k).toReal) = fun ω => (T ω : ℝ) ^ k := by
    funext ω; simp
  refine ⟨hfun ▸ integrable_toReal_of_lintegral_ne_top hmeas hne, ?_⟩
  rw [← hfun, integral_toReal hmeas (Eventually.of_forall fun ω => by simp)]
  exact ENNReal.toReal_le_of_le_ofReal hb h

section TreeGraph

variable [IsProbabilityMeasure μ] {T : Ω → ℕ}

omit [IsProbabilityMeasure μ] in
/-- The tree-graph hypotheses give the real moment bounds used above. -/
theorem integrable_pow_and_integral_le_of_tree_graph (hT : Measurable T)
    (hk : ∀ k : ℕ, 1 ≤ k → ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤
      ENNReal.ofReal ((2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1))) {k : ℕ} (hk1 : 1 ≤ k) :
    Integrable (fun ω => (T ω : ℝ) ^ k) μ ∧
      ∫ ω, (T ω : ℝ) ^ k ∂μ ≤ (2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1) := by
  have hχ0 : 0 ≤ ∫ ω, (T ω : ℝ) ∂μ := integral_nonneg fun ω => Nat.cast_nonneg _
  exact integrable_pow_and_integral_le_of_lintegral_le hT (by positivity) (hk k hk1)

/-- A variable with values at least one has mean at least one. -/
theorem one_le_integral_natCast (hT1 : ∀ ω, 1 ≤ T ω) (hint : Integrable (fun ω => (T ω : ℝ)) μ) :
    1 ≤ ∫ ω, (T ω : ℝ) ∂μ := by
  calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂μ := by simp
    _ ≤ _ := integral_mono (integrable_const _) hint fun ω => Nat.one_le_cast.2 (hT1 ω)

/-- **Band bound for cluster volumes.** Let `T ≥ 1` be integer-valued with mean `χ < ∞`,
`E T² ≥ α χ³` for some `α > 0`, and `E T^k ≤ (2k-3)!! χ^{2k-1}` for every `k ≥ 1`. With
`a = E T² / χ` and `B = 24/α²`, `P(a/2 ≤ T ≤ B χ²) ≥ α⁴ / (576 χ)`. -/
theorem measureReal_band_ge_of_tree_graph (hT : Measurable T) (hT1 : ∀ ω, 1 ≤ T ω)
    (hint : Integrable (fun ω => (T ω : ℝ)) μ) {α : ℝ} (hα0 : 0 < α)
    (h2 : α * (∫ ω, (T ω : ℝ) ∂μ) ^ 3 ≤ ∫ ω, (T ω : ℝ) ^ 2 ∂μ)
    (hk : ∀ k : ℕ, 1 ≤ k → ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤
      ENNReal.ofReal ((2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1))) :
    α ^ 4 / (576 * ∫ ω, (T ω : ℝ) ∂μ) ≤
      μ.real {ω | (∫ ω, (T ω : ℝ) ^ 2 ∂μ) / (∫ ω, (T ω : ℝ) ∂μ) / 2 ≤ T ω ∧
        (T ω : ℝ) ≤ 24 / α ^ 2 * (∫ ω, (T ω : ℝ) ∂μ) ^ 2} := by
  have hXm : Measurable fun ω => (T ω : ℝ) := (measurable_from_nat (f := ((↑) : ℕ → ℝ))).comp hT
  obtain ⟨hi2, h2u⟩ := integrable_pow_and_integral_le_of_tree_graph hT hk
    (k := 2) (by norm_num)
  obtain ⟨hi3, h3u⟩ := integrable_pow_and_integral_le_of_tree_graph hT hk
    (k := 3) (by norm_num)
  norm_num [Nat.doubleFactorial] at h2u h3u
  exact measureReal_band_ge_of_moments hXm (fun ω => Nat.cast_nonneg _) hint hi2 hi3 hα0
    (zero_lt_one.trans_le (one_le_integral_natCast hT1 hint)) h2 h2u h3u

/-- **Explicit moment bounds for cluster volumes.** Under the hypotheses of
`measureReal_band_ge_of_tree_graph`, for every real `r ≥ 1` the moment `E T^r` is finite and
`(α/2)^r α⁴/576 · χ^{2r-1} ≤ E T^r ≤ (1 + (2⌈r⌉ - 3)!!) χ^{2r-1}`. -/
theorem integral_rpow_bounds_of_tree_graph (hT : Measurable T) (hT1 : ∀ ω, 1 ≤ T ω)
    (hint : Integrable (fun ω => (T ω : ℝ)) μ) {α : ℝ} (hα0 : 0 < α)
    (h2 : α * (∫ ω, (T ω : ℝ) ∂μ) ^ 3 ≤ ∫ ω, (T ω : ℝ) ^ 2 ∂μ)
    (hk : ∀ k : ℕ, 1 ≤ k → ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤
      ENNReal.ofReal ((2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1))) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun ω => (T ω : ℝ) ^ r) μ ∧
      (α / 2) ^ r * α ^ 4 / 576 * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * r - 1) ≤
        ∫ ω, (T ω : ℝ) ^ r ∂μ ∧
      ∫ ω, (T ω : ℝ) ^ r ∂μ ≤
        (1 + ((2 * ⌈r⌉₊ - 3)‼ : ℝ)) * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * r - 1) := by
  have hXm : Measurable fun ω => (T ω : ℝ) := (measurable_from_nat (f := ((↑) : ℕ → ℝ))).comp hT
  have hχ := zero_lt_one.trans_le (one_le_integral_natCast hT1 hint)
  have hc1 : 1 ≤ ⌈r⌉₊ := Nat.ceil_pos.2 (by linarith)
  obtain ⟨hik, hkD⟩ := integrable_pow_and_integral_le_of_tree_graph hT hk hc1
  obtain ⟨hir, hup⟩ := integral_rpow_le_of_moment_le hXm (fun ω => Nat.cast_nonneg _) hint hc1
    hik hr (Nat.le_ceil r) hχ hkD
  obtain ⟨hi2, h2u⟩ := integrable_pow_and_integral_le_of_tree_graph hT hk
    (k := 2) (by norm_num)
  obtain ⟨hi3, h3u⟩ := integrable_pow_and_integral_le_of_tree_graph hT hk
    (k := 3) (by norm_num)
  norm_num [Nat.doubleFactorial] at h2u h3u
  exact ⟨hir, le_integral_rpow_of_moments hXm (fun ω => Nat.cast_nonneg _) hint hi2 hi3 hα0
    hχ h2 h2u h3u (by linarith) hir, hup⟩

/-- **Moment comparison.** For `α > 0` and real `r ≥ 1` there are constants `0 < c, C`
depending only on `α` and `r` such that every integer-valued `T ≥ 1` with mean `χ < ∞`,
`E T² ≥ α χ³` and `E T^k ≤ (2k-3)!! χ^{2k-1}` for all `k ≥ 1` satisfies
`c χ^{2r-1} ≤ E T^r ≤ C χ^{2r-1}` and `c χ² ≤ E T^{r+1} / E T^r ≤ C χ²`. -/
theorem exists_moment_comparison_of_tree_graph {α : ℝ} (hα0 : 0 < α) {r : ℝ}
    (hr : 1 ≤ r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (T : Ω → ℕ), Measurable T → (∀ ω, 1 ≤ T ω) →
      Integrable (fun ω => (T ω : ℝ)) μ →
      α * (∫ ω, (T ω : ℝ) ∂μ) ^ 3 ≤ ∫ ω, (T ω : ℝ) ^ 2 ∂μ →
      (∀ k : ℕ, 1 ≤ k → ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤
        ENNReal.ofReal ((2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1))) →
      c * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * r - 1) ≤ ∫ ω, (T ω : ℝ) ^ r ∂μ ∧
      ∫ ω, (T ω : ℝ) ^ r ∂μ ≤ C * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * r - 1) ∧
      c * (∫ ω, (T ω : ℝ) ∂μ) ^ 2 ≤ (∫ ω, (T ω : ℝ) ^ (r + 1) ∂μ) / ∫ ω, (T ω : ℝ) ^ r ∂μ ∧
      (∫ ω, (T ω : ℝ) ^ (r + 1) ∂μ) / ∫ ω, (T ω : ℝ) ^ r ∂μ ≤ C * (∫ ω, (T ω : ℝ) ∂μ) ^ 2 := by
  set c : ℝ → ℝ := fun s => (α / 2) ^ s * α ^ 4 / 576 with hcdef
  set C : ℝ → ℝ := fun s => 1 + ((2 * ⌈s⌉₊ - 3)‼ : ℝ) with hCdef
  have hc : ∀ s, 0 < c s := fun s => by simp only [hcdef]; positivity
  have hC : ∀ s, 0 < C s := fun s => by simp only [hCdef]; positivity
  refine ⟨min (c r) (c (r + 1) / C r), max (C r) (C (r + 1) / c r),
    lt_min (hc r) (div_pos (hc _) (hC r)), lt_max_of_lt_left (hC r), ?_⟩
  intro Ω _ μ _ T hT hT1 hint h2 hk
  obtain ⟨-, l0, u0⟩ := integral_rpow_bounds_of_tree_graph hT hT1 hint hα0 h2 hk hr
  obtain ⟨-, l1, u1⟩ := integral_rpow_bounds_of_tree_graph hT hT1 hint hα0 h2 hk
    (r := r + 1) (by linarith)
  set χ := ∫ ω, (T ω : ℝ) ∂μ with hχdef
  have hχ : 0 < χ := zero_lt_one.trans_le (one_le_integral_natCast hT1 hint)
  have hp0 : 0 < χ ^ (2 * r - 1) := rpow_pos_of_pos hχ _
  have hshift : χ ^ (2 * (r + 1) - 1) = χ ^ (2 * r - 1) * χ ^ 2 := by
    rw [← rpow_natCast, ← rpow_add hχ]; push_cast; ring_nf
  rw [hshift] at l1 u1
  change c r * χ ^ (2 * r - 1) ≤ _ at l0
  change _ ≤ C r * χ ^ (2 * r - 1) at u0
  change c (r + 1) * (χ ^ (2 * r - 1) * χ ^ 2) ≤ _ at l1
  change _ ≤ C (r + 1) * (χ ^ (2 * r - 1) * χ ^ 2) at u1
  have hm0 : 0 < ∫ ω, (T ω : ℝ) ^ r ∂μ := lt_of_lt_of_le (mul_pos (hc r) hp0) l0
  have hχ2 : 0 < χ ^ 2 := pow_pos hχ 2
  refine ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hp0.le) l0,
    u0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp0.le), ?_, ?_⟩
  · calc min (c r) (c (r + 1) / C r) * χ ^ 2 ≤ c (r + 1) / C r * χ ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hχ2.le
      _ = c (r + 1) * (χ ^ (2 * r - 1) * χ ^ 2) / (C r * χ ^ (2 * r - 1)) := by
          field_simp
      _ ≤ _ := div_le_div₀ (by positivity) l1 hm0 u0
  · calc (∫ ω, (T ω : ℝ) ^ (r + 1) ∂μ) / ∫ ω, (T ω : ℝ) ^ r ∂μ
        ≤ C (r + 1) * (χ ^ (2 * r - 1) * χ ^ 2) / (c r * χ ^ (2 * r - 1)) :=
          div_le_div₀ (by have := hC (r + 1); positivity) u1 (mul_pos (hc r) hp0) l0
      _ = C (r + 1) / c r * χ ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hχ2.le

end TreeGraph

end PercLib.Probability
