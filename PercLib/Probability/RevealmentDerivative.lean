/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Conversion of a weighted coordinate-covariance lower bound into a lower bound on the intensity
derivative of a finite product expectation, using the covariance form of the Russo formula and
the coefficient bound `J/(1 - e^{-βJ}) ≥ 1/β`. Mathematical reference: the finite-coordinate
covariance form of Russo's formula (proved in CovarianceRusso.lean). No new definition.
-/
module

public import PercLib.Probability.CovarianceRusso

/-!
# From a weighted covariance bound to an intensity derivative

Let `q_β(e) = 1 - e^{-βJₑ}` with `Jₑ ≥ 0` and `β > 0`, and let `f` be a monotone observable on
`E → Bool`. If `C ≤ ∑ₑ δₑ Cov_β(f, Xₑ)` and `δₑ ≤ R cₑ` for every `e` with `Jₑ > 0`, where
`cₑ = Jₑ/(1 - e^{-βJₑ})`, then `C ≤ R · d/dβ E_β[f]`. Zero-weight coordinates have zero
covariance, so they impose no condition on `δₑ`.

## Main results

* `IsUpperSet.monotone_indicator`
* `deriv_expectation_intensity_nonneg`
* `le_mul_deriv_expectation_of_le_sum_covariance`
* `div_iSup_le_deriv_expectation_of_le_sum_covariance`
* `eq_zero_of_iSup_eq_zero_of_le_sum_covariance`
* `div_mul_le_deriv_expectation_of_le_sum_covariance`
-/

@[expose] public section
noncomputable section

/-- The indicator of an upper set with a monotone nonnegative value function is monotone. -/
theorem IsUpperSet.monotone_indicator {α M : Type*} [Preorder α] [Zero M] [Preorder M]
    {s : Set α} (hs : IsUpperSet s) {f : α → M} (hf : Monotone f) (h0 : 0 ≤ f) :
    Monotone (s.indicator f) := by
  intro x y hxy
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hs hxy hx)]
    exact hf hxy
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun a _ => h0 a) y

namespace PercLib.Probability.FiniteProfile
open Finset
variable {E : Type*} [Fintype E]

omit [Fintype E] in
/-- The intensity profile `1 - e^{-βJₑ}` lies in `[0,1]` for `β ≥ 0` and `Jₑ ≥ 0`. -/
lemma one_sub_exp_neg_mul_mem_Icc {J : E → ℝ} (hJ : ∀ e, 0 ≤ J e) {β : ℝ} (hβ : 0 ≤ β)
    (e : E) : 1 - Real.exp (-β * J e) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hβ (hJ e)])),
    sub_le_self _ (Real.exp_pos _).le⟩

/-- For a monotone observable the intensity derivative of `E_β[f]` is nonnegative. -/
theorem deriv_expectation_intensity_nonneg (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e) {β : ℝ}
    (hβ : 0 < β) {f : (E → Bool) → ℝ} (hf : Monotone f) :
    0 ≤ deriv (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f) β := by
  rw [(expectation_intensity_hasDerivAt_covariance J hJ hβ f).deriv]
  refine sum_nonneg fun e he => mul_nonneg ?_ ?_
  · have hJe : 0 < J e := (mem_filter.mp he).2
    exact (lt_of_lt_of_le (one_div_pos.mpr hβ) (intensity_coefficient_bounds hJe hβ).1).le
  · exact covariance_coordinate_nonneg (one_sub_exp_neg_mul_mem_Icc hJ hβ.le) e hf

/-- Weighted covariance bound to derivative bound. If `C ≤ ∑ₑ δₑ Cov_β(f, Xₑ)` for a monotone
`f` and `δₑ ≤ R Jₑ/(1 - e^{-βJₑ})` whenever `Jₑ > 0`, then `C ≤ R · d/dβ E_β[f]`. No condition
is needed on zero-weight coordinates: their covariance vanishes. -/
theorem le_mul_deriv_expectation_of_le_sum_covariance (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    {β : ℝ} (hβ : 0 < β) {f : (E → Bool) → ℝ} (hf : Monotone f) {δ : E → ℝ} {C R : ℝ}
    (hR : ∀ e, 0 < J e → δ e ≤ R * (J e / (1 - Real.exp (-β * J e))))
    (hC : C ≤ ∑ e, δ e * (expectation (fun j => 1 - Real.exp (-β * J j))
        (fun ω => f ω * if ω e then 1 else 0) -
      expectation (fun j => 1 - Real.exp (-β * J j)) f *
        expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0))) :
    C ≤ R * deriv (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f) β := by
  rw [(expectation_intensity_hasDerivAt_covariance J hJ hβ f).deriv, mul_sum, sum_filter]
  refine hC.trans (sum_le_sum fun e _ => ?_)
  split_ifs with he
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hR e he)
      (covariance_coordinate_nonneg (one_sub_exp_neg_mul_mem_Icc hJ hβ.le) e hf)
  · have h0 : J e = 0 := le_antisymm (not_lt.mp he) (hJ e)
    rw [covariance_coordinate]
    simp [h0]

/-- The ratio `δₑ / cₑ` is at most its supremum over the positive-weight coordinates. -/
lemma le_iSup_mul_intensity_coefficient (J : E → ℝ) {β : ℝ} (hβ : 0 < β) (δ : E → ℝ) {e : E}
    (he : 0 < J e) :
    δ e ≤ (⨆ i : {i // 0 < J i}, δ i / (J i / (1 - Real.exp (-β * J i)))) *
      (J e / (1 - Real.exp (-β * J e))) := by
  have hc : 0 < J e / (1 - Real.exp (-β * J e)) :=
    lt_of_lt_of_le (one_div_pos.mpr hβ) (intensity_coefficient_bounds he hβ).1
  rw [← div_le_iff₀ hc]
  exact le_ciSup (f := fun i : {i // 0 < J i} => δ i / (J i / (1 - Real.exp (-β * J i))))
    (Set.finite_range _).bddAbove ⟨e, he⟩

/-- With `R = sup_{Jₑ > 0} δₑ / cₑ` and `R > 0`, the covariance bound gives
`C / R ≤ d/dβ E_β[f]`. -/
theorem div_iSup_le_deriv_expectation_of_le_sum_covariance (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    {β : ℝ} (hβ : 0 < β) {f : (E → Bool) → ℝ} (hf : Monotone f) {δ : E → ℝ} {C : ℝ}
    (hC : C ≤ ∑ e, δ e * (expectation (fun j => 1 - Real.exp (-β * J j))
        (fun ω => f ω * if ω e then 1 else 0) -
      expectation (fun j => 1 - Real.exp (-β * J j)) f *
        expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0)))
    (hR : 0 < ⨆ e : {e // 0 < J e}, δ e / (J e / (1 - Real.exp (-β * J e)))) :
    C / (⨆ e : {e // 0 < J e}, δ e / (J e / (1 - Real.exp (-β * J e)))) ≤
      deriv (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f) β := by
  rw [div_le_iff₀' hR]
  exact le_mul_deriv_expectation_of_le_sum_covariance J hJ hβ hf
    (fun e he => le_iSup_mul_intensity_coefficient J hβ δ he) hC

/-- With `R = sup_{Jₑ > 0} δₑ / cₑ` and `R = 0` (in particular when no weight is positive), a
covariance bound `0 ≤ C ≤ ∑ₑ δₑ Cov_β(f, Xₑ)` forces `C = 0`. -/
theorem eq_zero_of_iSup_eq_zero_of_le_sum_covariance (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    {β : ℝ} (hβ : 0 < β) {f : (E → Bool) → ℝ} (hf : Monotone f) {δ : E → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : C ≤ ∑ e, δ e * (expectation (fun j => 1 - Real.exp (-β * J j))
        (fun ω => f ω * if ω e then 1 else 0) -
      expectation (fun j => 1 - Real.exp (-β * J j)) f *
        expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0)))
    (hR : (⨆ e : {e // 0 < J e}, δ e / (J e / (1 - Real.exp (-β * J e)))) = 0) :
    C = 0 := by
  have h := le_mul_deriv_expectation_of_le_sum_covariance J hJ hβ hf
    (fun e he => le_iSup_mul_intensity_coefficient J hβ δ he) hC
  rw [hR, zero_mul] at h
  exact le_antisymm h hC0

/-- A uniform bound `δₑ ≤ D` on the positive-weight coordinates, with `D > 0`, turns the
covariance bound into `C / (βD) ≤ d/dβ E_β[f]`, via `cₑ ≥ 1/β`. -/
theorem div_mul_le_deriv_expectation_of_le_sum_covariance (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    {β : ℝ} (hβ : 0 < β) {f : (E → Bool) → ℝ} (hf : Monotone f) {δ : E → ℝ} {C D : ℝ}
    (hD : 0 < D) (hδD : ∀ e, 0 < J e → δ e ≤ D)
    (hC : C ≤ ∑ e, δ e * (expectation (fun j => 1 - Real.exp (-β * J j))
        (fun ω => f ω * if ω e then 1 else 0) -
      expectation (fun j => 1 - Real.exp (-β * J j)) f *
        expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0))) :
    C / (β * D) ≤ deriv (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f) β := by
  rw [div_le_iff₀' (mul_pos hβ hD)]
  refine le_mul_deriv_expectation_of_le_sum_covariance J hJ hβ hf (fun e he => ?_) hC
  have h1 := (intensity_coefficient_bounds he hβ).1
  calc δ e ≤ D := hδD e he
    _ = β * D * (1 / β) := by field_simp
    _ ≤ β * D * (J e / (1 - Real.exp (-β * J e))) :=
      mul_le_mul_of_nonneg_left h1 (mul_pos hβ hD).le

/-! ### Non-vacuity witness -/

/-- One coordinate of weight `1`, `f = X`, `δ = 1` and `C = 0`: the derivative bound reads
`0 ≤ d/dβ E_β[X]` at `β = 1`. -/
example : (0 : ℝ) / (1 * 1) ≤
    deriv (fun b => expectation (fun _ : Unit => 1 - Real.exp (-b * 1))
      (fun ω => if ω () then 1 else 0)) 1 := by
  refine div_mul_le_deriv_expectation_of_le_sum_covariance (fun _ => 1) (fun _ => zero_le_one)
    one_pos (fun a b hab => ?_) (δ := fun _ => 1) one_pos (fun _ _ => le_rfl) ?_
  · have := hab ()
    generalize a () = x at *
    generalize b () = y at *
    cases x <;> cases y <;> first | exact absurd this (by decide) | norm_num
  · simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
    exact covariance_coordinate_nonneg (one_sub_exp_neg_mul_mem_Icc (fun _ => zero_le_one)
      zero_le_one) () (fun a b hab => by
        have := hab ()
        generalize a () = x at *
        generalize b () = y at *
        cases x <;> cases y <;> first | exact absurd this (by decide) | norm_num)

end PercLib.Probability.FiniteProfile
