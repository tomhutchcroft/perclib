/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Fourier contractions for the joining diagram;
no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.ShiftedSeries

/-!
# Absolutely summable series in the joining diagram

## Main results

Finite products of absolutely summable series expand as a single summable
family. This provides the integrable expansion for the joining diagram's
three-frequency Fourier contraction.
-/

@[expose] public section
noncomputable section

open MeasureTheory UnitAddTorus

namespace PercLib.Analysis

/-- A finite product of independently indexed absolutely summable kernels
is absolutely summable over the tuple of indices. -/
theorem summable_norm_fin_prod {A R : Type*} [NormedCommRing R]
    (n : ℕ) (f : Fin n → A → R) (hf : ∀ i, Summable fun x => ‖f i x‖) :
    Summable (fun b : Fin n → A => ‖∏ i, f i (b i)‖) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    apply (Fin.consEquiv (fun _ : Fin (n + 1) => A)).summable_iff.mp
    have h := (hf 0).mul_norm (ih (fun i => f i.succ) (fun i => hf i.succ))
    apply h.congr
    intro p
    simp only [Function.comp_apply, Fin.prod_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ]

/-- The product of finitely many absolutely summable series is their
independently indexed product series. -/
theorem prod_tsum_eq_tsum_fin_prod {A R : Type*} [NormedCommRing R] [CompleteSpace R]
    (n : ℕ) (f : Fin n → A → R) (hf : ∀ i, Summable fun x => ‖f i x‖) :
    (∏ i, ∑' x, f i x) = ∑' b : Fin n → A, ∏ i, f i (b i) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, ih (fun i => f i.succ) (fun i => hf i.succ),
      tsum_mul_tsum_of_summable_norm (hf 0)
        (summable_norm_fin_prod n (fun i => f i.succ) (fun i => hf i.succ))]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).tsum_eq]
    apply tsum_congr
    intro p
    simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

open scoped Classical in
/-- Integration of an absolutely summable three-frequency character series
imposes its three zero-frequency constraints, in their actual order. -/
theorem integral_tsum_three_mFourier {ι A : Type*} [Fintype ι] [Countable A]
    (w : A → ℂ) (a b c : A → ι → ℤ) (hw : Summable fun i => ‖w i‖) :
    (∫ t₁ : UnitAddTorus ι, ∫ t₂ : UnitAddTorus ι, ∫ t₃ : UnitAddTorus ι,
      ∑' i, w i * mFourier (a i) t₁ * mFourier (b i) t₂ * mFourier (c i) t₃
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      ∑' i, if a i = 0 then (if b i = 0 then (if c i = 0 then w i else 0) else 0) else 0 := by
  classical
  let v : A → ℂ := fun i => if c i = 0 then w i else 0
  let u : A → ℂ := fun i => if b i = 0 then v i else 0
  have hv : Summable fun i => ‖v i‖ := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ hw
    intro i
    dsimp only [v]
    split_ifs <;> simp
  have hu : Summable fun i => ‖u i‖ := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ hv
    intro i
    dsimp only [u]
    split_ifs <;> simp
  have hthird (t₁ t₂ : UnitAddTorus ι) :
      (∫ t₃ : UnitAddTorus ι,
        ∑' i, w i * mFourier (a i) t₁ * mFourier (b i) t₂ * mFourier (c i) t₃
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      ∑' i, v i * mFourier (a i) t₁ * mFourier (b i) t₂ := by
    have hn : Summable fun i => ‖w i * mFourier (a i) t₁ * mFourier (b i) t₂‖ := by
      simpa only [norm_mul, norm_mFourier_apply, mul_one] using hw
    rw [integral_tsum_mul_mFourier _ _ hn]
    apply tsum_congr
    intro i
    dsimp only [v]
    split_ifs <;> simp
  have hsecond (t₁ : UnitAddTorus ι) :
      (∫ t₂ : UnitAddTorus ι, ∑' i, v i * mFourier (a i) t₁ * mFourier (b i) t₂
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      ∑' i, u i * mFourier (a i) t₁ := by
    have hn : Summable fun i => ‖v i * mFourier (a i) t₁‖ := by
      simpa only [norm_mul, norm_mFourier_apply, mul_one] using hv
    rw [integral_tsum_mul_mFourier _ _ hn]
    apply tsum_congr
    intro i
    dsimp only [u]
    split_ifs <;> simp
  simp_rw [hthird, hsecond]
  simpa only [u, v] using integral_tsum_mul_mFourier u a hu

end PercLib.Analysis
