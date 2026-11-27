/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original seven-edge Fourier contraction; no upstream Lean code is copied.
Mathematical reference: Heydenreich and van der Hofstad (2017), Section 8.3.
-/
module

public import PercLib.Analysis.LatticeFourier.JoiningSeries
public import PercLib.Analysis.LatticeFourier.Characters
public import PercLib.Analysis.LatticeFourier.Theta
public import PercLib.Analysis.LatticeFourier.TorusIntegration

/-!
# The seven-edge joining contraction

## Main results

The absolutely summable spatial joining diagram is exactly a three-frequency
Haar integral, with both endpoint phases and all normalization factors retained.
-/

@[expose] public section
noncomputable section

open MeasureTheory UnitAddTorus

namespace PercLib.Analysis

variable {ι : Type*} [Fintype ι]

/-- Negating a torus argument negates a Fourier monomial's frequency. -/
theorem mFourier_apply_neg (n : ι → ℤ) (t : UnitAddTorus ι) :
    mFourier n (-t) = mFourier (-n) t := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    smul_neg, neg_smul]

/-- Subtraction of torus arguments splits a Fourier monomial into two factors. -/
theorem mFourier_apply_sub (n : ι → ℤ) (s t : UnitAddTorus ι) :
    mFourier n (s - t) = mFourier n s * mFourier (-n) t := by
  rw [sub_eq_add_neg, mFourier_apply_add, mFourier_apply_neg]

/-- The seven-edge joining series is absolutely summable and is exactly its
three-frequency Fourier contraction. The two endpoint phases have unit modulus;
the evenness hypotheses are precisely those used to reverse spatial edges. -/
theorem joining_series_summable_and_integral_eq
    (f g h m : (ι → ℤ) → ℂ)
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖)
    (hh : Summable fun x => ‖h x‖) (hm : Summable fun x => ‖m x‖)
    (hfeven : Function.Even f) (hmeven : Function.Even m) (a b : ι → ℤ) :
    let F := fun t : UnitAddTorus ι => ∑' x, f x * mFourier x t
    let G := fun t : UnitAddTorus ι => ∑' x, g x * mFourier x t
    let H := fun t : UnitAddTorus ι => ∑' x, h x * mFourier x t
    let M := fun t : UnitAddTorus ι => ∑' x, m x * mFourier x t
    let S := fun p : (ι → ℤ) × (ι → ℤ) × (ι → ℤ) × (ι → ℤ) =>
      f p.1 * g (p.2.1 - a) * f (p.2.2.2 - p.2.1) * f (p.1 - p.2.2.2) *
        f (p.2.2.1 - p.2.2.2) * m (p.2.2.1 - p.1) * h (p.2.2.1 - p.2.1 - b)
    Summable (fun p => ‖S p‖) ∧
      (∫ t₁ : UnitAddTorus ι, ∫ t₂ : UnitAddTorus ι, ∫ t₃ : UnitAddTorus ι,
        mFourier a t₁ * mFourier b t₂ * G t₁ * F t₁ * H t₂ * M t₃ *
          F (t₁ - t₂) * F (t₂ - t₃) * F (t₁ - t₃)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = ∑' p, S p := by
  classical
  dsimp only
  let K : Fin 7 → (ι → ℤ) → ℂ := ![g, f, h, m, f, f, f]
  let W : (Fin 7 → ι → ℤ) → ℂ := fun z => ∏ i, K i (z i)
  let A : (Fin 7 → ι → ℤ) → ι → ℤ := fun z => a + z 0 + z 1 + z 4 + z 6
  let B : (Fin 7 → ι → ℤ) → ι → ℤ := fun z => b + z 2 - z 4 + z 5
  let C : (Fin 7 → ι → ℤ) → ι → ℤ := fun z => z 3 - z 5 - z 6
  let S := fun p : (ι → ℤ) × (ι → ℤ) × (ι → ℤ) × (ι → ℤ) =>
    f p.1 * g (p.2.1 - a) * f (p.2.2.2 - p.2.1) * f (p.1 - p.2.2.2) *
      f (p.2.2.1 - p.2.2.2) * m (p.2.2.1 - p.1) * h (p.2.2.1 - p.2.1 - b)
  let e : ((ι → ℤ) × (ι → ℤ) × (ι → ℤ) × (ι → ℤ)) → Fin 7 → ι → ℤ :=
    fun p => ![p.2.1 - a, -p.1, p.2.2.1 - p.2.1 - b, p.1 - p.2.2.1,
      p.2.2.2 - p.2.1, p.2.2.2 - p.2.2.1, p.1 - p.2.2.2]
  have hK (i : Fin 7) : Summable fun x => ‖K i x‖ := by
    fin_cases i
    · exact hg
    · exact hf
    · exact hh
    · exact hm
    · exact hf
    · exact hf
    · exact hf
  have hW : Summable fun z => ‖W z‖ := summable_norm_fin_prod 7 K hK
  have hWeval (z : Fin 7 → ι → ℤ) :
      W z = g (z 0) * f (z 1) * h (z 2) * m (z 3) * f (z 4) * f (z 5) * f (z 6) := by
    norm_num [W, K, Fin.prod_univ_succ]
    ring
  have hinj : Function.Injective e := by
    intro p q he
    have hu : p.1 = q.1 := by simpa [e] using congrFun he 1
    have hs : p.2.1 = q.2.1 := by simpa [e] using congrFun he 0
    have hz : p.2.2.2 = q.2.2.2 := by simpa [e, hs] using congrFun he 4
    have ht : p.2.2.1 = q.2.2.1 := by simpa [e, hz] using congrFun he 5
    exact Prod.ext hu (Prod.ext hs (Prod.ext ht hz))
  have heval (p : (ι → ℤ) × (ι → ℤ) × (ι → ℤ) × (ι → ℤ)) :
      W (e p) = S p := by
    rw [hWeval]
    simp only [e, S, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    change g (p.2.1 - a) * f (-p.1) * h (p.2.2.1 - p.2.1 - b) *
      m (p.1 - p.2.2.1) * f (p.2.2.2 - p.2.1) * f (p.2.2.2 - p.2.2.1) *
      f (p.1 - p.2.2.2) = _
    rw [hfeven p.1, show p.1 - p.2.2.1 = -(p.2.2.1 - p.1) by abel,
      hmeven, show p.2.2.2 - p.2.2.1 = -(p.2.2.1 - p.2.2.2) by abel, hfeven]
    ring
  refine ⟨?_, ?_⟩
  · apply (hW.comp_injective hinj).congr
    intro p
    change ‖W (e p)‖ = _
    rw [heval]
  · have hpoint (t₁ t₂ t₃ : UnitAddTorus ι) :
        mFourier a t₁ * mFourier b t₂ *
          (∑' x, g x * mFourier x t₁) * (∑' x, f x * mFourier x t₁) *
          (∑' x, h x * mFourier x t₂) * (∑' x, m x * mFourier x t₃) *
          (∑' x, f x * mFourier x (t₁ - t₂)) *
          (∑' x, f x * mFourier x (t₂ - t₃)) *
          (∑' x, f x * mFourier x (t₁ - t₃)) =
          ∑' z, W z * mFourier (A z) t₁ *
            mFourier (B z) t₂ * mFourier (C z) t₃ := by
      let T : Fin 7 → UnitAddTorus ι :=
        ![t₁, t₁, t₂, t₃, t₁ - t₂, t₂ - t₃, t₁ - t₃]
      have hKT (i : Fin 7) : Summable fun x => ‖K i x * mFourier x (T i)‖ := by
        simpa only [norm_mul, norm_mFourier_apply, mul_one] using hK i
      calc
        _ = (mFourier a t₁ * mFourier b t₂) *
            ∏ i : Fin 7, ∑' x, K i x * mFourier x (T i) := by
          simp only [K, T, Fin.prod_univ_succ, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
          ring
        _ = (mFourier a t₁ * mFourier b t₂) *
            ∑' z : Fin 7 → ι → ℤ, ∏ i, K i (z i) * mFourier (z i) (T i) := by
          rw [prod_tsum_eq_tsum_fin_prod 7 _ hKT]
        _ = ∑' z : Fin 7 → ι → ℤ, (mFourier a t₁ * mFourier b t₂) *
            ∏ i, K i (z i) * mFourier (z i) (T i) := tsum_mul_left.symm
        _ = _ := by
          apply tsum_congr
          intro z
          rw [hWeval]
          norm_num [K, T, Fin.prod_univ_succ, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, A, B, C,
            sub_eq_add_neg, mFourier_add, mFourier_apply_add, mFourier_apply_neg]
          ring
    simp_rw [hpoint]
    rw [integral_tsum_three_mFourier W A B C hW]
    let V := fun z => if A z = 0 then (if B z = 0 then (if C z = 0 then W z else 0)
      else 0) else 0
    have hsupport : Function.support V ⊆ Set.range e := by
      intro z hz
      have hA : A z = 0 := by
        by_contra ha
        exact hz (by simp [V, ha])
      have hB : B z = 0 := by
        by_contra hb
        exact hz (by simp [V, hA, hb])
      have hC : C z = 0 := by
        by_contra hc
        exact hz (by simp [V, hA, hB, hc])
      refine ⟨(a + z 0 + z 4 + z 6, a + z 0,
        a + z 0 + z 4 - z 5, a + z 0 + z 4), ?_⟩
      funext i
      fin_cases i
      · change (a + z 0) - a = z 0
        abel
      · change -(a + z 0 + z 4 + z 6) = z 1
        apply sub_eq_zero.mp
        calc
          _ = -A z := by dsimp [A]; abel
          _ = 0 := by rw [hA, neg_zero]
      · change (a + z 0 + z 4 - z 5) - (a + z 0) - b = z 2
        apply sub_eq_zero.mp
        calc
          _ = -B z := by dsimp [B]; abel
          _ = 0 := by rw [hB, neg_zero]
      · change (a + z 0 + z 4 + z 6) - (a + z 0 + z 4 - z 5) = z 3
        apply sub_eq_zero.mp
        calc
          _ = -C z := by dsimp [C]; abel
          _ = 0 := by rw [hC, neg_zero]
      · change (a + z 0 + z 4) - (a + z 0) = z 4
        abel
      · change (a + z 0 + z 4) - (a + z 0 + z 4 - z 5) = z 5
        abel
      · change (a + z 0 + z 4 + z 6) - (a + z 0 + z 4) = z 6
        abel
    change (∑' z, V z) = ∑' p, S p
    rw [← hinj.tsum_eq hsupport]
    apply tsum_congr
    intro p
    have hA : A (e p) = 0 := by dsimp [A, e]; abel
    have hB : B (e p) = 0 := by dsimp [B, e]; abel
    have hC : C (e p) = 0 := by dsimp [C, e]; abel
    simp only [V, hA, hB, hC, ite_eq_left, heval]


open Metric Real in
/-- Absolute values remove the endpoint phases in the joining contraction.
The three physical-frequency integrals carry the full normalization `(2*pi)^(-3d)`. -/
theorem norm_joining_integral_le_normalized_abs_cosine_transforms {d : ℕ}
    (f g h m : (Fin d → ℤ) → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (hm : Summable m)
    (hef : Function.Even f) (heg : Function.Even g)
    (heh : Function.Even h) (hem : Function.Even m) (a b : Fin d → ℤ) :
    let FT := fun (v : (Fin d → ℤ) → ℝ) (t : UnitAddTorus (Fin d)) =>
      ∑' x, (v x : ℂ) * mFourier x t
    ‖∫ l₁ : UnitAddTorus (Fin d), ∫ l₂ : UnitAddTorus (Fin d),
      ∫ l₃ : UnitAddTorus (Fin d),
        mFourier a l₁ * mFourier b l₂ * FT g l₁ * FT f l₁ * FT h l₂ * FT m l₃ *
          FT f (l₁ - l₂) * FT f (l₂ - l₃) * FT f (l₁ - l₃)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ ≤
      (((2 * π) ^ d)⁻¹) ^ 3 *
        (∫ l₁ in ball (0 : Fin d → ℝ) π, ∫ l₂ in ball (0 : Fin d → ℝ) π,
          ∫ l₃ in ball (0 : Fin d → ℝ) π,
            |latticeCosineTransform g l₁| * |latticeCosineTransform f l₁| *
              |latticeCosineTransform h l₂| * |latticeCosineTransform m l₃| *
              |latticeCosineTransform f (l₁ - l₂)| *
              |latticeCosineTransform f (l₂ - l₃)| *
              |latticeCosineTransform f (l₁ - l₃)|) := by
  let μ : Measure (UnitAddTorus (Fin d)) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  let : OpensMeasurableSpace (UnitAddTorus (Fin d) × UnitAddTorus (Fin d)) :=
    Prod.opensMeasurableSpace
  let : OpensMeasurableSpace
      (UnitAddTorus (Fin d) × UnitAddTorus (Fin d) × UnitAddTorus (Fin d)) :=
    Prod.opensMeasurableSpace
  let FT := fun (v : (Fin d → ℤ) → ℝ) (t : UnitAddTorus (Fin d)) =>
    ∑' x, (v x : ℂ) * mFourier x t
  have hcont {v : (Fin d → ℤ) → ℝ} (hv : Summable v) : Continuous (FT v) :=
    continuous_tsum_mul_mFourier _ (by simpa only [Complex.norm_real] using hv.norm)
  let I := fun l : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) × UnitAddTorus (Fin d) =>
    mFourier a l.1 * mFourier b l.2.1 * FT g l.1 * FT f l.1 * FT h l.2.1 * FT m l.2.2 *
      FT f (l.1 - l.2.1) * FT f (l.2.1 - l.2.2) * FT f (l.1 - l.2.2)
  have hcF : Continuous (FT f) := hcont hf
  have hcG : Continuous (FT g) := hcont hg
  have hcH : Continuous (FT h) := hcont hh
  have hcM : Continuous (FT m) := hcont hm
  have hI : Continuous I := by dsimp only [I]; fun_prop
  have hIi : Integrable I (μ.prod (μ.prod μ)) :=
    hI.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsection (l₁ : UnitAddTorus (Fin d)) :
      Integrable (fun l : UnitAddTorus (Fin d) × UnitAddTorus (Fin d) => I (l₁, l))
        (μ.prod μ) :=
    (hI.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm := norm_integral_le_integral_norm (μ := μ.prod (μ.prod μ)) I
  rw [integral_prod _ hIi, integral_prod _ hIi.norm] at hnorm
  simp_rw [integral_prod _ (hsection _), integral_prod _ (hsection _).norm] at hnorm
  have hn (l₁ l₂ l₃ : UnitAddTorus (Fin d)) :
      ‖I (l₁, l₂, l₃)‖ = ‖FT g l₁‖ * ‖FT f l₁‖ * ‖FT h l₂‖ * ‖FT m l₃‖ *
        ‖FT f (l₁ - l₂)‖ * ‖FT f (l₂ - l₃)‖ * ‖FT f (l₁ - l₃)‖ := by
    simp only [I, norm_mul, norm_mFourier_apply, one_mul, mul_one]
  simp_rw [hn] at hnorm
  let q : (Fin d → ℝ) → UnitAddTorus (Fin d) :=
    fun k i => ((k i / (2 * π) : ℝ) : UnitAddCircle)
  have hqsub (k l : Fin d → ℝ) : q k - q l = q (k - l) := by
    funext i
    simp only [q, Pi.sub_apply, sub_div, AddCircle.coe_sub]
  have hrep {v : (Fin d → ℤ) → ℝ} (hv : Summable v) (hev : Function.Even v)
      (k : Fin d → ℝ) : ‖FT v (q k)‖ = |latticeCosineTransform v k| := by
    rw [show FT v (q k) = (latticeCosineTransform v k : ℂ) from
      tsum_mul_mFourier_div_two_pi_eq_cosineTransform hv hev k,
      Complex.norm_real, Real.norm_eq_abs]
  have hphysical :
      (∫ l₁, ∫ l₂, ∫ l₃,
        ‖FT g l₁‖ * ‖FT f l₁‖ * ‖FT h l₂‖ * ‖FT m l₃‖ *
          ‖FT f (l₁ - l₂)‖ * ‖FT f (l₂ - l₃)‖ * ‖FT f (l₁ - l₃)‖ ∂μ ∂μ ∂μ) =
      (((2 * π) ^ d)⁻¹) ^ 3 *
        (∫ l₁ in ball (0 : Fin d → ℝ) π, ∫ l₂ in ball (0 : Fin d → ℝ) π,
          ∫ l₃ in ball (0 : Fin d → ℝ) π,
            |latticeCosineTransform g l₁| * |latticeCosineTransform f l₁| *
              |latticeCosineTransform h l₂| * |latticeCosineTransform m l₃| *
              |latticeCosineTransform f (l₁ - l₂)| *
              |latticeCosineTransform f (l₂ - l₃)| *
              |latticeCosineTransform f (l₁ - l₃)|) := by
    dsimp only [μ]
    simp_rw [integral_unitTorus_eq_normalized_box, smul_eq_mul]
    change (((2 * π) ^ d)⁻¹ * ∫ l₁ in ball (0 : Fin d → ℝ) π,
      ((2 * π) ^ d)⁻¹ * ∫ l₂ in ball (0 : Fin d → ℝ) π,
      ((2 * π) ^ d)⁻¹ * ∫ l₃ in ball (0 : Fin d → ℝ) π,
        ‖FT g (q l₁)‖ * ‖FT f (q l₁)‖ * ‖FT h (q l₂)‖ * ‖FT m (q l₃)‖ *
          ‖FT f (q l₁ - q l₂)‖ * ‖FT f (q l₂ - q l₃)‖ * ‖FT f (q l₁ - q l₃)‖) = _
    simp_rw [hqsub, hrep hf hef, hrep hg heg, hrep hh heh, hrep hm hem,
      integral_const_mul (((2 * π) ^ d)⁻¹)]
    ring
  rw [hphysical] at hnorm
  exact hnorm

end PercLib.Analysis
