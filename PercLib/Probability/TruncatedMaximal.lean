/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied.
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Data.Int.Log
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Doob's `L²` maximal inequality

For a real martingale `X` with every `X k` in `L²`,

  `E[(max_{k ≤ n} |X_k|)²] ≤ 4 E[X_n²]`   (`lintegral_sup_abs_sq_le`).

Mathlib at the pin has the weak-type inequality `MeasureTheory.maximal_ineq` and notes that
the `Lᵖ` form is still to come. The proof applies `maximal_ineq` to the nonnegative
submartingale `|X|`, integrates it against `2t dt` (layer cake), exchanges the integrals, and
closes with `2ab ≤ 2a² + b²/2`.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}

/-- The absolute value of a real martingale is a submartingale. -/
theorem submartingale_abs_of_martingale (hX : Martingale X ℱ μ) :
    Submartingale (fun n ω => |X n ω|) ℱ μ := by
  have h := hX.submartingale.sup hX.neg.submartingale
  have e : (fun n ω => |X n ω|) = X ⊔ -X := by
    funext n ω
    rfl
  rw [e]
  exact h

/-- **Doob's `L²` maximal inequality.** For a real martingale `X` with each `X k ∈ L²` and a
finite measure, `∫⁻ (max_{k ≤ n} |X_k|)² ≤ 4 ∫⁻ X_n²`. -/
theorem lintegral_sup_abs_sq_le [IsFiniteMeasure μ] (hX : Martingale X ℱ μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
        fun k => |X k ω|) ^ 2) ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ := by
  set M : Ω → ℝ := fun ω => (range (n + 1)).sup' nonempty_range_add_one fun k => |X k ω|
    with hMdef
  have hY := submartingale_abs_of_martingale hX
  have hYnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω => |X n ω| := fun _ _ => abs_nonneg _
  have hXm : ∀ k, Measurable (X k) := fun k =>
    (hX.stronglyMeasurable k).measurable.le (ℱ.le k)
  have hMm : Measurable M :=
    Finset.measurable_range_sup'' fun k _ => continuous_abs.measurable.comp (hXm k)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω =>
    (abs_nonneg _).trans (le_sup' (fun k => |X k ω|) (mem_range.2 n.succ_pos))
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal |X n ω| with hg
  have hgm : Measurable g := (continuous_abs.measurable.comp (hXm n)).ennreal_ofReal
  -- the weak-type bound
  have hweak : ∀ t : ℝ, 0 < t → μ {ω | t ≤ M ω} * ENNReal.ofReal t ≤
      ∫⁻ ω, (if t ≤ M ω then g ω else 0) ∂μ := by
    intro t ht
    have h := maximal_ineq hY hYnn (ε := t.toNNReal) n
    have hc : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [Real.coe_toNNReal t ht.le] at h
    have hset : MeasurableSet {ω | t ≤ M ω} := measurableSet_le measurable_const hMm
    rw [hc, ofReal_integral_eq_lintegral_ofReal ((hY.integrable n).integrableOn)
      (ae_of_all _ fun ω => abs_nonneg _)] at h
    rw [mul_comm]
    refine h.trans (le_of_eq ?_)
    rw [← lintegral_indicator hset]
    refine lintegral_congr fun ω => ?_
    simp only [indicator_apply, mem_ofPred_eq, hg]
  -- layer cake
  have hlc := lintegral_rpow_eq_lintegral_meas_le_mul μ (ae_of_all _ hM0) hMm.aemeasurable
    (p := 2) two_pos
  have hA : ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ ≤ 2 * ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ := by
    have e1 : ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ = ∫⁻ ω, ENNReal.ofReal (M ω ^ (2 : ℝ)) ∂μ := by
      simp_rw [Real.rpow_two]
    rw [e1, hlc, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_ofNat]
    gcongr
    calc ∫⁻ t in Set.Ioi 0, μ {a | t ≤ M a} * ENNReal.ofReal (t ^ (1 : ℝ))
        ≤ ∫⁻ t in Set.Ioi 0, ∫⁻ ω, (if t ≤ M ω then g ω else 0) ∂μ := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          rw [Real.rpow_one]
          exact hweak t ht
      _ = ∫⁻ ω, (∫⁻ t in Set.Ioi (0 : ℝ), (if t ≤ M ω then g ω else 0)) ∂μ := by
          refine lintegral_lintegral_swap ?_
          refine Measurable.aemeasurable ?_
          exact Measurable.ite (measurableSet_le measurable_fst (hMm.comp measurable_snd))
            (hgm.comp measurable_snd) measurable_const
      _ = ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ := by
          refine lintegral_congr fun ω => ?_
          have e2 : (fun t => if t ≤ M ω then g ω else 0) = (Set.Iic (M ω)).indicator fun _ =>
              g ω := by
            funext t
            simp only [indicator_apply, Set.mem_Iic]
          rw [e2, lintegral_indicator_const measurableSet_Iic,
            Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi, Real.volume_Ioc, sub_zero]
  -- finiteness of the left side
  have hfin : ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ ≠ ⊤ := by
    have hle : ∀ ω, M ω ^ 2 ≤ ∑ k ∈ range (n + 1), X k ω ^ 2 := fun ω => by
      obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one fun k => |X k ω|
      have : M ω = |X k ω| := hkeq
      rw [this, sq_abs]
      exact single_le_sum (f := fun k => X k ω ^ 2) (fun _ _ => sq_nonneg _) hk
    refine (lt_of_le_of_lt (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hle ω)) ?_).ne
    have hint : Integrable (fun ω => ∑ k ∈ range (n + 1), X k ω ^ 2) μ :=
      integrable_finsetSum _ fun k _ => (hL2 k).integrable_sq
    exact hint.lintegral_lt_top
  -- the elementary inequality `2ab ≤ 2a² + b²/2`
  have hpt : ∀ ω, 2 * (g ω * ENNReal.ofReal (M ω))
      ≤ 2 * ENNReal.ofReal (X n ω ^ 2) + ENNReal.ofReal (M ω ^ 2) / 2 := fun ω => by
    simp only [hg]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (2 * |X n ω| - M ω), sq_abs (X n ω)]
  have hB : 2 * ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ
      ≤ 2 * ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ + (∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ) / 2 := by
    have hm1 : Measurable fun ω => ENNReal.ofReal (X n ω ^ 2) :=
      ((hXm n).pow_const 2).ennreal_ofReal
    have hm2 : Measurable fun ω => ENNReal.ofReal (M ω ^ 2) := (hMm.pow_const 2).ennreal_ofReal
    calc 2 * ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ
        = ∫⁻ ω, 2 * (g ω * ENNReal.ofReal (M ω)) ∂μ :=
          (lintegral_const_mul 2 (hgm.mul hMm.ennreal_ofReal)).symm
      _ ≤ ∫⁻ ω, (2 * ENNReal.ofReal (X n ω ^ 2) + ENNReal.ofReal (M ω ^ 2) / 2) ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ ω, 2 * ENNReal.ofReal (X n ω ^ 2) ∂μ + ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) * 2⁻¹ ∂μ := by
          simp_rw [div_eq_mul_inv]
          exact lintegral_add_left (hm1.const_mul 2) _
      _ = _ := by
          rw [lintegral_const_mul _ hm1, lintegral_mul_const _ hm2, div_eq_mul_inv]
  set A := ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ
  set B := ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ
  have h1 : A / 2 + A / 2 ≤ 2 * B + A / 2 := by
    rw [ENNReal.add_halves]
    exact hA.trans hB
  have hA2 : A / 2 ≠ ⊤ := ENNReal.div_ne_top hfin two_ne_zero
  have h2 : A / 2 ≤ 2 * B := (ENNReal.add_le_add_iff_right hA2).1 h1
  calc A = 2 * (A / 2) := (ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
    _ ≤ 2 * (2 * B) := by gcongr
    _ = 4 * B := by rw [← mul_assoc]; norm_num

/-! ### The predictable quadratic variation -/

/-- **The compensator of `X²`.** For a real martingale `X` with each `X k ∈ L²` and a finite
measure, `X_n² − Q_n` is a martingale, where
`Q_n = ∑_{i<n} μ[(X_{i+1} − X_i)² | ℱ_i]` is the predictable quadratic variation. -/
theorem martingale_sq_sub_predictableVariation [IsFiniteMeasure μ] (hX : Martingale X ℱ μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) :
    Martingale (fun n ω => X n ω ^ 2 - ∑ i ∈ range n,
      μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) ℱ μ := by
  set D : ℕ → Ω → ℝ := fun i ω => (X (i + 1) ω - X i ω) ^ 2 with hD
  set Δ : ℕ → Ω → ℝ := fun i ω => X (i + 1) ω - X i ω with hΔ
  have hXi : ∀ k, Integrable (X k) μ := fun k => hX.integrable k
  have hDi : ∀ i, Integrable (D i) μ := fun i => ((hL2 (i + 1)).sub (hL2 i)).integrable_sq
  have hΔi : ∀ i, Integrable (Δ i) μ := fun i => (hXi (i + 1)).sub (hXi i)
  have hsq : ∀ k, Integrable (fun ω => X k ω ^ 2) μ := fun k => (hL2 k).integrable_sq
  have hprod : ∀ i, Integrable (X i * Δ i) μ := fun i => by
    have hm : AEStronglyMeasurable (X i * Δ i) μ :=
      (((hX.stronglyMeasurable i).mono (ℱ.le i)).aestronglyMeasurable).mul
        (hΔi i).aestronglyMeasurable
    refine Integrable.mono' (((hsq i).add (hDi i)).div_const 2) hm
      (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, abs_mul, hD, hΔ]
    nlinarith [sq_nonneg (|X i ω| - |X (i + 1) ω - X i ω|), sq_abs (X i ω),
      sq_abs (X (i + 1) ω - X i ω)]
  refine martingale_of_condExp_sub_eq_zero_nat ?_ ?_ ?_
  · intro n
    refine ((hX.stronglyMeasurable n).pow 2).sub ?_
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
    exact stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range.1 hi).le)
  · intro n
    exact (hsq n).sub (integrable_finsetSum _ fun i _ => integrable_condExp)
  · intro i
    have hdiff : (fun ω => X (i + 1) ω ^ 2 - ∑ j ∈ range (i + 1), μ[D j | ℱ j] ω) -
        (fun ω => X i ω ^ 2 - ∑ j ∈ range i, μ[D j | ℱ j] ω)
        = D i + (2 : ℝ) • (X i * Δ i) - μ[D i | ℱ i] := by
      funext ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
        Finset.sum_range_succ, hD, hΔ]
      ring
    rw [hdiff]
    have hcondΔ : μ[Δ i | ℱ i] =ᵐ[μ] 0 := by
      have h1 := condExp_sub (hXi (i + 1)) (hXi i) (ℱ i)
      have h2 := hX.condExp_ae_eq (Nat.le_succ i)
      rw [condExp_of_stronglyMeasurable (ℱ.le i) (hX.stronglyMeasurable i) (hXi i)] at h1
      filter_upwards [h1, h2] with ω h1 h2
      simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
      rw [show Δ i = X (i + 1) - X i from rfl, h1, h2, sub_self]
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (hX.stronglyMeasurable i)
      (hprod i) (hΔi i)
    have hsm := condExp_smul (μ := μ) (2 : ℝ) (X i * Δ i) (ℱ i)
    have hadd := condExp_add (hDi i) ((hprod i).smul (2 : ℝ)) (ℱ i)
    have hsub := condExp_sub ((hDi i).add ((hprod i).smul (2 : ℝ))) (integrable_condExp
      (m := ℱ i) (f := D i)) (ℱ i)
    have hcc : μ[μ[D i | ℱ i] | ℱ i] = μ[D i | ℱ i] :=
      condExp_of_stronglyMeasurable (ℱ.le i) stronglyMeasurable_condExp integrable_condExp
    rw [hcc] at hsub
    filter_upwards [hsub, hadd, hsm, hpull, hcondΔ] with ω e1 e2 e3 e4 e5
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.zero_apply,
      smul_eq_mul] at e1 e2 e3 e4 e5 ⊢
    rw [e1, e2, e3, e4, e5]
    ring

/-! ### Non-vacuity witnesses -/

/-- The hypotheses of `lintegral_sup_abs_sq_le` hold for the zero martingale on any finite
measure space. -/
example [IsFiniteMeasure μ]
    (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
        fun k => |(0 : ℕ → Ω → ℝ) k ω|) ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((0 : ℕ → Ω → ℝ) n ω ^ 2) ∂μ :=
  lintegral_sup_abs_sq_le (martingale_zero ℝ ℱ μ) (fun _ => MemLp.zero) n

/-- The hypotheses of `lintegral_sup_abs_sq_le` hold for a constant nonzero martingale. -/
example [IsFiniteMeasure μ]
    (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
        fun k => |(fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) k ω|) ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) n ω ^ 2) ∂μ :=
  lintegral_sup_abs_sq_le (martingale_const ℱ μ (1 : ℝ)) (fun _ => memLp_const 1) n

/-- The hypotheses of `martingale_sq_sub_predictableVariation` hold for the constant martingale
`X ≡ 1` on any finite measure space. -/
example [IsFiniteMeasure μ] :
    Martingale (fun n ω => (fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) n ω ^ 2 - ∑ i ∈ range n,
      μ[fun ω => ((fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) (i + 1) ω -
        (fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) i ω) ^ 2 | ℱ i] ω) ℱ μ :=
  martingale_sq_sub_predictableVariation (martingale_const ℱ μ (1 : ℝ))
    (fun _ => memLp_const 1)


/-! ### Stopping before a variance overshoot -/

/-- A martingale transform by indicators of predictable sets: if `G i` is `ℱ i`-measurable,
then `∑_{i<n} 1_{G i} (X_{i+1} − X_i)` is a martingale. -/
theorem martingale_sum_indicator_mul_sub [IsFiniteMeasure μ] (hX : Martingale X ℱ μ)
    {G : ℕ → Set Ω} (hG : ∀ i, MeasurableSet[ℱ i] (G i)) :
    Martingale (fun n => ∑ i ∈ range n, (G i).indicator 1 * (X (i + 1) - X i)) ℱ μ := by
  have hξ : StronglyAdapted ℱ fun i => (G i).indicator (1 : Ω → ℝ) := fun i =>
    stronglyMeasurable_const.indicator (hG i)
  have hb : ∀ n ω, (G n).indicator (1 : Ω → ℝ) ω ≤ 1 := fun n ω => by
    by_cases h : ω ∈ G n <;> simp [h]
  have hp : ∀ n ω, 0 ≤ (G n).indicator (1 : Ω → ℝ) ω := fun n ω => by
    by_cases h : ω ∈ G n <;> simp [h]
  have h1 := hX.submartingale.sum_mul_sub hξ hb hp
  have h2 := (hX.neg.submartingale.sum_mul_sub hξ hb hp).neg
  refine martingale_iff.2 ⟨?_, h1⟩
  convert h2 using 1
  funext n ω
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The predictable quadratic variation of the indicator transform
`∑_{i<n} 1_{G i} (X_{i+1} − X_i)` has increments `1_{G i} μ[(X_{i+1} − X_i)² | ℱ i]`. -/
theorem condExp_sq_sub_sum_indicator_mul_sub_ae_eq (hL2 : ∀ k, MemLp (X k) 2 μ)
    {G : ℕ → Set Ω} (hG : ∀ i, MeasurableSet[ℱ i] (G i)) (i : ℕ) :
    μ[fun ω => ((∑ j ∈ range (i + 1), (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω -
        (∑ j ∈ range i, (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω) ^ 2 | ℱ i] =ᵐ[μ]
      (G i).indicator (μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i]) := by
  have e : (fun ω => ((∑ j ∈ range (i + 1), (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω -
        (∑ j ∈ range i, (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω) ^ 2) =
      (G i).indicator fun ω => (X (i + 1) ω - X i ω) ^ 2 := by
    funext ω
    rw [Finset.sum_range_succ, Pi.add_apply, add_sub_cancel_left]
    by_cases h : ω ∈ G i <;> simp [h]
  rw [e]
  exact condExp_indicator ((hL2 (i + 1)).sub (hL2 i)).integrable_sq (hG i)

/-- **Doob's maximal bound with a truncated predictable variance.** Let `X` be a real
martingale with `X 0 = 0` and every `X n` in `L²`, let
`Q n = ∑_{i<n} μ[(X_{i+1} − X_i)² | ℱ i]` be its predictable quadratic variation and `T` a
stopping time with values in `ℕ∞ = WithTop ℕ`. With `Q_T = sup_n Q_{n ∧ T}` (the
increasing limit) and `M_T = sup_{n ≤ T} |X_n|`, for every finite `λ ≥ 0`,
`∫_{Q_T ≤ λ} M_T² ≤ 4 ∫ min Q_T λ`. -/
theorem setLIntegral_iSup_abs_sq_le_four_mul_lintegral_min [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) (hX0 : X 0 = 0) (hL2 : ∀ n, MemLp (X n) 2 μ)
    {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T) (l : ℝ≥0) :
    ∫⁻ ω in {ω | (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) ≤ l},
        (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, min (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) (l : ℝ≥0∞) ∂μ := by
  classical
  set q : ℕ → Ω → ℝ := fun i => μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] with hq
  set Q : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ range k, q i ω with hQ
  set QT : Ω → ℝ≥0∞ := fun ω => ⨆ n : ℕ, ENNReal.ofReal (stoppedProcess Q T n ω) with hQT
  change ∫⁻ ω in {ω | QT ω ≤ l}, _ ∂μ ≤ 4 * ∫⁻ ω, min (QT ω) (l : ℝ≥0∞) ∂μ
  -- basic measurability
  have hqm : ∀ i j, i ≤ j → Measurable[ℱ j] (q i) := fun i j hij =>
    (stronglyMeasurable_condExp.mono (ℱ.mono hij)).measurable
  have hQm : ∀ k, Measurable (Q k) := fun k =>
    Finset.measurable_sum _ fun i _ => (hqm i i le_rfl).mono (ℱ.le i) le_rfl
  have hQTm : Measurable QT := by
    refine Measurable.iSup fun n => Measurable.ennreal_ofReal ?_
    rw [stoppedProcess_eq]
    refine ((hQm n).indicator (ℱ.le n _ (hT.measurableSet_ge n))).add ?_
    rw [Finset.sum_fn]
    exact Finset.measurable_sum _ fun i _ => (hQm i).indicator (ℱ.le i _ (hT.measurableSet_eq i))
  have hE : MeasurableSet {ω | QT ω ≤ l} := measurableSet_le hQTm measurable_const
  -- `ofReal (Q k) ≤ Q_T` whenever `k ≤ T`
  have hQk : ∀ ω (k : ℕ), (k : WithTop ℕ) ≤ T ω → ENNReal.ofReal (Q k ω) ≤ QT ω := by
    intro ω k hk
    refine le_trans (le_of_eq ?_) (le_iSup (fun n : ℕ => ENNReal.ofReal (stoppedProcess Q T n ω)) k)
    rw [stoppedProcess_eq_of_le (u := Q) (i := k) hk]
  have hl : (l : ℝ≥0∞) = ENNReal.ofReal l := (ENNReal.ofReal_coe_nnreal).symm
  -- the predictable sets `{i < T} ∩ {Q_{j+1} ≤ λ for j ≤ i}`
  set G : ℕ → Set Ω := fun i => {ω | (i : WithTop ℕ) < T ω} ∩
    ⋂ j ∈ Finset.range (i + 1), {ω | Q (j + 1) ω ≤ l} with hGdef
  have hG : ∀ i, MeasurableSet[ℱ i] (G i) := by
    intro i
    refine MeasurableSet.inter ?_ (Finset.measurableSet_biInter _ fun j hj => ?_)
    · have : {ω | (i : WithTop ℕ) < T ω} = {ω | T ω ≤ i}ᶜ := by ext; simp
      rw [this]
      exact (hT i).compl
    · refine measurableSet_le (Finset.measurable_sum _ fun l' hl' => hqm l' i ?_) measurable_const
      have := Finset.mem_range.1 hj
      have := Finset.mem_range.1 hl'
      omega
  have hmemG : ∀ i ω, ω ∈ G i ↔ (i : WithTop ℕ) < T ω ∧ ∀ j < i + 1, Q (j + 1) ω ≤ l := by
    intro i ω
    simp [hGdef]
  -- the stopped martingale
  set Y : ℕ → Ω → ℝ := fun n => ∑ i ∈ range n, (G i).indicator 1 * (X (i + 1) - X i) with hYdef
  have hY : Martingale Y ℱ μ := martingale_sum_indicator_mul_sub hX hG
  have hYL2 : ∀ n, MemLp (Y n) 2 μ := fun n => by
    refine memLp_finsetSum' _ fun i _ => ?_
    have : (G i).indicator 1 * (X (i + 1) - X i) = (G i).indicator (X (i + 1) - X i) := by
      funext ω
      by_cases h : ω ∈ G i <;> simp [h]
    rw [this]
    exact ((hL2 (i + 1)).sub (hL2 i)).indicator (ℱ.le i _ (hG i)).nullMeasurableSet
  -- `E Y_n² = E ∑_{i<n} 1_{G i} q i`
  set R : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ range n, (G i).indicator (q i) ω with hRdef
  have hRint : ∀ n, Integrable (R n) μ := fun n =>
    integrable_finsetSum _ fun i _ => integrable_condExp.indicator (ℱ.le i _ (hG i))
  have hYsq : ∀ n, ∫ ω, Y n ω ^ 2 ∂μ = ∫ ω, R n ω ∂μ := by
    intro n
    have hmart := martingale_sq_sub_predictableVariation hY hYL2
    have h0 := hmart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
    simp only [setIntegral_univ] at h0
    have hY0 : Y 0 = 0 := by simp [hYdef]
    simp only [hY0, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.range_zero, Finset.sum_empty, sub_zero, integral_zero] at h0
    have hV : ∀ᵐ ω ∂μ, ∑ i ∈ range n, μ[fun ω => (Y (i + 1) ω - Y i ω) ^ 2 | ℱ i] ω = R n ω := by
      have := ae_all_iff.2 fun i => condExp_sq_sub_sum_indicator_mul_sub_ae_eq hL2 hG i
      filter_upwards [this] with ω hω
      exact Finset.sum_congr rfl fun i _ => hω i
    have hVint : Integrable (fun ω => ∑ i ∈ range n,
        μ[fun ω => (Y (i + 1) ω - Y i ω) ^ 2 | ℱ i] ω) μ :=
      integrable_finsetSum _ fun i _ => integrable_condExp
    rw [integral_sub (hYL2 n).integrable_sq hVint, integral_congr_ae hV] at h0
    linarith
  have hRnn : ∀ n, 0 ≤ᵐ[μ] R n := by
    intro n
    have := ae_all_iff.2 fun i => condExp_nonneg (m := ℱ i) (μ := μ)
      (f := fun ω => (X (i + 1) ω - X i ω) ^ 2) (Eventually.of_forall fun ω => sq_nonneg _)
    filter_upwards [this] with ω hω
    exact Finset.sum_nonneg fun i _ => Set.indicator_apply_nonneg fun _ => hω i
  -- the combinatorial bound `ofReal (R n) ≤ min Q_T λ`
  have hRle : ∀ n ω, ENNReal.ofReal (R n ω) ≤ min (QT ω) l := by
    intro n ω
    have hanti : ∀ i, ω ∈ G (i + 1) → ω ∈ G i := by
      intro i h
      rw [hmemG] at h ⊢
      refine ⟨lt_trans (WithTop.coe_lt_coe.2 i.lt_succ_self) h.1, fun j hj => h.2 j (by omega)⟩
    have hkn := Nat.findGreatest_le (P := fun k => ∀ i < k, ω ∈ G i) n
    have hspec : ∀ i < Nat.findGreatest (fun k => ∀ i < k, ω ∈ G i) n, ω ∈ G i :=
      Nat.findGreatest_spec (P := fun k => ∀ i < k, ω ∈ G i) (Nat.zero_le n)
        (fun i hi => absurd hi (Nat.not_lt_zero _))
    have hlarge : ∀ m, m ≤ n → (∀ i < m, ω ∈ G i) →
        m ≤ Nat.findGreatest (fun k => ∀ i < k, ω ∈ G i) n := fun m hm hP =>
      Nat.le_findGreatest (P := fun k => ∀ i < k, ω ∈ G i) hm hP
    generalize Nat.findGreatest (fun k => ∀ i < k, ω ∈ G i) n = k at hkn hspec hlarge
    have hiff : ∀ i < n, ω ∈ G i ↔ i < k := by
      intro i hi
      constructor
      · intro h
        by_contra hki
        have aux : ∀ d j, j + d = i → ω ∈ G j := by
          intro d
          induction d with
          | zero => intro j hj; rwa [show j = i by omega]
          | succ d ih => intro j hj; exact hanti j (ih (j + 1) (by omega))
        have hall : ∀ j < i + 1, ω ∈ G j := fun j hj => aux (i - j) j (by omega)
        have := hlarge (i + 1) (by omega) hall
        omega
      · exact hspec i
    have hRk : R n ω = Q k ω := by
      simp only [hRdef, hQ]
      rw [← Finset.sum_range_add_sum_Ico _ hkn]
      have h1 : ∑ i ∈ range k, (G i).indicator (q i) ω = ∑ i ∈ range k, q i ω :=
        Finset.sum_congr rfl fun i hi => Set.indicator_of_mem ((hiff i (by
          have := Finset.mem_range.1 hi; omega)).2 (Finset.mem_range.1 hi)) _
      have h2 : ∑ i ∈ Finset.Ico k n, (G i).indicator (q i) ω = 0 :=
        Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (fun h => by
          have := Finset.mem_Ico.1 hi
          have := (hiff i this.2).1 h
          omega) _
      rw [h1, h2, add_zero]
    rw [hRk]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · simp [h0, hQ]
    have hG' : ω ∈ G (k - 1) := (hiff (k - 1) (by omega)).2 (by omega)
    rw [hmemG] at hG'
    refine le_min (hQk ω k ?_) ?_
    · have h1 := hG'.1
      rcases hTω : T ω with _ | m
      · exact le_top
      · rw [hTω, Nat.cast_withTop] at h1
        have := WithTop.coe_lt_coe.1 h1
        rw [Nat.cast_withTop]
        exact WithTop.coe_le_coe.2 (by omega)
    · rw [hl]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hG'.2 (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
  -- `E Y_n² ≤ E min Q_T λ`
  have hYbd : ∀ n, ∫⁻ ω, ENNReal.ofReal (Y n ω ^ 2) ∂μ ≤ ∫⁻ ω, min (QT ω) l ∂μ := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hYL2 n).integrable_sq
      (Eventually.of_forall fun ω => sq_nonneg _), hYsq n,
      ofReal_integral_eq_lintegral_ofReal (hRint n) (hRnn n)]
    exact lintegral_mono fun ω => hRle n ω
  -- on `{Q_T ≤ λ}`, `Y_j = X_j` for `j ≤ T`
  have hYX : ∀ ω, QT ω ≤ l → ∀ j : ℕ, (j : WithTop ℕ) ≤ T ω → Y j ω = X j ω := by
    intro ω hω j hj
    have hsum : Y j ω = ∑ i ∈ range j, (X (i + 1) ω - X i ω) := by
      simp only [hYdef, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.1 hi
      have hmem : ω ∈ G i := by
        rw [hmemG]
        refine ⟨lt_of_lt_of_le (WithTop.coe_lt_coe.2 hi) hj, fun j' hj' => ?_⟩
        have hj1 : ((j' + 1 : ℕ) : WithTop ℕ) ≤ T ω :=
          le_trans (WithTop.coe_le_coe.2 (show j' + 1 ≤ j by omega)) hj
        have h1 := (hQk ω (j' + 1) hj1).trans hω
        rw [hl] at h1
        exact (ENNReal.ofReal_le_ofReal_iff l.coe_nonneg).1 h1
      simp [hmem]
    rw [hsum, Finset.sum_range_sub (fun i => X i ω), hX0, Pi.zero_apply, sub_zero]
  -- truncated maxima
  set MT : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ j : ℕ,
    {ω | (j : WithTop ℕ) ≤ T ω ∧ j ≤ n}.indicator (fun ω => ENNReal.ofReal |X j ω|) ω with hMT
  have hMTm : ∀ n, Measurable (MT n) := by
    intro n
    refine Measurable.iSup fun j => Measurable.indicator ?_ ?_
    · exact (continuous_abs.measurable.comp
        ((hX.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl)).ennreal_ofReal
    · rw [Set.ofPred_and]
      refine MeasurableSet.inter ?_ (MeasurableSet.const _)
      exact ℱ.le j _ (hT.measurableSet_ge j)
  have hMTmono : Monotone MT := by
    intro n n' hnn' ω
    refine iSup_mono fun j => Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le) ω
    intro ω' h
    exact ⟨h.1, h.2.trans hnn'⟩
  have hsup : ∀ ω, (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ≤
      ⨆ n, MT n ω ^ 2 := by
    intro ω
    have h1 : (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ≤ ⨆ n, MT n ω := by
      refine iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le j ?_)
      rw [Set.indicator_of_mem (show ω ∈ {ω | (j : WithTop ℕ) ≤ T ω ∧ j ≤ j} from ⟨hj, le_rfl⟩)]
    refine (pow_le_pow_left₀ zero_le h1 2).trans ?_
    rw [sq, ENNReal.iSup_mul]
    refine iSup_le fun a => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun b => le_iSup_of_le (max a b) ?_
    rw [sq]
    exact mul_le_mul' (hMTmono (le_max_left a b) ω) (hMTmono (le_max_right a b) ω)
  -- finite-horizon bound on the event
  have hfin : ∀ n, ∫⁻ ω in {ω | QT ω ≤ l}, MT n ω ^ 2 ∂μ ≤ 4 * ∫⁻ ω, min (QT ω) l ∂μ := by
    intro n
    calc ∫⁻ ω in {ω | QT ω ≤ l}, MT n ω ^ 2 ∂μ
        ≤ ∫⁻ ω in {ω | QT ω ≤ l}, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
            fun k => |Y k ω|) ^ 2) ∂μ := by
          refine setLIntegral_mono' hE fun ω hω => ?_
          have hs0 : 0 ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => |Y k ω| :=
            (abs_nonneg _).trans (le_sup' (fun k => |Y k ω|) (mem_range.2 n.succ_pos))
          rw [ENNReal.ofReal_pow hs0]
          refine pow_le_pow_left₀ zero_le (iSup_le fun j => ?_) 2
          by_cases hj : ω ∈ {ω | (j : WithTop ℕ) ≤ T ω ∧ j ≤ n}
          · rw [Set.indicator_of_mem hj, ← hYX ω hω j hj.1]
            exact ENNReal.ofReal_le_ofReal
              (le_sup' (fun k => |Y k ω|) (mem_range.2 (Nat.lt_succ_of_le hj.2)))
          · rw [Set.indicator_of_notMem hj]
            exact zero_le
      _ ≤ ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
            fun k => |Y k ω|) ^ 2) ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (Y n ω ^ 2) ∂μ := lintegral_sup_abs_sq_le hY hYL2 n
      _ ≤ 4 * ∫⁻ ω, min (QT ω) l ∂μ := mul_le_mul_of_nonneg_left (hYbd n) zero_le
  calc ∫⁻ ω in {ω | QT ω ≤ l},
        (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ∂μ
      ≤ ∫⁻ ω in {ω | QT ω ≤ l}, ⨆ n, MT n ω ^ 2 ∂μ := lintegral_mono hsup
    _ = ⨆ n, ∫⁻ ω in {ω | QT ω ≤ l}, MT n ω ^ 2 ∂μ :=
        lintegral_iSup (fun n => (hMTm n).pow_const 2)
          (fun n n' h ω => pow_le_pow_left₀ zero_le (hMTmono h ω) 2)
    _ ≤ 4 * ∫⁻ ω, min (QT ω) l ∂μ := iSup_le hfin


/-! ### A variance tail controls the damped maximum -/

/-- A stopped process of measurable functions is measurable at every time. -/
theorem measurable_stoppedProcess_of_measurable {u : ℕ → Ω → ℝ} (hu : ∀ k, Measurable (u k))
    {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T) (n : ℕ) : Measurable (stoppedProcess u T n) := by
  rw [stoppedProcess_eq]
  refine ((hu n).indicator (ℱ.le n _ (hT.measurableSet_ge n))).add ?_
  rw [Finset.sum_fn]
  exact Finset.measurable_sum _ fun i _ => (hu i).indicator (ℱ.le i _ (hT.measurableSet_eq i))

/-- The maximum of `|X_n|` over `n ≤ T` is measurable. -/
theorem measurable_iSup_ofReal_abs_of_le (hXm : ∀ n, Measurable (X n)) {T : Ω → WithTop ℕ}
    (hT : IsStoppingTime ℱ T) :
    Measurable fun ω => ⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω| := by
  refine Measurable.iSup fun n => ?_
  have e : (fun ω => ⨆ (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) =
      {ω | (n : WithTop ℕ) ≤ T ω}.indicator fun ω => ENNReal.ofReal |X n ω| := by
    funext ω
    by_cases h : (n : WithTop ℕ) ≤ T ω <;> simp [h]
  rw [e]
  exact (continuous_abs.measurable.comp (hXm n)).ennreal_ofReal.indicator
    (ℱ.le n _ (hT.measurableSet_ge n))

/-- **Truncated means from a power tail.** If `μ (f ≥ x) ≤ A x^{-θ}` for all `x > 0` with
`θ < 1`, then `∫ min f c ≤ A c^{1-θ} / (1 - θ)`. -/
theorem lintegral_min_ofReal_le_of_meas_le_rpow {f : Ω → ℝ≥0∞} (hf : Measurable f) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ1 : θ < 1)
    (htail : ∀ x : ℝ, 0 < x → μ {ω | ENNReal.ofReal x ≤ f ω} ≤ ENNReal.ofReal (A * x ^ (-θ)))
    {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ ω, min (f ω) (ENNReal.ofReal c) ∂μ ≤ ENNReal.ofReal (A * c ^ (1 - θ) / (1 - θ)) := by
  set g : Ω → ℝ := fun ω => (min (f ω) (ENNReal.ofReal c)).toReal with hg
  have hgm : Measurable g := (hf.min measurable_const).ennreal_toReal
  have hfin : ∀ ω, min (f ω) (ENNReal.ofReal c) ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  have e : ∀ ω, min (f ω) (ENNReal.ofReal c) = ENNReal.ofReal (g ω) := fun ω =>
    (ENNReal.ofReal_toReal (hfin ω)).symm
  simp_rw [e]
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
    hgm.aemeasurable]
  have hint : IntegrableOn (fun t : ℝ => A * t ^ (-θ)) (Set.Ioc 0 c) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (r := -θ)
      (by linarith)).const_mul A
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1 this
  calc ∫⁻ t in Set.Ioi 0, μ {ω | t < g ω}
      ≤ ∫⁻ t in Set.Ioi 0,
          (Set.Ioc 0 c).indicator (fun t => ENNReal.ofReal (A * t ^ (-θ))) t := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        by_cases htc : t ≤ c
        · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 c from ⟨ht, htc⟩)]
          refine (measure_mono fun ω hω => ?_).trans (htail t ht)
          simp only [Set.mem_ofPred_eq] at hω ⊢
          have h1 : ENNReal.ofReal t < min (f ω) (ENNReal.ofReal c) := by
            rw [e ω]
            exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (Set.mem_Ioi.1 ht) hω)).2 hω
          exact (h1.trans_le (min_le_left _ _)).le
        · rw [Set.indicator_of_notMem (fun h => htc h.2)]
          have : {ω | t < g ω} = ∅ := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            have : g ω ≤ c := ENNReal.toReal_le_of_le_ofReal hc (min_le_right _ _)
            linarith
          rw [this, measure_empty]
    _ ≤ ∫⁻ t, (Set.Ioc 0 c).indicator (fun t => ENNReal.ofReal (A * t ^ (-θ))) t :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Set.Ioc 0 c, ENNReal.ofReal (A * t ^ (-θ)) :=
        lintegral_indicator measurableSet_Ioc _
    _ = ENNReal.ofReal (∫ t in Set.Ioc 0 c, A * t ^ (-θ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc
          fun t ht => mul_nonneg hA (Real.rpow_nonneg ht.1.le _))).symm
    _ = ENNReal.ofReal (A * c ^ (1 - θ) / (1 - θ)) := by
        rw [← intervalIntegral.integral_of_le hc, intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith)), show -θ + 1 = 1 - θ by ring,
          Real.zero_rpow (by linarith : (1 - θ) ≠ 0), sub_zero, mul_div_assoc]

/-- The Cauchy–Schwarz inequality on a set, in `ℝ≥0∞`:
`∫_s f ≤ (∫_s f²)^{1/2} μ(s)^{1/2}`. -/
theorem setLIntegral_le_rpow_mul_rpow {f : Ω → ℝ≥0∞} (hf : Measurable f) (s : Set Ω) :
    ∫⁻ ω in s, f ω ∂μ ≤ (∫⁻ ω in s, f ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * μ s ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) Real.HolderConjugate.two_two
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at h
  simpa [ENNReal.rpow_two] using h

/-- The square root in the dyadic Cauchy–Schwarz step. -/
theorem sqrt_four_mul_rpow_mul_rpow_eq {A θ c : ℝ} (hA : 0 ≤ A) (hθ1 : θ < 1) (hc : 0 < c) :
    Real.sqrt (4 * (A * (2 * c) ^ (1 - θ) / (1 - θ)) * (A * c ^ (-θ))) =
      2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) * A * c ^ (1 / 2 - θ) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hs : 0 < Real.sqrt (1 - θ) := Real.sqrt_pos.2 hθ'
  rw [← Real.sqrt_sq (show 0 ≤ 2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) * A * c ^ (1 / 2 - θ)
    by positivity)]
  congr 1
  have e1 : ((2 : ℝ) ^ ((1 - θ) / 2)) ^ 2 = 2 ^ (1 - θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have e2 : (c ^ (1 / 2 - θ)) ^ 2 = c ^ (1 - θ) * c ^ (-θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]
    congr 1
    push_cast
    ring
  have e3 : Real.sqrt (1 - θ) ^ 2 = 1 - θ := Real.sq_sqrt hθ'.le
  rw [show (2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) * A * c ^ (1 / 2 - θ)) ^ 2 =
      4 * ((2 : ℝ) ^ ((1 - θ) / 2)) ^ 2 / Real.sqrt (1 - θ) ^ 2 * A ^ 2 * (c ^ (1 / 2 - θ)) ^ 2
      by ring, e1, e2, e3, Real.mul_rpow (by norm_num) hc.le]
  ring

/-- One dyadic piece: on a set where `c ≤ Q ≤ 2c`, the maximal bound and the power tail give
`∫_s M ≤ 2 · 2^{(1-θ)/2} (1-θ)^{-1/2} A c^{1/2-θ}`. -/
theorem setLIntegral_le_of_forall_le_of_meas_le_rpow {Qv Mv : Ω → ℝ≥0∞} (hQ : Measurable Qv)
    (hM : Measurable Mv)
    (hmax : ∀ l : ℝ≥0, ∫⁻ ω in {ω | Qv ω ≤ l}, Mv ω ^ 2 ∂μ ≤ 4 * ∫⁻ ω, min (Qv ω) l ∂μ)
    {A θ : ℝ} (hA : 0 < A) (hθ1 : θ < 1)
    (htail : ∀ x : ℝ, 0 < x → μ {ω | ENNReal.ofReal x ≤ Qv ω} ≤ ENNReal.ofReal (A * x ^ (-θ)))
    {c : ℝ} (hc : 0 < c) {s : Set Ω}
    (hs : s ⊆ {ω | ENNReal.ofReal c ≤ Qv ω ∧ Qv ω ≤ ENNReal.ofReal (2 * c)}) :
    ∫⁻ ω in s, Mv ω ∂μ ≤
      ENNReal.ofReal (2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) * A * c ^ (1 / 2 - θ)) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hα : 0 ≤ 4 * (A * (2 * c) ^ (1 - θ) / (1 - θ)) :=
    mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
      hθ'.le)
  have hβ : 0 ≤ A * c ^ (-θ) := mul_nonneg hA.le (Real.rpow_nonneg hc.le _)
  have h1 : ∫⁻ ω in s, Mv ω ^ 2 ∂μ ≤ ENNReal.ofReal (4 * (A * (2 * c) ^ (1 - θ) / (1 - θ))) := by
    have hl : ∫⁻ ω in {ω | Qv ω ≤ ENNReal.ofReal (2 * c)}, Mv ω ^ 2 ∂μ ≤
        4 * ∫⁻ ω, min (Qv ω) (ENNReal.ofReal (2 * c)) ∂μ := hmax (2 * c).toNNReal
    calc ∫⁻ ω in s, Mv ω ^ 2 ∂μ
        ≤ ∫⁻ ω in {ω | Qv ω ≤ ENNReal.ofReal (2 * c)}, Mv ω ^ 2 ∂μ :=
          lintegral_mono_set fun ω hω => (hs hω).2
      _ ≤ 4 * ∫⁻ ω, min (Qv ω) (ENNReal.ofReal (2 * c)) ∂μ := hl
      _ ≤ 4 * ENNReal.ofReal (A * (2 * c) ^ (1 - θ) / (1 - θ)) :=
          mul_le_mul_of_nonneg_left (lintegral_min_ofReal_le_of_meas_le_rpow hQ hA.le hθ1 htail
            (by positivity)) zero_le
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have h2 : μ s ≤ ENNReal.ofReal (A * c ^ (-θ)) :=
    (measure_mono fun ω hω => (hs hω).1).trans (htail c hc)
  refine (setLIntegral_le_rpow_mul_rpow hM s).trans ?_
  calc (∫⁻ ω in s, Mv ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * μ s ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (4 * (A * (2 * c) ^ (1 - θ) / (1 - θ))) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (A * c ^ (-θ)) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt (4 * (A * (2 * c) ^ (1 - θ) / (1 - θ)) * (A * c ^ (-θ)))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hα (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hβ (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          Real.sqrt_eq_rpow, Real.mul_rpow hα hβ]
    _ = _ := by rw [sqrt_four_mul_rpow_mul_rpow_eq hA.le hθ1 hc]

/-- **The damped maximum from a variance power tail**, for any pair `(Q, M)` satisfying the
truncated maximal bound `∫_{Q ≤ λ} M² ≤ 4 ∫ min Q λ` for every `λ`: if
`μ (Q ≥ x) ≤ A x^{-θ}` for all `x > 0`, with `A > 0` and `0 ≤ θ < 1/2`, then for `h > 0`,
`∫_{0 < Q < ∞} M (1 - e^{-hQ}) / Q ≤ C_θ A h^{1/2+θ}`. -/
theorem setLIntegral_mul_one_sub_exp_div_le_of_meas_le_rpow {Qv Mv : Ω → ℝ≥0∞}
    (hQ : Measurable Qv) (hM : Measurable Mv)
    (hmax : ∀ l : ℝ≥0, ∫⁻ ω in {ω | Qv ω ≤ l}, Mv ω ^ 2 ∂μ ≤ 4 * ∫⁻ ω, min (Qv ω) l ∂μ)
    {A θ : ℝ} (hA : 0 < A) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (htail : ∀ x : ℝ, 0 < x → μ {ω | ENNReal.ofReal x ≤ Qv ω} ≤ ENNReal.ofReal (A * x ^ (-θ)))
    {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω in {ω | 0 < Qv ω ∧ Qv ω < ⊤},
        Mv ω * ENNReal.ofReal ((1 - Real.exp (-(h * (Qv ω).toReal))) / (Qv ω).toReal) ∂μ ≤
      ENNReal.ofReal (2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) *
        (1 / (1 - 2 ^ (-(1 / 2 + θ))) + 1 / (2 ^ (1 / 2 - θ) - 1)) * A * h ^ (1 / 2 + θ)) := by
  have hθ1 : θ < 1 := by linarith
  set K : ℝ := 2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) * A with hK
  have hK0 : 0 ≤ K := by positivity
  set F : Ω → ℝ≥0∞ := fun ω =>
    Mv ω * ENNReal.ofReal ((1 - Real.exp (-(h * (Qv ω).toReal))) / (Qv ω).toReal) with hF
  set x : Ω → ℝ := fun ω => h * (Qv ω).toReal with hx
  set P : ℕ → Set Ω := fun n =>
    {ω | 0 < Qv ω ∧ Qv ω < ⊤ ∧ (2 : ℝ) ^ n ≤ x ω ∧ x ω < 2 ^ (n + 1)} with hP
  set N : ℕ → Set Ω := fun n =>
    {ω | 0 < Qv ω ∧ Qv ω < ⊤ ∧ ((2 : ℝ) ^ (n + 1))⁻¹ ≤ x ω ∧ x ω < ((2 : ℝ) ^ n)⁻¹} with hN
  -- every point of positive finite variance lies in one dyadic piece
  have hcover : {ω | 0 < Qv ω ∧ Qv ω < ⊤} ⊆ (⋃ n, P n) ∪ ⋃ n, N n := by
    intro ω hω
    obtain ⟨h0, htop⟩ := hω
    have hxpos : 0 < x ω := mul_pos hh (ENNReal.toReal_pos h0.ne' htop.ne)
    have hlo := Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
    have hhi := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (x ω)
    push_cast at hlo hhi
    rcases hk : Int.log 2 (x ω) with n | n
    · left
      refine Set.mem_iUnion.2 ⟨n, h0, htop, ?_, ?_⟩
      · rw [hk, Int.ofNat_eq_natCast, zpow_natCast] at hlo
        exact hlo
      · rw [hk, Int.ofNat_eq_natCast, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast] at hhi
        exact hhi
    · right
      refine Set.mem_iUnion.2 ⟨n, h0, htop, ?_, ?_⟩
      · rw [hk, zpow_negSucc] at hlo
        exact hlo
      · rw [hk, show Int.negSucc n + 1 = -(n : ℤ) by rw [Int.negSucc_eq]; ring, zpow_neg,
          zpow_natCast] at hhi
        exact hhi
  -- pointwise bounds on the damping factor
  have hdamp : ∀ ω, 0 < Qv ω → Qv ω < ⊤ →
      (1 - Real.exp (-(h * (Qv ω).toReal))) / (Qv ω).toReal ≤ h ∧
      (1 - Real.exp (-(h * (Qv ω).toReal))) / (Qv ω).toReal ≤ 1 / (Qv ω).toReal := by
    intro ω h0 htop
    have hq : 0 < (Qv ω).toReal := ENNReal.toReal_pos h0.ne' htop.ne
    constructor
    · rw [div_le_iff₀ hq]
      have := Real.add_one_le_exp (-(h * (Qv ω).toReal))
      linarith
    · exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(h * (Qv ω).toReal))])
        hq.le
  -- the two families of pieces
  have hpieceP : ∀ n : ℕ, ∫⁻ ω in P n, F ω ∂μ ≤
      ENNReal.ofReal (K * h ^ (1 / 2 + θ) * ((2 : ℝ) ^ (-(1 / 2 + θ))) ^ n) := by
    intro n
    set c : ℝ := (2 : ℝ) ^ n / h with hc
    have hc0 : 0 < c := by positivity
    have hsub : P n ⊆ {ω | ENNReal.ofReal c ≤ Qv ω ∧ Qv ω ≤ ENNReal.ofReal (2 * c)} := by
      rintro ω ⟨h0, htop, hlo, hhi⟩
      have hq := ENNReal.ofReal_toReal htop.ne
      constructor
      · rw [← hq]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc, div_le_iff₀ hh]
        linarith [hlo, mul_comm h (Qv ω).toReal]
      · rw [← hq]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc, ← mul_div_assoc, le_div_iff₀ hh, ← pow_succ']
        linarith [hhi, mul_comm h (Qv ω).toReal]
    calc ∫⁻ ω in P n, F ω ∂μ ≤ ∫⁻ ω in P n, Mv ω * ENNReal.ofReal (1 / c) ∂μ := by
          refine setLIntegral_mono (hM.mul_const _) fun ω hω => ?_
          have hq : c ≤ (Qv ω).toReal :=
            (ENNReal.ofReal_le_iff_le_toReal hω.2.1.ne).1 (hsub hω).1
          obtain ⟨h0, htop, _, _⟩ := hω
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          exact (hdamp ω h0 htop).2.trans (one_div_le_one_div_of_le hc0 hq)
      _ = (∫⁻ ω in P n, Mv ω ∂μ) * ENNReal.ofReal (1 / c) := lintegral_mul_const _ hM
      _ ≤ ENNReal.ofReal (K * c ^ (1 / 2 - θ)) * ENNReal.ofReal (1 / c) := by
          gcongr
          exact setLIntegral_le_of_forall_le_of_meas_le_rpow hQ hM hmax hA hθ1 htail hc0 hsub
      _ = ENNReal.ofReal (K * h ^ (1 / 2 + θ) * ((2 : ℝ) ^ (-(1 / 2 + θ))) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have e : ((2 : ℝ) ^ n) ^ (-(1 / 2 + θ)) = ((2 : ℝ) ^ (-(1 / 2 + θ))) ^ n := by
            rw [← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2 + θ))) n, ← Real.rpow_mul (by norm_num)]
            ring_nf
          rw [mul_assoc, ← div_eq_mul_one_div, ← Real.rpow_sub_one hc0.ne',
            show 1 / 2 - θ - 1 = -(1 / 2 + θ) by ring, hc, Real.div_rpow (by positivity) hh.le, e,
            Real.rpow_neg hh.le, div_inv_eq_mul]
          ring
  have hpieceN : ∀ n : ℕ, ∫⁻ ω in N n, F ω ∂μ ≤
      ENNReal.ofReal (K * h ^ (1 / 2 + θ) * ((2 : ℝ) ^ (-(1 / 2 - θ))) ^ (n + 1)) := by
    intro n
    set c : ℝ := ((2 : ℝ) ^ (n + 1))⁻¹ / h with hc
    have hc0 : 0 < c := by positivity
    have hsub : N n ⊆ {ω | ENNReal.ofReal c ≤ Qv ω ∧ Qv ω ≤ ENNReal.ofReal (2 * c)} := by
      rintro ω ⟨h0, htop, hlo, hhi⟩
      have hq := ENNReal.ofReal_toReal htop.ne
      constructor
      · rw [← hq]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc, div_le_iff₀ hh]
        linarith [hlo, mul_comm h (Qv ω).toReal]
      · rw [← hq]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc, ← mul_div_assoc, le_div_iff₀ hh,
          show 2 * ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹ by rw [pow_succ]; field_simp]
        linarith [hhi, mul_comm h (Qv ω).toReal]
    calc ∫⁻ ω in N n, F ω ∂μ ≤ ∫⁻ ω in N n, Mv ω * ENNReal.ofReal h ∂μ := by
          refine setLIntegral_mono (hM.mul_const _) fun ω hω => ?_
          obtain ⟨h0, htop, _, _⟩ := hω
          exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hdamp ω h0 htop).1) zero_le
      _ = (∫⁻ ω in N n, Mv ω ∂μ) * ENNReal.ofReal h := lintegral_mul_const _ hM
      _ ≤ ENNReal.ofReal (K * c ^ (1 / 2 - θ)) * ENNReal.ofReal h := by
          gcongr
          exact setLIntegral_le_of_forall_le_of_meas_le_rpow hQ hM hmax hA hθ1 htail hc0 hsub
      _ = ENNReal.ofReal (K * h ^ (1 / 2 + θ) * ((2 : ℝ) ^ (-(1 / 2 - θ))) ^ (n + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have e : (((2 : ℝ) ^ (n + 1))⁻¹) ^ (1 / 2 - θ) =
              ((2 : ℝ) ^ (-(1 / 2 - θ))) ^ (n + 1) := by
            rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast 2 (n + 1),
              ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num),
              ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2 - θ))) (n + 1),
              ← Real.rpow_mul (by norm_num)]
            ring_nf
          have e2 : h ^ (1 / 2 + θ) = h / h ^ (1 / 2 - θ) := by
            rw [show (1 / 2 + θ) = 1 - (1 / 2 - θ) by ring, Real.rpow_sub hh, Real.rpow_one]
          rw [hc, Real.div_rpow (by positivity) hh.le, e, e2]
          field_simp
  -- summing the pieces
  set a : ℝ := (2 : ℝ) ^ (-(1 / 2 + θ)) with ha
  set b : ℝ := (2 : ℝ) ^ (-(1 / 2 - θ)) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hKh : 0 ≤ K * h ^ (1 / 2 + θ) := by positivity
  have hsumP : ∑' n, ∫⁻ ω in P n, F ω ∂μ ≤ ENNReal.ofReal (K * h ^ (1 / 2 + θ) * (1 - a)⁻¹) := by
    calc ∑' n, ∫⁻ ω in P n, F ω ∂μ ≤ ∑' n : ℕ, ENNReal.ofReal (K * h ^ (1 / 2 + θ) * a ^ n) :=
          ENNReal.tsum_le_tsum hpieceP
      _ = ENNReal.ofReal (∑' n : ℕ, K * h ^ (1 / 2 + θ) * a ^ n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            ((summable_geometric_of_lt_one ha0 ha1).mul_left _)).symm
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
  have hsumN : ∑' n, ∫⁻ ω in N n, F ω ∂μ ≤
      ENNReal.ofReal (K * h ^ (1 / 2 + θ) * b * (1 - b)⁻¹) := by
    calc ∑' n, ∫⁻ ω in N n, F ω ∂μ ≤ ∑' n : ℕ, ENNReal.ofReal (K * h ^ (1 / 2 + θ) * b ^ (n + 1)) :=
          ENNReal.tsum_le_tsum hpieceN
      _ = ∑' n : ℕ, ENNReal.ofReal (K * h ^ (1 / 2 + θ) * b * b ^ n) := by
          congr 1
          funext n
          rw [pow_succ']
          ring_nf
      _ = ENNReal.ofReal (∑' n : ℕ, K * h ^ (1 / 2 + θ) * b * b ^ n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            ((summable_geometric_of_lt_one hb0 hb1).mul_left _)).symm
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hb0 hb1]
  have ht : 1 < (2 : ℝ) ^ (1 / 2 - θ) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hb' : b * (1 - b)⁻¹ = 1 / ((2 : ℝ) ^ (1 / 2 - θ) - 1) := by
    rw [hb, Real.rpow_neg (by norm_num)]
    have : (2 : ℝ) ^ (1 / 2 - θ) - 1 ≠ 0 := by linarith
    have : (2 : ℝ) ^ (1 / 2 - θ) ≠ 0 := by positivity
    field_simp
  calc ∫⁻ ω in {ω | 0 < Qv ω ∧ Qv ω < ⊤}, F ω ∂μ
      ≤ ∫⁻ ω in (⋃ n, P n) ∪ ⋃ n, N n, F ω ∂μ := lintegral_mono_set hcover
    _ ≤ ∫⁻ ω in ⋃ n, P n, F ω ∂μ + ∫⁻ ω in ⋃ n, N n, F ω ∂μ := lintegral_union_le _ _ _
    _ ≤ ∑' n, ∫⁻ ω in P n, F ω ∂μ + ∑' n, ∫⁻ ω in N n, F ω ∂μ :=
        add_le_add (lintegral_iUnion_le _ _) (lintegral_iUnion_le _ _)
    _ ≤ ENNReal.ofReal (K * h ^ (1 / 2 + θ) * (1 - a)⁻¹) +
          ENNReal.ofReal (K * h ^ (1 / 2 + θ) * b * (1 - b)⁻¹) := add_le_add hsumP hsumN
    _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg hKh (inv_pos.2 (by linarith)).le)
          (mul_nonneg (mul_nonneg hKh hb0) (inv_pos.2 (by linarith)).le)]
        congr 1
        rw [mul_assoc (K * h ^ (1 / 2 + θ)) b, hb', hK]
        ring

/-- The constant of the damped maximum bound satisfies `C_θ ≤ 32 / (1 - 2θ)` for
`0 ≤ θ < 1/2`. -/
theorem two_mul_rpow_div_sqrt_mul_add_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) *
        (1 / (1 - 2 ^ (-(1 / 2 + θ))) + 1 / (2 ^ (1 / 2 - θ) - 1)) ≤ 32 / (1 - 2 * θ) := by
  have hP : 2 * 2 ^ ((1 - θ) / 2) / Real.sqrt (1 - θ) ≤ 4 := by
    have hs : 0 < Real.sqrt (1 - θ) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hs]
    have h1 : (2 : ℝ) ^ ((1 - θ) / 2) ≤ 2 ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
    have h3 : Real.sqrt 2 ≤ 2 * Real.sqrt (1 - θ) := by
      rw [show (2 : ℝ) * Real.sqrt (1 - θ) = Real.sqrt (4 * (1 - θ)) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  have ha1 : (2 : ℝ) ^ (-(1 / 2 + θ)) ≤ 3 / 4 := by
    have h1 : (2 : ℝ) ^ (-(1 / 2 + θ)) ≤ 2 ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
        inv_le_comm₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num),
        show (3 / 4 : ℝ)⁻¹ = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hS1 : 1 / (1 - (2 : ℝ) ^ (-(1 / 2 + θ))) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hS1' : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-(1 / 2 + θ))) := div_nonneg zero_le_one (by linarith)
  have h1 : 1 + (1 / 2 - θ) * Real.log 2 ≤ (2 : ℝ) ^ (1 / 2 - θ) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 2 * (1 / 2 - θ))
    linarith
  have hl : (1 / 2 : ℝ) < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.add_one_lt_exp (show (-(1 / 2) : ℝ) ≠ 0 by norm_num)
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (1 / 2)]
  have hu : 0 < 1 / 2 - θ := by linarith
  have hpos : 0 < (2 : ℝ) ^ (1 / 2 - θ) - 1 := by nlinarith
  have hS2 : 1 / ((2 : ℝ) ^ (1 / 2 - θ) - 1) ≤ 4 / (1 - 2 * θ) := by
    rw [div_le_div_iff₀ hpos (by linarith)]
    nlinarith
  have hS2' : 0 ≤ 1 / ((2 : ℝ) ^ (1 / 2 - θ) - 1) := div_nonneg zero_le_one hpos.le
  have hinv : 1 ≤ 1 / (1 - 2 * θ) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  calc _ ≤ 4 * (4 + 4 / (1 - 2 * θ)) :=
        mul_le_mul hP (add_le_add hS1 hS2) (add_nonneg hS1' hS2') (by norm_num)
    _ ≤ 32 / (1 - 2 * θ) := by
        rw [show 32 / (1 - 2 * θ) = 32 * (1 / (1 - 2 * θ)) by ring,
          show 4 / (1 - 2 * θ) = 4 * (1 / (1 - 2 * θ)) by ring]
        nlinarith

/-- **The damped martingale maximum from a predictable-variance power tail.** Under the
assumptions of `setLIntegral_iSup_abs_sq_le_four_mul_lintegral_min`, if
`μ (Q_T ≥ x) ≤ A x^{-θ}` for every real `x > 0`, with `A > 0` and `0 ≤ θ < 1/2`, then for every
`h > 0`, `E[(M_T / Q_T)(1 - e^{-h Q_T}) 1{0 < Q_T < ∞}] ≤ C_θ A h^{1/2+θ}`. -/
theorem setLIntegral_iSup_abs_mul_one_sub_exp_div_le [IsFiniteMeasure μ]
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
        (1 / (1 - 2 ^ (-(1 / 2 + θ))) + 1 / (2 ^ (1 / 2 - θ) - 1)) * A * h ^ (1 / 2 + θ)) := by
  have hXm : ∀ n, Measurable (X n) := fun n =>
    (hX.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hQm : ∀ k, Measurable (fun ω => ∑ i ∈ range k,
      μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) := fun k =>
    Finset.measurable_sum _ fun i _ => (stronglyMeasurable_condExp.mono (ℱ.le i)).measurable
  have hQT : Measurable fun ω => ⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω =>
      ∑ i ∈ range k, μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω) :=
    Measurable.iSup fun n => (measurable_stoppedProcess_of_measurable hQm hT n).ennreal_ofReal
  exact setLIntegral_mul_one_sub_exp_div_le_of_meas_le_rpow hQT
    (measurable_iSup_ofReal_abs_of_le hXm hT)
    (fun l => setLIntegral_iSup_abs_sq_le_four_mul_lintegral_min hX hX0 hL2 hT l) hA hθ0 hθ
    htail hh

end PercLib.Probability
