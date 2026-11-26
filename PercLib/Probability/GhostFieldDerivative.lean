/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied and no definition is added.
Mathematical reference: the positive-field derivative formula for the ghost-field
transform `M(h) = E[1 - e^{-hT}]` (dominated differentiation under the expectation).
-/
module

public import PercLib.Probability.GhostTransform
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Positive-field derivatives of the ghost-field transform

Let `T : Ω → ℕ∞` be measurable on a finite measure space and, for `h > 0`,
`M(h) = E[1 - e^{-hT}]` (as the real number `(∫⁻ (1 - e^{-hT})).toReal`, with
`e^{-h·⊤} = 0`, the convention of `GhostTransform.lean`). On `(0, ∞)`, `M` differs by a
constant from the moment-generating function of `X = -T` under the measure restricted to
`{T < ∞}`, whose exponential integrability set contains `[0, ∞)`. Mathlib's analytic theory
of moment-generating functions then gives every derivative.

## Main results

* `ghost_toReal_eq_sub_mgf`: `M(h) = μ(Ω) - E[e^{-hT}; T < ∞]` for `h > 0`.
* `analyticOnNhd_ghost_toReal`, `contDiffOn_ghost_toReal`: `M` is analytic, hence smooth,
  on `(0, ∞)`.
* `iteratedDeriv_ghost_toReal`: for `k ≥ 1` and `h > 0`,
  `M^{(k)}(h) = (-1)^{k+1} E[T^k e^{-hT}; T < ∞]`.
* `monotoneOn_ghost_toReal`, `concaveOn_ghost_toReal`: `M` is nondecreasing and concave on
  `(0, ∞)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal Topology

namespace PercLib.Probability

/-- **Pointwise.** For `h > 0`, the real value of `1 - e^{-ht}` is `1` at `t = ⊤` and
`1 - e^{-h t}` for finite `t`. -/
theorem toReal_one_sub_ghost {h : ℝ} (hh : 0 < h) (t : ℕ∞) :
    (1 - EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal)))).toReal =
      1 - {s : ℕ∞ | s ≠ ⊤}.indicator (fun s => Real.exp (h * -(s.toNat : ℝ))) t := by
  induction t using ENat.recTopCoe with
  | top => simp [EReal.coe_mul_top_of_pos hh]
  | coe n =>
    rw [ghost_exp_natCast, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    have hle : Real.exp (n * -h) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [n.cast_nonneg (α := ℝ)])
    rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hle) ENNReal.one_ne_top]
    simp [Set.indicator, mul_comm, (Real.exp_pos _).le]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- `-T`, read through `ENat.toNat`, is measurable. -/
theorem measurable_neg_toNat (hT : Measurable T) :
    Measurable fun ω => -((T ω).toNat : ℝ) :=
  (measurable_of_countable fun t : ℕ∞ => -(t.toNat : ℝ)).comp hT

/-- The event `{T < ∞}` is measurable. -/
theorem measurableSet_ne_top (hT : Measurable T) : MeasurableSet {ω | T ω ≠ ⊤} :=
  (measurableSet_singleton ⊤).compl.preimage hT

/-- **Mgf form.** For `h > 0`, `M(h) = μ(Ω) - E[e^{-hT}; T < ∞]`, the last term being the
moment-generating function of `-T` under `μ` restricted to `{T < ∞}`. -/
theorem ghost_toReal_eq_sub_mgf [IsFiniteMeasure μ] (hT : Measurable T) {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal =
      μ.real univ - mgf (fun ω => -((T ω).toNat : ℝ)) (μ.restrict {ω | T ω ≠ ⊤}) h := by
  have hm : Measurable fun ω => (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) :=
    (measurable_of_countable fun t : ℕ∞ =>
      (1 - EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal))))).comp hT
  rw [← integral_toReal hm.aemeasurable
    (ae_of_all _ fun _ => tsub_le_self.trans_lt ENNReal.one_lt_top)]
  simp_rw [toReal_one_sub_ghost hh]
  have hX := measurable_neg_toNat hT
  have hS := measurableSet_ne_top hT
  have hInt : Integrable (fun ω => Real.exp (h * -((T ω).toNat : ℝ))) μ :=
    integrable_exp_mul_of_le h 0 hh.le hX.aemeasurable
      (ae_of_all _ fun ω => by simp)
  have hind : ∀ ω, {s : ℕ∞ | s ≠ ⊤}.indicator (fun s => Real.exp (h * -(s.toNat : ℝ))) (T ω) =
      {ω | T ω ≠ ⊤}.indicator (fun ω => Real.exp (h * -((T ω).toNat : ℝ))) ω := fun ω => by
    simp [Set.indicator]
  simp_rw [hind]
  rw [integral_sub (integrable_const _) (hInt.indicator hS), integral_const, integral_indicator hS]
  simp [mgf]

/-- `(0, ∞)` lies in the interior of the exponential integrability set of `-T` under `μ`
restricted to `{T < ∞}`. -/
theorem Ioi_subset_interior_integrableExpSet_neg_toNat [IsFiniteMeasure μ] (hT : Measurable T) :
    Ioi 0 ⊆ interior (integrableExpSet (fun ω => -((T ω).toNat : ℝ))
      (μ.restrict {ω | T ω ≠ ⊤})) :=
  interior_maximal (fun _ hh => integrable_exp_mul_of_le _ 0 (le_of_lt hh)
    (measurable_neg_toNat hT).aemeasurable (ae_of_all _ fun ω => by simp)) isOpen_Ioi

/-- Near each `h > 0`, `M` agrees with `μ(Ω)` minus the restricted mgf of `-T`. -/
theorem ghost_toReal_eventuallyEq [IsFiniteMeasure μ] (hT : Measurable T) {h : ℝ} (hh : 0 < h) :
    (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      =ᶠ[𝓝 h] fun h => μ.real univ -
        mgf (fun ω => -((T ω).toNat : ℝ)) (μ.restrict {ω | T ω ≠ ⊤}) h := by
  filter_upwards [isOpen_Ioi.mem_nhds hh] with x hx using ghost_toReal_eq_sub_mgf hT hx

/-- **Analyticity.** `M` is analytic on `(0, ∞)`. -/
theorem analyticOnNhd_ghost_toReal [IsFiniteMeasure μ] (hT : Measurable T) :
    AnalyticOnNhd ℝ
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      (Ioi 0) := fun _ hh =>
  (analyticAt_const.sub
    (analyticAt_mgf (Ioi_subset_interior_integrableExpSet_neg_toNat hT hh))).congr
      (ghost_toReal_eventuallyEq hT hh).symm

/-- **Smoothness.** `M` is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_ghost_toReal [IsFiniteMeasure μ] (hT : Measurable T) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      (Ioi 0) :=
  (analyticOnNhd_ghost_toReal hT).contDiffOn (uniqueDiffOn_Ioi 0)

/-- **Derivative formula.** For `k ≥ 1` and `h > 0`,
`M^{(k)}(h) = (-1)^{k+1} E[T^k e^{-hT}; T < ∞]`. -/
theorem iteratedDeriv_ghost_toReal [IsFiniteMeasure μ] (hT : Measurable T) {k : ℕ} (hk : 1 ≤ k)
    {h : ℝ} (hh : 0 < h) :
    iteratedDeriv k
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      h = (-1) ^ (k + 1) *
        ∫ ω in {ω | T ω ≠ ⊤}, ((T ω).toNat : ℝ) ^ k * Real.exp (-(h * (T ω).toNat)) ∂μ := by
  rw [(ghost_toReal_eventuallyEq hT hh).iteratedDeriv_eq, iteratedDeriv_const_sub hk,
    iteratedDeriv_neg, iteratedDeriv_mgf (Ioi_subset_interior_integrableExpSet_neg_toNat hT hh)]
  simp_rw [neg_pow ((T _).toNat : ℝ), mul_neg, mul_assoc, mul_comm h]
  rw [integral_const_mul, pow_succ]
  ring

/-- `M' ≥ 0` on `(0, ∞)`. -/
theorem deriv_ghost_toReal_nonneg [IsFiniteMeasure μ] (hT : Measurable T) {h : ℝ} (hh : 0 < h) :
    0 ≤ deriv
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      h := by
  rw [← iteratedDeriv_one, iteratedDeriv_ghost_toReal hT le_rfl hh]
  norm_num
  exact setIntegral_nonneg (measurableSet_ne_top hT) fun ω _ => by positivity

/-- `M'' ≤ 0` on `(0, ∞)`. -/
theorem iteratedDeriv_two_ghost_toReal_nonpos [IsFiniteMeasure μ] (hT : Measurable T) {h : ℝ}
    (hh : 0 < h) :
    iteratedDeriv 2
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      h ≤ 0 := by
  rw [iteratedDeriv_ghost_toReal hT (by norm_num) hh]
  norm_num
  exact setIntegral_nonneg (measurableSet_ne_top hT) fun ω _ => by positivity

/-- **Monotonicity.** `M` is nondecreasing on `(0, ∞)`. -/
theorem monotoneOn_ghost_toReal [IsFiniteMeasure μ] (hT : Measurable T) :
    MonotoneOn
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      (Ioi 0) := by
  have hM := contDiffOn_ghost_toReal (μ := μ) hT (n := 1)
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hM.continuousOn ?_ ?_
  · rw [interior_Ioi]; exact hM.differentiableOn one_ne_zero
  · rw [interior_Ioi]; exact fun h hh => deriv_ghost_toReal_nonneg hT hh

/-- **Concavity.** `M` is concave on `(0, ∞)`. -/
theorem concaveOn_ghost_toReal [IsFiniteMeasure μ] (hT : Measurable T) :
    ConcaveOn ℝ (Ioi 0)
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      := by
  have hM := contDiffOn_ghost_toReal (μ := μ) hT (n := 2)
  refine concaveOn_of_deriv2_nonpos (convex_Ioi 0) hM.continuousOn ?_ ?_ ?_
  · rw [interior_Ioi]; exact hM.differentiableOn (by norm_num)
  · rw [interior_Ioi]
    exact (hM.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn one_ne_zero
  · rw [interior_Ioi]
    intro h hh
    rw [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_two_ghost_toReal_nonpos hT hh

end PercLib.Probability
