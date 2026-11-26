/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference: the
sprinkling (independent layer) argument for the ghost field, in the form of the two-layer
ghost comparison of this library.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.IntensityForm
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Models.LongRange.RootIndependence
public import PercLib.Probability.GhostFieldDerivative
public import Mathlib.Analysis.Calculus.Monotone

/-!
# Changing the intensity at positive field

Let `J : Sym2 V → ℝ≥0` be preserved by a transitive group of bijections of the countable set
`V`, with off-diagonal row sum `L` at the root `o`. Write `q_β = intensityProfile J β` and
`M(β, h) = E_β[1 - e^{-h |K_o|}]` (the ghost transform, with `e^{-h·∞} = 0`).

## Main results

* `PercLib.Probability.deriv_ghost_toReal_eq`: for `h > 0`, `∂_h E[1 - e^{-hT}] = E[T e^{-hT}]`
  (with `T e^{-hT} = 0` at `T = ∞`).
* `PercLib.Probability.mul_ghost_exp_le`: `t e^{-ht} ≤ 1/(e h)`.
* `lintegral_ghost_intensity_add_le`: in `ℝ≥0∞`,
  `G(β + ε) ≤ G(β) + ε L E_β[|K| e^{-h|K|}] G(β + ε)`.
* `ghost_intensity_add_sub_nonneg`, `ghost_intensity_add_sub_le`: the real increment
  `0 ≤ M(β+ε,h) - M(β,h) ≤ ε L M(β+ε,h) ∂_h M(β,h)`.
* `lipschitzWith_ghost_intensity`: `β ↦ M(β, h)` is Lipschitz with constant `L/(e h)`.
* `ae_deriv_ghost_intensity_le`: for almost every `β > 0`, `β ↦ M(β, h)` is differentiable
  and `0 ≤ ∂_β M(β,h) ≤ L M(β,h) ∂_h M(β,h)`.

No finiteness of the susceptibility or of the cluster is assumed: the two-layer comparison
`lintegral_ghost_union_le_of_rowSum_le` allows infinite clusters.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal unitInterval

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- `t e^{-ht} ≤ 1/(e h)` for `h > 0`, with value `0` at `t = ∞`. -/
theorem mul_ghost_exp_le {h : ℝ} (hh : 0 < h) (t : ℕ∞) :
    (t : ℝ≥0∞) * EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal))) ≤
      ENNReal.ofReal (1 / (Real.exp 1 * h)) := by
  induction t using ENat.recTopCoe with
  | top => rw [PercLib.Analysis.exp_neg_mul_top hh, mul_zero]; exact zero_le
  | coe m =>
    rw [PercLib.Percolation.Bond.exp_neg_mul_natCast_eq, ENat.toENNReal_coe,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by positivity)).2 ?_)
    have key : h * m ≤ Real.exp (h * m - 1) := by
      linarith [Real.add_one_le_exp (h * m - 1)]
    have e1 : Real.exp (h * m - 1) * Real.exp 1 = Real.exp (h * m) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(h * m)) * Real.exp (h * m) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hE : 0 ≤ Real.exp (-(h * m)) * Real.exp 1 := by positivity
    calc (m : ℝ) * Real.exp (-(h * m)) * (Real.exp 1 * h)
        = Real.exp (-(h * m)) * Real.exp 1 * (h * m) := by ring
      _ ≤ Real.exp (-(h * m)) * Real.exp 1 * Real.exp (h * m - 1) :=
          mul_le_mul_of_nonneg_left key hE
      _ = 1 := by rw [mul_assoc, mul_comm (Real.exp 1), e1, e2]

/-- `E[T e^{-hT}] ≤ 1/(e h)`. -/
theorem lintegral_mul_ghost_exp_le [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω, (T ω : ℝ≥0∞) * EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal))) ∂μ ≤
      ENNReal.ofReal (1 / (Real.exp 1 * h)) := by
  calc _ ≤ ∫⁻ _, ENNReal.ofReal (1 / (Real.exp 1 * h)) ∂μ :=
        lintegral_mono fun ω => mul_ghost_exp_le hh (T ω)
    _ = _ := by simp

/-- **The field derivative of the ghost transform.** For `h > 0`,
`∂_h E[1 - e^{-hT}] = E[T e^{-hT}]`, where `T e^{-hT} = 0` at `T = ∞`. -/
theorem deriv_ghost_toReal_eq [IsProbabilityMeasure μ] (hT : Measurable T) {h : ℝ} (hh : 0 < h) :
    deriv (fun h : ℝ =>
        (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal) h =
      (∫⁻ ω, (T ω : ℝ≥0∞) * EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal))) ∂μ).toReal := by
  have h1 := iteratedDeriv_ghost_toReal (μ := μ) hT (k := 1) le_rfl hh
  rw [iteratedDeriv_one] at h1
  rw [h1]
  have hS := measurableSet_ne_top hT
  have hf : Measurable fun ω => ((T ω).toNat : ℝ) ^ 1 * Real.exp (-(h * (T ω).toNat)) :=
    (measurable_of_countable
      (fun t : ℕ∞ => (t.toNat : ℝ) ^ 1 * Real.exp (-(h * t.toNat)))).comp hT
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => by positivity)
    hf.aestronglyMeasurable, ← lintegral_indicator hS]
  norm_num
  congr 1
  refine lintegral_congr fun ω => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rcases eq_or_ne (T ω) ⊤ with ht | ht
  · rw [ite_eq_right (not_not.2 ht), ht]
    simp [EReal.coe_mul_top_of_pos hh]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ht
    rw [ite_eq_left ht, ← hm, ENat.toNat_natCast, PercLib.Percolation.Bond.exp_neg_mul_natCast_eq,
      ENat.toENNReal_coe]

end PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A monotone function on `ℝ≥0` whose increments are at most `K` times the step is
`K`-Lipschitz. -/
theorem lipschitzWith_of_monotone_of_add_sub_le {f : ℝ≥0 → ℝ} {K : ℝ≥0} (hf : Monotone f)
    (hK : ∀ x ε : ℝ≥0, f (x + ε) - f x ≤ K * ε) : LipschitzWith K f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  wlog hxy : x ≤ y generalizing x y
  · rw [dist_comm, dist_comm x]
    exact this y x (le_of_not_ge hxy)
  obtain ⟨ε, rfl⟩ := exists_add_of_le hxy
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 (hf le_self_add)), neg_sub, dist_comm,
    NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg ε.coe_nonneg]
  exact hK x ε

/-- Transitivity of the kernel gives transitivity of every intensity profile. -/
theorem intensityProfile_transitive {J : Sym2 V → ℝ≥0}
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) (β : ℝ≥0) :
    ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧
      ∀ e, intensityProfile J β (Sym2.map φ e) = intensityProfile J β e := fun x y => by
  obtain ⟨φ, hφx, hφ⟩ := hT x y
  exact ⟨φ, hφx, intensityProfile_map_eq hφ β⟩

/-- **Sprinkling at positive field, in `ℝ≥0∞`.** For a transitive kernel with root row sum at
most `L`, `G(β + ε) ≤ G(β) + ε L E_β[|K| e^{-h|K|}] G(β + ε)`, where `G(β)` is the ghost
transform at intensity `β`. -/
theorem lintegral_ghost_intensity_add_le [Countable V] {J : Sym2 V → ℝ≥0}
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) {o : V} {L : ℝ≥0}
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o ≤ L) (β ε : ℝ≥0) {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J (β + ε))) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J β)) +
        ε * L * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))
            ∂(law (intensityProfile J β))) *
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J (β + ε))) := by
  have hrow : ∀ u, rowSum (fun e => unitInterval.toENNReal (intensityProfile J ε e)) u ≤
      ε * L := fun u =>
    intensity_rowSum_le J L (fun v => (rowSum_eq_of_transitive J hT v o).trans_le hL) ε u
  have hlaw : (fun e => σ (σ (intensityProfile J β e) * σ (intensityProfile J ε e))) =
      intensityProfile J (β + ε) := funext fun e => (intensityProfile_add J β ε e).symm
  have hG : ∀ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
      (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J (β + ε))) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J (β + ε))) := fun v =>
    (PercLib.Models.LongRange.lintegral_encard_cluster_eq_of_transitive _
      (intensityProfile_transitive hT (β + ε))
      (fun t => 1 - EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal)))) v o).le
  have := lintegral_ghost_union_le_of_rowSum_le (intensityProfile J β) (intensityProfile J ε) o
    hh hrow (G := ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
      (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J (β + ε))))
    (by rw [hlaw]; exact hG)
  rwa [hlaw] at this

/-- The ghost transform at intensity `β` is nondecreasing in `β`. -/
theorem lintegral_ghost_intensity_le_add [Countable V] (J : Sym2 V → ℝ≥0) (o : V)
    (β ε : ℝ≥0) {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J β)) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J (β + ε))) := by
  have hlaw : (fun e => σ (σ (intensityProfile J β e) * σ (intensityProfile J ε e))) =
      intensityProfile J (β + ε) := funext fun e => (intensityProfile_add J β ε e).symm
  have := lintegral_ghost_le_union (intensityProfile J β) (intensityProfile J ε) o hh
  rwa [hlaw] at this

/-- **Sprinkling at positive field: monotonicity.** `0 ≤ M(β + ε, h) - M(β, h)`. -/
theorem ghost_intensity_add_sub_nonneg [Countable V] (J : Sym2 V → ℝ≥0) (o : V)
    (β ε : ℝ≥0) {h : ℝ} (hh : 0 < h) :
    0 ≤ (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J (β + ε)))).toReal -
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J β))).toReal :=
  sub_nonneg.2 (ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (lintegral_one_sub_exp_le_one _ o h)) (lintegral_ghost_intensity_le_add J o β ε hh))

/-- **Sprinkling at positive field: the increment bound.** For a transitive kernel with root
row sum `L`, `M(β + ε, h) - M(β, h) ≤ ε L M(β + ε, h) ∂_h M(β, h)`. -/
theorem ghost_intensity_add_sub_le [Countable V] {J : Sym2 V → ℝ≥0}
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) {o : V} {L : ℝ≥0}
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o = L) (β ε : ℝ≥0) {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J (β + ε)))).toReal -
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J β))).toReal ≤
      ε * L * (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J (β + ε)))).toReal *
        deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
          (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J β))).toReal) h := by
  have hm : Measurable fun ω : Config V => (cluster ω o).encard := measurable_encard_cluster o
  rw [PercLib.Probability.deriv_ghost_toReal_eq hm hh]
  set G₁ := ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
    ∂(law (intensityProfile J (β + ε))) with hG₁
  set G₀ := ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
    ∂(law (intensityProfile J β)) with hG₀
  set D := ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
    EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))
      ∂(law (intensityProfile J β)) with hD
  have hG₁t : G₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (lintegral_one_sub_exp_le_one _ o h)
  have hG₀t : G₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (lintegral_one_sub_exp_le_one _ o h)
  have hDt : D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (PercLib.Probability.lintegral_mul_ghost_exp_le hh)
  have key := lintegral_ghost_intensity_add_le hT hL.le β ε hh
  rw [← hG₀, ← hG₁, ← hD] at key
  have hfin : G₀ + ε * L * D * G₁ ≠ ⊤ := by
    simp only [ne_eq, ENNReal.add_eq_top, hG₀t, false_or]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.coe_ne_top) hDt) hG₁t
  have := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_add hG₀t (ENNReal.add_ne_top.1 hfin).2] at this
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  linarith

/-- The real field derivative `∂_h M(β, h)` is at most `1/(e h)`. -/
theorem deriv_ghost_le [Countable V] (q : Sym2 V → unitInterval) (o : V) {h : ℝ} (hh : 0 < h) :
    deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
      (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law q)).toReal) h ≤ 1 / (Real.exp 1 * h) := by
  rw [PercLib.Probability.deriv_ghost_toReal_eq (measurable_encard_cluster o) hh]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (PercLib.Probability.lintegral_mul_ghost_exp_le hh)

/-- **Lipschitz continuity in the intensity.** For a transitive kernel with root row sum `L`
and `h > 0`, `β ↦ M(β, h)` is Lipschitz with constant `L/(e h)`. -/
theorem lipschitzWith_ghost_intensity [Countable V] {J : Sym2 V → ℝ≥0}
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) {o : V} {L : ℝ≥0}
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o = L) {h : ℝ} (hh : 0 < h) :
    LipschitzWith (Real.toNNReal (L / (Real.exp 1 * h))) fun β : ℝ≥0 =>
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J β))).toReal := by
  refine lipschitzWith_of_monotone_of_add_sub_le (fun β β' hββ' => ?_) fun β ε => ?_
  · obtain ⟨ε, rfl⟩ := exists_add_of_le hββ'
    exact sub_nonneg.1 (ghost_intensity_add_sub_nonneg J o β ε hh)
  · refine (ghost_intensity_add_sub_le hT hL β ε hh).trans ?_
    have hM0 : 0 ≤ (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J (β + ε)))).toReal :=
      ENNReal.toReal_nonneg
    have hM1 : (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J (β + ε)))).toReal ≤
        1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
          ((lintegral_one_sub_exp_le_one _ o h).trans_eq ENNReal.ofReal_one.symm)
    have hD := deriv_ghost_le (intensityProfile J β) o hh
    have hD0 : 0 ≤ deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J β))).toReal) h := by
      rw [PercLib.Probability.deriv_ghost_toReal_eq (measurable_encard_cluster o) hh]
      exact ENNReal.toReal_nonneg
    rw [Real.coe_toNNReal _ (by positivity)]
    have hεL : 0 ≤ (ε : ℝ) * L := by positivity
    calc (ε : ℝ) * L * _ * _ ≤ (ε : ℝ) * L * 1 * (1 / (Real.exp 1 * h)) := by gcongr
      _ = L / (Real.exp 1 * h) * ε := by ring

/-- **Almost-everywhere intensity derivative.** For a transitive kernel with root row sum `L`
and `h > 0`, for almost every `β > 0` the map `b ↦ M(b, h)` is differentiable at `β` and
`0 ≤ ∂_β M(β, h) ≤ L M(β, h) ∂_h M(β, h)`. -/
theorem ae_deriv_ghost_intensity_le [Countable V] {J : Sym2 V → ℝ≥0}
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) {o : V} {L : ℝ≥0}
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o = L) {h : ℝ} (hh : 0 < h) :
    ∀ᵐ β : ℝ, 0 < β →
      DifferentiableAt ℝ (fun b : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J b.toNNReal))).toReal)
        β ∧
      0 ≤ deriv (fun b : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J b.toNNReal))).toReal)
        β ∧
      deriv (fun b : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J b.toNNReal))).toReal)
        β ≤
        L * (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J β.toNNReal))).toReal *
          deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
            (((cluster ω o).encard : ℝ≥0∞) : EReal))))
              ∂(law (intensityProfile J β.toNNReal))).toReal) h := by
  set M : ℝ≥0 → ℝ := fun β => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
    (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J β))).toReal with hM
  have hmono : Monotone M := fun β β' hββ' => by
    obtain ⟨ε, rfl⟩ := exists_add_of_le hββ'
    exact sub_nonneg.1 (ghost_intensity_add_sub_nonneg J o β ε hh)
  have hf : Monotone fun b : ℝ => M b.toNNReal := hmono.comp fun _ _ hab => Real.toNNReal_mono hab
  filter_upwards [hf.ae_differentiableAt] with β hβd hβ
  refine ⟨hβd, ?_⟩
  set D := deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
    (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J β.toNNReal))).toReal) h
    with hD
  have hslope := hβd.hasDerivAt.tendsto_slope_zero_right
  have hcont : Tendsto (fun t : ℝ => (L : ℝ) * M (β + t).toNNReal * D) (𝓝[>] 0)
      (𝓝 ((L : ℝ) * M β.toNNReal * D)) := by
    have h1 : Tendsto (fun t : ℝ => β + t) (𝓝[>] 0) (𝓝 β) := by
      have := (continuous_const_add β).tendsto 0
      rw [add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    exact ((hβd.continuousAt.tendsto.comp h1).const_mul _).mul_const _
  have hstep : ∀ t : ℝ, 0 < t →
      0 ≤ t⁻¹ • (M (β + t).toNNReal - M β.toNNReal) ∧
        t⁻¹ • (M (β + t).toNNReal - M β.toNNReal) ≤ (L : ℝ) * M (β + t).toNNReal * D := by
    intro t ht
    have hadd : (β + t).toNNReal = β.toNNReal + t.toNNReal := Real.toNNReal_add hβ.le ht.le
    rw [hadd, smul_eq_mul]
    have h0 := ghost_intensity_add_sub_nonneg J o β.toNNReal t.toNNReal hh
    have h1 := ghost_intensity_add_sub_le hT hL β.toNNReal t.toNNReal hh
    rw [Real.coe_toNNReal _ ht.le] at h1
    refine ⟨mul_nonneg (inv_nonneg.2 ht.le) h0, ?_⟩
    rw [inv_mul_le_iff₀ ht]
    calc M (β.toNNReal + t.toNNReal) - M β.toNNReal ≤ _ := h1
      _ = t * ((L : ℝ) * M (β.toNNReal + t.toNNReal) * D) := by rw [hD]; ring
  refine ⟨ge_of_tendsto hslope (eventually_nhdsWithin_of_forall fun t ht => (hstep t ht).1),
    le_of_tendsto_of_tendsto hslope hcont
      (eventually_nhdsWithin_of_forall fun t ht => (hstep t ht).2)⟩

end PercLib.Percolation.Bond
