/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied. Mathematical content:
expansion of the mixed moments of a rescaled counting measure of a random set by Tonelli,
with and without volume size bias.
-/
module

public import PercLib.Probability.SizeBias.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Rescaled cluster measures under volume size bias

Let `K` be a random subset of a countable set `V` with positions `e : V → E`, and for
constants `ζ, s` let `μ = ζ⁻¹ ∑_{x ∈ K} δ_{e x / s}`. Expanding finite products of the
integrals `⟨μ, f_j⟩` and applying Tonelli gives

* `E ∏_j ⟨μ, f_j⟩ = ζ^{-k} ∑_{x_1, …, x_k} ∏_j f_j(e x_j / s) P(x_1, …, x_k ∈ K)`;
* under the volume-biased law `Q = sizeBiased P |K|` (density `|K| / E|K|`),
  `E_Q ∏_j ⟨μ, f_j⟩ = ζ^{-k} ∑_{y, x_1, …, x_k} ∏_j f_j(e x_j / s) P(y, x_1, …, x_k ∈ K) / E|K|`;
* if `0 < E|K| < ∞`, `E|K|² < ∞` and `ζ = E|K|² / E|K|`, then `E_Q μ(E) = 1`.

## Main results

* `prod_tsum_eq_tsum_prod`: `∏_j ∑'_x g_j(x) = ∑'_{x : Fin k → V} ∏_j g_j(x_j)` in `ℝ≥0∞`;
* `lintegral_rescaledCount`: `⟨μ, f⟩ = ζ⁻¹ ∑_{x ∈ K} f(e x / s)`;
* `lintegral_prod_lintegral_rescaledCount`, `lintegral_prod_lintegral_rescaledCount_sizeBiased`,
  `lintegral_rescaledCount_univ_sizeBiased`: the three statements above.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

/-- **Products of sums over a finite index.** In `ℝ≥0∞`,
`∏_{j < k} ∑'_x g_j(x) = ∑'_{x : Fin k → V} ∏_j g_j(x_j)`. -/
theorem prod_tsum_eq_tsum_prod {V : Type*} : ∀ {k : ℕ} (g : Fin k → V → ℝ≥0∞),
    ∏ j, ∑' x, g j x = ∑' x : Fin k → V, ∏ j, g j (x j)
  | 0, g => by simp
  | k + 1, g => by
    rw [Fin.prod_univ_succ, prod_tsum_eq_tsum_prod (fun j => g j.succ),
      ← (Fin.consEquiv fun _ => V).tsum_eq, ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
    refine tsum_congr fun x => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun y => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

variable {Ω : Type*} [MeasurableSpace Ω] {V : Type*} {E : Type*} [MeasurableSpace E]
  [SMul ℝ E]

/-- The rescaled counting measure `ζ⁻¹ ∑_{x ∈ K} δ_{e x / s}` of a set `K ⊆ V`. -/
abbrev rescaledCount (e : V → E) (ζ s : ℝ) (K : Set V) : Measure E :=
  (ENNReal.ofReal ζ)⁻¹ • Measure.sum fun x : V => K.indicator (fun x => Measure.dirac (s⁻¹ • e x)) x

/-- `⟨μ, f⟩ = ζ⁻¹ ∑_{x ∈ K} f(e x / s)`. -/
theorem lintegral_rescaledCount (e : V → E) (ζ s : ℝ) (K : Set V) {f : E → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(rescaledCount e ζ s K) =
      (ENNReal.ofReal ζ)⁻¹ * ∑' x, K.indicator (fun x => f (s⁻¹ • e x)) x := by
  rw [lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx, indicator_of_mem hx, lintegral_dirac' _ hf]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, lintegral_zero_measure]

/-- Pointwise expansion of a product of indicator sums. -/
theorem prod_indicator_eq_mul_indicator {k : ℕ} (K : Set V) (g : Fin k → V → ℝ≥0∞)
    (x : Fin k → V) :
    ∏ j, K.indicator (g j) (x j) =
      (∏ j, g j (x j)) * {_u : Unit | ∀ j, x j ∈ K}.indicator 1 () := by
  by_cases h : ∀ j, x j ∈ K
  · rw [indicator_of_mem (show () ∈ {_u : Unit | ∀ j, x j ∈ K} from h), Pi.one_apply, mul_one]
    exact Finset.prod_congr rfl fun j _ => indicator_of_mem (h j) _
  · rw [indicator_of_notMem (show () ∉ {_u : Unit | ∀ j, x j ∈ K} from h), mul_zero]
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (indicator_of_notMem hj _)

/-- **Mixed moments of a rescaled random counting measure.** For measurable `f_j ≥ 0`,
`E ∏_j ⟨μ, f_j⟩ = ζ^{-k} ∑_{x_1, …, x_k} ∏_j f_j(e x_j / s) P(x_1, …, x_k ∈ K)`. -/
theorem lintegral_prod_lintegral_rescaledCount [Countable V] (P : Measure Ω) (K : Ω → Set V)
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (e : V → E) (ζ s : ℝ) {k : ℕ}
    (f : Fin k → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    ∫⁻ ω, ∏ j, ∫⁻ y, f j y ∂(rescaledCount e ζ s (K ω)) ∂P =
      (ENNReal.ofReal ζ)⁻¹ ^ k *
        ∑' x : Fin k → V, (∏ j, f j (s⁻¹ • e (x j))) * P {ω | ∀ j, x j ∈ K ω} := by
  have hset : ∀ x : Fin k → V, MeasurableSet {ω | ∀ j, x j ∈ K ω} := fun x => by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => hK (x j)
  have hpt : ∀ ω, ∏ j, ∫⁻ y, f j y ∂(rescaledCount e ζ s (K ω)) =
      (ENNReal.ofReal ζ)⁻¹ ^ k * ∑' x : Fin k → V,
        (∏ j, f j (s⁻¹ • e (x j))) * {ω | ∀ j, x j ∈ K ω}.indicator 1 ω := by
    intro ω
    simp_rw [lintegral_rescaledCount e ζ s (K ω) (hf _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prod_tsum_eq_tsum_prod]
    congr 1
    refine tsum_congr fun x => ?_
    rw [prod_indicator_eq_mul_indicator (K ω) (fun j x => f j (s⁻¹ • e x)) x]
    rfl
  simp_rw [hpt]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun x => (((measurable_one.indicator (hset x)).const_mul _).const_mul
      _).aemeasurable]
  refine tsum_congr fun x => ?_
  rw [lintegral_const_mul _ ((measurable_one.indicator (hset x)).const_mul _),
    lintegral_const_mul _ (measurable_one.indicator (hset x)), lintegral_indicator_one (hset x)]

/-- **Mixed moments under volume size bias.** For `Q = sizeBiased P |K|` and measurable
`f_j ≥ 0`, `E_Q ∏_j ⟨μ, f_j⟩ =
ζ^{-k} ∑_{y, x_1, …, x_k} ∏_j f_j(e x_j / s) P(y, x_1, …, x_k ∈ K) / E|K|`, for `ζ > 0`. -/
theorem lintegral_prod_lintegral_rescaledCount_sizeBiased [Countable V] (P : Measure Ω)
    (K : Ω → Set V) (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (e : V → E) {ζ : ℝ} (hζ : 0 < ζ)
    (s : ℝ) {k : ℕ} (f : Fin k → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    ∫⁻ ω, ∏ j, ∫⁻ y, f j y ∂(rescaledCount e ζ s (K ω))
        ∂(sizeBiased P fun ω => ((K ω).encard : ℝ≥0∞)) =
      (ENNReal.ofReal ζ)⁻¹ ^ k * (∑' (y : V) (x : Fin k → V),
        (∏ j, f j (s⁻¹ • e (x j))) * P {ω | y ∈ K ω ∧ ∀ j, x j ∈ K ω}) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P := by
  -- the volume is a sum of indicators
  have hvol : ∀ ω, ((K ω).encard : ℝ≥0∞) = ∑' y, (K ω).indicator 1 y := fun ω => by
    rw [← ENNReal.tsum_set_one]; exact tsum_subtype (K ω) (fun _ => (1 : ℝ≥0∞))
  have hXm : Measurable fun ω => ((K ω).encard : ℝ≥0∞) := by
    simp_rw [hvol]
    exact Measurable.tsum fun y => by
      have : (fun ω => (K ω).indicator (1 : V → ℝ≥0∞) y) = {ω | y ∈ K ω}.indicator 1 := by
        funext ω; by_cases h : y ∈ K ω <;> simp [h]
      rw [this]; exact measurable_one.indicator (hK y)
  have hFm : ∀ k (f : Fin k → E → ℝ≥0∞), (∀ j, Measurable (f j)) →
      Measurable fun ω => ∏ j, ∫⁻ y, f j y ∂(rescaledCount e ζ s (K ω)) := by
    intro k f hf
    refine Finset.measurable_prod _ fun j _ => ?_
    simp_rw [lintegral_rescaledCount e ζ s _ (hf j)]
    refine measurable_const.mul (Measurable.tsum fun x => ?_)
    have : (fun ω => (K ω).indicator (fun x => f j (s⁻¹ • e x)) x) =
        {ω | x ∈ K ω}.indicator fun _ => f j (s⁻¹ • e x) := by
      funext ω; by_cases h : x ∈ K ω <;> simp [h]
    rw [this]; exact measurable_const.indicator (hK x)
  rw [lintegral_sizeBiased P hXm (hFm k f hf)]
  congr 1
  -- `|K| = ζ ⟨μ, 1⟩`: reduce to `k + 1` functions with `f_0 = 1`
  set f' : Fin (k + 1) → E → ℝ≥0∞ := Fin.cons 1 f with hf'
  have hf'm : ∀ j, Measurable (f' j) := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact measurable_one
    · simpa [hf'] using hf j
  have hζ0 : ENNReal.ofReal ζ ≠ 0 := (ENNReal.ofReal_pos.2 hζ).ne'
  have hpt : ∀ ω, ((K ω).encard : ℝ≥0∞) * ∏ j, ∫⁻ y, f j y ∂(rescaledCount e ζ s (K ω)) =
      ENNReal.ofReal ζ * ∏ j, ∫⁻ y, f' j y ∂(rescaledCount e ζ s (K ω)) := by
    intro ω
    rw [Fin.prod_univ_succ]
    simp only [hf', Fin.cons_zero, Fin.cons_succ]
    rw [lintegral_rescaledCount e ζ s _ measurable_one, ← mul_assoc, ← mul_assoc,
      ENNReal.mul_inv_cancel hζ0 ENNReal.ofReal_ne_top, one_mul, hvol]
    rfl
  simp_rw [hpt]
  rw [lintegral_const_mul _ (hFm _ f' hf'm),
    lintegral_prod_lintegral_rescaledCount P K hK e ζ s f' hf'm]
  rw [show ∀ S : ℝ≥0∞, ENNReal.ofReal ζ * ((ENNReal.ofReal ζ)⁻¹ ^ (k + 1) * S) =
      (ENNReal.ofReal ζ)⁻¹ ^ k * S from fun S => by
    rw [pow_succ, mul_comm ((ENNReal.ofReal ζ)⁻¹ ^ k), mul_assoc, ← mul_assoc (ENNReal.ofReal ζ),
      ENNReal.mul_inv_cancel hζ0 ENNReal.ofReal_ne_top, one_mul]]
  congr 1
  rw [← (Fin.consEquiv fun _ => V).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun y => tsum_congr fun x => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    hf', Pi.one_apply, one_mul, Fin.forall_fin_succ]

/-- **Mean-one normalization under volume size bias.** If `0 < E|K| < ∞`, `E|K|² < ∞` and
`ζ = E|K|² / E|K|`, then `E_Q μ(E) = 1` for `Q = sizeBiased P |K|`. -/
theorem lintegral_rescaledCount_univ_sizeBiased [Countable V] (P : Measure Ω) (K : Ω → Set V)
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (e : V → E) (s : ℝ)
    (h0 : ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P ≠ 0) (htop : ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P ≠ ∞)
    (h2 : ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ^ 2 ∂P ≠ ∞) :
    ∫⁻ ω, rescaledCount e ((∫⁻ ω, ((K ω).encard : ℝ≥0∞) ^ 2 ∂P).toReal /
        (∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P).toReal) s (K ω) univ
        ∂(sizeBiased P fun ω => ((K ω).encard : ℝ≥0∞)) = 1 := by
  set X : Ω → ℝ≥0∞ := fun ω => ((K ω).encard : ℝ≥0∞) with hX
  set m1 := ∫⁻ ω, X ω ∂P with hm1
  set m2 := ∫⁻ ω, X ω ^ 2 ∂P with hm2
  have hvol : ∀ ω, X ω = ∑' y, (K ω).indicator 1 y := fun ω => by
    change ((K ω).encard : ℝ≥0∞) = _
    rw [← ENNReal.tsum_set_one]; exact tsum_subtype (K ω) (fun _ => (1 : ℝ≥0∞))
  have hXm : Measurable X := by
    rw [show X = fun ω => ∑' y, (K ω).indicator 1 y from funext hvol]
    exact Measurable.tsum fun y => by
      have : (fun ω => (K ω).indicator (1 : V → ℝ≥0∞) y) = {ω | y ∈ K ω}.indicator 1 := by
        funext ω; by_cases h : y ∈ K ω <;> simp [h]
      rw [this]; exact measurable_one.indicator (hK y)
  -- `m1² ≤ m2`, so `m2 ≠ 0`
  have hm2_0 : m2 ≠ 0 := by
    intro h
    have hae : X =ᵐ[P] 0 := by
      have := (lintegral_eq_zero_iff (hXm.pow_const 2)).1 h
      filter_upwards [this] with ω hω
      simpa using hω
    exact h0 (by rw [hm1, lintegral_congr_ae hae]; simp)
  have hζ : ENNReal.ofReal (m2.toReal / m1.toReal) = m2 / m1 := by
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal h2,
      ENNReal.ofReal_toReal htop]
  have hpt : ∀ ω, rescaledCount e (m2.toReal / m1.toReal) s (K ω) univ = (m2 / m1)⁻¹ * X ω := by
    intro ω
    rw [← lintegral_one, lintegral_rescaledCount e _ s _ (f := fun _ => 1) measurable_const, hζ,
      hvol]
    rfl
  simp_rw [hpt]
  rw [lintegral_const_mul _ hXm, lintegral_self_sizeBiased P hXm, ENNReal.inv_div (Or.inr h2)
    (Or.inr hm2_0)]
  calc m1 / m2 * (m2 / m1) = (m1 * m1⁻¹) * (m2 * m2⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    _ = 1 := by rw [ENNReal.mul_inv_cancel h0 htop, ENNReal.mul_inv_cancel hm2_0 h2, one_mul]

end PercLib.Probability
