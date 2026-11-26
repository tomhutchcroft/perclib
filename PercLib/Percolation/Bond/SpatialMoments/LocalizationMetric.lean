/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, adapting the group-based proofs of
`PercLib.Percolation.Bond.SpatialMoments.Localization`. Mathematical reference:
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.4.1.
No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Spatial moments localise the volume of a random set

Let `K` be a random subset of a countable vertex type `V` over a measure space `(Ω, μ)`, with
measurable membership events, and write `χ = E|K|`. For an arbitrary function `f : V → ℝ`
(for instance `f = (dist · o)` on a pseudometric space), write `B_R = {x | f x ≤ R}` and
`S = E[∑_{x ∈ K} f(x)^p]`. Nothing about `f` is assumed: no group structure, no sign; nothing
about `μ` either (it need not be a probability measure), and no coupling between the random
sets of different scales is used. Root clusters of bond percolation are a special case.

## Main results

* `PercLib.Probability.encard_diff_le_mul_tsum_indicator`: for every set `s`,
  `|s \ B_R| ≤ R^{-p} ∑_{x ∈ s} f(x)^p`.
* `PercLib.Probability.lintegral_encard_diff_le_of_lintegral_le`: if `S ≤ (C_p r)^p χ`, then
  `E|K \ B_{C r}| ≤ (C_p / C)^p χ`.
* `PercLib.Probability.lintegral_encard_eq_inter_add_diff`: `χ = E|K ∩ A| + E|K \ A|`.
* `PercLib.Probability.exists_lintegral_encard_le_mul_lintegral_encard_inter`: for every
  `ε > 0` one `C > 0`, depending only on `p`, `C_p`, `ε`, gives `χ ≤ (1 + ε) E|K ∩ B_{C r}|`
  whenever `S ≤ (C_p r)^p χ < ∞`.
* `PercLib.Probability.measure_encard_diff_pos_le`: `μ(|K \ A| > 0) ≤ E|K \ A|` (Markov).
* Metric forms, with `B_R = closedBall o R` and the correlation length
  `ξ_p = (E[∑_{x ∈ K} d(o, x)^p] / χ)^{1/p}`:
  `PercLib.Probability.lintegral_encard_diff_closedBall_div_lintegral_encard_le`,
  `PercLib.Probability.exists_lintegral_encard_le_mul_lintegral_encard_inter_closedBall`,
  `PercLib.Probability.measure_encard_diff_closedBall_pos_le`.
* Bond-percolation corollaries for the root cluster under `law q`:
  `PercLib.Percolation.Bond.lintegral_encard_diff_closedBall_div_chi_le`,
  `PercLib.Percolation.Bond.exists_chi_le_mul_lintegral_encard_inter_closedBall`,
  `PercLib.Percolation.Bond.law_encard_diff_closedBall_pos_le`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {Ω V : Type*} [MeasurableSpace Ω]

/-! ### Localization of a random set along an arbitrary function -/

/-- The volume of a random set inside a fixed set is measurable when the membership events
are measurable. -/
theorem measurable_encard_inter_set [Countable V] {K : Ω → Set V}
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (A : Set V) :
    Measurable fun ω => ((K ω ∩ A).encard : ℝ≥0∞) :=
  (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
    (measurable_encard.comp (Measurable.of_mem fun x => by
      by_cases hx : x ∈ A
      · simp only [mem_inter_iff, hx, and_true]
        exact (hK x).mem
      · simp only [mem_inter_iff, hx, and_false]
        exact measurable_const))

/-- **Pointwise Markov bound.** Every point of `s` with `f x > R > 0` contributes more
than `R^p` to `∑_{x ∈ s} f(x)^p`. -/
theorem encard_diff_le_mul_tsum_indicator (s : Set V) (f : V → ℝ) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R) :
    ((s \ {x | f x ≤ R}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((R ^ p)⁻¹) * ∑' x, s.indicator (fun x => ENNReal.ofReal (f x ^ p)) x := by
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  rw [← ENNReal.tsum_set_one, tsum_subtype (s \ {x | f x ≤ R}) (fun _ => (1 : ℝ≥0∞)),
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ s \ {x | f x ≤ R}
  · rw [indicator_of_mem hx, indicator_of_mem hx.1,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hRp.le), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, one_le_div hRp]
    exact Real.rpow_le_rpow hR.le (le_of_lt (not_le.1 hx.2)) hp.le
  · rw [indicator_of_notMem hx]
    exact zero_le

/-- **Localization from the spatial moment.** Let `p, r, C > 0` and `C_p ≥ 0`. If
`E[∑_{x ∈ K} f(x)^p] ≤ (C_p r)^p E|K|`, then `E|K \ {f ≤ C r}| ≤ (C_p / C)^p E|K|`. -/
theorem lintegral_encard_diff_le_of_lintegral_le (μ : Measure Ω) (K : Ω → Set V)
    {f : V → ℝ} {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C)
    (hS : ∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂μ ≤
      ENNReal.ofReal ((Cp * r) ^ p) * ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) :
    ∫⁻ ω, ((K ω \ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂μ ≤
      ENNReal.ofReal ((Cp / C) ^ p) * ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ := by
  have hCr : 0 < C * r := mul_pos hC hr
  have hCrp : 0 < (C * r) ^ p := Real.rpow_pos_of_pos hCr p
  calc ∫⁻ ω, ((K ω \ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂μ :=
        lintegral_mono fun ω => encard_diff_le_mul_tsum_indicator (K ω) f hp hCr
    _ = ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          ∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          (ENNReal.ofReal ((Cp * r) ^ p) * ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) := by
        gcongr
    _ = ENNReal.ofReal ((Cp / C) ^ p) * ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hCrp.le)]
        congr 2
        rw [Real.mul_rpow (NNReal.coe_nonneg Cp) hr.le, Real.mul_rpow hC.le hr.le,
          Real.div_rpow (NNReal.coe_nonneg Cp) hC.le]
        have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
        have hCp' : 0 < C ^ p := Real.rpow_pos_of_pos hC p
        field_simp

/-- The expected volume of a random set is the expected volume inside `A` plus that
outside. -/
theorem lintegral_encard_eq_inter_add_diff [Countable V] {μ : Measure Ω} {K : Ω → Set V}
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (A : Set V) :
    ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ = ∫⁻ ω, ((K ω ∩ A).encard : ℝ≥0∞) ∂μ +
      ∫⁻ ω, ((K ω \ A).encard : ℝ≥0∞) ∂μ := by
  rw [← lintegral_add_left (measurable_encard_inter_set hK A)]
  refine lintegral_congr fun ω => ?_
  have h := Set.encard_union_eq (s := K ω ∩ A) (t := K ω \ A)
    (Set.disjoint_left.2 fun x h1 h2 => h2.2 h1.2)
  rw [Set.inter_union_sdiff] at h
  rw [h, ENat.toENNReal_add]

/-- **Uniform localization.** For every `ε > 0` there is `C > 0`, depending only on `p`,
`C_p` and `ε`, such that every measure, random set `K` with measurable membership events,
function `f` and scale `r > 0` with `E[∑_{x ∈ K} f(x)^p] ≤ (C_p r)^p E|K| < ∞` satisfy
`E|K| ≤ (1 + ε) E|K ∩ {f ≤ C r}|`. -/
theorem exists_lintegral_encard_le_mul_lintegral_encard_inter [Countable V] {p : ℝ}
    {Cp : ℝ≥0} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure Ω) (K : Ω → Set V), (∀ x, MeasurableSet {ω | x ∈ K ω}) →
      ∀ (f : V → ℝ) (r : ℝ), 0 < r →
      ∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂μ ≤
        ENNReal.ofReal ((Cp * r) ^ p) * ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ →
      ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ < ⊤ →
      ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((K ω ∩ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂μ := by
  -- choose `C` with `(C_p / C)^p ≤ ε / (1 + ε)`
  set δ : ℝ := ε / (1 + ε) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hCp : (0 : ℝ) ≤ Cp := (NNReal.coe_nonneg Cp)
  set C : ℝ := (Cp + 1) / δ ^ p⁻¹ with hC_def
  have hδp : 0 < δ ^ p⁻¹ := Real.rpow_pos_of_pos hδ0 _
  have hC : 0 < C := div_pos (by linarith) hδp
  have hratio : ((Cp : ℝ) / C) ^ p ≤ δ := by
    have h1 : (Cp : ℝ) / C ≤ δ ^ p⁻¹ := by
      rw [hC_def, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ((Cp : ℝ) / C) ^ p ≤ (δ ^ p⁻¹) ^ p :=
          Real.rpow_le_rpow (div_nonneg hCp hC.le) h1 hp.le
      _ = δ := by rw [← Real.rpow_mul hδ0.le, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  refine ⟨C, hC, fun μ K hK f r hr hS hfin => ?_⟩
  have hout := lintegral_encard_diff_le_of_lintegral_le μ K hp hr hC hS
  set χ := ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ
  set I := ∫⁻ ω, ((K ω ∩ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂μ
  have hsplit : χ = I + _ := lintegral_encard_eq_inter_add_diff hK {x | f x ≤ C * r}
  have h1 : χ ≤ I + ENNReal.ofReal δ * χ := by
    calc χ = I + _ := hsplit
      _ ≤ I + ENNReal.ofReal (((Cp : ℝ) / C) ^ p) * χ := add_le_add le_rfl hout
      _ ≤ I + ENNReal.ofReal δ * χ := by gcongr
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (by rw [hsplit]; exact le_self_add)
  have hχ := ENNReal.toReal_mono (by
    exact ENNReal.add_ne_top.2 ⟨hItop, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne⟩) h1
  rw [ENNReal.toReal_add hItop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0.le] at hχ
  rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_toReal hItop,
    ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hχ0 : 0 ≤ χ.toReal := ENNReal.toReal_nonneg
  have hkey : χ.toReal * (1 - δ) ≤ I.toReal := by nlinarith
  have hone : (1 + ε) * (1 - δ) = 1 := by
    rw [hδ]; field_simp; ring
  nlinarith

/-- **Markov form.** The measure of the event that a random set leaves `A` is at most the
expected volume of the random set outside `A`. -/
theorem measure_encard_diff_pos_le [Countable V] {μ : Measure Ω} {K : Ω → Set V}
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (A : Set V) :
    μ {ω | 0 < (K ω \ A).encard} ≤ ∫⁻ ω, ((K ω \ A).encard : ℝ≥0∞) ∂μ := by
  have hm : Measurable fun ω => ((K ω \ A).encard : ℝ≥0∞) := by
    simpa only [sdiff_eq] using measurable_encard_inter_set hK Aᶜ
  calc μ {ω | 0 < (K ω \ A).encard}
      ≤ μ {ω | 1 ≤ ((K ω \ A).encard : ℝ≥0∞)} := by
        refine measure_mono ?_
        intro ω hω
        simp only [mem_ofPred_eq] at hω ⊢
        have h1 : (1 : ℕ∞) ≤ (K ω \ A).encard := Order.one_le_iff_pos.2 hω
        calc (1 : ℝ≥0∞) = ((1 : ℕ∞) : ℝ≥0∞) := by simp
          _ ≤ _ := ENat.toENNReal_le.2 h1
    _ = 1 * μ {ω | 1 ≤ ((K ω \ A).encard : ℝ≥0∞)} := (one_mul _).symm
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hm.aemeasurable 1

/-! ### Metric forms -/

section Metric

variable [PseudoMetricSpace V]

/-- A correlation-length bound `ξ_p ≤ a`, with `ξ_p^p = E[∑_{x ∈ K} d(o, x)^p] / E|K|` and
`E|K| < ∞`, gives the spatial-moment bound `E[∑_{x ∈ K} d(x, o)^p] ≤ a^p E|K|`. -/
theorem lintegral_tsum_dist_rpow_le_of_rpow_inv_le (μ : Measure Ω) (K : Ω → Set V) (o : V)
    {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hχ : ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x ∂μ) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) ^ p⁻¹ ≤ ENNReal.ofReal a) :
    ∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (dist x o ^ p)) x ∂μ ≤
      ENNReal.ofReal (a ^ p) * ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ := by
  rw [ENNReal.rpow_inv_le_iff hp, ENNReal.ofReal_rpow_of_nonneg ha hp.le,
    ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hχ.ne)] at hξ
  simpa only [dist_comm] using hξ

/-- **First clause, for one scale.** If `0 < E|K| < ∞` and the correlation length satisfies
`ξ_p ≤ C_p r`, then `E|K \ B_{C r}| / E|K| ≤ (C_p / C)^p` for every `C > 0`. -/
theorem lintegral_encard_diff_closedBall_div_lintegral_encard_le (μ : Measure Ω)
    (K : Ω → Set V) (o : V) {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C)
    (hχ0 : 0 < ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) (hχ : ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x ∂μ) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    (∫⁻ ω, ((K ω \ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂μ) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((Cp / C) ^ p) := by
  have hS := lintegral_tsum_dist_rpow_le_of_rpow_inv_le μ K o hp
    (mul_nonneg (NNReal.coe_nonneg Cp) hr.le) hχ hξ
  rw [ENNReal.div_le_iff_le_mul (Or.inl hχ0.ne') (Or.inl hχ.ne)]
  exact lintegral_encard_diff_le_of_lintegral_le μ K (f := (dist · o)) hp hr hC hS

/-- **Second clause.** For every `ε > 0` there is `C > 0`, depending only on `p`, `C_p` and
`ε`, such that every measure, random set `K` with measurable membership events, root `o` and
scale `r > 0` with `E|K| < ∞` and `ξ_p ≤ C_p r` satisfy `E|K| ≤ (1 + ε) E|K ∩ B_{C r}|`. -/
theorem exists_lintegral_encard_le_mul_lintegral_encard_inter_closedBall [Countable V]
    {p : ℝ} {Cp : ℝ≥0} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure Ω) (K : Ω → Set V), (∀ x, MeasurableSet {ω | x ∈ K ω}) →
      ∀ (o : V) (r : ℝ), 0 < r →
      ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ < ⊤ →
      ((∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x ∂μ) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r) →
      ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((K ω ∩ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂μ := by
  obtain ⟨C, hC, h⟩ :=
    exists_lintegral_encard_le_mul_lintegral_encard_inter (Ω := Ω) (V := V) (Cp := Cp) hp hε
  refine ⟨C, hC, fun μ K hK o r hr hχ hξ => ?_⟩
  exact h μ K hK (dist · o) r hr
    (lintegral_tsum_dist_rpow_le_of_rpow_inv_le μ K o hp
      (mul_nonneg (NNReal.coe_nonneg Cp) hr.le) hχ hξ) hχ

/-- **Third clause, for one scale.** If `E|K| < ∞` and `ξ_p ≤ C_p r`, then
`μ(|K \ B_{C r}| > 0) ≤ E|K| (C_p / C)^p` for every `C > 0`. -/
theorem measure_encard_diff_closedBall_pos_le [Countable V] {μ : Measure Ω} {K : Ω → Set V}
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (o : V) {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p)
    (hr : 0 < r) (hC : 0 < C) (hχ : ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (K ω).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x ∂μ) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    μ {ω | 0 < (K ω \ Metric.closedBall o (C * r)).encard} ≤
      (∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ) * ENNReal.ofReal ((Cp / C) ^ p) := by
  have hS := lintegral_tsum_dist_rpow_le_of_rpow_inv_le μ K o hp
    (mul_nonneg (NNReal.coe_nonneg Cp) hr.le) hχ hξ
  rw [mul_comm (∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂μ)]
  exact (measure_encard_diff_pos_le hK _).trans
    (lintegral_encard_diff_le_of_lintegral_le μ K (f := (dist · o)) hp hr hC hS)

end Metric

end PercLib.Probability

/-! ### Bond-percolation corollaries -/

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- The cluster volume inside a set is measurable. -/
theorem measurable_encard_cluster_inter (o : V) (A : Set V) :
    Measurable fun ω : Config V => ((cluster ω o ∩ A).encard : ℝ≥0∞) :=
  Probability.measurable_encard_inter_set (fun x => measurableSet_conn o x) A

section Metric

variable [PseudoMetricSpace V]

omit [Countable V] in
/-- First clause of the localization for the root cluster under one profile `q`: if
`0 < χ < ∞` and `ξ_p ≤ C_p r`, then `E|K_o \ B_{C r}| / χ ≤ (C_p / C)^p` for every `C > 0`. -/
theorem lintegral_encard_diff_closedBall_div_chi_le (q : Sym2 V → unitInterval) (o : V)
    {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C) (hχ0 : 0 < chi q o)
    (hχ : chi q o < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    (∫⁻ ω, ((cluster ω o \ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂law q) / chi q o ≤
      ENNReal.ofReal ((Cp / C) ^ p) :=
  Probability.lintegral_encard_diff_closedBall_div_lintegral_encard_le (law q) (cluster · o) o
    hp hr hC hχ0 hχ hξ

/-- Second clause for root clusters: for every `ε > 0` there is `C > 0`, depending only on
`p`, `C_p` and `ε`, such that every profile and scale `r > 0` with `χ < ∞` and `ξ_p ≤ C_p r`
satisfy `χ ≤ (1 + ε) E|K_o ∩ B_{C r}|`. -/
theorem exists_chi_le_mul_lintegral_encard_inter_closedBall {p : ℝ} {Cp : ℝ≥0} (hp : 0 < p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Sym2 V → unitInterval) (o : V) (r : ℝ), 0 < r →
      chi q o < ⊤ →
      ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r) →
      chi q o ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((cluster ω o ∩ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂law q := by
  obtain ⟨C, hC, h⟩ := Probability.exists_lintegral_encard_le_mul_lintegral_encard_inter_closedBall
    (Ω := Config V) (V := V) (Cp := Cp) hp hε
  exact ⟨C, hC, fun q o r hr hχ hξ =>
    h (law q) (cluster · o) (fun x => measurableSet_conn o x) o r hr hχ hξ⟩

/-- Third clause for root clusters: if `χ < ∞` and `ξ_p ≤ C_p r`, then
`P(|K_o \ B_{C r}| > 0) ≤ χ (C_p / C)^p` for every `C > 0`. -/
theorem law_encard_diff_closedBall_pos_le (q : Sym2 V → unitInterval) (o : V)
    {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C) (hχ : chi q o < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    law q {ω | 0 < (cluster ω o \ Metric.closedBall o (C * r)).encard} ≤
      chi q o * ENNReal.ofReal ((Cp / C) ^ p) :=
  Probability.measure_encard_diff_closedBall_pos_le (fun x => measurableSet_conn o x) o
    hp hr hC hχ hξ

end Metric

end PercLib.Percolation.Bond
