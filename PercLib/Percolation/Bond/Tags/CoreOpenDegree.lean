/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Degree
public import PercLib.Percolation.Bond.DegreeGenerating
public import PercLib.Percolation.Bond.InfiniteDegree
public import PercLib.Percolation.Bond.LocalFiniteness

/-! Correspondence wrappers for the open-degree laws of independent bond percolation.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond
variable {V : Type*}

open Classical in
/-- The expected number of open pairs in a finite set of pairs is the sum of their
probabilities, and the expected number of open ordered pairs leaving a finite vertex set
is the sum of the exterior probabilities. -/
@[tag "TOTD"]
theorem lintegral_open_pairs_and_boundary [Countable V] (q : Sym2 V → unitInterval)
    (F : Finset (Sym2 V)) (Λ : Finset V) :
    ∫⁻ ω, ((ω ∩ F).ncard : ℝ≥0∞) ∂law q = ∑ e ∈ F, (unitInterval.toNNReal (q e) : ℝ≥0∞) ∧
    ∫⁻ ω, ({z : V × V | z.1 ∈ Λ ∧ z.2 ∉ Λ ∧ (openGraph ω).Adj z.1 z.2}.encard : ℝ≥0∞)
        ∂law q =
      ∑ x ∈ Λ, ∑' y, if y ∈ Λ then 0 else (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) :=
  ⟨lintegral_ncard_inter_finset_pairs q F, lintegral_encard_boundary_pairs q Λ⟩

open Classical in
/-- The generating function of the number of open pairs from `v` into a finite set, and
the probability that there is none. -/
@[tag "TEYJ"]
theorem lintegral_pow_card_open_and_law_none (q : Sym2 V → unitInterval) (v : V)
    (F : Finset V) (s : ℝ≥0∞) :
    ∫⁻ ω, s ^ (F.filter fun w => s(v, w) ∈ ω).card ∂law q =
      ∏ w ∈ F, (s * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞))) ∧
    law q {ω : Config V | ∀ w ∈ F, s(v, w) ∉ ω} =
      ∏ w ∈ F, (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) :=
  ⟨lintegral_pow_card_open q v F s, law_forall_not_mem q v F⟩

/-- An infinite off-diagonal row of the kernel at `v` gives, at every positive intensity,
infinite degree and an infinite cluster at `v` almost surely, and both critical
intensities vanish. -/
@[tag "VNRG"]
theorem infinite_row_degree_cluster_threshold [Countable V] (J : Sym2 V → ℝ≥0) (v : V)
    (hJ : rowSum (fun e => (J e : ℝ≥0∞)) v = ∞) :
    (∀ β : ℝ≥0, 0 < β →
      (∀ᵐ ω ∂law (intensityProfile J β), {w | (openGraph ω).Adj v w}.Infinite) ∧
      law (intensityProfile J β) {ω | (cluster ω v).Infinite} = 1) ∧
    rootCriticalIntensity J v = 0 ∧ globalCriticalIntensity J = 0 :=
  ⟨fun _ hβ =>
    ⟨ae_infinite_neighbors_of_rowSum_eq_top _ v (rowSum_intensityProfile_eq_top J v hβ hJ),
      law_cluster_infinite_eq_one_of_rowSum_eq_top _ v
        (rowSum_intensityProfile_eq_top J v hβ hJ)⟩,
    rootCriticalIntensity_eq_zero_of_rowSum_eq_top J v hJ,
    globalCriticalIntensity_eq_zero_of_rowSum_eq_top J v hJ⟩

/-- The open degree is measurable, its mean is the off-diagonal row sum, it satisfies the
Markov bound, and it is almost surely finite when the row sum is finite. -/
@[tag "SZLN"]
theorem open_degree_law [Countable V] (q : Sym2 V → unitInterval) (v : V) :
    Measurable (fun ω : Config V => {w | (openGraph ω).Adj v w}.encard) ∧
    ∫⁻ ω, ({w | (openGraph ω).Adj v w}.encard : ℝ≥0∞) ∂law q =
      rowSum (fun e => unitInterval.toENNReal (q e)) v ∧
    (∀ k : ℕ, (k : ℝ≥0∞) * law q {ω | (k : ℕ∞) ≤ {w | (openGraph ω).Adj v w}.encard} ≤
      rowSum (fun e => unitInterval.toENNReal (q e)) v) ∧
    (rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞ →
      ∀ᵐ ω ∂law q, {w | (openGraph ω).Adj v w}.encard < ⊤) := by
  refine ⟨measurable_degree v, lintegral_degree q v, mul_law_le_degree_le q v,
    fun hrow => ?_⟩
  filter_upwards [ae_finite_neighbors_of_rowSum_lt_top q v hrow] with ω hω
  exact Set.encard_lt_top_iff.2 hω

open Classical in
/-- For `s ≤ 1` and an increasing sequence of finite sets, the generating function of the
limiting number of open pairs from `v` is the decreasing limit, equivalently the infimum,
of the finite products. -/
@[tag "TYZP"]
theorem lintegral_iInf_pow_card_open_tendsto (q : Sym2 V → unitInterval) (v : V)
    {F : ℕ → Finset V} (hF : Monotone F) {s : ℝ≥0∞} (hs : s ≤ 1) :
    ∫⁻ ω, ⨅ n, s ^ ((F n).filter fun w => s(v, w) ∈ ω).card ∂law q =
      ⨅ n, ∏ w ∈ F n, (s * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞))) ∧
    Tendsto (fun n => ∏ w ∈ F n, (s * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)))) atTop
      (𝓝 (∫⁻ ω, ⨅ n, s ^ ((F n).filter fun w => s(v, w) ∈ ω).card ∂law q)) := by
  have h := lintegral_iInf_pow_card_open q v hF hs
  refine ⟨h, ?_⟩
  rw [h]
  apply tendsto_atTop_iInf
  intro m n hmn
  apply Finset.prod_le_prod_of_subset_of_le_one (hF hmn)
  intro w _ _
  have hq : (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (q s(v, w)).property.2
  calc s * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞))
      ≤ 1 * (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) := by gcongr
    _ = 1 := by rw [one_mul, add_tsub_cancel_of_le hq]

/-- On a countable vertex set, almost surely, simultaneously at every vertex, the open
degree is finite where the off-diagonal row sum is finite and infinite where it is
infinite. -/
@[tag "XJ74"]
theorem ae_degree_finite_iff_rowSum [Countable V] (q : Sym2 V → unitInterval) :
    ∀ᵐ ω ∂law q, ∀ v,
      (rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞ →
        ((openGraph ω).neighborSet v).Finite) ∧
      (rowSum (fun e => unitInterval.toENNReal (q e)) v = ∞ →
        ((openGraph ω).neighborSet v).Infinite) := by
  rw [ae_all_iff]
  intro v
  by_cases h : rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞
  · filter_upwards [ae_finite_neighbors_of_rowSum_lt_top q v h] with ω hω
    exact ⟨fun _ => hω, fun h' => absurd h' h.ne⟩
  · have h' : rowSum (fun e => unitInterval.toENNReal (q e)) v = ∞ :=
      not_lt_top_iff.1 h
    filter_upwards [ae_infinite_neighbors_of_rowSum_eq_top q v h'] with ω hω
    exact ⟨fun h'' => absurd h'' h, fun _ => hω⟩

end PercLib.Percolation.Bond
