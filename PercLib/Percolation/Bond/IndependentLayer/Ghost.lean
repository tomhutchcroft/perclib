/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied.
-/
module

public import PercLib.Analysis.Elementary
public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.Coordinate
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-!
# Bernoulli configurations on a sum index, and the ghost transform as a mark probability

1. **Sum index.** A Bernoulli configuration on `α ⊕ β` with profile `Sum.elim p r` restricts
   to the two summands as independent Bernoulli configurations with profiles `p` and `r`
   (`prodBernoulli_map_preimage_inl`, `prodBernoulli_map_preimage_inr`,
   `prodBernoulli_sum_map_prod`).
2. **The exponential of an extended volume.** For `h > 0` and `T : ℕ∞` the quantity
   `e^{-hT}` is written `EReal.exp (-(h * T))`, so that `e^{-h·⊤} = 0`
   (`exp_neg_mul_natCast`, `PercLib.Analysis.exp_neg_mul_top`).
3. **Marks.** Mark each vertex independently with probability `p`, where `1 - p = e^{-h}`.
   A set `A` contains no mark with probability `e^{-h|A|}`, also when `A` is infinite
   (`prodBernoulli_inter_eq_empty`), and so meets the marks with probability
   `1 - e^{-h|A|}` (`prodBernoulli_inter_nonempty`).
4. **Ghost transform.** For a random set `K` with measurable membership events,
   `∫ (1 - e^{-h|K|}) dμ` is the probability that `K` meets an independent mark set
   (`lintegral_one_sub_exp_eq_prod`); for bond clusters this is
   `lintegral_cluster_one_sub_exp_eq_prod`.

This file adds no definition. The marks are only a device of proof; the statements are integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond

/-! ### Bernoulli configurations on a sum index -/

section SumIndex

variable {α β : Type*}

theorem measurable_preimage_inl : Measurable fun η : Set (α ⊕ β) => (Sum.inl ⁻¹' η : Set α) :=
  Measurable.of_mem fun a => measurable_set_mem (Sum.inl a)

theorem measurable_preimage_inr : Measurable fun η : Set (α ⊕ β) => (Sum.inr ⁻¹' η : Set β) :=
  Measurable.of_mem fun b => measurable_set_mem (Sum.inr b)

/-- The left summand of a Bernoulli configuration on `α ⊕ β` is Bernoulli with profile `p`. -/
theorem prodBernoulli_map_preimage_inl (p : α → I) (r : β → I) :
    (prodBernoulli (Sum.elim p r)).map (fun η => (Sum.inl ⁻¹' η : Set α)) = prodBernoulli p := by
  have : IsProbabilityMeasure ((prodBernoulli (Sum.elim p r)).map
      (fun η => (Sum.inl ⁻¹' η : Set α))) :=
    (Measure.isProbabilityMeasure_map_iff measurable_preimage_inl.aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  rw [Measure.map_apply measurable_preimage_inl (measurableSet_setOf_finset_coe_subset F)]
  have hpre : (fun η : Set (α ⊕ β) => (Sum.inl ⁻¹' η : Set α)) ⁻¹' {ω | (F : Set α) ⊆ ω} =
      {η | ((F.map Function.Embedding.inl : Finset (α ⊕ β)) : Set (α ⊕ β)) ⊆ η} := by
    ext η
    simp [Set.subset_def]
  rw [hpre, prodBernoulli_subset, prodBernoulli_subset, Finset.prod_map]
  rfl

/-- The right summand of a Bernoulli configuration on `α ⊕ β` is Bernoulli with profile
`r`. -/
theorem prodBernoulli_map_preimage_inr (p : α → I) (r : β → I) :
    (prodBernoulli (Sum.elim p r)).map (fun η => (Sum.inr ⁻¹' η : Set β)) = prodBernoulli r := by
  have : IsProbabilityMeasure ((prodBernoulli (Sum.elim p r)).map
      (fun η => (Sum.inr ⁻¹' η : Set β))) :=
    (Measure.isProbabilityMeasure_map_iff measurable_preimage_inr.aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  rw [Measure.map_apply measurable_preimage_inr (measurableSet_setOf_finset_coe_subset F)]
  have hpre : (fun η : Set (α ⊕ β) => (Sum.inr ⁻¹' η : Set β)) ⁻¹' {ω | (F : Set β) ⊆ ω} =
      {η | ((F.map Function.Embedding.inr : Finset (α ⊕ β)) : Set (α ⊕ β)) ⊆ η} := by
    ext η
    simp [Set.subset_def]
  rw [hpre, prodBernoulli_subset, prodBernoulli_subset, Finset.prod_map]
  rfl

/-- **Independent summands.** A Bernoulli configuration on `α ⊕ β` is the pair of independent
Bernoulli configurations on `α` and on `β`. -/
theorem prodBernoulli_sum_map_prod (p : α → I) (r : β → I) :
    (prodBernoulli (Sum.elim p r)).map
        (fun η => ((Sum.inl ⁻¹' η : Set α), (Sum.inr ⁻¹' η : Set β))) =
      (prodBernoulli p).prod (prodBernoulli r) := by
  have hm : Measurable fun η : Set (α ⊕ β) => ((Sum.inl ⁻¹' η : Set α), (Sum.inr ⁻¹' η : Set β)) :=
    measurable_preimage_inl.prodMk measurable_preimage_inr
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hm (hs.prod ht), mk_preimage_prod,
    prodBernoulli_inter_of_determined (Sum.elim p r) (P := range Sum.inl) (Q := range Sum.inr)
      Set.isCompl_range_inl_range_inr.disjoint (measurable_preimage_inl hs)
      (measurable_preimage_inr ht) ?_ ?_,
    ← Measure.map_apply measurable_preimage_inl hs, ← Measure.map_apply measurable_preimage_inr ht,
    prodBernoulli_map_preimage_inl, prodBernoulli_map_preimage_inr]
  · intro ω ω' h
    have : (Sum.inl ⁻¹' ω : Set α) = Sum.inl ⁻¹' ω' := by
      ext a
      have := congrArg (Sum.inl a ∈ ·) h
      simpa using this
    simp only [mem_preimage, this]
  · intro ω ω' h
    have : (Sum.inr ⁻¹' ω : Set β) = Sum.inr ⁻¹' ω' := by
      ext b
      have := congrArg (Sum.inr b ∈ ·) h
      simpa using this
    simp only [mem_preimage, this]

end SumIndex

/-! ### The exponential of an extended volume -/

section Exp

/-- At a finite volume `n`, `e^{-hn}` is the `n`-th power of `e^{-h}`. -/
theorem exp_neg_mul_natCast (h : ℝ) (n : ℕ) :
    EReal.exp (-((h : EReal) * (((n : ℕ∞) : ℝ≥0∞) : EReal))) =
      ENNReal.ofReal (Real.exp (-h)) ^ n := by
  have : (((n : ℕ∞) : ℝ≥0∞) : EReal) = ((n : ℝ) : EReal) := by
    simp
  rw [this, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe,
    ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  ring

/-- `e^{-hT} ≤ 1` for `h ≥ 0`. -/
theorem exp_neg_mul_le_one {h : ℝ} (hh : 0 ≤ h) (T : ℕ∞) :
    EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) ≤ 1 := by
  rw [EReal.exp_le_one_iff, EReal.neg_le, neg_zero]
  exact mul_nonneg (by exact_mod_cast hh) (EReal.coe_ennreal_nonneg _)

end Exp

/-! ### Marks -/

section Marks

variable {V : Type*} {h : ℝ} {p : I}

theorem toNNReal_symm_eq_ofReal_exp (hp : ((σ p : I) : ℝ) = Real.exp (-h)) :
    ((unitInterval.toNNReal (σ p) : NNReal) : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-h)) := by
  rw [← hp, ← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]

/-- A finite set contains no mark with probability `e^{-h|F|}`. -/
theorem prodBernoulli_finset_inter_eq_empty (hp : ((σ p : I) : ℝ) = Real.exp (-h))
    (F : Finset V) :
    prodBernoulli (fun _ : V => p) {g | (F : Set V) ∩ g = ∅} =
      ENNReal.ofReal (Real.exp (-h)) ^ F.card := by
  have hc : Measurable (compl : Set V → Set V) :=
    Measurable.of_mem fun i => (measurable_set_mem i).not
  have hpre : {g : Set V | (F : Set V) ∩ g = ∅} = compl ⁻¹' {ω | (F : Set V) ⊆ ω} := by
    ext g
    simp only [mem_ofPred_eq, mem_preimage, subset_compl_iff_disjoint_right,
      disjoint_iff_inter_eq_empty]
  rw [hpre, ← Measure.map_apply hc (measurableSet_setOf_finset_coe_subset F),
    prodBernoulli_map_compl, prodBernoulli_subset]
  simp only [toNNReal_symm_eq_ofReal_exp hp, Finset.prod_const]

/-- **No mark.** A set `A` contains no mark with probability `e^{-h|A|}`; an infinite set
meets the marks almost surely. -/
theorem prodBernoulli_inter_eq_empty (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h))
    (A : Set V) :
    prodBernoulli (fun _ : V => p) {g | A ∩ g = ∅} =
      EReal.exp (-((h : EReal) * ((A.encard : ℝ≥0∞) : EReal))) := by
  rcases A.finite_or_infinite with hA | hA
  · lift A to Finset V using hA
    rw [prodBernoulli_finset_inter_eq_empty hp, encard_coe_eq_coe_finsetCard,
      exp_neg_mul_natCast]
  · rw [hA.encard_eq, PercLib.Analysis.exp_neg_mul_top hh]
    have hz : ENNReal.ofReal (Real.exp (-h)) < 1 := by
      rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
      linarith
    refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hz)
      fun n => ?_) bot_le
    obtain ⟨F, hFA, hF⟩ := hA.exists_subset_card_eq n
    rw [← hF, ← prodBernoulli_finset_inter_eq_empty hp]
    refine measure_mono fun g hg => ?_
    simp only [mem_ofPred_eq] at hg ⊢
    exact subset_empty_iff.1 (hg ▸ inter_subset_inter_left g hFA)

theorem measurableSet_inter_nonempty [Countable V] (A : Set V) :
    MeasurableSet {g : Set V | (A ∩ g).Nonempty} := by
  have : {g : Set V | (A ∩ g).Nonempty} = ⋃ v ∈ A, {g | v ∈ g} := by
    ext g
    simp [Set.Nonempty]
  rw [this]
  exact MeasurableSet.biUnion (to_countable A) fun v _ => measurableSet_mem v

/-- **A mark is hit.** A set `A` meets the marks with probability `1 - e^{-h|A|}`. -/
theorem prodBernoulli_inter_nonempty [Countable V] (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) (A : Set V) :
    prodBernoulli (fun _ : V => p) {g | (A ∩ g).Nonempty} =
      1 - EReal.exp (-((h : EReal) * ((A.encard : ℝ≥0∞) : EReal))) := by
  have hc : {g : Set V | (A ∩ g).Nonempty} = {g | A ∩ g = ∅}ᶜ := by
    ext g
    simp [nonempty_iff_ne_empty]
  rw [hc, prob_compl_eq_one_sub, prodBernoulli_inter_eq_empty hh hp]
  have := (measurableSet_inter_nonempty A).compl
  rwa [hc, compl_compl] at this

/-! ### The ghost transform -/

theorem measurableSet_prod_inter_nonempty [Countable V] {Ω : Type*} [MeasurableSpace Ω]
    {K : Ω → Set V} (hK : ∀ v, MeasurableSet {ω | v ∈ K ω}) :
    MeasurableSet {x : Ω × Set V | (K x.1 ∩ x.2).Nonempty} := by
  have : {x : Ω × Set V | (K x.1 ∩ x.2).Nonempty} =
      ⋃ v, {ω | v ∈ K ω} ×ˢ {g : Set V | v ∈ g} := by
    ext x
    simp [Set.Nonempty]
  rw [this]
  exact MeasurableSet.iUnion fun v => (hK v).prod (measurableSet_mem v)

/-- **The ghost transform is a mark probability.** For a random set `K` with measurable
membership events and independent marks of density `1 - e^{-h}`,
`∫ (1 - e^{-h|K|}) dμ` is the probability that `K` contains a mark. -/
theorem lintegral_one_sub_exp_eq_prod [Countable V] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {K : Ω → Set V} (hK : ∀ v, MeasurableSet {ω | v ∈ K ω})
    (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h)) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((K ω).encard : ℝ≥0∞) : EReal)))) ∂μ =
      (μ.prod (prodBernoulli fun _ : V => p)) {x | (K x.1 ∩ x.2).Nonempty} := by
  rw [Measure.prod_apply (measurableSet_prod_inter_nonempty hK)]
  refine lintegral_congr fun ω => ?_
  rw [← prodBernoulli_inter_nonempty hh hp]
  rfl

/-- The ghost transform of a bond cluster is the probability that the cluster contains a
mark. -/
theorem lintegral_cluster_one_sub_exp_eq_prod [Countable V] (q : Sym2 V → I) (x : V)
    (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h)) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω x).encard : ℝ≥0∞) : EReal)))) ∂(law q) =
      ((law q).prod (prodBernoulli fun _ : V => p))
        {y | (cluster y.1 x ∩ y.2).Nonempty} :=
  lintegral_one_sub_exp_eq_prod (law q) (fun v => measurableSet_conn x v) hh hp

/-! ### Three layers on one index

Two edge layers and the marks are the three blocks of one Bernoulli configuration `η` on
`(Sym2 V ⊕ Sym2 V) ⊕ V` with profile `Sum.elim (Sum.elim q₀ s) (fun _ => p)`: the first
layer is `Sum.inl ⁻¹' (Sum.inl ⁻¹' η)`, the second `Sum.inr ⁻¹' (Sum.inl ⁻¹' η)` and the
marks `Sum.inr ⁻¹' η`. -/

theorem measurable_union_preimage {α : Type*} :
    Measurable fun E : Set (α ⊕ α) => (Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E : Set α) :=
  Measurable.of_mem fun a => (measurable_set_mem (Sum.inl a)).or (measurable_set_mem (Sum.inr a))

/-- The union of the two edge layers has the superposition law. -/
theorem prodBernoulli_map_union_preimage (q₀ s : Sym2 V → I) :
    (prodBernoulli (Sum.elim q₀ s)).map
        (fun E : Set (Sym2 V ⊕ Sym2 V) => (Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E : Config V)) =
      law (fun e => σ (σ (q₀ e) * σ (s e))) := by
  have hm : Measurable fun E : Set (Sym2 V ⊕ Sym2 V) =>
      ((Sum.inl ⁻¹' E : Set (Sym2 V)), (Sum.inr ⁻¹' E : Set (Sym2 V))) :=
    measurable_preimage_inl.prodMk measurable_preimage_inr
  have hu : Measurable fun ω : Config V × Config V => ω.1 ∪ ω.2 :=
    Measurable.of_mem fun e => ((measurable_set_mem e).comp measurable_fst).or
      ((measurable_set_mem e).comp measurable_snd)
  rw [law, ← prodBernoulli_prod_map_union, ← prodBernoulli_sum_map_prod, Measure.map_map hu hm]
  rfl

/-- **Ghost transform of a layer function.** If a random set `K` is a function of the
edge layers, `K = L ∘ F` with `F` measurable, then the probability that `K` contains a
mark is the ghost transform of `L` under the law of `F`. -/
theorem prodBernoulli_sum_inter_nonempty [Countable V] {α : Type*} (a : α → I) {Ω : Type*}
    [MeasurableSpace Ω] {F : Set α → Ω} (hF : Measurable F) {L : Ω → Set V}
    (hL : ∀ v, MeasurableSet {ω | v ∈ L ω}) (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) :
    prodBernoulli (Sum.elim a fun _ : V => p)
        {η | (L (F (Sum.inl ⁻¹' η)) ∩ Sum.inr ⁻¹' η).Nonempty} =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((L ω).encard : ℝ≥0∞) : EReal))))
        ∂((prodBernoulli a).map F) := by
  have hm : Measurable fun η : Set (α ⊕ V) =>
      ((Sum.inl ⁻¹' η : Set α), (Sum.inr ⁻¹' η : Set V)) :=
    measurable_preimage_inl.prodMk measurable_preimage_inr
  have hS := measurableSet_prod_inter_nonempty (Ω := Ω) hL
  have hFm : Measurable (Prod.map F (id : Set V → Set V)) := hF.prodMap measurable_id
  have hprod : ((prodBernoulli a).map F).prod (prodBernoulli fun _ : V => p) =
      ((prodBernoulli a).prod (prodBernoulli fun _ : V => p)).map (Prod.map F id) := by
    rw [← Measure.map_prod_map _ _ hF measurable_id, Measure.map_id]
  rw [lintegral_one_sub_exp_eq_prod _ hL hh hp, hprod, Measure.map_apply hFm hS,
    ← prodBernoulli_sum_map_prod, Measure.map_apply hm (hFm hS)]
  rfl

/-- Under the three-layer law, the union cluster of `v` contains a mark with probability
equal to its ghost transform under the superposition law. -/
theorem prodBernoulli_three_union_cluster [Countable V] (q₀ s : Sym2 V → I) (v : V)
    (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h)) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
        {η | (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) v ∩
          Sum.inr ⁻¹' η).Nonempty} =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) := by
  rw [← prodBernoulli_map_union_preimage]
  exact prodBernoulli_sum_inter_nonempty (Sum.elim q₀ s) measurable_union_preimage
    (L := fun ω => cluster ω v) (fun w => measurableSet_conn v w) hh hp

/-- Under the three-layer law, the first-layer cluster of `v` contains a mark with
probability equal to its ghost transform under `law q₀`. -/
theorem prodBernoulli_three_first_cluster [Countable V] (q₀ s : Sym2 V → I) (v : V)
    (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h)) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
        {η | (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) v ∩ Sum.inr ⁻¹' η).Nonempty} =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
        ∂(law q₀) := by
  have := prodBernoulli_map_preimage_inl q₀ s
  rw [law, ← this]
  exact prodBernoulli_sum_inter_nonempty (Sum.elim q₀ s) measurable_preimage_inl
    (L := fun ω => cluster ω v) (fun w => measurableSet_conn v w) hh hp

end Marks

/-! ### Non-vacuity -/

/-- `e^{-h}` is the complement of a mark probability for every `h ≥ 0`. -/
example (h : ℝ) (hh : 0 ≤ h) : ∃ p : I, ((σ p : I) : ℝ) = Real.exp (-h) :=
  ⟨σ ⟨Real.exp (-h), (Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩, by simp⟩

/-- With `h = log 2`, a single vertex contains a mark with probability `1/2`. -/
example : prodBernoulli (fun _ : Unit => (σ ⟨1 / 2, by norm_num, by norm_num⟩ : I))
    {g | ({()} ∩ g).Nonempty} = 1 - EReal.exp (-((Real.log 2 : EReal) *
      ((({()} : Set Unit).encard : ℝ≥0∞) : EReal))) :=
  prodBernoulli_inter_nonempty (Real.log_pos (by norm_num))
    (by simp [Real.exp_neg, Real.exp_log]) _

end PercLib.Percolation.Bond

end
