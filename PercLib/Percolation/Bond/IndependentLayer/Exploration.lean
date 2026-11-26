/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.Ghost
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Probability.OpenEventHarris

/-!
# Exploring a union cluster from a first-layer cluster

Let `ω₁`, `ω₂` be two configurations and `C = K_o(ω₁)` the first-layer cluster of `o`.

1. **Exploration inclusion** (`cluster_union_subset`). Every vertex of the union cluster
   `K_o(ω₁ ∪ ω₂)` is in `C` or in the cluster of some `v ∉ C`, joined to some `u ∈ C` by a
   second-layer pair `s(u, v) ∈ ω₂`. That cluster is taken in `(ω₁ ∪ ω₂)` with every pair
   meeting `C` removed, and it avoids `C` (`cluster_inter_avoid_subset`).
2. **Factorisation** (`prodBernoulli_three_explore_eq`). Under the three-layer law of
   `Ghost.lean`, fix a finite `C ∋ o`, `u ∈ C` and `v ∉ C`. The four events
   * `K_o(ω₁) = C`,
   * `C` has no mark,
   * `s(u, v) ∈ ω₂`,
   * the cluster of `v` off `C` contains a mark,

   depend on disjoint sets of coordinates, so their joint probability is the product.
   The last factor is at most the ghost transform `G_v(h)` of the union law
   (`prodBernoulli_three_avoid_le`).

This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The exploration inclusion -/

/-- Removing every pair that meets `C`, the cluster of a vertex outside `C` avoids `C`. -/
theorem cluster_inter_avoid_subset (ω : Config V) (C : Set V) {v : V} (hv : v ∉ C) :
    cluster (ω ∩ {e | ∀ x ∈ e, x ∉ C}) v ⊆ Cᶜ := by
  intro y hy
  change (openGraph _).Reachable v y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact hv
  | @tail b c _ hbc _ =>
    rw [openGraph_adj_iff] at hbc
    exact hbc.1.2 c (Sym2.mem_mk_right b c)

/-- **Exploration inclusion.** The union cluster of `o` lies in the first-layer cluster `C`
together with the clusters off `C` of the vertices `v ∉ C` reached from `C` by a
second-layer pair. -/
theorem cluster_union_subset (ω₁ ω₂ : Config V) (o : V) :
    cluster (ω₁ ∪ ω₂) o ⊆ cluster ω₁ o ∪ ⋃ u ∈ cluster ω₁ o, ⋃ v ∈ (cluster ω₁ o)ᶜ,
      ⋃ (_ : s(u, v) ∈ ω₂), cluster ((ω₁ ∪ ω₂) ∩ {e | ∀ x ∈ e, x ∉ cluster ω₁ o}) v := by
  set C := cluster ω₁ o with hC
  intro y hy
  change (openGraph _).Reachable o y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact Or.inl (mem_cluster_self ω₁ o)
  | @tail b c _ hbc ih =>
    rw [openGraph_adj_iff] at hbc
    obtain ⟨hbc, hne⟩ := hbc
    by_cases hc : c ∈ C
    · exact Or.inl hc
    by_cases hb : b ∈ C
    · have h2 : s(b, c) ∈ ω₂ := by
        rcases hbc with h1 | h2
        · exact absurd ((show (openGraph ω₁).Reachable o b from hb).trans
            (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω₁ b c).2 ⟨h1, hne⟩))) hc
        · exact h2
      exact Or.inr (mem_iUnion₂.2 ⟨b, hb, mem_iUnion₂.2 ⟨c, hc,
        mem_iUnion.2 ⟨h2, mem_cluster_self _ c⟩⟩⟩)
    · rcases ih with h | h
      · exact absurd h hb
      obtain ⟨u, hu, h⟩ := mem_iUnion₂.1 h
      obtain ⟨v, hv, h⟩ := mem_iUnion₂.1 h
      obtain ⟨huv, h⟩ := mem_iUnion.1 h
      refine Or.inr (mem_iUnion₂.2 ⟨u, hu, mem_iUnion₂.2 ⟨v, hv, mem_iUnion.2 ⟨huv, ?_⟩⟩⟩)
      have hadj : (openGraph ((ω₁ ∪ ω₂) ∩ {e | ∀ x ∈ e, x ∉ C})).Adj b c := by
        rw [openGraph_adj_iff]
        refine ⟨⟨hbc, fun x hx => ?_⟩, hne⟩
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact hb
        · exact hc
      exact (show (openGraph _).Reachable v b from h).trans hadj.reachable

/-! ### Determined events -/

section Determined

variable {ι : Type*}

theorem mem_iff_of_inter_eq {η η' P : Set ι} (h : η ∩ P = η' ∩ P) {i : ι} (hi : i ∈ P) :
    i ∈ η ↔ i ∈ η' := by
  have := congrArg (i ∈ ·) h
  simpa [hi] using this

/-- An intersection of an event determined by `P` and one determined by `Q` is determined
by `P ∪ Q`. -/
theorem determined_inter {P Q : Set ι} {A B : Set (Set ι)}
    (hA : ∀ ω ω', ω ∩ P = ω' ∩ P → (ω ∈ A ↔ ω' ∈ A))
    (hB : ∀ ω ω', ω ∩ Q = ω' ∩ Q → (ω ∈ B ↔ ω' ∈ B)) :
    ∀ ω ω', ω ∩ (P ∪ Q) = ω' ∩ (P ∪ Q) → (ω ∈ A ∩ B ↔ ω' ∈ A ∩ B) := by
  intro ω ω' h
  have hP : ω ∩ P = ω' ∩ P := by
    have := congrArg (· ∩ P) h
    simpa only [inter_assoc, inter_eq_right.2 subset_union_left] using this
  have hQ : ω ∩ Q = ω' ∩ Q := by
    have := congrArg (· ∩ Q) h
    simpa only [inter_assoc, inter_eq_right.2 subset_union_right] using this
  exact and_congr (hA _ _ hP) (hB _ _ hQ)

end Determined

/-! ### Three layers: marginals -/

section Three

variable (q₀ s : Sym2 V → I) (p : I)

theorem measurable_three_first :
    Measurable fun η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) => (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) :=
  measurable_preimage_inl.comp measurable_preimage_inl

theorem measurable_three_second :
    Measurable fun η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) => (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V) :=
  measurable_preimage_inr.comp measurable_preimage_inl

/-- The first layer has law `law q₀`. -/
theorem prodBernoulli_three_map_first :
    (prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)).map
        (fun η => (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V)) = law q₀ := by
  have h1 := measurable_preimage_inl (α := Sym2 V ⊕ Sym2 V) (β := V)
  have h2 := measurable_preimage_inl (α := Sym2 V) (β := Sym2 V)
  rw [show (fun η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) => (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V)) =
      (fun E => (Sum.inl ⁻¹' E : Config V)) ∘ (fun η => Sum.inl ⁻¹' η) from rfl,
    ← Measure.map_map h2 h1, prodBernoulli_map_preimage_inl, prodBernoulli_map_preimage_inl]
  rfl

/-- A second-layer pair is open with probability `s e`. -/
theorem prodBernoulli_three_second_mem (e : Sym2 V) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
        {η | e ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)} =
      (unitInterval.toNNReal (s e) : ℝ≥0∞) := by
  have : {η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) | e ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)} =
      {η | (({Sum.inl (Sum.inr e)} : Finset ((Sym2 V ⊕ Sym2 V) ⊕ V)) : Set _) ⊆ η} := by
    ext η
    simp
  rw [this, prodBernoulli_subset, Finset.prod_singleton]
  rfl

/-- A set contains no mark with probability `e^{-h|C|}`. -/
theorem prodBernoulli_three_marks_eq_empty [Countable V] {h : ℝ} (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) (A : Set V) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p) {η | A ∩ Sum.inr ⁻¹' η = ∅} =
      EReal.exp (-((h : EReal) * ((A.encard : ℝ≥0∞) : EReal))) := by
  rw [← prodBernoulli_inter_eq_empty hh hp A,
    ← prodBernoulli_map_preimage_inr (Sum.elim q₀ s) (fun _ : V => p),
    Measure.map_apply measurable_preimage_inr]
  · rfl
  · have := (measurableSet_inter_nonempty (V := V) A).compl
    convert this using 1
    ext g
    simp [nonempty_iff_ne_empty]

/-! ### Three layers: the four exploration events -/

/-- **Factorisation.** For a finite `C ∋ o`, `u ∈ C` and `v ∉ C`, the events `K_o(ω₁) = C`,
`C ∩ marks = ∅`, `s(u, v) ∈ ω₂` and "the cluster of `v` in `(ω₁ ∪ ω₂)` off `C` contains a
mark" are independent. -/
theorem prodBernoulli_three_explore_eq [Countable V] {h : ℝ} (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) (o : V) (C : Finset V) (ho : o ∈ C) {u v : V}
    (hu : u ∈ C) (hv : v ∉ C) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
        ({η | cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o = C} ∩
          {η | (C : Set V) ∩ Sum.inr ⁻¹' η = ∅} ∩
          {η | s(u, v) ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)} ∩
          {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
            {e | ∀ x ∈ e, x ∉ (C : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty}) =
      law q₀ {ω | cluster ω o = C} *
        EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))) *
        (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) *
        prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
          {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
            {e | ∀ x ∈ e, x ∉ (C : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty} := by
  classical
  set out : Set (Sym2 V) := {e | ∀ x ∈ e, x ∉ (C : Set V)} with hout
  set M : Set (Sym2 V) := {e | ∃ x ∈ e, x ∈ C} with hM
  set P1 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) := Sum.inl '' (Sum.inl '' M)
  set P2 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) := Sum.inr '' (C : Set V)
  set P3 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) := {Sum.inl (Sum.inr s(u, v))}
  set P4 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) :=
    Sum.inl '' (Sum.inl '' out ∪ Sum.inr '' out) ∪ Sum.inr '' (C : Set V)ᶜ
  set A1 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) := {η | cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o = C}
  set A2 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) := {η | (C : Set V) ∩ Sum.inr ⁻¹' η = ∅}
  set A3 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    {η | s(u, v) ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)}
  set A4 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩ out) v ∩
      Sum.inr ⁻¹' η).Nonempty}
  -- measurability
  have hm1 : MeasurableSet A1 :=
    measurable_three_first (measurableSet_cluster_eq_finset o C ho)
  have hm2 : MeasurableSet A2 := by
    have hg : MeasurableSet {g : Set V | (C : Set V) ∩ g = ∅} := by
      convert (measurableSet_inter_nonempty (V := V) (C : Set V)).compl using 1
      ext g
      simp [nonempty_iff_ne_empty]
    exact measurable_preimage_inr (α := Sym2 V ⊕ Sym2 V) hg
  have hm3 : MeasurableSet A3 := measurable_three_second (measurableSet_mem s(u, v))
  have hm4 : MeasurableSet A4 := by
    have hW : Measurable fun η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) =>
        (((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩ out : Config V),
          (Sum.inr ⁻¹' η : Set V)) := by
      refine Measurable.prodMk (Measurable.of_mem fun e => ?_) measurable_preimage_inr
      exact ((measurable_set_mem (Sum.inl (Sum.inl e))).or
        (measurable_set_mem (Sum.inl (Sum.inr e)))).and measurable_const
    exact hW (measurableSet_prod_inter_nonempty (K := fun ω : Config V => cluster ω v)
      fun w => measurableSet_conn v w)
  -- determinedness
  have hd1 : ∀ η η' : Set ((Sym2 V ⊕ Sym2 V) ⊕ V), η ∩ P1 = η' ∩ P1 → (η ∈ A1 ↔ η' ∈ A1) := by
    intro η η' hη
    have hagree : (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) ∩ M =
        (Sum.inl ⁻¹' (Sum.inl ⁻¹' η') : Config V) ∩ M := by
      ext e
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_left fun he => mem_iff_of_inter_eq hη ⟨Sum.inl e, ⟨e, he, rfl⟩, rfl⟩
    have e1 := cluster_eq_finset_determined o C ho (Sum.inl ⁻¹' (Sum.inl ⁻¹' η))
    have e2 := cluster_eq_finset_determined o C ho (Sum.inl ⁻¹' (Sum.inl ⁻¹' η'))
    simp only [mem_ofPred_eq] at e1 e2
    change cluster _ o = (C : Set V) ↔ cluster _ o = (C : Set V)
    rw [e1, e2, hagree]
  have hd2 : ∀ η η' : Set ((Sym2 V ⊕ Sym2 V) ⊕ V), η ∩ P2 = η' ∩ P2 → (η ∈ A2 ↔ η' ∈ A2) := by
    intro η η' hη
    have : (C : Set V) ∩ Sum.inr ⁻¹' η = (C : Set V) ∩ Sum.inr ⁻¹' η' := by
      ext x
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_right fun hx => mem_iff_of_inter_eq hη ⟨x, hx, rfl⟩
    simp only [A2, mem_ofPred_eq, this]
  have hd3 : ∀ η η' : Set ((Sym2 V ⊕ Sym2 V) ⊕ V), η ∩ P3 = η' ∩ P3 → (η ∈ A3 ↔ η' ∈ A3) :=
    fun η η' hη => mem_iff_of_inter_eq hη rfl
  have hd4 : ∀ η η' : Set ((Sym2 V ⊕ Sym2 V) ⊕ V), η ∩ P4 = η' ∩ P4 → (η ∈ A4 ↔ η' ∈ A4) := by
    intro η η' hη
    have hW : ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩ out : Config V) =
        (Sum.inl ⁻¹' (Sum.inl ⁻¹' η') ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η')) ∩ out := by
      ext e
      simp only [mem_inter_iff, mem_union, mem_preimage]
      refine and_congr_left fun he => or_congr ?_ ?_
      · exact mem_iff_of_inter_eq hη (Or.inl ⟨Sum.inl e, Or.inl ⟨e, he, rfl⟩, rfl⟩)
      · exact mem_iff_of_inter_eq hη (Or.inl ⟨Sum.inr e, Or.inr ⟨e, he, rfl⟩, rfl⟩)
    have hK := cluster_inter_avoid_subset
      ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η') ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η') : Config V)) (C : Set V)
      (v := v) (by simpa using hv)
    simp only [A4, mem_ofPred_eq, hW]
    have : cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η') ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η')) ∩ out) v ∩
          Sum.inr ⁻¹' η =
        cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η') ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η')) ∩ out) v ∩
          Sum.inr ⁻¹' η' := by
      ext y
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_right fun hy => mem_iff_of_inter_eq hη (Or.inr ⟨y, hK hy, rfl⟩)
    rw [this]
  -- disjointness
  have hdis12 : Disjoint P1 P2 := by
    refine Set.disjoint_left.2 fun i hi h2 => ?_
    rcases i with (e | e) | x <;> simp [P1, P2] at hi h2
  have hdis123 : Disjoint (P1 ∪ P2) P3 := by
    refine Set.disjoint_left.2 fun i hi h3 => ?_
    rcases i with (e | e) | x <;> simp [P1, P2, P3] at hi h3
  have hdis4 : Disjoint (P1 ∪ P2 ∪ P3) P4 := by
    refine Set.disjoint_left.2 fun i hi h4 => ?_
    rcases i with (e | e) | x <;> simp only [hM, union_singleton, mem_insert_iff, Sum.inl.injEq,
        reduceCtorEq, mem_union, mem_image, mem_ofPred_eq, exists_eq_right, SetLike.mem_coe,
        and_false, exists_false, or_false, false_or, hout, mem_compl_iff, P1, P2, P3, P4,
        Sum.inr.injEq, or_self] at hi h4
    · obtain ⟨x, hx, hxC⟩ := hi
      exact h4 x hx hxC
    · subst hi
      exact h4 u (Sym2.mem_mk_left u v) hu
    · exact h4 hi
  rw [prodBernoulli_inter_of_determined _ hdis4 ((hm1.inter hm2).inter hm3) hm4
      (determined_inter (determined_inter hd1 hd2) hd3) hd4,
    prodBernoulli_inter_of_determined _ hdis123 (hm1.inter hm2) hm3 (determined_inter hd1 hd2) hd3,
    prodBernoulli_inter_of_determined _ hdis12 hm1 hm2 hd1 hd2,
    prodBernoulli_three_marks_eq_empty q₀ s p hh hp, prodBernoulli_three_second_mem,
    ← prodBernoulli_three_map_first q₀ s p, Measure.map_apply (measurable_three_first)
      (measurableSet_cluster_eq_finset o C ho)]
  rfl

/-- The cluster of `v` off `C` contains a mark with probability at most the ghost transform
of the union cluster of `v`. -/
theorem prodBernoulli_three_avoid_le [Countable V] {h : ℝ} (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) (C : Set V) (v : V) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
        {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
          {e | ∀ x ∈ e, x ∉ C}) v ∩ Sum.inr ⁻¹' η).Nonempty} ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) := by
  rw [← prodBernoulli_three_union_cluster q₀ s v hh hp]
  exact measure_mono fun η hη => hη.mono (inter_subset_inter_left _
    (cluster_mono inter_subset_left v))

end Three

/-! ### Summing over the values of a finite cluster -/

/-- `{K_o = C}` is measurable for every finite `C`; it is empty when `o ∉ C`. -/
theorem measurableSet_cluster_eq_finset' [Countable V] (o : V) (C : Finset V) :
    MeasurableSet {ω : Config V | cluster ω o = C} := by
  by_cases ho : o ∈ C
  · exact measurableSet_cluster_eq_finset o C ho
  · convert MeasurableSet.empty
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h
    have := mem_cluster_self ω o
    rw [h] at this
    exact ho (by exact_mod_cast this)

/-- **Decomposition over finite cluster values.** For every `F : ℕ∞ → ℝ≥0∞`,
`∑_C P(K_o = C) F(|C|) ≤ E[F(|K_o|)]`, the sum over finite sets `C`. -/
theorem tsum_law_cluster_eq_finset_mul_le [Countable V] (q : Sym2 V → I) (o : V)
    (F : ℕ∞ → ℝ≥0∞) :
    ∑' C : Finset V, law q {ω | cluster ω o = C} * F ((C : Set V).encard) ≤
      ∫⁻ ω, F (cluster ω o).encard ∂(law q) := by
  classical
  have hpt : ∀ ω : Config V, ∑' C : Finset V,
      {ω' : Config V | cluster ω' o = C}.indicator (fun _ => F ((C : Set V).encard)) ω ≤
        F (cluster ω o).encard := by
    intro ω
    rcases (cluster ω o).finite_or_infinite with hK | hK
    · rw [tsum_eq_single hK.toFinset]
      · simp [indicator]
      · intro C hC
        simp only [indicator, mem_ofPred_eq, ite_eq_right_iff]
        intro h
        exact absurd (Finset.coe_injective (by simp [h])) hC
    · rw [ENNReal.tsum_eq_zero.2 fun C => ?_]
      · exact zero_le
      simp only [indicator, mem_ofPred_eq, ite_eq_right_iff]
      intro h
      exact absurd (h ▸ C.finite_toSet) hK
  calc ∑' C : Finset V, law q {ω | cluster ω o = C} * F ((C : Set V).encard)
      = ∑' C : Finset V, ∫⁻ ω, {ω' : Config V | cluster ω' o = C}.indicator
          (fun _ => F ((C : Set V).encard)) ω ∂(law q) := by
        refine tsum_congr fun C => ?_
        rw [lintegral_indicator_const (measurableSet_cluster_eq_finset' o C), mul_comm]
    _ = ∫⁻ ω, ∑' C : Finset V, {ω' : Config V | cluster ω' o = C}.indicator
          (fun _ => F ((C : Set V).encard)) ω ∂(law q) :=
        (lintegral_tsum fun C =>
          (measurable_const.indicator (measurableSet_cluster_eq_finset' o C)).aemeasurable).symm
    _ ≤ ∫⁻ ω, F (cluster ω o).encard ∂(law q) := lintegral_mono hpt

end PercLib.Percolation.Bond

end
