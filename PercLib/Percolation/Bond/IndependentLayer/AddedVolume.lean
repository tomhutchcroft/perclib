/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer

/-!
# The volume added by an independent layer, given the original cluster (AYPN)

Let `ω ~ law q₀` and `ξ ~ law s` be independent, `C = K_o(ω)`, `K⁺ = K_o(ω ∪ ξ)` and
`D = K⁺ \ C`, the vertices added by the second layer. With `a` a bound on the off-diagonal
row sums of `s` and `M*(h) = ⨆ v, E_r[1 - e^{-h|K_v|}]` the largest ghost transform of the
union law `r`:

* `lintegral_ghost_added_mul_le` (**AYPN**): if `C` is finite almost surely, then for every
  measurable functional `f ≥ 0` of the original cluster,
  `E[(1 - e^{-h|D|}) f(C)] ≤ E[min(1, a M*(h) |C|) f(C)]`
  (the conditional form `E[1 - e^{-h|D|} | C] ≤ min(1, a M*(h)|C|)`, stated without
  conditional expectations).
* `law_added_volume_ge_mul_le`: `(1 - e^{-ht}) P(|D| ≥ t) ≤ E[min(1, a M*(h)|C|)]`.

The proof marks vertices independently with probability `1 - e^{-h}` and explores `K⁺` from
`C` (`Exploration.lean`): a mark in `D` lies in the cluster off `C` of some `v ∉ C` joined to
some `u ∈ C` by a second-layer pair, and the three events `K_o(ω) = C`, `s(u, v) ∈ ξ` and
"the cluster of `v` off `C` contains a mark" are independent
(`prodBernoulli_three_explore_added_eq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Three events of the exploration -/

section Three

variable (q₀ s : Sym2 V → I) (p : I)

/-- **Factorisation without the marks of `C`.** For a finite `C ∋ o`, `u ∈ C` and `v ∉ C`,
the events `K_o(ω₁) = C`, `s(u, v) ∈ ω₂` and "the cluster of `v` in `ω₁ ∪ ω₂` off `C` contains
a mark" are independent. -/
theorem prodBernoulli_three_explore_added_eq [Countable V] (o : V) (C : Finset V) (ho : o ∈ C)
    {u v : V} (hu : u ∈ C) (hv : v ∉ C) :
    prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
        ({η | cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o = C} ∩
          {η | s(u, v) ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)} ∩
          {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
            {e | ∀ x ∈ e, x ∉ (C : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty}) =
      law q₀ {ω | cluster ω o = C} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) *
        prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p)
          {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
            {e | ∀ x ∈ e, x ∉ (C : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty} := by
  classical
  set out : Set (Sym2 V) := {e | ∀ x ∈ e, x ∉ (C : Set V)} with hout
  set M : Set (Sym2 V) := {e | ∃ x ∈ e, x ∈ C} with hM
  set P1 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) := Sum.inl '' (Sum.inl '' M)
  set P3 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) := {Sum.inl (Sum.inr s(u, v))}
  set P4 : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) :=
    Sum.inl '' (Sum.inl '' out ∪ Sum.inr '' out) ∪ Sum.inr '' (C : Set V)ᶜ
  set A1 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) := {η | cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o = C}
  set A3 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    {η | s(u, v) ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)}
  set A4 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩ out) v ∩
      Sum.inr ⁻¹' η).Nonempty}
  have hm1 : MeasurableSet A1 :=
    measurable_three_first (measurableSet_cluster_eq_finset o C ho)
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
  have hdis13 : Disjoint P1 P3 := by
    refine Set.disjoint_left.2 fun i hi h3 => ?_
    rcases i with (e | e) | x <;> simp [P1, P3] at hi h3
  have hdis4 : Disjoint (P1 ∪ P3) P4 := by
    refine Set.disjoint_left.2 fun i hi h4 => ?_
    rcases i with (e | e) | x <;> simp only [hM, union_singleton, mem_insert_iff, Sum.inl.injEq,
        reduceCtorEq, mem_image, mem_ofPred_eq, exists_eq_right, false_or, hout, SetLike.mem_coe,
        mem_union, and_false, exists_false, or_false, mem_compl_iff, P1, P3, P4, Sum.inr.injEq,
        or_self] at hi h4
    · obtain ⟨x, hx, hxC⟩ := hi
      exact h4 x hx hxC
    · subst hi
      exact h4 u (Sym2.mem_mk_left u v) hu
  rw [prodBernoulli_inter_of_determined _ hdis4 (hm1.inter hm3) hm4
      (determined_inter hd1 hd3) hd4,
    prodBernoulli_inter_of_determined _ hdis13 hm1 hm3 hd1 hd3,
    prodBernoulli_three_second_mem, ← prodBernoulli_three_map_first q₀ s p,
    Measure.map_apply (measurable_three_first) (measurableSet_cluster_eq_finset o C ho)]
  rfl

end Three

/-! ### Summing over the values of a finite cluster -/

/-- **Decomposition over finite cluster values.** For every `G : Set V → ℝ≥0∞`,
`∑_C P(K_o = C) G(C) ≤ E[G(K_o)]`, the sum over finite sets `C`. -/
theorem tsum_law_cluster_eq_finset_mul_le_set [Countable V] (q : Sym2 V → I) (o : V)
    (G : Set V → ℝ≥0∞) :
    ∑' C : Finset V, law q {ω | cluster ω o = C} * G C ≤ ∫⁻ ω, G (cluster ω o) ∂(law q) := by
  classical
  have hpt : ∀ ω : Config V, ∑' C : Finset V,
      {ω' : Config V | cluster ω' o = C}.indicator (fun _ => G C) ω ≤ G (cluster ω o) := by
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
  calc ∑' C : Finset V, law q {ω | cluster ω o = C} * G C
      = ∑' C : Finset V, ∫⁻ ω, {ω' : Config V | cluster ω' o = C}.indicator
          (fun _ => G C) ω ∂(law q) := by
        refine tsum_congr fun C => ?_
        rw [lintegral_indicator_const (measurableSet_cluster_eq_finset' o C), mul_comm]
    _ = ∫⁻ ω, ∑' C : Finset V, {ω' : Config V | cluster ω' o = C}.indicator
          (fun _ => G C) ω ∂(law q) :=
        (lintegral_tsum fun C =>
          (measurable_const.indicator (measurableSet_cluster_eq_finset' o C)).aemeasurable).symm
    _ ≤ ∫⁻ ω, G (cluster ω o) ∂(law q) := lintegral_mono hpt

/-! ### AYPN -/

/-- Membership in the added set `K_o(ω ∪ ξ) \ K_o(ω)` is measurable. -/
theorem measurableSet_mem_added [Countable V] (o v : V) :
    MeasurableSet {x : Config V × Config V | v ∈ cluster (x.1 ∪ x.2) o \ cluster x.1 o} := by
  have hu : Measurable fun x : Config V × Config V => x.1 ∪ x.2 :=
    Measurable.of_mem fun e => ((measurable_set_mem e).comp measurable_fst).or
      ((measurable_set_mem e).comp measurable_snd)
  exact (hu (measurableSet_conn o v)).diff (measurable_fst (measurableSet_conn o v))

open Classical in
/-- The off-diagonal row sums of `s` from a finite set `C` to its complement. -/
theorem tsum_tsum_ite_mem_not_mem_le (s : Sym2 V → I) (C : Finset V) {a : ℝ≥0∞}
    (ha : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ a) :
    ∑' u, ∑' v,
      (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) ≤
        (C.card : ℝ≥0∞) * a := by
  classical
  calc ∑' u, ∑' v, (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0)
      ≤ ∑' u, (if u ∈ C then a else 0) := by
        refine ENNReal.tsum_le_tsum fun u => ?_
        by_cases hu : u ∈ C
        · simp only [hu, true_and, ite_true]
          exact (tsum_ite_not_mem_le s C hu).trans (ha u)
        · simp [hu]
    _ = ∑ u ∈ C, a := by
        rw [tsum_eq_sum (s := C) fun u hu => by simp [hu]]
        exact Finset.sum_congr rfl fun u hu => by simp [hu]
    _ = (C.card : ℝ≥0∞) * a := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Ghost bound for the added mass.** Let `ω ~ law q₀` and `ξ ~ law s` be independent,
`C = K_o(ω)` finite almost surely, `D = K_o(ω ∪ ξ) \ C`, `a` a bound on the off-diagonal row sums of
`s` and `M*(h) = ⨆ v, E_r[1 - e^{-h|K_v|}]` for the union law `r`. Then for every measurable
functional `f ≥ 0` of the original cluster, `E[(1 - e^{-h|D|}) f(C)] ≤ E[min(1, a M*(h) |C|) f(C)]`.
-/
theorem lintegral_ghost_added_mul_le [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) (hfin : ∀ᵐ ω ∂(law q₀), (cluster ω o).Finite) {a : ℝ≥0∞}
    (ha : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ a)
    (f : Set V → ℝ≥0∞) (hf : Measurable fun ω : Config V => f (cluster ω o)) :
    ∫⁻ x, (1 - EReal.exp (-((h : EReal) *
        (((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞) : EReal)))) *
        f (cluster x.1 o) ∂((law q₀).prod (law s)) ≤
      ∫⁻ ω, min 1 (a * (⨆ v, ∫⁻ ω', (1 - EReal.exp (-((h : EReal) *
          (((cluster ω' v).encard : ℝ≥0∞) : EReal)))) ∂(law fun e => σ (σ (q₀ e) * σ (s e)))) *
          (cluster ω o).encard) * f (cluster ω o) ∂(law q₀) := by
  classical
  obtain ⟨p, hp⟩ := exists_symm_eq_exp hh.le
  set Mx := ⨆ v, ∫⁻ ω', (1 - EReal.exp (-((h : EReal) *
      (((cluster ω' v).encard : ℝ≥0∞) : EReal)))) ∂(law fun e => σ (σ (q₀ e) * σ (s e)))
    with hMx
  set Pm := prodBernoulli (fun _ : V => p) with hPm
  set P3 := prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p) with hP3
  set D : Config V × Config V → Set V := fun x => cluster (x.1 ∪ x.2) o \ cluster x.1 o
    with hD
  set Sd := {z : (Config V × Config V) × Set V | (D z.1 ∩ z.2).Nonempty} with hSd_def
  have hSd : MeasurableSet Sd := measurableSet_prod_inter_nonempty (measurableSet_mem_added o)
  set Ψ : (Config V × Config V) × Set V → ℝ≥0∞ :=
    fun z => Sd.indicator (fun z => f (cluster z.1.1 o)) z with hΨ_def
  have hfm : Measurable fun z : (Config V × Config V) × Set V => f (cluster z.1.1 o) :=
    hf.comp (measurable_fst.comp measurable_fst)
  have hΨ : Measurable Ψ := hfm.indicator hSd
  -- the ghost transform of `D` is the probability that `D` contains a mark
  have hAB : ∫⁻ x, (1 - EReal.exp (-((h : EReal) *
        (((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞) : EReal)))) *
        f (cluster x.1 o) ∂((law q₀).prod (law s)) =
      ∫⁻ z, Ψ z ∂(((law q₀).prod (law s)).prod Pm) := by
    rw [lintegral_prod _ hΨ.aemeasurable]
    refine lintegral_congr fun x => ?_
    have hsec : (fun g => Ψ (x, g)) =
        {g : Set V | (D x ∩ g).Nonempty}.indicator (fun _ => f (cluster x.1 o)) := by
      funext g
      simp only [hΨ_def, hSd_def, indicator, mem_ofPred_eq]
    rw [hsec, lintegral_indicator_const (measurableSet_inter_nonempty (D x)),
      prodBernoulli_inter_nonempty hh hp, mul_comm]
  -- transfer to the three-layer law
  set split : Set (Sym2 V ⊕ Sym2 V) → Config V × Config V :=
    fun E => ((Sum.inl ⁻¹' E : Config V), (Sum.inr ⁻¹' E : Config V)) with hsplit_def
  have hsplit : Measurable split := measurable_preimage_inl.prodMk measurable_preimage_inr
  set first : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) → Set (Sym2 V ⊕ Sym2 V) × Set V :=
    fun η => ((Sum.inl ⁻¹' η : Set (Sym2 V ⊕ Sym2 V)), (Sum.inr ⁻¹' η : Set V)) with hfirst_def
  have hfirst : Measurable first := measurable_preimage_inl.prodMk measurable_preimage_inr
  have hΘ : Measurable (Prod.map split id ∘ first) := (hsplit.prodMap measurable_id).comp hfirst
  have hmap : P3.map (Prod.map split id ∘ first) = ((law q₀).prod (law s)).prod Pm := by
    have h1 := prodBernoulli_sum_map_prod (Sum.elim q₀ s) (fun _ : V => p)
    have h2 := prodBernoulli_sum_map_prod q₀ s
    rw [← Measure.map_map (hsplit.prodMap measurable_id) hfirst, h1,
      ← Measure.map_prod_map _ _ hsplit measurable_id, Measure.map_id, h2]
    rfl
  rw [hAB, ← hmap, lintegral_map hΨ hΘ]
  -- the events of the three-layer law
  set A1 : Finset V → Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    fun S => {η | cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o = S} with hA1_def
  set E := (Prod.map split id ∘ first) ⁻¹' Sd with hE_def
  have hEm : MeasurableSet E := hΘ hSd
  have hA1m : ∀ S, MeasurableSet (A1 S) := fun S =>
    measurable_three_first (measurableSet_cluster_eq_finset' o S)
  -- the first-layer cluster is finite almost surely
  have hfin3 : ∀ᵐ η ∂P3, (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o).Finite := by
    have hm := prodBernoulli_three_map_first q₀ s p
    rw [← hm] at hfin
    exact ae_of_ae_map (measurable_three_first).aemeasurable hfin
  -- decomposition over the value of the first-layer cluster
  have hpt : ∀ᵐ η ∂P3, Ψ ((Prod.map split id ∘ first) η) ≤
      ∑' S : Finset V, (A1 S ∩ E).indicator (fun _ => f S) η := by
    filter_upwards [hfin3] with η hη
    by_cases hηE : η ∈ E
    · refine le_trans (le_of_eq ?_) (ENNReal.le_tsum hη.toFinset)
      have hc : cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o = (hη.toFinset : Set V) := by
        simp
      have hmem : η ∈ A1 hη.toFinset ∩ E := ⟨hc, hηE⟩
      rw [indicator_of_mem hmem]
      simp only [hΨ_def]
      rw [indicator_of_mem (show (Prod.map split id ∘ first) η ∈ Sd from hηE)]
      change f (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o) = _
      exact congrArg f hc
    · simp only [hΨ_def]
      rw [indicator_of_notMem (show (Prod.map split id ∘ first) η ∉ Sd from hηE)]
      exact zero_le
  -- each value of the cluster
  have hS : ∀ S : Finset V, P3 (A1 S ∩ E) ≤
      law q₀ {ω | cluster ω o = S} * min 1 (a * Mx * ((S : Set V).encard)) := by
    intro S
    by_cases ho : o ∈ S
    swap
    · have hempty : A1 S = ∅ := by
        ext η
        simp only [hA1_def, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hc
        have := mem_cluster_self (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o
        rw [hc] at this
        exact ho (by exact_mod_cast this)
      rw [hempty, empty_inter, measure_empty]
      exact zero_le
    have hfirst_law : P3 (A1 S) = law q₀ {ω | cluster ω o = S} := by
      rw [← prodBernoulli_three_map_first q₀ s p,
        Measure.map_apply measurable_three_first (measurableSet_cluster_eq_finset' o S)]
      rfl
    -- the bound by the first factor
    have hle1 : P3 (A1 S ∩ E) ≤ law q₀ {ω | cluster ω o = S} :=
      (measure_mono inter_subset_left).trans hfirst_law.le
    -- the bound by the exploration
    set T : V → V → Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) := fun u v =>
      ⋃ (_ : u ∈ S ∧ v ∉ S),
        A1 S ∩ {η | s(u, v) ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)} ∩
          {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
            {e | ∀ x ∈ e, x ∉ (S : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty} with hT
    have hsubT : A1 S ∩ E ⊆ ⋃ u, ⋃ v, T u v := by
      rintro η ⟨hc, y, ⟨hyK, hyC⟩, hym⟩
      simp only [hA1_def, mem_ofPred_eq] at hc
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id, hsplit_def,
        hfirst_def] at hyK hyC hym
      rcases cluster_union_subset _ _ o hyK with hy | hy
      · exact absurd hy hyC
      obtain ⟨u, hu, hy⟩ := mem_iUnion₂.1 hy
      obtain ⟨v, hv, hy⟩ := mem_iUnion₂.1 hy
      obtain ⟨huv, hy⟩ := mem_iUnion.1 hy
      rw [hc] at hu hv hy
      refine mem_iUnion.2 ⟨u, mem_iUnion.2 ⟨v, mem_iUnion.2
        ⟨⟨by exact_mod_cast hu, by exact_mod_cast hv⟩, ⟨⟨hc, huv⟩, ⟨y, hy, hym⟩⟩⟩⟩⟩
    have hTle : ∀ u v, P3 (T u v) ≤ law q₀ {ω | cluster ω o = S} * Mx *
        (if u ∈ S ∧ v ∉ S then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) := by
      intro u v
      by_cases hc : u ∈ S ∧ v ∉ S
      · simp only [hT, hc, not_false_eq_true, and_self, iUnion_true, ite_true]
        rw [prodBernoulli_three_explore_added_eq q₀ s p o S ho hc.1 hc.2]
        calc law q₀ {ω | cluster ω o = S} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) *
              P3 {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
                {e | ∀ x ∈ e, x ∉ (S : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty}
            ≤ law q₀ {ω | cluster ω o = S} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) * Mx := by
              gcongr
              exact (prodBernoulli_three_avoid_le q₀ s p hh hp _ v).trans
                (le_iSup (fun v => ∫⁻ ω', (1 - EReal.exp (-((h : EReal) *
                  (((cluster ω' v).encard : ℝ≥0∞) : EReal))))
                  ∂(law fun e => σ (σ (q₀ e) * σ (s e)))) v)
          _ = _ := by ring
      · simp only [hT, hc, iUnion_false, measure_empty, ite_false, mul_zero]
        exact le_rfl
    have hle2 : P3 (A1 S ∩ E) ≤ law q₀ {ω | cluster ω o = S} * (a * Mx * ((S : Set V).encard)) := by
      calc P3 (A1 S ∩ E) ≤ P3 (⋃ u, ⋃ v, T u v) := measure_mono hsubT
        _ ≤ ∑' u, ∑' v, P3 (T u v) :=
            (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun u => measure_iUnion_le _)
        _ ≤ ∑' u, ∑' v, law q₀ {ω | cluster ω o = S} * Mx *
              (if u ∈ S ∧ v ∉ S then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) :=
            ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => hTle u v
        _ = law q₀ {ω | cluster ω o = S} * Mx * ∑' u, ∑' v,
              (if u ∈ S ∧ v ∉ S then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) := by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun u => ENNReal.tsum_mul_left
        _ ≤ law q₀ {ω | cluster ω o = S} * Mx * ((S.card : ℝ≥0∞) * a) := by
            gcongr
            exact tsum_tsum_ite_mem_not_mem_le s S ha
        _ = _ := by
            rw [Set.encard_coe_eq_coe_finsetCard]
            push_cast
            ring
    rcases le_total 1 (a * Mx * ((S : Set V).encard)) with hmin | hmin
    · rw [min_eq_left hmin, mul_one]; exact hle1
    · rw [min_eq_right hmin]; exact hle2
  calc ∫⁻ η, Ψ ((Prod.map split id ∘ first) η) ∂P3
      ≤ ∫⁻ η, ∑' S : Finset V, (A1 S ∩ E).indicator (fun _ => f S) η ∂P3 := lintegral_mono_ae hpt
    _ = ∑' S : Finset V, f S * P3 (A1 S ∩ E) := by
        rw [lintegral_tsum fun S => (measurable_const.indicator
          ((hA1m S).inter hEm)).aemeasurable]
        exact tsum_congr fun S => lintegral_indicator_const ((hA1m S).inter hEm) _
    _ ≤ ∑' S : Finset V, law q₀ {ω | cluster ω o = S} *
          (min 1 (a * Mx * ((S : Set V).encard)) * f S) := by
        refine ENNReal.tsum_le_tsum fun S => ?_
        calc f S * P3 (A1 S ∩ E)
            ≤ f S * (law q₀ {ω | cluster ω o = S} * min 1 (a * Mx * ((S : Set V).encard))) := by
              gcongr
              exact hS S
          _ = _ := by ring
    _ ≤ _ := tsum_law_cluster_eq_finset_mul_le_set q₀ o
        (fun T => min 1 (a * Mx * T.encard) * f T)

/-- **Tail form.** Under the hypotheses of `lintegral_ghost_added_mul_le`, for every
`t`, `(1 - e^{-ht}) P(|D| ≥ t) ≤ E[min(1, a M*(h) |C|)]`. -/
theorem law_added_volume_ge_mul_le [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) (hfin : ∀ᵐ ω ∂(law q₀), (cluster ω o).Finite) {a : ℝ≥0∞}
    (ha : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ a)
    (t : ℕ∞) :
    (1 - EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal)))) *
        ((law q₀).prod (law s)) {x | t ≤ (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard} ≤
      ∫⁻ ω, min 1 (a * (⨆ v, ∫⁻ ω', (1 - EReal.exp (-((h : EReal) *
          (((cluster ω' v).encard : ℝ≥0∞) : EReal)))) ∂(law fun e => σ (σ (q₀ e) * σ (s e)))) *
          (cluster ω o).encard) ∂(law q₀) := by
  have hD : Measurable fun x : Config V × Config V => cluster (x.1 ∪ x.2) o \ cluster x.1 o :=
    Measurable.of_mem fun v => (measurableSet_mem_added o v).mem
  have hS : MeasurableSet {x : Config V × Config V |
      t ≤ (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard} :=
    (measurable_encard.comp hD) (Set.to_countable {n : ℕ∞ | t ≤ n}).measurableSet
  have h1 := lintegral_ghost_added_mul_le q₀ s o hh hfin ha (fun _ => 1) measurable_const
  simp only [mul_one] at h1
  refine le_trans ?_ h1
  rw [← lintegral_indicator_const hS]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ {x : Config V × Config V |
      t ≤ (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard}
  · rw [indicator_of_mem hx]
    refine tsub_le_tsub_left (EReal.exp_monotone (EReal.neg_le_neg_iff.2 ?_)) 1
    refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hh.le)
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (by exact_mod_cast hx)
  · rw [indicator_of_notMem hx]
    exact zero_le

/-! ### Non-vacuity witness -/

/-- **Non-vacuity witness.** On `Bool` with no first layer (`q₀ = 0`) and a second layer of
probability `1` on every pair, the hypotheses of `lintegral_ghost_added_mul_le` hold with
`a = 1` (each off-diagonal row has one pair), for every `h > 0` and every `f`. -/
example (f : Set Bool → ℝ≥0∞) :
    ∫⁻ x, (1 - EReal.exp (-(((1 : ℝ) : EReal) *
        (((cluster (x.1 ∪ x.2) false \ cluster x.1 false).encard : ℝ≥0∞) : EReal)))) *
        f (cluster x.1 false) ∂((law (fun _ : Sym2 Bool => (0 : I))).prod
          (law (fun _ : Sym2 Bool => (1 : I)))) ≤
      ∫⁻ ω, min 1 (1 * (⨆ v, ∫⁻ ω', (1 - EReal.exp (-(((1 : ℝ) : EReal) *
          (((cluster ω' v).encard : ℝ≥0∞) : EReal))))
          ∂(law fun e => σ (σ ((fun _ : Sym2 Bool => (0 : I)) e) *
            σ ((fun _ : Sym2 Bool => (1 : I)) e)))) *
          (cluster ω false).encard) * f (cluster ω false)
              ∂(law (fun _ : Sym2 Bool => (0 : I))) := by
  refine lintegral_ghost_added_mul_le _ _ false one_pos
    (Filter.Eventually.of_forall fun ω => Set.toFinite _) ?_ f (measurable_of_countable _)
  intro u
  rw [rowSum_toENNReal, tsum_fintype]
  cases u <;> simp [Fintype.univ_bool]

end PercLib.Percolation.Bond
