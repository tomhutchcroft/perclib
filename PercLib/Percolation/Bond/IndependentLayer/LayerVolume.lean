/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.IndependentLayer.AddedVolume

/-!
# The volume of the union cluster, given the original cluster (F4RR)

Let `ω ~ law q₀` and `ξ ~ law s` be independent, `C = K_o(ω)` and `K⁺ = K_o(ω ∪ ξ)`. If every
off-diagonal row sum of `s` is at most `ε` and every susceptibility of the union law `r` is at
most `χ₊`, then for every measurable functional `f ≥ 0` of the original cluster
`E[|K⁺| f(C)] ≤ (1 + ε χ₊) E[|C| f(C)]` (`lintegral_encard_union_mul_le`, extended values
allowed).

The proof explores `K⁺` from `C` (`cluster_union_subset`): `|K⁺|` is at most `|C|` plus the
volumes of the clusters off `C` of the vertices `v ∉ C` joined to `C` by a second-layer pair
(`encard_cluster_union_le`). For a fixed finite value of `C`, the three events `K_o(ω) = C`,
`s(u, v) ∈ ξ` and `y ∈` the cluster of `v` off `C` are independent
(`prodBernoulli_two_explore_eq`), and the cluster of `v` off `C` lies in the union cluster of
`v`, of expected volume at most `χ₊`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The exploration bound for the volume -/

/-- Volume as a sum of indicators. -/
theorem encard_eq_tsum_indicator_one (A : Set V) :
    (A.encard : ℝ≥0∞) = ∑' y, A.indicator (fun _ => (1 : ℝ≥0∞)) y := by
  rw [← ENNReal.tsum_set_one, tsum_subtype A (fun _ => (1 : ℝ≥0∞))]

open Classical in
/-- **Exploration bound for the volume.** `|K_o(ω₁ ∪ ω₂)|` is at most `|C|` plus the volumes
of the clusters off `C = K_o(ω₁)` of the vertices `v ∉ C` joined to some `u ∈ C` by a pair of
`ω₂`. -/
theorem encard_cluster_union_le (ω₁ ω₂ : Config V) (o : V) :
    ((cluster (ω₁ ∪ ω₂) o).encard : ℝ≥0∞) ≤ (cluster ω₁ o).encard +
      ∑' u, ∑' v, (if u ∈ cluster ω₁ o ∧ v ∉ cluster ω₁ o ∧ s(u, v) ∈ ω₂ then
        ((cluster ((ω₁ ∪ ω₂) ∩ {e | ∀ x ∈ e, x ∉ cluster ω₁ o}) v).encard : ℝ≥0∞) else 0) := by
  set C := cluster ω₁ o
  set L : V → Set V := fun v => cluster ((ω₁ ∪ ω₂) ∩ {e | ∀ x ∈ e, x ∉ C}) v
  have hswap : ∑' u, ∑' v, (if u ∈ C ∧ v ∉ C ∧ s(u, v) ∈ ω₂ then ((L v).encard : ℝ≥0∞)
      else 0) = ∑' y, ∑' u, ∑' v, (if u ∈ C ∧ v ∉ C ∧ s(u, v) ∈ ω₂ then
        (L v).indicator (fun _ => (1 : ℝ≥0∞)) y else 0) := by
    have : ∀ u v, (if u ∈ C ∧ v ∉ C ∧ s(u, v) ∈ ω₂ then ((L v).encard : ℝ≥0∞) else 0) =
        ∑' y, (if u ∈ C ∧ v ∉ C ∧ s(u, v) ∈ ω₂ then
          (L v).indicator (fun _ => (1 : ℝ≥0∞)) y else 0) := by
      intro u v
      by_cases h : u ∈ C ∧ v ∉ C ∧ s(u, v) ∈ ω₂
      · simp only [ite_eq_left_of_eq_true _ _ (eq_true h)]
        exact encard_eq_tsum_indicator_one _
      · simp [h]
    simp_rw [this]
    refine (tsum_congr fun u => ENNReal.tsum_comm).trans ?_
    exact ENNReal.tsum_comm
  rw [hswap, encard_eq_tsum_indicator_one, encard_eq_tsum_indicator_one C, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases hy : y ∈ cluster (ω₁ ∪ ω₂) o
  · rw [indicator_of_mem hy]
    rcases cluster_union_subset ω₁ ω₂ o hy with hyC | hyC
    · rw [indicator_of_mem hyC]
      exact le_self_add
    · obtain ⟨u, hu, hy'⟩ := mem_iUnion₂.1 hyC
      obtain ⟨v, hv, hy'⟩ := mem_iUnion₂.1 hy'
      obtain ⟨huv, hy'⟩ := mem_iUnion.1 hy'
      refine le_trans ?_ le_add_self
      refine le_trans ?_ (ENNReal.le_tsum u)
      refine le_trans ?_ (ENNReal.le_tsum v)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hu, hv, huv⟩), indicator_of_mem hy']
  · rw [indicator_of_notMem hy]
    exact zero_le

/-! ### Two layers: three independent events -/

section Two

variable (q₀ s : Sym2 V → I)

/-- A second-layer pair is open with probability `s e`. -/
theorem prodBernoulli_two_second_mem (e : Sym2 V) :
    prodBernoulli (Sum.elim q₀ s) {E | e ∈ (Sum.inr ⁻¹' E : Config V)} =
      (unitInterval.toNNReal (s e) : ℝ≥0∞) := by
  have : {E : Set (Sym2 V ⊕ Sym2 V) | e ∈ (Sum.inr ⁻¹' E : Config V)} =
      {E | (({Sum.inr e} : Finset (Sym2 V ⊕ Sym2 V)) : Set _) ⊆ E} := by
    ext E
    simp
  rw [this, prodBernoulli_subset, Finset.prod_singleton]
  rfl

/-- **Factorisation.** For a finite `C ∋ o`, `u ∈ C` and any `v`, `y`, the events
`K_o(ω) = C`, `s(u, v) ∈ ξ` and "`y` is in the cluster of `v` in `ω ∪ ξ` off `C`" are
independent. -/
theorem prodBernoulli_two_explore_eq [Countable V] (o : V) (C : Finset V) (ho : o ∈ C)
    {u v : V} (hu : u ∈ C) (y : V) :
    prodBernoulli (Sum.elim q₀ s)
        ({E | cluster (Sum.inl ⁻¹' E) o = C} ∩ {E | s(u, v) ∈ (Sum.inr ⁻¹' E : Config V)} ∩
          {E | y ∈ cluster ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩
            {e | ∀ x ∈ e, x ∉ (C : Set V)}) v}) =
      law q₀ {ω | cluster ω o = C} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) *
        prodBernoulli (Sum.elim q₀ s) {E | y ∈ cluster ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩
          {e | ∀ x ∈ e, x ∉ (C : Set V)}) v} := by
  set out : Set (Sym2 V) := {e | ∀ x ∈ e, x ∉ (C : Set V)} with hout
  set M : Set (Sym2 V) := {e | ∃ x ∈ e, x ∈ C} with hM
  set P1 : Set (Sym2 V ⊕ Sym2 V) := Sum.inl '' M
  set P3 : Set (Sym2 V ⊕ Sym2 V) := {Sum.inr s(u, v)}
  set P4 : Set (Sym2 V ⊕ Sym2 V) := Sum.inl '' out ∪ Sum.inr '' out
  set A1 : Set (Set (Sym2 V ⊕ Sym2 V)) := {E | cluster (Sum.inl ⁻¹' E) o = C}
  set A3 : Set (Set (Sym2 V ⊕ Sym2 V)) := {E | s(u, v) ∈ (Sum.inr ⁻¹' E : Config V)}
  set A4 : Set (Set (Sym2 V ⊕ Sym2 V)) :=
    {E | y ∈ cluster ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ out) v}
  have hm1 : MeasurableSet A1 := measurable_preimage_inl (measurableSet_cluster_eq_finset o C ho)
  have hm3 : MeasurableSet A3 := measurable_preimage_inr (measurableSet_mem s(u, v))
  have hm4 : MeasurableSet A4 := by
    have hW : Measurable fun E : Set (Sym2 V ⊕ Sym2 V) =>
        ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ out : Config V) :=
      Measurable.of_mem fun e => ((measurable_set_mem (Sum.inl e)).or
        (measurable_set_mem (Sum.inr e))).and measurable_const
    exact hW (measurableSet_conn v y)
  have hd1 : ∀ E E' : Set (Sym2 V ⊕ Sym2 V), E ∩ P1 = E' ∩ P1 → (E ∈ A1 ↔ E' ∈ A1) := by
    intro E E' hE
    have hagree : (Sum.inl ⁻¹' E : Config V) ∩ M = (Sum.inl ⁻¹' E' : Config V) ∩ M := by
      ext e
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_left fun he => mem_iff_of_inter_eq hE ⟨e, he, rfl⟩
    have e1 := cluster_eq_finset_determined o C ho (Sum.inl ⁻¹' E)
    have e2 := cluster_eq_finset_determined o C ho (Sum.inl ⁻¹' E')
    simp only [mem_ofPred_eq] at e1 e2
    change cluster _ o = (C : Set V) ↔ cluster _ o = (C : Set V)
    rw [e1, e2, hagree]
  have hd3 : ∀ E E' : Set (Sym2 V ⊕ Sym2 V), E ∩ P3 = E' ∩ P3 → (E ∈ A3 ↔ E' ∈ A3) :=
    fun E E' hE => mem_iff_of_inter_eq hE rfl
  have hd4 : ∀ E E' : Set (Sym2 V ⊕ Sym2 V), E ∩ P4 = E' ∩ P4 → (E ∈ A4 ↔ E' ∈ A4) := by
    intro E E' hE
    have hW : ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ out : Config V) =
        (Sum.inl ⁻¹' E' ∪ Sum.inr ⁻¹' E') ∩ out := by
      ext e
      simp only [mem_inter_iff, mem_union, mem_preimage]
      refine and_congr_left fun he => or_congr ?_ ?_
      · exact mem_iff_of_inter_eq hE (Or.inl ⟨e, he, rfl⟩)
      · exact mem_iff_of_inter_eq hE (Or.inr ⟨e, he, rfl⟩)
    simp only [A4, mem_ofPred_eq, hW]
  have hdis13 : Disjoint P1 P3 := by
    refine Set.disjoint_left.2 fun i hi h3 => ?_
    rcases i with e | e <;> simp [P1, P3] at hi h3
  have hdis4 : Disjoint (P1 ∪ P3) P4 := by
    refine Set.disjoint_left.2 fun i hi h4 => ?_
    rcases i with e | e <;> simp only [hM, union_singleton, mem_insert_iff, reduceCtorEq, mem_image,
        mem_ofPred_eq, Sum.inl.injEq, exists_eq_right, false_or, hout, SetLike.mem_coe, mem_union,
        and_false, exists_false, or_false, P1, P3, P4, Sum.inr.injEq] at hi h4
    · obtain ⟨x, hx, hxC⟩ := hi
      exact h4 x hx hxC
    · subst hi
      exact h4 u (Sym2.mem_mk_left u v) hu
  have hA1 : prodBernoulli (Sum.elim q₀ s) A1 = law q₀ {ω | cluster ω o = C} := by
    rw [law, ← prodBernoulli_map_preimage_inl q₀ s,
      Measure.map_apply measurable_preimage_inl (measurableSet_cluster_eq_finset o C ho)]
    rfl
  rw [prodBernoulli_inter_of_determined _ hdis4 (hm1.inter hm3) hm4
      (determined_inter hd1 hd3) hd4,
    prodBernoulli_inter_of_determined _ hdis13 hm1 hm3 hd1 hd3,
    prodBernoulli_two_second_mem, hA1]

end Two

/-! ### F4RR -/

open Classical in
/-- **F4RR.** Let `ω ~ law q₀` and `ξ ~ law s` be independent, `C = K_o(ω)` and
`K⁺ = K_o(ω ∪ ξ)`. If every off-diagonal row sum of `s` is at most `ε` and every
susceptibility of the union law is at most `χ₊`, then for every measurable functional
`f ≥ 0` of the original cluster, `E[|K⁺| f(C)] ≤ (1 + ε χ₊) E[|C| f(C)]` (extended values
allowed). -/
@[tag "F4RR"]
theorem lintegral_encard_union_mul_le [Countable V] (q₀ s : Sym2 V → I) (o : V)
    {ε χ : ℝ≥0∞}
    (hε : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ ε)
    (hχ : ∀ v, chi (fun e => σ (σ (q₀ e) * σ (s e))) v ≤ χ)
    (f : Set V → ℝ≥0∞) (hf : Measurable fun ω : Config V => f (cluster ω o)) :
    ∫⁻ x, ((cluster (x.1 ∪ x.2) o).encard : ℝ≥0∞) * f (cluster x.1 o)
        ∂((law q₀).prod (law s)) ≤
      (1 + ε * χ) * ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀) := by
  set P2 := prodBernoulli (Sum.elim q₀ s) with hP2
  set split : Set (Sym2 V ⊕ Sym2 V) → Config V × Config V :=
    fun E => ((Sum.inl ⁻¹' E : Config V), (Sum.inr ⁻¹' E : Config V)) with hsplit_def
  have hsplit : Measurable split := measurable_preimage_inl.prodMk measurable_preimage_inr
  have hμ : (law q₀).prod (law s) = P2.map split := (prodBernoulli_sum_map_prod q₀ s).symm
  have hu : Measurable fun x : Config V × Config V => x.1 ∪ x.2 :=
    Measurable.of_mem fun e => ((measurable_set_mem e).comp measurable_fst).or
      ((measurable_set_mem e).comp measurable_snd)
  have hcard : ∀ x : V, Measurable fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞) :=
    fun x => (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard_cluster x)
  have hΦ : Measurable fun x : Config V × Config V =>
      ((cluster (x.1 ∪ x.2) o).encard : ℝ≥0∞) * f (cluster x.1 o) :=
    ((hcard o).comp hu).mul (hf.comp measurable_fst)
  rw [hμ, lintegral_map hΦ hsplit]
  -- notation on the two-layer space
  set A1 : Finset V → Set (Set (Sym2 V ⊕ Sym2 V)) :=
    fun S => {E | cluster (Sum.inl ⁻¹' E) o = S} with hA1_def
  set A3 : V → V → Set (Set (Sym2 V ⊕ Sym2 V)) :=
    fun u v => {E | s(u, v) ∈ (Sum.inr ⁻¹' E : Config V)} with hA3_def
  set X : Finset V → V → Set (Sym2 V ⊕ Sym2 V) → ℝ≥0∞ := fun S v E =>
    ((cluster ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ {e | ∀ x ∈ e, x ∉ (S : Set V)}) v).encard :
      ℝ≥0∞) with hX_def
  set Z : Finset V → V → V → Set (Sym2 V ⊕ Sym2 V) → ℝ≥0∞ := fun S u v E =>
    f S * (if u ∈ S ∧ v ∉ S then (A1 S ∩ A3 u v).indicator (X S v) E else 0) with hZ_def
  have hA1m : ∀ S, MeasurableSet (A1 S) := fun S =>
    measurable_preimage_inl (measurableSet_cluster_eq_finset' o S)
  have hA3m : ∀ u v, MeasurableSet (A3 u v) := fun u v =>
    measurable_preimage_inr (measurableSet_mem s(u, v))
  have hXm : ∀ S v, Measurable (X S v) := by
    intro S v
    have hW : Measurable fun E : Set (Sym2 V ⊕ Sym2 V) =>
        ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ {e | ∀ x ∈ e, x ∉ (S : Set V)} : Config V) :=
      Measurable.of_mem fun e => ((measurable_set_mem (Sum.inl e)).or
        (measurable_set_mem (Sum.inr e))).and measurable_const
    exact (hcard v).comp hW
  have hZm : ∀ S u v, Measurable (Z S u v) := by
    intro S u v
    refine measurable_const.mul ?_
    split_ifs
    · exact (hXm S v).indicator ((hA1m S).inter (hA3m u v))
    · exact measurable_const
  have hm1 : Measurable fun E : Set (Sym2 V ⊕ Sym2 V) =>
      ((cluster (Sum.inl ⁻¹' E : Config V) o).encard : ℝ≥0∞) *
        f (cluster (Sum.inl ⁻¹' E : Config V) o) :=
    ((hcard o).comp measurable_preimage_inl).mul (hf.comp measurable_preimage_inl)
  -- the pointwise exploration bound
  have hZeq : ∀ (S : Finset V) (E : Set (Sym2 V ⊕ Sym2 V)), E ∈ A1 S → ∀ u v,
      Z S u v E = f S * (if u ∈ S ∧ v ∉ S ∧ s(u, v) ∈ (Sum.inr ⁻¹' E : Config V)
        then X S v E else 0) := by
    intro S E hE u v
    simp only [hZ_def]
    congr 1
    by_cases h1 : u ∈ S ∧ v ∉ S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      by_cases h3 : s(u, v) ∈ (Sum.inr ⁻¹' E : Config V)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1.1, h1.2, h3⟩),
          indicator_of_mem (show E ∈ A1 S ∩ A3 u v from ⟨hE, h3⟩)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h3 h.2.2),
          indicator_of_notMem (show E ∉ A1 S ∩ A3 u v from fun h => h3 h.2)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1),
        ite_eq_right_of_eq_false _ _ (eq_false fun h => h1 ⟨h.1, h.2.1⟩)]
  have hpt : ∀ E : Set (Sym2 V ⊕ Sym2 V),
      ((cluster ((split E).1 ∪ (split E).2) o).encard : ℝ≥0∞) * f (cluster (split E).1 o) ≤
        ((cluster (Sum.inl ⁻¹' E : Config V) o).encard : ℝ≥0∞) *
          f (cluster (Sum.inl ⁻¹' E : Config V) o) + ∑' S, ∑' u, ∑' v, Z S u v E := by
    intro E
    simp only [hsplit_def]
    rcases (cluster (Sum.inl ⁻¹' E : Config V) o).finite_or_infinite with hK | hK
    · set S0 := hK.toFinset with hS0
      have hc : cluster (Sum.inl ⁻¹' E : Config V) o = (S0 : Set V) := by simp [S0]
      have hE : E ∈ A1 S0 := hc
      refine le_trans (mul_le_mul_of_nonneg_right (encard_cluster_union_le _ _ o) zero_le) ?_
      rw [add_mul]
      refine add_le_add le_rfl ?_
      refine le_trans ?_ (ENNReal.le_tsum S0)
      rw [mul_comm, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun u => ?_
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun v => le_of_eq ?_
      rw [hZeq S0 E hE u v, hc]
      simp only [Finset.mem_coe, hX_def]
    · have htop : ((cluster (Sum.inl ⁻¹' E : Config V) o).encard : ℝ≥0∞) = ⊤ := by
        simp [Set.encard_eq_top_iff.2 hK]
      refine le_trans ?_ le_self_add
      rw [htop]
      exact mul_le_mul_of_nonneg_right le_top zero_le
  -- the expectation of one exploration term
  have hZint : ∀ S u v, ∫⁻ E, Z S u v E ∂P2 ≤ f S * (law q₀ {ω | cluster ω o = S} * χ *
      (if u ∈ S ∧ v ∉ S then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0)) := by
    intro S u v
    by_cases huv : u ∈ S ∧ v ∉ S
    swap
    · have h0 : (fun E => Z S u v E) = fun _ => 0 := by
        funext E
        simp only [hZ_def]
        rw [ite_eq_right_of_eq_false _ _ (eq_false huv), mul_zero]
      rw [h0, lintegral_zero]
      exact zero_le
    have hZ' : (fun E => Z S u v E) =
        fun E => f S * (A1 S ∩ A3 u v).indicator (X S v) E := by
      funext E
      simp only [hZ_def]
      rw [ite_eq_left_of_eq_true _ _ (eq_true huv)]
    rw [hZ', lintegral_const_mul _ ((hXm S v).indicator ((hA1m S).inter (hA3m u v))),
      ite_eq_left_of_eq_true _ _ (eq_true huv)]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    by_cases ho : o ∈ S
    swap
    · have hempty : A1 S = ∅ := by
        ext E
        simp only [hA1_def, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hc
        have := mem_cluster_self (Sum.inl ⁻¹' E : Config V) o
        rw [hc] at this
        exact ho (by exact_mod_cast this)
      rw [hempty, empty_inter, indicator_empty, lintegral_zero]
      exact zero_le
    set B : V → Set (Set (Sym2 V ⊕ Sym2 V)) := fun y => {E | y ∈ cluster
      ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ {e | ∀ x ∈ e, x ∉ (S : Set V)}) v} with hB_def
    have hBm : ∀ y, MeasurableSet (B y) := by
      intro y
      have hW : Measurable fun E : Set (Sym2 V ⊕ Sym2 V) =>
          ((Sum.inl ⁻¹' E ∪ Sum.inr ⁻¹' E) ∩ {e | ∀ x ∈ e, x ∉ (S : Set V)} : Config V) :=
        Measurable.of_mem fun e => ((measurable_set_mem (Sum.inl e)).or
          (measurable_set_mem (Sum.inr e))).and measurable_const
      exact hW (measurableSet_conn v y)
    have hXsum : ∀ E, (A1 S ∩ A3 u v).indicator (X S v) E =
        ∑' y, (A1 S ∩ A3 u v ∩ B y).indicator (fun _ => (1 : ℝ≥0∞)) E := by
      intro E
      by_cases hE : E ∈ A1 S ∩ A3 u v
      · rw [indicator_of_mem hE, hX_def]
        simp only
        rw [encard_eq_tsum_indicator_one]
        refine tsum_congr fun y => ?_
        by_cases hy : E ∈ B y
        · rw [indicator_of_mem (show y ∈ _ from hy),
            indicator_of_mem (show E ∈ A1 S ∩ A3 u v ∩ B y from ⟨hE, hy⟩)]
        · rw [indicator_of_notMem (show y ∉ _ from hy),
            indicator_of_notMem (show E ∉ A1 S ∩ A3 u v ∩ B y from fun h => hy h.2)]
      · rw [indicator_of_notMem hE]
        exact (ENNReal.tsum_eq_zero.2 fun y =>
          indicator_of_notMem (fun h => hE h.1) _).symm
    simp_rw [hXsum]
    rw [lintegral_tsum fun y => (measurable_const.indicator
      (((hA1m S).inter (hA3m u v)).inter (hBm y))).aemeasurable]
    have hint : ∀ y, ∫⁻ E, (A1 S ∩ A3 u v ∩ B y).indicator (fun _ => (1 : ℝ≥0∞)) E ∂P2 =
        P2 (A1 S ∩ A3 u v ∩ B y) := fun y => by
      rw [lintegral_indicator_const (((hA1m S).inter (hA3m u v)).inter (hBm y)), one_mul]
    simp_rw [hint]
    have hfac : ∀ y, P2 (A1 S ∩ A3 u v ∩ B y) =
        law q₀ {ω | cluster ω o = S} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) * P2 (B y) :=
      fun y => prodBernoulli_two_explore_eq q₀ s o S ho huv.1 y
    simp_rw [hfac]
    rw [ENNReal.tsum_mul_left]
    have hchi : ∑' y, P2 (B y) ≤ χ := by
      refine le_trans ?_ (hχ v)
      rw [chi_eq_tsum_tau]
      refine ENNReal.tsum_le_tsum fun y => ?_
      rw [tau, ← prodBernoulli_map_union_preimage,
        Measure.map_apply measurable_union_preimage (measurableSet_conn v y)]
      exact measure_mono fun E hE => cluster_mono inter_subset_left v hE
    calc law q₀ {ω | cluster ω o = S} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) *
          ∑' y, P2 (B y)
        ≤ law q₀ {ω | cluster ω o = S} * (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) * χ := by
          gcongr
      _ = _ := by ring
  -- assembling
  have hfirst : ∫⁻ E, ((cluster (Sum.inl ⁻¹' E : Config V) o).encard : ℝ≥0∞) *
      f (cluster (Sum.inl ⁻¹' E : Config V) o) ∂P2 =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀) := by
    rw [show law q₀ = P2.map (fun E => (Sum.inl ⁻¹' E : Config V)) from
      (prodBernoulli_map_preimage_inl q₀ s).symm,
      lintegral_map (f := fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o))
        ((hcard o).mul hf) measurable_preimage_inl]
  calc ∫⁻ E, ((cluster ((split E).1 ∪ (split E).2) o).encard : ℝ≥0∞) *
        f (cluster (split E).1 o) ∂P2
      ≤ ∫⁻ E, (((cluster (Sum.inl ⁻¹' E : Config V) o).encard : ℝ≥0∞) *
          f (cluster (Sum.inl ⁻¹' E : Config V) o) + ∑' S, ∑' u, ∑' v, Z S u v E) ∂P2 :=
        lintegral_mono hpt
    _ = ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀) +
          ∑' S, ∑' u, ∑' v, ∫⁻ E, Z S u v E ∂P2 := by
        rw [lintegral_add_left hm1, hfirst,
          lintegral_tsum fun S => (Measurable.tsum fun u =>
            Measurable.tsum fun v => hZm S u v).aemeasurable]
        congr 1
        refine tsum_congr fun S => ?_
        rw [lintegral_tsum fun u => (Measurable.tsum fun v => hZm S u v).aemeasurable]
        exact tsum_congr fun u => lintegral_tsum fun v => (hZm S u v).aemeasurable
    _ ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀) +
          ∑' S : Finset V, law q₀ {ω | cluster ω o = S} *
            (((S : Set V).encard : ℝ≥0∞) * f S) * (ε * χ) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun S => ?_)
        calc ∑' u, ∑' v, ∫⁻ E, Z S u v E ∂P2
            ≤ ∑' u, ∑' v, f S * (law q₀ {ω | cluster ω o = S} * χ *
                (if u ∈ S ∧ v ∉ S then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0)) :=
              ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => hZint S u v
          _ = f S * (law q₀ {ω | cluster ω o = S} * χ) * ∑' u, ∑' v,
                (if u ∈ S ∧ v ∉ S then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) := by
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr fun u => ?_
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun v => by ring
          _ ≤ f S * (law q₀ {ω | cluster ω o = S} * χ) * ((S.card : ℝ≥0∞) * ε) := by
              gcongr
              exact tsum_tsum_ite_mem_not_mem_le s S hε
          _ = _ := by
              rw [Set.encard_coe_eq_coe_finsetCard]
              push_cast
              ring
    _ = ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀) +
          (∑' S : Finset V, law q₀ {ω | cluster ω o = S} *
            (((S : Set V).encard : ℝ≥0∞) * f S)) * (ε * χ) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀) +
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) * f (cluster ω o) ∂(law q₀)) * (ε * χ) := by
        gcongr
        exact tsum_law_cluster_eq_finset_mul_le_set q₀ o (fun T => (T.encard : ℝ≥0∞) * f T)
    _ = _ := by ring

/-! ### Non-vacuity witness -/

/-- **Non-vacuity witness.** On `Bool` with no first layer (`q₀ = 0`) and a fully open second layer,
the hypotheses of `lintegral_encard_union_mul_le` hold with `ε = 1` (one pair per row) and
`χ₊ = 2` (two vertices), for every `f`. -/
example (f : Set Bool → ℝ≥0∞) :
    ∫⁻ x, ((cluster (x.1 ∪ x.2) false).encard : ℝ≥0∞) * f (cluster x.1 false)
        ∂((law (fun _ : Sym2 Bool => (0 : I))).prod (law (fun _ : Sym2 Bool => (1 : I)))) ≤
      (1 + 1 * 2) * ∫⁻ ω, ((cluster ω false).encard : ℝ≥0∞) * f (cluster ω false)
        ∂(law (fun _ : Sym2 Bool => (0 : I))) := by
  refine lintegral_encard_union_mul_le _ _ false ?_ ?_ f (measurable_of_countable _)
  · intro u
    rw [rowSum_toENNReal, tsum_fintype]
    cases u <;> simp [Fintype.univ_bool]
  · intro v
    refine le_trans (lintegral_mono (g := fun _ => (2 : ℝ≥0∞)) fun ω => ?_) (by simp)
    change ((cluster ω v).encard : ℝ≥0∞) ≤ 2
    have h : (cluster ω v).encard ≤ (Set.univ : Set Bool).encard :=
      Set.encard_le_encard (Set.subset_univ _)
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool] at h
    exact_mod_cast h

end PercLib.Percolation.Bond
