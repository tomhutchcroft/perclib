/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.Exploration
public import PercLib.Percolation.Bond.RowSum
public import PercLib.Percolation.Bond.Susceptibility

/-!
# Adding an independent layer: the two-layer ghost comparison (BEJT)

Let `q₀, s : Sym2 V → I` and let `r = σ (σ q₀ · σ s)`, the law of the union of independent
configurations with profiles `q₀` and `s` (`prodBernoulli_prod_map_union`). For `h > 0` and
`T : ℕ∞` write `e^{-hT}` for `EReal.exp (-(h * T))`, so that `e^{-h·⊤} = 0`. Write `X` for
the `q₀`-cluster volume of `o`, `G_v(h) = ∫ (1 - e^{-h|K_v|}) d(law r)` and
`G* = ⨆ v, G_v(h)`.

**BEJT** (`lintegral_ghost_le_layer`). If `X < ⊤` almost surely, then
`E[1 - e^{-hX}] ≤ G_o(h) ≤ E[1 - e^{-hX}] + δ · E[X e^{-hX}] · G*(h)`,
where `δ = ⨆ u, ∑'_{v ≠ u} s(u, v)`.

The proof marks the vertices independently with probability `1 - e^{-h}`.
`Ghost.lean` turns each ghost transform into the probability that a cluster contains a
mark. The union cluster of `o` contains a mark only if one of two things happens:
* the `q₀`-cluster `C` contains one;
* `C` contains no mark, some second-layer pair `s(u, v)` with `u ∈ C`, `v ∉ C` is open, and
  the cluster of `v` off `C` contains a mark.

These four events are independent (`Exploration.lean`), so summing over `C`, `u` and `v`
gives the bound.

This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- For every `h`, a mark probability `p` with `1 - p = e^{-h}` exists when `h ≥ 0`. -/
theorem exists_symm_eq_exp {h : ℝ} (hh : 0 ≤ h) : ∃ p : I, ((σ p : I) : ℝ) = Real.exp (-h) :=
  ⟨σ ⟨Real.exp (-h), (Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩, by simp⟩

/-- **Two-layer ghost comparison, lower bound.** Adding a layer only increases the ghost transform.
-/
theorem lintegral_ghost_le_union [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q₀) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) := by
  obtain ⟨p, hp⟩ := exists_symm_eq_exp hh.le
  rw [← prodBernoulli_three_first_cluster q₀ s o hh hp,
    ← prodBernoulli_three_union_cluster q₀ s o hh hp]
  exact measure_mono fun η hη => hη.mono (inter_subset_inter_left _
    (cluster_mono subset_union_left o))

open Classical in
/-- The off-diagonal row sum over the vertices outside a set containing `u` is at most the
full off-diagonal row sum. -/
theorem tsum_ite_not_mem_le (s : Sym2 V → I) (C : Finset V) {u : V} (hu : u ∈ C) :
    ∑' v, (if v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) ≤
      rowSum (fun e => unitInterval.toENNReal (s e)) u := by
  rw [rowSum_toENNReal]
  refine ENNReal.tsum_le_tsum fun v => ?_
  by_cases hv : v ∈ C
  · simp [hv]
  · have : v ≠ u := fun h => hv (h ▸ hu)
    simp [hv, this]

/-- **Two-layer ghost comparison, upper bound, with explicit bounds.** If every off-diagonal row
sum of `s` is at most `δ` and every ghost transform `G_v(h)` of the union law is at most `G`, then
`G_o(h) ≤ E[1 - e^{-hX}] + δ · E[X e^{-hX}] · G`. The `q₀`-cluster of `o` may be infinite with
positive probability: on that event it contains a mark almost surely. -/
theorem lintegral_ghost_union_le_of_rowSum_le [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) {δ G : ℝ≥0∞}
    (hδ : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ δ)
    (hG : ∀ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ≤ G) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law q₀) +
        δ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))) ∂(law q₀)) * G := by
  classical
  obtain ⟨p, hp⟩ := exists_symm_eq_exp hh.le
  set Pr := prodBernoulli (Sum.elim (Sum.elim q₀ s) fun _ : V => p) with hPr
  -- the exploration event for `C`, `u`, `v`
  set T : Finset V → V → V → Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) := fun C u v =>
    ⋃ (_ : o ∈ C ∧ u ∈ C ∧ v ∉ C),
      {η | cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o = C} ∩
        {η | (C : Set V) ∩ Sum.inr ⁻¹' η = ∅} ∩
        {η | s(u, v) ∈ (Sum.inr ⁻¹' (Sum.inl ⁻¹' η) : Config V)} ∩
        {η | (cluster ((Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) ∩
          {e | ∀ x ∈ e, x ∉ (C : Set V)}) v ∩ Sum.inr ⁻¹' η).Nonempty} with hT
  set E1 : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    {η | (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o ∩ Sum.inr ⁻¹' η).Nonempty} with hE1
  set Einf : Set (Set ((Sym2 V ⊕ Sym2 V) ⊕ V)) :=
    {η | (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) o).Infinite} with hEinf
  -- the inclusion
  have hsub : {η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) |
      (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) ∪ Sum.inr ⁻¹' (Sum.inl ⁻¹' η)) o ∩
        Sum.inr ⁻¹' η).Nonempty} ⊆ E1 ∪ Einf ∪ ⋃ C, ⋃ u, ⋃ v, T C u v := by
    rintro η ⟨y, hyK, hyg⟩
    by_cases h1 : η ∈ E1
    · exact Or.inl (Or.inl h1)
    rcases (cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o).finite_or_infinite with hK | hK
    swap
    · exact Or.inl (Or.inr hK)
    refine Or.inr ?_
    set C := hK.toFinset
    have hKC : cluster (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o = (C : Set V) := by simp [C]
    rcases cluster_union_subset _ _ o hyK with hy | hy
    · exact absurd ⟨y, hy, hyg⟩ h1
    obtain ⟨u, hu, hy⟩ := mem_iUnion₂.1 hy
    obtain ⟨v, hv, hy⟩ := mem_iUnion₂.1 hy
    obtain ⟨huv, hy⟩ := mem_iUnion.1 hy
    rw [hKC] at hu hv hy
    have ho : o ∈ C := by
      have := mem_cluster_self (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V) o
      rw [hKC] at this
      exact_mod_cast this
    refine mem_iUnion.2 ⟨C, mem_iUnion.2 ⟨u, mem_iUnion.2 ⟨v, mem_iUnion.2
      ⟨⟨ho, by exact_mod_cast hu, by exact_mod_cast hv⟩, ⟨⟨⟨hKC, ?_⟩, huv⟩, ⟨y, hy, hyg⟩⟩⟩⟩⟩⟩
    rw [← hKC]
    exact not_nonempty_iff_eq_empty.1 h1
  -- each exploration event
  have hTle : ∀ C u v, Pr (T C u v) ≤ law q₀ {ω | cluster ω o = C} *
      EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))) * G *
        (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) := by
    intro C u v
    by_cases hc : o ∈ C ∧ u ∈ C ∧ v ∉ C
    · simp only [hT, hc, not_false_eq_true, and_self, iUnion_true]
      rw [prodBernoulli_three_explore_eq q₀ s p hh hp o C hc.1 hc.2.1 hc.2.2]
      calc _ ≤ law q₀ {ω | cluster ω o = C} *
            EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))) *
            (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) * G := by
            gcongr
            exact (prodBernoulli_three_avoid_le q₀ s p hh hp _ v).trans (hG v)
        _ = _ := by simp only [↓reduceIte]; ring
    · simp only [hT, hc, iUnion_false, measure_empty]
      exact zero_le
  -- the row sums
  have hrow : ∀ C : Finset V, ∑' u, ∑' v,
      (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) ≤
        (C.card : ℝ≥0∞) * δ := by
    intro C
    calc ∑' u, ∑' v, (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0)
        ≤ ∑' u, (if u ∈ C then δ else 0) := by
          refine ENNReal.tsum_le_tsum fun u => ?_
          by_cases hu : u ∈ C
          · simp only [hu, true_and]
            exact (tsum_ite_not_mem_le s C hu).trans (hδ u)
          · simp [hu]
      _ = ∑ u ∈ C, δ := by
          rw [tsum_eq_sum (s := C) fun u hu => by simp [hu]]
          exact Finset.sum_congr rfl fun u hu => by simp [hu]
      _ = (C.card : ℝ≥0∞) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the infinite part
  have hinf : Pr (E1 ∪ Einf) = Pr E1 := by
    -- the marks hit an infinite first-layer cluster almost surely
    set Linf : Config V → Set V := fun ω => {w | w ∈ cluster ω o ∧ (cluster ω o).Infinite}
      with hLinf
    have hLm : ∀ w, MeasurableSet {ω | w ∈ Linf ω} := fun w =>
      (measurableSet_conn o w).inter (measurableSet_cluster_infinite o)
    have hA := prodBernoulli_sum_inter_nonempty (Sum.elim q₀ s) measurable_preimage_inl
      (L := Linf) hLm hh hp (p := p)
    rw [prodBernoulli_map_preimage_inl] at hA
    have hint : ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((Linf ω).encard : ℝ≥0∞) : EReal))))
        ∂(prodBernoulli q₀) = law q₀ {ω | (cluster ω o).Infinite} := by
      rw [← lintegral_indicator_one (measurableSet_cluster_infinite o), law]
      refine lintegral_congr fun ω => ?_
      by_cases hω : (cluster ω o).Infinite
      · have hL : Linf ω = cluster ω o := by ext w; simp [hLinf, hω]
        rw [hL, hω.encard_eq, PercLib.Analysis.exp_neg_mul_top hh]
        simp [hω]
      · have hL : Linf ω = ∅ := by ext w; simp [hLinf, hω]
        simp [hL, hω]
    have hEinf : Pr Einf = law q₀ {ω | (cluster ω o).Infinite} := by
      change Pr ((fun η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) => (Sum.inl ⁻¹' (Sum.inl ⁻¹' η) : Config V))
        ⁻¹' {ω | (cluster ω o).Infinite}) = _
      rw [← Measure.map_apply measurable_three_first (measurableSet_cluster_infinite o), hPr,
        prodBernoulli_three_map_first]
    have hAsub : {η : Set ((Sym2 V ⊕ Sym2 V) ⊕ V) |
        (Linf (Sum.inl ⁻¹' (Sum.inl ⁻¹' η)) ∩ Sum.inr ⁻¹' η).Nonempty} ⊆ Einf ∩ E1 := by
      rintro η ⟨y, ⟨hy, hyi⟩, hym⟩
      exact ⟨hyi, y, hy, hym⟩
    have hE1m : MeasurableSet E1 :=
      (measurableSet_prod_inter_nonempty (K := fun ω : Config V => cluster ω o)
        (fun w => measurableSet_conn o w)).preimage
        (measurable_three_first.prodMk measurable_preimage_inr)
    have hdiff : Pr (Einf \ E1) = 0 := by
      have hsplit := measure_inter_add_sdiff Einf hE1m (μ := Pr)
      have hle : Pr Einf ≤ Pr (Einf ∩ E1) := by
        rw [hEinf, ← hint, ← hA, hPr]
        exact measure_mono hAsub
      refine le_antisymm ?_ zero_le
      refine (ENNReal.add_le_add_iff_left (measure_ne_top Pr (Einf ∩ E1))).1 ?_
      rw [hsplit, add_zero]
      exact hle
    refine le_antisymm ?_ (measure_mono subset_union_left)
    rw [← union_sdiff_self]
    exact (measure_union_le _ _).trans (by rw [hdiff, add_zero])
  -- assembling
  rw [← prodBernoulli_three_union_cluster q₀ s o hh hp,
    ← prodBernoulli_three_first_cluster q₀ s o hh hp]
  calc _ ≤ Pr (E1 ∪ Einf ∪ ⋃ C, ⋃ u, ⋃ v, T C u v) := measure_mono hsub
    _ ≤ Pr (E1 ∪ Einf) + ∑' C, ∑' u, ∑' v, Pr (T C u v) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun C =>
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun u => measure_iUnion_le _))
    _ ≤ Pr E1 + ∑' C : Finset V, law q₀ {ω | cluster ω o = C} *
          (((C : Set V).encard : ℝ≥0∞) *
            EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal)))) * (δ * G) := by
        rw [hinf]
        gcongr with C
        calc ∑' u, ∑' v, Pr (T C u v)
            ≤ ∑' u, ∑' v, law q₀ {ω | cluster ω o = C} *
                EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))) * G *
                (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) :=
              ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => hTle C u v
          _ = law q₀ {ω | cluster ω o = C} *
                EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))) * G *
                ∑' u, ∑' v,
                  (if u ∈ C ∧ v ∉ C then (unitInterval.toNNReal (s s(u, v)) : ℝ≥0∞) else 0) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun u => ENNReal.tsum_mul_left
          _ ≤ law q₀ {ω | cluster ω o = C} *
                EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))) * G *
                ((C.card : ℝ≥0∞) * δ) := by gcongr; exact hrow C
          _ = _ := by
              rw [Set.encard_coe_eq_coe_finsetCard]
              push_cast
              ring
    _ = Pr E1 + (∑' C : Finset V, law q₀ {ω | cluster ω o = C} *
          (((C : Set V).encard : ℝ≥0∞) *
            EReal.exp (-((h : EReal) * (((C : Set V).encard : ℝ≥0∞) : EReal))))) * (δ * G) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ _ := by
        refine add_le_add le_rfl ((mul_le_mul_left (tsum_law_cluster_eq_finset_mul_le q₀ o
          (fun T => (T : ℝ≥0∞) * EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))))) _).trans_eq ?_)
        ring

/-- **Two-layer ghost comparison, upper bound, with explicit bounds**, in the form with an
almost surely finite `q₀`-cluster; the finiteness is not needed
(`lintegral_ghost_union_le_of_rowSum_le`). -/
theorem lintegral_ghost_union_le [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) (_hfin : ∀ᵐ ω ∂(law q₀), (cluster ω o).Finite) {δ G : ℝ≥0∞}
    (hδ : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ δ)
    (hG : ∀ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ≤ G) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law q₀) +
        δ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))) ∂(law q₀)) * G :=
  lintegral_ghost_union_le_of_rowSum_le q₀ s o hh hδ hG

/-- **BEJT.** If the `q₀`-cluster `X` of `o` is finite almost surely, then
`E[1 - e^{-hX}] ≤ G_o(h) ≤ E[1 - e^{-hX}] + δ · E[X e^{-hX}] · G*(h)`, where
`δ = ⨆ u, ∑'_{v ≠ u} s(u, v)` and `G*(h) = ⨆ v, G_v(h)`. -/
@[tag "BEJT"]
theorem lintegral_ghost_le_layer [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) (hfin : ∀ᵐ ω ∂(law q₀), (cluster ω o).Finite) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q₀) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ∧
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law q₀) +
        (⨆ u, rowSum (fun e => unitInterval.toENNReal (s e)) u) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
            EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))) ∂(law q₀)) *
          ⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
            ∂(law fun e => σ (σ (q₀ e) * σ (s e))) :=
  ⟨lintegral_ghost_le_union q₀ s o hh,
    lintegral_ghost_union_le q₀ s o hh hfin (fun u => le_iSup (fun u =>
      rowSum (fun e => unitInterval.toENNReal (s e)) u) u)
      (fun v => le_iSup (fun v => ∫⁻ ω,
        (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
          ∂(law fun e => σ (σ (q₀ e) * σ (s e)))) v)⟩

/-! ### Elementary bounds on `1 - e^{-hT}` -/

theorem exp_neg_mul_natCast_eq (h : ℝ) (m : ℕ) :
    EReal.exp (-((h : EReal) * (((m : ℕ∞) : ℝ≥0∞) : EReal))) =
      ENNReal.ofReal (Real.exp (-(h * m))) := by
  rw [exp_neg_mul_natCast, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  ring

/-- `1 - e^{-hT} ≤ hT`. -/
theorem one_sub_exp_le_mul {h : ℝ} (hh : 0 < h) (T : ℕ∞) :
    1 - EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) ≤ ENNReal.ofReal h * T := by
  induction T using ENat.recTopCoe with
  | top => simp [ENNReal.mul_top (ENNReal.ofReal_pos.2 hh).ne']
  | coe m =>
    rw [exp_neg_mul_natCast_eq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
      ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hh.le]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [Real.add_one_le_exp (-(h * m))]

/-- `hT e^{-hT} ≤ 1 - e^{-hT}`. -/
theorem mul_mul_exp_le_one_sub {h : ℝ} (hh : 0 < h) (T : ℕ∞) :
    ENNReal.ofReal h * ((T : ℝ≥0∞) * EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal)))) ≤
      1 - EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) := by
  induction T using ENat.recTopCoe with
  | top => rw [PercLib.Analysis.exp_neg_mul_top hh]; simp
  | coe m =>
    rw [exp_neg_mul_natCast_eq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
      ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hh.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.add_one_le_exp (h * m)
    have h2 : Real.exp (h * m) * Real.exp (-(h * m)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := Real.exp_pos (-(h * m))
    nlinarith

/-- `T e^{-hT} ≤ T`. -/
theorem mul_exp_le_self {h : ℝ} (hh : 0 ≤ h) (T : ℕ∞) :
    (T : ℝ≥0∞) * EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) ≤ T :=
  mul_le_of_le_one_right' (exp_neg_mul_le_one hh T)

/-- The ghost transform is at most one. -/
theorem lintegral_one_sub_exp_le_one (q : Sym2 V → I) (v : V) (h : ℝ) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂(law q) ≤
      1 :=
  (lintegral_mono fun _ => tsub_le_self).trans_eq (by simp)

/-- `T e^{-T/(n+1)} → T` for finite `T`. -/
theorem tendsto_mul_exp_neg_div (m : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((m : ℕ∞) : ℝ≥0∞) *
        EReal.exp (-(((1 / ((n : ℝ) + 1) : ℝ) : EReal) * (((m : ℕ∞) : ℝ≥0∞) : EReal))))
      Filter.atTop (nhds ((m : ℕ∞) : ℝ≥0∞)) := by
  simp_rw [exp_neg_mul_natCast_eq]
  conv => arg 3; rw [← mul_one ((m : ℕ∞) : ℝ≥0∞)]
  refine ENNReal.Tendsto.const_mul ?_ (Or.inr (by simp))
  rw [← ENNReal.ofReal_one]
  refine ENNReal.tendsto_ofReal ?_
  rw [← Real.exp_zero]
  refine (Real.continuous_exp.tendsto 0).comp ?_
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (m : ℝ)
  rw [zero_mul] at this
  simpa using this.neg

/-! ### MLLO -/

/-- A finite susceptibility makes the cluster finite almost surely. -/
@[tag "INZI"]
theorem ae_cluster_finite_of_chi_lt_top [Countable V] {q : Sym2 V → I} {v : V}
    (h : chi q v < ⊤) : ∀ᵐ ω ∂(law q), (cluster ω v).Finite := by
  have hmeas : Measurable (fun ω : Config V => ((cluster ω v).encard : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster v)
  filter_upwards [ae_lt_top hmeas h.ne] with ω hω
  exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp hω)

/-- **Ghost form.** Under the hypotheses of `chi_union_le_of_bounds`, every ghost
transform of the union law satisfies `G_v(h) ≤ h χ_{q₀}(v) / (1 - δM)`. -/
theorem lintegral_ghost_union_le_mul [Countable V] (q₀ s : Sym2 V → I) {δ M : ℝ≥0∞}
    (hδ : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ δ)
    (hchi : ∀ v, chi q₀ v ≤ M) (hM : M < ⊤) (hδM : δ * M < 1) {h : ℝ} (hh : 0 < h) (v : V) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) ≤
      ENNReal.ofReal h * (chi q₀ v / (1 - δ * M)) := by
  set r : Sym2 V → I := fun e => σ (σ (q₀ e) * σ (s e)) with hr
  set g : V → ℝ≥0∞ := fun w => ∫⁻ ω,
    (1 - EReal.exp (-((h : EReal) * (((cluster ω w).encard : ℝ≥0∞) : EReal)))) ∂(law r) with hg
  set Gs := ⨆ w, g w with hGs
  have hc1 : 1 - δ * M ≠ 0 := (tsub_pos_of_lt hδM).ne'
  have hc2 : 1 - δ * M ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  -- the ghost comparison at each vertex
  have hstep : ∀ w, g w ≤ ENNReal.ofReal h * chi q₀ w + δ * chi q₀ w * Gs := by
    intro w
    refine (lintegral_ghost_union_le q₀ s w hh
      (ae_cluster_finite_of_chi_lt_top ((hchi w).trans_lt hM)) hδ
      (fun v => le_iSup g v)).trans (add_le_add ?_ ?_)
    · have hm : Measurable fun ω : Config V => ((cluster ω w).encard : ℝ≥0∞) :=
        (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster w)
      rw [chi, ← lintegral_const_mul _ hm]
      exact lintegral_mono fun ω => one_sub_exp_le_mul hh _
    · gcongr
      exact lintegral_mono fun ω => mul_exp_le_self hh.le _
  -- the supremum
  have hGs1 : Gs ≤ 1 := iSup_le fun w => lintegral_one_sub_exp_le_one r w h
  have hGsM : Gs ≤ ENNReal.ofReal h * M / (1 - δ * M) := by
    have hle : Gs ≤ ENNReal.ofReal h * M + δ * M * Gs := iSup_le fun w =>
      (hstep w).trans (by gcongr <;> exact hchi w)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc1) (Or.inl hc2)]
    have hfin : δ * M * Gs ≠ ⊤ :=
      ENNReal.mul_ne_top (ne_top_of_lt hδM) (ne_top_of_le_ne_top ENNReal.one_ne_top hGs1)
    rw [ENNReal.mul_sub (fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top hGs1), mul_one]
    exact tsub_le_iff_right.2 (hle.trans_eq (by ring))
  -- the vertex `v`
  calc g v ≤ ENNReal.ofReal h * chi q₀ v + δ * chi q₀ v * Gs := hstep v
    _ ≤ ENNReal.ofReal h * chi q₀ v +
        δ * chi q₀ v * (ENNReal.ofReal h * M / (1 - δ * M)) := by gcongr
    _ = ENNReal.ofReal h * chi q₀ v * (1 + δ * M / (1 - δ * M)) := by
        simp only [div_eq_mul_inv]
        ring
    _ = ENNReal.ofReal h * (chi q₀ v / (1 - δ * M)) := by
        have e : (1 - δ * M) / (1 - δ * M) + δ * M / (1 - δ * M) = 1 / (1 - δ * M) := by
          rw [ENNReal.div_add_div_same, tsub_add_cancel_of_le hδM.le]
        rw [ENNReal.div_self hc1 hc2] at e
        rw [e]
        simp only [div_eq_mul_inv, one_mul]
        ring

/-- **Susceptibility of a union with an independent layer.** Let `δ` bound the off-diagonal row sums
of `s`, `M` bound `χ_{q₀}`, `M < ⊤` and `δM < 1`. Then `χ_r(v) ≤ χ_{q₀}(v) / (1 - δM)` for the union
law `r`. -/
theorem chi_union_le_of_bounds [Countable V] (q₀ s : Sym2 V → I) {δ M : ℝ≥0∞}
    (hδ : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ δ)
    (hchi : ∀ v, chi q₀ v ≤ M) (hM : M < ⊤) (hδM : δ * M < 1) (v : V) :
    chi (fun e => σ (σ (q₀ e) * σ (s e))) v ≤ chi q₀ v / (1 - δ * M) := by
  set r : Sym2 V → I := fun e => σ (σ (q₀ e) * σ (s e)) with hr
  set K := chi q₀ v / (1 - δ * M) with hK
  have hc1 : 1 - δ * M ≠ 0 := (tsub_pos_of_lt hδM).ne'
  have hKtop : K ≠ ⊤ := ENNReal.div_ne_top ((hchi v).trans_lt hM).ne hc1
  have hG := fun {h : ℝ} (hh : 0 < h) =>
    lintegral_ghost_union_le_mul q₀ s hδ hchi hM hδM hh v
  -- the cluster of `v` is finite almost surely
  have hinf : law r {ω | (cluster ω v).encard = ⊤} = 0 := by
    have hle : ∀ n : ℕ, law r {ω | (cluster ω v).encard = ⊤} ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) * K := by
      intro n
      have hh : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine le_trans ?_ (hG hh)
      have hms : MeasurableSet {ω : Config V | (cluster ω v).encard = ⊤} :=
        (measurable_encard_cluster v) (measurableSet_singleton ⊤)
      rw [← lintegral_indicator_one hms]
      refine lintegral_mono fun ω => ?_
      by_cases hω : (cluster ω v).encard = ⊤
      · rw [Set.indicator_of_mem (show ω ∈ {ω : Config V | (cluster ω v).encard = ⊤} from hω), hω,
          PercLib.Analysis.exp_neg_mul_top hh]
        simp
      · rw [Set.indicator_of_notMem (show ω ∉ {ω : Config V | (cluster ω v).encard = ⊤} from hω)]
        exact zero_le
    have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)) * K)
        Filter.atTop (nhds 0) := by
      rw [← zero_mul K]
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hKtop)
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_antisymm (ge_of_tendsto' ht hle) zero_le
  -- the moments `E[T e^{-hT}]` are at most `K`
  set f : ℕ → Config V → ℝ≥0∞ := fun n ω => ((cluster ω v).encard : ℝ≥0∞) *
    EReal.exp (-(((1 / ((n : ℝ) + 1) : ℝ) : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal)))
    with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_of_countable (fun T : ℕ∞ => (T : ℝ≥0∞) *
      EReal.exp (-(((1 / ((n : ℝ) + 1) : ℝ) : EReal) * ((T : ℝ≥0∞) : EReal))))).comp
      (measurable_encard_cluster v)
  have hfK : ∀ n, ∫⁻ ω, f n ω ∂(law r) ≤ K := by
    intro n
    have hh : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h1 : ENNReal.ofReal (1 / ((n : ℝ) + 1)) * ∫⁻ ω, f n ω ∂(law r) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) * K := by
      rw [← lintegral_const_mul _ (hfm n)]
      exact (lintegral_mono fun ω => mul_mul_exp_le_one_sub hh _).trans (hG hh)
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hh).ne'
      ENNReal.ofReal_ne_top).1 h1
  -- Fatou
  have hae : ∀ᵐ ω ∂(law r), ((cluster ω v).encard : ℝ≥0∞) =
      Filter.liminf (fun n => f n ω) Filter.atTop := by
    have : ∀ᵐ ω ∂(law r), (cluster ω v).encard ≠ ⊤ := by
      rw [ae_iff]
      simpa using hinf
    filter_upwards [this] with ω hω
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hω
    have := (tendsto_mul_exp_neg_div m).liminf_eq
    rw [hm] at this
    exact this.symm
  calc chi r v = ∫⁻ ω, Filter.liminf (fun n => f n ω) Filter.atTop ∂(law r) :=
        lintegral_congr_ae hae
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, f n ω ∂(law r)) Filter.atTop := lintegral_liminf_le hfm
    _ ≤ K := Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hfK)

/-- **MLLO.** If `M = ⨆ v, χ_{q₀}(v) < ⊤` and `δ M < 1`, where
`δ = ⨆ u, ∑'_{v ≠ u} s(u, v)`, then `χ_r(v) ≤ χ_{q₀}(v) / (1 - δM)` for every `v`. -/
@[tag "MLLO"]
theorem chi_union_le [Countable V] (q₀ s : Sym2 V → I) (hM : ⨆ v, chi q₀ v < ⊤)
    (hδM : (⨆ u, rowSum (fun e => unitInterval.toENNReal (s e)) u) *
      (⨆ v, chi q₀ v) < 1) (v : V) :
    chi (fun e => σ (σ (q₀ e) * σ (s e))) v ≤ chi q₀ v /
      (1 - (⨆ u, rowSum (fun e => unitInterval.toENNReal (s e)) u) *
        (⨆ v, chi q₀ v)) :=
  chi_union_le_of_bounds q₀ s (fun u => le_iSup (fun u =>
    rowSum (fun e => unitInterval.toENNReal (s e)) u) u)
    (fun v => le_iSup (fun v => chi q₀ v) v) hM hδM v

/-! ### Non-vacuity -/

/-- With `s = 0` the off-diagonal row sums vanish, so `δ = 0`. -/
example (V : Type*) :
    (⨆ u : V, rowSum (fun e => unitInterval.toENNReal ((fun _ => 0 : Sym2 V → I) e)) u) =
      0 := by
  simp

/-- `s = 0`, `q₀ = 0` on `ℕ`: the hypotheses of `lintegral_ghost_le_layer` and
`chi_union_le_of_bounds` hold (`X = 1`, `M = 1`, `δ = 0`), and the latter gives `χ_r ≤ χ_{q₀}`. -/
example :
    ∀ᵐ ω ∂(law (fun _ : Sym2 ℕ => (0 : I))), (cluster ω 0).Finite := by
  refine ae_cluster_finite_of_chi_lt_top ?_
  rw [chi_eq_one_of_offDiagonal_zero _ (fun _ _ _ => rfl)]
  exact ENNReal.one_lt_top

example : chi (fun e => σ (σ ((fun _ : Sym2 ℕ => (0 : I)) e) * σ ((fun _ => (0 : I)) e))) 0 ≤
    chi (fun _ : Sym2 ℕ => (0 : I)) 0 / (1 - 0 * 1) := by
  have hchi : ∀ v, chi (fun _ : Sym2 ℕ => (0 : I)) v = 1 :=
    chi_eq_one_of_offDiagonal_zero _ fun _ _ _ => rfl
  have := chi_union_le_of_bounds (fun _ : Sym2 ℕ => (0 : I)) (fun _ => 0) (δ := 0) (M := 1)
    (fun u => by simp) (fun v => (hchi v).le) ENNReal.one_lt_top (by simp) 0
  exact this

/-- On a finite vertex type every cluster is finite, so `lintegral_ghost_le_layer` applies to the
one-edge example below. -/
example : ∀ᵐ ω ∂(law (fun _ : Sym2 Bool => (0 : I))), (cluster ω false).Finite :=
  ae_of_all _ fun _ => Set.toFinite _

/-- One blue edge: on `Bool`, `q₀ = 0` and `s ≡ 1/2` (the only non-loop pair is
`s(false, true)`). Every off-diagonal row sum of `s` is `1/2`, `χ_{q₀} = 1`, so
`δ M = 1/2 < 1` and `chi_union_le_of_bounds` gives `χ_r ≤ 2`; the true value is `3/2`. -/
example : chi (fun e => σ (σ ((fun _ : Sym2 Bool => (0 : I)) e) *
      σ ((fun _ => (⟨1 / 2, by norm_num, by norm_num⟩ : I)) e))) false ≤ 2 := by
  have hchi : ∀ v, chi (fun _ : Sym2 Bool => (0 : I)) v = 1 :=
    chi_eq_one_of_offDiagonal_zero _ fun _ _ _ => rfl
  have hrow : ∀ u : Bool, rowSum (fun e => unitInterval.toENNReal
      ((fun _ => (⟨1 / 2, by norm_num, by norm_num⟩ : I)) e)) u ≤ 2⁻¹ := by
    intro u
    rw [rowSum_toENNReal, tsum_fintype, Fintype.sum_bool]
    have : ((unitInterval.toNNReal (⟨1 / 2, by norm_num, by norm_num⟩ : I) : NNReal) :
        ℝ≥0∞) = 2⁻¹ := by
      rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
      simp [ENNReal.ofReal_inv_of_pos]
    cases u <;> simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, this, add_zero,
      zero_add, le_refl]
  have := chi_union_le_of_bounds (fun _ : Sym2 Bool => (0 : I))
    (fun _ => (⟨1 / 2, by norm_num, by norm_num⟩ : I)) (δ := 2⁻¹) (M := 1)
    (fun u => by convert hrow u) (fun v => (hchi v).le) ENNReal.one_lt_top
    (by simp [ENNReal.inv_lt_one]) false
  exact this.trans_eq (by rw [hchi, mul_one, ENNReal.one_sub_inv_two, ENNReal.div_eq_inv_mul,
    inv_inv, mul_one])

end PercLib.Percolation.Bond

end
