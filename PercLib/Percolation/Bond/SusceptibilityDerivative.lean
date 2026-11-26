/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the derivative bound for the finite-volume susceptibility (wiki
integrated-susceptibility, tag TAVM) and the integrated mean-field inequality for the susceptibility
of a transitive kernel (tag MXGM). No upstream proof is copied, no definition is added and no Input
is introduced.
-/
module

public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.FiniteVolumeRusso
public import PercLib.Percolation.Bond.BoundaryContraction
public import PercLib.Percolation.Bond.Embedding
public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.Transport
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PercLib.Probability.CountableBK
public import PercLib.Probability.OpenEventHarris

/-! # The derivative of the finite-volume susceptibility

For a finite `F ⊆ V` and `o ∈ F` write `τ_F(u,v)` for connection inside `F`,
`χ_F(u) = ∑_{v ∈ F} τ_F(u,v)`, `M_F = max_{u ∈ F} χ_F(u)` and
`R_F = max_{u ∈ F} ∑_{v ∈ F, v ≠ u} J(u,v)`. In the intensity family
`q_β = 1 - e^{-β J}`, the map `β ↦ χ_F(o)` has at every `β > 0` a derivative `D` with
`0 ≤ D ≤ R_F χ_F(o) M_F` (`hasDerivAt_finiteChi_le`, tag TAVM).

Russo's formula writes `D` as a sum over pairs `e` inside `F` of
`J_e e^{-β J_e} P(e pivotal for o ↔_F v)`. If `e` is pivotal, then an open path from `o`
to `v` inside `F` through `e = s(a,b)` splits into disjoint witnesses of `o ↔_F a` and
`b ↔_F v` (`exists_disjointOccurrence_of_pivotal_conn`). BK on the pairs inside `F` and
a double count over the two orientations of each pair give the bound.

For a transitive kernel (`∀ x y, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e`) on a
countable `V` with finite off-diagonal row sum `R`, `M_F ≤ χ(β)` and `R_F ≤ R`, so the
finite-volume derivative is at most `R χ(β)²`. Integrating and exhausting `V` by finite sets
gives `χ(t) - χ(s) ≤ R ∫_s^t χ(u)² du` wherever `χ` is finite (`chi_sub_le_integral`,
tag MXGM), and hence `χ` is Lipschitz on compact subintervals (`lipschitzOnWith_chi`) and
locally Lipschitz on open intervals (`locallyLipschitzOn_chi`),
differentiable almost everywhere (`ae_differentiableAt_chi`) with derivative in `[0, R χ²]`
(`hasDerivAt_chi_mem_Icc`). Finally `1/χ(s) - 1/χ(t) ≤ R (t - s)` (`inv_chi_sub_le`).
The endpoint blow-up `χ(β) ≥ 1/(R (b - β))` when `χ(b) = ∞` is left to a later file, which
will carry its non-vacuity witness.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-! ### Pivotal pairs split an open path -/

/-- A walk through the edge `e` splits at `e`. -/
theorem walk_exists_append_cons_of_mem_edges {W : Type*} {G : SimpleGraph W}
    {x y : W} (p : G.Walk x y) {e : Sym2 W} (he : e ∈ p.edges) :
    ∃ a b, ∃ h : G.Adj a b, ∃ p₁ : G.Walk x a, ∃ p₂ : G.Walk b y,
      s(a, b) = e ∧ p = p₁.append (.cons h p₂) := by
  induction p with
  | nil => simp at he
  | @cons x x' y h q ih =>
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨x, x', h, .nil, q, rfl, rfl⟩
    · obtain ⟨a, b, hab, p₁, p₂, hab', rfl⟩ := ih he
      exact ⟨a, b, hab, .cons h p₁, p₂, hab', rfl⟩

/-- If opening `e` connects `x` to `y` and closing it disconnects them, then
`e = s(a,b)` with `a ≠ b`, and `x ↔ a` and `b ↔ y` occur disjointly. -/
theorem exists_disjointOccurrence_of_pivotal_conn {W : Type*} {σ : Config W} {e : Sym2 W}
    {x y : W} (h₁ : insert e σ ∈ conn x y) (h₂ : σ \ {e} ∉ conn x y) :
    ∃ a b, a ≠ b ∧ s(a, b) = e ∧ σ ∈ disjointOccurrence (conn x a) (conn b y) := by
  obtain ⟨p, hp⟩ := (show (openGraph (insert e σ)).Reachable x y from h₁).exists_isPath
  have hmem : ∀ f ∈ p.edges, f ∈ insert e σ := fun f hf => by
    have := p.edges_subset_edgeSet hf
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  have he : e ∈ p.edges := by
    by_contra he
    exact h₂ (mem_conn_of_walk_edges p fun f hf =>
      ⟨(mem_insert_iff.1 (hmem f hf)).resolve_left fun h => he (h ▸ hf),
        fun h => he ((mem_singleton_iff.1 h) ▸ hf)⟩)
  obtain ⟨a, b, hab, p₁, p₂, rfl, rfl⟩ := walk_exists_append_cons_of_mem_edges p he
  have hnd := hp.isTrail.edges_nodup
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, List.nodup_append,
    List.nodup_cons] at hnd
  obtain ⟨-, ⟨hab₂, -⟩, hdisj⟩ := hnd
  have hin : ∀ f, f ∈ p₁.edges ∨ f ∈ p₂.edges → f ≠ s(a, b) → f ∈ σ := by
    intro f hf hne
    have : f ∈ (p₁.append (.cons hab p₂)).edges := by
      rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons]
      rcases hf with hf | hf
      · exact List.mem_append_left _ hf
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    exact (mem_insert_iff.1 (hmem f this)).resolve_left hne
  have hab₁ : s(a, b) ∉ p₁.edges := fun h =>
    hdisj _ h _ (List.mem_cons_self) rfl
  refine ⟨a, b, hab.ne, rfl, ?_⟩
  rw [mem_disjointOccurrence_iff_open (isUpperSet_conn x a) (isUpperSet_conn b y)]
  refine ⟨{f | f ∈ p₁.edges}, {f | f ∈ p₂.edges}, List.finite_toSet _, List.finite_toSet _,
    ?_, fun f hf => hin f (Or.inl hf) fun h => hab₁ (h ▸ hf),
    fun f hf => hin f (Or.inr hf) fun h => hab₂ (h ▸ hf),
    mem_conn_of_walk_edges p₁ fun _ h => h, mem_conn_of_walk_edges p₂ fun _ h => h⟩
  rw [Set.disjoint_left]
  intro f h₁ h₂
  exact hdisj f h₁ f (List.mem_cons_of_mem _ h₂) rfl

/-! ### Pivotal pairs for internal connection -/

section Local

variable (S : Finset V)

theorem sym2_map_val_injective :
    Function.Injective (Sym2.map (Subtype.val : ↥(S : Set V) → V)) :=
  Sym2.map.injective Subtype.val_injective

/-- Disjoint occurrence in the restricted configuration lifts to internal connection
events. -/
theorem mem_disjointOccurrence_localConn_of_restrict {ω : Config V} {x a b y : (S : Set V)}
    (h : Sym2.map (Subtype.val : ↥(S : Set V) → V) ⁻¹' ω ∈
      disjointOccurrence (conn x a) (conn b y)) :
    ω ∈ disjointOccurrence {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x a}
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable b y} := by
  rw [mem_disjointOccurrence_iff_open (isUpperSet_conn x a) (isUpperSet_conn b y)] at h
  obtain ⟨F, H, hF, hH, hd, hFω, hHω, hFc, hHc⟩ := h
  have hinj := sym2_map_val_injective S
  rw [mem_disjointOccurrence_iff_open (isUpperSet_setOf_reachable_induce _ x a)
    (isUpperSet_setOf_reachable_induce _ b y)]
  refine ⟨Sym2.map Subtype.val '' F, Sym2.map Subtype.val '' H, hF.image _, hH.image _,
    (Set.disjoint_image_iff hinj).2 hd, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hFω hf
  · rintro _ ⟨f, hf, rfl⟩
    exact hHω hf
  · change ((openGraph _).induce (S : Set V)).Reachable x a
    rw [openGraph_induce, Set.preimage_image_eq _ hinj]
    exact hFc
  · change ((openGraph _).induce (S : Set V)).Reachable b y
    rw [openGraph_induce, Set.preimage_image_eq _ hinj]
    exact hHc

/-- A pair `e` inside `S` that is pivotal for `x ↔_S y` is `s(a,b)` with `a ≠ b` in `S`,
and `x ↔_S a`, `b ↔_S y` occur disjointly. -/
theorem exists_disjointOccurrence_of_pivotal_localConn {ω : Config V} {e : Sym2 V}
    (he : e ∈ S.sym2) {x y : (S : Set V)}
    (h₁ : insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y})
    (h₂ : ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}) :
    ∃ a b : (S : Set V), a ≠ b ∧ s((a : V), (b : V)) = e ∧
      ω ∈ disjointOccurrence {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x a}
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable b y} := by
  have hinj := sym2_map_val_injective S
  induction e using Sym2.ind with
  | h u v =>
  obtain ⟨hu, hv⟩ := Finset.mk_mem_sym2_iff.1 he
  set e' : Sym2 (S : Set V) := s(⟨u, hu⟩, ⟨v, hv⟩)
  have he' : Sym2.map Subtype.val e' = s(u, v) := rfl
  have hins : Sym2.map (Subtype.val : ↥(S : Set V) → V) ⁻¹' insert s(u, v) ω =
      insert e' (Sym2.map Subtype.val ⁻¹' ω) := by
    ext f
    simp only [mem_preimage, mem_insert_iff, ← he', hinj.eq_iff]
  have hdiff : Sym2.map (Subtype.val : ↥(S : Set V) → V) ⁻¹' (ω \ {s(u, v)}) =
      Sym2.map Subtype.val ⁻¹' ω \ {e'} := by
    ext f
    simp only [mem_preimage, mem_sdiff, mem_singleton_iff, ← he', hinj.eq_iff]
  have h₁' : insert e' (Sym2.map Subtype.val ⁻¹' ω) ∈ conn x y := by
    rw [← hins]
    have := h₁
    simp only [mem_ofPred_eq, openGraph_induce] at this
    exact this
  have h₂' : Sym2.map Subtype.val ⁻¹' ω \ {e'} ∉ conn x y := by
    rw [← hdiff]
    have := h₂
    simp only [mem_ofPred_eq, openGraph_induce] at this
    exact this
  obtain ⟨a, b, hab, habe, hd⟩ := exists_disjointOccurrence_of_pivotal_conn h₁' h₂'
  refine ⟨a, b, hab, ?_, mem_disjointOccurrence_localConn_of_restrict S hd⟩
  rw [← he', ← habe]
  rfl

/-- Internal connection inside `S` is a cylinder event on the pairs inside `S`. -/
theorem localConn_eq_preimage_restrict (x y : (S : Set V)) :
    {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} =
      (fun ω : Config V => (Subtype.val ⁻¹' ω : Set (S.sym2 : Set (Sym2 V)))) ⁻¹'
        {η | Subtype.val '' η ∈
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, Subtype.image_preimage_coe]
  rw [Set.inter_comm]
  exact localConn_dependsOn_sym2 S x y ω

/-- **BK for internal connections.** -/
theorem measureReal_disjointOccurrence_localConn_le (q : Sym2 V → unitInterval)
    (x a b y : (S : Set V)) :
    (law q).real (disjointOccurrence
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x a}
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable b y}) ≤
      (law q).real {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x a} *
        (law q).real {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable b y} := by
  rw [localConn_eq_preimage_restrict S x a, localConn_eq_preimage_restrict S b y]
  refine cylinder_profile_bk q S.sym2 _ _ ?_ ?_
  · exact fun η η' h hη => isUpperSet_setOf_reachable_induce _ x a (image_mono h) hη
  · exact fun η η' h hη => isUpperSet_setOf_reachable_induce _ b y (image_mono h) hη

open Classical in
/-- The probability that `e` is pivotal for `x ↔_S y` is at most
`∑ τ_S(x,a) τ_S(b,y)` over the two orientations `(a,b)` of `e`. -/
theorem measureReal_pivotal_localConn_le (q : Sym2 V → unitInterval) {e : Sym2 V}
    (he : e ∈ S.sym2) (x y : (S : Set V)) :
    (law q).real {ω | insert e ω ∈
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
        ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}} ≤
      ∑ p ∈ (Finset.univ : Finset (↥(S : Set V) × ↥(S : Set V))).filter
          (fun p => p.1 ≠ p.2 ∧ s((p.1 : V), (p.2 : V)) = e),
        (law q).real {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x p.1} *
          (law q).real {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable p.2 y} := by
  have hsub : {ω | insert e ω ∈
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
        ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}} ⊆
      ⋃ p ∈ (Finset.univ : Finset (↥(S : Set V) × ↥(S : Set V))).filter
          (fun p => p.1 ≠ p.2 ∧ s((p.1 : V), (p.2 : V)) = e),
        disjointOccurrence
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x p.1}
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable p.2 y} := by
    rintro ω ⟨h₁, h₂⟩
    obtain ⟨a, b, hab, habe, hd⟩ := exists_disjointOccurrence_of_pivotal_localConn S he h₁ h₂
    exact mem_iUnion₂.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, hab, habe⟩, hd⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  exact Finset.sum_le_sum fun p _ => measureReal_disjointOccurrence_localConn_le S q _ _ _ _

open Classical in
/-- The Russo derivative of `χ_S(o)` is at most `R_S χ_S(o) M_S`. -/
theorem russo_finiteChi_le (J : Sym2 V → ℝ≥0) (o : (S : Set V)) {β : ℝ} (hβ : 0 ≤ β) :
    (∑ y : (S : Set V), ∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}}) ≤
      Finset.univ.sup' ⟨o, Finset.mem_univ o⟩
          (fun u : (S : Set V) => ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) *
        (∑ y : (S : Set V), (law (intensityProfile J β.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}) *
        Finset.univ.sup' ⟨o, Finset.mem_univ o⟩ (fun u : (S : Set V) =>
          ∑ y : (S : Set V), (law (intensityProfile J β.toNNReal)).real
            {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable u y}) := by
  set μ := law (intensityProfile J β.toNNReal)
  set τ : ↥(S : Set V) → ↥(S : Set V) → ℝ := fun x y =>
    μ.real {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}
  set M := Finset.univ.sup' ⟨o, Finset.mem_univ o⟩ (fun u : (S : Set V) => ∑ y, τ u y)
  set R := Finset.univ.sup' ⟨o, Finset.mem_univ o⟩
    (fun u : (S : Set V) => ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ))
  set fib : Sym2 V → Finset (↥(S : Set V) × ↥(S : Set V)) := fun e =>
    (Finset.univ : Finset (↥(S : Set V) × ↥(S : Set V))).filter
      (fun p => p.1 ≠ p.2 ∧ s((p.1 : V), (p.2 : V)) = e)
  have hτ0 : ∀ x y, 0 ≤ τ x y := fun _ _ => measureReal_nonneg
  have hM : ∀ u, ∑ y, τ u y ≤ M := fun u =>
    Finset.le_sup' (fun u : (S : Set V) => ∑ y, τ u y) (Finset.mem_univ u)
  have hR : ∀ u, (∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) ≤ R :=
    fun u => Finset.le_sup' (fun u : (S : Set V) =>
      ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) (Finset.mem_univ u)
  calc _ ≤ ∑ y : (S : Set V), ∑ e ∈ S.sym2, (J e : ℝ) *
          ∑ p ∈ fib e, τ o p.1 * τ p.2 y := by
        refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun e he => ?_
        have hexp : Real.exp (-β * J e) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [(J e).coe_nonneg])
        calc (J e : ℝ) * Real.exp (-β * J e) * _
            ≤ (J e : ℝ) * 1 * _ := by
              gcongr
          _ ≤ _ := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left (measureReal_pivotal_localConn_le S _ he o y)
                (J e).coe_nonneg
    _ = ∑ e ∈ S.sym2, ∑ p ∈ fib e, (J e : ℝ) * τ o p.1 * ∑ y, τ p.2 y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun y _ => ?_
        ring
    _ ≤ ∑ e ∈ S.sym2, ∑ p ∈ fib e, (J e : ℝ) * τ o p.1 * M := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul_of_nonneg_left (hM p.2) (mul_nonneg (J e).coe_nonneg (hτ0 _ _))
    _ = ∑ p ∈ (Finset.univ : Finset (↥(S : Set V) × ↥(S : Set V))).filter
          (fun p => p.1 ≠ p.2), (J s((p.1 : V), (p.2 : V)) : ℝ) * τ o p.1 * M := by
        rw [← Finset.sum_fiberwise_of_maps_to (t := S.sym2)
          (g := fun p : ↥(S : Set V) × ↥(S : Set V) => s((p.1 : V), (p.2 : V)))]
        · refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.filter_filter]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [(Finset.mem_filter.1 hp).2.2]
        · intro p _
          exact Finset.mk_mem_sym2_iff.2 ⟨p.1.2, p.2.2⟩
    _ = M * ∑ a : (S : Set V), τ o a *
          ∑ b : (S : Set V), if b = a then 0 else (J s((a : V), b) : ℝ) := by
        rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hab : b = a
        · simp [hab]
        · rw [ite_eq_left (Ne.symm hab), ite_eq_right hab]
          ring
    _ ≤ M * ∑ a : (S : Set V), τ o a * R := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hR a) (hτ0 _ _)) ?_
        exact (Finset.sum_nonneg fun y _ => hτ0 o y).trans (hM o)
    _ = R * (∑ y, τ o y) * M := by
        rw [← Finset.sum_mul]
        ring

open Classical in
/-- **Right derivative.** At every `β ≥ 0` the finite-volume susceptibility
`β ↦ χ_S(o) = ∑_{y ∈ S} τ_S(o,y)` has a derivative `D` within `[0, ∞)` with
`0 ≤ D ≤ R_S χ_S(o) M_S`, where `R_S = max_{u ∈ S} ∑_{v ∈ S, v ≠ u} J(u,v)` and
`M_S = max_{u ∈ S} χ_S(u)`. -/
theorem hasDerivWithinAt_finiteChi_le (J : Sym2 V → ℝ≥0) (o : (S : Set V)) {β : ℝ}
    (hβ : 0 ≤ β) :
    ∃ D, HasDerivWithinAt (fun b : ℝ => ∑ y : (S : Set V),
        (law (intensityProfile J b.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}) D (Ici 0) β ∧
      0 ≤ D ∧
      D ≤ Finset.univ.sup' ⟨o, Finset.mem_univ o⟩
          (fun u : (S : Set V) => ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) *
        (∑ y : (S : Set V), (law (intensityProfile J β.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}) *
        Finset.univ.sup' ⟨o, Finset.mem_univ o⟩ (fun u : (S : Set V) =>
          ∑ y : (S : Set V), (law (intensityProfile J β.toNNReal)).real
            {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable u y}) :=
  ⟨_, sum_law_localConn_hasDerivWithinAt J S o hβ,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun e _ => mul_nonneg
      (mul_nonneg (J e).coe_nonneg (Real.exp_pos _).le) measureReal_nonneg,
    russo_finiteChi_le S J o hβ⟩

open Classical in
/-- **TAVM.** At every `β > 0` the finite-volume susceptibility `β ↦ χ_S(o)` has a
derivative `D` with `0 ≤ D ≤ R_S χ_S(o) M_S`. -/
@[tag "TAVM"]
theorem hasDerivAt_finiteChi_le (J : Sym2 V → ℝ≥0) (o : (S : Set V)) {β : ℝ}
    (hβ : 0 < β) :
    ∃ D, HasDerivAt (fun b : ℝ => ∑ y : (S : Set V),
        (law (intensityProfile J b.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}) D β ∧
      0 ≤ D ∧
      D ≤ Finset.univ.sup' ⟨o, Finset.mem_univ o⟩
          (fun u : (S : Set V) => ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) *
        (∑ y : (S : Set V), (law (intensityProfile J β.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}) *
        Finset.univ.sup' ⟨o, Finset.mem_univ o⟩ (fun u : (S : Set V) =>
          ∑ y : (S : Set V), (law (intensityProfile J β.toNNReal)).real
            {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable u y}) := by
  obtain ⟨D, hD, h0, hle⟩ := hasDerivWithinAt_finiteChi_le S J o hβ.le
  exact ⟨D, hD.hasDerivAt (Ici_mem_nhds hβ), h0, hle⟩

end Local

/-! ### Transitive kernels -/

section Transitive

/-- A profile invariant under a vertex bijection gives an invariant law. -/
theorem law_map_image_of_invariant {q : Sym2 V → unitInterval} (σ : V ≃ V)
    (hσ : ∀ e, q (Sym2.map σ e) = q e) :
    (law q).map (fun ω => Sym2.map σ '' ω) = law q := by
  have himg : (fun ω : Config V => Sym2.map σ '' ω) =
      fun ω => (Sym2.map σ.symm.toEmbedding ⁻¹' ω : Config V) := by
    funext ω
    ext e
    exact mem_image_sym2Map_iff σ ω e
  rw [himg, law_map_preimage_sym2Map]
  congr 1
  funext e
  have h := hσ (Sym2.map σ.symm e)
  rw [Sym2.map_map, σ.self_comp_symm, Sym2.map_id, id] at h
  exact h.symm

open Classical in
/-- For a transitive kernel, the off-diagonal row sums do not depend on the vertex. -/
theorem rowSum_eq_of_transitive (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (u o : V) :
    rowSum (fun e => (J e : ℝ≥0∞)) u =
      rowSum (fun e => (J e : ℝ≥0∞)) o := by
  obtain ⟨σ, hσo, hσ⟩ := hJ o u
  rw [← hσo, rowSum_def, rowSum_def, ← σ.tsum_eq]
  refine tsum_congr fun w => ?_
  rw [σ.injective.eq_iff, ← Sym2.map_mk, hσ]

end Transitive

/-! ### Finite volume and the susceptibility -/

section Exhaustion

/-- The finite-volume susceptibility is at most the susceptibility. -/
theorem finiteChi_le_chi [Countable V] (q : Sym2 V → unitInterval) (S : Finset V)
    (x : (S : Set V)) :
    ∑ y : (S : Set V), law q {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ≤
      chi q x := by
  calc _ ≤ ∑ y : (S : Set V), tau q x y :=
        Finset.sum_le_sum fun y _ => measure_mono fun ω h => conn_of_localConn ω _ x y h
    _ = ∑ y ∈ S, tau q x y := Finset.sum_finset_coe (fun y => tau q x y) S
    _ ≤ ∑' y, tau q x y := ENNReal.sum_le_tsum S
    _ = chi q x := (chi_eq_tsum_tau q x).symm

open Classical in
/-- On a countable vertex set the susceptibility is the supremum of finite-volume
susceptibilities along an exhaustion by finite sets containing the root. -/
theorem exists_chi_eq_iSup_finiteChi [Countable V] (q : Sym2 V → unitInterval) (o : V) :
    ∃ S : ℕ → Finset V, ∃ ho : ∀ n, o ∈ S n, chi q o = ⨆ n, ∑ y : (S n : Set V),
      law q {ω : Config V | ((openGraph ω).induce (S n : Set V)).Reachable
        ⟨o, Finset.mem_coe.2 (ho n)⟩ y} := by
  have : Nonempty V := ⟨o⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat V
  set S : ℕ → Finset V := fun n => insert o ((Finset.range n).image f)
  have hS : Monotone fun n => (S n : Set V) := fun m n hmn => Finset.coe_subset.2
    (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.range_mono hmn)))
  have hcover : ∀ v, ∃ n, v ∈ (S n : Set V) := fun v => by
    obtain ⟨k, rfl⟩ := hf v
    exact ⟨k + 1, Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem f (Finset.mem_range.2 k.lt_succ_self)))⟩
  have ho : ∀ n, o ∈ S n := fun n => Finset.mem_insert_self _ _
  refine ⟨S, ho, ?_⟩
  rw [chi_eq_iSup_lintegral_induce q hS hcover o]
  refine iSup_congr fun n => ?_
  rw [lintegral_encard_induce,
    tsum_eq_sum (s := S n) fun v hv => law_induce_conn_eq_zero_of_notMem (Or.inr hv),
    ← Finset.sum_finset_coe _ (S n)]
  refine Finset.sum_congr rfl fun y _ => congrArg (law q) ?_
  ext ω
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, y.2, h⟩⟩

end Exhaustion

/-! ### MXGM: the integrated differential inequality -/

section MXGM

variable [Countable V] (J : Sym2 V → ℝ≥0)
  (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)

include hJ in
open Classical in
/-- On a transitive kernel the Russo derivative of a finite-volume susceptibility is at most
`R χ(β)²`, where `R` is the off-diagonal row sum of `J` and `χ(β)` the susceptibility. -/
theorem russo_finiteChi_le_rowSum_mul_sq (S : Finset V) (o : (S : Set V)) {β : ℝ}
    (hβ : 0 ≤ β) (hχ : chi (intensityProfile J β.toNNReal) o ≠ ⊤)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) (o : V) ≠ ⊤) :
    (∑ y : (S : Set V), ∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y}}) ≤
      (rowSum (fun e => (J e : ℝ≥0∞)) (o : V)).toReal *
        (chi (intensityProfile J β.toNNReal) o).toReal ^ 2 := by
  set q := intensityProfile J β.toNNReal
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) (o : V)).toReal
  set χ := (chi q o).toReal
  have hχS : ∀ u : (S : Set V), ∑ y : (S : Set V), (law q).real
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable u y} ≤ χ := by
    intro u
    have hu : chi q u = chi q o := chi_eq_of_transitive J hJ _ u o
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum fun y _ => measure_ne_top _ _]
    exact ENNReal.toReal_mono hχ ((finiteChi_le_chi q S u).trans hu.le)
  have hRS : ∀ u : (S : Set V),
      (∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) ≤ R := by
    intro u
    have hrow := rowSum_eq_of_transitive J hJ (u : V) (o : V)
    have h1 : (∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) =
        (∑ v ∈ S, if v = (u : V) then 0 else (J s((u : V), v) : ℝ≥0∞)).toReal := by
      rw [ENNReal.toReal_sum fun v _ => by split_ifs <;> simp,
        ← Finset.sum_finset_coe _ S]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v = u
      · simp [hv]
      · rw [ite_eq_right hv, ite_eq_right (fun h => hv (Subtype.ext h))]
        simp
    rw [h1]
    refine ENNReal.toReal_mono hR ?_
    rw [← hrow, rowSum_def]
    exact ENNReal.sum_le_tsum S
  have hnn : ∀ u y : (S : Set V), 0 ≤ (law q).real
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable u y} :=
    fun _ _ => measureReal_nonneg
  refine (russo_finiteChi_le S J o hβ).trans ?_
  have hR0 : 0 ≤ Finset.univ.sup' ⟨o, Finset.mem_univ o⟩
      (fun u : (S : Set V) => ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) :=
    (Finset.sum_nonneg fun v _ => by split_ifs <;> simp).trans
      (Finset.le_sup' (fun u : (S : Set V) =>
        ∑ v : (S : Set V), if v = u then 0 else (J s((u : V), v) : ℝ)) (Finset.mem_univ o))
  have hχS0 : 0 ≤ ∑ y : (S : Set V), (law q).real
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o y} :=
    Finset.sum_nonneg fun y _ => hnn o y
  rw [sq, ← mul_assoc]
  refine mul_le_mul (mul_le_mul (Finset.sup'_le _ _ fun u _ => hRS u) (hχS o) hχS0
    (hR0.trans (Finset.sup'_le _ _ fun u _ => hRS u)))
    (Finset.sup'_le _ _ fun u _ => hχS u)
    (hχS0.trans (Finset.le_sup' (fun u : (S : Set V) => ∑ y : (S : Set V), (law q).real
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable u y}) (Finset.mem_univ o)))
    (mul_nonneg (hR0.trans (Finset.sup'_le _ _ fun u _ => hRS u)) (hχS0.trans (hχS o)))

include hJ in
/-- **Integrated form.** For a transitive kernel with finite off-diagonal row sum `R`,
if `χ(β) = chi q_β o` is finite for `β ∈ (a,b)`, `0 ≤ a`, then for `a < s ≤ t < b`,
`χ(t) - χ(s) ≤ R ∫_s^t χ(u)² du`. -/
theorem chi_sub_le_integral (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) {s t : ℝ}
    (hs : a < s) (hst : s ≤ t) (ht : t < b) :
    (chi (intensityProfile J t.toNNReal) o).toReal -
        (chi (intensityProfile J s.toNNReal) o).toReal ≤
      (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal *
        ∫ u in s..t, (chi (intensityProfile J u.toNNReal) o).toReal ^ 2 := by
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  have hmem : ∀ u ∈ Icc s t, u ∈ Ioo a b := fun u hu =>
    ⟨hs.trans_le hu.1, hu.2.trans_lt ht⟩
  have hmono : MonotoneOn (fun u => R * χ u ^ 2) (Icc s t) := by
    intro u hu v hv huv
    have hle : χ u ≤ χ v := ENNReal.toReal_mono (hfin v (hmem v hv))
      (chi_mono (fun e => intensityProfile_mono J (Real.toNNReal_le_toNNReal huv) e) o)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2)
      ENNReal.toReal_nonneg
  have hint : IntegrableOn (fun u => R * χ u ^ 2) (Icc s t) :=
    hmono.integrableOn_isCompact isCompact_Icc
  set I := ∫ u in s..t, R * χ u ^ 2
  have hI : I = R * ∫ u in s..t, χ u ^ 2 := intervalIntegral.integral_const_mul _ _
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hst fun u _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have ha0 : ∀ u ∈ Icc s t, 0 ≤ u := fun u hu => ha.trans (hs.le.trans hu.1)
  -- Every finite-volume susceptibility at `t` is at most `χ(s) + I`.
  have hfinite : ∀ (S : Finset V) (hoS : o ∈ S),
      ∑ y : (S : Set V), law (intensityProfile J t.toNNReal)
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable
          ⟨o, Finset.mem_coe.2 hoS⟩ y} ≤ ENNReal.ofReal (χ s + I) := by
    intro S hoS
    set o' : (S : Set V) := ⟨o, Finset.mem_coe.2 hoS⟩
    set g : ℝ → ℝ := fun b => ∑ y : (S : Set V), (law (intensityProfile J b.toNNReal)).real
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable o' y}
    have hgs : g s ≤ χ s := by
      simp only [g, measureReal_def]
      rw [← ENNReal.toReal_sum fun y _ => measure_ne_top _ _]
      exact ENNReal.toReal_mono (hfin s (hmem s ⟨le_rfl, hst⟩)) (finiteChi_le_chi _ S o')
    have hgt : g t - g s ≤ I := by
      refine intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst
        (fun x hx => ((sum_law_localConn_hasDerivWithinAt J S o' (ha0 x hx)).continuousWithinAt
          ).mono fun y hy => ha0 y hy)
        (fun x hx => ((sum_law_localConn_hasDerivWithinAt J S o'
          (ha0 x (Ioo_subset_Icc_self hx))).hasDerivAt
            (Ici_mem_nhds ((ha.trans_lt hs).trans hx.1))).hasDerivWithinAt) hint
        (fun x hx => ?_)
      exact russo_finiteChi_le_rowSum_mul_sq J hJ S o' (ha0 x (Ioo_subset_Icc_self hx))
        (hfin x (hmem x (Ioo_subset_Icc_self hx))) hR
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _)
      (by linarith [ENNReal.toReal_nonneg (a := chi (intensityProfile J s.toNNReal) o)]),
      ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
    change g t ≤ χ s + I
    linarith
  obtain ⟨S, hoS, hsup⟩ := exists_chi_eq_iSup_finiteChi (intensityProfile J t.toNNReal) o
  have hle : chi (intensityProfile J t.toNNReal) o ≤ ENNReal.ofReal (χ s + I) := by
    rw [hsup]
    exact iSup_le fun n => hfinite (S n) (hoS n)
  have := ENNReal.toReal_le_of_le_ofReal (by
    linarith [ENNReal.toReal_nonneg (a := chi (intensityProfile J s.toNNReal) o)]) hle
  rw [← hI]
  change χ t - χ s ≤ I
  linarith

/-- The susceptibility is nondecreasing in the parameter where it is finite. -/
theorem monotoneOn_toReal_chi (o : V) {A : Set ℝ}
    (hfin : ∀ β ∈ A, chi (intensityProfile J β.toNNReal) o ≠ ⊤) :
    MonotoneOn (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) A :=
  fun _ _ v hv huv => ENNReal.toReal_mono (hfin v hv)
    (chi_mono (fun e => intensityProfile_mono J (Real.toNNReal_le_toNNReal huv) e) o)

include hJ in
/-- **Lipschitz form.** Under the hypotheses of `chi_sub_le_integral`, the
susceptibility is Lipschitz on every `[s,t] ⊆ (a,b)`, with constant `R χ(t)²`. -/
theorem lipschitzOnWith_chi (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) {s t : ℝ}
    (hs : a < s) (ht : t < b) :
    LipschitzOnWith (Real.toNNReal ((rowSum (fun e => (J e : ℝ≥0∞)) o).toReal *
        (chi (intensityProfile J t.toNNReal) o).toReal ^ 2))
      (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) (Icc s t) := by
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  have hmem : ∀ u ∈ Icc s t, u ∈ Ioo a b := fun u hu =>
    ⟨hs.trans_le hu.1, hu.2.trans_lt ht⟩
  have hmono : MonotoneOn χ (Icc s t) :=
    (monotoneOn_toReal_chi J o hfin).mono fun u hu => hmem u hu
  -- One-sided bound for `u ≤ v`.
  have key : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, u ≤ v → χ v - χ u ≤ R * χ t ^ 2 * (v - u) := by
    intro u hu v hv huv
    refine (chi_sub_le_integral J hJ o hR ha hfin (hmem u hu).1 huv (hmem v hv).2).trans ?_
    have hsq : MonotoneOn (fun w => χ w ^ 2) (Icc s t) := fun w hw w' hw' hww' =>
      pow_le_pow_left₀ ENNReal.toReal_nonneg (hmono hw hw' hww') 2
    have hsub : Icc u v ⊆ Icc s t := Icc_subset_Icc hu.1 hv.2
    have hint : IntervalIntegrable (fun w => χ w ^ 2) MeasureTheory.volume u v :=
      (hsq.mono (by rw [uIcc_of_le huv]; exact hsub)).intervalIntegrable
    have : ∫ w in u..v, χ w ^ 2 ≤ ∫ w in u..v, χ t ^ 2 :=
      intervalIntegral.integral_mono_on huv hint intervalIntegrable_const fun w hw =>
        hsq (hsub hw) ⟨(hu.1.trans huv).trans hv.2, le_rfl⟩ (hsub hw).2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
    nlinarith
  refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.2 (hmono hx hy hxy)), abs_of_nonpos (sub_nonpos.2 hxy)]
    linarith [key x hx y hy hxy]
  · rw [abs_of_nonneg (sub_nonneg.2 (hmono hy hx hxy)), abs_of_nonneg (sub_nonneg.2 hxy)]
    exact key y hy x hx hxy

/-! ### MXGM: the reciprocal estimate -/

omit [Countable V] in
/-- A uniform step bound `g(u) - g(v) ≤ A (v-u) + B (v-u)²` gives `g(s) - g(t) ≤ A (t-s)`. -/
theorem sub_le_of_step_le {g : ℝ → ℝ} {s t A B : ℝ} (hst : s ≤ t) (hB : 0 ≤ B)
    (hstep : ∀ u v, s ≤ u → u ≤ v → v ≤ t → g u - g v ≤ A * (v - u) + B * (v - u) ^ 2) :
    g s - g t ≤ A * (t - s) := by
  have hbound : ∀ N : ℕ, 0 < N → g s - g t ≤ A * (t - s) + B * (t - s) ^ 2 / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
    set h := (t - s) / N
    have hh : 0 ≤ h := div_nonneg (sub_nonneg.2 hst) hN'.le
    set x : ℕ → ℝ := fun k => s + k * h
    have hxN : x N = t := by
      simp only [x, h]
      field_simp
      ring
    have hx : ∀ k ≤ N, s ≤ x k ∧ x k ≤ t := by
      intro k hk
      refine ⟨le_add_of_nonneg_right (mul_nonneg k.cast_nonneg hh), ?_⟩
      rw [← hxN]
      have := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk : (k : ℝ) ≤ N) hh
      simp only [x]
      linarith
    have htel : g s - g t = ∑ k ∈ Finset.range N, (g (x k) - g (x (k + 1))) := by
      rw [Finset.sum_range_sub', ← hxN]
      simp [x]
    have hstep' : ∀ k ∈ Finset.range N, g (x k) - g (x (k + 1)) ≤ A * h + B * h ^ 2 := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hdiff : x (k + 1) - x k = h := by
        simp only [x]
        push_cast
        ring
      have := hstep (x k) (x (k + 1)) (hx k hk'.le).1 (by linarith) (hx (k + 1) hk').2
      rwa [hdiff] at this
    rw [htel]
    refine (Finset.sum_le_sum hstep').trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [h]
    field_simp
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (B * (t - s) ^ 2 / ε)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (mul_nonneg hB (sq_nonneg _)) hε.le) hN
    exact_mod_cast this
  refine (hbound N hN0).trans_lt ?_
  have : B * (t - s) ^ 2 / N < ε := by
    rw [div_lt_iff₀ (Nat.cast_pos.2 hN0)]
    rw [div_lt_iff₀ hε] at hN
    linarith
  linarith

include hJ in
/-- `χ(v) - χ(u) ≤ R (v - u) χ(v)²` for `a < u ≤ v < b`. -/
theorem chi_sub_le_mul_sq (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) {u v : ℝ}
    (hu : a < u) (huv : u ≤ v) (hv : v < b) :
    (chi (intensityProfile J v.toNNReal) o).toReal -
        (chi (intensityProfile J u.toNNReal) o).toReal ≤
      (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal * (v - u) *
        (chi (intensityProfile J v.toNNReal) o).toReal ^ 2 := by
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hmono := monotoneOn_toReal_chi J o hfin
  have hmem : ∀ w, u ≤ w → w ≤ v → w ∈ Ioo a b := fun w h1 h2 =>
    ⟨hu.trans_le h1, h2.trans_lt hv⟩
  have hint := chi_sub_le_integral J hJ o hR ha hfin hu huv hv
  have hsq : ∫ w in u..v, χ w ^ 2 ≤ (v - u) * χ v ^ 2 := by
    have hsqm : MonotoneOn (fun w => χ w ^ 2) (Icc u v) := fun w hw w' hw' hww' =>
      pow_le_pow_left₀ ENNReal.toReal_nonneg (hmono (hmem w hw.1 hw.2)
        (hmem w' hw'.1 hw'.2) hww') 2
    have hii : IntervalIntegrable (fun w => χ w ^ 2) MeasureTheory.volume u v :=
      (hsqm.mono (by rw [uIcc_of_le huv])).intervalIntegrable
    have := intervalIntegral.integral_mono_on huv hii intervalIntegrable_const
      fun w hw => hsqm hw ⟨huv, le_rfl⟩ hw.2
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have := mul_le_mul_of_nonneg_left hsq hR0
  change χ v - χ u ≤ _ at hint
  change χ v - χ u ≤ R * (v - u) * χ v ^ 2
  nlinarith

include hJ in
/-- **Comparison for `1/χ`.** Under the hypotheses of `chi_sub_le_integral`,
`1/χ(s) - 1/χ(t) ≤ R (t - s)` for `a < s ≤ t < b`. -/
theorem inv_chi_sub_le (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) {s t : ℝ}
    (hs : a < s) (hst : s ≤ t) (ht : t < b) :
    1 / (chi (intensityProfile J s.toNNReal) o).toReal -
        1 / (chi (intensityProfile J t.toNNReal) o).toReal ≤
      (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal * (t - s) := by
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  have hmem : ∀ u, s ≤ u → u ≤ t → u ∈ Ioo a b := fun u h1 h2 =>
    ⟨hs.trans_le h1, h2.trans_lt ht⟩
  have hone : ∀ u, s ≤ u → u ≤ t → 1 ≤ χ u := fun u h1 h2 => by
    have := ENNReal.toReal_mono (hfin u (hmem u h1 h2))
      (one_le_chi (intensityProfile J u.toNNReal) o)
    simpa using this
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hmono := monotoneOn_toReal_chi J o hfin
  set C := R * χ t ^ 2
  have hC : 0 ≤ C := mul_nonneg hR0 (sq_nonneg _)
  refine sub_le_of_step_le (g := fun u => 1 / χ u) hst (mul_nonneg hR0 hC) ?_
  intro u v hu huv hv
  have hu1 := hone u hu (huv.trans hv)
  have hv1 := hone v (hu.trans huv) hv
  have hχuv : χ u ≤ χ v := hmono (hmem u hu (huv.trans hv)) (hmem v (hu.trans huv) hv) huv
  have hχvt : χ v ≤ χ t :=
    hmono (hmem v (hu.trans huv) hv) (hmem t (hu.trans (huv.trans hv)) le_rfl) hv
  have hdiff : χ v - χ u ≤ R * (v - u) * χ v ^ 2 :=
    chi_sub_le_mul_sq J hJ o hR ha hfin (hmem u hu (huv.trans hv)).1 huv
      (hmem v (hu.trans huv) hv).2
  -- `χ(v) - χ(u) ≤ C (v - u)`.
  have hlip : χ v - χ u ≤ C * (v - u) := by
    have : R * (v - u) * χ v ^ 2 ≤ R * (v - u) * χ t ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hχvt 2)
        (mul_nonneg hR0 (sub_nonneg.2 huv))
    simp only [C]
    nlinarith
  have hu0 : 0 < χ u := by linarith
  have hv0 : 0 < χ v := by linarith
  change 1 / χ u - 1 / χ v ≤ R * (v - u) + R * C * (v - u) ^ 2
  rw [div_sub_div _ _ hu0.ne' hv0.ne', div_le_iff₀ (mul_pos hu0 hv0)]
  -- `χ v - χ u ≤ R (v-u) χ v²` and `χ v ≤ χ u (1 + C (v - u))`.
  have h1 : χ v ≤ χ u * (1 + C * (v - u)) := by nlinarith
  have hvu : 0 ≤ v - u := sub_nonneg.2 huv
  nlinarith [mul_nonneg hR0 hvu, mul_nonneg (mul_nonneg hR0 hvu) hv0.le]

include hJ in
/-- **Derivative.** Wherever `β ↦ χ(β)` is differentiable in `(a,b)`, its derivative
lies in `[0, R χ(β)²]`. -/
theorem hasDerivAt_chi_mem_Icc (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) {β D : ℝ}
    (hβ : β ∈ Ioo a b)
    (hD : HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) D β) :
    0 ≤ D ∧ D ≤ (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal *
      (chi (intensityProfile J β.toNNReal) o).toReal ^ 2 := by
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  have hslope : Filter.Tendsto (slope χ β) (nhdsWithin β (Ioi β)) (nhds D) := by
    have := hasDerivWithinAt_iff_tendsto_slope.1 (hD.hasDerivWithinAt (s := Ioi β))
    rwa [Set.sdiff_singleton_eq_self (show β ∉ Ioi β from lt_irrefl β)] at this
  have hev : ∀ᶠ y in nhdsWithin β (Ioi β), y ∈ Ioo β b := Ioo_mem_nhdsGT hβ.2
  have hmono := monotoneOn_toReal_chi J o hfin
  have hg : Filter.Tendsto (fun y => R * χ y ^ 2) (nhdsWithin β (Ioi β))
      (nhds (R * χ β ^ 2)) :=
    ((hD.continuousAt.pow 2).const_mul R).tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · refine ge_of_tendsto hslope (hev.mono fun y hy => ?_)
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.2 (hmono hβ ⟨hβ.1.trans hy.1, hy.2⟩ hy.1.le))
      (sub_nonneg.2 hy.1.le)
  · refine le_of_tendsto_of_tendsto hslope hg (hev.mono fun y hy => ?_)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hy.1)]
    have := chi_sub_le_mul_sq J hJ o hR ha hfin hβ.1 hy.1.le hy.2
    change χ y - χ β ≤ R * (y - β) * χ y ^ 2 at this
    linarith

include hJ in
/-- **Almost-everywhere differentiability.** `β ↦ χ(β)` is differentiable at almost
every `β ∈ (a,b)` (Rademacher, applied on compact subintervals). -/
theorem ae_differentiableAt_chi (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) :
    ∀ᵐ β, β ∈ Ioo a b →
      DifferentiableAt ℝ (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) β := by
  rcases le_or_gt b a with hba | hab
  · exact Filter.Eventually.of_forall fun β hβ => absurd (hβ.1.trans hβ.2) (not_lt.2 hba)
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  set d : ℕ → ℝ := fun n => (b - a) / (n + 2)
  have hd : ∀ n, 0 < d n := fun n => div_pos (sub_pos.2 hab) (by positivity)
  have hd2 : ∀ n, d n < (b - a) / 2 + (b - a) / 2 := fun n => by
    have : d n ≤ (b - a) / 2 := div_le_div_of_nonneg_left (sub_pos.2 hab).le two_pos
      (by have := n.cast_nonneg (α := ℝ); linarith)
    linarith [hd n]
  have hae : ∀ n, ∀ᵐ x, x ∈ Icc (a + d n) (b - d n) →
      DifferentiableWithinAt ℝ χ (Icc (a + d n) (b - d n)) x := fun n =>
    LipschitzOnWith.ae_differentiableWithinAt_of_mem_of_real
      (lipschitzOnWith_chi J hJ o hR ha hfin (s := a + d n) (t := b - d n)
        (by linarith [hd n]) (by linarith [hd n]))
  filter_upwards [ae_all_iff.2 hae] with β hβ hmem
  set m := min (β - a) (b - β)
  have hm : 0 < m := lt_min (sub_pos.2 hmem.1) (sub_pos.2 hmem.2)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / m)
  have hdn : d n < m := by
    rw [div_lt_iff₀ hm] at hn
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have h1 : a + d n < β := by linarith [min_le_left (β - a) (b - β)]
  have h2 : β < b - d n := by linarith [min_le_right (β - a) (b - β)]
  exact (hβ n ⟨h1.le, h2.le⟩).differentiableAt (Icc_mem_nhds h1 h2)

end MXGM

/-! ### Non-vacuity -/

/-- `F = {o}`: `χ_F ≡ 1`, so the derivative of `hasDerivAt_finiteChi_le` is `0`. -/
example (J : Sym2 V → ℝ≥0) (o : V) {β : ℝ} (hβ : 0 < β) :
    ∃ D, HasDerivAt (fun b : ℝ => ∑ y : (({o} : Finset V) : Set V),
        (law (intensityProfile J b.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (({o} : Finset V) : Set V)).Reachable
            ⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩ y}) D β ∧ D = 0 := by
  obtain ⟨D, hD, -, -⟩ := hasDerivAt_finiteChi_le {o} J
    ⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩ hβ
  refine ⟨D, hD, ?_⟩
  have hconst : (fun b : ℝ => ∑ y : (({o} : Finset V) : Set V),
      (law (intensityProfile J b.toNNReal)).real
        {ω : Config V | ((openGraph ω).induce (({o} : Finset V) : Set V)).Reachable
          ⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩ y}) = fun _ => 1 := by
    funext b
    have hy : ∀ y : (({o} : Finset V) : Set V),
        y = ⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩ := fun y =>
      Subtype.ext (Finset.mem_singleton.1 (Finset.mem_coe.1 y.2))
    have hunique : (Finset.univ : Finset (({o} : Finset V) : Set V)) =
        {⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun y _ => hy y⟩
    rw [hunique, Finset.sum_singleton]
    have : {ω : Config V | ((openGraph ω).induce (({o} : Finset V) : Set V)).Reachable
        ⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩
        ⟨o, Finset.mem_coe.2 (Finset.mem_singleton_self o)⟩} = univ :=
      eq_univ_of_forall fun ω => SimpleGraph.Reachable.refl _
    rw [this, probReal_univ]
  rw [hconst] at hD
  exact hD.unique (hasDerivAt_const β 1)

/-- Two vertices with one pair of intensity `1`: `hasDerivAt_finiteChi_le` applies at every `β > 0`.
-/
example {β : ℝ} (hβ : 0 < β) :=
  hasDerivAt_finiteChi_le (Finset.univ : Finset Bool)
    (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0)
    ⟨false, Finset.mem_coe.2 (Finset.mem_univ false)⟩ hβ

/-- On two vertices every susceptibility is at most `2`. -/
theorem chi_bool_ne_top (J : Sym2 Bool → ℝ≥0) (β : ℝ≥0) (x : Bool) :
    chi (intensityProfile J β) x ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := 2) ENNReal.ofNat_ne_top ?_
  rw [chi_eq_tsum_tau, tsum_fintype, Fintype.sum_bool]
  calc _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add (tau_le_one _ _ _) (tau_le_one _ _ _)
    _ = 2 := one_add_one_eq_two

/-- The kernel with intensity `1` on the one pair of `Bool` is transitive. -/
theorem bool_pair_transitive : ∀ x y : Bool, ∃ σ : Bool ≃ Bool, σ x = y ∧
    ∀ e, (fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0) (Sym2.map σ e) =
      (fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0) e := by
  intro x y
  refine ⟨if x = y then Equiv.refl Bool else Equiv.swap false true, ?_, fun e => ?_⟩
  · cases x <;> cases y <;> simp
  · induction e using Sym2.ind with
    | h u v =>
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [hxy, Sym2.map_mk]
        cases u <;> cases v <;> simp [Sym2.eq_swap]

/-- The comparison `1/χ(s) - 1/χ(t) ≤ R (t - s)` on two vertices, for `0 < s ≤ t`. -/
example {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :=
  inv_chi_sub_le (fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0)
    bool_pair_transitive false (by simp [rowSum_def, tsum_fintype]) le_rfl (b := t + 1)
    (fun β _ => chi_bool_ne_top _ _ _) hs hst (by linarith)

/-- Almost-everywhere differentiability and the derivative bound on two vertices. -/
example : ∀ᵐ β, β ∈ Ioo (0 : ℝ) 1 → DifferentiableAt ℝ (fun u : ℝ => (chi (intensityProfile
    (fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0) u.toNNReal)
      false).toReal) β :=
  ae_differentiableAt_chi _ bool_pair_transitive false (by simp [rowSum_def, tsum_fintype]) le_rfl
    fun β _ => chi_bool_ne_top _ _ _

/-- The integrated mean-field inequality on two vertices joined by a pair of intensity `1`: the
kernel is transitive (the swap of the two vertices), `R = 1`, and every susceptibility is at most
`2`, so the integrated inequality holds on `(0, b)` for every `b`. -/
example {s t b : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < b) :
    (chi (intensityProfile (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0)
        t.toNNReal) false).toReal -
      (chi (intensityProfile (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0)
        s.toNNReal) false).toReal ≤
      (rowSum (fun e' => ((fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0) e' :
        ℝ≥0∞)) false).toReal *
        ∫ u in s..t, (chi (intensityProfile
          (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0) u.toNNReal)
            false).toReal ^ 2 := by
  have hchi : ∀ (J : Sym2 Bool → ℝ≥0) (β : ℝ≥0) (x : Bool), chi (intensityProfile J β) x ≠ ⊤ := by
    intro J β x
    refine ne_top_of_le_ne_top (b := 2) ENNReal.ofNat_ne_top ?_
    rw [chi_eq_tsum_tau, tsum_fintype, Fintype.sum_bool]
    calc _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add (tau_le_one _ _ _) (tau_le_one _ _ _)
      _ = 2 := one_add_one_eq_two
  have hJ : ∀ x y : Bool, ∃ σ : Bool ≃ Bool, σ x = y ∧
      ∀ e, (fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0)
        (Sym2.map σ e) = (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0) e := by
    intro x y
    refine ⟨if x = y then Equiv.refl Bool else Equiv.swap false true, ?_, fun e => ?_⟩
    · cases x <;> cases y <;> simp
    · induction e using Sym2.ind with
      | h u v =>
        by_cases hxy : x = y
        · simp [hxy]
        · simp only [hxy, Sym2.map_mk]
          cases u <;> cases v <;> simp [Sym2.eq_swap]
  convert chi_sub_le_integral (fun e : Sym2 Bool => if e = s(false, true) then (1 : ℝ≥0) else 0)
    hJ false (by simp [rowSum_def, tsum_fintype]) le_rfl
    (fun β _ => hchi _ _ _) hs hst ht using 4

end PercLib.Percolation.Bond

/-! ### Local Lipschitz continuity -/

namespace PercLib.Models.NormalizedSmallIntensity

open PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

open Set in
/-- **Local Lipschitz continuity of `χ`.** In a transitive intensity model with finite
off-diagonal row sum at `o` and susceptibility finite on `(a, b)`, `0 ≤ a`, the real
susceptibility `β ↦ χ_β(o)` is locally Lipschitz on `(a, b)`. -/
theorem locallyLipschitzOn_chi (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) :
    LocallyLipschitzOn (Ioo a b)
      (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) := by
  intro β hβ
  have hs : a < (a + β) / 2 := by linarith [hβ.1]
  have hs' : (a + β) / 2 < β := by linarith [hβ.1]
  have ht : (β + b) / 2 < b := by linarith [hβ.2]
  have ht' : β < (β + b) / 2 := by linarith [hβ.2]
  exact ⟨_, Icc ((a + β) / 2) ((β + b) / 2),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hs' ht'),
    lipschitzOnWith_chi J hJ o hR ha hfin hs ht⟩

end PercLib.Models.NormalizedSmallIntensity
