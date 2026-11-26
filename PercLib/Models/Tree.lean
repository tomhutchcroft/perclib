/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-15. No upstream proof is copied. Source of the model: G. Grimmett,
*Percolation* (2nd ed., 1999), the rooted tree example; the statements here are elementary.
-/
module

public import Mathlib.Data.Set.Finite.List
public import PercLib.Percolation.Bond.Diagonal.Probability
public import PercLib.Percolation.Bond.Host
public import PercLib.Probability.Cylinder

/-!
# Bond percolation on the rooted `k`-ary tree: deterministic structure and decay

The vertices are the words `List (Fin k)`, the root is `[]`, and the children of `u` are
the words `b :: u`. The tree is written as the explicit graph
`SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u` (no new definition). The
ancestors of `w` are its suffixes `w.drop m`, and the `m`-th edge on the way from `w` to the
root is `s(w.drop (m + 1), w.drop m)`.

* A configuration supported on the tree joins the root to `w` exactly when every edge on
  the way from `w` to the root is open (`reachable_nil_iff_of_subset`).
* For such a configuration the cluster of the root is infinite exactly when it reaches every
  depth (`cluster_nil_infinite_iff`).
* With open probability `p` on tree edges and `0` on other pairs (any value on the
  diagonal), the probability that the root reaches depth `n` is at most `(k p)ⁿ`
  (`law_reach_depth_le`).
* Reaching depth `n` is witnessed by an open chain to the root
  (`exists_reachable_nil_iff_of_subset`), the root cluster is infinite exactly when the root
  reaches every depth (`cluster_nil_infinite_iff_forall_reach_depth`), and the root reaches
  depth `0` almost surely (`law_reach_depth_zero`).
* For `k = 0` the root cluster is `{[]}` (`cluster_nil_eq_singleton_of_eq_zero`); at `p = 1`
  every tree edge is almost surely open (`ae_kTree_edgeSet_subset_of_eq_one`).
* The two deterministic statements also hold when only the open graph lies in the tree,
  so open diagonal pairs are allowed (`reachable_nil_iff_of_openGraph_le`,
  `cluster_nil_infinite_iff_forall_reach_depth_of_openGraph_le`).

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

variable {k : ℕ}

/-- Adjacency in the rooted `k`-ary tree: one word is a child of the other. -/
theorem kTree_adj_iff (u w : List (Fin k)) :
    (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).Adj u w ↔
      (∃ b, w = b :: u) ∨ ∃ b, u = b :: w := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  rcases h with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
  · have := congrArg List.length hb
    simp at this

/-- If every edge on the way from `w` to the root is open, the root is joined to `w`. -/
theorem reachable_nil_of_forall_drop (ω : Config (List (Fin k))) (w : List (Fin k))
    (h : ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω) : (openGraph ω).Reachable [] w := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons b w ih =>
    have h' : ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω := fun m hm => by
      simpa using h (m + 1) (by simp; omega)
    have h0 : s(w, b :: w) ∈ ω := by simpa using h 0 (by simp)
    have hne : w ≠ b :: w := fun e => by
      have := congrArg List.length e
      simp at this
    exact (ih h').trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω w (b :: w)).2 ⟨h0, hne⟩))

/-- **Paths to the root in a tree configuration.** If every open pair is a tree edge and the
root is joined to `w`, every edge on the way from `w` to the root is open. -/
theorem forall_drop_of_reachable_nil {ω : Config (List (Fin k))}
    (hω : ω ⊆ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet)
    {w : List (Fin k)} (h : (openGraph ω).Reachable [] w) :
    ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => intro m hm; simp at hm
  | @tail v u _ hvu ih =>
    rw [openGraph_adj_iff] at hvu
    obtain ⟨hvuω, -⟩ := hvu
    have hadj := (kTree_adj_iff v u).1 (hω hvuω)
    rcases hadj with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · intro m hm
      cases m with
      | zero => simpa using hvuω
      | succ m =>
        have := ih m (by simp at hm; omega)
        simpa using this
    · intro m hm
      have := ih (m + 1) (by simp; omega)
      simpa using this

/-- **Reaching a word in a tree configuration.** -/
theorem reachable_nil_iff_of_subset {ω : Config (List (Fin k))}
    (hω : ω ⊆ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet)
    (w : List (Fin k)) :
    (openGraph ω).Reachable [] w ↔ ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω :=
  ⟨forall_drop_of_reachable_nil hω, reachable_nil_of_forall_drop ω w⟩

/-- **The root cluster is infinite exactly when it reaches every depth** (tree
configurations). -/
theorem cluster_nil_infinite_iff {ω : Config (List (Fin k))} [Finite (Fin k)]
    (hω : ω ⊆ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet) :
    (cluster ω []).Infinite ↔
      ∀ n, ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω := by
  constructor
  · intro hinf n
    obtain ⟨w, hw, hwn⟩ := (hinf.sdiff (List.finite_length_lt (Fin k) n)).nonempty
    simp only [mem_ofPred_eq, not_lt] at hwn
    have hanc := forall_drop_of_reachable_nil hω hw
    refine ⟨w.drop (w.length - n), by simp; omega, fun m hm => ?_⟩
    have := hanc (w.length - n + m) (by omega)
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  · intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image List.length).bddAbove
    obtain ⟨w, hw, hanc⟩ := h (N + 1)
    have hmem : w ∈ cluster ω [] := reachable_nil_of_forall_drop ω w (hw ▸ hanc)
    have := hN ⟨w, hmem, rfl⟩
    omega

/-- The event that the root reaches depth `n` is measurable. -/
theorem measurableSet_reach_depth (n : ℕ) :
    MeasurableSet {ω : Config (List (Fin k)) |
      ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w} := by
  have : {ω : Config (List (Fin k)) |
      ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w} =
      ⋃ w : List (Fin k), {_ω : Config (List (Fin k)) | w.length = n} ∩ conn [] w := by
    ext ω
    simp [mem_conn_iff]
  rw [this]
  exact MeasurableSet.iUnion fun w => (MeasurableSet.const _).inter (measurableSet_conn _ _)

/-- **Subcritical decay on the tree.** With open probability `p` on tree edges and `0` on
the other pairs (any value on the diagonal), the root reaches depth `n` with probability at
most `(k p)ⁿ`. -/
theorem law_reach_depth_le (p : unitInterval) (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (n : ℕ) :
    law q {ω | ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w} ≤
      ((k : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin k)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  set A := {ω : Config (List (Fin k)) |
    ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w}
  have hdiag : law q A = law q₀ A := by
    refine law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he) (measurableSet_reach_depth n)
      fun ω ω' h => ?_
    simp only [A, mem_ofPred_eq]
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  rw [hdiag]
  have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
    ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
  set W : Finset (List (Fin k)) := Finset.univ.image fun f : Fin n → Fin k => List.ofFn f
  set F : List (Fin k) → Finset (Sym2 (List (Fin k))) := fun w =>
    (Finset.range n).image fun m => s(w.drop (m + 1), w.drop m)
  have hsub : A ≤ᵐ[law q₀] ⋃ w ∈ W, {ω : Config (List (Fin k)) | (F w : Set _) ⊆ ω} := by
    filter_upwards [hsupp] with ω hω hA
    obtain ⟨w, hwn, hw⟩ := hA
    have hanc := forall_drop_of_reachable_nil hω hw
    refine mem_iUnion₂.2 ⟨w, ?_, ?_⟩
    · refine Finset.mem_image.2 ⟨fun i => w.get (i.cast hwn.symm), Finset.mem_univ _, ?_⟩
      apply List.ext_get <;> simp [hwn]
    · intro e he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
      exact hanc m (by rw [hwn]; exact Finset.mem_range.1 hm)
  have hcyl : ∀ w ∈ W, law q₀ {ω : Config (List (Fin k)) | (F w : Set _) ⊆ ω} =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
    intro w hw
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hw
    change prodBernoulli q₀ _ = _
    rw [prodBernoulli_subset]
    have hinj : Set.InjOn (fun m => s((List.ofFn f).drop (m + 1), (List.ofFn f).drop m))
        (Finset.range n : Set ℕ) := by
      intro a ha b hb hab
      rcases Sym2.eq_iff.1 hab with ⟨h1, -⟩ | ⟨h1, h2⟩
      · have := congrArg List.length h1
        simp only [List.length_drop, List.length_ofFn] at this
        simp only [Finset.coe_range, mem_Iio] at ha hb
        omega
      · have e1 := congrArg List.length h1
        have e2 := congrArg List.length h2
        simp only [List.length_drop, List.length_ofFn] at e1 e2
        simp only [Finset.coe_range, mem_Iio] at ha hb
        omega
    rw [Finset.prod_image hinj]
    have hval : ∀ m ∈ Finset.range n, (unitInterval.toNNReal (q₀
        s((List.ofFn f).drop (m + 1), (List.ofFn f).drop m)) : ℝ≥0∞) =
        (unitInterval.toNNReal p : ℝ≥0∞) := by
      intro m hm
      have hlen : m < (List.ofFn f).length := by simpa using hm
      have hcons : (List.ofFn f).drop m = ((List.ofFn f).get ⟨m, hlen⟩) ::
          (List.ofFn f).drop (m + 1) := List.drop_eq_getElem_cons hlen
      have hedge : s((List.ofFn f).drop (m + 1), (List.ofFn f).drop m) ∈ G.edgeSet := by
        rw [SimpleGraph.mem_edgeSet, kTree_adj_iff]
        exact Or.inl ⟨_, hcons⟩
      simp only [q₀, hedge, ite_true]
    rw [Finset.prod_congr rfl hval, Finset.prod_const, Finset.card_range]
  calc law q₀ A ≤ law q₀ (⋃ w ∈ W, {ω : Config (List (Fin k)) | (F w : Set _) ⊆ ω}) :=
        measure_mono_ae hsub
    _ ≤ ∑ w ∈ W, law q₀ {ω : Config (List (Fin k)) | (F w : Set _) ⊆ ω} :=
        measure_biUnion_finset_le W _
    _ = ∑ _w ∈ W, (unitInterval.toNNReal p : ℝ≥0∞) ^ n := Finset.sum_congr rfl hcyl
    _ ≤ (k : ℝ≥0∞) ^ n * (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have : W.card ≤ k ^ n := (Finset.card_image_le).trans (by simp)
        exact_mod_cast this
    _ = _ := (mul_pow _ _ _).symm

/-- **Subcritical trees do not percolate.** If `k p < 1`, the root cluster is almost surely
finite. -/
theorem law_cluster_nil_infinite_eq_zero (p : unitInterval)
    (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hkp : (k : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) < 1) :
    law q {ω | (cluster ω []).Infinite} = 0 := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin k)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  have hdiag : law q {ω | (cluster ω []).Infinite} = law q₀ {ω | (cluster ω []).Infinite} := by
    refine law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he)
      (measurableSet_cluster_infinite _) fun ω ω' h => ?_
    simp only [mem_ofPred_eq, cluster]
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
    ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
  have hle : ∀ n, law q₀ {ω | (cluster ω []).Infinite} ≤
      ((k : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n := by
    intro n
    refine le_trans (measure_mono_ae ?_) (law_reach_depth_le p q₀ (fun e _ => rfl) n)
    filter_upwards [hsupp] with ω hω hinf
    obtain ⟨w, hw, hanc⟩ := (cluster_nil_infinite_iff hω).1 hinf n
    exact ⟨w, hw, reachable_nil_of_forall_drop ω w (hw ▸ hanc)⟩
  rw [hdiag]
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hkp) hle)
    zero_le

/-! ### Depth events, the start of the depth sequence and the trivial cases -/

/-- **Reaching depth `n` in a tree configuration** is witnessed by a word of length `n`
whose edges to the root are all open. -/
theorem exists_reachable_nil_iff_of_subset {ω : Config (List (Fin k))}
    (hω : ω ⊆ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet)
    (n : ℕ) :
    (∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w) ↔
      ∃ w : List (Fin k), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω := by
  refine exists_congr fun w => and_congr_right fun hw => ?_
  rw [reachable_nil_iff_of_subset hω, hw]

/-- **The root cluster is infinite exactly when the root reaches every depth** (tree
configurations). -/
theorem cluster_nil_infinite_iff_forall_reach_depth {ω : Config (List (Fin k))}
    (hω : ω ⊆ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet) :
    (cluster ω []).Infinite ↔
      ∀ n, ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w := by
  rw [cluster_nil_infinite_iff hω]
  exact forall_congr' fun n => (exists_reachable_nil_iff_of_subset hω n).symm

/-- The root reaches depth `0` with probability one, for every profile. -/
theorem law_reach_depth_zero (q : Sym2 (List (Fin k)) → unitInterval) :
    law q {ω | ∃ w : List (Fin k), w.length = 0 ∧ (openGraph ω).Reachable [] w} = 1 := by
  have : {ω : Config (List (Fin k)) |
      ∃ w : List (Fin k), w.length = 0 ∧ (openGraph ω).Reachable [] w} = univ :=
    eq_univ_of_forall fun ω => ⟨[], rfl, SimpleGraph.Reachable.refl _⟩
  rw [this, measure_univ]

/-- Over an empty alphabet the root is the only word, so its cluster is `{[]}`. -/
theorem cluster_nil_eq_singleton {α : Type*} [IsEmpty α] (ω : Config (List α)) :
    cluster ω [] = {[]} := by
  ext w
  cases w with
  | nil => simpa using mem_cluster_self ω []
  | cons a _ => exact isEmptyElim a

/-- **The tree with no children.** For `k = 0` the root cluster is `{[]}`. -/
theorem cluster_nil_eq_singleton_of_eq_zero (hk : k = 0) (ω : Config (List (Fin k))) :
    cluster ω [] = {[]} := by
  subst hk
  exact cluster_nil_eq_singleton ω

/-- If every edge of a graph has open probability one, then almost surely every edge of the
graph is open. -/
theorem ae_edgeSet_subset_of_forall_eq_one {V : Type*} [Countable V] (G : SimpleGraph V)
    (q : Sym2 V → unitInterval) (hq : ∀ e ∈ G.edgeSet, q e = 1) :
    ∀ᵐ ω ∂law q, G.edgeSet ⊆ ω := by
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ G.edgeSet → e ∈ ω := by
    by_cases h : e ∈ G.edgeSet
    · have h1 : law q {ω | e ∈ ω} = 1 := by
        simpa [law, hq e h] using PercLib.Probability.prodBernoulli_setOf_mem q e
      have h0 : law q {ω | e ∈ ω}ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff (measurableSet_mem e)]
        exact h1
      rw [ae_iff]
      simpa [h, Set.compl_ofPred] using h0
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  filter_upwards [ae_all_iff.mpr he] with ω hω
  exact fun e he' => hω e he'

/-- **At `p = 1` every tree edge is open.** With open probability `1` on tree edges (any
values elsewhere), almost surely every edge of the tree is open. -/
theorem ae_kTree_edgeSet_subset_of_eq_one (p : unitInterval)
    (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : p = 1) :
    ∀ᵐ ω ∂law q,
      (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet ⊆ ω :=
  ae_edgeSet_subset_of_forall_eq_one _ q fun e he => by
    rw [hq e (SimpleGraph.not_isDiag_of_mem_edgeSet _ he)]
    simp [he, hp]

/-! ### Configurations whose open graph lies in the tree -/

/-- **Reaching a word when the open graph lies in the tree.** Open diagonal pairs are
allowed: a word is joined to the root iff every edge on its way to the root is open. -/
theorem reachable_nil_iff_of_openGraph_le {ω : Config (List (Fin k))}
    (hω : openGraph ω ≤ SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u)
    (w : List (Fin k)) :
    (openGraph ω).Reachable [] w ↔ ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω := by
  have hs : ω \ Sym2.diagSet ⊆
      (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet :=
    by simpa [openGraph] using hω
  rw [← openGraph_sdiff_diagSet ω, reachable_nil_iff_of_subset hs]
  refine forall₂_congr fun m hm => ?_
  have hnd : ¬ (s(w.drop (m + 1), w.drop m)).IsDiag := by
    intro hd
    have := congrArg List.length (Sym2.mk_isDiag_iff.mp hd)
    simp at this
    omega
  simp [Sym2.mem_diagSet, hnd]

/-- **The root cluster is infinite exactly when it reaches every depth**, for a configuration
whose open graph lies in the tree (open diagonal pairs allowed). -/
theorem cluster_nil_infinite_iff_forall_reach_depth_of_openGraph_le
    {ω : Config (List (Fin k))}
    (hω : openGraph ω ≤ SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u) :
    (cluster ω []).Infinite ↔
      ∀ n, ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w := by
  have hs : ω \ Sym2.diagSet ⊆
      (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet :=
    by simpa [openGraph] using hω
  have hc : cluster ω [] = cluster (ω \ Sym2.diagSet) [] := by
    simp only [cluster, openGraph_sdiff_diagSet]
  rw [hc, cluster_nil_infinite_iff_forall_reach_depth hs, openGraph_sdiff_diagSet]

/-! ### Non-vacuity -/

/-- The binary tree with `p = 1/4`: the root reaches depth `n` with probability at most
`2⁻ⁿ`. -/
example (n : ℕ) :
    law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 4, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = n ∧ (openGraph ω).Reachable [] w} ≤
      ((2 : ℝ≥0∞) * (unitInterval.toNNReal ⟨1 / 4, by norm_num, by norm_num⟩ : ℝ≥0∞)) ^ n := by
  exact_mod_cast law_reach_depth_le (k := 2) _ _ (fun _ _ => rfl) n

/-- With every tree edge open, the root cluster is infinite. -/
example : (cluster ((SimpleGraph.fromRel fun u w : List (Fin 1) => ∃ b, w = b :: u).edgeSet)
    []).Infinite := by
  rw [cluster_nil_infinite_iff subset_rfl]
  intro n
  refine ⟨List.replicate n 0, by simp, fun m hm => ?_⟩
  rw [SimpleGraph.mem_edgeSet, kTree_adj_iff]
  refine Or.inl ⟨0, ?_⟩
  simp only [List.drop_replicate]
  rw [show n - m = (n - (m + 1)) + 1 by omega, List.replicate_succ]

end PercLib.Models
