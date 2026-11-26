/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Leaf-labelled trivalent tree shapes `𝒯_k` (wiki tag SO5J, article `multipoint-trees`) and the
multipoint tree-graph target AFH6, on the bond interface. New definitions and proofs;
nothing is copied. Mathlib at the pinned revision has trees (`SimpleGraph.IsTree`) and star graphs,
which are used, but no leaf-labelled tree shapes;
`Mathlib/Combinatorics/Enumerative/Catalan/Tree.lean` has rooted plane binary trees, which are a
different notion (ordered children, unlabelled leaves).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Basic
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Bounded

/-! # Leaf-labelled trivalent tree shapes

A shape in `𝒯_k` is an isomorphism class of finite unrooted trees whose leaves carry the
distinct labels `0, …, k-1` and whose other vertices have degree three, under isomorphisms
preserving the leaf labels. Such a tree has exactly `k - 2` internal vertices, so every
class has a representative on the vertex type `Fin k ⊕ Fin (k - 2)`: leaves `Sum.inl i`,
internal vertices `Sum.inr j`. A shape is therefore an equivalence class of trees on that
vertex type (`IsTrivalentTree`) under leaf-fixing graph isomorphisms (`treeShapeSetoid`);
a leaf-fixing isomorphism is exactly a relabelling of the internal vertices. Sums over
internal positions are sums over `z : Fin (k - 2) → V`. As in the wiki, the AFH6 sum uses
one chosen representative of each shape (`Quotient.out`); its weight does not depend on the
choice, because relabelling internal vertices reindexes the sum over `z`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SimpleGraph
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-- A **leaf-labelled trivalent tree with `k` leaves** on `Fin k ⊕ Fin (k - 2)`: a tree in
which every leaf `Sum.inl i` has degree one and every internal vertex `Sum.inr j` has
degree three. -/
structure IsTrivalentTree (k : ℕ) (G : SimpleGraph (Fin k ⊕ Fin (k - 2))) : Prop where
  isTree : G.IsTree
  ncard_leaf : ∀ i, (G.neighborSet (Sum.inl i)).ncard = 1
  ncard_internal : ∀ j, (G.neighborSet (Sum.inr j)).ncard = 3

/-- Two leaf-labelled trivalent trees are equivalent when a graph isomorphism between them
fixes every leaf label. -/
def treeShapeSetoid (k : ℕ) : Setoid {G : SimpleGraph (Fin k ⊕ Fin (k - 2)) //
    IsTrivalentTree k G} where
  r G H := ∃ φ : G.1 ≃g H.1, ∀ i, φ (Sum.inl i) = Sum.inl i
  iseqv := ⟨fun _ => ⟨Iso.refl, fun _ => rfl⟩,
    fun ⟨φ, h⟩ => ⟨φ.symm, fun i => by rw [RelIso.symm_apply_eq, h i]⟩,
    fun ⟨φ, h⟩ ⟨ψ, h'⟩ => ⟨φ.trans ψ, fun i => by simp [h, h']⟩⟩

/-- The **tree shapes** `𝒯_k`: isomorphism classes of finite unrooted trees
with `k` labelled leaves and all other vertices of degree three. -/
def TreeShape (k : ℕ) : Type :=
  Quotient (treeShapeSetoid k)

variable {V : Type*}

/-- The **tree weight** of a trivalent tree `G` with leaves at `x`:
`∑_{z ∈ V^{Int}} ∏_{{u,v} ∈ E(G)} τ(ξ_u, ξ_v)` with `ξ = x` on leaves and `ξ = z` on internal
vertices. -/
def treeWeight (q : Sym2 V → unitInterval) {k : ℕ} (x : Fin k → V)
    (G : SimpleGraph (Fin k ⊕ Fin (k - 2))) : ℝ≥0∞ :=
  ∑' z : Fin (k - 2) → V, ∏ᶠ e ∈ G.edgeSet,
    Sym2.lift ⟨fun u v => tau q (Sum.elim x z u) (Sum.elim x z v), fun _ _ => tau_comm q _ _⟩ e

/-- **AFH6**, the multipoint tree-graph inequality: for `k ≥ 2` and `x : Fin k → V`, not
necessarily distinct, `P(x_0, …, x_{k-1} in one cluster) ≤ ∑_{T ∈ 𝒯_k} ∑_z ∏_{E(T)} τ`,
for every profile. A proposition to prove. -/
@[tag "AFH6"]
def MultipointTreeGraphInequality (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (k : ℕ) (x : Fin k → V), 2 ≤ k →
    law q {ω | ∀ i j, ω ∈ conn (x i) (x j)} ≤ ∑' T : TreeShape k, treeWeight q x T.out.1

/-! ### API -/

theorem treeShape_eq_iff {k : ℕ} {G H : {G : SimpleGraph (Fin k ⊕ Fin (k - 2)) //
    IsTrivalentTree k G}} :
    (Quotient.mk (treeShapeSetoid k) G : TreeShape k) = Quotient.mk _ H ↔
      ∃ φ : G.1 ≃g H.1, ∀ i, φ (Sum.inl i) = Sum.inl i :=
  Quotient.eq

/-- If all leaf-labelled trivalent trees with `k` leaves are equal, there is at most one shape. -/
theorem subsingleton_treeShape_of_eq {k : ℕ}
    (h : ∀ G H : SimpleGraph (Fin k ⊕ Fin (k - 2)), IsTrivalentTree k G → IsTrivalentTree k H →
      G = H) : Subsingleton (TreeShape k) := by
  refine ⟨fun T T' => Quotient.inductionOn₂ T T' fun G H => Quotient.sound ?_⟩
  obtain rfl : G = H := Subtype.ext (h _ _ G.2 H.2)
  exact ⟨Iso.refl, fun _ => rfl⟩

/-! ### Witnesses: `|𝒯_2| = |𝒯_3| = 1` -/

/-- The neighbours of the centre of a star are all other vertices. -/
private theorem neighborSet_starGraph_center {W : Type*} (r : W) :
    (starGraph r).neighborSet r = {r}ᶜ := by
  ext v; simp [eq_comm]

/-- A non-centre vertex of a star has only the centre as a neighbour. -/
private theorem neighborSet_starGraph_of_ne {W : Type*} {r v : W} (h : v ≠ r) :
    (starGraph r).neighborSet v = {r} := by
  ext w; simp only [mem_neighborSet, starGraph_adj, mem_singleton_iff]
  constructor
  · rintro ⟨-, h' | h'⟩
    · exact absurd h' h
    · exact h'
  · rintro rfl; exact ⟨h, Or.inr rfl⟩

/-- The single edge is the trivalent tree with two leaves. -/
theorem isTrivalentTree_two : IsTrivalentTree 2 (starGraph (Sum.inl 0)) where
  isTree := isTree_starGraph _
  ncard_leaf i := by
    by_cases hi : i = 0
    · subst hi
      rw [neighborSet_starGraph_center, ncard_compl, ncard_singleton]; simp
    · rw [neighborSet_starGraph_of_ne (by simpa using hi), ncard_singleton]
  ncard_internal j := j.elim0

/-- The tripod is the trivalent tree with three leaves. -/
theorem isTrivalentTree_three : IsTrivalentTree 3 (starGraph (Sum.inr 0)) where
  isTree := isTree_starGraph _
  ncard_leaf i := by rw [neighborSet_starGraph_of_ne (by simp), ncard_singleton]
  ncard_internal j := by
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
    rw [neighborSet_starGraph_center, ncard_compl, ncard_singleton]; simp

/-- In a graph where `r` is adjacent to every other vertex and every other vertex has
exactly one neighbour, the graph is the star at `r`. -/
private theorem eq_starGraph {W : Type*} {G : SimpleGraph W} (r : W)
    (hr : ∀ v, v ≠ r → G.Adj r v) (hv : ∀ v, v ≠ r → (G.neighborSet v).ncard = 1) :
    G = starGraph r := by
  have key : ∀ v, v ≠ r → ∀ w, G.Adj v w ↔ w = r := by
    intro v hvr w
    obtain ⟨a, ha⟩ := ncard_eq_one.1 (hv v hvr)
    have hra : r ∈ G.neighborSet v := (hr v hvr).symm
    rw [ha, mem_singleton_iff] at hra
    subst hra
    change w ∈ G.neighborSet v ↔ w = r
    rw [ha, mem_singleton_iff]
  ext v w
  rw [starGraph_adj]
  by_cases hvr : v = r
  · subst hvr
    exact ⟨fun h => ⟨h.ne, Or.inl rfl⟩, fun h => hr w (Ne.symm h.1)⟩
  · rw [key v hvr w]
    exact ⟨fun h => ⟨h ▸ hvr, Or.inr h⟩, fun h => h.2.resolve_left hvr⟩

theorem nonempty_treeShape_two : Nonempty (TreeShape 2) :=
  ⟨Quotient.mk _ ⟨_, isTrivalentTree_two⟩⟩

theorem nonempty_treeShape_three : Nonempty (TreeShape 3) :=
  ⟨Quotient.mk _ ⟨_, isTrivalentTree_three⟩⟩

/-- `|𝒯_2| = 1`: the only trivalent tree with two leaves is the single edge. -/
theorem card_treeShape_two : Nat.card (TreeShape 2) = 1 := by
  have := subsingleton_treeShape_of_eq (k := 2) fun G H hG hH => by
    have hstar : ∀ G : SimpleGraph (Fin 2 ⊕ Fin 0), IsTrivalentTree 2 G →
        G = starGraph (Sum.inl 0) := fun G hG => by
      have h1 : G.Adj (Sum.inl 0) (Sum.inl 1) := by
        obtain ⟨a, ha⟩ := ncard_eq_one.1 (hG.ncard_leaf 0)
        have : a ∈ G.neighborSet (Sum.inl 0) := ha ▸ mem_singleton a
        rcases a with a | a
        · fin_cases a
          · exact absurd this (G.irrefl)
          · exact this
        · exact a.elim0
      refine eq_starGraph _ (fun v hv => ?_) (fun v hv => ?_)
      · rcases v with a | a
        · fin_cases a
          · exact absurd rfl hv
          · exact h1
        · exact a.elim0
      · rcases v with a | a
        · fin_cases a
          · exact absurd rfl hv
          · exact hG.ncard_leaf 1
        · exact a.elim0
    rw [hstar G hG, hstar H hH]
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, nonempty_treeShape_two⟩

/-- `|𝒯_3| = 1`: the only trivalent tree with three leaves is the tripod. -/
theorem card_treeShape_three : Nat.card (TreeShape 3) = 1 := by
  have := subsingleton_treeShape_of_eq (k := 3) fun G H hG hH => by
    have hstar : ∀ G : SimpleGraph (Fin 3 ⊕ Fin 1), IsTrivalentTree 3 G →
        G = starGraph (Sum.inr 0) := fun G hG => by
      have hc : G.neighborSet (Sum.inr 0) = {Sum.inr 0}ᶜ := by
        refine eq_of_subset_of_ncard_le (fun v hv => G.ne_of_adj hv |>.symm) ?_ (toFinite _)
        rw [hG.ncard_internal 0, ncard_compl, ncard_singleton]; simp
      refine eq_starGraph _ (fun v hv => ?_) (fun v hv => ?_)
      · change v ∈ G.neighborSet _; rw [hc]; exact hv
      · rcases v with a | a
        · exact hG.ncard_leaf a
        · exact absurd (congrArg Sum.inr (Subsingleton.elim (α := Fin 1) a 0)) hv
    rw [hstar G hG, hstar H hH]
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, nonempty_treeShape_three⟩

/-! ### Multipoint geometry: the recursive three-part distance and the sweep product

Wiki tags Y4H4 and CS13 (article `multipoint-trees`). A finite
metric space `(A, d)` is a `Finset` in a metric space; for `A ⊆ ℝ^d` with the Euclidean
distance (`EuclideanSpace ℝ (Fin d)`), `threePartDistance` is the `S(A)` of Y4H4, and in
general it is the `S_d(A)` of CS13. -/

section Geometry

variable {X : Type*} [MetricSpace X] [DecidableEq X]

/-- The **recursive three-part distance** `S(A)`: for `|A| ≤ 2` it is
`diam(A)²`, so `S({x, y}) = d(x, y)²`; for `|A| ≥ 3` it is the minimum over ordered
partitions `A = A₁ ⊔ A₂ ⊔ A₃` into nonempty parts of
`√(S(A₁ ∪ A₂) S(A₂ ∪ A₃) S(A₃ ∪ A₁))`. A partition is encoded by `(A₁, A₂)`, with
`A₃ = A \ (A₁ ∪ A₂)`. The value at `|A| ≤ 1` (namely `0`) is not used by the wiki. -/
@[tag "Y4H4"]
noncomputable def threePartDistance (A : Finset X) : ℝ :=
  if A.card ≤ 2 then Metric.diam (A : Set X) ^ 2
  else if h : ((A.powerset ×ˢ A.powerset).filter fun p : Finset X × Finset X =>
      Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ (A \ (p.1 ∪ p.2)).Nonempty).Nonempty then
    ((A.powerset ×ˢ A.powerset).filter fun p : Finset X × Finset X =>
      Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ (A \ (p.1 ∪ p.2)).Nonempty).attach.inf'
      (Finset.attach_nonempty_iff.2 h) fun p =>
        Real.sqrt (threePartDistance (p.1.1 ∪ p.1.2) *
          threePartDistance (p.1.2 ∪ (A \ (p.1.1 ∪ p.1.2))) *
          threePartDistance ((A \ (p.1.1 ∪ p.1.2)) ∪ p.1.1))
  else 0
termination_by A.card
decreasing_by
  all_goals
    have hp := p.2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp
    obtain ⟨⟨h1, h2⟩, hd, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hp
    apply Finset.card_lt_card
    first
    | exact (Finset.ssubset_iff_of_subset (Finset.union_subset h1 h2)).2
        ⟨c, (Finset.mem_sdiff.1 hc).1, (Finset.mem_sdiff.1 hc).2⟩
    | exact (Finset.ssubset_iff_of_subset (Finset.union_subset h2 Finset.sdiff_subset)).2
        ⟨a, h1 ha, fun h => (Finset.mem_union.1 h).elim (Finset.disjoint_left.1 hd ha)
          fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_union_left _ ha)⟩
    | exact (Finset.ssubset_iff_of_subset (Finset.union_subset Finset.sdiff_subset h1)).2
        ⟨b, h2 hb, fun h => (Finset.mem_union.1 h).elim
          (fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_union_right _ hb))
          fun h => Finset.disjoint_left.1 hd h hb⟩

open Classical in
/-- The **sweep product** `Sweep_d(A)` (wiki tag CS13): the minimum over rooted trees on `A`
of `∏_{x ∈ A} diam(A_x)`, where `A_root = A` and, for `x` not the root, `A_x` consists of `x`,
its parent and its descendants. A rooted tree is a root `r` with a parent map `p : A → A`,
`p r = r`, such that every vertex reaches `r` under iteration of `p`; the descendants of `x`
are the `y` with `p^[n] y = x` for some `n ≥ 1`. The value at `A = ∅` (namely `0`) is not used
by the wiki. -/
@[tag "CS13"]
noncomputable def sweepProduct (A : Finset X) : ℝ :=
  if h : ((Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x, ∃ n, t.2^[n] x = t.1).Nonempty then
    ((Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x, ∃ n, t.2^[n] x = t.1).inf' h fun t =>
        ∏ x : A, Metric.diam (if x = t.1 then (A : Set X)
          else insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x}))
  else 0

/-- `S({x, y}) = d(x, y)²`. -/
theorem threePartDistance_pair (x y : X) :
    threePartDistance ({x, y} : Finset X) = dist x y ^ 2 := by
  rw [threePartDistance]
  simp only [Finset.card_le_two, ↓reduceIte, Finset.coe_insert, Finset.coe_singleton,
    Metric.diam_pair]

/-- Non-vacuity: in `ℝ^d`, `S({x, y}) = ‖x - y‖₂²`. -/
example {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    threePartDistance ({x, y} : Finset _) = ‖x - y‖ ^ 2 := by
  rw [threePartDistance_pair, dist_eq_norm]

/-- Non-vacuity: the sweep product of a two-point space is `d(x, y)²`. -/
theorem sweepProduct_pair {x y : X} (hxy : x ≠ y) :
    sweepProduct ({x, y} : Finset X) = dist x y ^ 2 := by
  classical
  set A : Finset X := {x, y}
  have hmem : ∀ z : A, (z : X) = x ∨ (z : X) = y := fun z =>
    (Finset.mem_insert.1 z.2).imp_right Finset.mem_singleton.1
  -- every factor is `diam A = d(x, y)`
  have hdiam : Metric.diam (A : Set X) = dist x y := by
    simp [A, Metric.diam_pair]
  have hfac : ∀ t : A × (A → A), (∀ x', ∃ n, t.2^[n] x' = t.1) → ∀ z : A,
      Metric.diam (if z = t.1 then (A : Set X)
        else insert (t.2 z : X) ((↑) '' {y' : A | ∃ n, t.2^[n] y' = z})) = dist x y := by
    intro t hreach z
    split_ifs with hz
    · exact hdiam
    · have hsub : insert (t.2 z : X) ((↑) '' {y' : A | ∃ n, t.2^[n] y' = z}) ⊆ (A : Set X) := by
        rintro w (rfl | ⟨w, -, rfl⟩) <;> exact Finset.mem_coe.2 (Subtype.prop _)
      refine le_antisymm (hdiam ▸ Metric.diam_mono hsub (Finset.finite_toSet A).isBounded) ?_
      have hpz : t.2 z ≠ z := by
        intro hfix
        obtain ⟨n, hn⟩ := hreach z
        exact hz (by rw [← hn, Function.iterate_fixed hfix])
      have hzmem : (z : X) ∈ insert (t.2 z : X) ((↑) '' {y' : A | ∃ n, t.2^[n] y' = z}) :=
        Set.mem_insert_of_mem _ ⟨z, ⟨0, rfl⟩, rfl⟩
      have hd : dist (t.2 z : X) (z : X) = dist x y := by
        have hne : (t.2 z : X) ≠ (z : X) := fun h => hpz (Subtype.ext h)
        rcases hmem (t.2 z) with h1 | h1 <;> rcases hmem z with h2 | h2 <;>
          rw [h1, h2] at hne ⊢ <;> first | exact absurd rfl hne | exact _root_.dist_comm _ _
      rw [← hd]
      exact Metric.dist_le_diam_of_mem ((Finset.finite_toSet A).isBounded.subset hsub)
        (Set.mem_insert _ _) hzmem
  have hcard : Fintype.card A = 2 := by
    simp [A, Finset.card_pair hxy]
  have hval : ∀ t ∈ ((Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x', ∃ n, t.2^[n] x' = t.1),
      (∏ z : A, Metric.diam (if z = t.1 then (A : Set X)
        else insert (t.2 z : X) ((↑) '' {y' : A | ∃ n, t.2^[n] y' = z}))) = dist x y ^ 2 := by
    intro t ht
    rw [Finset.prod_congr rfl fun z _ => hfac t (Finset.mem_filter.1 ht).2.2 z,
      Finset.prod_const, Finset.card_univ, hcard]
  have hstar : ((⟨x, by simp [A]⟩ : A), fun _ : A => (⟨x, by simp [A]⟩ : A)) ∈
      ((Finset.univ : Finset (A × (A → A))).filter fun t =>
        t.2 t.1 = t.1 ∧ ∀ x', ∃ n, t.2^[n] x' = t.1) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, fun _ => ⟨1, rfl⟩⟩
  rw [sweepProduct]
  split_ifs with hne
  · refine le_antisymm ((Finset.inf'_le _ hstar).trans_eq (hval _ hstar)) ?_
    exact Finset.le_inf' _ _ fun t ht => (hval t ht).ge
  · exact absurd ⟨_, hstar⟩ hne

end Geometry

end PercLib.Percolation.Bond
