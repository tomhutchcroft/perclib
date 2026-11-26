/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. Mathematical reference: the leaf-removal bijection for
leaf-labelled trivalent (unrooted binary) trees, e.g. C. Semple and M. Steel, *Phylogenetics*
(Oxford University Press, 2003), Section 2.1. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Multipoint.ShapeCount
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting leaf-labelled trivalent tree shapes

We prove `|𝒯_k| = (2k - 5)!!` for `k ≥ 2` (with `(-1)!! = 1`), where `𝒯_k = TreeShape k` is
the type of leaf-labelled trivalent trees with `k` leaves up to leaf-fixing isomorphism.

Write `k = n + 2`; trees live on `Vtx n = Fin (n + 2) ⊕ Fin n`. The proof follows the
leaf-removal bijection. The new leaf `Sum.inl 0` and the new internal vertex `Sum.inr 0` of a
tree with `n + 3` leaves are attached by `graft` to an edge of a tree with `n + 2` leaves
(whose labels are shifted up by one by `embed`); `prune` removes them again and joins the two
other neighbours of `Sum.inr 0`. The trees obtained from the single edge by repeated grafting
form the family `canonical n`; it has `(2n - 1)!!` members because a tree with `n + 2` leaves
has `2n + 1` edges. Every leaf-labelled trivalent tree is `canonical` after a unique
relabelling of its internal vertices (`existsUnique_canonical`); this gives a bijection between
`canonical n` and `TreeShape (n + 2)`, and in particular shows that a leaf-labelled trivalent
tree has no nontrivial leaf-fixing automorphism.

## Main definitions

* `TrivalentTree.graft`, `TrivalentTree.prune`: inserting and removing the leaf `Sum.inl 0`.
* `TrivalentTree.canonical`: the trees built from the single edge by grafting.

## Main results

* `TrivalentTree.isTrivalentTree_of_connected`: a connected graph with the trivalent degrees is
  a tree.
* `TrivalentTree.existsUnique_canonical`: each trivalent tree has a unique canonical relabelling.
* `card_treeShape`: `Nat.card (TreeShape k) = (2 * k - 5)‼` for `2 ≤ k`.
* `card_internal_and_card_edgeFinset_of_isTree`: a finite tree with `k` labelled leaves and all
  other vertices of degree three has `k - 2` internal vertices and `2k - 3` edges.
-/

@[expose] public section

noncomputable section

open SimpleGraph Function

namespace PercLib.Percolation.Bond

/-! ### Two facts about reachability and acyclic graphs -/

/-- Reachability is transported along a map sending adjacent vertices to reachable ones. -/
theorem reachable_map_of_adj {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (f : α → β) (h : ∀ a b, G.Adj a b → H.Reachable (f a) (f b)) {a b : α}
    (hab : G.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- A set closed under adjacency is closed under reachability. -/
theorem mem_of_reachable_of_closed {α : Type*} {G : SimpleGraph α} {S : Set α}
    (hS : ∀ a b, G.Adj a b → a ∈ S → b ∈ S) {a b : α} (h : G.Reachable a b) (ha : a ∈ S) :
    b ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hS _ _ hadj ha)

/-- An acyclic graph has no triangle. -/
theorem not_adj_of_adj_of_adj_of_isAcyclic {α : Type*} {G : SimpleGraph α}
    (hG : G.IsAcyclic) {u v w : α} (huv : G.Adj u v) (huw : G.Adj u w) : ¬ G.Adj v w :=
  fun hvw => by
    classical
    exact hG.cliqueFree_three {u, v, w} (is3Clique_triple_iff.2 ⟨huv, huw, hvw⟩)

/-- If `v` has exactly one neighbour and `w` is a neighbour, then `w` is the only one. -/
theorem adj_iff_eq_of_ncard_neighborSet_eq_one {α : Type*} {G : SimpleGraph α}
    {v w : α} (h : (G.neighborSet v).ncard = 1) (hw : G.Adj v w) (y : α) :
    G.Adj v y ↔ y = w := by
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 h
  have hw' : w ∈ G.neighborSet v := hw
  rw [hz, Set.mem_singleton_iff] at hw'
  change y ∈ G.neighborSet v ↔ _
  rw [hz, Set.mem_singleton_iff, hw']

namespace TrivalentTree

/-- The vertex type of a trivalent tree with `n + 2` leaves. -/
abbrev Vtx (n : ℕ) : Type := Fin (n + 2) ⊕ Fin n

variable {n : ℕ}

/-- Shift every label up by one, freeing the leaf `Sum.inl 0` and internal vertex `Sum.inr 0`. -/
def embed (n : ℕ) : Vtx n → Vtx (n + 1) := Sum.map Fin.succ Fin.succ

@[simp] theorem embed_inl (i : Fin (n + 2)) : embed n (Sum.inl i) = Sum.inl i.succ := rfl

@[simp] theorem embed_inr (j : Fin n) : embed n (Sum.inr j) = Sum.inr j.succ := rfl

theorem embed_injective (n : ℕ) : Injective (embed n) :=
  Sum.map_injective.2 ⟨Fin.succ_injective _, Fin.succ_injective _⟩

@[simp] theorem embed_inj {a b : Vtx n} : embed n a = embed n b ↔ a = b :=
  (embed_injective n).eq_iff

@[simp] theorem embed_ne_leaf (a : Vtx n) : embed n a ≠ Sum.inl 0 := by
  cases a <;> simp [Fin.succ_ne_zero]

@[simp] theorem embed_ne_hub (a : Vtx n) : embed n a ≠ Sum.inr 0 := by
  cases a <;> simp [Fin.succ_ne_zero]

@[simp] theorem leaf_ne_embed (a : Vtx n) : Sum.inl 0 ≠ embed n a := (embed_ne_leaf a).symm

@[simp] theorem hub_ne_embed (a : Vtx n) : Sum.inr 0 ≠ embed n a := (embed_ne_hub a).symm

/-- Every vertex is the new leaf, the new internal vertex, or a shifted old vertex. -/
theorem vtx_cases (x : Vtx (n + 1)) : x = Sum.inl 0 ∨ x = Sum.inr 0 ∨ ∃ a, x = embed n a := by
  rcases x with i | j
  · induction i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr (Or.inr ⟨Sum.inl i, rfl⟩)
  · induction j using Fin.cases with
    | zero => exact Or.inr (Or.inl rfl)
    | succ j => exact Or.inr (Or.inr ⟨Sum.inr j, rfl⟩)

/-! ### Relabelling internal vertices -/

/-- The permutation of `Vtx n` fixing the leaves and permuting internal vertices by `σ`. -/
def hat (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Vtx n) := Equiv.sumCongr (Equiv.refl _) σ

@[simp] theorem hat_inl (σ : Equiv.Perm (Fin n)) (i : Fin (n + 2)) :
    hat σ (Sum.inl i) = Sum.inl i := rfl

@[simp] theorem hat_inr (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    hat σ (Sum.inr j) = Sum.inr (σ j) := rfl

theorem coe_hat_mul (σ τ : Equiv.Perm (Fin n)) : ⇑(hat (σ * τ)) = hat σ ∘ hat τ := by
  funext x; cases x <;> rfl

theorem coe_hat_one : ⇑(hat (1 : Equiv.Perm (Fin n))) = id := by
  funext x; cases x <;> rfl

@[simp] theorem hat_decomposeFin_embed (σ : Equiv.Perm (Fin n)) (a : Vtx n) :
    hat (Equiv.Perm.decomposeFin.symm (0, σ)) (embed n a) = embed n (hat σ a) := by
  cases a <;> simp

theorem coe_hat_decomposeFin (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    ⇑(hat (Equiv.Perm.decomposeFin.symm (p, σ))) =
      hat (Equiv.swap 0 p) ∘ hat (Equiv.Perm.decomposeFin.symm (0, σ)) := by
  funext x
  rcases x with i | j
  · rfl
  · induction j using Fin.cases <;> simp

theorem mem_map_symm_iff (f : Equiv.Perm (Vtx n)) (e : Sym2 (Vtx n)) (a : Vtx n) :
    a ∈ e.map f.symm ↔ f a ∈ e := by
  induction e using Sym2.ind with
  | h u v => simp [Sym2.mem_iff, Equiv.eq_symm_apply]

theorem map_symm_mem_edgeSet_comap {P : SimpleGraph (Vtx n)} (f : Equiv.Perm (Vtx n))
    {e : Sym2 (Vtx n)} (he : e ∈ P.edgeSet) : e.map f.symm ∈ (P.comap f).edgeSet := by
  induction e using Sym2.ind with
  | h u v => simpa using he

/-- Relabelling the internal vertices preserves being a trivalent tree. -/
theorem isTrivalentTree_comap_hat {Y : SimpleGraph (Vtx n)} (hY : IsTrivalentTree (n + 2) Y)
    (σ : Equiv.Perm (Fin n)) : IsTrivalentTree (n + 2) (Y.comap (hat σ)) := by
  have hN : ∀ x, (Y.comap (hat σ)).neighborSet x = hat σ ⁻¹' Y.neighborSet (hat σ x) :=
    fun _ => rfl
  have hc : ∀ x, ((Y.comap (hat σ)).neighborSet x).ncard = (Y.neighborSet (hat σ x)).ncard :=
    fun x => by
      rw [hN]
      exact Set.ncard_preimage_of_injective_subset_range (hat σ).injective
        (by simp [(hat σ).surjective.range_eq])
  exact ⟨(Iso.comap (hat σ) Y).isTree_iff.2 hY.isTree,
    fun i => by rw [hc]; exact hY.ncard_leaf i, fun j => by rw [hc]; exact hY.ncard_internal _⟩

/-- A leaf-fixing isomorphism is a relabelling of the internal vertices. -/
theorem exists_perm_of_iso {G H : SimpleGraph (Vtx n)} (φ : G ≃g H)
    (hφ : ∀ i, φ (Sum.inl i) = Sum.inl i) : ∃ σ : Equiv.Perm (Fin n), G = H.comap (hat σ) := by
  have hφ' : ∀ i, φ.symm (Sum.inl i) = Sum.inl i := fun i => by
    rw [RelIso.symm_apply_eq, hφ]
  have hr : ∀ j, ∃ j', φ (Sum.inr j) = Sum.inr j' := fun j => by
    rcases h : φ (Sum.inr j) with i | j'
    · rw [← hφ i] at h; exact absurd (φ.injective h) Sum.inr_ne_inl
    · exact ⟨j', rfl⟩
  have hr' : ∀ j, ∃ j', φ.symm (Sum.inr j) = Sum.inr j' := fun j => by
    rcases h : φ.symm (Sum.inr j) with i | j'
    · rw [← hφ' i] at h; exact absurd (φ.symm.injective h) Sum.inr_ne_inl
    · exact ⟨j', rfl⟩
  choose f hf using hr
  choose g hg using hr'
  let σ : Equiv.Perm (Fin n) :=
    { toFun := f, invFun := g
      left_inv := fun j => by
        have := hg (f j)
        rw [← hf j, RelIso.symm_apply_apply] at this
        exact (Sum.inr_injective this).symm
      right_inv := fun j => by
        have := hf (g j)
        rw [← hg j, RelIso.apply_symm_apply] at this
        exact (Sum.inr_injective this).symm }
  have hσ : ∀ x, hat σ x = φ x := by
    rintro (i | j)
    · exact (hφ i).symm
    · exact (hf j).symm
  refine ⟨σ, ?_⟩
  ext x y
  rw [comap_adj, hσ, hσ, φ.map_adj_iff]

/-- A relabelling of the internal vertices is a leaf-fixing isomorphism. -/
theorem exists_iso_of_eq_comap {G H : SimpleGraph (Vtx n)} {σ : Equiv.Perm (Fin n)}
    (h : G = H.comap (hat σ)) : ∃ φ : G ≃g H, ∀ i, φ (Sum.inl i) = Sum.inl i := by
  subst h
  exact ⟨Iso.comap (hat σ) H, fun _ => rfl⟩

/-! ### Trees from degrees -/

/-- A connected graph on `Vtx n` whose leaves have degree one and whose internal vertices have
degree three is a trivalent tree: the degree sum forces `2n + 1` edges. -/
theorem isTrivalentTree_of_connected {G : SimpleGraph (Vtx n)} (hc : G.Connected)
    (hl : ∀ i, (G.neighborSet (Sum.inl i)).ncard = 1)
    (hi : ∀ j, (G.neighborSet (Sum.inr j)).ncard = 3) : IsTrivalentTree (n + 2) G := by
  classical
  refine ⟨?_, hl, hi⟩
  rw [isTree_iff_connected_and_card]
  refine ⟨hc, ?_⟩
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, G.degree v = (G.neighborSet v).ncard := fun v => by
    rw [← card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  simp only [hdeg, Fintype.sum_sum_type, hl, hi, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]
  omega

/-- The two leaf-labelled trivalent trees with two leaves are equal. -/
theorem eq_of_isTrivalentTree_two {G H : SimpleGraph (Vtx 0)} (hG : IsTrivalentTree 2 G)
    (hH : IsTrivalentTree 2 H) : G = H := by
  have hsub : Subsingleton (TreeShape 2) :=
    (Nat.card_eq_one_iff_unique.1 card_treeShape_two).1
  obtain ⟨φ, hφ⟩ := treeShape_eq_iff.1
    (@Subsingleton.elim _ hsub (Quotient.mk (treeShapeSetoid 2) ⟨G, hG⟩)
      (Quotient.mk (treeShapeSetoid 2) ⟨H, hH⟩))
  have hid : ∀ x, φ x = x := by
    rintro (i | j)
    · exact hφ i
    · exact j.elim0
  ext x y
  rw [← φ.map_adj_iff, hid, hid]

/-! ### Grafting a leaf onto an edge -/

/-- Graft the new leaf `Sum.inl 0` onto the edge `e`: subdivide `e` by the new internal vertex
`Sum.inr 0` and join it to the new leaf. -/
def graft (X : SimpleGraph (Vtx n)) (e : Sym2 (Vtx n)) : SimpleGraph (Vtx (n + 1)) :=
  SimpleGraph.fromRel fun x y =>
    (∃ a b, x = embed n a ∧ y = embed n b ∧ X.Adj a b ∧ ¬(a ∈ e ∧ b ∈ e)) ∨
      (x = Sum.inr 0 ∧ (y = Sum.inl 0 ∨ ∃ a ∈ e, y = embed n a))

variable {X : SimpleGraph (Vtx n)} {e : Sym2 (Vtx n)}

@[simp] theorem graft_adj_embed {a b : Vtx n} :
    (graft X e).Adj (embed n a) (embed n b) ↔ X.Adj a b ∧ ¬(a ∈ e ∧ b ∈ e) := by
  simp only [graft, fromRel_adj]
  constructor
  · rintro ⟨-, (⟨a', b', h1, h2, h, hn⟩ | ⟨h1, -⟩) | (⟨a', b', h1, h2, h, hn⟩ | ⟨h1, -⟩)⟩
    · rw [embed_inj] at h1 h2; subst h1 h2; exact ⟨h, hn⟩
    · exact absurd h1 (embed_ne_hub a)
    · rw [embed_inj] at h1 h2; subst h1 h2; exact ⟨h.symm, fun ⟨x, y⟩ => hn ⟨y, x⟩⟩
    · exact absurd h1 (embed_ne_hub b)
  · rintro ⟨h, hn⟩
    exact ⟨fun hab => h.ne (embed_inj.1 hab), Or.inl (Or.inl ⟨a, b, rfl, rfl, h, hn⟩)⟩

@[simp] theorem graft_adj_hub_embed {a : Vtx n} :
    (graft X e).Adj (Sum.inr 0) (embed n a) ↔ a ∈ e := by
  simp only [graft, fromRel_adj]
  constructor
  · rintro ⟨-, (⟨a', b', h1, -⟩ | ⟨-, h | ⟨a', ha', h⟩⟩) | (⟨a', b', -, h2, -⟩ | ⟨h1, -⟩)⟩
    · exact absurd h1 (hub_ne_embed a')
    · exact absurd h (embed_ne_leaf a)
    · rw [embed_inj] at h; exact h ▸ ha'
    · exact absurd h2 (hub_ne_embed b')
    · exact absurd h1 (embed_ne_hub a)
  · intro h
    exact ⟨hub_ne_embed a, Or.inl (Or.inr ⟨trivial, Or.inr ⟨a, h, rfl⟩⟩)⟩

@[simp] theorem graft_adj_embed_hub {a : Vtx n} :
    (graft X e).Adj (embed n a) (Sum.inr 0) ↔ a ∈ e := by
  rw [adj_comm, graft_adj_hub_embed]

@[simp] theorem graft_adj_hub_leaf : (graft X e).Adj (Sum.inr 0) (Sum.inl 0) := by
  simp only [graft, fromRel_adj]
  exact ⟨by simp, Or.inl (Or.inr ⟨trivial, Or.inl trivial⟩)⟩

@[simp] theorem graft_adj_leaf_hub : (graft X e).Adj (Sum.inl 0) (Sum.inr 0) :=
  graft_adj_hub_leaf.symm

@[simp] theorem graft_not_adj_leaf_embed {a : Vtx n} :
    ¬ (graft X e).Adj (Sum.inl 0) (embed n a) := by
  simp only [graft, fromRel_adj]
  rintro ⟨-, (⟨a', b', h1, -⟩ | ⟨h1, -⟩) | (⟨a', b', -, h2, -⟩ | ⟨h1, -⟩)⟩
  · exact absurd h1 (leaf_ne_embed a')
  · exact absurd h1 (by simp)
  · exact absurd h2 (leaf_ne_embed b')
  · exact absurd h1 (embed_ne_hub a)

@[simp] theorem graft_not_adj_embed_leaf {a : Vtx n} :
    ¬ (graft X e).Adj (embed n a) (Sum.inl 0) :=
  fun h => graft_not_adj_leaf_embed h.symm

/-- Grafting commutes with relabelling the internal vertices. -/
theorem comap_graft (X : SimpleGraph (Vtx n)) (e : Sym2 (Vtx n)) (σ : Equiv.Perm (Fin n)) :
    (graft X e).comap (hat (Equiv.Perm.decomposeFin.symm (0, σ))) =
      graft (X.comap (hat σ)) (e.map (hat σ).symm) := by
  ext x y
  rcases vtx_cases x with rfl | rfl | ⟨a, rfl⟩ <;>
    rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩ <;>
    simp [mem_map_symm_iff, -Sym2.mem_map]

/-! ### Pruning the leaf `Sum.inl 0` -/

/-- Remove the leaf `Sum.inl 0` and the vertex `Sum.inr 0`, joining the other neighbours of
`Sum.inr 0`. -/
def prune (Y : SimpleGraph (Vtx (n + 1))) : SimpleGraph (Vtx n) :=
  SimpleGraph.fromRel fun a b => Y.Adj (embed n a) (embed n b) ∨
    (Y.Adj (Sum.inr 0) (embed n a) ∧ Y.Adj (Sum.inr 0) (embed n b))

theorem prune_adj {Y : SimpleGraph (Vtx (n + 1))} {a b : Vtx n} :
    (prune Y).Adj a b ↔ a ≠ b ∧ (Y.Adj (embed n a) (embed n b) ∨
      (Y.Adj (Sum.inr 0) (embed n a) ∧ Y.Adj (Sum.inr 0) (embed n b))) := by
  simp only [prune, fromRel_adj, Y.adj_comm (embed n b)]
  constructor <;> rintro ⟨h, h'⟩ <;> refine ⟨h, ?_⟩ <;> tauto

theorem prune_comap (Y : SimpleGraph (Vtx (n + 1))) (σ : Equiv.Perm (Fin n)) :
    prune (Y.comap (hat (Equiv.Perm.decomposeFin.symm (0, σ)))) = (prune Y).comap (hat σ) := by
  ext a b
  simp [prune_adj]

theorem prune_graft (he : e ∈ X.edgeSet) : prune (graft X e) = X := by
  ext a b
  rw [prune_adj, graft_adj_embed, graft_adj_hub_embed, graft_adj_hub_embed]
  constructor
  · rintro ⟨hab, ⟨h, -⟩ | ⟨ha, hb⟩⟩
    · exact h
    · rw [← mem_edgeSet, ← (Sym2.mem_and_mem_iff hab).1 ⟨ha, hb⟩]; exact he
  · intro h
    refine ⟨h.ne, ?_⟩
    by_cases hm : a ∈ e ∧ b ∈ e
    · exact Or.inr hm
    · exact Or.inl ⟨h, hm⟩

/-! ### Grafting and pruning preserve trivalent trees -/

/-- Grafting onto an edge of a trivalent tree gives a trivalent tree. -/
theorem isTrivalentTree_graft (hX : IsTrivalentTree (n + 2) X) (he : e ∈ X.edgeSet) :
    IsTrivalentTree (n + 1 + 2) (graft X e) := by
  induction e using Sym2.ind with
  | h u v =>
  have huv : X.Adj u v := he
  have hdeg : ∀ a, ((graft X s(u, v)).neighborSet (embed n a)).ncard =
      (X.neighborSet a).ncard := by
    intro a
    by_cases ha : a ∈ s(u, v)
    · obtain ⟨p, hap, hp⟩ : ∃ p, X.Adj a p ∧ ∀ b, X.Adj a b → (b ∈ s(u, v) ↔ b = p) := by
        rcases Sym2.mem_iff.1 ha with rfl | rfl
        · exact ⟨v, huv, fun b hb => by simp [Sym2.mem_iff, hb.ne']⟩
        · exact ⟨u, huv.symm, fun b hb => by simp [Sym2.mem_iff, hb.ne']⟩
      have hN : (graft X s(u, v)).neighborSet (embed n a) =
          insert (Sum.inr 0) (embed n '' (X.neighborSet a \ {p})) := by
        ext y
        rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩
        · simp
        · simp [ha]
        · simp only [mem_neighborSet, graft_adj_embed, Set.mem_insert_iff, embed_ne_hub,
            false_or, (embed_injective n).mem_set_image, Set.mem_sdiff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h, hn⟩; exact ⟨h, fun hbp => hn ⟨ha, (hp b h).2 hbp⟩⟩
          · rintro ⟨h, hn⟩; exact ⟨h, fun hab => hn ((hp b h).1 hab.2)⟩
      rw [hN, Set.ncard_insert_of_notMem (by simp), Set.ncard_image_of_injective _
        (embed_injective n), Set.ncard_sdiff_singleton_of_mem (show p ∈ X.neighborSet a from hap)]
      have : 0 < (X.neighborSet a).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨p, hap⟩
      omega
    · have hN : (graft X s(u, v)).neighborSet (embed n a) = embed n '' X.neighborSet a := by
        ext y
        rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩
        · simp
        · simp [ha]
        · simp [ha, (embed_injective n).mem_set_image]
      rw [hN, Set.ncard_image_of_injective _ (embed_injective n)]
  have hleaf : (graft X s(u, v)).neighborSet (Sum.inl 0) = {Sum.inr 0} := by
    ext y
    rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩ <;> simp
  have hhub : (graft X s(u, v)).neighborSet (Sum.inr 0) =
      {Sum.inl 0, embed n u, embed n v} := by
    ext y
    rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩ <;> simp [Sym2.mem_iff]
  refine isTrivalentTree_of_connected ?_ (fun i => ?_) (fun j => ?_)
  · rw [connected_iff_exists_forall_reachable]
    refine ⟨Sum.inr 0, fun w => ?_⟩
    have hu : (graft X s(u, v)).Reachable (Sum.inr 0) (embed n u) :=
      (graft_adj_hub_embed.2 (Sym2.mem_mk_left u v)).reachable
    rcases vtx_cases w with rfl | rfl | ⟨a, rfl⟩
    · exact graft_adj_hub_leaf.reachable
    · rfl
    · refine hu.trans (reachable_map_of_adj (embed n) (fun a b hab => ?_)
        (hX.isTree.connected.preconnected u a))
      by_cases hm : a ∈ s(u, v) ∧ b ∈ s(u, v)
      · exact (graft_adj_hub_embed.2 hm.1).reachable.symm.trans
          (graft_adj_hub_embed.2 hm.2).reachable
      · exact (graft_adj_embed.2 ⟨hab, hm⟩).reachable
  · induction i using Fin.cases with
    | zero => rw [hleaf, Set.ncard_singleton]
    | succ i => exact (hdeg (Sum.inl i)).trans (hX.ncard_leaf i)
  · induction j using Fin.cases with
    | zero =>
      rw [hhub, Set.ncard_eq_three]
      exact ⟨_, _, _, leaf_ne_embed u, leaf_ne_embed v,
        fun h => huv.ne (embed_inj.1 h), rfl⟩
    | succ j => exact (hdeg (Sum.inr j)).trans (hX.ncard_internal j)

section prune

variable {Y : SimpleGraph (Vtx (n + 1))}

/-- In a trivalent tree with `n + 3` leaves where `Sum.inl 0` is attached to `Sum.inr 0`, the
vertex `Sum.inr 0` has two further neighbours, both shifted old vertices. -/
theorem exists_hub_neighbors (hY : IsTrivalentTree (n + 1 + 2) Y)
    (hLW : Y.Adj (Sum.inl 0) (Sum.inr 0)) :
    ∃ c d, c ≠ d ∧ ∀ y, Y.Adj (Sum.inr 0) y ↔ y = Sum.inl 0 ∨ y = embed n c ∨ y = embed n d := by
  have hmem : (Sum.inl 0 : Vtx (n + 1)) ∈ Y.neighborSet (Sum.inr 0) := hLW.symm
  have h2 : (Y.neighborSet (Sum.inr 0) \ {Sum.inl 0}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem hmem, hY.ncard_internal (0 : Fin (n + 1))]
  obtain ⟨x, y, hxy, hS⟩ := Set.ncard_eq_two.1 h2
  have key : ∀ z ∈ Y.neighborSet (Sum.inr 0) \ {Sum.inl 0}, ∃ c, z = embed n c := by
    rintro z ⟨hz, hz'⟩
    rcases vtx_cases z with rfl | rfl | h
    · exact absurd rfl hz'
    · exact absurd hz (Y.irrefl)
    · exact h
  obtain ⟨c, rfl⟩ := key x (by rw [hS]; simp)
  obtain ⟨d, rfl⟩ := key y (by rw [hS]; simp)
  refine ⟨c, d, fun h => hxy (h ▸ rfl), fun z => ?_⟩
  by_cases hz : z = Sum.inl 0
  · subst hz; simp [hLW.symm]
  · have : z ∈ Y.neighborSet (Sum.inr 0) ↔ z ∈ Y.neighborSet (Sum.inr 0) \ {Sum.inl 0} := by
      simp [hz]
    change z ∈ Y.neighborSet _ ↔ _
    rw [this, hS]
    simp [hz]

/-- Pruning a trivalent tree gives a trivalent tree, and grafting onto the joined edge
recovers the original tree. -/
theorem isTrivalentTree_prune_and_exists_graft_eq (hY : IsTrivalentTree (n + 1 + 2) Y)
    (hLW : Y.Adj (Sum.inl 0) (Sum.inr 0)) :
    IsTrivalentTree (n + 2) (prune Y) ∧ ∃ e ∈ (prune Y).edgeSet, graft (prune Y) e = Y := by
  obtain ⟨c, d, hcd, hhub⟩ := exists_hub_neighbors hY hLW
  have hubE : ∀ a, Y.Adj (Sum.inr 0) (embed n a) ↔ a = c ∨ a = d := fun a => by
    rw [hhub]; simp
  have hleaf : ∀ y, Y.Adj (Sum.inl 0) y ↔ y = Sum.inr 0 :=
    adj_iff_eq_of_ncard_neighborSet_eq_one (hY.ncard_leaf 0) hLW
  have leafE : ∀ a, ¬ Y.Adj (embed n a) (Sum.inl 0) := fun a h =>
    embed_ne_hub a ((hleaf _).1 h.symm)
  have hacyc := hY.isTree.isAcyclic
  have notri : ¬ Y.Adj (embed n c) (embed n d) :=
    not_adj_of_adj_of_adj_of_isAcyclic hacyc ((hubE c).2 (Or.inl rfl)) ((hubE d).2 (Or.inr rfl))
  have hpr : ∀ a b, (prune Y).Adj a b ↔
      a ≠ b ∧ (Y.Adj (embed n a) (embed n b) ∨ ((a = c ∨ a = d) ∧ (b = c ∨ b = d))) :=
    fun a b => by rw [prune_adj, hubE, hubE]
  refine ⟨?_, s(c, d), (hpr c d).2 ⟨hcd, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, ?_⟩
  · -- degrees
    have hdeg : ∀ a, ((prune Y).neighborSet a).ncard = (Y.neighborSet (embed n a)).ncard := by
      intro a
      set A : Set (Vtx n) := {b | Y.Adj (embed n a) (embed n b)} with hA
      have hYn : Y.neighborSet (embed n a) =
          embed n '' A ∪ {y | (a = c ∨ a = d) ∧ y = Sum.inr 0} := by
        ext y
        rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩
        · simp [leafE, hA]
        · simp [Y.adj_comm (embed n a), hubE, hA]
        · simp [(embed_injective n).mem_set_image, hA]
      by_cases ha : a = c ∨ a = d
      · obtain ⟨p, hpa, hp, hpn⟩ : ∃ p, p ≠ a ∧ (p = c ∨ p = d) ∧
            ∀ b, b ≠ a → (b = c ∨ b = d) → b = p := by
          rcases ha with rfl | rfl
          · exact ⟨d, hcd.symm, Or.inr rfl, fun b hb h => h.resolve_left hb⟩
          · exact ⟨c, hcd, Or.inl rfl, fun b hb h => h.resolve_right hb⟩
        have hPn : (prune Y).neighborSet a = insert p A := by
          ext b
          simp only [mem_neighborSet, hpr, Set.mem_insert_iff, hA, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨hab, h | ⟨-, hb⟩⟩
            · exact Or.inr h
            · exact Or.inl (hpn b (Ne.symm hab) hb)
          · rintro (rfl | h)
            · exact ⟨hpa.symm, Or.inr ⟨ha, hp⟩⟩
            · exact ⟨fun hab => h.ne (hab ▸ rfl), Or.inl h⟩
        have hpA : p ∉ A := fun h =>
          not_adj_of_adj_of_adj_of_isAcyclic hacyc ((hubE a).2 ha) ((hubE p).2 hp) h
        have hYn' : Y.neighborSet (embed n a) = insert (Sum.inr 0) (embed n '' A) := by
          rw [hYn]; ext y; simp [ha, or_comm]
        rw [hPn, hYn', Set.ncard_insert_of_notMem hpA, Set.ncard_insert_of_notMem (by simp),
          Set.ncard_image_of_injective _ (embed_injective n)]
      · have hPn : (prune Y).neighborSet a = A := by
          ext b
          simp only [mem_neighborSet, hpr, hA, Set.mem_ofPred_eq, ha, false_and, or_false]
          exact ⟨And.right, fun h => ⟨fun hab => h.ne (hab ▸ rfl), h⟩⟩
        rw [hPn, hYn]
        simp [ha, Set.ncard_image_of_injective _ (embed_injective n)]
    -- connectivity
    have hreach : ∀ b, Y.Adj (Sum.inr 0) (embed n b) → (prune Y).Reachable c b := by
      intro b hb
      by_cases hbc : c = b
      · subst hbc; rfl
      · exact ((hpr c b).2 ⟨hbc, Or.inr ⟨Or.inl rfl, (hubE b).1 hb⟩⟩).reachable
    obtain ⟨f, hf0, hf1, hfe⟩ : ∃ f : Vtx (n + 1) → Vtx n,
        f (Sum.inl 0) = c ∧ f (Sum.inr 0) = c ∧ ∀ a, f (embed n a) = a :=
      ⟨Sum.elim (fun i => Fin.cases (motive := fun _ => Vtx n) c (fun i' => Sum.inl i') i)
        (fun j => Fin.cases (motive := fun _ => Vtx n) c (fun j' => Sum.inr j') j),
        rfl, rfl, by rintro (i | j) <;> rfl⟩
    have hadj : ∀ x y, Y.Adj x y → (prune Y).Reachable (f x) (f y) := by
      intro x y h
      rcases vtx_cases x with rfl | rfl | ⟨a, rfl⟩ <;>
        rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩
      · exact absurd h (Y.irrefl)
      · rw [hf0, hf1]
      · exact absurd h.symm (leafE b)
      · rw [hf0, hf1]
      · exact absurd h (Y.irrefl)
      · rw [hf1, hfe]; exact hreach b h
      · exact absurd h (leafE a)
      · rw [hfe, hf1]; exact (hreach a h.symm).symm
      · rw [hfe, hfe]
        exact ((hpr a b).2 ⟨fun hab => h.ne (hab ▸ rfl), Or.inl h⟩).reachable
    refine isTrivalentTree_of_connected ⟨fun a b => ?_⟩ (fun i => ?_) (fun j => ?_)
    · simpa [hfe] using reachable_map_of_adj f hadj
        (hY.isTree.connected.preconnected (embed n a) (embed n b))
    · rw [hdeg]; exact hY.ncard_leaf i.succ
    · rw [hdeg]; exact hY.ncard_internal j.succ
  · -- grafting back
    ext x y
    rcases vtx_cases x with rfl | rfl | ⟨a, rfl⟩ <;>
      rcases vtx_cases y with rfl | rfl | ⟨b, rfl⟩
    · simp
    · simp [hLW]
    · simp only [graft_not_adj_leaf_embed, false_iff]; exact fun h => leafE b h.symm
    · simp [hLW.symm]
    · simp
    · simp [hubE, Sym2.mem_iff]
    · simp only [graft_not_adj_embed_leaf, false_iff]; exact leafE a
    · rw [graft_adj_embed_hub, Y.adj_comm, hubE, Sym2.mem_iff]
    · rw [graft_adj_embed, hpr]
      simp only [Sym2.mem_iff]
      constructor
      · rintro ⟨⟨-, h | h⟩, hn⟩
        · exact h
        · exact absurd h hn
      · intro h
        refine ⟨⟨fun hab => h.ne (hab ▸ rfl), Or.inl h⟩, ?_⟩
        rintro ⟨ha, hb⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Y.irrefl h
        · exact notri h
        · exact notri h.symm
        · exact Y.irrefl h

end prune

/-! ### Canonical trees and the count -/

/-- The trees obtained from the single edge by repeatedly grafting the new leaf onto an
edge. -/
def canonical : (n : ℕ) → Set (SimpleGraph (Vtx n))
  | 0 => {G | IsTrivalentTree 2 G}
  | n + 1 => {Y | ∃ X ∈ canonical n, ∃ e ∈ X.edgeSet, Y = graft X e}

theorem mem_canonical_succ {Y : SimpleGraph (Vtx (n + 1))} :
    Y ∈ canonical (n + 1) ↔ ∃ X ∈ canonical n, ∃ e ∈ X.edgeSet, Y = graft X e := Iff.rfl

theorem isTrivalentTree_of_mem_canonical :
    ∀ {n : ℕ} {G : SimpleGraph (Vtx n)}, G ∈ canonical n → IsTrivalentTree (n + 2) G
  | 0, _, h => h
  | _ + 1, _, ⟨_, hX, _, he, h⟩ =>
    h ▸ isTrivalentTree_graft (isTrivalentTree_of_mem_canonical hX) he

/-- In a trivalent tree with at least three leaves, the leaf `Sum.inl 0` is attached to an
internal vertex. -/
theorem exists_adj_leaf_iff {H : SimpleGraph (Vtx (n + 1))} (hH : IsTrivalentTree (n + 1 + 2) H) :
    ∃ j, ∀ y, H.Adj (Sum.inl 0) y ↔ y = Sum.inr j := by
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 (hH.ncard_leaf 0)
  have hadj : ∀ z, H.Adj (Sum.inl 0) z ↔ z = y := fun z => by
    change z ∈ H.neighborSet _ ↔ _; rw [hy, Set.mem_singleton_iff]
  rcases y with i | j
  · exfalso
    have hadj' : ∀ z, H.Adj (Sum.inl i) z ↔ z = Sum.inl 0 :=
      adj_iff_eq_of_ncard_neighborSet_eq_one (hH.ncard_leaf i) ((hadj _).2 rfl).symm
    have hcl : ∀ a b, H.Adj a b → a ∈ ({Sum.inl 0, Sum.inl i} : Set (Vtx (n + 1))) →
        b ∈ ({Sum.inl 0, Sum.inl i} : Set (Vtx (n + 1))) := by
      rintro a b h (rfl | rfl)
      · simp [(hadj b).1 h]
      · simp [(hadj' b).1 h]
    have := mem_of_reachable_of_closed hcl
      (hH.isTree.connected.preconnected (Sum.inl 0) (Sum.inr 0 : Vtx (n + 1))) (by simp)
    simp at this
  · exact ⟨j, hadj⟩

/-- Every leaf-labelled trivalent tree `H` with `n + 2` leaves has exactly one relabelling of
its internal vertices which is canonical. -/
theorem existsUnique_canonical : ∀ (n : ℕ) (H : SimpleGraph (Vtx n)),
    IsTrivalentTree (n + 2) H →
    ∃! p : canonical n × Equiv.Perm (Fin n), p.1.1 = H.comap (hat p.2)
  | 0, H, hH => by
    refine ⟨(⟨H, hH⟩, 1), by simp [coe_hat_one], ?_⟩
    rintro ⟨⟨G, hG⟩, σ⟩ -
    exact Prod.ext (Subtype.ext (eq_of_isTrivalentTree_two hG hH)) (Subsingleton.elim _ _)
  | n + 1, H, hH => by
    obtain ⟨j, hj⟩ := exists_adj_leaf_iff hH
    set H1 := H.comap (hat (Equiv.swap 0 j)) with hH1
    have hH1t : IsTrivalentTree (n + 1 + 2) H1 := isTrivalentTree_comap_hat hH _
    have hLW : H1.Adj (Sum.inl 0) (Sum.inr 0) := by simp [hH1, hj]
    obtain ⟨hPt, e1, he1, hge⟩ := isTrivalentTree_prune_and_exists_graft_eq hH1t hLW
    obtain ⟨⟨⟨G, hGc⟩, σ⟩, hG, huniq⟩ := existsUnique_canonical n (prune H1) hPt
    have hcomp : ∀ ρ : Equiv.Perm (Fin n),
        H.comap (hat (Equiv.Perm.decomposeFin.symm (j, ρ))) =
          graft ((prune H1).comap (hat ρ)) (e1.map (hat ρ).symm) := by
      intro ρ
      rw [coe_hat_decomposeFin, ← comap_comap, ← hH1, ← comap_graft, hge]
    have hG' : G = (prune H1).comap (hat σ) := hG
    refine ⟨(⟨graft G (e1.map (hat σ).symm), G, hGc, _,
      hG' ▸ map_symm_mem_edgeSet_comap _ he1, rfl⟩, Equiv.Perm.decomposeFin.symm (j, σ)),
      ?_, ?_⟩
    · change graft G _ = _
      rw [hcomp, hG']
    · rintro ⟨⟨G'', hG''⟩, π⟩ hπ
      obtain ⟨X, hXc, e, he, rfl⟩ := mem_canonical_succ.1 hG''
      obtain ⟨⟨p, ρ⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective π
      change graft X e = H.comap (hat (Equiv.Perm.decomposeFin.symm (p, ρ))) at hπ
      have hp : p = j := by
        have h : (graft X e).Adj (Sum.inl 0) (Sum.inr 0) := graft_adj_leaf_hub
        rw [hπ] at h
        simp only [comap_adj, hat_inl, hat_inr, Equiv.Perm.decomposeFin_symm_apply_zero] at h
        exact Sum.inr_injective ((hj _).1 h)
      subst hp
      rw [hcomp] at hπ
      have hX : X = (prune H1).comap (hat ρ) := by
        rw [← prune_graft he, hπ, prune_graft (map_symm_mem_edgeSet_comap _ he1)]
      have h := huniq (⟨X, hXc⟩, ρ) hX
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Prod.ext (Subtype.ext ?_) rfl
      change graft X e = graft X _
      rw [hπ, ← hX]

/-- The canonical trees with `n + 2` leaves are in bijection with the tree shapes. -/
theorem card_treeShape_eq_card_canonical (n : ℕ) :
    Nat.card (TreeShape (n + 2)) = Nat.card (canonical n) := by
  let g : canonical n → TreeShape (n + 2) := fun G =>
    Quotient.mk (treeShapeSetoid (n + 2)) ⟨G.1, isTrivalentTree_of_mem_canonical G.2⟩
  refine (Nat.card_congr (Equiv.ofBijective g ⟨fun G G' h => ?_, fun T => ?_⟩)).symm
  · obtain ⟨φ, hφ⟩ := Quotient.exact h
    obtain ⟨τ, hτ⟩ := exists_perm_of_iso φ hφ
    have hu := (existsUnique_canonical n G'.1 (isTrivalentTree_of_mem_canonical G'.2)).unique
      (y₁ := (G, τ)) (y₂ := (G', 1)) hτ (by simp [coe_hat_one])
    exact congrArg Prod.fst hu
  · induction T using Quotient.inductionOn with
    | h H =>
    obtain ⟨⟨G, σ⟩, hG, -⟩ := existsUnique_canonical n H.1 H.2
    exact ⟨G, Quotient.sound (exists_iso_of_eq_comap hG)⟩

/-- A trivalent tree with `n + 2` leaves has `2n + 1` edges. -/
theorem card_edgeSet_of_isTrivalentTree {G : SimpleGraph (Vtx n)}
    (hG : IsTrivalentTree (n + 2) G) : Nat.card G.edgeSet = 2 * n + 1 := by
  classical
  have h := card_edgeFinset_trivalentTree hG
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, h]
  omega

theorem card_canonical_succ (n : ℕ) :
    Nat.card (canonical (n + 1)) = (2 * n + 1) * Nat.card (canonical n) := by
  classical
  let F : (Σ X : canonical n, X.1.edgeSet) → canonical (n + 1) := fun p =>
    ⟨graft p.1.1 p.2.1, p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
  have hF : Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨X, hX⟩, ⟨e, he⟩⟩ ⟨⟨X', hX'⟩, ⟨e', he'⟩⟩ h
      have h' : graft X e = graft X' e' := congrArg Subtype.val h
      have he0 : e ∈ X.edgeSet := he
      have he0' : e' ∈ X'.edgeSet := he'
      obtain rfl : X = X' := by rw [← prune_graft he0, h', prune_graft he0']
      obtain rfl : e = e' := Sym2.ext fun a => by
        rw [← graft_adj_hub_embed (X := X), h', graft_adj_hub_embed]
      rfl
    · rintro ⟨Y, X, hX, e, he, rfl⟩
      exact ⟨⟨⟨X, hX⟩, ⟨e, he⟩⟩, rfl⟩
  have : Fintype (canonical n) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_sigma]
  simp only [fun X : canonical n => card_edgeSet_of_isTrivalentTree
    (isTrivalentTree_of_mem_canonical X.2), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]
  ring

theorem card_canonical (n : ℕ) : Nat.card (canonical n) = Nat.doubleFactorial (2 * n - 1) := by
  induction n with
  | zero =>
    rw [← card_treeShape_eq_card_canonical]
    exact card_treeShape_two
  | succ n ih =>
    rw [card_canonical_succ, ih]
    rcases n with _ | n
    · rfl
    · rw [show 2 * (n + 1 + 1) - 1 = (2 * n + 1) + 2 by omega, Nat.doubleFactorial_add_two,
        show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      ring

end TrivalentTree

/-- A finite tree whose leaves carry the distinct labels `0, …, k - 1` and whose other vertices
have degree three has `k - 2` internal vertices and `2k - 3` edges (degree sum: with `j`
internal vertices, `k + 3j = 2(k + j - 1)`). -/
theorem card_internal_and_card_edgeFinset_of_isTree {α : Type*} [Fintype α] [DecidableEq α]
    {H : SimpleGraph α} [DecidableRel H.Adj] (hH : H.IsTree) {k : ℕ} (ℓ : Fin k ↪ α)
    (hleaf : ∀ i, H.degree (ℓ i) = 1) (hint : ∀ v, (∀ i, ℓ i ≠ v) → H.degree v = 3) :
    (Finset.univ.filter fun v => ∀ i, ℓ i ≠ v).card = k - 2 ∧
      H.edgeFinset.card = 2 * k - 3 := by
  have hcompl : (Finset.univ.filter fun v => ¬ ∀ i, ℓ i ≠ v) = Finset.univ.map ℓ := by
    ext v
    simp
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun v => ∀ i, ℓ i ≠ v)
  rw [hcompl, Finset.card_map, Finset.card_univ, Fintype.card_fin, Finset.card_univ] at hcard
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => ∀ i, ℓ i ≠ v)
    (fun v => H.degree v)
  rw [hcompl, Finset.sum_map, H.sum_degrees_eq_twice_card_edges,
    Finset.sum_congr rfl fun v hv => hint v (Finset.mem_filter.1 hv).2] at hsum
  simp only [hleaf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at hsum
  have htree := hH.card_edgeFinset
  omega

open TrivalentTree in
/-- **The number of leaf-labelled trivalent tree shapes.** For `k ≥ 2`,
`|𝒯_k| = (2k - 5)!!`, with `(-1)!! = 1` (here `2 * 2 - 5 = 0` in `ℕ` and `0‼ = 1`). -/
theorem card_treeShape {k : ℕ} (hk : 2 ≤ k) :
    Nat.card (TreeShape k) = Nat.doubleFactorial (2 * k - 5) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [card_treeShape_eq_card_canonical, card_canonical]
  congr 1

end PercLib.Percolation.Bond
