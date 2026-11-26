/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. Statements from the wiki article `multipoint-trees` (sweep
products and minimum-product spanning trees); T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, §I.2. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Multipoint.Sweep
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Sweep products and minimum-product spanning trees

A rooted tree on a finite type, given by a root `r` and a parent map `p` with every vertex
reaching `r` under iteration of `p`, determines the graph with edges `{x, p x}`; this graph is a
spanning tree. For a finite set `A` in a metric space, each nonroot factor `diam(A_x)` of a sweep
tree product is at least the length of the parent edge `d(x, p x)`, so every sweep tree product,
hence `Sweep(A)`, is at least `diam(A)` times the edge-length product of a minimum-product
spanning tree. This holds in every metric space; for an ultrametric it is one half of the sweep
identity of the wiki article.

## Main results

* `SimpleGraph.isTree_fromEdgeSet_parent`: the parent graph of a rooted tree is a tree;
* `prod_edgeFinset_fromEdgeSet_parent`: a product over its edges is the product over the
  nonroot vertices of the parent edges;
* `diam_mul_prod_le_sweepProduct`: `diam(A) ∏_{e ∈ T} d(e) ≤ Sweep(A)` for a spanning tree `T`
  of `A` of minimum edge-length product;
* `exists_isTree_forall_prod_le`: such a spanning tree exists when `A` is nonempty.
-/

@[expose] public section

noncomputable section

open Finset SimpleGraph

namespace PercLib.Percolation.Bond

/-! ### The parent graph of a rooted tree -/

section RootedTree

variable {V : Type*} {p : V → V} {r : V}

/-- In a rooted tree a vertex other than the root is not fixed by the parent map. -/
theorem apply_ne_self_of_iterate_eq (hr : ∀ y, ∃ n, p^[n] y = r) {x : V} (hx : x ≠ r) :
    p x ≠ x := by
  intro hfix
  obtain ⟨n, hn⟩ := hr x
  exact hx (by rw [← hn, Function.iterate_fixed hfix])

/-- Every vertex is joined to its iterated parents in the parent graph. -/
theorem reachable_fromEdgeSet_parent_iterate (x : V) (n : ℕ) :
    (fromEdgeSet (Set.range fun x => s(x, p x))).Reachable x (p^[n] x) := by
  induction n generalizing x with
  | zero => exact Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    refine Reachable.trans ?_ (ih (p x))
    by_cases h : x = p x
    · rw [← h]
    · exact Adj.reachable ((fromEdgeSet_adj _).2 ⟨⟨x, rfl⟩, h⟩)

/-- In a rooted tree, two parent edges of nonroot vertices coincide only for equal vertices. -/
theorem injOn_parent_edge (hr : ∀ y, ∃ n, p^[n] y = r) :
    Set.InjOn (fun x => s(x, p x)) {x | x ≠ r} := by
  intro x hx y hy hxy
  rcases Sym2.eq_iff.1 hxy with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  · exfalso
    -- `x = p y` and `p x = y`, so the iterates of `x` alternate between `x` and `p x`
    have halt : ∀ n, p^[n] x = x ∨ p^[n] x = p x := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with h | h <;> rw [h]
        · exact Or.inr rfl
        · exact Or.inl (by rw [h2, h1])
    obtain ⟨n, hn⟩ := hr x
    rcases halt n with h | h
    · exact hx (h ▸ hn)
    · exact hy (by rw [← h2, ← h, hn])

/-- The edge set of the parent graph: the parent edges of the nonroot vertices. -/
theorem edgeSet_fromEdgeSet_parent (hroot : p r = r) (hr : ∀ y, ∃ n, p^[n] y = r) :
    (fromEdgeSet (Set.range fun x => s(x, p x))).edgeSet = (fun x => s(x, p x)) '' {x | x ≠ r} := by
  rw [edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Set.mem_range, Sym2.mem_diagSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, rfl⟩, hd⟩
    refine ⟨x, fun hx => hd ?_, rfl⟩
    rw [hx, hroot]
    exact Sym2.mk_isDiag_iff.2 rfl
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, fun hd => apply_ne_self_of_iterate_eq hr hx (Sym2.mk_isDiag_iff.1 hd).symm⟩

variable [Fintype V] [DecidableEq V]

/-- The edge finset of the parent graph is the image of the nonroot vertices. -/
theorem edgeFinset_fromEdgeSet_parent [Fintype (fromEdgeSet (Set.range fun x => s(x, p x))).edgeSet]
    (hroot : p r = r) (hr : ∀ y, ∃ n, p^[n] y = r) :
    (fromEdgeSet (Set.range fun x => s(x, p x))).edgeFinset =
      (univ.erase r).image fun x => s(x, p x) := by
  refine Finset.coe_injective ?_
  rw [coe_edgeFinset, edgeSet_fromEdgeSet_parent hroot hr, coe_image, coe_erase, coe_univ]
  congr 1
  ext x
  simp

/-- **The parent graph of a rooted tree is a tree.** -/
theorem _root_.SimpleGraph.isTree_fromEdgeSet_parent (hroot : p r = r)
    (hr : ∀ y, ∃ n, p^[n] y = r) : (fromEdgeSet (Set.range fun x => s(x, p x))).IsTree := by
  classical
  have : Nonempty V := ⟨r⟩
  rw [isTree_iff_connected_and_card]
  refine ⟨⟨fun x y => ?_⟩, ?_⟩
  · obtain ⟨m, hm⟩ := hr x
    obtain ⟨n, hn⟩ := hr y
    have hx := reachable_fromEdgeSet_parent_iterate (p := p) x m
    have hy := reachable_fromEdgeSet_parent_iterate (p := p) y n
    rw [hm] at hx
    rw [hn] at hy
    exact hx.trans hy.symm
  · rw [← coe_edgeFinset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      edgeFinset_fromEdgeSet_parent hroot hr,
      card_image_of_injOn (fun x hx y hy h => injOn_parent_edge hr
        (by simpa using hx) (by simpa using hy) h),
      card_erase_of_mem (mem_univ r), card_univ, Nat.card_eq_fintype_card]
    have : 0 < Fintype.card V := Fintype.card_pos
    omega

/-- A product over the edges of the parent graph is the product of the parent edges over the
nonroot vertices. -/
theorem prod_edgeFinset_fromEdgeSet_parent {M : Type*} [CommMonoid M]
    [Fintype (fromEdgeSet (Set.range fun x => s(x, p x))).edgeSet] (f : Sym2 V → M)
    (hroot : p r = r) (hr : ∀ y, ∃ n, p^[n] y = r) :
    ∏ e ∈ (fromEdgeSet (Set.range fun x => s(x, p x))).edgeFinset, f e =
      ∏ x ∈ univ.erase r, f s(x, p x) := by
  rw [edgeFinset_fromEdgeSet_parent hroot hr, prod_image (fun x hx y hy h => injOn_parent_edge hr
    (by simpa using hx) (by simpa using hy) h)]

end RootedTree

/-! ### The sweep lower bound -/

variable {X : Type*} [MetricSpace X] [DecidableEq X]

open Classical in
/-- **Sweep lower bound.** In any metric space, if `T` is a spanning tree of the finite set `A`
of minimum edge-length product, then `diam(A) ∏_{e ∈ T} d(e) ≤ Sweep(A)`: every rooted tree
determines a spanning tree, and each nonroot set `A_x` contains the parent edge of `x`. -/
theorem diam_mul_prod_le_sweepProduct {A : Finset X} {T : SimpleGraph A} (hT : T.IsTree)
    (hmin : ∀ T' : SimpleGraph A, T'.IsTree →
      ∏ e ∈ T.edgeFinset, Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩ e ≤
        ∏ e ∈ T'.edgeFinset,
          Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩ e) :
    Metric.diam (A : Set X) *
        ∏ e ∈ T.edgeFinset, Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩ e ≤
      sweepProduct A := by
  obtain ⟨a⟩ := hT.1.nonempty
  refine le_sweepProduct ⟨a.1, a.2⟩ fun t hroot hreach => ?_
  have hG := isTree_fromEdgeSet_parent hroot hreach
  refine (mul_le_mul_of_nonneg_left (hmin _ hG) Metric.diam_nonneg).trans ?_
  have hprod := prod_edgeFinset_fromEdgeSet_parent
    (Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩) hroot hreach
  have key : Metric.diam (A : Set X) * ∏ x ∈ univ.erase t.1, dist (x : X) (t.2 x) ≤
      ∏ x : A, Metric.diam (if x = t.1 then (A : Set X)
        else insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x})) := by
    rw [← mul_prod_erase univ _ (mem_univ t.1)]
    simp only [↓reduceIte]
    refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun x _ => dist_nonneg) fun x hx => ?_)
        Metric.diam_nonneg
    have hx : x ≠ t.1 := ne_of_mem_erase hx
    simp only [hx, ↓reduceIte]
    rw [_root_.dist_comm]
    have hfin : (insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x})).Finite :=
      (Set.toFinite _).insert _
    exact Metric.dist_le_diam_of_mem hfin.isBounded (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ ⟨x, ⟨0, rfl⟩, rfl⟩)
  refine le_trans (le_of_eq ?_) key
  congr 1
  convert hprod using 2 with x
  all_goals first | rfl | exact Finset.coe_injective (by rw [coe_edgeFinset, coe_edgeFinset])

open Classical in
/-- Non-vacuity of the minimality hypothesis: every nonempty finite set carries a spanning tree
of minimum edge-length product. -/
theorem exists_isTree_forall_prod_le {A : Finset X} (hA : A.Nonempty) :
    ∃ T : SimpleGraph A, T.IsTree ∧ ∀ T' : SimpleGraph A, T'.IsTree →
      ∏ e ∈ T.edgeFinset, Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩ e ≤
        ∏ e ∈ T'.edgeFinset,
          Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩ e := by
  have : Nonempty A := hA.to_subtype
  obtain ⟨T₀, -, hT₀⟩ := (connected_top (V := A)).exists_isTree_le
  obtain ⟨T, hT, hmin⟩ := (univ.filter fun T : SimpleGraph A => T.IsTree).exists_min_image
    (fun T => ∏ e ∈ T.edgeFinset,
      Sym2.lift ⟨fun x y : A => dist (x : X) y, fun _ _ => dist_comm _ _⟩ e)
    ⟨T₀, mem_filter.2 ⟨mem_univ _, hT₀⟩⟩
  exact ⟨T, (mem_filter.1 hT).2, fun T' h' => hmin T' (mem_filter.2 ⟨mem_univ _, h'⟩)⟩

end PercLib.Percolation.Bond
