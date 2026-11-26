/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, using mathlib's `SimpleGraph`, lists and finite sets. Mathematical reference: the
probabilistic depth-first search of I. Gladkov and I. Pak, *Exploring mazes at random*; the pivot
involution argument is the one written out in the PercLib wiki article on adaptive three-point
bounds. No source text or code is copied.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic.Ring

/-! # The pivot involution of a randomised depth-first search

A recursive depth-first search on a finite graph is encoded by an *order function*
`σ : V → V → List V`: on entering `u` from its parent `p`, the search examines the vertices of
`σ u p` in this order, and descends immediately into each vertex not yet visited.
`DFS.visit σ n p u S` is the list of discoveries `(child, parent)`, in discovery order, made by the
call at `u` (entered from `p`) when the vertices of `S` are already visited, with recursion depth
at most `n`.

## Main results

* `PercLib.DFS.visit_congr`: two runs agree as long as they examine the same vertices with the
  same visited status.
* `PercLib.DFS.visit_closure`: a run with enough fuel visits every neighbour of every vertex it
  discovers.
* `PercLib.DFS.visit_swap_decomposition`: reversing the child order at a vertex with two children
  exchanges the two child blocks of the discovery list and changes nothing else.
* `PercLib.coinRun_flipCoin`: for the randomised search (`PercLib.coinRun`: a fair coin at each
  vertex of degree three reverses a fixed order `ρ` of the other neighbours), flipping the coin at a
  branching vertex of the discovery tree exchanges its two child blocks.
* `PercLib.exists_involutive_coinRun_pivot`: an involution of the coin space keeping the discovery
  tree and exchanging the discovery orders of two leaf targets `B, C`.
* `PercLib.card_filter_idxOf_lt_div`: `B` is discovered before `C` for exactly half of the coin
  assignments.
* `PercLib.card_filter_coinRun_eq_of_branching`: given the discovery tree, the coins at its
  branching vertices are uniform (independent and fair).

The order `ρ u p` is an arbitrary listing of the neighbours of `u` other than `p`; no plane
embedding or cyclic order is used. The coin space is `{u // G.degree u = 3} → Bool` with the
uniform law; an involution of a finite set is a bijection, so it preserves that law.
-/

@[expose] public section

namespace PercLib
namespace DFS

variable {V : Type*} [DecidableEq V]

/-- The loop of the search at `u` over the candidate list, from the discoveries `L` so far;
`S` is the visited set at entry and `rec` the recursive call. -/
def visitList (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V) :
    List V → List (V × V) → List (V × V)
  | [], L => L
  | w :: ws, L => visitList rec u S ws
      (if w ∈ S ∨ w ∈ L.map Prod.fst then L
        else L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)))

/-- The discoveries `(child, parent)` of the recursive search at `u`, entered from `p`, with the
vertices of `S` already visited and recursion depth at most `n`. -/
def visit (σ : V → V → List V) : ℕ → V → V → Finset V → List (V × V)
  | 0, _, _, _ => []
  | n + 1, p, u, S => visitList (visit σ n) u S (σ u p) []

@[simp] theorem visitList_nil (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V)
    (L : List (V × V)) : visitList rec u S [] L = L := rfl

theorem visitList_cons (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V) (w : V)
    (ws : List V) (L : List (V × V)) :
    visitList rec u S (w :: ws) L = visitList rec u S ws
      (if w ∈ S ∨ w ∈ L.map Prod.fst then L
        else L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset))) := rfl

@[simp] theorem visit_zero (σ : V → V → List V) (p u : V) (S : Finset V) :
    visit σ 0 p u S = [] := rfl

theorem visit_succ (σ : V → V → List V) (n : ℕ) (p u : V) (S : Finset V) :
    visit σ (n + 1) p u S = visitList (visit σ n) u S (σ u p) [] := rfl

theorem exists_visitList_eq_append (rec : V → V → Finset V → List (V × V)) (u : V)
    (S : Finset V) : ∀ (ws : List V) (L : List (V × V)), ∃ M, visitList rec u S ws L = L ++ M
  | [], L => ⟨[], by simp⟩
  | w :: ws, L => by
    obtain ⟨M, hM⟩ := exists_visitList_eq_append rec u S ws
      (if w ∈ S ∨ w ∈ L.map Prod.fst then L
        else L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)))
    rw [visitList_cons, hM]
    split_ifs
    · exact ⟨M, rfl⟩
    · exact ⟨(w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)) ++ M, by simp⟩

/-- Induction along the loop: a property of the discovery list preserved by every new block. -/
theorem visitList_induction (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V)
    (Q : List (V × V) → Prop) (ws : List V)
    (hstep : ∀ L w, w ∈ ws → Q L → w ∉ S → w ∉ L.map Prod.fst →
      Q (L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)))) :
    ∀ L, Q L → Q (visitList rec u S ws L) := by
  induction ws with
  | nil => intro L h; exact h
  | cons w ws ih =>
    intro L hL
    rw [visitList_cons]
    apply ih (fun L w' hw' => hstep L w' (List.mem_cons_of_mem _ hw'))
    split_ifs with h
    · exact hL
    · simp only [not_or] at h
      exact hstep L w List.mem_cons_self hL h.1 h.2

theorem mem_or_mem_visitList (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V) :
    ∀ (ws : List V) (L : List (V × V)) (w : V), w ∈ ws →
      w ∈ S ∨ w ∈ (visitList rec u S ws L).map Prod.fst
  | [], _, _, h => absurd h List.not_mem_nil
  | w :: ws, L, w', h => by
    rw [visitList_cons]
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨M, hM⟩ := exists_visitList_eq_append rec u S ws
        (if w' ∈ S ∨ w' ∈ L.map Prod.fst then L
          else L ++ (w', u) :: rec u w' (insert w' (S ∪ (L.map Prod.fst).toFinset)))
      rw [hM]
      split_ifs with hc
      · rcases hc with hc | hc
        · exact Or.inl hc
        · exact Or.inr (by simp only [List.map_append, List.mem_append]; exact Or.inl hc)
      · exact Or.inr (by simp)
    · exact mem_or_mem_visitList rec u S ws _ w' h

/-- Basic shape of a run: discovered vertices are new and distinct, every parent is the start
vertex or discovered earlier. -/
theorem visit_wf (σ : V → V → List V) : ∀ (n : ℕ) (p u : V) (S : Finset V), u ∈ S →
    ((visit σ n p u S).map Prod.fst).Nodup ∧ (∀ e ∈ visit σ n p u S, e.1 ∉ S) ∧
    (∀ e ∈ visit σ n p u S, e.2 = u ∨ e.2 ∈ (visit σ n p u S).map Prod.fst) ∧
    (visit σ n p u S).Pairwise (fun e f => e.2 ≠ f.1)
  | 0, p, u, S, _ => by simp
  | n + 1, p, u, S, hu => by
    rw [visit_succ]
    apply visitList_induction _ u S (fun L => (L.map Prod.fst).Nodup ∧ (∀ e ∈ L, e.1 ∉ S) ∧
      (∀ e ∈ L, e.2 = u ∨ e.2 ∈ L.map Prod.fst) ∧ L.Pairwise (fun e f => e.2 ≠ f.1)) _ _ _
      (by simp)
    intro L w _ ⟨h1, h2, h3, h4⟩ hwS hwL
    obtain ⟨k1, k2, k3, k4⟩ := visit_wf σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
      (Finset.mem_insert_self _ _)
    set D := visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
    have k2' : ∀ e ∈ D, e.1 ≠ w ∧ e.1 ∉ S ∧ e.1 ∉ L.map Prod.fst := by
      intro e he
      have := k2 e he
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, not_or] at this
      exact this
    have huw : u ≠ w := fun h => hwS (h ▸ hu)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons]
      refine List.nodup_append.2 ⟨h1, List.nodup_cons.2 ⟨?_, k1⟩, ?_⟩
      · intro hw
        obtain ⟨e, he, hew⟩ := List.mem_map.1 hw
        exact (k2' e he).1 hew
      · intro a ha b hb hab
        subst hab
        rcases List.mem_cons.1 hb with hb | hb
        · exact hwL (hb ▸ ha)
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
          exact (k2' e he).2.2 ha
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact h2 e he
      · rcases List.mem_cons.1 he with rfl | he
        · exact hwS
        · exact (k2' e he).2.1
    · intro e he
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      rcases List.mem_append.1 he with he | he
      · rcases h3 e he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.1 he with rfl | he
        · exact Or.inl rfl
        · rcases k3 e he with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
    · refine List.pairwise_append.2 ⟨h4, List.pairwise_cons.2 ⟨?_, k4⟩, ?_⟩
      · intro f hf h
        exact (k2' f hf).2.1 (h ▸ hu)
      · intro e he f hf h
        have hpar : e.2 ∈ S ∨ e.2 ∈ L.map Prod.fst := by
          rcases h3 e he with h' | h'
          · exact Or.inl (h' ▸ hu)
          · exact Or.inr h'
        rcases List.mem_cons.1 hf with rfl | hf
        · rcases hpar with h' | h' <;> simp_all
        · rcases hpar with h' | h'
          · exact (k2' f hf).2.1 (h ▸ h')
          · exact (k2' f hf).2.2 (h ▸ h')

/-- Every discovery is along an edge, when the order function lists only neighbours. -/
theorem visit_adj {G : SimpleGraph V} {σ : V → V → List V}
    (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w) : ∀ (n : ℕ) (p u : V) (S : Finset V),
    ∀ e ∈ visit σ n p u S, G.Adj e.2 e.1
  | 0, _, _, _ => by simp
  | n + 1, p, u, S => by
    rw [visit_succ]
    apply visitList_induction _ u S (fun L => ∀ e ∈ L, G.Adj e.2 e.1) _ _ _ (by simp)
    intro L w hw hL _ _ e he
    rcases List.mem_append.1 he with he | he
    · exact hL e he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hσ' _ _ _ hw
      · exact visit_adj hσ' n u w _ e he

/-- A child discovered directly from the start vertex is one of its candidates. -/
theorem mem_of_mem_visit (σ : V → V → List V) (n : ℕ) (p u x : V) (S : Finset V) (hu : u ∈ S)
    (h : (x, u) ∈ visit σ n p u S) : x ∈ σ u p := by
  cases n with
  | zero => simp at h
  | succ n =>
    rw [visit_succ] at h
    revert h x
    apply visitList_induction _ u S (fun L => ∀ x, (x, u) ∈ L → x ∈ σ u p) _ _ _ (by simp)
    intro L w hw hL hwS _ x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL x hx
    · rcases List.mem_cons.1 hx with h | hx
      · cases h; exact hw
      · obtain ⟨-, k2, k3, -⟩ := visit_wf σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
          (Finset.mem_insert_self _ _)
        rcases k3 _ hx with h | h
        · exact absurd (h ▸ hu) hwS
        · obtain ⟨e, he, hee⟩ := List.mem_map.1 h
          exact absurd (by simp [hu]) (hee ▸ k2 e he)

/-- **Lockstep.** Two runs coincide when, at every vertex the first run enters, the order
functions agree and the examined vertices have the same visited status. -/
theorem visit_congr {σ σ' : V → V → List V} : ∀ (n : ℕ) (p u : V) (S₁ S₂ : Finset V),
    (∀ z, (z = u ∨ z ∈ (visit σ n p u S₁).map Prod.fst) →
      (∀ q, σ' z q = σ z q) ∧ ∀ q, ∀ w ∈ σ z q, (w ∈ S₂ ↔ w ∈ S₁)) →
    visit σ' n p u S₂ = visit σ n p u S₁
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, u, S₁, S₂, h => by
    rw [visit_succ, visit_succ, (h u (Or.inl rfl)).1 p]
    have key : ∀ (ws : List V) (L : List (V × V)), (∀ w ∈ ws, (w ∈ S₂ ↔ w ∈ S₁)) →
        (∀ z ∈ (visitList (visit σ n) u S₁ ws L).map Prod.fst,
          (∀ q, σ' z q = σ z q) ∧ ∀ q, ∀ w ∈ σ z q, (w ∈ S₂ ↔ w ∈ S₁)) →
        visitList (visit σ' n) u S₂ ws L = visitList (visit σ n) u S₁ ws L := by
      intro ws
      induction ws with
      | nil => intro L _ _; rfl
      | cons w ws ih =>
        intro L hws hz
        rw [visitList_cons, visitList_cons]
        have hw := hws w List.mem_cons_self
        have hws' : ∀ w' ∈ ws, (w' ∈ S₂ ↔ w' ∈ S₁) :=
          fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')
        by_cases hc : w ∈ S₁ ∨ w ∈ L.map Prod.fst
        · have hc' : w ∈ S₂ ∨ w ∈ L.map Prod.fst := by rwa [hw]
          simp only [hc, hc', ↓reduceIte]
          rw [visitList_cons] at hz
          simp only [hc, ↓reduceIte] at hz
          exact ih L hws' hz
        · have hc' : ¬ (w ∈ S₂ ∨ w ∈ L.map Prod.fst) := by rwa [hw]
          simp only [hc, hc', ↓reduceIte]
          rw [visitList_cons] at hz
          simp only [hc, ↓reduceIte] at hz
          obtain ⟨M, hM⟩ := exists_visitList_eq_append (visit σ n) u S₁ ws
            (L ++ (w, u) :: visit σ n u w (insert w (S₁ ∪ (L.map Prod.fst).toFinset)))
          have hrec : visit σ' n u w (insert w (S₂ ∪ (L.map Prod.fst).toFinset)) =
              visit σ n u w (insert w (S₁ ∪ (L.map Prod.fst).toFinset)) := by
            apply visit_congr n u w
            intro z hz2
            have hzmem : z ∈ (visitList (visit σ n) u S₁ ws
                (L ++ (w, u) :: visit σ n u w (insert w (S₁ ∪ (L.map Prod.fst).toFinset)))).map
                  Prod.fst := by
              rw [hM]
              simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
              tauto
            obtain ⟨h1, h2⟩ := hz z hzmem
            refine ⟨h1, fun q w' hw' => ?_⟩
            simp only [Finset.mem_insert, Finset.mem_union, h2 q w' hw']
          rw [hrec]
          exact ih _ hws' hz
    exact key _ [] (fun w hw => (h u (Or.inl rfl)).2 p w hw) (fun z hz => h z (Or.inr hz))

variable [Fintype V]

theorem card_compl_insert_lt {S T : Finset V} {w : V} {n : ℕ} (hw : w ∉ S)
    (hn : Sᶜ.card < n + 1) : (insert w (S ∪ T))ᶜ.card < n := by
  have : (insert w (S ∪ T))ᶜ ⊂ Sᶜ := by
    refine Finset.ssubset_iff_of_subset (Finset.compl_subset_compl.2 ?_) |>.2 ⟨w, ?_, ?_⟩
    · intro a ha; simp [ha]
    · simpa using hw
    · simp
  have := Finset.card_lt_card this
  omega

/-- **Closure.** A run with enough fuel, from an order function listing all neighbours except the
parent, leaves no unvisited neighbour of the start vertex or of any discovered vertex. -/
theorem visit_closure {G : SimpleGraph V} {σ : V → V → List V}
    (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p) : ∀ (n : ℕ) (p u : V) (S : Finset V),
    u ∈ S → p ∈ S → Sᶜ.card < n →
    ∀ z, (z = u ∨ z ∈ (visit σ n p u S).map Prod.fst) → ∀ w, G.Adj z w →
      w ∈ S ∨ w ∈ (visit σ n p u S).map Prod.fst
  | 0, _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, u, S, hu, hp, hn => by
    rw [visit_succ]
    have hQ := visitList_induction (visit σ n) u S
      (fun L => ∀ z ∈ L.map Prod.fst, ∀ w, G.Adj z w → w ∈ S ∨ w ∈ L.map Prod.fst) (σ u p)
      (by
        intro L w _ hL hwS _ z hz w' hzw'
        have IH := visit_closure hσ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
          (Finset.mem_insert_self _ _) (by simp [hu]) (card_compl_insert_lt hwS hn)
        simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with hz | hz
        · rcases hL z hz w' hzw' with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases IH z hz w' hzw' with h | h
          · simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at h
            tauto
          · tauto) [] (by simp)
    intro z hz w hzw
    rcases hz with rfl | hz
    · by_cases hwp : w = p
      · exact Or.inl (hwp ▸ hp)
      · exact mem_or_mem_visitList _ z S _ [] w (hσ _ _ _ hzw hwp)
    · exact hQ z hz w hzw

omit [DecidableEq V] [Fintype V] in
theorem eq_pair_or_eq_pair_of_length_le_two {l : List V} {x y : V} (hl : l.length ≤ 2)
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) : l = [x, y] ∨ l = [y, x] := by
  match l, hl, hx, hy with
  | [], _, hx, _ => simp at hx
  | [a], _, hx, hy =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  | [a, b], _, hx, hy =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
  | _ :: _ :: _ :: _, hl, _, _ => simp at hl

variable {G : SimpleGraph V}

/-- **The pivot at one vertex.** If the search at `v` examines `[x, y]` and discovers both, then
examining `[y, x]` instead exchanges the two child blocks; each block has no unvisited
neighbour once it is finished. -/
theorem visit_swap_at {σ σ' : V → V → List V}
    (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p) (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w)
    {v : V} (hv : ∀ z, z ≠ v → ∀ q, σ' z q = σ z q)
    {n : ℕ} {p x y : V} {S : Finset V} (hxy : x ≠ y) (hvS : v ∈ S)
    (hn : Sᶜ.card < n + 1) (hσv : σ v p = [x, y]) (hσ'v : σ' v p = [y, x])
    (hx : (x, v) ∈ visit σ (n + 1) p v S) (hy : (y, v) ∈ visit σ (n + 1) p v S) :
    ∃ t₁ t₂ : List (V × V), visit σ (n + 1) p v S = (x, v) :: t₁ ++ (y, v) :: t₂ ∧
      visit σ' (n + 1) p v S = (y, v) :: t₂ ++ (x, v) :: t₁ ∧
      (∀ c ∈ ((x, v) :: t₁).map Prod.fst, ∀ a, G.Adj c a →
        a ∈ S ∨ a ∈ ((x, v) :: t₁).map Prod.fst) ∧
      (∀ c ∈ ((y, v) :: t₂).map Prod.fst, ∀ a, G.Adj c a →
        a ∈ S ∨ a ∈ ((x, v) :: t₁ ++ (y, v) :: t₂).map Prod.fst) := by
  have hxS : x ∉ S := (visit_wf σ (n + 1) p v S hvS).2.1 _ hx
  have hyS : y ∉ S := (visit_wf σ (n + 1) p v S hvS).2.1 _ hy
  have hxv : x ≠ v := fun h => hxS (h ▸ hvS)
  have hyv : y ≠ v := fun h => hyS (h ▸ hvS)
  set Dx := visit σ n v x (insert x S) with hDx
  obtain ⟨-, kx2, kx3, -⟩ := visit_wf σ n v x (insert x S) (Finset.mem_insert_self _ _)
  have kxc := visit_closure hσ n v x (insert x S) (Finset.mem_insert_self _ _)
    (by simp [hvS]) (by simpa using card_compl_insert_lt (T := ∅) hxS hn)
  have hD : visit σ (n + 1) p v S =
      if y ∈ S ∨ y ∈ ((x, v) :: Dx).map Prod.fst then (x, v) :: Dx
      else (x, v) :: Dx ++ (y, v) :: visit σ n v y
        (insert y (S ∪ (((x, v) :: Dx).map Prod.fst).toFinset)) := by
    rw [visit_succ, hσv, visitList_cons, visitList_cons]
    simp only [visitList_nil, hxS, List.map_nil, List.not_mem_nil, or_false, ↓reduceIte,
      List.nil_append, List.toFinset_nil, Finset.union_empty, hDx]
  have hc : ¬ (y ∈ S ∨ y ∈ ((x, v) :: Dx).map Prod.fst) := by
    intro hc
    rw [hD] at hy
    simp only [hc, ↓reduceIte] at hy
    rcases List.mem_cons.1 hy with h | h
    · exact hxy (Prod.mk.inj h).1.symm
    · rcases kx3 _ h with h' | h'
      · exact hxv h'.symm
      · obtain ⟨e, he, hee⟩ := List.mem_map.1 h'
        exact kx2 e he (by simp [hee, hvS])
  simp only [hc, ↓reduceIte] at hD
  set Sy := insert y (S ∪ (((x, v) :: Dx).map Prod.fst).toFinset) with hSy
  set Dy := visit σ n v y Sy with hDy
  have hySy : y ∈ Sy := Finset.mem_insert_self _ _
  obtain ⟨-, ky2, -, -⟩ := visit_wf σ n v y Sy hySy
  have kyc := visit_closure hσ n v y Sy hySy (by simp [hSy, hvS])
    (card_compl_insert_lt hyS hn)
  simp only [List.map_cons, List.mem_cons, not_or] at hc
  have hDy' : visit σ' n v y (insert y S) = Dy := by
    apply visit_congr
    intro z hz
    have hzv : z ≠ v := by
      rcases hz with rfl | hz
      · exact hyv
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
        intro h; exact ky2 e he (by simp [hSy, h, hvS])
    refine ⟨hv z hzv, fun q w hw => ?_⟩
    have hzw : G.Adj w z := (hσ' _ _ _ hw).symm
    constructor
    · intro h; simp only [hSy, Finset.mem_insert, Finset.mem_union] at h ⊢; tauto
    · intro h
      simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
        List.mem_cons] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have := kxc w (Or.inl h) z hzw
        rcases hz with rfl | hz
        · simp only [Finset.mem_insert] at this; tauto
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
          apply ky2 e he
          simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
            List.mem_cons] at this ⊢
          tauto
      · exfalso
        have := kxc w (Or.inr h) z hzw
        rcases hz with rfl | hz
        · simp only [Finset.mem_insert] at this; tauto
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
          apply ky2 e he
          simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
            List.mem_cons] at this ⊢
          tauto
  have hxDy : x ∉ Dy.map Prod.fst := by
    intro h
    obtain ⟨e, he, hee⟩ := List.mem_map.1 h
    exact ky2 e he (by simp [hSy, hee])
  have hDx' : visit σ' n v x (insert x (S ∪ (y :: Dy.map Prod.fst).toFinset)) = Dx := by
    apply visit_congr
    intro z hz
    have hzv : z ≠ v := by
      rcases hz with rfl | hz
      · exact hxv
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
        intro h; exact kx2 e he (by simp [h, hvS])
    refine ⟨hv z hzv, fun q w hw => ?_⟩
    have hzw : G.Adj z w := hσ' _ _ _ hw
    rcases kxc z hz w hzw with h | h
    · simp only [Finset.mem_insert, Finset.mem_union] at h ⊢; tauto
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      have h1 := kx2 e he
      have h2 : e.1 ∉ Dy.map Prod.fst := by
        intro h'
        obtain ⟨f, hf, hfe⟩ := List.mem_map.1 h'
        apply ky2 f hf
        rw [hSy, hfe]
        simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
          List.mem_cons]
        exact Or.inr (Or.inr (Or.inr h))
      have h3 : e.1 ≠ y := fun h' => hc.2.2 (h' ▸ h)
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
        List.mem_cons] at h1 ⊢
      tauto
  refine ⟨Dx, Dy, hD, ?_, ?_, ?_⟩
  · rw [visit_succ, hσ'v, visitList_cons, visitList_cons]
    simp only [visitList_nil, hyS, List.map_nil, List.not_mem_nil, or_false, ↓reduceIte,
      List.nil_append, List.toFinset_nil, Finset.union_empty, hDy', List.map_cons,
      List.mem_cons, hxS, hxy, hxDy, hDx']
  · intro c hc' a hca
    rcases kxc c (by simpa using hc') a hca with h | h
    · simp only [Finset.mem_insert] at h
      simp only [List.map_cons, List.mem_cons]; tauto
    · simp only [List.map_cons, List.mem_cons]; tauto
  · intro c hc' a hca
    rcases kyc c (by simpa using hc') a hca with h | h
    · simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at h
      simp only [List.map_cons, List.map_append, List.mem_append, List.mem_cons] at h ⊢; tauto
    · simp only [List.map_cons, List.map_append, List.mem_append, List.mem_cons]; tauto

omit [DecidableEq V] [Fintype V] in
theorem not_mem_map_fst_of_nodup {P Q : List (V × V)} {a : V}
    (h : ((P ++ Q).map Prod.fst).Nodup) (ha : a ∈ P.map Prod.fst) : a ∉ Q.map Prod.fst := by
  rw [List.map_append, List.nodup_append] at h
  exact fun hb => h.2.2 a ha a hb rfl

omit [Fintype V] in
theorem mem_of_mem_insert_or {S : Finset V} {L A : List (V × V)} {w u z : V}
    (h : z ∈ insert w (S ∪ (L.map Prod.fst).toFinset) ∨ z ∈ A.map Prod.fst) :
    z ∈ S ∨ z ∈ (L ++ (w, u) :: A).map Prod.fst := by
  simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_append,
    List.map_cons, List.mem_append, List.mem_cons] at h ⊢
  tauto

/-- In a run `F` whose block of `w` contains `v`, every pair of `F` with parent `v` lies in that
block. -/
theorem mem_block_of_mem {σ : V → V → List V} (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p)
    {n : ℕ} {u v : V} {S : Finset V} (hu : u ∈ S) (hn : Sᶜ.card < n + 1) (huv : u ≠ v)
    {F : List (V × V)} (F1 : (F.map Prod.fst).Nodup) (F2 : ∀ e ∈ F, e.1 ∉ S)
    (F4 : F.Pairwise (fun e f => e.2 ≠ f.1)) (Fadj : ∀ e ∈ F, G.Adj e.2 e.1)
    (L M : List (V × V)) (w : V) (hwS : w ∉ S)
    (hFe : F = L ++ (w, u) :: visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) ++ M)
    (hvD : v = w ∨ v ∈ (visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))).map Prod.fst)
    (t : V) (ht : (t, v) ∈ F) :
    (t, v) ∈ visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) := by
  set D := visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) with hD
  have hFe' := hFe
  rw [hFe] at ht
  simp only [List.mem_append, List.mem_cons] at ht
  rcases ht with (ht | ht | ht) | ht
  · exfalso
    rw [hFe, List.append_assoc] at F4
    have := (List.pairwise_append.1 F4).2.2 _ ht
    rcases hvD with hvw | hvD
    · exact this (w, u) (by simp) hvw
    · obtain ⟨e, he, hev⟩ := List.mem_map.1 hvD
      exact this e (by simp [he]) hev.symm
  · exact absurd (Prod.mk.inj ht).2 huv.symm
  · exact ht
  · exfalso
    have hadj : G.Adj v t := Fadj (t, v) (by rw [hFe]; exact List.mem_append_right _ ht)
    have hcl := visit_closure hσ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
      (Finset.mem_insert_self _ _) (by simp [hu]) (card_compl_insert_lt hwS hn) v hvD t hadj
    have htM : t ∈ M.map Prod.fst := List.mem_map.2 ⟨_, ht, rfl⟩
    have hF1 := F1
    rw [hFe] at hF1
    rcases hcl with h | h
    · simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at h
      rcases h with h | h | h
      · exact not_mem_map_fst_of_nodup hF1
              (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto)
              htM
      · exact F2 (t, v) (by rw [hFe]; exact List.mem_append_right _ ht) h
      · exact not_mem_map_fst_of_nodup hF1
              (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto)
              htM
    · exact not_mem_map_fst_of_nodup hF1
            (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto)
            htM

/-- **Pivot decomposition.** Let `σ'` agree with `σ` except at `v`, where it reverses every
candidate list of length two. If a run discovers `x ≠ y` both as children of `v` (with `v` not the
start vertex), then the two runs are `L₁ ++ M₁ ++ M₂ ++ L₂` and `L₁ ++ M₂ ++ M₁ ++ L₂`, where
`M₁, M₂` are the blocks of `x` and `y`, each closed under adjacency once finished. -/
theorem visit_swap_decomposition {σ σ' : V → V → List V}
    (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p) (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w)
    {v x y : V} (hxy : x ≠ y) (hv : ∀ z, z ≠ v → ∀ q, σ' z q = σ z q)
    (hlen : ∀ q, G.Adj q v → (σ v q).length ≤ 2)
    (hrev : ∀ q, G.Adj q v → 2 ≤ (σ v q).length → σ' v q = (σ v q).reverse) :
    ∀ (n : ℕ) (p u : V) (S : Finset V), u ∈ S → p ∈ S → Sᶜ.card < n → u ≠ v →
    (x, v) ∈ visit σ n p u S → (y, v) ∈ visit σ n p u S →
    ∃ L₁ M₁ M₂ L₂ : List (V × V), ∃ a₁ a₂ : V, ((a₁ = x ∧ a₂ = y) ∨ (a₁ = y ∧ a₂ = x)) ∧
      M₁.head? = some (a₁, v) ∧ M₂.head? = some (a₂, v) ∧
      visit σ n p u S = L₁ ++ M₁ ++ M₂ ++ L₂ ∧ visit σ' n p u S = L₁ ++ M₂ ++ M₁ ++ L₂ ∧
      (∀ c ∈ M₁.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁).map Prod.fst) ∧
      (∀ c ∈ M₂.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁ ++ M₂).map Prod.fst)
  | 0, _, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, u, S, hu, hp, hn, huv, hx, hy => by
    obtain ⟨F1, F2, F3, F4⟩ := visit_wf σ (n + 1) p u S hu
    have Fadj := visit_adj hσ' (n + 1) p u S
    rw [visit_succ] at hx hy F1 F2 F3 F4 Fadj ⊢
    rw [visit_succ, hv u huv p]
    set F := visitList (visit σ n) u S (σ u p) [] with hF
    let Dec : List (V × V) → List (V × V) → Prop := fun L L' =>
      ∃ L₁ M₁ M₂ L₂ : List (V × V), ∃ a₁ a₂ : V, ((a₁ = x ∧ a₂ = y) ∨ (a₁ = y ∧ a₂ = x)) ∧
      M₁.head? = some (a₁, v) ∧ M₂.head? = some (a₂, v) ∧
      L = L₁ ++ M₁ ++ M₂ ++ L₂ ∧ L' = L₁ ++ M₂ ++ M₁ ++ L₂ ∧
      (∀ c ∈ M₁.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁).map Prod.fst) ∧
      (∀ c ∈ M₂.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁ ++ M₂).map Prod.fst)
    have inBlock := fun L M w hwS (_ : w ∉ L.map Prod.fst) hFe hvD t ht =>
      mem_block_of_mem hσ hu hn huv F1 F2 F4 Fadj L M w hwS hFe hvD t ht
    have key : ∀ (ws : List V), (∀ w ∈ ws, w ∈ σ u p) → ∀ (L L' : List (V × V)),
        visitList (visit σ n) u S ws L = F →
        ((L' = L ∧ v ∉ L.map Prod.fst) ∨ Dec L L') →
        ((visitList (visit σ' n) u S ws L' = visitList (visit σ n) u S ws L ∧
          v ∉ (visitList (visit σ n) u S ws L).map Prod.fst) ∨
          Dec (visitList (visit σ n) u S ws L) (visitList (visit σ' n) u S ws L')) := by
      intro ws
      induction ws with
      | nil => intro _ L L' _ h; exact h
      | cons w ws ih =>
        intro hws L L' hfin hR
        rw [visitList_cons] at hfin ⊢
        rw [visitList_cons]
        apply ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) _ _ hfin
        obtain ⟨M, hM⟩ := exists_visitList_eq_append (visit σ n) u S ws
          (if w ∈ S ∨ w ∈ L.map Prod.fst then L
            else L ++ (w, u) :: visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)))
        rw [hfin] at hM
        rcases hR with ⟨hLL, hvL⟩ | ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, hL, hL', hc₁, hc₂⟩
        · rw [hLL]
          by_cases hc : w ∈ S ∨ w ∈ L.map Prod.fst
          · simp only [hc, ↓reduceIte]
            exact Or.inl ⟨by simp, hvL⟩
          · simp only [hc, ↓reduceIte] at hM ⊢
            simp only [not_or] at hc
            set Sw := insert w (S ∪ (L.map Prod.fst).toFinset) with hSw
            set D := visit σ n u w Sw with hD
            have hwSw : w ∈ Sw := Finset.mem_insert_self _ _
            have huSw : u ∈ Sw := by simp [hSw, hu]
            obtain ⟨-, kd2, -, -⟩ := visit_wf σ n u w Sw hwSw
            have hFe : F = L ++ (w, u) :: D ++ M := by rw [hM]
            by_cases hvw : v = w
            · -- the block of `v` itself
              have hxD := inBlock L M w hc.1 hc.2 hFe (Or.inl hvw) x hx
              have hyD := inBlock L M w hc.1 hc.2 hFe (Or.inl hvw) y hy
              subst hvw
              cases n with
              | zero => simp at hxD
              | succ m =>
                have huv' : G.Adj u v := hσ' u p v (hws v List.mem_cons_self)
                have hxσ := mem_of_mem_visit σ (m + 1) u v x Sw hwSw hxD
                have hyσ := mem_of_mem_visit σ (m + 1) u v y Sw hwSw hyD
                have hfuel : Swᶜ.card < m + 1 := card_compl_insert_lt hc.1 hn
                have hcl : ∀ (a b : V) (t₁ t₂ : List (V × V)),
                    (∀ c ∈ ((a, v) :: t₁).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ Sw ∨ z ∈ ((a, v) :: t₁).map Prod.fst) →
                    (∀ c ∈ ((b, v) :: t₂).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ Sw ∨ z ∈ ((a, v) :: t₁ ++ (b, v) :: t₂).map Prod.fst) →
                    (∀ c ∈ ((a, v) :: t₁).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ S ∨ z ∈ ((L ++ [(v, u)]) ++ (a, v) :: t₁).map Prod.fst) ∧
                    (∀ c ∈ ((b, v) :: t₂).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ S ∨ z ∈ ((L ++ [(v, u)]) ++ (a, v) :: t₁ ++ (b, v) :: t₂).map
                        Prod.fst) := by
                  intro a b t₁ t₂ h₁ h₂
                  refine ⟨fun c hc z hz => ?_, fun c hc z hz => ?_⟩
                  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
                      mem_of_mem_insert_or (u := u) (h₁ c hc z hz)
                  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
                      mem_of_mem_insert_or (u := u) (h₂ c hc z hz)
                rcases eq_pair_or_eq_pair_of_length_le_two (hlen u huv') hxσ hyσ hxy
                  with h | h
                · have h' : σ' v u = [y, x] := by rw [hrev u huv' (by simp [h]), h]; rfl
                  obtain ⟨t₁, t₂, e₁, e₂, c₁, c₂⟩ :=
                    visit_swap_at hσ hσ' hv hxy hwSw hfuel h h' hxD hyD
                  obtain ⟨d₁, d₂⟩ := hcl x y t₁ t₂ c₁ c₂
                  refine Or.inr ⟨L ++ [(v, u)], (x, v) :: t₁, (y, v) :: t₂, [], x, y,
                    Or.inl ⟨rfl, rfl⟩, rfl, rfl, ?_, ?_, d₁, d₂⟩
                  · rw [hD, e₁]; simp
                  · rw [e₂]; simp
                · have h' : σ' v u = [x, y] := by rw [hrev u huv' (by simp [h]), h]; rfl
                  obtain ⟨t₁, t₂, e₁, e₂, c₁, c₂⟩ :=
                    visit_swap_at hσ hσ' hv hxy.symm hwSw hfuel h h' hyD hxD
                  obtain ⟨d₁, d₂⟩ := hcl y x t₁ t₂ c₁ c₂
                  refine Or.inr ⟨L ++ [(v, u)], (y, v) :: t₁, (x, v) :: t₂, [], y, x,
                    Or.inr ⟨rfl, rfl⟩, rfl, rfl, ?_, ?_, d₁, d₂⟩
                  · rw [hD, e₁]; simp
                  · rw [e₂]; simp
            · by_cases hvD : v ∈ D.map Prod.fst
              · have hxD := inBlock L M w hc.1 hc.2 hFe (Or.inr hvD) x hx
                have hyD := inBlock L M w hc.1 hc.2 hFe (Or.inr hvD) y hy
                obtain ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, e₁, e₂, c₁, c₂⟩ :=
                  visit_swap_decomposition hσ hσ' hxy hv hlen hrev n u w Sw hwSw huSw
                    (card_compl_insert_lt hc.1 hn) (Ne.symm hvw) hxD hyD
                refine Or.inr ⟨L ++ (w, u) :: L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, ?_, ?_, ?_, ?_⟩
                · rw [hD, e₁]; simp
                · rw [e₂]; simp
                · intro c hc z hz
                  simpa only [List.append_assoc, List.cons_append] using
                    mem_of_mem_insert_or (u := u) (c₁ c hc z hz)
                · intro c hc z hz
                  simpa only [List.append_assoc, List.cons_append] using
                    mem_of_mem_insert_or (u := u) (c₂ c hc z hz)
              · have hDD : visit σ' n u w Sw = D := by
                  apply visit_congr
                  intro z hz
                  refine ⟨hv z ?_, fun _ _ _ => Iff.rfl⟩
                  rcases hz with rfl | hz
                  · exact Ne.symm hvw
                  · exact fun h => hvD (h ▸ hz)
                rw [hDD]
                refine Or.inl ⟨rfl, ?_⟩
                simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
                tauto
        · -- the pivot has already happened
          have hvs : ∀ a, a ∈ L'.map Prod.fst ↔ a ∈ L.map Prod.fst := by
            intro a; rw [hL, hL']
            simp only [List.map_append, List.mem_append]; tauto
          have hvL : v ∈ L.map Prod.fst := by
            have ha₁ : (a₁, v) ∈ L := by
              rw [hL]; cases M₁ with
              | nil => simp at hM₁
              | cons m M₁ => simp only [List.head?_cons, Option.some.injEq] at hM₁; simp [hM₁]
            have hFL : ∃ X, F = L ++ X := by
              split_ifs at hM
              · exact ⟨M, hM⟩
              · exact ⟨_, by rw [hM, List.append_assoc]⟩
            obtain ⟨X, hX⟩ := hFL
            rcases F3 (a₁, v) (by rw [hX]; exact List.mem_append_left _ ha₁) with h | h
            · exact absurd h huv.symm
            · rw [hX] at h F4
              simp only [List.map_append, List.mem_append] at h
              rcases h with h | h
              · exact h
              · exfalso
                obtain ⟨e, he, hev⟩ := List.mem_map.1 h
                exact (List.pairwise_append.1 F4).2.2 _ ha₁ e he hev.symm
          have hc' : (w ∈ S ∨ w ∈ L'.map Prod.fst) ↔ (w ∈ S ∨ w ∈ L.map Prod.fst) := by
            rw [hvs]
          by_cases hc : w ∈ S ∨ w ∈ L.map Prod.fst
          · simp only [hc, hc'.2 hc, ↓reduceIte]
            exact Or.inr ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, hL, hL', hc₁, hc₂⟩
          · have hcn : ¬ (w ∈ S ∨ w ∈ L'.map Prod.fst) := fun h => hc (hc'.1 h)
            simp only [hc, hcn, ↓reduceIte]
            simp only [not_or] at hc
            have hSS : insert w (S ∪ (L'.map Prod.fst).toFinset) =
                insert w (S ∪ (L.map Prod.fst).toFinset) := by
              ext a; simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, hvs]
            have hwv : w ≠ v := fun h => hc.2 (h ▸ hvL)
            obtain ⟨-, kd2, -, -⟩ := visit_wf σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
              (Finset.mem_insert_self _ _)
            have hDD : visit σ' n u w (insert w (S ∪ (L'.map Prod.fst).toFinset)) =
                visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) := by
              rw [hSS]
              apply visit_congr
              intro z hz
              refine ⟨hv z ?_, fun _ _ _ => Iff.rfl⟩
              rcases hz with rfl | hz
              · exact hwv
              · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
                intro h; exact kd2 e he (by simp [h, hvL])
            rw [hDD]
            refine Or.inr ⟨L₁, M₁, M₂, L₂ ++ (w, u) ::
              visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)), a₁, a₂, ha, hM₁, hM₂,
              ?_, ?_, hc₁, hc₂⟩
            · rw [hL]; simp
            · rw [hL']; simp
    rcases key (σ u p) (fun _ h => h) [] [] rfl (Or.inl ⟨rfl, by simp⟩) with ⟨-, hvF⟩ | h
    · exfalso
      rcases F3 (x, v) hx with h | h
      · exact huv h.symm
      · exact hvF h
    · exact h

omit [Fintype V] in
theorem visit_eq_nil_of_eq_nil (σ : V → V → List V) {p u : V} (h : σ u p = []) :
    ∀ (n : ℕ) (S : Finset V), visit σ n p u S = []
  | 0, _ => rfl
  | n + 1, S => by rw [visit_succ, h]; rfl

omit [Fintype V] in
/-- Every vertex discovered by a run descends, along discovery pairs, from the start vertex. -/
theorem visit_reflTransGen (σ : V → V → List V) : ∀ (n : ℕ) (p u : V) (S : Finset V),
    ∀ a ∈ (visit σ n p u S).map Prod.fst,
      Relation.ReflTransGen (fun a c => (a, c) ∈ visit σ n p u S) a u
  | 0, _, _, _ => by simp
  | n + 1, p, u, S => by
    rw [visit_succ]
    apply visitList_induction _ u S (fun L => ∀ a ∈ L.map Prod.fst,
      Relation.ReflTransGen (fun a c => (a, c) ∈ L) a u) _ _ _ (by simp)
    intro L w _ hL _ _ a ha
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at ha
    rcases ha with ha | ha | ha
    · exact (Relation.ReflTransGen.mono · _ _ ·) (fun a c h => List.mem_append_left _ h) (hL a ha)
    · rw [ha]; exact Relation.ReflTransGen.single (by simp)
    · exact ((Relation.ReflTransGen.mono · _ _ ·) (fun a c h => by simp [h])
        (visit_reflTransGen σ n u w _ a ha)).tail (by simp)

omit [Fintype V] in
/-- Two leaf targets discovered by a run lie below two different children of one vertex. -/
theorem exists_branch_of_mem_visit {σ : V → V → List V}
    (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w) {B C : V} (hBC : B ≠ C)
    (hB : ∀ q, G.Adj q B → σ B q = []) (hC : ∀ q, G.Adj q C → σ C q = []) :
    ∀ (n : ℕ) (p u : V) (S : Finset V),
    B ∈ (visit σ n p u S).map Prod.fst → C ∈ (visit σ n p u S).map Prod.fst →
    ∃ w x y, x ≠ y ∧ (x, w) ∈ visit σ n p u S ∧ (y, w) ∈ visit σ n p u S ∧
      Relation.ReflTransGen (fun a c => (a, c) ∈ visit σ n p u S) B x ∧
      Relation.ReflTransGen (fun a c => (a, c) ∈ visit σ n p u S) C y
  | 0, _, _, _ => by simp
  | n + 1, p, u, S => by
    rw [visit_succ]
    have hQ := visitList_induction (visit σ n) u S (fun L =>
      (B ∈ L.map Prod.fst → ∃ x, (x, u) ∈ L ∧
        Relation.ReflTransGen (fun a c => (a, c) ∈ L) B x) ∧
      (C ∈ L.map Prod.fst → ∃ y, (y, u) ∈ L ∧
        Relation.ReflTransGen (fun a c => (a, c) ∈ L) C y) ∧
      (B ∈ L.map Prod.fst → C ∈ L.map Prod.fst → ∃ w x y, x ≠ y ∧ (x, w) ∈ L ∧ (y, w) ∈ L ∧
        Relation.ReflTransGen (fun a c => (a, c) ∈ L) B x ∧
        Relation.ReflTransGen (fun a c => (a, c) ∈ L) C y)) (σ u p) ?_ [] (by simp)
    · exact fun hB' hC' => hQ.2.2 hB' hC'
    · intro L w hw ⟨q1, q2, q3⟩ _ hwL
      set D := visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) with hD
      have mL : ∀ a c, (a, c) ∈ L → (a, c) ∈ L ++ (w, u) :: D :=
        fun a c h => List.mem_append_left _ h
      have mD : ∀ a c, (a, c) ∈ D → (a, c) ∈ L ++ (w, u) :: D := fun a c h => by simp [h]
      have hwu : (w, u) ∈ L ++ (w, u) :: D := by simp
      have desc : ∀ a, a = w ∨ a ∈ D.map Prod.fst →
          Relation.ReflTransGen (fun a c => (a, c) ∈ L ++ (w, u) :: D) a w := by
        intro a ha
        rcases ha with ha | ha
        · rw [ha]
        · exact (Relation.ReflTransGen.mono · _ _ ·) mD (visit_reflTransGen σ n u w _ a ha)
      have split : ∀ t, t ∈ (L ++ (w, u) :: D).map Prod.fst ↔
          t ∈ L.map Prod.fst ∨ (t = w ∨ t ∈ D.map Prod.fst) := by
        intro t; simp
      have hadj : G.Adj u w := hσ' u p w hw
      refine ⟨fun hBN => ?_, fun hCN => ?_, fun hBN hCN => ?_⟩
      · rcases (split B).1 hBN with h | h
        · obtain ⟨x, hx, hr⟩ := q1 h
          exact ⟨x, mL _ _ hx, (Relation.ReflTransGen.mono · _ _ ·) mL hr⟩
        · exact ⟨w, hwu, desc B h⟩
      · rcases (split C).1 hCN with h | h
        · obtain ⟨y, hy, hr⟩ := q2 h
          exact ⟨y, mL _ _ hy, (Relation.ReflTransGen.mono · _ _ ·) mL hr⟩
        · exact ⟨w, hwu, desc C h⟩
      · rcases (split B).1 hBN with hb | hb <;> rcases (split C).1 hCN with hc | hc
        · obtain ⟨w', x, y, hxy, hx, hy, rB, rC⟩ := q3 hb hc
          exact ⟨w', x, y, hxy, mL _ _ hx, mL _ _ hy, (Relation.ReflTransGen.mono · _ _ ·) mL rB,
            (Relation.ReflTransGen.mono · _ _ ·) mL rC⟩
        · obtain ⟨x, hx, rB⟩ := q1 hb
          refine ⟨u, x, w, ?_, mL _ _ hx, hwu, (Relation.ReflTransGen.mono · _ _ ·) mL rB,
            desc C hc⟩
          rintro rfl; exact hwL (List.mem_map.2 ⟨_, hx, rfl⟩)
        · obtain ⟨y, hy, rC⟩ := q2 hc
          refine ⟨u, w, y, ?_, hwu, mL _ _ hy, desc B hb,
            (Relation.ReflTransGen.mono · _ _ ·) mL rC⟩
          rintro rfl; exact hwL (List.mem_map.2 ⟨_, hy, rfl⟩)
        · have hb' : B ∈ D.map Prod.fst := by
            rcases hb with hb | hb
            · exfalso
              have hD0 : D = [] := by
                rw [hD]; exact visit_eq_nil_of_eq_nil σ (hb ▸ hB u (hb ▸ hadj)) _ _
              rw [hD0] at hc
              simp only [List.map_nil, List.not_mem_nil, or_false] at hc
              exact hBC (hb.trans hc.symm)
            · exact hb
          have hc' : C ∈ D.map Prod.fst := by
            rcases hc with hc | hc
            · exfalso
              have hD0 : D = [] := by
                rw [hD]; exact visit_eq_nil_of_eq_nil σ (hc ▸ hC u (hc ▸ hadj)) _ _
              rw [hD0] at hb'
              simp at hb'
            · exact hc
          obtain ⟨w', x, y, hxy, hx, hy, rB, rC⟩ :=
            exists_branch_of_mem_visit hσ' hBC hB hC n u w _ hb' hc'
          exact ⟨w', x, y, hxy, mD _ _ hx, mD _ _ hy, (Relation.ReflTransGen.mono · _ _ ·) mD rB,
            (Relation.ReflTransGen.mono · _ _ ·) mD rC⟩

omit [DecidableEq V] [Fintype V] in
/-- In a run split as `L₁ ++ M ++ L₂`, with `M` closed under adjacency relative to everything
before it, every discovery whose parent lies in `M` lies in `M`. -/
theorem mem_block_of_parent_mem {S : Finset V} {L₁ M L₂ : List (V × V)}
    (F1 : ((L₁ ++ M ++ L₂).map Prod.fst).Nodup) (F2 : ∀ e ∈ L₁ ++ M ++ L₂, e.1 ∉ S)
    (F4 : (L₁ ++ M ++ L₂).Pairwise (fun e f => e.2 ≠ f.1))
    (Fadj : ∀ e ∈ L₁ ++ M ++ L₂, G.Adj e.2 e.1)
    (hM : ∀ c ∈ M.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M).map Prod.fst)
    {a c : V} (hac : (a, c) ∈ L₁ ++ M ++ L₂) (hc : c ∈ M.map Prod.fst) :
    a ∈ M.map Prod.fst := by
  rcases List.mem_append.1 hac with h | h
  · rcases List.mem_append.1 h with h | h
    · exfalso
      obtain ⟨f, hf, hfc⟩ := List.mem_map.1 hc
      rw [List.append_assoc] at F4
      exact (List.pairwise_append.1 F4).2.2 _ h f (List.mem_append_left _ hf) hfc.symm
    · exact List.mem_map.2 ⟨_, h, rfl⟩
  · exfalso
    rcases hM c hc a (Fadj _ hac) with h' | h'
    · exact F2 _ hac h'
    · exact not_mem_map_fst_of_nodup F1 h' (List.mem_map.2 ⟨_, h, rfl⟩)

omit [Fintype V] in
theorem idxOf_lt_idxOf_of_mem {l₁ m₁ m₂ l₂ : List V} {b c : V}
    (hnd : (l₁ ++ m₁ ++ m₂ ++ l₂).Nodup) (hb : b ∈ m₁) (hc : c ∈ m₂) :
    (l₁ ++ m₁ ++ m₂ ++ l₂).idxOf b < (l₁ ++ m₁ ++ m₂ ++ l₂).idxOf c := by
  rw [List.append_assoc, List.append_assoc] at hnd ⊢
  have hb1 : b ∉ l₁ := fun h => (List.nodup_append.1 hnd).2.2 b h b (by simp [hb]) rfl
  have hc1 : c ∉ l₁ := fun h => (List.nodup_append.1 hnd).2.2 c h c (by simp [hc]) rfl
  have hc2 : c ∉ m₁ := fun h =>
    (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 c h c (by simp [hc]) rfl
  rw [List.idxOf_append_of_notMem hb1, List.idxOf_append_of_notMem hc1,
    List.idxOf_append_of_mem hb, List.idxOf_append_of_notMem hc2]
  have := List.idxOf_lt_length_of_mem hb
  omega

end DFS

open DFS

section Maze

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The randomised child order: at a vertex of degree three the coin `b` decides whether the
base order `ρ u p` of the other neighbours is reversed. -/
def coinOrder (ρ : V → V → List V) (b : {u // G.degree u = 3} → Bool) (u p : V) : List V :=
  if h : G.degree u = 3 then (if b ⟨u, h⟩ then (ρ u p).reverse else ρ u p) else ρ u p

/-- The discoveries `(child, parent)`, in order, of the complete randomised search from `A`. -/
def coinRun (ρ : V → V → List V) (A : V) (b : {u // G.degree u = 3} → Bool) : List (V × V) :=
  visit (coinOrder G ρ b) (Fintype.card V) A A {A}

/-- Flip the coin at `v` (no change if `v` does not have degree three). -/
def flipCoin (v : V) (b : {u // G.degree u = 3} → Bool) : {u // G.degree u = 3} → Bool :=
  fun s => if s.1 = v then !b s else b s

variable {G}

omit [DecidableEq V] in
@[simp] theorem mem_coinOrder {ρ : V → V → List V} {b : {u // G.degree u = 3} → Bool}
    {u p w : V} : w ∈ coinOrder G ρ b u p ↔ w ∈ ρ u p := by
  unfold coinOrder; split_ifs <;> simp

omit [DecidableEq V] in
@[simp] theorem length_coinOrder {ρ : V → V → List V} {b : {u // G.degree u = 3} → Bool}
    {u p : V} : (coinOrder G ρ b u p).length = (ρ u p).length := by
  unfold coinOrder; split_ifs <;> simp

theorem coinOrder_flipCoin_of_ne {ρ : V → V → List V} {b : {u // G.degree u = 3} → Bool}
    {v z : V} (hz : z ≠ v) (q : V) : coinOrder G ρ (flipCoin G v b) z q = coinOrder G ρ b z q := by
  unfold coinOrder flipCoin; split_ifs <;> simp_all

theorem coinOrder_flipCoin_self {ρ : V → V → List V} {b : {u // G.degree u = 3} → Bool}
    {v : V} (hv : G.degree v = 3) (q : V) :
    coinOrder G ρ (flipCoin G v b) v q = (coinOrder G ρ b v q).reverse := by
  unfold coinOrder flipCoin
  simp only [hv, ↓reduceDIte, ↓reduceIte]
  cases b ⟨v, hv⟩ <;> simp

theorem flipCoin_flipCoin (v : V) (b : {u // G.degree u = 3} → Bool) :
    flipCoin G v (flipCoin G v b) = b := by
  funext s; unfold flipCoin; split_ifs <;> simp

theorem length_eq_degree_sub_one {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) {v q : V}
    (hq : G.Adj q v) : (ρ v q).length = G.degree v - 1 := by
  rw [← List.toFinset_card_of_nodup (hρ v q).1, ← G.card_neighborFinset_eq_degree,
    ← Finset.card_erase_of_mem (s := G.neighborFinset v) (a := q) (by simpa using hq.symm)]
  congr 1
  ext w; simp [(hρ v q).2, and_comm]

theorem eq_nil_of_degree_eq_one {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) {v q : V}
    (hv : G.degree v = 1) (hq : G.Adj q v) : ρ v q = [] := by
  have := length_eq_degree_sub_one hρ hq
  rw [hv] at this
  exact List.eq_nil_of_length_eq_zero this

theorem card_compl_singleton_lt (A : V) : ({A} : Finset V)ᶜ.card < Fintype.card V := by
  rw [Finset.card_compl, Finset.card_singleton]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨A⟩
  omega

/-- **Pivot at a branching vertex.** Flipping the coin at a vertex with two children `x ≠ y` in
the discovery tree exchanges the two child blocks of the discovery list. -/
theorem coinRun_flipCoin {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) {A : V}
    (hA : G.degree A = 1) (hdeg : ∀ u, G.degree u ≤ 3) {b : {u // G.degree u = 3} → Bool}
    {v x y : V} (hxy : x ≠ y) (hx : (x, v) ∈ coinRun G ρ A b) (hy : (y, v) ∈ coinRun G ρ A b) :
    ∃ L₁ M₁ M₂ L₂ : List (V × V), ∃ a₁ a₂ : V, ((a₁ = x ∧ a₂ = y) ∨ (a₁ = y ∧ a₂ = x)) ∧
      M₁.head? = some (a₁, v) ∧ M₂.head? = some (a₂, v) ∧
      coinRun G ρ A b = L₁ ++ M₁ ++ M₂ ++ L₂ ∧
      coinRun G ρ A (flipCoin G v b) = L₁ ++ M₂ ++ M₁ ++ L₂ ∧
      (∀ c ∈ M₁.map Prod.fst, ∀ a, G.Adj c a → a ∈ ({A} : Finset V) ∨
        a ∈ (L₁ ++ M₁).map Prod.fst) ∧
      (∀ c ∈ M₂.map Prod.fst, ∀ a, G.Adj c a → a ∈ ({A} : Finset V) ∨
        a ∈ (L₁ ++ M₁ ++ M₂).map Prod.fst) := by
  have hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ coinOrder G ρ b u p :=
    fun u p w h h' => mem_coinOrder.2 ((hρ u p).2 w |>.2 ⟨h, h'⟩)
  have hσ' : ∀ u p w, w ∈ coinOrder G ρ b u p → G.Adj u w :=
    fun u p w h => ((hρ u p).2 w |>.1 (mem_coinOrder.1 h)).1
  have hvA : A ≠ v := by
    rintro rfl
    have h1 := hσ' _ _ _ (mem_of_mem_visit _ _ _ _ _ _ (Finset.mem_singleton_self A) hx)
    have h2 := hσ' _ _ _ (mem_of_mem_visit _ _ _ _ _ _ (Finset.mem_singleton_self A) hy)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 ((G.card_neighborFinset_eq_degree A).trans hA)
    have hx' : x ∈ G.neighborFinset A := by simpa using h1
    have hy' : y ∈ G.neighborFinset A := by simpa using h2
    rw [ha, Finset.mem_singleton] at hx' hy'
    exact hxy (hx'.trans hy'.symm)
  exact visit_swap_decomposition hσ hσ' hxy (fun z hz q => coinOrder_flipCoin_of_ne hz q)
    (fun q hq => by rw [length_coinOrder, length_eq_degree_sub_one hρ hq]; have := hdeg v; omega)
    (fun q hq h2 => by
      rw [length_coinOrder, length_eq_degree_sub_one hρ hq] at h2
      exact coinOrder_flipCoin_self (by have := hdeg v; omega) q)
    _ A A {A} (Finset.mem_singleton_self A) (Finset.mem_singleton_self A)
    (card_compl_singleton_lt A) hvA hx hy

/-- Every vertex of a connected graph other than the root is discovered. -/
theorem mem_coinRun_of_connected {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) (hconn : G.Connected)
    (A : V) (b : {u // G.degree u = 3} → Bool) (z : V) (hz : z ≠ A) :
    z ∈ (coinRun G ρ A b).map Prod.fst := by
  have hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ coinOrder G ρ b u p :=
    fun u p w h h' => mem_coinOrder.2 ((hρ u p).2 w |>.2 ⟨h, h'⟩)
  have hcl := visit_closure hσ _ A A {A} (Finset.mem_singleton_self A)
    (Finset.mem_singleton_self A) (card_compl_singleton_lt A)
  have key : ∀ a c (w : G.Walk a c), (a = A ∨ a ∈ (coinRun G ρ A b).map Prod.fst) →
      (c = A ∨ c ∈ (coinRun G ρ A b).map Prod.fst) := by
    intro a c w
    induction w with
    | nil => exact id
    | cons h _ ih =>
      intro ha
      apply ih
      rcases hcl _ ha _ h with h' | h'
      · exact Or.inl (Finset.mem_singleton.1 h')
      · exact Or.inr h'
  obtain ⟨w⟩ := hconn.preconnected A z
  rcases key A z w (Or.inl rfl) with h | h
  · exact absurd h hz
  · exact h

/-- Flipping the coins of any set of branching vertices of the discovery tree `T` keeps the
tree. -/
theorem coinRun_toFinset_flip_of_branching {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) {A : V}
    (hA : G.degree A = 1) (hdeg : ∀ u, G.degree u ≤ 3) {T : Finset (V × V)} :
    ∀ D : Finset {u // G.degree u = 3},
    (∀ w ∈ D, ∃ x y, x ≠ y ∧ (x, w.1) ∈ T ∧ (y, w.1) ∈ T) →
    ∀ b, (coinRun G ρ A b).toFinset = T →
      (coinRun G ρ A (fun s => if s ∈ D then !b s else b s)).toFinset = T := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _ b hb; simpa using hb
  | @insert w D hwD ih =>
    intro hD b hb
    have hb' := ih (fun w' hw' => hD w' (Finset.mem_insert_of_mem hw')) b hb
    obtain ⟨x, y, hxy, hx, hy⟩ := hD w (Finset.mem_insert_self _ _)
    rw [← hb', List.mem_toFinset] at hx hy
    obtain ⟨L₁, M₁, M₂, L₂, -, -, -, -, -, e₁, e₂, -, -⟩ := coinRun_flipCoin hρ hA hdeg hxy hx hy
    have heq : (fun s => if s ∈ insert w D then !b s else b s) =
        flipCoin G w.1 (fun s => if s ∈ D then !b s else b s) := by
      funext s; unfold flipCoin
      by_cases hs : s = w
      · subst hs; simp [hwD]
      · have : s.1 ≠ w.1 := fun h => hs (Subtype.ext h)
        simp [hs, this]
    rw [heq, ← hb']
    ext e; simp only [List.mem_toFinset, e₁, e₂, List.mem_append]; tauto

/-- **The pivot involution.** For the randomised search from a leaf `A` of a connected graph of
maximum degree three, with leaf targets `B, C`, there is an involution of the coin space that
keeps the discovery tree and exchanges the discovery orders of `B` and `C`. -/
theorem exists_involutive_coinRun_pivot {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) (hconn : G.Connected)
    {A B C : V} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hA : G.degree A = 1)
    (hB : G.degree B = 1) (hC : G.degree C = 1) (hdeg : ∀ u, G.degree u ≤ 3) :
    ∃ φ : ({u // G.degree u = 3} → Bool) → ({u // G.degree u = 3} → Bool),
      Function.Involutive φ ∧ ∀ b, (coinRun G ρ A (φ b)).toFinset = (coinRun G ρ A b).toFinset ∧
        (((coinRun G ρ A (φ b)).map Prod.fst).idxOf B <
            ((coinRun G ρ A (φ b)).map Prod.fst).idxOf C ↔
          ((coinRun G ρ A b).map Prod.fst).idxOf C < ((coinRun G ρ A b).map Prod.fst).idxOf B) := by
  have : Nonempty V := ⟨A⟩
  let Sep : Finset (V × V) → V → Prop := fun T w => ∃ x y, x ≠ y ∧ (x, w) ∈ T ∧ (y, w) ∈ T ∧
    Relation.ReflTransGen (fun a c => (a, c) ∈ T) B x ∧
    Relation.ReflTransGen (fun a c => (a, c) ∈ T) C y
  let piv : ({u // G.degree u = 3} → Bool) → V :=
    fun b => Classical.epsilon (Sep (coinRun G ρ A b).toFinset)
  have hσ' : ∀ b, ∀ u p w, w ∈ coinOrder G ρ b u p → G.Adj u w :=
    fun b u p w h => ((hρ u p).2 w |>.1 (mem_coinOrder.1 h)).1
  have leaf : ∀ b {t : V}, G.degree t = 1 → ∀ q, G.Adj q t → coinOrder G ρ b t q = [] := by
    intro b t ht q hq
    have := eq_nil_of_degree_eq_one hρ ht hq
    unfold coinOrder; split_ifs <;> simp [this]
  have hsep : ∀ b, Sep (coinRun G ρ A b).toFinset (piv b) := by
    intro b
    apply Classical.epsilon_spec
    obtain ⟨w, x, y, hxy, hx, hy, rB, rC⟩ := exists_branch_of_mem_visit (hσ' b) hBC
      (leaf b hB) (leaf b hC) _ A A {A} (mem_coinRun_of_connected hρ hconn A b B hAB.symm)
      (mem_coinRun_of_connected hρ hconn A b C hAC.symm)
    exact ⟨w, x, y, hxy, by simpa [coinRun] using hx, by simpa [coinRun] using hy,
      by simpa [coinRun] using rB, by simpa [coinRun] using rC⟩
  have main : ∀ b, (coinRun G ρ A (flipCoin G (piv b) b)).toFinset =
      (coinRun G ρ A b).toFinset ∧
      (((coinRun G ρ A (flipCoin G (piv b) b)).map Prod.fst).idxOf B <
          ((coinRun G ρ A (flipCoin G (piv b) b)).map Prod.fst).idxOf C ↔
        ((coinRun G ρ A b).map Prod.fst).idxOf C <
          ((coinRun G ρ A b).map Prod.fst).idxOf B) := by
    intro b
    obtain ⟨x, y, hxy, hx, hy, rB, rC⟩ := hsep b
    simp only [List.mem_toFinset] at hx hy rB rC
    obtain ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, e₁, e₂, c₁, c₂⟩ :=
      coinRun_flipCoin hρ hA hdeg hxy hx hy
    have F := visit_wf (coinOrder G ρ b) (Fintype.card V) A A {A} (Finset.mem_singleton_self A)
    have F1 : ((coinRun G ρ A b).map Prod.fst).Nodup := F.1
    have F2 : ∀ e ∈ coinRun G ρ A b, e.1 ∉ ({A} : Finset V) := F.2.1
    have F4 : (coinRun G ρ A b).Pairwise (fun e f => e.2 ≠ f.1) := F.2.2.2
    have Fadj : ∀ e ∈ coinRun G ρ A b, G.Adj e.2 e.1 := visit_adj (hσ' b) _ A A {A}
    have chain : ∀ (M : List (V × V)), (∀ a c, (a, c) ∈ coinRun G ρ A b →
        c ∈ M.map Prod.fst → a ∈ M.map Prod.fst) → ∀ t z,
        Relation.ReflTransGen (fun a c => (a, c) ∈ coinRun G ρ A b) t z →
        z ∈ M.map Prod.fst → t ∈ M.map Prod.fst := by
      intro M hM t z h hz
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact hz
      | head hac _ ih => exact hM _ _ hac ih
    rw [e₁] at F1 F2 F4 Fadj
    have step₂ : ∀ a c, (a, c) ∈ coinRun G ρ A b → c ∈ M₂.map Prod.fst →
        a ∈ M₂.map Prod.fst := fun a c hac hc =>
      mem_block_of_parent_mem F1 F2 F4 Fadj c₂ (by rwa [e₁] at hac) hc
    have e₃ : L₁ ++ M₁ ++ M₂ ++ L₂ = L₁ ++ M₁ ++ (M₂ ++ L₂) := by simp
    rw [e₃] at F1 F2 F4 Fadj
    have step₁ : ∀ a c, (a, c) ∈ coinRun G ρ A b → c ∈ M₁.map Prod.fst →
        a ∈ M₁.map Prod.fst := fun a c hac hc =>
      mem_block_of_parent_mem F1 F2 F4 Fadj c₁ (by rwa [e₁, e₃] at hac) hc
    have head : ∀ (M : List (V × V)) a q, M.head? = some (a, q) → a ∈ M.map Prod.fst := by
      intro M a q hM
      cases M with
      | nil => simp at hM
      | cons m M => simp only [List.head?_cons, Option.some.injEq] at hM; simp [hM]
    have nd₁ : (L₁.map Prod.fst ++ M₁.map Prod.fst ++ M₂.map Prod.fst ++
        L₂.map Prod.fst).Nodup := by
      simpa [List.append_assoc] using F1
    have nd₂ : (L₁.map Prod.fst ++ M₂.map Prod.fst ++ M₁.map Prod.fst ++
        L₂.map Prod.fst).Nodup := by
      have F' : ((coinRun G ρ A (flipCoin G (piv b) b)).map Prod.fst).Nodup :=
        (visit_wf _ (Fintype.card V) A A {A} (Finset.mem_singleton_self A)).1
      rw [e₂] at F'
      simpa [List.append_assoc] using F'
    refine ⟨?_, ?_⟩
    · ext e; simp only [List.mem_toFinset, e₁, e₂, List.mem_append]; tauto
    · rw [e₁, e₂]
      simp only [List.map_append]
      rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hB₁ := chain M₁ step₁ B _ rB (head M₁ _ _ hM₁)
        have hC₂ := chain M₂ step₂ C _ rC (head M₂ _ _ hM₂)
        have h1 := idxOf_lt_idxOf_of_mem nd₁ hB₁ hC₂
        have h2 := idxOf_lt_idxOf_of_mem nd₂ hC₂ hB₁
        constructor <;> intro h <;> omega
      · have hB₂ := chain M₂ step₂ B _ rB (head M₂ _ _ hM₂)
        have hC₁ := chain M₁ step₁ C _ rC (head M₁ _ _ hM₁)
        have h1 := idxOf_lt_idxOf_of_mem nd₁ hC₁ hB₂
        have h2 := idxOf_lt_idxOf_of_mem nd₂ hB₂ hC₁
        constructor <;> intro _ <;> omega
  refine ⟨fun b => flipCoin G (piv b) b, fun b => ?_, main⟩
  have hpiv : piv (flipCoin G (piv b) b) = piv b := by
    change Classical.epsilon (Sep (coinRun G ρ A (flipCoin G (piv b) b)).toFinset) =
      Classical.epsilon (Sep (coinRun G ρ A b).toFinset)
    rw [(main b).1]
  simp only [hpiv, flipCoin_flipCoin]

/-- **Fair order of two exits.** Exactly half of the coin assignments discover `B` before `C`. -/
theorem two_mul_card_filter_idxOf_lt {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) (hconn : G.Connected)
    {A B C : V} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hA : G.degree A = 1)
    (hB : G.degree B = 1) (hC : G.degree C = 1) (hdeg : ∀ u, G.degree u ≤ 3) :
    2 * (Finset.univ.filter fun b : {u // G.degree u = 3} → Bool =>
      ((coinRun G ρ A b).map Prod.fst).idxOf B < ((coinRun G ρ A b).map Prod.fst).idxOf C).card =
      Fintype.card ({u // G.degree u = 3} → Bool) := by
  obtain ⟨φ, hφ, hφb⟩ := exists_involutive_coinRun_pivot hρ hconn hAB hAC hBC hA hB hC hdeg
  set P : ({u // G.degree u = 3} → Bool) → Prop := fun b =>
    ((coinRun G ρ A b).map Prod.fst).idxOf B < ((coinRun G ρ A b).map Prod.fst).idxOf C
  have hne : ∀ b, ((coinRun G ρ A b).map Prod.fst).idxOf B ≠
      ((coinRun G ρ A b).map Prod.fst).idxOf C := fun b h =>
    hBC ((List.idxOf_inj (mem_coinRun_of_connected hρ hconn A b B hAB.symm)).1 h)
  have h1 : (Finset.univ.filter P).card = (Finset.univ.filter fun b => ¬ P b).card := by
    apply Finset.card_nbij' φ φ
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, P] at hb ⊢
      intro h
      have := (hφb b).2.1 h
      omega
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, P] at hb ⊢
      have := hne b
      exact (hφb b).2.2 (by omega)
    · intro b _; exact hφ b
    · intro b _; exact hφ b
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  rw [← h1] at h2
  change 2 * (Finset.univ.filter P).card = _
  rw [← Finset.card_univ, ← h2]
  omega

/-- The probability that `B` is discovered before `C` is `1/2`. -/
theorem card_filter_idxOf_lt_div {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) (hconn : G.Connected)
    {A B C : V} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hA : G.degree A = 1)
    (hB : G.degree B = 1) (hC : G.degree C = 1) (hdeg : ∀ u, G.degree u ≤ 3) :
    ((Finset.univ.filter fun b : {u // G.degree u = 3} → Bool =>
      ((coinRun G ρ A b).map Prod.fst).idxOf B <
        ((coinRun G ρ A b).map Prod.fst).idxOf C).card : ℚ) /
      Fintype.card ({u // G.degree u = 3} → Bool) = 1 / 2 := by
  have key : ∀ k N : ℕ, 2 * k = N → 0 < N → (k : ℚ) / N = 1 / 2 := by
    intro k N h hN
    subst h
    have hk : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [div_eq_iff (by push_cast; exact mul_ne_zero two_ne_zero hk)]
    push_cast
    ring
  exact key _ _ (two_mul_card_filter_idxOf_lt hρ hconn hAB hAC hBC hA hB hC hdeg)
    Fintype.card_pos

/-- **Conditional fairness.** Given the discovery tree `T`, the coins at any set `W` of its
branching vertices are uniformly distributed: every prescription of their values is met by the
same number of coin assignments with discovery tree `T`. -/
theorem card_filter_coinRun_eq_of_branching {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) {A : V}
    (hA : G.degree A = 1) (hdeg : ∀ u, G.degree u ≤ 3) (T : Finset (V × V))
    (W : Finset {u // G.degree u = 3})
    (hW : ∀ w ∈ W, ∃ x y, x ≠ y ∧ (x, w.1) ∈ T ∧ (y, w.1) ∈ T)
    (a a' : {u // G.degree u = 3} → Bool) :
    (Finset.univ.filter fun b => (coinRun G ρ A b).toFinset = T ∧ ∀ s ∈ W, b s = a s).card =
      (Finset.univ.filter fun b => (coinRun G ρ A b).toFinset = T ∧ ∀ s ∈ W, b s = a' s).card := by
  set D := W.filter fun s => a s ≠ a' s
  have hD : ∀ w ∈ D, ∃ x y, x ≠ y ∧ (x, w.1) ∈ T ∧ (y, w.1) ∈ T :=
    fun w hw => hW w (Finset.mem_filter.1 hw).1
  let g : ({u // G.degree u = 3} → Bool) → ({u // G.degree u = 3} → Bool) :=
    fun b s => if s ∈ D then !b s else b s
  have hg : ∀ b, g (g b) = b := by
    intro b; funext s; simp only [g]; split_ifs <;> simp
  have hmap : ∀ (c c' : {u // G.degree u = 3} → Bool), D = W.filter (fun s => c s ≠ c' s) →
      ∀ b, ((coinRun G ρ A b).toFinset = T ∧ ∀ s ∈ W, b s = c s) →
        ((coinRun G ρ A (g b)).toFinset = T ∧ ∀ s ∈ W, g b s = c' s) := by
    intro c c' hDc b ⟨hb, hbc⟩
    refine ⟨coinRun_toFinset_flip_of_branching hρ hA hdeg D hD b hb, fun s hs => ?_⟩
    simp only [g, hDc, Finset.mem_filter, hs, true_and, hbc s hs]
    cases c s <;> cases c' s <;> simp
  apply Finset.card_nbij' g g
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
    exact hmap a a' rfl b hb
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
    exact hmap a' a (by simp only [D]; congr 1; funext s; exact propext ne_comm) b hb
  · intro b _; exact hg b
  · intro b _; exact hg b

end Maze
end PercLib
