/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. Mathematical reference: the
Dirichlet-energy argument for killed Green functions on a locally finite graph, as used by
Barlow, Járai, Kumagai and Slade (Section 2.1 of their 2007 manuscript on the incipient
infinite cluster in high dimensions). No upstream proof is copied.
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Dirichlet energy of a killed Green function

Deterministic, walk-free steps of the killed Green function argument on a locally finite
simple graph `G`. A function `u : V → ℝ` vanishing outside a finite set `D` is "killed" at
the boundary of `D`. The (ordered) Dirichlet energy over a finite set `A` is
`∑ x ∈ A, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2`; when `A` contains `D` and all
neighbours of `D` it counts every edge meeting `D` twice.

## Main results

* `SimpleGraph.sum_sum_sq_sub_eq_two_mul_of_support` (**summation by parts**). For `u`
  vanishing off `D`, the ordered energy over `A` equals
  `2 * ∑ x ∈ D, u x * ∑ y ∼ x, (u x - u y)`.
* `SimpleGraph.sum_sum_sq_sub_eq_two_mul_of_dirichlet` (**energy identity**). If moreover
  `u` solves the unit-source Dirichlet system `∑ y ∼ x, (u x - u y) = 𝟙[x = o]` on `D`,
  the energy equals `2 * u o`, i.e. `ℰ(u) = u o` with each edge counted once.
* `SimpleGraph.Walk.sq_sub_le_length_mul_sum` (**Cauchy–Schwarz along a walk**).
* `SimpleGraph.Walk.IsPath.two_mul_sum_sq_sub_le` (a path's increments are part of the
  energy).
* `SimpleGraph.half_le_of_dirichlet` (**near-root lower bound**). For a Dirichlet
  solution, `u y ≥ u o / 2` whenever `y` is joined to `o` by a path in `A` of length at
  most `u o / 4`.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- Summation by parts for a function vanishing off a finite set `D`: the ordered Dirichlet
energy over any finite `A ⊇ D` containing all neighbours of `D` is twice the pairing of `u`
with its graph Laplacian on `D`. -/
theorem sum_sum_sq_sub_eq_two_mul_of_support (u : V → ℝ) {D A : Finset V}
    (hu : ∀ x ∉ D, u x = 0) (hDA : D ⊆ A) (hN : ∀ x ∈ D, ∀ y, G.Adj x y → y ∈ A) :
    ∑ x ∈ A, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 =
      2 * ∑ x ∈ D, u x * ∑ y ∈ G.neighborFinset x, (u x - u y) := by
  have key : ∀ x y, (u x - u y) ^ 2 = u x * (u x - u y) + u y * (u y - u x) := by
    intro x y; ring
  simp_rw [key, Finset.sum_add_distrib]
  have h1 : ∑ x ∈ A, ∑ y ∈ G.neighborFinset x, u x * (u x - u y) =
      ∑ x ∈ D, u x * ∑ y ∈ G.neighborFinset x, (u x - u y) := by
    rw [← Finset.sum_subset hDA (fun x _ hx => by simp [hu x hx])]
    simp_rw [Finset.mul_sum]
  have h2 : ∑ x ∈ A, ∑ y ∈ G.neighborFinset x, u y * (u y - u x) =
      ∑ y ∈ D, ∑ x ∈ G.neighborFinset y, u y * (u y - u x) := by
    have hf : ∀ x ∈ A, ∑ y ∈ G.neighborFinset x, u y * (u y - u x) =
        ∑ y ∈ (G.neighborFinset x).filter (· ∈ D), u y * (u y - u x) := by
      intro x _
      refine (Finset.sum_filter_of_ne fun y _ hy => ?_).symm
      by_contra h
      simp [hu y h] at hy
    rw [Finset.sum_congr rfl hf]
    refine Finset.sum_comm' fun x y => ?_
    simp only [Finset.mem_filter, mem_neighborFinset]
    constructor
    · rintro ⟨_, hxy, hy⟩
      exact ⟨hxy.symm, hy⟩
    · rintro ⟨hyx, hy⟩
      exact ⟨hN y hy x hyx, hyx.symm, hy⟩
  rw [h1, h2, two_mul]
  congr 1
  simp_rw [Finset.mul_sum]

/-- Energy identity for the unit-source Dirichlet problem: if `u` vanishes off `D`, `o ∈ D`
and `∑ y ∼ x, (u x - u y) = 𝟙[x = o]` for `x ∈ D`, then the ordered energy over `A` is
`2 * u o` (so the energy counting each edge once is `u o`). -/
theorem sum_sum_sq_sub_eq_two_mul_of_dirichlet (u : V → ℝ) {D A : Finset V} {o : V}
    (hu : ∀ x ∉ D, u x = 0) (hDA : D ⊆ A) (hN : ∀ x ∈ D, ∀ y, G.Adj x y → y ∈ A)
    (ho : o ∈ D)
    (hdir : ∀ x ∈ D, ∑ y ∈ G.neighborFinset x, (u x - u y) = if x = o then 1 else 0) :
    ∑ x ∈ A, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 = 2 * u o := by
  rw [G.sum_sum_sq_sub_eq_two_mul_of_support u hu hDA hN,
    Finset.sum_congr rfl fun x hx => by rw [hdir x hx]]
  simp [ho]

variable {G}

omit [DecidableEq V] [G.LocallyFinite] in
/-- Cauchy–Schwarz along a walk: the squared difference of `u` between the endpoints is at
most the length times the sum of the squared increments. -/
theorem Walk.sq_sub_le_length_mul_sum (u : V → ℝ) {a b : V} (p : G.Walk a b) :
    (u a - u b) ^ 2 ≤
      p.length * ∑ i ∈ range p.length, (u (p.getVert i) - u (p.getVert (i + 1))) ^ 2 := by
  have h : u a - u b = ∑ i ∈ range p.length, (u (p.getVert i) - u (p.getVert (i + 1))) := by
    rw [Finset.sum_range_sub' (fun i => u (p.getVert i))]
    simp [Walk.getVert_zero, Walk.getVert_length]
  rw [h]
  simpa using sq_sum_le_card_mul_sum_sq (s := range p.length)
    (f := fun i => u (p.getVert i) - u (p.getVert (i + 1)))

/-- The squared increments of `u` along a path inside `A`, counted in both directions, are
part of the ordered energy over `A`. -/
theorem Walk.IsPath.two_mul_sum_sq_sub_le (u : V → ℝ) {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {A : Finset V} (hA : ∀ i ≤ p.length, p.getVert i ∈ A) :
    2 * ∑ i ∈ range p.length, (u (p.getVert i) - u (p.getVert (i + 1))) ^ 2 ≤
      ∑ x ∈ A, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 := by
  set n := p.length
  let fwd : ℕ → (_ : V) × V := fun i => ⟨p.getVert i, p.getVert (i + 1)⟩
  let bwd : ℕ → (_ : V) × V := fun i => ⟨p.getVert (i + 1), p.getVert i⟩
  let f : (_ : V) × V → ℝ := fun q => (u q.1 - u q.2) ^ 2
  have hinj : ∀ {i j}, i ≤ n → j ≤ n → p.getVert i = p.getVert j → i = j :=
    fun hi hj h => hp.getVert_injOn (Set.mem_ofPred.2 hi) (Set.mem_ofPred.2 hj) h
  have hfwd : Set.InjOn fwd (range n) := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact hinj hi.le hj.le (Sigma.mk.inj_iff.1 h).1
  have hbwd : Set.InjOn bwd (range n) := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := hinj (by omega) (by omega) (Sigma.mk.inj_iff.1 h).1
    omega
  have hdisj : Disjoint ((range n).image fwd) ((range n).image bwd) := by
    rw [Finset.disjoint_left]
    rintro q hq hq'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨j, hj, h⟩ := Finset.mem_image.1 hq'
    rw [mem_range] at hi hj
    have h' := Sigma.mk.inj_iff.1 h
    have e1 := hinj (by omega) (by omega) h'.1
    have e2 := hinj (by omega) (by omega) (eq_of_heq h'.2)
    omega
  have hsub : (range n).image fwd ∪ (range n).image bwd ⊆ A.sigma fun x => G.neighborFinset x := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq <;>
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq <;> rw [mem_range] at hi <;>
      simp only [fwd, bwd, Finset.mem_sigma, mem_neighborFinset]
    · exact ⟨hA i hi.le, p.adj_getVert_succ hi⟩
    · exact ⟨hA (i + 1) hi, (p.adj_getVert_succ hi).symm⟩
  calc 2 * ∑ i ∈ range n, (u (p.getVert i) - u (p.getVert (i + 1))) ^ 2
      = ∑ q ∈ (range n).image fwd ∪ (range n).image bwd, f q := by
        rw [Finset.sum_union hdisj, Finset.sum_image hfwd, Finset.sum_image hbwd, two_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by simp only [f, bwd]; ring
    _ ≤ ∑ q ∈ A.sigma fun x => G.neighborFinset x, f q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => sq_nonneg _
    _ = ∑ x ∈ A, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 := Finset.sum_sigma _ _ _

/-- Elementary arithmetic step: if `(R - v) ^ 2 ≤ d * R` with `0 ≤ R` and `4 d ≤ R`, then
`R / 2 ≤ v`. -/
theorem half_le_of_sq_sub_le_mul {R v d : ℝ} (hR : 0 ≤ R) (h : (R - v) ^ 2 ≤ d * R)
    (hd : 4 * d ≤ R) : R / 2 ≤ v := by
  by_contra hv
  rw [not_le] at hv
  nlinarith

variable (G)

/-- Near-root lower bound for the unit-source Dirichlet solution: if `y` is joined to `o` by
a path inside `A` of length at most `u o / 4`, then `u o / 2 ≤ u y`. -/
theorem half_le_of_dirichlet (u : V → ℝ) {D A : Finset V} {o y : V}
    (hu : ∀ x ∉ D, u x = 0) (hDA : D ⊆ A) (hN : ∀ x ∈ D, ∀ y, G.Adj x y → y ∈ A)
    (ho : o ∈ D)
    (hdir : ∀ x ∈ D, ∑ y ∈ G.neighborFinset x, (u x - u y) = if x = o then 1 else 0)
    (p : G.Walk o y) (hp : p.IsPath) (hA : ∀ i ≤ p.length, p.getVert i ∈ A)
    (hlen : 4 * (p.length : ℝ) ≤ u o) :
    u o / 2 ≤ u y := by
  have hE := G.sum_sum_sq_sub_eq_two_mul_of_dirichlet u hu hDA hN ho hdir
  have hpath := hp.two_mul_sum_sq_sub_le u hA
  have hcs := p.sq_sub_le_length_mul_sum u
  have huo : 0 ≤ u o := le_trans (by positivity) hlen
  refine half_le_of_sq_sub_le_mul huo (le_trans hcs ?_) hlen
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

end SimpleGraph
