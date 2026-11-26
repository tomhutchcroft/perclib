/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the canonical finite Bernoulli law. Mathematical reference: predictable sharing
in decision trees, N. Gladkov, "Percolation Inequalities and Decision Trees", arXiv:2408.08457
(2024).
A decision tree is encoded, as in `PercLib.Probability.Exploration.Transcript`, by its query
and sharing functions on revealed histories; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.ProductExpectation
public import Mathlib.Probability.Independence.Basic

/-!
# Predictable coordinate swaps

Two independent Bernoulli configurations `X, Y` are read by a decision tree which, before
revealing the pair `(X e, Y e)` of a freshly queried coordinate `e`, decides whether `e` is
shared. Exchanging the two configurations on the unshared coordinates (equivalently, on the
shared ones) preserves the product pair law.

The tree has a common depth `n`; at step `k` it queries `next k h` and shares it when
`share k h`, where `h` is the history of the `k` previously revealed pairs. A coordinate may be
queried again (for instance after the tree has stopped), but it is shared only at its first
query. `answers ω` is the history revealed on `ω = (X, Y)`, and `S ω` the shared set.

## Main results

* `MeasureTheory.Measure.map_eq_self_of_injective_of_singleton`: on a finite discrete space an
  injective map preserving every point mass preserves the measure.
* `prodBernoulli_prod_singleton_swap`: exchanging two configurations on a set of coordinates
  preserves the product point mass.
* `predictableSwap_injective`: the predictable swap is injective.
* `prodBernoulli_prod_map_predictableSwap`: the predictable swap preserves `μ ⊗ μ`.
* `map_predictableSwap_eq_prodBernoulli_prod`: the same for independent configurations on an
  arbitrary probability space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- On a finite space with measurable singletons, an injective self-map that preserves every
point mass preserves the measure. -/
theorem MeasureTheory.Measure.map_eq_self_of_injective_of_singleton {α : Type*}
    [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α] {μ : Measure α} {f : α → α}
    (hf : Function.Injective f) (hμ : ∀ a, μ {f a} = μ {a}) : μ.map f = μ := by
  rw [Measure.ext_iff_singleton]
  intro a
  obtain ⟨b, rfl⟩ := hf.bijective_of_finite.2 a
  have hpre : f ⁻¹' {f b} = {b} := by
    ext c
    simp [hf.eq_iff]
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton _), hpre, hμ]

namespace PercLib.Probability

variable {E : Type*}

/-- Exchanging two configurations on any set `S` of coordinates preserves their product point
mass: at each coordinate the two bits are kept or swapped. -/
theorem prodBernoulli_prod_singleton_swap [Fintype E] (p : E → unitInterval) (S x y : Set E) :
    (prodBernoulli p).prod (prodBernoulli p) {(x ∩ S ∪ y \ S, y ∩ S ∪ x \ S)} =
      (prodBernoulli p).prod (prodBernoulli p) {(x, y)} := by
  classical
  simp only [← Set.singleton_prod_singleton, Measure.prod_prod, prodBernoulli_singleton,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases hS : e ∈ S <;> by_cases hx : e ∈ x <;> by_cases hy : e ∈ y <;>
    simp [hS, hx, hy, mul_comm]

/-- Exchanging the two configurations on the shared coordinates of a predictable sharing tree
is injective: the outputs and the decisions already made recover the next revealed pair. -/
theorem predictableSwap_injective {n : ℕ}
    (next : (k : Fin n) → (Fin k.val → Bool × Bool) → E)
    (share : (k : Fin n) → (Fin k.val → Bool × Bool) → Bool)
    (answers : Set E × Set E → Fin n → Bool × Bool)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e) :
    Function.Injective (fun ω : Set E × Set E =>
      (ω.1 ∩ S ω ∪ ω.2 \ S ω, ω.2 ∩ S ω ∪ ω.1 \ S ω)) := by
  intro ω ω' heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hH, hH'⟩ := heq
  -- membership of a coordinate whose shared status agrees in both inputs
  have hrec : ∀ e, (e ∈ S ω ↔ e ∈ S ω') → (e ∈ ω.1 ↔ e ∈ ω'.1) ∧ (e ∈ ω.2 ↔ e ∈ ω'.2) := by
    intro e hSe
    have h1 := Set.ext_iff.mp hH e
    have h2 := Set.ext_iff.mp hH' e
    by_cases hs : e ∈ S ω
    · have hs' := hSe.mp hs
      simp only [mem_union, mem_inter_iff, mem_sdiff, hs, hs', not_true, and_false,
        or_false, and_true] at h1 h2
      exact ⟨h1, h2⟩
    · have hs' : e ∉ S ω' := fun h => hs (hSe.mpr h)
      simp only [mem_union, mem_inter_iff, mem_sdiff, hs, hs', not_false_eq_true, and_false,
        false_or, and_true] at h1 h2
      exact ⟨h2, h1⟩
  -- shared status of a coordinate at its first query
  have hfirst : ∀ (ν : Set E × Set E) (k : Fin n),
      (∀ j : Fin n, j < k → next j (fun i => answers ν ⟨i.val, i.isLt.trans j.isLt⟩) ≠
        next k (fun i => answers ν ⟨i.val, i.isLt.trans k.isLt⟩)) →
      (next k (fun i => answers ν ⟨i.val, i.isLt.trans k.isLt⟩) ∈ S ν ↔
        share k (fun i => answers ν ⟨i.val, i.isLt.trans k.isLt⟩) = true) := by
    intro ν k hk
    rw [hS]
    constructor
    · rintro ⟨k', hsh, hk'⟩
      rcases lt_trichotomy k' k with hlt | rfl | hgt
      · exact absurd hk' (hk k' hlt)
      · exact hsh
      · exact absurd hk'.symm (hfresh (answers ν) k' hsh k hgt)
    · intro hsh
      exact ⟨k, hsh, rfl⟩
  have hall : ∀ m, ∀ hm : m < n, answers ω ⟨m, hm⟩ = answers ω' ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      set k : Fin n := ⟨m, hm⟩
      have hpre : ∀ j : Fin n, j.val ≤ m →
          (fun i : Fin j.val => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) =
            (fun i : Fin j.val => answers ω' ⟨i.val, i.isLt.trans j.isLt⟩) := by
        intro j hj
        funext i
        exact ih i.val (lt_of_lt_of_le i.isLt hj) _
      have hk := hrun ω k
      have hk' := hrun ω' k
      rw [← hpre k le_rfl] at hk'
      set e := next k (fun i => answers ω ⟨i.val, i.isLt.trans k.isLt⟩) with he
      have hmem : (e ∈ ω.1 ↔ e ∈ ω'.1) ∧ (e ∈ ω.2 ↔ e ∈ ω'.2) := by
        by_cases hA : ∃ j : Fin n, j < k ∧
            next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e
        · obtain ⟨j, hjk, hj⟩ := hA
          have hj' : next j (fun i => answers ω' ⟨i.val, i.isLt.trans j.isLt⟩) = e := by
            rw [← hpre j hjk.le]; exact hj
          have ha := ih j.val hjk j.isLt
          have h1 := hrun ω j
          have h2 := hrun ω' j
          rw [hj] at h1
          rw [hj'] at h2
          rw [← h1.1, ← h1.2, ← h2.1, ← h2.2]
          change answers ω j = answers ω' j at ha
          rw [ha]
          exact ⟨Iff.rfl, Iff.rfl⟩
        · push Not at hA
          apply hrec
          have hA' : ∀ j : Fin n, j < k →
              next j (fun i => answers ω' ⟨i.val, i.isLt.trans j.isLt⟩) ≠
                next k (fun i => answers ω' ⟨i.val, i.isLt.trans k.isLt⟩) := by
            intro j hjk
            rw [← hpre j hjk.le, ← hpre k le_rfl]
            exact hA j hjk
          have h1 := hfirst ω k hA
          have h2 := hfirst ω' k hA'
          rw [← hpre k le_rfl] at h2
          rw [h1, h2]
      apply Prod.ext <;> rw [Bool.eq_iff_iff]
      · rw [hk.1, hk'.1]; exact hmem.1
      · rw [hk.2, hk'.2]; exact hmem.2
  have hans : answers ω = answers ω' := funext fun k => hall k.val k.isLt
  have hSeq : S ω = S ω' := by
    ext e
    rw [hS, hS, hans]
  have hrec' := fun e => hrec e (by rw [hSeq])
  exact Prod.ext (Set.ext fun e => (hrec' e).1) (Set.ext fun e => (hrec' e).2)

/-- Predictable coordinate swaps preserve the product pair law `μ ⊗ μ` of two independent
Bernoulli configurations on a finite coordinate set. -/
theorem prodBernoulli_prod_map_predictableSwap [Fintype E] (p : E → unitInterval) {n : ℕ}
    (next : (k : Fin n) → (Fin k.val → Bool × Bool) → E)
    (share : (k : Fin n) → (Fin k.val → Bool × Bool) → Bool)
    (answers : Set E × Set E → Fin n → Bool × Bool)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e) :
    ((prodBernoulli p).prod (prodBernoulli p)).map
        (fun ω => (ω.1 ∩ S ω ∪ ω.2 \ S ω, ω.2 ∩ S ω ∪ ω.1 \ S ω)) =
      (prodBernoulli p).prod (prodBernoulli p) :=
  Measure.map_eq_self_of_injective_of_singleton
    (predictableSwap_injective next share answers hrun hfresh S hS)
    fun ω => prodBernoulli_prod_singleton_swap p (S ω) ω.1 ω.2

/-- Predictable coordinate swaps of two independent configurations with law `prodBernoulli p`
on an arbitrary probability space have the product pair law. -/
theorem map_predictableSwap_eq_prodBernoulli_prod [Fintype E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (p : E → unitInterval) {X Y : Ω → Set E}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hXlaw : P.map X = prodBernoulli p) (hYlaw : P.map Y = prodBernoulli p) {n : ℕ}
    (next : (k : Fin n) → (Fin k.val → Bool × Bool) → E)
    (share : (k : Fin n) → (Fin k.val → Bool × Bool) → Bool)
    (answers : Set E × Set E → Fin n → Bool × Bool)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e) :
    P.map (fun ω => (X ω ∩ S (X ω, Y ω) ∪ Y ω \ S (X ω, Y ω),
        Y ω ∩ S (X ω, Y ω) ∪ X ω \ S (X ω, Y ω))) =
      (prodBernoulli p).prod (prodBernoulli p) := by
  have hpair : P.map (fun ω => (X ω, Y ω)) = (prodBernoulli p).prod (prodBernoulli p) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hXY,
      hXlaw, hYlaw]
  have hm := prodBernoulli_prod_map_predictableSwap p next share answers hrun hfresh S hS
  rw [← hm, ← hpair, Measure.map_map (measurable_of_countable _) (hX.prodMk hY)]
  rfl

end PercLib.Probability
