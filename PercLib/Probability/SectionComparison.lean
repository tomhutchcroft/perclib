/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21: finite sums of probability mass functions and mathlib
product measures. Mathematical reference: N. Gladkov, Percolation inequalities and decision
trees, arXiv:2408.08457v1, Main Lemma 8.1 (with the sign of the replacement step corrected).
No upstream code is copied and no Input is introduced. One definition is added: the inductive
type `SamplingTree` of predictable sampling trees and its output law `SamplingTree.law`.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Comparison of sections bounds every predictable sampling tree

Let `E` be finite and, for every coordinate `e`, let `μ e` and `ν e` be probability mass
functions on a finite alphabet `Ω e`. A predictable sampling tree (`SamplingTree`) assigns the
coordinates one at a time: at every node it chooses an unassigned coordinate and one of the two
laws `μ e`, `ν e` as a function of the values generated so far, and draws a fresh value from it.
Every coordinate is assigned exactly once.

If a set `A` of configurations satisfies the section comparison
`∑ u, μ e u * 1_A(z[e ↦ u]) ≤ ∑ u, ν e u * 1_A(z[e ↦ u])` for every `e` and every `z`, then
the output `Z` of every such tree, also when the tree is chosen by an independent random seed,
satisfies `(⊗ μ)(A) ≤ P(Z ∈ A) ≤ (⊗ ν)(A)`. No order on the alphabets is used.

## Main definitions

* `SamplingTree Ω S`: predictable sampling trees on the unassigned coordinates `S`.
* `SamplingTree.law`: the law of the configuration produced by a tree.

## Main results

* `sum_prod_mul_indicator_eq_sum_mul_update_pure`: conditioning a product sum on one coordinate.
* `sum_prod_update_mul_indicator_le_of_section_le`: a section comparison at `e` integrates
  against every product law of the other coordinates.
* `SamplingTree.measure_pi_le_toMeasure_bind_law`: `(⊗ μ)(A) ≤ P(Z ∈ A)`.
* `SamplingTree.toMeasure_bind_law_le_measure_pi`: `P(Z ∈ A) ≤ (⊗ ν)(A)`.
-/

@[expose] public section

open MeasureTheory Finset Function
open scoped ENNReal

namespace PercLib.Probability

universe u v

variable {E : Type u} [DecidableEq E] {Ω : E → Type v}

/-- A predictable sampling tree on the set `S` of still unassigned coordinates. A `node`
chooses an unassigned coordinate `e`, a law (`false` for the first law, `true` for the second),
and, for every value drawn at `e`, a continuation tree on the remaining coordinates. Since the
continuation is indexed by the drawn value, every choice is a function of the values generated
so far, and every coordinate of `S` is assigned exactly once. -/
inductive SamplingTree (Ω : E → Type v) : Finset E → Type (max u v)
  /-- No coordinate is left unassigned. -/
  | done : SamplingTree Ω ∅
  /-- Draw coordinate `e ∈ S` from the second law if `second`, else from the first law. -/
  | node {S : Finset E} (e : E) (he : e ∈ S) (second : Bool)
      (next : Ω e → SamplingTree Ω (S.erase e)) : SamplingTree Ω S

namespace SamplingTree

/-- The law of the configuration produced by the tree `t` from the configuration `x`, when the
first law at every coordinate is `μ` and the second is `ν`. Coordinates outside `S` keep their
values in `x`; every coordinate of `S` is overwritten by its drawn value. -/
noncomputable def law (μ ν : ∀ e, PMF (Ω e)) :
    {S : Finset E} → SamplingTree Ω S → (∀ e, Ω e) → PMF (∀ e, Ω e)
  | _, done, x => PMF.pure x
  | _, node e _ second next, x =>
      (cond second (ν e) (μ e)).bind fun w => law μ ν (next w) (update x e w)

@[simp]
theorem law_done (μ ν : ∀ e, PMF (Ω e)) (x : ∀ e, Ω e) :
    (done : SamplingTree Ω ∅).law μ ν x = PMF.pure x := by
  simp [law]

@[simp]
theorem law_node (μ ν : ∀ e, PMF (Ω e)) {S : Finset E} (e : E) (he : e ∈ S) (second : Bool)
    (next : Ω e → SamplingTree Ω (S.erase e)) (x : ∀ e, Ω e) :
    (node e he second next).law μ ν x =
      (cond second (ν e) (μ e)).bind fun w => (next w).law μ ν (update x e w) := by
  simp [law]

end SamplingTree

variable [Fintype E] [∀ e, Fintype (Ω e)]

/-- Conditioning on the value at `e`: a product sum is the average over `u ∼ ρ e` of the
product sums with `ρ e` replaced by the point mass at `u`. -/
theorem sum_prod_mul_indicator_eq_sum_mul_update_pure (ρ : ∀ e, PMF (Ω e)) (e : E)
    (A : Set (∀ e, Ω e)) :
    ∑ y, (∏ f, ρ f (y f)) * A.indicator 1 y =
      ∑ w, ρ e w * ∑ y, (∏ f, update ρ e (PMF.pure w) f (y f)) * A.indicator 1 y := by
  classical
  have key : ∀ (w : Ω e) (y : ∀ e, Ω e), ∏ f, update ρ e (PMF.pure w) f (y f) =
      (if y e = w then 1 else 0) * ∏ f ∈ univ.erase e, ρ f (y f) := by
    intro w y
    rw [← mul_prod_erase univ _ (mem_univ e)]
    congr 1
    · simp [PMF.pure_apply]
    · refine prod_congr rfl fun f hf => ?_
      rw [update_of_ne (ne_of_mem_erase hf)]
  have hρ : ∀ y : ∀ e, Ω e, ∏ f, ρ f (y f) = ρ e (y e) * ∏ f ∈ univ.erase e, ρ f (y f) :=
    fun y => (mul_prod_erase univ _ (mem_univ e)).symm
  simp_rw [key, hρ, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  simp_rw [← mul_assoc, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [sum_ite_eq]
  simp

/-- A section comparison at `e` integrates against every product law of the other
coordinates. -/
theorem sum_prod_update_mul_indicator_le_of_section_le (ρ : ∀ e, PMF (Ω e)) (e : E)
    (α β : PMF (Ω e)) (A : Set (∀ e, Ω e))
    (h : ∀ z : ∀ e, Ω e,
      ∑ w, α w * A.indicator 1 (update z e w) ≤ ∑ w, β w * A.indicator 1 (update z e w)) :
    ∑ y, (∏ f, update ρ e α f (y f)) * A.indicator 1 y ≤
      ∑ y, (∏ f, update ρ e β f (y f)) * A.indicator 1 y := by
  classical
  set R : (∀ e, Ω e) → ℝ≥0∞ := fun y => ∏ f ∈ univ.erase e, ρ f (y f) with hR
  have hRu : ∀ (y : ∀ e, Ω e) (w : Ω e), R (update y e w) = R y := fun y w =>
    prod_congr rfl fun f hf => by rw [update_of_ne (ne_of_mem_erase hf)]
  have hsplit : ∀ (κ : PMF (Ω e)) (y : ∀ e, Ω e),
      ∏ f, update ρ e κ f (y f) = κ (y e) * R y := by
    intro κ y
    rw [← mul_prod_erase univ _ (mem_univ e), update_self]
    congr 1
    exact prod_congr rfl fun f hf => by rw [update_of_ne (ne_of_mem_erase hf)]
  -- the involution `(y, w) ↦ (y[e ↦ w], y e)` regroups the sum by the values off `e`
  let σ : Equiv.Perm ((∀ e, Ω e) × Ω e) :=
    Function.Involutive.toPerm (fun p => (update p.1 e p.2, p.1 e)) fun p => by
      simp
  have hsum1 : ∑ w, α w = 1 := by
    have h1 := α.tsum_coe
    rwa [tsum_fintype] at h1
  have regroup : ∀ κ : PMF (Ω e),
      ∑ y, (∏ f, update ρ e κ f (y f)) * A.indicator 1 y =
        ∑ z, α (z e) * (R z * ∑ w, κ w * A.indicator 1 (update z e w)) := by
    intro κ
    calc ∑ y, (∏ f, update ρ e κ f (y f)) * A.indicator 1 y
        = ∑ p : (∀ e, Ω e) × Ω e, α p.2 * (κ (p.1 e) * R p.1 * A.indicator 1 p.1) := by
          rw [Fintype.sum_prod_type]
          refine sum_congr rfl fun y _ => ?_
          dsimp only
          rw [← sum_mul, hsum1, one_mul, hsplit]
      _ = ∑ p : (∀ e, Ω e) × Ω e,
            α (p.1 e) * (κ p.2 * R p.1 * A.indicator 1 (update p.1 e p.2)) := by
          rw [← Equiv.sum_comp σ]
          refine sum_congr rfl fun p _ => ?_
          have hσ : σ p = (update p.1 e p.2, p.1 e) := rfl
          rw [hσ]
          simp [hRu]
      _ = ∑ z, α (z e) * (R z * ∑ w, κ w * A.indicator 1 (update z e w)) := by
          rw [Fintype.sum_prod_type]
          refine sum_congr rfl fun z _ => ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun w _ => ?_
          ring
  rw [regroup α, regroup β]
  exact sum_le_sum fun z _ => by gcongr α (z e) * (R z * ?_); exact h z

namespace SamplingTree

variable (μ ν : ∀ e, PMF (Ω e))

omit [Fintype E] [∀ e, Fintype (Ω e)] in
private theorem update_pure_eq {S : Finset E} {e : E} (he : e ∈ S) (x : ∀ e, Ω e) (w : Ω e) :
    (fun f => if f ∈ S.erase e then μ f else PMF.pure (update x e w f)) =
      update (fun f => if f ∈ S then μ f else PMF.pure (x f)) e (PMF.pure w) := by
  funext f
  by_cases hf : f = e
  · subst hf; simp
  · simp [hf]

omit [Fintype E] [∀ e, Fintype (Ω e)] in
private theorem update_self_eq {S : Finset E} {e : E} (he : e ∈ S) (x : ∀ e, Ω e) :
    update (fun f => if f ∈ S then μ f else PMF.pure (x f)) e (μ e) =
      fun f => if f ∈ S then μ f else PMF.pure (x f) := by
  rw [update_eq_self_iff]; simp [he]

private theorem sum_done_eq (x : ∀ e, Ω e) (A : Set (∀ e, Ω e)) :
    ∑ y, (∏ f, (if f ∈ (∅ : Finset E) then μ f else PMF.pure (x f)) (y f)) * A.indicator 1 y =
      ∑ y, (PMF.pure x) y * A.indicator 1 y := by
  classical
  refine sum_congr rfl fun y _ => ?_
  congr 1
  simp only [notMem_empty, ite_false, PMF.pure_apply, prod_boole, mem_univ, true_imp_iff]
  simp [funext_iff]

private theorem sum_law_node_eq {S : Finset E} (e : E) (he : e ∈ S) (second : Bool)
    (next : Ω e → SamplingTree Ω (S.erase e)) (x : ∀ e, Ω e) (A : Set (∀ e, Ω e)) :
    ∑ y, (node e he second next).law μ ν x y * A.indicator 1 y =
      ∑ w, cond second (ν e) (μ e) w *
        ∑ y, (next w).law μ ν (update x e w) y * A.indicator 1 y := by
  simp only [law_node, PMF.bind_apply, tsum_fintype, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_
  ring

end SamplingTree

/-- One step of the lower bound: if the reference family `ρ` uses the first law at `e`, then
the product sum of `ρ` is at most the average, under either law at `e`, of any upper bounds
for the product sums conditioned on the value at `e`. -/
theorem sum_prod_mul_indicator_le_sum_cond_mul (μ ν : ∀ e, PMF (Ω e)) (ρ : ∀ e, PMF (Ω e))
    (e : E) (A : Set (∀ e, Ω e)) (second : Bool) (hρ : ρ e = μ e)
    (hsec : ∀ z : ∀ e, Ω e,
      ∑ w, μ e w * A.indicator 1 (update z e w) ≤ ∑ w, ν e w * A.indicator 1 (update z e w))
    (L : Ω e → ℝ≥0∞)
    (hL : ∀ w, ∑ y, (∏ f, update ρ e (PMF.pure w) f (y f)) * A.indicator 1 y ≤ L w) :
    ∑ y, (∏ f, ρ f (y f)) * A.indicator 1 y ≤ ∑ w, cond second (ν e) (μ e) w * L w := by
  have hκ : ∑ y, (∏ f, ρ f (y f)) * A.indicator 1 y ≤
      ∑ y, (∏ f, update ρ e (cond second (ν e) (μ e)) f (y f)) * A.indicator 1 y := by
    have hρ' : update ρ e (μ e) = ρ := by rw [← hρ, update_eq_self]
    cases second
    · rw [Bool.cond_false, hρ']
    · rw [Bool.cond_true]
      conv_lhs => rw [← hρ']
      exact sum_prod_update_mul_indicator_le_of_section_le ρ e _ _ A hsec
  refine hκ.trans ?_
  rw [sum_prod_mul_indicator_eq_sum_mul_update_pure _ e]
  simp only [update_self, update_idem]
  exact sum_le_sum fun w _ => by gcongr (cond second (ν e) (μ e)) w * ?_; exact hL w

/-- One step of the upper bound: if the reference family `ρ` uses the second law at `e`, then
the average, under either law at `e`, of any lower bounds for the product sums conditioned on
the value at `e` is at most the product sum of `ρ`. -/
theorem sum_cond_mul_le_sum_prod_mul_indicator (μ ν : ∀ e, PMF (Ω e)) (ρ : ∀ e, PMF (Ω e))
    (e : E) (A : Set (∀ e, Ω e)) (second : Bool) (hρ : ρ e = ν e)
    (hsec : ∀ z : ∀ e, Ω e,
      ∑ w, μ e w * A.indicator 1 (update z e w) ≤ ∑ w, ν e w * A.indicator 1 (update z e w))
    (L : Ω e → ℝ≥0∞)
    (hL : ∀ w, L w ≤ ∑ y, (∏ f, update ρ e (PMF.pure w) f (y f)) * A.indicator 1 y) :
    ∑ w, cond second (ν e) (μ e) w * L w ≤ ∑ y, (∏ f, ρ f (y f)) * A.indicator 1 y := by
  have hκ : ∑ y, (∏ f, update ρ e (cond second (ν e) (μ e)) f (y f)) * A.indicator 1 y ≤
      ∑ y, (∏ f, ρ f (y f)) * A.indicator 1 y := by
    have hρ' : update ρ e (ν e) = ρ := by rw [← hρ, update_eq_self]
    cases second
    · rw [Bool.cond_false]
      conv_rhs => rw [← hρ']
      exact sum_prod_update_mul_indicator_le_of_section_le ρ e _ _ A hsec
    · rw [Bool.cond_true, hρ']
  refine le_trans ?_ hκ
  rw [sum_prod_mul_indicator_eq_sum_mul_update_pure _ e]
  simp only [update_self, update_idem]
  exact sum_le_sum fun w _ => by gcongr (cond second (ν e) (μ e)) w * ?_; exact hL w

namespace SamplingTree

variable (μ ν : ∀ e, PMF (Ω e))

/-- Lower bound at every node: from the configuration `x`, the probability that a tree on the
unassigned coordinates `S` ends in `A` is at least the probability under independent first-law
draws on `S`. -/
theorem sum_prod_mul_indicator_le_law (A : Set (∀ e, Ω e))
    (hsec : ∀ (e : E) (z : ∀ e, Ω e),
      ∑ w, μ e w * A.indicator 1 (update z e w) ≤ ∑ w, ν e w * A.indicator 1 (update z e w))
    {S : Finset E} (t : SamplingTree Ω S) (x : ∀ e, Ω e) :
    ∑ y, (∏ f, (if f ∈ S then μ f else PMF.pure (x f)) (y f)) * A.indicator 1 y ≤
      ∑ y, t.law μ ν x y * A.indicator 1 y := by
  induction t generalizing x with
  | done => rw [law_done, sum_done_eq]
  | @node S e he second next ih =>
    rw [sum_law_node_eq]
    refine sum_prod_mul_indicator_le_sum_cond_mul μ ν _ e A second (by simp [he]) (hsec e) _
      fun w => ?_
    rw [← update_pure_eq μ he]
    exact ih w (update x e w)

/-- Upper bound at every node: from the configuration `x`, the probability that a tree on the
unassigned coordinates `S` ends in `A` is at most the probability under independent
second-law draws on `S`. -/
theorem law_le_sum_prod_mul_indicator (A : Set (∀ e, Ω e))
    (hsec : ∀ (e : E) (z : ∀ e, Ω e),
      ∑ w, μ e w * A.indicator 1 (update z e w) ≤ ∑ w, ν e w * A.indicator 1 (update z e w))
    {S : Finset E} (t : SamplingTree Ω S) (x : ∀ e, Ω e) :
    ∑ y, t.law μ ν x y * A.indicator 1 y ≤
      ∑ y, (∏ f, (if f ∈ S then ν f else PMF.pure (x f)) (y f)) * A.indicator 1 y := by
  induction t generalizing x with
  | done => rw [law_done, sum_done_eq]
  | @node S e he second next ih =>
    rw [sum_law_node_eq]
    refine sum_cond_mul_le_sum_prod_mul_indicator μ ν _ e A second (by simp [he]) (hsec e) _
      fun w => ?_
    rw [← update_pure_eq ν he]
    exact ih w (update x e w)

end SamplingTree

section Measure

variable [∀ e, MeasurableSpace (Ω e)] [∀ e, MeasurableSingletonClass (Ω e)]

/-- The product of the measures of a family of probability mass functions, evaluated on a set
of configurations, as a finite sum. -/
theorem measure_pi_toMeasure_apply (ρ : ∀ e, PMF (Ω e)) (A : Set (∀ e, Ω e)) :
    Measure.pi (fun e => (ρ e).toMeasure) A = ∑ y, (∏ f, ρ f (y f)) * A.indicator 1 y := by
  classical
  calc Measure.pi (fun e => (ρ e).toMeasure) A
      = ∑ y ∈ A.toFinset, ∏ f, ρ f (y f) := by
        conv_lhs => rw [← Set.coe_toFinset A]
        rw [← sum_measure_singleton]
        refine sum_congr rfl fun y _ => ?_
        rw [Measure.pi_singleton]
        exact prod_congr rfl fun f _ =>
          PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    _ = _ := by
        simp only [Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
        rw [← sum_filter]
        congr 1
        ext y
        simp

namespace SamplingTree

variable (μ ν : ∀ e, PMF (Ω e))

/-- The law of a tree, evaluated on a set, as a finite sum. -/
theorem law_toMeasure_apply {S : Finset E} (t : SamplingTree Ω S) (x : ∀ e, Ω e)
    (A : Set (∀ e, Ω e)) :
    (t.law μ ν x).toMeasure A = ∑ y, t.law μ ν x y * A.indicator 1 y := by
  rw [PMF.toMeasure_apply_fintype]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ A <;> simp [hy]

/-- Lower bound: if every section of `A` is at least as likely under the first law as under the
second, then the output of a predictable sampling tree, chosen by an independent seed `i ∼ σ`,
lies in `A` with probability at least the product probability `(⊗ μ)(A)`. -/
theorem measure_pi_le_toMeasure_bind_law {ι : Type*} (σ : PMF ι)
    (t : ι → SamplingTree Ω (univ : Finset E)) (x : ∀ e, Ω e) (A : Set (∀ e, Ω e))
    (hsec : ∀ (e : E) (z : ∀ e, Ω e),
      ∑ w, μ e w * A.indicator 1 (update z e w) ≤ ∑ w, ν e w * A.indicator 1 (update z e w)) :
    Measure.pi (fun e => (μ e).toMeasure) A ≤ (σ.bind fun i => (t i).law μ ν x).toMeasure A := by
  rw [PMF.toMeasure_bind_apply _ _ _ A.toFinite.measurableSet]
  calc Measure.pi (fun e => (μ e).toMeasure) A
      = ∑' i, σ i * Measure.pi (fun e => (μ e).toMeasure) A := by
        rw [ENNReal.tsum_mul_right, σ.tsum_coe, one_mul]
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        gcongr σ i * ?_
        rw [law_toMeasure_apply, measure_pi_toMeasure_apply]
        simpa using sum_prod_mul_indicator_le_law μ ν A hsec (t i) x

/-- Upper bound: if every section of `A` is at least as likely under the first law as under the
second, then the output of a predictable sampling tree, chosen by an independent seed `i ∼ σ`,
lies in `A` with probability at most the product probability `(⊗ ν)(A)`. -/
theorem toMeasure_bind_law_le_measure_pi {ι : Type*} (σ : PMF ι)
    (t : ι → SamplingTree Ω (univ : Finset E)) (x : ∀ e, Ω e) (A : Set (∀ e, Ω e))
    (hsec : ∀ (e : E) (z : ∀ e, Ω e),
      ∑ w, μ e w * A.indicator 1 (update z e w) ≤ ∑ w, ν e w * A.indicator 1 (update z e w)) :
    (σ.bind fun i => (t i).law μ ν x).toMeasure A ≤ Measure.pi (fun e => (ν e).toMeasure) A := by
  rw [PMF.toMeasure_bind_apply _ _ _ A.toFinite.measurableSet]
  calc _ ≤ ∑' i, σ i * Measure.pi (fun e => (ν e).toMeasure) A := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        gcongr σ i * ?_
        rw [law_toMeasure_apply, measure_pi_toMeasure_apply]
        simpa using law_le_sum_prod_mul_indicator μ ν A hsec (t i) x
    _ = Measure.pi (fun e => (ν e).toMeasure) A := by
        rw [ENNReal.tsum_mul_right, σ.tsum_coe, one_mul]

end SamplingTree

end Measure

end PercLib.Probability
