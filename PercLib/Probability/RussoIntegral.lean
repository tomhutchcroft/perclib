/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Integrated and open-pivotal forms of Russo's identity. New consequences of PercLib's Russo.lean
(native NearCritical source c820fea91a7482c1755de0ec94ecb9f59ccfcacc, reused with Tom Hutchcroft's
permission) and mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679's fundamental theorem of calculus.
No new law or pivotal convention is introduced.
-/
module

public import PercLib.Probability.Cylinder
public import PercLib.Probability.Russo
public import PercLib.Probability.Pivotal.Algebra
public import PercLib.Probability.FiniteEnergy.Insertion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrated Russo formula

The integral form of Russo's identity along a profile curve, and the Margulis–Russo form with open
pivotal coordinates.

## Main results

* `prodBernoulli_real_open_pivotal`
* `prodBernoulli_sub_eq_integral_profile`
* `prodBernoulli_hasDerivWithinAt_open_pivotal`
* `prodBernoulli_sub_eq_integral_pivotal`
* `prodBernoulli_sub_eq_integral_segment`
* `prodBernoulli_real_open_pivotal_of_measurableSet` and
  `prodBernoulli_real_closed_pivotal_of_measurableSet`: the pivotal factorisation on an
  arbitrary index type
* `eq_setOf_sdiff_mem_union_open_pivotal`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set

namespace PercLib.Probability
open FiniteProfile
variable {E : Type*} [Fintype E]

open Classical in
/-- Coordinate-independent observables factor against the open-coordinate indicator. -/
theorem expectation_open_coordinate (q : E → ℝ) (e : E) (g : (E → Bool) → ℝ)
    (hg : ∀ ω, g (flip e ω) = g ω) :
    expectation q (fun ω => if ω e then g ω else 0) = q e * expectation q g := by
  have hpoint (ω : E → Bool) :
      (if ω e then g ω else 0) * weight q ω +
        (if flip e ω e then g (flip e ω) else 0) * weight q (flip e ω) =
      q e * (g ω * weight q ω + g (flip e ω) * weight q (flip e ω)) := by
    rw [weight_split q e ω, weight_split q e (flip e ω)]
    simp only [deletedWeight_flip, flip_apply_self, hg]
    cases ω e <;> simp <;> ring
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun ω _ => hpoint ω)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [sum_flip e (fun ω => (if ω e then g ω else 0) * weight q ω),
    sum_flip e (fun ω => g ω * weight q ω)] at h
  unfold expectation
  linarith

omit [Fintype E] in
/-- The open part of a pivotal event is contained in the event. -/
theorem open_pivotal_subset (A : Set (Set E)) (e : E) :
    {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω} ⊆ A := by
  intro ω hω
  simpa only [Set.insert_eq_of_mem hω.2] using hω.1.1

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- Pivotality is independent of the tested coordinate, including p_e = 0 or 1. -/
theorem prodBernoulli_real_open_pivotal (p : E → unitInterval) (A : Set (Set E)) (e : E) :
    (prodBernoulli p).real {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω} =
      (p e : ℝ) * (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  rw [← expectation_event_eq_real, ← expectation_pivotal_eq_real]
  have hg (ω : E → Bool) : (if pivotal A e (flip e ω) then (1 : ℝ) else 0) =
      if pivotal A e ω then 1 else 0 := by
    simp only [pivotal, force_flip]
    split_ifs <;> simp_all
  convert expectation_open_coordinate (fun j => (p j : ℝ)) e
    (fun ω => if pivotal A e ω then (1 : ℝ) else 0) hg using 1
  congr 1
  funext ω
  simp only [eventValue, Set.mem_ofPred_eq, pivotal, toSet_force_true, toSet_force_false]
  by_cases h : ω e = true <;> simp [toSet, h]

open Classical in
/-- The probability along any C¹ real profile curve has the integral Russo formula.
The supplied interval-valued profile only has to agree with the real curve on the
integration interval, including its endpoints. -/
@[tag "VYTC"]
theorem prodBernoulli_sub_eq_integral_profile (q dq : E → ℝ → ℝ)
    (hq : ∀ e t, HasDerivAt (q e) (dq e t) t) (hdq : ∀ e, Continuous (dq e))
    (p : ℝ → E → unitInterval) (a b : ℝ)
    (hp : ∀ t ∈ uIcc a b, ∀ e, (p t e : ℝ) = q e t)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    (prodBernoulli (p b)).real A - (prodBernoulli (p a)).real A =
      ∫ t in a..b, ∑ e, dq e t * (prodBernoulli (p t)).real
        {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  have hcont (g : (E → Bool) → ℝ) :
      Continuous (fun t => expectation (fun e => q e t) g) := by
    unfold expectation weight
    apply continuous_finsetSum
    intro ω _
    apply continuous_const.mul
    apply continuous_finsetProd
    intro e _
    cases ω e
    · exact continuous_const.sub (continuous_iff_continuousAt.mpr fun t => (hq e t).continuousAt)
    · exact continuous_iff_continuousAt.mpr fun t => (hq e t).continuousAt
  have hc : Continuous (fun t => ∑ e, dq e t * expectation (fun j => q j t)
      (fun ω => if pivotal A e ω then (1 : ℝ) else 0)) :=
    continuous_finsetSum _ (fun e _ => (hdq e).mul (hcont _))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun t _ => event_hasDerivAt q (fun e => dq e t) t
      (fun e => hq e t) hA) (hc.intervalIntegrable a b)
  have hev (t : ℝ) (ht : t ∈ uIcc a b) :
      expectation (fun e => q e t) (eventValue A) = (prodBernoulli (p t)).real A := by
    simpa only [hp t ht] using expectation_event_eq_real (p t) A
  rw [hev b (right_mem_uIcc), hev a (left_mem_uIcc)] at hFTC
  rw [← hFTC]
  apply intervalIntegral.integral_congr
  intro t ht
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  simpa only [hp t ht] using expectation_pivotal_eq_real (p t) A e

open Classical in
/-- Expected number of open pivotal coordinates, with inhomogeneous marginals. -/
theorem integral_open_pivotal_count (p : E → unitInterval) (A : Set (Set E)) :
    (∫ ω, (∑ e, if (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω then (1 : ℝ) else 0)
      ∂prodBernoulli p) =
      ∑ e, (p e : ℝ) * (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
    (integral_indicator_one (Set.toFinite
    {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω}).measurableSet).trans
      (prodBernoulli_real_open_pivotal p A e)

open Classical in
/-- In an increasing event, pivotal coordinates are open exactly when the event occurs. -/
theorem pivotal_count_on_event (A : Set (Set E)) (ω : Set E) :
    (if ω ∈ A then ∑ e, if insert e ω ∈ A ∧ ω \ {e} ∉ A then (1 : ℝ) else 0 else 0) =
      ∑ e, if (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω then (1 : ℝ) else 0 := by
  have he (e : E) : ((insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ ω ∈ A) ↔
      ((insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω) := by
    constructor
    · rintro ⟨hp, hω⟩
      refine ⟨hp, ?_⟩
      by_contra he
      have hs : ω \ {e} = ω := by ext x; simp only [Set.mem_sdiff, Set.mem_singleton_iff]; grind
      exact hp.2 (by rwa [hs])
    · rintro ⟨hp, he⟩
      exact ⟨hp, open_pivotal_subset A e ⟨hp, he⟩⟩
  by_cases hω : ω ∈ A
  · simp only [hω, ite_true]
    apply Finset.sum_congr rfl
    intro e _
    have h := he e
    simp only [hω, and_true] at h
    split_ifs <;> simp_all
  · simp only [hω, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro e _
    have h := he e
    simp only [hω, and_false, false_iff] at h
    simp [h]

open Classical in
/-- Homogeneous Margulis–Russo, including p = 1 as a within-domain derivative. -/
theorem prodBernoulli_hasDerivWithinAt_open_pivotal {A : Set (Set E)} (hA : IsUpperSet A)
    (p : unitInterval) (hp : 0 < p) :
    HasDerivWithinAt (fun t => (prodBernoulli
      (fun _ : E => projIcc 0 1 zero_le_one t)).real A)
      ((1 / (p : ℝ)) * ∫ ω,
        (∑ e, if (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω then (1 : ℝ) else 0)
        ∂prodBernoulli (fun _ => p)) (Icc 0 1) p := by
  have hc : projIcc 0 1 zero_le_one (p : ℝ) = p := by simp
  have h := event_homogeneous_real_hasDerivWithinAt (E := E) (p : ℝ)
    (fun t _ => projIcc 0 1 zero_le_one t) (Icc 0 1)
    (fun _ => by simp) (fun t ht _ => by rw [projIcc_of_mem zero_le_one ht]) hA
  simp only [hc] at h
  convert h using 1
  rw [integral_open_pivotal_count, ← Finset.mul_sum]
  have hp' : (p : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hp)
  field_simp

open Classical in
/-- Expected total pivotal count restricted to the event gives the same derivative. -/
theorem prodBernoulli_hasDerivWithinAt_pivotal_on_event {A : Set (Set E)} (hA : IsUpperSet A)
    (p : unitInterval) (hp : 0 < p) :
    HasDerivWithinAt (fun t => (prodBernoulli
      (fun _ : E => projIcc 0 1 zero_le_one t)).real A)
      ((1 / (p : ℝ)) * ∫ ω,
        (if ω ∈ A then ∑ e, if insert e ω ∈ A ∧ ω \ {e} ∉ A then (1 : ℝ) else 0 else 0)
        ∂prodBernoulli (fun _ => p)) (Icc 0 1) p := by
  simp_rw [pivotal_count_on_event A]
  exact prodBernoulli_hasDerivWithinAt_open_pivotal hA p hp

/-- Homogeneous integral Russo formula with an explicit clamped real parameter. -/
theorem prodBernoulli_sub_eq_integral_pivotal {A : Set (Set E)} (hA : IsUpperSet A)
    (p₁ p₂ : unitInterval) :
    (prodBernoulli fun _ : E => p₂).real A - (prodBernoulli fun _ : E => p₁).real A =
      ∫ t in (p₁ : ℝ)..p₂, ∑ e,
        (prodBernoulli fun _ : E => projIcc 0 1 zero_le_one t).real
          {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  have h := prodBernoulli_sub_eq_integral_profile (E := E) (fun _ t => t) (fun _ _ => 1)
    (fun _ t => hasDerivAt_id t) (fun _ => continuous_const)
    (fun t _ => projIcc 0 1 zero_le_one t) p₁ p₂ (fun t ht _ => ?_) hA
  · simpa using h
  · rw [projIcc_of_mem zero_le_one]
    exact ⟨le_trans (le_min p₁.property.1 p₂.property.1) ht.1,
      le_trans ht.2 (max_le p₁.property.2 p₂.property.2)⟩

/-- Along a segment of profiles, integrate the coordinate slopes times pivotal probabilities.
The identity also holds for unordered profiles; ordered profiles make every slope nonnegative. -/
theorem prodBernoulli_sub_eq_integral_segment (p₁ p₂ : E → unitInterval)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    (prodBernoulli p₂).real A - (prodBernoulli p₁).real A =
      ∫ t in (0 : ℝ)..1, ∑ e, ((p₂ e : ℝ) - p₁ e) *
        (prodBernoulli fun j => projIcc 0 1 zero_le_one
          ((1 - t) * (p₁ j : ℝ) + t * (p₂ j : ℝ))).real
            {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  have h := prodBernoulli_sub_eq_integral_profile (E := E)
    (fun e t => (1 - t) * (p₁ e : ℝ) + t * (p₂ e : ℝ))
    (fun e _ => (p₂ e : ℝ) - p₁ e)
    (fun e t => ?_) (fun _ => continuous_const)
    (fun t j => projIcc 0 1 zero_le_one ((1 - t) * (p₁ j : ℝ) + t * (p₂ j : ℝ)))
    0 1 (fun t ht e => ?_) hA
  · simpa using h
  · convert (((hasDerivAt_id t).const_sub 1).mul_const (p₁ e : ℝ)).add
      ((hasDerivAt_id t).mul_const (p₂ e : ℝ)) using 1
    · funext u; simp
    · ring
  · rw [projIcc_of_mem zero_le_one]
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have h₁ := (p₁ e).property
    have h₂ := (p₂ e).property
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht'.2) h₁.1) (mul_nonneg ht'.1 h₂.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht'.2) (sub_nonneg.mpr h₁.2),
        mul_nonneg ht'.1 (sub_nonneg.mpr h₂.2)]

-- Degenerate parameter intervals give zero on both sides, without excluding endpoints.
example {A : Set (Set E)} (hA : IsUpperSet A) (p : unitInterval) :
    (prodBernoulli fun _ : E => p).real A - (prodBernoulli fun _ : E => p).real A =
      ∫ t in (p : ℝ)..p, ∑ e,
        (prodBernoulli fun _ : E => projIcc 0 1 zero_le_one t).real
          {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} :=
  prodBernoulli_sub_eq_integral_pivotal hA p p

-- Empty and full events have no pivotal coordinates.
example (p : E → unitInterval) :
    (∑ e, (prodBernoulli p).real {ω | insert e ω ∈ (∅ : Set (Set E)) ∧ ω \ {e} ∉ (∅ : Set (Set E))})
        = 0 := by
  simp
example (p : E → unitInterval) :
    (∑ e, (prodBernoulli p).real {ω | insert e ω ∈ (Set.univ : Set (Set E)) ∧ ω \ {e} ∉ Set.univ})
        = 0 := by
  simp

-- A two-coordinate increasing event has derivative 2p and probability p².
example (p₁ p₂ : unitInterval) :
    (p₂ : ℝ) ^ 2 - (p₁ : ℝ) ^ 2 =
      ∫ t in (p₁ : ℝ)..p₂, 2 * (projIcc 0 1 zero_le_one t : ℝ) := by
  let A : Set (Set (Fin 2)) := {ω | 0 ∈ ω ∧ 1 ∈ ω}
  have hA : IsUpperSet A := fun _ _ h hω => ⟨h hω.1, h hω.2⟩
  have hevent (p : unitInterval) : (prodBernoulli fun _ : Fin 2 => p).real A = (p : ℝ) ^ 2 := by
    have heq : A = {ω : Set (Fin 2) | (↑({0, 1} : Finset (Fin 2)) : Set (Fin 2)) ⊆ ω} := by
      ext ω; simp [A, Set.insert_subset_iff]
    rw [heq, measureReal_def, prodBernoulli_subset]
    simp [pow_two]
  have h0 : {ω : Set (Fin 2) | insert 0 ω ∈ A ∧ ω \ {0} ∉ A} = {ω | 1 ∈ ω} := by
    ext ω; simp [A]
  have h1 : {ω : Set (Fin 2) | insert 1 ω ∈ A ∧ ω \ {1} ∉ A} = {ω | 0 ∈ ω} := by
    ext ω; simp [A]
  have hsum (p : unitInterval) :
      (∑ e : Fin 2, (prodBernoulli fun _ : Fin 2 => p).real
        {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) = 2 * (p : ℝ) := by
    rw [Fin.sum_univ_two, h0, h1]
    simp [measureReal_def, prodBernoulli_setOf_mem, two_mul]
  have h := prodBernoulli_sub_eq_integral_pivotal hA p₁ p₂
  simpa only [hevent, hsum] using h

end PercLib.Probability

/-! ### Pivotal events on an arbitrary index type -/

namespace PercLib.Probability

variable {I : Type*}

/-- The open-pivotal event of a measurable event is measurable, on any index type. -/
theorem measurableSet_setOf_insert_mem_and_sdiff_notMem {A : Set (Set I)}
    (hA : MeasurableSet A) (e : I) :
    MeasurableSet {ω : Set I | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  classical
  simpa only [FiniteProfile.pivotal_decide_iff] using
    FiniteProfile.measurableSet_pivotal_decide hA e

/-- Pivotality of `e` does not depend on the state of `e`. -/
theorem insert_mem_and_sdiff_notMem_iff_of_sdiff_eq (A : Set (Set I)) (e : I)
    {ω ω' : Set I} (h : ω \ {e} = ω' \ {e}) :
    (insert e ω ∈ A ∧ ω \ {e} ∉ A) ↔ (insert e ω' ∈ A ∧ ω' \ {e} ∉ A) := by
  classical
  simpa only [FiniteProfile.pivotal_decide_iff] using
    FiniteProfile.pivotal_decide_of_sdiff_eq A e h

/-- **Open pivotal factorisation on any index type.** The open part of the pivotal event of a
measurable event has probability `p e` times that of the pivotal event; no countability of the
index type is needed. -/
theorem prodBernoulli_real_open_pivotal_of_measurableSet (p : I → unitInterval)
    {A : Set (Set I)} (hA : MeasurableSet A) (e : I) :
    (prodBernoulli p).real {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω} =
      (p e : ℝ) * (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  classical
  have h := prodBernoulli_inter_pattern p {e} {e} (Finset.Subset.refl _) _
    (measurableSet_setOf_insert_mem_and_sdiff_notMem hA e)
    (fun ω ω' h => insert_mem_and_sdiff_notMem_iff_of_sdiff_eq A e (by simpa using h))
  have heq : {ω : Set I | ω ∩ (({e} : Finset I) : Set I) = (({e} : Finset I) : Set I)} =
      {ω | e ∈ ω} := by
    ext ω; simp [Set.inter_eq_right]
  rw [heq] at h
  simp only [Finset.sdiff_self, Finset.prod_empty, mul_one, Finset.prod_singleton] at h
  rw [measureReal_def, show {ω : Set I | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω} =
    {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} ∩ {ω | e ∈ ω} from rfl, h, ENNReal.toReal_mul,
    mul_comm, measureReal_def]
  rfl

/-- **Closed pivotal factorisation on any index type.** The closed part of the pivotal event of a
measurable event has probability `1 - p e` times that of the pivotal event. -/
theorem prodBernoulli_real_closed_pivotal_of_measurableSet (p : I → unitInterval)
    {A : Set (Set I)} (hA : MeasurableSet A) (e : I) :
    (prodBernoulli p).real {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∉ ω} =
      (1 - (p e : ℝ)) * (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  classical
  have h := prodBernoulli_inter_pattern p {e} ∅ (Finset.empty_subset _) _
    (measurableSet_setOf_insert_mem_and_sdiff_notMem hA e)
    (fun ω ω' h => insert_mem_and_sdiff_notMem_iff_of_sdiff_eq A e (by simpa using h))
  have heq : {ω : Set I | ω ∩ (({e} : Finset I) : Set I) = ((∅ : Finset I) : Set I)} =
      {ω | e ∉ ω} := by
    ext ω; simp [Set.inter_singleton_eq_empty]
  rw [heq] at h
  simp only [Finset.sdiff_empty, Finset.prod_empty, mul_one, Finset.prod_singleton] at h
  rw [measureReal_def, show {ω : Set I | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∉ ω} =
    {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} ∩ {ω | e ∉ ω} from rfl, h, ENNReal.toReal_mul,
    mul_comm, measureReal_def]
  congr 1

/-- **Pivotal decomposition.** An increasing event splits into the configurations that stay
in it after closing `e`, and the open pivotal configurations. -/
theorem eq_setOf_sdiff_mem_union_open_pivotal {A : Set (Set I)} (hA : IsUpperSet A) (e : I) :
    A = {ω | ω \ {e} ∈ A} ∪ {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω} := by
  classical
  rw [union_comm]
  simpa only [FiniteProfile.pivotal_decide_iff] using
    FiniteProfile.event_eq_pivotal_open_union hA e

/-- The two parts of the pivotal decomposition are disjoint, for every event. -/
theorem disjoint_setOf_sdiff_mem_open_pivotal (A : Set (Set I)) (e : I) :
    Disjoint {ω | ω \ {e} ∈ A} {ω | (insert e ω ∈ A ∧ ω \ {e} ∉ A) ∧ e ∈ ω} := by
  classical
  simpa only [FiniteProfile.pivotal_decide_iff] using
    (FiniteProfile.disjoint_pivotal_open_closed A e).symm

end PercLib.Probability
