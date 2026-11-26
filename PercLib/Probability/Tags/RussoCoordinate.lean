/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for Russo's formula on finite cylinders and for the one-coordinate
structure of Bernoulli laws. Every statement is assembled from lemmas proved in the
imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.RussoCylinder
public import PercLib.Probability.Coordinate

/-!
# Cylinder Russo formula and one-coordinate structure: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `cylinder_russo_formula`
* `prodBernoulli_one_coordinate`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal unitInterval

namespace PercLib.Probability
variable {ι : Type*}

/-- Russo's formula for a finite cylinder event on an arbitrary coordinate type, the
vanishing of the forced difference off the cylinder support, and the identification of the
forced difference of an increasing measurable event with its pivotal probability. -/
@[tag "XU3W"]
theorem cylinder_russo_formula :
    (∀ (F : Finset ι) (B : Set (Set F)) (q : ι → ℝ → ℝ) (dq : ι → ℝ) (t : ℝ),
      (∀ e ∈ F, HasDerivAt (q e) (dq e) t) →
      ∀ (p : ℝ → ι → unitInterval) (s : Set ℝ),
      (∀ e ∈ F, (p t e : ℝ) = q e t) →
      (∀ u ∈ s, ∀ e ∈ F, (p u e : ℝ) = q e u) →
      HasDerivWithinAt
        (fun u => (prodBernoulli (p u)).real {ω | (Subtype.val ⁻¹' ω : Set F) ∈ B})
        (∑ e : F, dq e *
          ((prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' insert (e:ι) ω : Set F) ∈ B} -
           (prodBernoulli (p t)).real {ω | (Subtype.val ⁻¹' (ω \ {(e:ι)}) : Set F) ∈ B}))
        s t) ∧
    (∀ (p : ι → unitInterval) (F : Finset ι) (B : Set (Set F)) {e : ι}, e ∉ F →
      (prodBernoulli p).real {ω | (Subtype.val ⁻¹' insert e ω : Set F) ∈ B} -
        (prodBernoulli p).real {ω | (Subtype.val ⁻¹' (ω \ {e}) : Set F) ∈ B} = 0) ∧
    (∀ (p : ι → unitInterval) {A : Set (Set ι)}, IsUpperSet A → MeasurableSet A → ∀ e : ι,
      (prodBernoulli p).real {ω | insert e ω ∈ A} -
        (prodBernoulli p).real {ω | ω \ {e} ∈ A} =
        (prodBernoulli p).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) :=
  ⟨fun F B q dq t hq p s ht hs => cylinder_difference_hasDerivWithinAt F B q dq t hq p s ht hs,
    fun p F B _ he => cylinder_difference_outside p F B he,
    fun p _ hA hm e => forced_difference_eq_pivotal p hA hm e⟩

/-- One-coordinate structure: forcing `e` open or closed gives the laws with `q e` replaced
by `1` or `0`; the law with `q e` replaced by `t` is the corresponding mixture; every
probability is affine in `t` with slope the forced difference; and for an increasing event
the slope is the pivotal probability. -/
@[tag "AQDI"]
theorem prodBernoulli_one_coordinate [DecidableEq ι] (q : ι → unitInterval) (e : ι) :
    (prodBernoulli q).map (fun ω => insert e ω) = prodBernoulli (update q e 1) ∧
    (prodBernoulli q).map (fun ω => ω \ {e}) = prodBernoulli (update q e 0) ∧
    (∀ t : unitInterval, prodBernoulli (update q e t) =
      (unitInterval.toNNReal t) • prodBernoulli (update q e 1) +
        (unitInterval.toNNReal (σ t)) • prodBernoulli (update q e 0)) ∧
    (∀ A : Set (Set ι), MeasurableSet A → ∀ t : unitInterval,
      (prodBernoulli (update q e t)).real A =
        (prodBernoulli q).real {ω | ω \ {e} ∈ A} +
          (t : ℝ) * ((prodBernoulli q).real {ω | insert e ω ∈ A} -
            (prodBernoulli q).real {ω | ω \ {e} ∈ A})) ∧
    (∀ A : Set (Set ι), MeasurableSet A → IsUpperSet A →
      (prodBernoulli q).real {ω | insert e ω ∈ A} -
          (prodBernoulli q).real {ω | ω \ {e} ∈ A} =
        (prodBernoulli q).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) :=
  ⟨prodBernoulli_map_insert q e, prodBernoulli_map_diff_singleton q e,
    prodBernoulli_update_eq_smul_add_smul q e,
    fun _ hA t => prodBernoulli_update_real_eq q e hA t,
    fun _ hA hup => prodBernoulli_real_insert_sub_diff_eq_pivotal q e hA hup⟩

end PercLib.Probability
