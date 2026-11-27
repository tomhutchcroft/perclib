/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers assembled from the existing finite-product, ordered-coupling and Harris
APIs. No upstream proof is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.FiniteContinuity
public import PercLib.Probability.Harris
public import PercLib.Probability.Tags.ProductModel
public import PercLib.Probability.TotalVariation

/-!
# Profile continuity and association: correspondence

Wiki correspondence for finite-profile continuity, the ordered coupling, and Harris-type
association.

## Main results

* `finite_restrictions_and_weighted_expectations`
* `continuous_finite_observations`
* `ordered_product_coupling_and_comparison`
* `ordered_coordinate_association`
* `ordered_product_association`
-/

@[expose] public section
noncomputable section
open MeasureTheory Measure Set
open scoped ENNReal

namespace PercLib.Probability
variable {I : Type*}

private theorem measurable_restrict_block (F : Finset I) :
    Measurable (fun ω : Set I => (Subtype.val ⁻¹' ω : Set F)) := by
  apply Measurable.of_mem
  intro i
  exact (measurableSet_mem i.val).mem

open Classical in
/-- Finite restrictions, configuration weights, integrals and mixed cylinders
under arbitrary profiles and arbitrary ambient coordinate sets. -/
@[tag "ZNMQ"]
theorem finite_restrictions_and_weighted_expectations (q : I → unitInterval) (F : Finset I) :
    Measurable (fun ω : Set I => (Subtype.val ⁻¹' ω : Set F)) ∧
    (prodBernoulli q).map (fun ω => (Subtype.val ⁻¹' ω : Set F)) =
      prodBernoulli (fun i : F => q i) ∧
    (∀ η : Set F, prodBernoulli q {ω | (Subtype.val ⁻¹' ω : Set F) = η} =
      ∏ i : F, if i ∈ η then (unitInterval.toNNReal (q i) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (q i)) : ℝ≥0∞)) ∧
    (∀ f : Set F → ℝ, Integrable (fun ω => f (Subtype.val ⁻¹' ω)) (prodBernoulli q) ∧
      (∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q) =
        ∑ η : Set F, f η * ∏ i : F, if i ∈ η then (q i : ℝ) else 1 - (q i : ℝ)) ∧
    (∀ A : Set (Set F), prodBernoulli q {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A} =
      ∑ η ∈ A.toFinset, ∏ i : F, if i ∈ η then (unitInterval.toNNReal (q i) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (q i)) : ℝ≥0∞)) ∧
    (∀ A B : Finset I, Disjoint A B →
      prodBernoulli q {ω | (↑A : Set I) ⊆ ω ∧ Disjoint (↑B : Set I) ω} =
        (∏ i ∈ A, (unitInterval.toNNReal (q i) : ℝ≥0∞)) *
          ∏ i ∈ B, (unitInterval.toNNReal (unitInterval.symm (q i)) : ℝ≥0∞)) := by
  refine ⟨measurable_restrict_block F, prodBernoulli_map_restrict q F, ?_, ?_,
    prodBernoulli_cylinder_sum q F, prodBernoulli_open_closed q⟩
  · intro η
    simpa using (prodBernoulli_cylinder_apply q F {η}).trans
      (prodBernoulli_singleton (fun i : F => q i) η)
  · intro f
    refine ⟨?_, integral_prodBernoulli_cylinder q F f⟩
    have h : Integrable f ((prodBernoulli q).map
        (fun ω => (Subtype.val ⁻¹' ω : Set F))) := by
      rw [prodBernoulli_map_restrict]
      exact Integrable.of_finite
    exact h.comp_measurable (measurable_restrict_block F)

/-- Finite real expectations, finite cylinder probabilities and finite-domain
bond connections are continuous, including all endpoint profiles. -/
@[tag "RA0Z"]
theorem continuous_finite_observations :
    (∀ (F : Finset I) (f : Set F → ℝ), Continuous (fun q : I → unitInterval =>
      ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q)) ∧
    (∀ (F : Finset I) (A : Set (Set F)), Continuous (fun q : I → unitInterval =>
      prodBernoulli q {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A})) ∧
    (∀ (V : Type*) (Λ : Set V) (_ : Finite Λ) (x y : Λ),
      Continuous (fun q : Sym2 V → unitInterval =>
        PercLib.Percolation.Bond.tau (fun e : Sym2 Λ => q (Sym2.map Subtype.val e)) x y)) := by
  refine ⟨?_, continuous_prodBernoulli_cylinder, ?_⟩
  · intro F f
    simp_rw [integral_prodBernoulli_cylinder]
    apply continuous_finsetSum
    intro η _
    apply Continuous.const_mul
    apply continuous_finsetProd
    intro i _
    split_ifs <;> fun_prop
  · intro V Λ _ x y
    exact PercLib.Percolation.Bond.continuous_tau_finite_domain Λ x y

/-- Ordered profiles admit a coupling with ordered configurations and compare
both increasing events and arbitrary nonnegative measurable observables. -/
@[tag "6B9V"]
theorem ordered_product_coupling_and_comparison [Countable I]
    (p q : I → unitInterval) (hpq : p ≤ q) :
    (∃ γ : Measure (Set I × Set I), IsProbabilityMeasure γ ∧
      γ.map Prod.fst = prodBernoulli p ∧ γ.map Prod.snd = prodBernoulli q ∧
      ∀ᵐ z ∂γ, z.1 ⊆ z.2) ∧
    (∀ A : Set (Set I), MeasurableSet A → IsUpperSet A →
      prodBernoulli p A ≤ prodBernoulli q A) ∧
    (∀ H : Set I → ℝ≥0∞, Measurable H → Monotone H →
      (∫⁻ ω, H ω ∂prodBernoulli p) ≤ ∫⁻ ω, H ω ∂prodBernoulli q) :=
  ⟨exists_prodBernoulli_monotone_coupling p q hpq,
    fun _ => prodBernoulli_mono_event p q hpq,
    fun _ => lintegral_prodBernoulli_mono p q hpq⟩

/-- Chebyshev's inequality on a linearly ordered measurable probability space,
without any compatibility assumption between the order and sigma algebra. -/
@[tag "P52U"]
theorem ordered_coordinate_association {Y : Type*} [MeasurableSpace Y] [LinearOrder Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] {f g : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfm : Monotone f) (hgm : Monotone g)
    {C D : ℝ} (hfb : ∀ y, ‖f y‖ ≤ C) (hgb : ∀ y, ‖g y‖ ≤ D) :
    (∫ y, f y ∂ν) * (∫ y, g y ∂ν) ≤ ∫ y, f y * g y ∂ν :=
  integral_mul_integral_le_integral_mul_of_monotone ν hfm hgm hf hg
    (fun y => (hfb y).trans (le_max_left C D)) (fun y => (hgb y).trans (le_max_right C D))

section Product
variable {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

open Classical in
/-- Finite-coordinate averaging preserves the law and means, contracts bounds
and L1 differences, fixes finite-coordinate functions, and preserves order.
The integrable version includes product and almost-everywhere section integrability. -/
@[tag "WBBE"]
theorem finite_coordinate_averaging (F : Finset I) {f : (Π i, X i) → ℝ}
    (hf : Measurable f) {C : ℝ} (hfb : ∀ x, ‖f x‖ ≤ C) :
    Measurable (fun z : (Π i, X i) × (Π i, X i) => F.piecewise z.1 z.2) ∧
    ((infinitePi μ).prod (infinitePi μ)).map (fun z => F.piecewise z.1 z.2) = infinitePi μ ∧
    Measurable (fun x => ∫ y, f (F.piecewise x y) ∂infinitePi μ) ∧
    DependsOn (fun x => ∫ y, f (F.piecewise x y) ∂infinitePi μ) (F : Set I) ∧
    (∫ x, ∫ y, f (F.piecewise x y) ∂infinitePi μ ∂infinitePi μ) = ∫ x, f x ∂infinitePi μ ∧
    (∀ x, ‖∫ y, f (F.piecewise x y) ∂infinitePi μ‖ ≤ C) ∧
    (DependsOn f (F : Set I) → ∀ x, (∫ y, f (F.piecewise x y) ∂infinitePi μ) = f x) ∧
    (∀ (g : (Π i, X i) → ℝ) (D : ℝ), Measurable g → (∀ x, ‖g x‖ ≤ D) →
      (∫ x, ‖(∫ y, f (F.piecewise x y) ∂infinitePi μ) -
        ∫ y, g (F.piecewise x y) ∂infinitePi μ‖ ∂infinitePi μ) ≤
          ∫ x, ‖f x - g x‖ ∂infinitePi μ) ∧
    (∀ (_ : ∀ i, Preorder (X i)), Monotone f →
      Monotone (fun x => ∫ y, f (F.piecewise x y) ∂infinitePi μ)) ∧
    (∀ g : (Π i, X i) → ℝ, Measurable g → Integrable g (infinitePi μ) →
      Integrable (fun z : (Π i, X i) × (Π i, X i) => g (F.piecewise z.1 z.2))
        ((infinitePi μ).prod (infinitePi μ)) ∧
      (∀ᵐ x ∂infinitePi μ, Integrable (fun y => g (F.piecewise x y)) (infinitePi μ)) ∧
      (∫ x, ∫ y, g (F.piecewise x y) ∂infinitePi μ ∂infinitePi μ) =
        ∫ x, g x ∂infinitePi μ) := by
  have hfi : Integrable f (infinitePi μ) :=
    .of_bound hf.aestronglyMeasurable C (ae_of_all _ hfb)
  refine ⟨measurable_finsetPiecewise F, infinitePi_prod_map_piecewise μ F,
    measurable_integral_piecewise μ hf, dependsOn_integral_piecewise μ f,
    integral_integral_piecewise μ hfi, norm_integral_piecewise_le μ hfb,
    integral_piecewise_eq_self μ, ?_, ?_, ?_⟩
  · intro g D hg hgb
    exact integral_norm_integral_piecewise_sub_le μ hf hg
      (fun x => (hfb x).trans (le_max_left C D)) (fun x => (hgb x).trans (le_max_right C D))
  · intro _ hfm
    exact monotone_integral_piecewise μ hfm hf hfb
  · intro g _ hgi
    have hi : Integrable (fun z : (Π i, X i) × (Π i, X i) => g (F.piecewise z.1 z.2))
        ((infinitePi μ).prod (infinitePi μ)) := by
      have h := hgi
      rw [← infinitePi_prod_map_piecewise μ F] at h
      exact h.comp_measurable (measurable_finsetPiecewise F)
    exact ⟨hi, hi.prod_right_ae, integral_integral_piecewise μ hgi⟩

open Classical in
/-- Indicator averages approximate in L1 uniformly over all finite supersets of
a sufficiently large block, with no countability assumption on the index set. -/
@[tag "NPRG"]
theorem finite_coordinate_indicator_approximation {A : Set (Π i, X i)}
    (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ F₀ : Finset I, ∀ F : Finset I, F₀ ⊆ F →
      (∫ x, ‖(∫ y, A.indicator (1 : (Π i, X i) → ℝ) (F.piecewise x y) ∂infinitePi μ) -
        A.indicator 1 x‖ ∂infinitePi μ) < ε := by
  obtain ⟨F₀, h⟩ := exists_integral_norm_integral_piecewise_indicator_sub_le μ hA (half_pos hε)
  exact ⟨F₀, fun F hF => (h F hF).trans_lt (half_lt_self hε)⟩

open Classical in
/-- Product association bundles finite-coordinate real observables and arbitrary
increasing measurable events on products of linearly ordered spaces. -/
@[tag "9U6I"]
theorem ordered_product_association [∀ i, LinearOrder (X i)] :
    (∀ (F : Finset I) (f g : (Π i, X i) → ℝ) (C D : ℝ),
      Monotone f → Monotone g → Measurable f → Measurable g →
      DependsOn f (F : Set I) → DependsOn g (F : Set I) →
      (∀ x, ‖f x‖ ≤ C) → (∀ x, ‖g x‖ ≤ D) →
      (∫ x, f x ∂infinitePi μ) * (∫ x, g x ∂infinitePi μ) ≤
        ∫ x, f x * g x ∂infinitePi μ) ∧
    (∀ A B : Set (Π i, X i), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B →
      (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B)) := by
  refine ⟨?_, fun _ _ => infinitePi_harris μ⟩
  intro F f g C D hfm hgm hf hg hFf hFg hfb hgb
  exact infinitePi_harris_dependsOn μ F hfm hgm hf hg hFf hFg
    (fun x => (hfb x).trans (le_max_left C D)) (fun x => (hgb x).trans (le_max_right C D))

end Product
end PercLib.Probability

namespace PercLib.Probability

open Classical in
/-- An empty observation is constant even on an uncountable coordinate space. -/
example (q : ℝ → unitInterval) (f : Set (∅ : Finset ℝ) → ℝ) :
    (∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q) = f ∅ := by
  rw [(finite_restrictions_and_weighted_expectations q ∅).2.2.2.1 f |>.2]
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Finset.sum_singleton]
  exact congrArg f (Subsingleton.elim _ _)

/-- Finite real expectations are continuous at the two extreme profiles. -/
example (F : Finset ℝ) (f : Set F → ℝ) :
    ContinuousAt (fun q : ℝ → unitInterval => ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q)
      (fun _ => 0) ∧
    ContinuousAt (fun q : ℝ → unitInterval => ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q)
      (fun _ => 1) :=
  ⟨(continuous_finite_observations.{0, 0}.1 F f).continuousAt,
    (continuous_finite_observations.{0, 0}.1 F f).continuousAt⟩

/-- The ordered comparison includes an everywhere-infinite observable. -/
example : (∫⁻ _ : Set ℕ, (∞ : ℝ≥0∞) ∂prodBernoulli (fun _ => 0)) ≤
    ∫⁻ _ : Set ℕ, (∞ : ℝ≥0∞) ∂prodBernoulli (fun _ => 1) :=
  (ordered_product_coupling_and_comparison (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one)).2.2 (fun _ => ∞) measurable_const monotone_const

/-- The one-coordinate contract has a nonzero bounded witness. -/
example : (∫ _ : ℝ, (1 : ℝ) ∂Measure.dirac 0) * (∫ _ : ℝ, (1 : ℝ) ∂Measure.dirac 0) ≤
    ∫ _ : ℝ, (1 : ℝ) * 1 ∂Measure.dirac 0 :=
  ordered_coordinate_association (Measure.dirac 0) measurable_const measurable_const
    monotone_const monotone_const (C := 1) (D := 1) (by simp) (by simp)

/-- The averaging contract applies to an empty block with uncountably many
coordinates, and fixes the constant one observable pointwise. -/
example (x : ℝ → ℝ) :
    (∫ y, (fun _ : ℝ → ℝ => (1 : ℝ)) ((∅ : Finset ℝ).piecewise x y)
      ∂infinitePi (fun _ : ℝ => Measure.dirac (0 : ℝ))) = 1 := by
  have h := finite_coordinate_averaging (fun _ : ℝ => Measure.dirac (0 : ℝ))
    (∅ : Finset ℝ) (f := fun _ => 1) measurable_const (C := 1) (by simp)
  exact h.2.2.2.2.2.2.1 (by intro a b _; rfl) x

/-- Approximation covers measurable coordinate events on uncountable products. -/
example : ∃ F₀ : Finset ℝ, ∀ F : Finset ℝ, F₀ ⊆ F →
    (∫ x : ℝ → ℝ, ‖(∫ y, ({z : ℝ → ℝ | 0 ≤ z 0}).indicator (1 : (ℝ → ℝ) → ℝ)
      (F.piecewise x y) ∂infinitePi (fun _ : ℝ => Measure.dirac (0 : ℝ))) -
      ({z : ℝ → ℝ | 0 ≤ z 0}).indicator 1 x‖
        ∂infinitePi (fun _ : ℝ => Measure.dirac (0 : ℝ))) < 1 / 2 := by
  apply finite_coordinate_indicator_approximation
  · exact measurableSet_le measurable_const (measurable_pi_apply 0)
  · norm_num

/-- Ordered product association applies to a nontrivial increasing coordinate event. -/
example (μ : ℝ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (infinitePi μ).real {x | 0 ≤ x 0} * (infinitePi μ).real {x | 0 ≤ x 0} ≤
      (infinitePi μ).real {x | 0 ≤ x 0} := by
  have h := (ordered_product_association μ).2 {x | 0 ≤ x 0} {x | 0 ≤ x 0}
    (fun _ _ hxy hx => hx.trans (hxy 0)) (fun _ _ hxy hx => hx.trans (hxy 0))
    (measurableSet_le measurable_const (measurable_pi_apply 0))
    (measurableSet_le measurable_const (measurable_pi_apply 0))
  simpa using h

end PercLib.Probability

namespace PercLib.Probability
open Filter Topology PercLib.Percolation.Bond

/-- Events with arbitrary finite open witness families have measurable,
lower-semicontinuous probability on countable coordinate spaces. Coordinatewise
convergence gives the liminf bound, with connection events as a special case. -/
@[tag "ARYU"]
theorem finite_open_witness_probability_regular {I : Type*} [Countable I] (W : Set (Finset I)) :
    MeasurableSet (⋃ F ∈ W, {ω : Set I | (F : Set I) ⊆ ω}) ∧
    LowerSemicontinuous (fun q : I → unitInterval =>
      prodBernoulli q (⋃ F ∈ W, {ω : Set I | (F : Set I) ⊆ ω})) ∧
    (∀ (q : ℕ → I → unitInterval) (p : I → unitInterval),
      (∀ i, Tendsto (fun n => q n i) atTop (𝓝 (p i))) →
      prodBernoulli p (⋃ F ∈ W, {ω : Set I | (F : Set I) ⊆ ω}) ≤
        liminf (fun n => prodBernoulli (q n) (⋃ F ∈ W, {ω : Set I | (F : Set I) ⊆ ω})) atTop) ∧
    (∀ (V : Type*) (_ : Countable V) (x y : V),
      LowerSemicontinuous (fun q : Sym2 V → unitInterval => tau q x y)) := by
  have hlsc := lowerSemicontinuous_prodBernoulli_iUnion_witness W
  refine ⟨measurableSet_iUnion_witness W, hlsc, ?_, fun _ _ => lowerSemicontinuous_tau⟩
  intro q p hp
  exact (hlsc.le_liminf p).trans ((tendsto_pi_nhds.mpr hp).liminf_le_liminf_comp)

/-- Empty witness families are allowed. -/
example : LowerSemicontinuous (fun q : ℕ → unitInterval =>
    prodBernoulli q (⋃ F ∈ (∅ : Set (Finset ℕ)), {ω : Set ℕ | (F : Set ℕ) ⊆ ω})) :=
  (finite_open_witness_probability_regular.{0, 0} ∅).2.1

/-- A countably infinite family of singleton witnesses gives the nonempty event,
including endpoint profiles. -/
example : LowerSemicontinuous (fun q : ℕ → unitInterval =>
    prodBernoulli q {ω : Set ℕ | ω.Nonempty}) := by
  have heq : (⋃ F ∈ {F : Finset ℕ | ∃ i, F = {i}}, {ω : Set ℕ | (F : Set ℕ) ⊆ ω}) =
      {ω : Set ℕ | ω.Nonempty} := by
    ext ω
    simp [Set.Nonempty]
  simpa only [heq] using
    (finite_open_witness_probability_regular.{0, 0} {F : Finset ℕ | ∃ i, F = {i}}).2.1

end PercLib.Probability

namespace PercLib.Probability

private theorem finite_sum_oscillation_bound {X : Type*} [Fintype X] [Nonempty X]
    (f d : X → ℝ) (a b δ : ℝ) (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b)
    (hd : ∑ x, d x = 0) (hδ : ∀ S : Finset X, ∑ x ∈ S, d x ≤ δ) :
    ∑ x, f x * d x ≤ (b - a) * δ := by
  have hab : a ≤ b := (ha (Classical.arbitrary X)).trans (hb _)
  calc
    ∑ x, f x * d x = ∑ x, (f x - a) * d x := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hd]
      simp
    _ ≤ ∑ x, if 0 ≤ d x then (b - a) * d x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · exact mul_le_mul_of_nonneg_right (sub_le_sub_right (hb x) a) hx
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (ha x)) (le_of_not_ge hx)
    _ = (b - a) * ∑ x ∈ Finset.univ.filter (fun x => 0 ≤ d x), d x := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ ≤ (b - a) * δ := mul_le_mul_of_nonneg_left (hδ _) (sub_nonneg.mpr hab)

private theorem finite_integral_oscillation_bound {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℝ) (a b δ : ℝ) (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b)
    (hδ : ∀ S : Set X, |μ.real S - ν.real S| ≤ δ) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ (b - a) * δ := by
  have he (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
      (∫ x, f x ∂μ) - ∫ x, f x ∂ν =
        ∑ x, f x * (μ.real {x} - ν.real {x}) := by
    rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    simp only [smul_eq_mul]
    ring
  have hup (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (h : ∀ S : Set X, |μ.real S - ν.real S| ≤ δ) :
      (∫ x, f x ∂μ) - ∫ x, f x ∂ν ≤ (b - a) * δ := by
    rw [he]
    apply finite_sum_oscillation_bound f _ a b δ ha hb
    · simp [Finset.sum_sub_distrib]
    · intro S
      rw [Finset.sum_sub_distrib, sum_measureReal_singleton, sum_measureReal_singleton]
      exact (le_abs_self _).trans (h S)
  exact abs_le.mpr ⟨by linarith [hup ν μ (fun S => by simpa [abs_sub_comm] using hδ S)],
    hup μ ν hδ⟩

private theorem finite_profile_event_bound {J : Type*} [Fintype J]
    (p q : J → unitInterval) (A : Set (Set J)) :
    |(prodBernoulli p).real A - (prodBernoulli q).real A| ≤
      min 1 (∑ j, |(p j : ℝ) - q j|) := by
  apply le_min
  · apply abs_le.mpr
    have hp0 := measureReal_nonneg (μ := prodBernoulli p) (s := A)
    have hq0 := measureReal_nonneg (μ := prodBernoulli q) (s := A)
    have hp1 := measureReal_le_one (μ := prodBernoulli p) (s := A)
    have hq1 := measureReal_le_one (μ := prodBernoulli q) (s := A)
    constructor <;> linarith
  · have h := abs_prodBernoulli_real_sub_le p q (Set.toFinite A).measurableSet
      (by simp [tsum_fintype])
    simpa [tsum_fintype, ENNReal.toReal_sum, ENNReal.toReal_ofReal, abs_nonneg] using h

/-- The finite-observable perturbation bound with its exact oscillation and
clipping at one. Profiles need not be ordered; finite-cylinder events satisfy
the corresponding bound without an oscillation factor. -/
@[tag "RGN6"]
theorem finite_profile_oscillation_and_event_bound {I : Type*}
    (F : Finset I) (p q : I → unitInterval) :
    (∀ f : Set F → ℝ,
      |(∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli p) -
        ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q| ≤
      (sSup (Set.range f) - sInf (Set.range f)) *
        min 1 (∑ i ∈ F, |(p i : ℝ) - q i|)) ∧
    (∀ A : Set (Set F),
      |(prodBernoulli p).real {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A} -
        (prodBernoulli q).real {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A}| ≤
        min 1 (∑ i ∈ F, |(p i : ℝ) - q i|)) := by
  have hs : (∑ i : F, |(p i : ℝ) - q i|) = ∑ i ∈ F, |(p i : ℝ) - q i| := by
    exact Finset.sum_coe_sort F (fun i => |(p i : ℝ) - q i|)
  constructor
  · intro f
    have hr (p : I → unitInterval) :
        (∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli p) =
          ∫ ω, f ω ∂prodBernoulli (fun i : F => p i) := by
      rw [integral_prodBernoulli_cylinder, integral_prodBernoulli]
    rw [hr p, hr q, ← hs]
    exact finite_integral_oscillation_bound _ _ f _ _ _
      (fun x => csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self x))
      (fun x => le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self x))
      (finite_profile_event_bound _ _)
  · intro A
    simp only [measureReal_def, prodBernoulli_cylinder_apply]
    rw [← hs]
    exact finite_profile_event_bound _ _ A

end PercLib.Probability

namespace PercLib.Probability

/-- Empty observations have zero perturbation, even when ambient profiles differ. -/
example (p q : ℝ → unitInterval) (f : Set (∅ : Finset ℝ) → ℝ) :
    (∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli p) =
      ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli q := by
  have h := (finite_profile_oscillation_and_event_bound ∅ p q).1 f
  simpa only [Finset.sum_empty, min_eq_right zero_le_one, mul_zero,
    abs_nonpos_iff, sub_eq_zero] using h

/-- Two oppositely ordered endpoint profiles have coordinate-distance sum two;
the finite observable bound still clips its multiplier to one. -/
example (f : Set (Finset.univ : Finset Bool) → ℝ) :
    |(∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli (fun b : Bool => if b then 1 else 0)) -
      ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli (fun b : Bool => if b then 0 else 1)| ≤
      sSup (Set.range f) - sInf (Set.range f) := by
  have h := (finite_profile_oscillation_and_event_bound Finset.univ
    (fun b : Bool => if b then 1 else 0) (fun b : Bool => if b then 0 else 1)).1 f
  norm_num at h ⊢
  exact h

/-- The clipped event bound is attained by the preceding unordered profiles. -/
example :
    |(prodBernoulli (fun b : Bool => if b then 1 else 0)).real {ω | true ∈ ω} -
      (prodBernoulli (fun b : Bool => if b then 0 else 1)).real {ω | true ∈ ω}| = 1 := by
  norm_num [measureReal_def, prodBernoulli_setOf_mem]

end PercLib.Probability
