/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The independence argument adapts the method of bondPercolation_inter_of_disjoint and
bondPercolation_finiteEnergy in Percolation/Literature/FiniteEnergy.lean at
tomhutchcroft/near-critical-diffusivity, revision c820fea91a7482c1755de0ec94ecb9f59ccfcacc, under
Tom Hutchcroft's reuse permission recorded in `docs/DECISIONS.md`. Licence status: that file lies in
the source's `Percolation/Literature/` tree, which holds code vendored from the `percolation/`
project of `anthropics/formal-math` (Apache-2.0; see the source's `third_party/formal-math/`). For
any vendored part, the Apache-2.0 licence and its notices are those retained in
`third_party/percolation/`; no other upstream licence is asserted. Here the assignment is fixed, the
profile is inhomogeneous, and the law is PercLib's existing prodBernoulli. The overwrite proof uses
mathlib directly.
-/
module

public import PercLib.Probability.Cylinder
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.Superposition
public import Mathlib.Data.Sym.Sym2

/-! # Finite-energy identities

Finite assignments have their exact product probability, independently of every
measurable event determined by the complementary coordinates. Overwriting a
block fixes its profile at zero or one. Ambient indices need not be countable;
for bonds they include the diagonal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {ι : Type*}

/-- Exact probability of a finite assignment, including closed coordinates. -/
theorem prodBernoulli_inter_finset_eq [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) :
    prodBernoulli p {ω | ω ∩ (F : Set ι) = (a : Set ι)} =
      (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        ∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  classical
  rw [prodBernoulli_eq_map]
  change (Measure.map (MeasurableEquiv.setOfPred : (ι → Prop) ≃ᵐ Set ι)
    (Measure.infinitePi fun i => bernoulliMeasure True False (p i))) _ = _
  rw [MeasurableEquiv.setOfPred.map_apply]
  have h : MeasurableEquiv.setOfPred ⁻¹' {ω | ω ∩ (F : Set ι) = (a : Set ι)} =
      Set.pi (F : Set ι) (fun i => ({i ∈ a} : Set Prop)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe,
      Set.mem_singleton_iff]
    constructor
    · intro h i hi
      have := Set.ext_iff.mp h i
      simpa [hi] using this
    · intro h
      ext i
      by_cases hi : i ∈ F
      · simpa [hi] using h i hi
      · simp [hi, show i ∉ a from fun ha' => hi (ha ha')]
  rw [h, Measure.infinitePi_pi (μ := fun i : ι => bernoulliMeasure True False (p i))
    (s := F) (t := fun i => ({i ∈ a} : Set Prop))
    (fun i _ => measurableSet_singleton (i ∈ a)), ← Finset.prod_sdiff ha, mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [hi, bernoulliMeasure_def]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_sdiff.mp hi |>.2, bernoulliMeasure_def]

/-- A finite assignment is independent of any measurable event determined by
coordinates outside the assigned block. The determination hypothesis is stated
as invariance under changes inside the block. -/
theorem prodBernoulli_inter_pattern [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) (B : Set (Set ι)) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set ι, ω \ (F : Set ι) = ω' \ (F : Set ι) →
      (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (B ∩ {ω | ω ∩ (F : Set ι) = (a : Set ι)}) =
      prodBernoulli p B * (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        ∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  classical
  let S : Set ι := F
  let A : Set (Set S) := {{i : S | (i : ι) ∈ a}}
  let D : Set (Set (Sᶜ : Set ι)) := (fun u => Subtype.val '' u) ⁻¹' B
  have hD : MeasurableSet D := hB.preimage (measurable_image_val Sᶜ)
  have hA : MeasurableSet A := measurableSet_singleton _
  have hpreA : {ω : Set ι | {i : S | (i : ι) ∈ ω} ∈ A} =
      {ω | ω ∩ (F : Set ι) = (a : Set ι)} := by
    ext ω
    change ({i : S | (i : ι) ∈ ω} = {i : S | (i : ι) ∈ a}) ↔ _
    constructor
    · intro h
      ext i
      by_cases hi : i ∈ F
      · exact (and_iff_left hi).trans (Set.ext_iff.mp h ⟨i, hi⟩)
      · simp [hi, show i ∉ a from fun h => hi (ha h)]
    · intro h
      ext i
      have hi : (i : ι) ∈ F := i.property
      simpa [hi] using Set.ext_iff.mp h (i : ι)
  have hpreD : {ω : Set ι | {i : (Sᶜ : Set ι) | (i : ι) ∈ ω} ∈ D} = B := by
    ext ω
    change (Subtype.val '' {i : (Sᶜ : Set ι) | (i : ι) ∈ ω}) ∈ B ↔ ω ∈ B
    apply houtside
    ext i
    simp [S, Set.mem_image, and_comm]
  have h := prodBernoulli_block_inter p Sᶜ S (disjoint_compl_left)
    D A hD hA
  change prodBernoulli p
    ({ω | {i : (Sᶜ : Set ι) | (i : ι) ∈ ω} ∈ D} ∩ {ω | {i : S | (i : ι) ∈ ω} ∈ A}) = _ at h
  rw [hpreD, hpreA, prodBernoulli_inter_finset_eq p F a ha] at h
  exact h.trans (mul_assoc _ _ _).symm

/-- Overwriting any block by a fixed assignment fixes precisely those marginals.
The finiteness of the block is unnecessary for this pushforward identity. -/
theorem prodBernoulli_map_overwrite (p : ι → unitInterval)
    (F a : Set ι) (ha : a ⊆ F) [DecidablePred (· ∈ F)] [DecidablePred (· ∈ a)] :
    (prodBernoulli p).map (fun ω => (ω \ F) ∪ a) =
      prodBernoulli (fun i => if i ∈ F then (if i ∈ a then 1 else 0) else p i) := by
  classical
  let f : ι → Prop → Prop := fun i b => (b ∧ i ∉ F) ∨ i ∈ a
  have hf : ∀ i, Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hS : Measurable (fun q : ι → Prop => {i | q i}) :=
    MeasurableEquiv.setOfPred.measurable
  have ho : Measurable (fun ω : Set ι => (ω \ F) ∪ a) := by fun_prop
  rw [prodBernoulli_eq_map, Measure.map_map ho hS, prodBernoulli_eq_map]
  change (Measure.infinitePi fun i => bernoulliMeasure True False (p i)).map
    ((fun q : ι → Prop => {i | q i}) ∘ (fun q i => f i (q i))) = _
  rw [← Measure.map_map hS (by fun_prop), Measure.infinitePi_map_pi _ hf]
  congr 1
  congr 1
  funext i
  rw [map_bernoulliMeasure]
  by_cases hi : i ∈ F
  · by_cases hai : i ∈ a <;> simp [f, hi, hai]
  · have hai : i ∉ a := fun h => hi (ha h)
    simp [f, hi, hai]

/-- Every strictly interior finite assignment has positive probability inside
any positive measurable event determined by its complementary coordinates. -/
theorem prodBernoulli_inter_pattern_pos [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) (B : Set (Set ι)) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set ι, ω \ (F : Set ι) = ω' \ (F : Set ι) →
      (ω ∈ B ↔ ω' ∈ B)) (hpos : 0 < prodBernoulli p B)
    (hp : ∀ i ∈ F, 0 < p i ∧ p i < 1) :
    0 < prodBernoulli p (B ∩ {ω | ω ∩ (F : Set ι) = (a : Set ι)}) := by
  rw [prodBernoulli_inter_pattern p F a ha B hB houtside]
  apply pos_iff_ne_zero.mpr
  apply mul_ne_zero (mul_ne_zero (ne_of_gt hpos) ?_) ?_
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have h : 0 < unitInterval.toNNReal (p i) := (hp i (ha hi)).1
    exact ne_of_gt (by exact_mod_cast h)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have h : 0 < unitInterval.toNNReal (unitInterval.symm (p i)) := by
      change 0 < (unitInterval.symm (p i) : ℝ)
      rw [unitInterval.coe_symm_eq]
      exact sub_pos.mpr (hp i (Finset.mem_sdiff.mp hi).1).2
    exact ne_of_gt (by exact_mod_cast h)

/-- Inserting a single bond fixes its marginal at one, even for a loop. -/
theorem prodBernoulli_map_insert_bond {V : Type*} [DecidableEq (Sym2 V)]
    (p : Sym2 V → unitInterval) (e : Sym2 V) :
    (prodBernoulli p).map (fun ω => insert e ω) =
      prodBernoulli (Function.update p e 1) := by
  have hp : (fun i => if i ∈ ({e} : Set (Sym2 V)) then
      (if i ∈ ({e} : Set (Sym2 V)) then (1 : unitInterval) else 0) else p i) =
      Function.update p e 1 := by
    funext i
    by_cases h : i = e <;> simp [h]
  have h := prodBernoulli_map_overwrite p {e} {e} (Set.Subset.refl _)
  rw [hp] at h
  have hf : (fun ω : Set (Sym2 V) => (ω \ {e}) ∪ {e}) = fun ω => insert e ω := by
    funext ω
    ext i
    by_cases hi : i = e <;> simp [hi]
  rw [hf] at h
  exact h

/-- Deleting a single bond fixes its marginal at zero, even for a loop. -/
theorem prodBernoulli_map_delete_bond {V : Type*} [DecidableEq (Sym2 V)]
    (p : Sym2 V → unitInterval) (e : Sym2 V) :
    (prodBernoulli p).map (fun ω => ω \ {e}) =
      prodBernoulli (Function.update p e 0) := by
  have hp : (fun i => if i ∈ ({e} : Set (Sym2 V)) then
      (if i ∈ (∅ : Set (Sym2 V)) then (1 : unitInterval) else 0) else p i) =
      Function.update p e 0 := by
    funext i
    simp [Function.update_apply]
  simpa only [hp, Set.union_empty] using
    prodBernoulli_map_overwrite p {e} ∅ (Set.empty_subset _)

/-- The one-bond open factor is independent of any measurable event determined
by all other bonds. No non-diagonal hypothesis is needed. -/
theorem prodBernoulli_inter_bond_open {V : Type*} (p : Sym2 V → unitInterval)
    (e : Sym2 V) (B : Set (Set (Sym2 V))) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set (Sym2 V), ω \ {e} = ω' \ {e} → (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (B ∩ {ω | e ∈ ω}) =
      prodBernoulli p B * (unitInterval.toNNReal (p e) : ℝ≥0∞) := by
  classical
  have heq : {ω : Set (Sym2 V) | ω ∩ {e} = {e}} = {ω | e ∈ ω} := by
    ext ω
    simp [Set.inter_eq_right]
  simpa [heq] using prodBernoulli_inter_pattern p {e} {e} (Finset.Subset.refl _)
    B hB (by simpa using houtside)

/-- The one-bond closed factor, including diagonal bonds. -/
theorem prodBernoulli_inter_bond_closed {V : Type*} (p : Sym2 V → unitInterval)
    (e : Sym2 V) (B : Set (Set (Sym2 V))) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set (Sym2 V), ω \ {e} = ω' \ {e} → (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (B ∩ {ω | e ∉ ω}) = prodBernoulli p B *
      (unitInterval.toNNReal (unitInterval.symm (p e)) : ℝ≥0∞) := by
  classical
  simpa [Set.inter_singleton_eq_empty] using
    prodBernoulli_inter_pattern p {e} ∅ (Finset.empty_subset _) B hB (by simpa using houtside)

/-! ### Images of events under a finite overwrite -/

/-- The event that a configuration has a prescribed trace on a finite set is measurable. -/
theorem measurableSet_setOf_inter_eq (F : Finset ι) (A : Set ι) :
    MeasurableSet {ω : Set ι | ω ∩ (F : Set ι) = A} := by
  classical
  by_cases hA : A ⊆ F
  · have : {ω : Set ι | ω ∩ (F : Set ι) = A} = ⋂ i ∈ F, {ω | i ∈ ω ↔ i ∈ A} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · rintro rfl i hi
        simp [hi]
      · intro h
        ext i
        by_cases hi : i ∈ F
        · simpa [hi] using h i hi
        · simp only [Set.mem_inter_iff, Finset.mem_coe, hi, and_false, false_iff]
          exact fun h' => hi (hA h')
    rw [this]
    refine Finset.measurableSet_biInter F fun i _ => ?_
    by_cases hiA : i ∈ A
    · simpa [hiA] using measurableSet_mem i
    · have := (measurableSet_mem i).compl
      simpa [hiA, Set.compl_def] using this
  · have : {ω : Set ι | ω ∩ (F : Set ι) = A} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact hA Set.inter_subset_right
    rw [this]
    exact MeasurableSet.empty

/-- Exact probability of a finite assignment, in real form. -/
theorem prodBernoulli_real_inter_finset_eq [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) :
    (prodBernoulli p).real {ω | ω ∩ (F : Set ι) = (a : Set ι)} =
      (∏ i ∈ a, (p i : ℝ)) * ∏ i ∈ F \ a, (1 - (p i : ℝ)) := by
  classical
  rw [measureReal_def, prodBernoulli_inter_finset_eq p F a ha, ENNReal.toReal_mul,
    ENNReal.toReal_prod, ENNReal.toReal_prod]
  simp [unitInterval.coe_symm_eq]

/-- Assembling an outside configuration with a fixed block assignment is measurable. -/
theorem measurable_image_val_union (P : Set ι) (b : Set ι) :
    Measurable (fun ξ : Set P => (Subtype.val '' ξ : Set ι) ∪ b) :=
  (measurable_image_val P).union measurable_const

/-- The outside configurations that admit an assignment on `F` lying in `A`. -/
theorem measurableSet_setOf_exists_image_val_union_mem (F : Finset ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) :
    MeasurableSet {ξ : Set ((F : Set ι)ᶜ : Set ι) |
      ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A} := by
  have : {ξ : Set ((F : Set ι)ᶜ : Set ι) |
      ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A} =
      ⋃ b ∈ F.powerset, (fun ξ : Set ((F : Set ι)ᶜ : Set ι) =>
        (Subtype.val '' ξ : Set ι) ∪ (b : Set ι)) ⁻¹' A := by
    ext ξ; simp
  rw [this]
  exact Finset.measurableSet_biUnion _ fun b _ => measurable_image_val_union _ _ hA

/-- The image of an event under a finite overwrite: the overwritten block carries the
prescribed assignment and the outside part admits some assignment in the event. -/
theorem image_overwrite_eq [DecidableEq ι] (F a : Finset ι) (ha : a ⊆ F) (A : Set (Set ι)) :
    (fun ω => (ω \ (F : Set ι)) ∪ (a : Set ι)) '' A =
      {ω | {i : ((F : Set ι)ᶜ : Set ι) | (i : ι) ∈ ω} ∈
          {ξ : Set ((F : Set ι)ᶜ : Set ι) |
            ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A}} ∩
        {ω | ω ∩ (F : Set ι) = (a : Set ι)} := by
  have hval : ∀ ω : Set ι,
      (Subtype.val '' {i : ((F : Set ι)ᶜ : Set ι) | (i : ι) ∈ ω} : Set ι) = ω \ F := by
    intro ω; ext i; simp [and_comm]
  classical
  ext ω
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_powerset, hval]
  constructor
  · rintro ⟨η, hη, rfl⟩
    refine ⟨⟨F.filter (· ∈ η), Finset.filter_subset _ _, ?_⟩, ?_⟩
    · convert hη using 1
      ext i
      by_cases hi : i ∈ F
      · by_cases hai : i ∈ a <;> simp [hi, hai]
      · simp [hi, show i ∉ a from fun h => hi (ha h)]
    · ext i
      by_cases hi : i ∈ F
      · by_cases hai : i ∈ a <;> simp [hi, hai]
      · simp [hi, show i ∉ a from fun h => hi (ha h)]
  · rintro ⟨⟨b, hb, hA⟩, hωF⟩
    refine ⟨_, hA, ?_⟩
    ext i
    by_cases hi : i ∈ F
    · have := Set.ext_iff.1 hωF i
      simp only [Set.mem_inter_iff, Finset.mem_coe, hi, and_true] at this
      simpa [hi] using this.symm
    · have hb' : i ∉ b := fun h => hi (hb h)
      have hai : i ∉ a := fun h => hi (ha h)
      simp [hi, hb', hai]

/-- Every configuration of `A` restricts to an outside configuration admitting an
assignment on `F` in `A`. -/
theorem prodBernoulli_le_prodBernoulli_compl_exists_union_mem (p : ι → unitInterval)
    (F : Finset ι) {A : Set (Set ι)} (hA : MeasurableSet A) :
    prodBernoulli p A ≤ prodBernoulli (fun i : ((F : Set ι)ᶜ : Set ι) => p i)
      {ξ | ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A} := by
  classical
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set ((F : Set ι)ᶜ : Set ι))) :=
    Measurable.of_mem fun i => (measurableSet_mem i.val).mem
  rw [← prodBernoulli_map_preimage_val p, Measure.map_apply hm
    (measurableSet_setOf_exists_image_val_union_mem F hA)]
  refine measure_mono fun ω hω => ⟨F.filter (· ∈ ω), Finset.mem_powerset.2
    (Finset.filter_subset _ _), ?_⟩
  convert hω using 1
  ext i
  by_cases hi : i ∈ F <;> simp [hi]

/-- **Image of a finite overwrite, measurability.** -/
theorem measurableSet_image_overwrite [DecidableEq ι] (F a : Finset ι) (ha : a ⊆ F)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    MeasurableSet ((fun ω => (ω \ (F : Set ι)) ∪ (a : Set ι)) '' A) := by
  rw [image_overwrite_eq F a ha A]
  refine MeasurableSet.inter ?_ (measurableSet_setOf_inter_eq F a)
  exact (measurableSet_setOf_exists_image_val_union_mem F hA).preimage
    (Measurable.of_mem fun i => (measurableSet_mem i.val).mem)

/-- **Image of a finite overwrite, probability.** -/
theorem prodBernoulli_image_overwrite [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) {A : Set (Set ι)} (hA : MeasurableSet A) :
    prodBernoulli p ((fun ω => (ω \ (F : Set ι)) ∪ (a : Set ι)) '' A) =
      (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        (∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞)) *
        prodBernoulli (fun i : ((F : Set ι)ᶜ : Set ι) => p i)
          {ξ | ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A} := by
  have hS := measurableSet_setOf_exists_image_val_union_mem F hA
  have hm : Measurable (fun ω : Set ι => {i : ((F : Set ι)ᶜ : Set ι) | (i : ι) ∈ ω}) :=
    Measurable.of_mem fun i => (measurableSet_mem i.val).mem
  have hm' : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set ((F : Set ι)ᶜ : Set ι))) :=
    hm
  rw [image_overwrite_eq F a ha A, prodBernoulli_inter_pattern p F a ha
    {ω | {i : ((F : Set ι)ᶜ : Set ι) | (i : ι) ∈ ω} ∈
      {ξ : Set ((F : Set ι)ᶜ : Set ι) |
        ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A}} (hS.preimage hm),
    ← prodBernoulli_map_preimage_val p, Measure.map_apply hm' hS, mul_assoc, mul_comm]
  · rfl
  · intro ω ω' h
    have : {i : ((F : Set ι)ᶜ : Set ι) | (i : ι) ∈ ω} =
        {i : ((F : Set ι)ᶜ : Set ι) | (i : ι) ∈ ω'} := by
      ext i
      have := Set.ext_iff.1 h i
      have hi : (i : ι) ∉ F := i.2
      simpa [hi] using this
    simp only [Set.mem_ofPred_eq, this]

/-- **Image of a finite overwrite, lower bound.** -/
theorem mul_prodBernoulli_le_mul_prodBernoulli_compl_exists_union_mem [DecidableEq ι]
    (p : ι → unitInterval) (F a : Finset ι) {A : Set (Set ι)} (hA : MeasurableSet A) :
    (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        (∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞)) *
        prodBernoulli p A ≤
      (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        (∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞)) *
        prodBernoulli (fun i : ((F : Set ι)ᶜ : Set ι) => p i)
          {ξ | ∃ b ∈ F.powerset, (Subtype.val '' ξ : Set ι) ∪ (b : Set ι) ∈ A} :=
  mul_le_mul_right (prodBernoulli_le_prodBernoulli_compl_exists_union_mem p F hA) _

-- Endpoint, empty-block, non-vacuity, and diagonal witnesses.
example : prodBernoulli (fun b : Bool => if b then 1 else 0)
    {ω | ω ∩ ({false, true} : Set Bool) = {true}} = 1 := by
  simpa using prodBernoulli_inter_finset_eq (fun b : Bool => if b then 1 else 0)
    {false, true} {true} (by simp)

example (p : ι → unitInterval) (B : Set (Set ι)) :
    prodBernoulli p (B ∩ {ω | ω ∩ (∅ : Set ι) = ∅}) = prodBernoulli p B := by
  simp

example : 0 < prodBernoulli (fun _ : Bool => ⟨(1/2 : ℝ), by constructor <;> norm_num⟩)
    {ω | ω ∩ ({false, true} : Set Bool) = {true}} := by
  simpa using prodBernoulli_inter_pattern_pos
    (fun _ : Bool => ⟨(1/2 : ℝ), by constructor <;> norm_num⟩)
    {false, true} {true} (by simp) Set.univ MeasurableSet.univ
    (by simp) (by simp) (by
        intro i hi
        constructor
        · change (0 : ℝ) < 1 / 2
          norm_num
        · change (1 / 2 : ℝ) < 1
          norm_num)

example (p : Sym2 Bool → unitInterval) :
    prodBernoulli p {ω | s(false, false) ∉ ω} =
      (unitInterval.toNNReal (unitInterval.symm (p s(false, false))) : ℝ≥0∞) := by
  simpa using prodBernoulli_inter_bond_closed p s(false, false) Set.univ
    MeasurableSet.univ (by simp)

end PercLib.Probability
