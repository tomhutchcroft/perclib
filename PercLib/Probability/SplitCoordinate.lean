/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the exact increment of a disjoint-occurrence probability when one
shared coordinate is split into two independent copies (wiki backbone-connections, tag XWH4). No
upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Probability.Coordinate
public import PercLib.Probability.DisjointOccurrence
public import PercLib.Probability.Transport.Pullback

/-! # Splitting one coordinate of a disjoint occurrence

Let `I` be finite, `A B ⊆ Set I` increasing, `e : I`, and write `S = {e}ᶜ`. For `η ⊆ S` the
sections are `A₀ = {η | η ∈ A}` (`e` closed) and `A₁ = {η | insert e η ∈ A}` (`e` open), viewed
as events on `Set S`, and similarly for `B`. Put `C_ij = A_i □ B_j`, `U = C₁₀ ∪ C₀₁` and
`V = C₁₀ ∩ C₀₁`, with `μ` the product law on `S`.

* `mem_disjointOccurrence_iff_of_mem`, `mem_disjointOccurrence_iff_of_notMem`: with `e` open,
  `A □ B` occurs exactly when its trace on `S` is in `U`; with `e` closed, when it is in `C₀₀`.
* `mem_disjointOccurrence_split_iff`: on `I ⊕ Unit`, where `A` reads `e` from `inl e` and `B`
  reads it from `inr ()`, the split event occurs exactly when the trace is in `C_ab`, with `a`
  and `b` the states of the two copies.
* `prodBernoulli_real_split_sub` (XWH4):
  `P(H̃) - P(H) = p² μ(C₁₁ \ U) + p (1-p) μ(V \ C₀₀)` with `p = q e`; both terms are
  nonnegative (`split_terms_nonneg`), and the second vanishes exactly when `p ∈ {0,1}` or
  `μ(V \ C₀₀) = 0` (`split_second_term_eq_zero_iff`).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set

namespace PercLib.Probability

variable {I : Type*}

section Combinatorics

variable {A B : Set (Set I)} {e : I}

/-- The image of a subset of `{e}ᶜ` does not contain `e`. -/
theorem notMem_image_val_compl (η : Set ({e}ᶜ : Set I)) : e ∉ Subtype.val '' η := by
  rintro ⟨j, -, hj⟩
  exact j.2 hj

/-- The trace on `{e}ᶜ` is unchanged by inserting `e`. -/
theorem preimage_val_insert (ω : Set I) :
    (Subtype.val ⁻¹' insert e ω : Set ({e}ᶜ : Set I)) = Subtype.val ⁻¹' ω := by
  ext j
  have hj : (j : I) ≠ e := j.2
  simp [hj]

/-- The trace on `{e}ᶜ` is unchanged by deleting `e`. -/
theorem preimage_val_diff (ω : Set I) :
    (Subtype.val ⁻¹' (ω \ {e}) : Set ({e}ᶜ : Set I)) = Subtype.val ⁻¹' ω := by
  ext j
  simp

theorem isUpperSet_section_zero (hA : IsUpperSet A) :
    IsUpperSet {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∈ A} :=
  fun _ _ h hη => hA (image_mono h) hη

theorem isUpperSet_section_one (hA : IsUpperSet A) :
    IsUpperSet {η : Set ({e}ᶜ : Set I) | insert e (Subtype.val '' η) ∈ A} :=
  fun _ _ h hη => hA (insert_subset_insert (image_mono h)) hη

/-- `val '' (val⁻¹' F) = F` when `e ∉ F`. -/
theorem image_preimage_val_of_notMem {F : Set I} (he : e ∉ F) :
    Subtype.val '' (Subtype.val ⁻¹' F : Set ({e}ᶜ : Set I)) = F := by
  rw [Subtype.image_preimage_coe]
  exact inter_eq_right.2 fun x hx hxe => he (hxe ▸ hx)

/-- `F ⊆ insert e (val '' (val⁻¹' F))`. -/
theorem subset_insert_image_preimage_val (F : Set I) :
    F ⊆ insert e (Subtype.val '' (Subtype.val ⁻¹' F : Set ({e}ᶜ : Set I))) := by
  intro x hx
  by_cases hxe : x = e
  · exact Or.inl hxe
  · exact Or.inr ⟨⟨x, hxe⟩, hx, rfl⟩

/-- Disjoint traces have disjoint images. -/
theorem disjoint_image_val {F H : Set ({e}ᶜ : Set I)} (h : Disjoint F H) :
    Disjoint (Subtype.val '' F) (Subtype.val '' H) :=
  (disjoint_image_iff Subtype.val_injective).2 h

/-- **`e` open.** If `e ∈ ω`, then `ω ∈ A □ B` iff its trace on `{e}ᶜ` is in `C₁₀ ∪ C₀₁`. -/
theorem mem_disjointOccurrence_iff_of_mem (hA : IsUpperSet A) (hB : IsUpperSet B) {ω : Set I}
    (he : e ∈ ω) :
    ω ∈ disjointOccurrence A B ↔
      (Subtype.val ⁻¹' ω : Set ({e}ᶜ : Set I)) ∈
        disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A} {η | Subtype.val '' η ∈ B} ∪
        disjointOccurrence {η | Subtype.val '' η ∈ A} {η | insert e (Subtype.val '' η) ∈ B} := by
  rw [mem_union, mem_disjointOccurrence_iff_open hA hB,
    mem_disjointOccurrence_iff_open (isUpperSet_section_one hA) (isUpperSet_section_zero hB),
    mem_disjointOccurrence_iff_open (isUpperSet_section_zero hA) (isUpperSet_section_one hB)]
  constructor
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩
    have hF' := hF.preimage (Subtype.val_injective (p := (· ∈ ({e}ᶜ : Set I)))).injOn
    have hH' := hH.preimage (Subtype.val_injective (p := (· ∈ ({e}ᶜ : Set I)))).injOn
    have hd' : Disjoint (Subtype.val ⁻¹' F : Set ({e}ᶜ : Set I)) (Subtype.val ⁻¹' H) :=
      hd.preimage _
    by_cases heH : e ∈ H
    · have heF : e ∉ F := fun h => hd.ne_of_mem h heH rfl
      refine Or.inr ⟨_, _, hF', hH', hd', preimage_mono hFω, preimage_mono hHω, ?_, ?_⟩
      · change Subtype.val '' _ ∈ A
        rwa [image_preimage_val_of_notMem heF]
      · exact hB (subset_insert_image_preimage_val H) hHB
    · refine Or.inl ⟨_, _, hF', hH', hd', preimage_mono hFω, preimage_mono hHω, ?_, ?_⟩
      · exact hA (subset_insert_image_preimage_val F) hFA
      · change Subtype.val '' _ ∈ B
        rwa [image_preimage_val_of_notMem heH]
  · rintro (⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩ | ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩)
    · refine ⟨insert e (Subtype.val '' F), Subtype.val '' H, (hF.image _).insert e, hH.image _,
        ?_, insert_subset he (image_subset_iff.2 hFω), image_subset_iff.2 hHω, hFA, hHB⟩
      exact disjoint_insert_left.2 ⟨notMem_image_val_compl H, disjoint_image_val hd⟩
    · refine ⟨Subtype.val '' F, insert e (Subtype.val '' H), hF.image _, (hH.image _).insert e,
        ?_, image_subset_iff.2 hFω, insert_subset he (image_subset_iff.2 hHω), hFA, hHB⟩
      exact disjoint_insert_right.2 ⟨notMem_image_val_compl F, disjoint_image_val hd⟩

/-- **`e` closed.** If `e ∉ ω`, then `ω ∈ A □ B` iff its trace on `{e}ᶜ` is in `C₀₀`. -/
theorem mem_disjointOccurrence_iff_of_notMem (hA : IsUpperSet A) (hB : IsUpperSet B)
    {ω : Set I} (he : e ∉ ω) :
    ω ∈ disjointOccurrence A B ↔
      (Subtype.val ⁻¹' ω : Set ({e}ᶜ : Set I)) ∈
        disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B} := by
  rw [mem_disjointOccurrence_iff_open hA hB,
    mem_disjointOccurrence_iff_open (isUpperSet_section_zero hA) (isUpperSet_section_zero hB)]
  constructor
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩
    refine ⟨_, _, hF.preimage Subtype.val_injective.injOn,
      hH.preimage Subtype.val_injective.injOn, hd.preimage _, preimage_mono hFω,
      preimage_mono hHω, ?_, ?_⟩
    · change Subtype.val '' _ ∈ A
      rwa [image_preimage_val_of_notMem fun h => he (hFω h)]
    · change Subtype.val '' _ ∈ B
      rwa [image_preimage_val_of_notMem fun h => he (hHω h)]
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩
    exact ⟨Subtype.val '' F, Subtype.val '' H, hF.image _, hH.image _, disjoint_image_val hd,
      image_subset_iff.2 hFω, image_subset_iff.2 hHω, hFA, hHB⟩

/-- The trace of a configuration on `I ⊕ Unit` along `j ↦ inl j`, `j ∈ {e}ᶜ`. -/
theorem injective_inl_val : Function.Injective
    (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) :=
  fun _ _ h => Subtype.val_injective (Sum.inl_injective h)

/-- **The split model.** On `I ⊕ Unit`, let `A` read `e` from `inl e` and `B` read it from
`inr ()`. Then the split event occurs iff the trace on `{e}ᶜ` lies in the disjoint occurrence
of the sections selected by the states of `inl e` and `inr ()`. -/
theorem mem_disjointOccurrence_split_iff (hA : IsUpperSet A) (hB : IsUpperSet B)
    (ω : Set (I ⊕ Unit)) :
    ω ∈ disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A}
        {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B} ↔
      ((fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' ω) ∈
        disjointOccurrence {η | Subtype.val '' η ∪ {i | i = e ∧ Sum.inl e ∈ ω} ∈ A}
          {η | Subtype.val '' η ∪ {i | i = e ∧ Sum.inr () ∈ ω} ∈ B} := by
  set g : ({e}ᶜ : Set I) → I ⊕ Unit := fun j => Sum.inl (j : I) with hg
  have hgi : Function.Injective g := injective_inl_val
  have hA' : IsUpperSet {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A} :=
    fun _ _ h hω => hA (preimage_mono h) hω
  have hB' : IsUpperSet {ω : Set (I ⊕ Unit) |
      {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B} := by
    refine fun _ _ h hω => hB ?_ hω
    rintro i (⟨hi, hm⟩ | ⟨hi, hm⟩)
    · exact Or.inl ⟨hi, h hm⟩
    · exact Or.inr ⟨hi, h hm⟩
  have hsA : ∀ c : Prop, IsUpperSet
      {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∪ {i | i = e ∧ c} ∈ A} :=
    fun c _ _ h hη => hA (union_subset_union_left _ (image_mono h)) hη
  have hsB : ∀ c : Prop, IsUpperSet
      {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∪ {i | i = e ∧ c} ∈ B} :=
    fun c _ _ h hη => hB (union_subset_union_left _ (image_mono h)) hη
  rw [mem_disjointOccurrence_iff_open hA' hB', mem_disjointOccurrence_iff_open (hsA _) (hsB _)]
  constructor
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩
    refine ⟨g ⁻¹' F, g ⁻¹' H, hF.preimage hgi.injOn, hH.preimage hgi.injOn, hd.preimage _,
      preimage_mono hFω, preimage_mono hHω, ?_, ?_⟩
    · refine hA ?_ hFA
      intro i hi
      by_cases hie : i = e
      · exact Or.inr ⟨hie, hFω (hie ▸ hi)⟩
      · exact Or.inl ⟨⟨i, hie⟩, hi, rfl⟩
    · refine hB ?_ hHB
      rintro i (⟨hie, hi⟩ | ⟨hie, hi⟩)
      · exact Or.inl ⟨⟨i, hie⟩, hi, rfl⟩
      · exact Or.inr ⟨hie, hHω hi⟩
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩
    refine ⟨g '' F ∪ {x | x = Sum.inl e ∧ Sum.inl e ∈ ω},
      g '' H ∪ {x | x = Sum.inr () ∧ Sum.inr () ∈ ω},
      (hF.image g).union ((finite_singleton (Sum.inl e)).subset fun x hx => hx.1),
      (hH.image g).union ((finite_singleton (Sum.inr ())).subset fun x hx => hx.1), ?_,
      union_subset (image_subset_iff.2 hFω) fun x hx => hx.1 ▸ hx.2,
      union_subset (image_subset_iff.2 hHω) fun x hx => hx.1 ▸ hx.2, ?_, ?_⟩
    · refine disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩,
        disjoint_union_right.2 ⟨?_, ?_⟩⟩
      · exact (disjoint_image_iff hgi).2 hd
      · rw [disjoint_left]
        rintro _ ⟨j, -, rfl⟩ ⟨h, -⟩
        exact Sum.inl_ne_inr h
      · rw [disjoint_left]
        rintro _ ⟨h, -⟩ ⟨j, -, hj⟩
        rw [h] at hj
        exact j.2 (Sum.inl_injective hj)
      · rw [disjoint_left]
        rintro _ ⟨h, -⟩ ⟨h', -⟩
        rw [h] at h'
        exact Sum.inl_ne_inr h'
    · refine hA ?_ hFA
      rintro i (⟨j, hj, rfl⟩ | ⟨rfl, hi⟩)
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨rfl, hi⟩
    · refine hB ?_ hHB
      rintro i (⟨j, hj, rfl⟩ | ⟨rfl, hi⟩)
      · exact Or.inl ⟨j.2, Or.inl ⟨j, hj, rfl⟩⟩
      · exact Or.inr ⟨rfl, Or.inr ⟨rfl, hi⟩⟩

end Combinatorics

section Measure

variable [Finite I] {A B : Set (Set I)} {e : I}

omit [Finite I] in
/-- The trace map on `{e}ᶜ` is measurable. -/
theorem measurable_preimage_val_compl :
    Measurable fun ω : Set I => (Subtype.val ⁻¹' ω : Set ({e}ᶜ : Set I)) :=
  Measurable.of_mem fun i => (measurableSet_mem i.val).mem

/-- **The unsplit probability.** `P(A □ B) = p μ(C₁₀ ∪ C₀₁) + (1 - p) μ(C₀₀)` with `p = q e`. -/
theorem prodBernoulli_real_disjointOccurrence_eq (q : I → unitInterval) (hA : IsUpperSet A)
    (hB : IsUpperSet B) :
    (prodBernoulli q).real (disjointOccurrence A B) =
      (q e : ℝ) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A} {η | Subtype.val '' η ∈ B} ∪
            disjointOccurrence {η | Subtype.val '' η ∈ A} {η | insert e (Subtype.val '' η) ∈ B}) +
        (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          (disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B}) := by
  classical
  rw [prodBernoulli_eq_affine q e]
  congr 2
  · rw [← prodBernoulli_map_insert q e,
      map_measureReal_apply (measurable_insert e) (Set.toFinite _).measurableSet]
    have hpre : (fun ω : Set I => insert e ω) ⁻¹' disjointOccurrence A B =
        (fun ω : Set I => (Subtype.val ⁻¹' ω : Set ({e}ᶜ : Set I))) ⁻¹'
          (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A} {η | Subtype.val '' η ∈ B} ∪
            disjointOccurrence {η | Subtype.val '' η ∈ A}
              {η | insert e (Subtype.val '' η) ∈ B}) := by
      ext ω
      simp only [mem_preimage]
      rw [mem_disjointOccurrence_iff_of_mem hA hB (mem_insert e ω), preimage_val_insert]
    rw [hpre, ← map_measureReal_apply measurable_preimage_val_compl
      (Set.toFinite _).measurableSet, prodBernoulli_map_preimage_val]
  · rw [← prodBernoulli_map_diff_singleton q e,
      map_measureReal_apply (measurable_diff_singleton e) (Set.toFinite _).measurableSet]
    have hpre : (fun ω : Set I => ω \ {e}) ⁻¹' disjointOccurrence A B =
        (fun ω : Set I => (Subtype.val ⁻¹' ω : Set ({e}ᶜ : Set I))) ⁻¹'
          disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B} := by
      ext ω
      simp only [mem_preimage]
      rw [mem_disjointOccurrence_iff_of_notMem hA hB (fun h => h.2 rfl), preimage_val_diff]
    rw [hpre, ← map_measureReal_apply measurable_preimage_val_compl
      (Set.toFinite _).measurableSet, prodBernoulli_map_preimage_val]

/-- One of the four cases of the split model: after a measurable modification `φ` that fixes
the trace and sets the two copies of `e` to `s` and `t`, the split event has the probability of
`C_st`. -/
theorem prodBernoulli_real_map_split (q : I → unitInterval) (hA : IsUpperSet A)
    (hB : IsUpperSet B) (φ : Set (I ⊕ Unit) → Set (I ⊕ Unit)) (hφ : Measurable φ) (s t : Prop)
    (hs : ∀ ω, Sum.inl e ∈ φ ω ↔ s) (ht : ∀ ω, Sum.inr () ∈ φ ω ↔ t)
    (htr : ∀ ω, (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' φ ω =
      (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' ω) :
    ((prodBernoulli (Sum.elim q fun _ : Unit => q e)).map φ).real
        (disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A}
          {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B}) =
      (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
        (disjointOccurrence {η | Subtype.val '' η ∪ {i | i = e ∧ s} ∈ A}
          {η | Subtype.val '' η ∪ {i | i = e ∧ t} ∈ B}) := by
  set g : ({e}ᶜ : Set I) → I ⊕ Unit := fun j => Sum.inl (j : I) with hg
  have hgm : Measurable fun ω : Set (I ⊕ Unit) => g ⁻¹' ω :=
    Measurable.of_mem fun j => (measurableSet_mem (g j)).mem
  rw [map_measureReal_apply hφ (Set.toFinite _).measurableSet]
  have hpre : φ ⁻¹' disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A}
      {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B} =
      (fun ω : Set (I ⊕ Unit) => g ⁻¹' ω) ⁻¹'
        disjointOccurrence {η | Subtype.val '' η ∪ {i | i = e ∧ s} ∈ A}
          {η | Subtype.val '' η ∪ {i | i = e ∧ t} ∈ B} := by
    ext ω
    simp only [mem_preimage]
    rw [mem_disjointOccurrence_split_iff hA hB, htr ω]
    simp only [hs, ht]
  rw [hpre, ← map_measureReal_apply hgm (Set.toFinite _).measurableSet,
    prodBernoulli_map_preimage _ injective_inl_val]
  rfl

omit [Finite I] in
/-- The four sections, with `True`/`False` cases simplified. -/
theorem setOf_union_true (X : Set (Set I)) :
    {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∪ {i | i = e ∧ True} ∈ X} =
      {η | insert e (Subtype.val '' η) ∈ X} := by
  ext η
  simp [union_singleton]

omit [Finite I] in
theorem setOf_union_false (X : Set (Set I)) :
    {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∪ {i | i = e ∧ False} ∈ X} =
      {η | Subtype.val '' η ∈ X} := by
  ext η
  simp

/-- **The split probability.** With `p = q e` for both copies,
`P(H̃) = p (p μ(C₁₁) + (1-p) μ(C₁₀)) + (1-p) (p μ(C₀₁) + (1-p) μ(C₀₀))`. -/
theorem prodBernoulli_real_split_eq (q : I → unitInterval) (hA : IsUpperSet A)
    (hB : IsUpperSet B) :
    (prodBernoulli (Sum.elim q fun _ : Unit => q e)).real
        (disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A}
          {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B}) =
      (q e : ℝ) * ((q e : ℝ) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
            (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
              {η | insert e (Subtype.val '' η) ∈ B}) +
          (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
            (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
              {η | Subtype.val '' η ∈ B})) +
        (1 - (q e : ℝ)) * ((q e : ℝ) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
            (disjointOccurrence {η | Subtype.val '' η ∈ A}
              {η | insert e (Subtype.val '' η) ∈ B}) +
          (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
            (disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B})) := by
  classical
  have hab : (Sum.inr () : I ⊕ Unit) ≠ Sum.inl e := Sum.inr_ne_inl
  have hqb : ∀ t, Function.update (Sum.elim q fun _ : Unit => q e) (Sum.inl e) t (Sum.inr ()) =
      q e := fun t => by
    rw [Function.update_of_ne hab]
    rfl
  have hne : ∀ (c : I ⊕ Unit), (c = Sum.inl e ∨ c = Sum.inr ()) → ∀ j : ({e}ᶜ : Set I),
      (Sum.inl (j : I) : I ⊕ Unit) ≠ c := by
    rintro c (rfl | rfl) j
    · exact fun h => j.2 (Sum.inl_injective h)
    · exact Sum.inl_ne_inr
  have htr_ins : ∀ (c : I ⊕ Unit), (c = Sum.inl e ∨ c = Sum.inr ()) → ∀ ω : Set (I ⊕ Unit),
      (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' insert c ω =
        (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' ω := by
    rintro c hc ω
    ext j
    simp [hne c hc j]
  have htr_diff : ∀ (c : I ⊕ Unit), (c = Sum.inl e ∨ c = Sum.inr ()) → ∀ ω : Set (I ⊕ Unit),
      (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' (ω \ {c}) =
        (fun j : ({e}ᶜ : Set I) => (Sum.inl (j : I) : I ⊕ Unit)) ⁻¹' ω := by
    rintro c hc ω
    ext j
    simp [hne c hc j]
  have ha : (Sum.inl e : I ⊕ Unit) = Sum.inl e ∨ (Sum.inl e : I ⊕ Unit) = Sum.inr () :=
    Or.inl rfl
  have hb : (Sum.inr () : I ⊕ Unit) = Sum.inl e ∨ (Sum.inr () : I ⊕ Unit) = Sum.inr () :=
    Or.inr rfl
  rw [prodBernoulli_eq_affine _ (Sum.inl e), prodBernoulli_eq_affine _ (Sum.inr ()), hqb,
    prodBernoulli_eq_affine (Function.update _ (Sum.inl e) 0) (Sum.inr ()), hqb]
  have hqa : ((Sum.elim q fun _ : Unit => q e) (Sum.inl e)) = q e := rfl
  rw [hqa]
  rw [← prodBernoulli_map_insert (Function.update _ (Sum.inl e) 1),
    ← prodBernoulli_map_insert (Sum.elim q fun _ : Unit => q e),
    Measure.map_map (measurable_insert _) (measurable_insert _),
    ← prodBernoulli_map_diff_singleton (Function.update _ (Sum.inl e) 1),
    ← prodBernoulli_map_insert (Sum.elim q fun _ : Unit => q e),
    Measure.map_map (measurable_diff_singleton _) (measurable_insert _),
    ← prodBernoulli_map_insert (Function.update _ (Sum.inl e) 0),
    ← prodBernoulli_map_diff_singleton (Sum.elim q fun _ : Unit => q e),
    Measure.map_map (measurable_insert _) (measurable_diff_singleton _),
    ← prodBernoulli_map_diff_singleton (Function.update _ (Sum.inl e) 0),
    ← prodBernoulli_map_diff_singleton (Sum.elim q fun _ : Unit => q e),
    Measure.map_map (measurable_diff_singleton _) (measurable_diff_singleton _)]
  rw [prodBernoulli_real_map_split q hA hB _
      ((measurable_insert _).comp (measurable_insert _)) True True
      (fun ω => by simp) (fun ω => by simp)
      (fun ω => by simp only [Function.comp_apply]; rw [htr_ins _ hb, htr_ins _ ha]),
    prodBernoulli_real_map_split q hA hB _
      ((measurable_diff_singleton _).comp (measurable_insert _)) True False
      (fun ω => by simp) (fun ω => by simp)
      (fun ω => by simp only [Function.comp_apply]; rw [htr_diff _ hb, htr_ins _ ha]),
    prodBernoulli_real_map_split q hA hB _
      ((measurable_insert _).comp (measurable_diff_singleton _)) False True
      (fun ω => by simp) (fun ω => by simp)
      (fun ω => by simp only [Function.comp_apply]; rw [htr_ins _ hb, htr_diff _ ha]),
    prodBernoulli_real_map_split q hA hB _
      ((measurable_diff_singleton _).comp (measurable_diff_singleton _)) False False
      (fun ω => by simp) (fun ω => by simp)
      (fun ω => by simp only [Function.comp_apply]; rw [htr_diff _ hb, htr_diff _ ha])]
  simp only [setOf_union_true, setOf_union_false]

/-- **Splitting a shared coordinate.** Let `I` be finite, `A, B` increasing and `p = q e`. With the
sections `A₀ = {η | η ∈ A}`, `A₁ = {η | insert e η ∈ A}` on `{e}ᶜ`, `C_ij = A_i □ B_j`,
`U = C₁₀ ∪ C₀₁`, `V = C₁₀ ∩ C₀₁` and `μ` the product law on `{e}ᶜ`, the split event `H̃` (on
`I ⊕ Unit`, `A` reading `e` from `inl e` and `B` from the independent copy `inr ()`, also with
probability `p`) and `H = A □ B` satisfy `P(H̃) - P(H) = p² μ(C₁₁ \ U) + p (1-p) μ(V \ C₀₀)`. -/
theorem prodBernoulli_real_split_sub (q : I → unitInterval) (hA : IsUpperSet A)
    (hB : IsUpperSet B) :
    (prodBernoulli (Sum.elim q fun _ : Unit => q e)).real
        (disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A}
          {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B}) -
      (prodBernoulli q).real (disjointOccurrence A B) =
      (q e : ℝ) ^ 2 * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
              {η | insert e (Subtype.val '' η) ∈ B} \
            (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∪
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B})) +
        (q e : ℝ) * (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          ((disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∩
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B}) \
            disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B}) := by
  rw [prodBernoulli_real_split_eq q hA hB, prodBernoulli_real_disjointOccurrence_eq q hA hB]
  set μ := prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)
  set A₀ := {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∈ A}
  set A₁ := {η : Set ({e}ᶜ : Set I) | insert e (Subtype.val '' η) ∈ A}
  set B₀ := {η : Set ({e}ᶜ : Set I) | Subtype.val '' η ∈ B}
  set B₁ := {η : Set ({e}ᶜ : Set I) | insert e (Subtype.val '' η) ∈ B}
  have hA01 : A₀ ⊆ A₁ := fun η h => hA (subset_insert _ _) h
  have hB01 : B₀ ⊆ B₁ := fun η h => hB (subset_insert _ _) h
  have hU : disjointOccurrence A₁ B₀ ∪ disjointOccurrence A₀ B₁ ⊆ disjointOccurrence A₁ B₁ :=
    union_subset (disjointOccurrence_mono subset_rfl hB01)
      (disjointOccurrence_mono hA01 subset_rfl)
  have hV : disjointOccurrence A₀ B₀ ⊆
      disjointOccurrence A₁ B₀ ∩ disjointOccurrence A₀ B₁ :=
    subset_inter (disjointOccurrence_mono hA01 subset_rfl)
      (disjointOccurrence_mono subset_rfl hB01)
  rw [measureReal_sdiff hU (Set.toFinite _).measurableSet,
    measureReal_sdiff hV (Set.toFinite _).measurableSet]
  have hUV := measureReal_union_add_inter (μ := μ) (s := disjointOccurrence A₁ B₀)
    (Set.toFinite (disjointOccurrence A₀ B₁)).measurableSet
  linear_combination (-(q e : ℝ) * (1 - (q e : ℝ))) * hUV

/-- Both terms of `prodBernoulli_real_split_sub` are nonnegative. -/
theorem split_terms_nonneg (p : unitInterval) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (p : ℝ) ^ 2 * x ∧ 0 ≤ (p : ℝ) * (1 - (p : ℝ)) * y :=
  ⟨by positivity, mul_nonneg (mul_nonneg p.2.1 (sub_nonneg.2 p.2.2)) hy⟩

/-- The second term of `prodBernoulli_real_split_sub` vanishes exactly when `p ∈ {0, 1}` or
`μ(V \ C₀₀) = 0`. -/
theorem split_second_term_eq_zero_iff (p : unitInterval) (y : ℝ) :
    (p : ℝ) * (1 - (p : ℝ)) * y = 0 ↔ (p : ℝ) = 0 ∨ (p : ℝ) = 1 ∨ y = 0 := by
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

/-! ### Non-vacuity -/

/-- **Non-vacuity witness for `prodBernoulli_real_split_sub`, `I = {e}`, `A = B = {e open}`.** Here
`P(H) = 0`, `C₁₁` is everything and `U = V = ∅`, so the theorem gives `P(H̃) = p²`. -/
theorem prodBernoulli_real_split_unit (q : Unit → unitInterval) :
    (prodBernoulli (Sum.elim q fun _ : Unit => q ())).real
        (disjointOccurrence {ω : Set (Unit ⊕ Unit) | Sum.inl ⁻¹' ω ∈ {ω : Set Unit | () ∈ ω}}
          {ω : Set (Unit ⊕ Unit) | {i | (i ≠ () ∧ Sum.inl i ∈ ω) ∨ (i = () ∧ Sum.inr () ∈ ω)} ∈
            {ω : Set Unit | () ∈ ω}}) = (q () : ℝ) ^ 2 := by
  have hup : IsUpperSet {ω : Set Unit | () ∈ ω} := fun _ _ h hω => h hω
  have h := prodBernoulli_real_split_sub (e := ()) q hup hup
  have hH : disjointOccurrence {ω : Set Unit | () ∈ ω} {ω : Set Unit | () ∈ ω} = ∅ :=
    disjointOccurrence_mem_self ()
  have h0 : {η : Set ({()}ᶜ : Set Unit) | Subtype.val '' η ∈ {ω : Set Unit | () ∈ ω}} = ∅ :=
    eq_empty_of_forall_notMem fun η hη => notMem_image_val_compl η hη
  have h1 : {η : Set ({()}ᶜ : Set Unit) | insert () (Subtype.val '' η) ∈
      {ω : Set Unit | () ∈ ω}} = univ :=
    eq_univ_of_forall fun η => mem_insert () _
  have hC0 : ∀ X : Set (Set ({()}ᶜ : Set Unit)), disjointOccurrence ∅ X = ∅ := fun X =>
    subset_empty_iff.1 ((disjointOccurrence_subset_inter _ _).trans (by simp))
  have hC0' : ∀ X : Set (Set ({()}ᶜ : Set Unit)), disjointOccurrence X ∅ = ∅ := fun X =>
    subset_empty_iff.1 ((disjointOccurrence_subset_inter _ _).trans (by simp))
  rw [hH, h0, h1, disjointOccurrence_univ, hC0, hC0'] at h
  simpa only [measureReal_empty, sub_zero, union_empty, sdiff_empty, inter_empty,
    empty_sdiff, mul_zero, add_zero, probReal_univ, mul_one] using h

/-- **Non-vacuity witness for `prodBernoulli_real_split_sub`, `A = B = univ`.** The hypotheses hold
for every finite `I`, and then both sides vanish. -/
theorem prodBernoulli_real_split_sub_univ (q : I → unitInterval) (e : I) :
    (prodBernoulli (Sum.elim q fun _ : Unit => q e)).real
        (disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ (univ : Set (Set I))}
          {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈
            (univ : Set (Set I))}) -
      (prodBernoulli q).real (disjointOccurrence (univ : Set (Set I)) univ) = 0 := by
  rw [prodBernoulli_real_split_sub q isUpperSet_univ isUpperSet_univ]
  simp [disjointOccurrence_univ]

end Measure

end PercLib.Probability
