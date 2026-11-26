/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Positivity, monotonicity and scaling of the recursive three-part distance `S(A)` (wiki tag Y4H4,
article `multipoint-trees`; T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
§I.2). New proofs; no upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Multipoint.Defs

/-! # The three-part distance: positivity, monotonicity and scaling

For a finite set `A` in a metric space, `threePartDistance A` is `diam(A)²` for `|A| ≤ 2` and,
for `|A| ≥ 3`, the minimum over partitions `A = A₁ ⊔ A₂ ⊔ A₃` into nonempty parts of
`√(S(A₁ ∪ A₂) S(A₂ ∪ A₃) S(A₃ ∪ A₁))`.

* `threePartDistance_le_of_partition`, `exists_threePartDistance_eq`: the minimum is a
  minimum (attained);
* `threePartDistance_nonneg`, `threePartDistance_pos` (item 1);
* `pow_card_mul_threePartDistance_le_image` (item 2 with a factor): if `f` is injective on `A`
  and `c d(x, y) ≤ d(f x, f y)` on `A`, then `c^|A| S(A) ≤ S(f A)`; `c = 1` is item 2;
* `threePartDistance_image_smul` (item 3): `S(c • A) = c^|A| S(A)` for `c > 0` in a normed
  space.
-/

@[expose] public section
noncomputable section

open Finset

namespace PercLib.Percolation.Bond

variable {X : Type*} [MetricSpace X] [DecidableEq X]

omit [MetricSpace X] in
/-- The partitions used in the recursion. -/
theorem mem_partitions_iff {A p₁ p₂ : Finset X} :
    (p₁, p₂) ∈ ((A.powerset ×ˢ A.powerset).filter fun p : Finset X × Finset X =>
      Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ (A \ (p.1 ∪ p.2)).Nonempty) ↔
      p₁ ⊆ A ∧ p₂ ⊆ A ∧ Disjoint p₁ p₂ ∧ p₁.Nonempty ∧ p₂.Nonempty ∧
        (A \ (p₁ ∪ p₂)).Nonempty := by
  simp only [mem_filter, mem_product, mem_powerset, and_assoc]

/-- For `|A| ≥ 3`, `S(A)` is at most the value of every admissible partition. -/
theorem threePartDistance_le_of_partition {A p₁ p₂ : Finset X} (hA : 3 ≤ A.card)
    (h₁ : p₁ ⊆ A) (h₂ : p₂ ⊆ A) (hd : Disjoint p₁ p₂) (hn₁ : p₁.Nonempty) (hn₂ : p₂.Nonempty)
    (hn₃ : (A \ (p₁ ∪ p₂)).Nonempty) :
    threePartDistance A ≤ Real.sqrt (threePartDistance (p₁ ∪ p₂) *
      threePartDistance (p₂ ∪ (A \ (p₁ ∪ p₂))) * threePartDistance ((A \ (p₁ ∪ p₂)) ∪ p₁)) := by
  have hmem := mem_partitions_iff.2 ⟨h₁, h₂, hd, hn₁, hn₂, hn₃⟩
  rw [threePartDistance]
  split_ifs with h2 h3
  · omega
  · exact Finset.inf'_le _ (Finset.mem_attach _ ⟨_, hmem⟩)
  · exact absurd ⟨_, hmem⟩ h3

/-- For `|A| ≥ 3` the minimum is attained at an admissible partition. -/
theorem exists_threePartDistance_eq {A : Finset X} (hA : 3 ≤ A.card) :
    ∃ p₁ p₂ : Finset X, p₁ ⊆ A ∧ p₂ ⊆ A ∧ Disjoint p₁ p₂ ∧ p₁.Nonempty ∧ p₂.Nonempty ∧
      (A \ (p₁ ∪ p₂)).Nonempty ∧
      threePartDistance A = Real.sqrt (threePartDistance (p₁ ∪ p₂) *
        threePartDistance (p₂ ∪ (A \ (p₁ ∪ p₂))) *
          threePartDistance ((A \ (p₁ ∪ p₂)) ∪ p₁)) := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < A.card)
  have hmem := mem_partitions_iff (A := A) (p₁ := {a}) (p₂ := {b}) |>.2
    ⟨by simpa using ha, by simpa using hb, by simpa using hab, singleton_nonempty a,
      singleton_nonempty b, ⟨c, by simp [hc, Ne.symm hac, Ne.symm hbc]⟩⟩
  have hne : ((A.powerset ×ˢ A.powerset).filter fun p : Finset X × Finset X =>
      Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ (A \ (p.1 ∪ p.2)).Nonempty).Nonempty :=
    ⟨_, hmem⟩
  obtain ⟨⟨p, hp⟩, -, heq⟩ := Finset.exists_mem_eq_inf' (Finset.attach_nonempty_iff.2 hne)
    (fun p : {x // x ∈ ((A.powerset ×ˢ A.powerset).filter fun p : Finset X × Finset X =>
      Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ (A \ (p.1 ∪ p.2)).Nonempty)} =>
        Real.sqrt (threePartDistance (p.1.1 ∪ p.1.2) *
          threePartDistance (p.1.2 ∪ (A \ (p.1.1 ∪ p.1.2))) *
          threePartDistance ((A \ (p.1.1 ∪ p.1.2)) ∪ p.1.1)))
  obtain ⟨h₁, h₂, hd, hn₁, hn₂, hn₃⟩ := mem_partitions_iff.1 hp
  refine ⟨p.1, p.2, h₁, h₂, hd, hn₁, hn₂, hn₃, ?_⟩
  rw [threePartDistance]
  split_ifs with h2
  · omega
  · exact heq

/-- `S(A) ≥ 0`. -/
theorem threePartDistance_nonneg (A : Finset X) : 0 ≤ threePartDistance A := by
  rw [threePartDistance]
  split_ifs with h1 h2
  · positivity
  · exact Finset.le_inf' _ _ fun _ _ => Real.sqrt_nonneg _
  · exact le_rfl

omit [MetricSpace X] in
/-- The three parts' unions have total size `2 |A|`, and each is a proper subset of `A`. -/
theorem card_partition_unions {A p₁ p₂ : Finset X} (h₁ : p₁ ⊆ A) (h₂ : p₂ ⊆ A)
    (hd : Disjoint p₁ p₂) :
    (p₁ ∪ p₂).card + (p₂ ∪ (A \ (p₁ ∪ p₂))).card + ((A \ (p₁ ∪ p₂)) ∪ p₁).card =
      2 * A.card := by
  have hu : p₁ ∪ p₂ ⊆ A := union_subset h₁ h₂
  have h3 := card_sdiff_add_card_eq_card hu
  have hd2 : Disjoint p₂ (A \ (p₁ ∪ p₂)) :=
    disjoint_sdiff.mono_left subset_union_right
  have hd3 : Disjoint (A \ (p₁ ∪ p₂)) p₁ :=
    (disjoint_sdiff.mono_left subset_union_left).symm
  rw [card_union_of_disjoint hd, card_union_of_disjoint hd2, card_union_of_disjoint hd3]
  rw [card_union_of_disjoint hd] at h3
  omega

omit [MetricSpace X] in
theorem card_union_lt {A p₁ p₂ : Finset X} (h₁ : p₁ ⊆ A) (h₂ : p₂ ⊆ A)
    (hn₃ : (A \ (p₁ ∪ p₂)).Nonempty) : (p₁ ∪ p₂).card < A.card := by
  obtain ⟨c, hc⟩ := hn₃
  exact card_lt_card ((ssubset_iff_of_subset (union_subset h₁ h₂)).2
    ⟨c, (mem_sdiff.1 hc).1, (mem_sdiff.1 hc).2⟩)

omit [MetricSpace X] in
/-- The sizes of the three unions in terms of the parts. -/
theorem card_partition_parts {A p₁ p₂ : Finset X} (h₁ : p₁ ⊆ A) (h₂ : p₂ ⊆ A)
    (hd : Disjoint p₁ p₂) :
    (p₁ ∪ p₂).card = p₁.card + p₂.card ∧
      (p₂ ∪ (A \ (p₁ ∪ p₂))).card = p₂.card + (A \ (p₁ ∪ p₂)).card ∧
      ((A \ (p₁ ∪ p₂)) ∪ p₁).card = (A \ (p₁ ∪ p₂)).card + p₁.card ∧
      A.card = p₁.card + p₂.card + (A \ (p₁ ∪ p₂)).card := by
  have hd2 : Disjoint p₂ (A \ (p₁ ∪ p₂)) := disjoint_sdiff.mono_left subset_union_right
  have hd3 : Disjoint (A \ (p₁ ∪ p₂)) p₁ := (disjoint_sdiff.mono_left subset_union_left).symm
  have h3 := card_sdiff_add_card_eq_card (union_subset h₁ h₂)
  rw [card_union_of_disjoint hd] at h3
  refine ⟨card_union_of_disjoint hd, card_union_of_disjoint hd2, card_union_of_disjoint hd3, ?_⟩
  omega

/-- **Item 1.** `S(A) > 0` when `|A| ≥ 2`. -/
theorem threePartDistance_pos : ∀ (A : Finset X), 2 ≤ A.card → 0 < threePartDistance A := by
  intro A
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  intro h2
  by_cases h3 : 3 ≤ n
  · obtain ⟨p₁, p₂, h₁, h₂, hd, hn₁, hn₂, hn₃, heq⟩ := exists_threePartDistance_eq (hn ▸ h3)
    rw [heq]
    have hd2 : Disjoint p₂ (A \ (p₁ ∪ p₂)) := disjoint_sdiff.mono_left subset_union_right
    have hd3 : Disjoint (A \ (p₁ ∪ p₂)) p₁ := (disjoint_sdiff.mono_left subset_union_left).symm
    have two : ∀ {s t : Finset X}, Disjoint s t → s.Nonempty → t.Nonempty → 2 ≤ (s ∪ t).card :=
      fun hst hs ht => by
        rw [card_union_of_disjoint hst]
        have := hs.card_pos; have := ht.card_pos; omega
    have hu₁ := card_union_lt h₁ h₂ hn₃
    obtain ⟨c₁, c₂, c₃, cA⟩ := card_partition_parts h₁ h₂ hd
    have := hn₁.card_pos; have := hn₂.card_pos; have := hn₃.card_pos
    have hu₂ : (p₂ ∪ (A \ (p₁ ∪ p₂))).card < A.card := by omega
    have hu₃ : ((A \ (p₁ ∪ p₂)) ∪ p₁).card < A.card := by omega
    refine Real.sqrt_pos.2 (mul_pos (mul_pos ?_ ?_) ?_)
    · exact ih _ (hn ▸ hu₁) _ rfl (two hd hn₁ hn₂)
    · exact ih _ (hn ▸ hu₂) _ rfl (two hd2 hn₂ hn₃)
    · exact ih _ (hn ▸ hu₃) _ rfl (two hd3 hn₃ hn₁)
  · have h2' : A.card = 2 := by omega
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 h2'
    rw [threePartDistance_pair]
    exact pow_pos (dist_pos.2 hxy) 2

/-! ### Comparison under maps -/

section Image

variable {Y : Type*} [MetricSpace Y] [DecidableEq Y]

/-- For `|A| ≤ 2`, `c^|A| diam(A)² ≤ diam(f A)²` when `c d ≤ d ∘ f` on `A`. -/
theorem pow_card_mul_diam_sq_le_image {f : X → Y} {c : ℝ} (hc : 0 ≤ c) {A : Finset X}
    (hA : A.card ≤ 2) (hf : ∀ x ∈ A, ∀ y ∈ A, c * dist x y ≤ dist (f x) (f y)) :
    c ^ A.card * Metric.diam (A : Set X) ^ 2 ≤ Metric.diam
        ((A.image f : Finset Y) : Set Y) ^ 2 := by
  rcases Nat.lt_or_ge A.card 2 with h | h
  · have hs : (A : Set X).Subsingleton := fun x hx y hy =>
      Finset.card_le_one.1 (by omega) x hx y hy
    rw [Metric.diam_subsingleton hs]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 (le_antisymm hA h)
    rw [card_pair hxy, image_insert, image_singleton]
    simp only [coe_insert, coe_singleton, Metric.diam_pair]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc dist_nonneg)
      (hf x (by simp) y (by simp)) 2

/-- **Item 2 with a factor.** If `f` is injective on `A` and `c d(x, y) ≤ d(f x, f y)` on `A`
with `c ≥ 0`, then `c^|A| S(A) ≤ S(f A)`. -/
theorem pow_card_mul_threePartDistance_le_image {f : X → Y} {c : ℝ} (hc : 0 ≤ c) :
    ∀ (A : Finset X), Set.InjOn f A → (∀ x ∈ A, ∀ y ∈ A, c * dist x y ≤ dist (f x) (f y)) →
      c ^ A.card * threePartDistance A ≤ threePartDistance (A.image f) := by
  intro A
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  intro hinj hf
  have hcard : (A.image f).card = A.card := card_image_of_injOn hinj
  by_cases h3 : 3 ≤ n
  · obtain ⟨q₁, q₂, h₁, h₂, hd, hn₁, hn₂, hn₃, heq⟩ :=
      exists_threePartDistance_eq (A := A.image f) (by omega)
    set p₁ := A.filter fun x => f x ∈ q₁
    set p₂ := A.filter fun x => f x ∈ q₂
    have himg : ∀ {q : Finset Y}, q ⊆ A.image f → (A.filter fun x => f x ∈ q).image f = q :=
      fun {q} hq => by
        ext y
        simp only [mem_image, mem_filter]
        constructor
        · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
        · intro hy
          obtain ⟨x, hx, rfl⟩ := mem_image.1 (hq hy)
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
    have hp₁ : p₁ ⊆ A := filter_subset _ _
    have hp₂ : p₂ ⊆ A := filter_subset _ _
    have hi₁ : p₁.image f = q₁ := himg h₁
    have hi₂ : p₂.image f = q₂ := himg h₂
    have hpd : Disjoint p₁ p₂ := by
      rw [disjoint_left]
      intro x hx₁ hx₂
      exact disjoint_left.1 hd (mem_filter.1 hx₁).2 (mem_filter.1 hx₂).2
    have hi₃ : (A \ (p₁ ∪ p₂)).image f = A.image f \ (q₁ ∪ q₂) := by
      rw [image_sdiff_of_injOn hinj (union_subset hp₁ hp₂), image_union, hi₁, hi₂]
    have hpn₁ : p₁.Nonempty := Finset.Nonempty.of_image (f := f) (by rw [hi₁]; exact hn₁)
    have hpn₂ : p₂.Nonempty := Finset.Nonempty.of_image (f := f) (by rw [hi₂]; exact hn₂)
    have hpn₃ : (A \ (p₁ ∪ p₂)).Nonempty :=
      Finset.Nonempty.of_image (f := f) (by rw [hi₃]; exact hn₃)
    obtain ⟨c₁, c₂, c₃, cA⟩ := card_partition_parts hp₁ hp₂ hpd
    have := hpn₁.card_pos; have := hpn₂.card_pos; have := hpn₃.card_pos
    set p₃ := A \ (p₁ ∪ p₂)
    have hsub : ∀ {s : Finset X}, s ⊆ A → Set.InjOn f s := fun hs => hinj.mono (by
      exact_mod_cast hs)
    have hfs : ∀ {s : Finset X}, s ⊆ A → ∀ x ∈ s, ∀ y ∈ s, c * dist x y ≤ dist (f x) (f y) :=
      fun hs x hx y hy => hf x (hs hx) y (hs hy)
    have hU₁ : p₁ ∪ p₂ ⊆ A := union_subset hp₁ hp₂
    have hU₂ : p₂ ∪ p₃ ⊆ A := union_subset hp₂ sdiff_subset
    have hU₃ : p₃ ∪ p₁ ⊆ A := union_subset sdiff_subset hp₁
    have hd2 : Disjoint p₂ p₃ := disjoint_sdiff.mono_left subset_union_right
    have hd3 : Disjoint p₃ p₁ := (disjoint_sdiff.mono_left subset_union_left).symm
    have hcards := card_partition_unions hp₁ hp₂ hpd
    have two : ∀ {s t : Finset X}, Disjoint s t → s.Nonempty → t.Nonempty → 1 ≤ t.card →
        (s ∪ t).card < s.card + t.card + 1 := fun hst _ _ _ => by
      rw [card_union_of_disjoint hst]; omega
    have hlt₁ : (p₁ ∪ p₂).card < n := hn ▸ card_union_lt hp₁ hp₂ hpn₃
    have hlt₂ : (p₂ ∪ p₃).card < n := by omega
    have hlt₃ : (p₃ ∪ p₁).card < n := by omega
    have e₁ := ih _ hlt₁ _ rfl (hsub hU₁) (hfs hU₁)
    have e₂ := ih _ hlt₂ _ rfl (hsub hU₂) (hfs hU₂)
    have e₃ := ih _ hlt₃ _ rfl (hsub hU₃) (hfs hU₃)
    rw [image_union, hi₁, hi₂] at e₁
    rw [image_union, hi₂, hi₃] at e₂
    rw [image_union, hi₃, hi₁] at e₃
    rw [heq]
    have hle := threePartDistance_le_of_partition (A := A) (by omega) hp₁ hp₂ hpd hpn₁ hpn₂ hpn₃
    have hsq : Real.sqrt (c ^ (2 * n)) = c ^ n := by
      rw [pow_mul', Real.sqrt_sq (pow_nonneg hc n)]
    calc c ^ n * threePartDistance A
        ≤ c ^ n * Real.sqrt (threePartDistance (p₁ ∪ p₂) * threePartDistance (p₂ ∪ p₃) *
            threePartDistance (p₃ ∪ p₁)) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg hc n)
      _ = Real.sqrt (c ^ (p₁ ∪ p₂).card * threePartDistance (p₁ ∪ p₂) *
            (c ^ (p₂ ∪ p₃).card * threePartDistance (p₂ ∪ p₃)) *
            (c ^ (p₃ ∪ p₁).card * threePartDistance (p₃ ∪ p₁))) := by
          rw [← hsq, ← Real.sqrt_mul (pow_nonneg hc _), ← hn, ← hcards, pow_add, pow_add]
          congr 1
          ring
      _ ≤ _ := by
          refine Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul e₁ e₂ ?_ ?_) e₃ ?_ ?_)
          · exact mul_nonneg (pow_nonneg hc _) (threePartDistance_nonneg _)
          · exact threePartDistance_nonneg _
          · exact mul_nonneg (pow_nonneg hc _) (threePartDistance_nonneg _)
          · exact mul_nonneg (threePartDistance_nonneg _) (threePartDistance_nonneg _)
  · have h2 : A.card ≤ 2 := by omega
    have h2' : (A.image f).card ≤ 2 := hcard ▸ h2
    rw [threePartDistance, threePartDistance]
    simp only [h2, h2', ite_true]
    rw [← hn]
    exact pow_card_mul_diam_sq_le_image hc h2 hf

/-- **Item 2.** An expanding map injective on `A` does not decrease `S`. -/
theorem threePartDistance_le_image {f : X → Y} {A : Finset X} (hinj : Set.InjOn f A)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist (f x) (f y)) :
    threePartDistance A ≤ threePartDistance (A.image f) := by
  simpa using pow_card_mul_threePartDistance_le_image (f := f) zero_le_one A hinj
    fun x hx y hy => by rw [one_mul]; exact hf x hx y hy

end Image

/-- **Item 3.** In a normed space, `S(c • A) = c^|A| S(A)` for `c > 0`. -/
theorem threePartDistance_image_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] {c : ℝ} (hc : 0 < c) (A : Finset E) :
    threePartDistance (A.image (c • ·)) = c ^ A.card * threePartDistance A := by
  have hinj : ∀ (B : Finset E) (a : ℝ), a ≠ 0 → Set.InjOn (a • · : E → E) B :=
    fun _ a ha x _ y _ h => smul_right_injective E ha h
  have hd : ∀ (a : ℝ), 0 < a → ∀ x y : E, a * dist x y ≤ dist (a • x) (a • y) := fun a ha x y => by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ha]
  refine le_antisymm ?_ (pow_card_mul_threePartDistance_le_image hc.le A (hinj A c hc.ne')
    fun x _ y _ => hd c hc x y)
  have h := pow_card_mul_threePartDistance_le_image (inv_pos.2 hc).le (A.image (c • ·))
    (hinj _ _ (inv_ne_zero hc.ne')) fun x _ y _ => hd _ (inv_pos.2 hc) x y
  rw [image_image, card_image_of_injOn (hinj A c hc.ne')] at h
  have hid : ((c⁻¹ • ·) ∘ (c • ·) : E → E) = id := by
    funext x; simp [smul_smul, inv_mul_cancel₀ hc.ne']
  rw [hid, image_id] at h
  have hpos : 0 < c ^ A.card := pow_pos hc _
  rw [inv_pow] at h
  calc threePartDistance (A.image (c • ·))
      = c ^ A.card * ((c ^ A.card)⁻¹ * threePartDistance (A.image (c • ·))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ c ^ A.card * threePartDistance A := mul_le_mul_of_nonneg_left h hpos.le

/-! ### Witnesses -/

/-- `A = {0, 1, 3} ⊆ ℝ`: `S(A) > 0`, and `S(2 • A) = 8 S(A)`. -/
example : 0 < threePartDistance ({0, 1, 3} : Finset ℝ) :=
  threePartDistance_pos _ (by
    rw [card_insert_of_notMem (by norm_num), card_pair (by norm_num)]; norm_num)

example : threePartDistance (({0, 1, 3} : Finset ℝ).image ((2 : ℝ) • ·)) =
    2 ^ 3 * threePartDistance ({0, 1, 3} : Finset ℝ) := by
  rw [threePartDistance_image_smul two_pos, card_insert_of_notMem (by norm_num),
    card_pair (by norm_num)]

/-! ### Covariance -/

section Covariance

variable {Y : Type*} [MetricSpace Y] [DecidableEq Y]

omit [MetricSpace X] in
/-- The three pairwise unions of a partition cover each point twice, so the products of a
weight over them multiply to the square of the product over `A`. -/
theorem prod_partition_unions_eq_sq {M : Type*} [CommMonoid M] (l : X → M) {A p₁ p₂ : Finset X}
    (h₁ : p₁ ⊆ A) (h₂ : p₂ ⊆ A) (hd : Disjoint p₁ p₂) :
    (∏ x ∈ p₁ ∪ p₂, l x) * (∏ x ∈ p₂ ∪ (A \ (p₁ ∪ p₂)), l x) *
        (∏ x ∈ (A \ (p₁ ∪ p₂)) ∪ p₁, l x) = (∏ x ∈ A, l x) ^ 2 := by
  have hd2 : Disjoint p₂ (A \ (p₁ ∪ p₂)) := disjoint_sdiff.mono_left subset_union_right
  have hd3 : Disjoint (A \ (p₁ ∪ p₂)) p₁ := (disjoint_sdiff.mono_left subset_union_left).symm
  have hA := prod_sdiff (f := l) (union_subset h₁ h₂)
  rw [prod_union hd, prod_union hd2, prod_union hd3, ← hA, prod_union hd, sq]
  ac_rfl

/-- **Covariance, one inequality.** If `f` is injective on `A`, `l ≥ 0` on `A` and
`l x l y d(x, y)² ≤ d(f x, f y)²` on `A`, then `(∏_{x ∈ A} l x) S(A) ≤ S(f A)`. -/
theorem prod_mul_threePartDistance_le_image {f : X → Y} {l : X → ℝ} :
    ∀ (A : Finset X), (∀ x ∈ A, 0 ≤ l x) → Set.InjOn f A →
      (∀ x ∈ A, ∀ y ∈ A, l x * l y * dist x y ^ 2 ≤ dist (f x) (f y) ^ 2) →
      (∏ x ∈ A, l x) * threePartDistance A ≤ threePartDistance (A.image f) := by
  intro A
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  intro hl hinj hf
  have hcard : (A.image f).card = A.card := card_image_of_injOn hinj
  by_cases h3 : 3 ≤ n
  · obtain ⟨q₁, q₂, h₁, h₂, hd, hn₁, hn₂, hn₃, heq⟩ :=
      exists_threePartDistance_eq (A := A.image f) (by omega)
    set p₁ := A.filter fun x => f x ∈ q₁
    set p₂ := A.filter fun x => f x ∈ q₂
    have himg : ∀ {q : Finset Y}, q ⊆ A.image f → (A.filter fun x => f x ∈ q).image f = q :=
      fun {q} hq => by
        ext y
        simp only [mem_image, mem_filter]
        constructor
        · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
        · intro hy
          obtain ⟨x, hx, rfl⟩ := mem_image.1 (hq hy)
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
    have hp₁ : p₁ ⊆ A := filter_subset _ _
    have hp₂ : p₂ ⊆ A := filter_subset _ _
    have hi₁ : p₁.image f = q₁ := himg h₁
    have hi₂ : p₂.image f = q₂ := himg h₂
    have hpd : Disjoint p₁ p₂ := by
      rw [disjoint_left]
      intro x hx₁ hx₂
      exact disjoint_left.1 hd (mem_filter.1 hx₁).2 (mem_filter.1 hx₂).2
    have hi₃ : (A \ (p₁ ∪ p₂)).image f = A.image f \ (q₁ ∪ q₂) := by
      rw [image_sdiff_of_injOn hinj (union_subset hp₁ hp₂), image_union, hi₁, hi₂]
    have hpn₁ : p₁.Nonempty := Finset.Nonempty.of_image (f := f) (by rw [hi₁]; exact hn₁)
    have hpn₂ : p₂.Nonempty := Finset.Nonempty.of_image (f := f) (by rw [hi₂]; exact hn₂)
    have hpn₃ : (A \ (p₁ ∪ p₂)).Nonempty :=
      Finset.Nonempty.of_image (f := f) (by rw [hi₃]; exact hn₃)
    obtain ⟨c₁, c₂, c₃, cA⟩ := card_partition_parts hp₁ hp₂ hpd
    have := hpn₁.card_pos; have := hpn₂.card_pos; have := hpn₃.card_pos
    have hprod := prod_partition_unions_eq_sq l hp₁ hp₂ hpd
    set p₃ := A \ (p₁ ∪ p₂)
    have hU₁ : p₁ ∪ p₂ ⊆ A := union_subset hp₁ hp₂
    have hU₂ : p₂ ∪ p₃ ⊆ A := union_subset hp₂ sdiff_subset
    have hU₃ : p₃ ∪ p₁ ⊆ A := union_subset sdiff_subset hp₁
    have hlt₁ : (p₁ ∪ p₂).card < n := hn ▸ card_union_lt hp₁ hp₂ hpn₃
    have hlt₂ : (p₂ ∪ p₃).card < n := by omega
    have hlt₃ : (p₃ ∪ p₁).card < n := by omega
    have hsub : ∀ {s : Finset X}, s ⊆ A → (∀ x ∈ s, 0 ≤ l x) ∧ Set.InjOn f s ∧
        ∀ x ∈ s, ∀ y ∈ s, l x * l y * dist x y ^ 2 ≤ dist (f x) (f y) ^ 2 :=
      fun hs => ⟨fun x hx => hl x (hs hx), hinj.mono (by exact_mod_cast hs),
        fun x hx y hy => hf x (hs hx) y (hs hy)⟩
    have e₁ := ih _ hlt₁ _ rfl (hsub hU₁).1 (hsub hU₁).2.1 (hsub hU₁).2.2
    have e₂ := ih _ hlt₂ _ rfl (hsub hU₂).1 (hsub hU₂).2.1 (hsub hU₂).2.2
    have e₃ := ih _ hlt₃ _ rfl (hsub hU₃).1 (hsub hU₃).2.1 (hsub hU₃).2.2
    rw [image_union, hi₁, hi₂] at e₁
    rw [image_union, hi₂, hi₃] at e₂
    rw [image_union, hi₃, hi₁] at e₃
    rw [heq]
    have hle := threePartDistance_le_of_partition (A := A) (by omega) hp₁ hp₂ hpd hpn₁ hpn₂ hpn₃
    have hP : 0 ≤ ∏ x ∈ A, l x := prod_nonneg hl
    have hPs : ∀ {s : Finset X}, s ⊆ A → 0 ≤ ∏ x ∈ s, l x := fun hs =>
      prod_nonneg (hsub hs).1
    calc (∏ x ∈ A, l x) * threePartDistance A
        ≤ (∏ x ∈ A, l x) * Real.sqrt (threePartDistance (p₁ ∪ p₂) *
            threePartDistance (p₂ ∪ p₃) * threePartDistance (p₃ ∪ p₁)) :=
          mul_le_mul_of_nonneg_left hle hP
      _ = Real.sqrt ((∏ x ∈ p₁ ∪ p₂, l x) * threePartDistance (p₁ ∪ p₂) *
            ((∏ x ∈ p₂ ∪ p₃, l x) * threePartDistance (p₂ ∪ p₃)) *
            ((∏ x ∈ p₃ ∪ p₁, l x) * threePartDistance (p₃ ∪ p₁))) := by
          rw [← Real.sqrt_sq hP, ← hprod,
            ← Real.sqrt_mul (mul_nonneg (mul_nonneg (hPs hU₁) (hPs hU₂)) (hPs hU₃))]
          congr 1
          ring
      _ ≤ _ := by
          refine Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul e₁ e₂ ?_ ?_) e₃ ?_ ?_)
          · exact mul_nonneg (hPs hU₂) (threePartDistance_nonneg _)
          · exact threePartDistance_nonneg _
          · exact mul_nonneg (hPs hU₃) (threePartDistance_nonneg _)
          · exact mul_nonneg (threePartDistance_nonneg _) (threePartDistance_nonneg _)
  · have h2 : A.card ≤ 2 := by omega
    have h2' : (A.image f).card ≤ 2 := hcard ▸ h2
    rw [threePartDistance, threePartDistance]
    simp only [h2, h2', ite_true]
    rcases Nat.lt_or_ge A.card 2 with h | h
    · have hs : (A : Set X).Subsingleton := fun x hx y hy =>
        Finset.card_le_one.1 (by omega) x hx y hy
      rw [Metric.diam_subsingleton hs]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 (le_antisymm h2 h)
      rw [prod_pair hxy, image_insert, image_singleton]
      simp only [coe_insert, coe_singleton, Metric.diam_pair]
      exact hf x (by simp) y (by simp)

/-- **Covariance.** If `f` is injective on `A`, `l > 0` on `A` and
`d(f x, f y)² = l x l y d(x, y)²` on `A`, then `S(f A) = S(A) ∏_{x ∈ A} l x`. -/
theorem threePartDistance_image_eq_mul_prod {f : X → Y} {l : X → ℝ} {A : Finset X}
    (hl : ∀ x ∈ A, 0 < l x) (hinj : Set.InjOn f A)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ^ 2 = l x * l y * dist x y ^ 2) :
    threePartDistance (A.image f) = threePartDistance A * ∏ x ∈ A, l x := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · rw [image_empty, prod_empty, mul_one, threePartDistance, threePartDistance]
    simp
  have : Nonempty X := ⟨a⟩
  have hP : 0 < ∏ x ∈ A, l x := prod_pos hl
  have hle := prod_mul_threePartDistance_le_image A (fun x hx => (hl x hx).le) hinj
    fun x hx y hy => (hf x hx y hy).ge
  set g := Function.invFunOn f A
  have hgf : ∀ x ∈ A, g (f x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  have hrev := prod_mul_threePartDistance_le_image (f := g) (l := fun y => (l (g y))⁻¹)
    (A.image f)
    (by
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro x hx
      rw [hgf x hx]
      exact (inv_pos.2 (hl x hx)).le)
    (by
      simp only [Set.InjOn, coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro x hx y hy hxy
      rw [hgf x hx, hgf y hy] at hxy
      rw [hxy])
    (by
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro x hx y hy
      rw [hgf x hx, hgf y hy, hf x hx y hy]
      have := (hl x hx).ne'
      have := (hl y hy).ne'
      field_simp
      rfl)
  rw [prod_image hinj, image_image, prod_congr rfl fun x hx => by rw [hgf x hx],
    prod_inv_distrib] at hrev
  have himg : A.image (g ∘ f) = A := by
    rw [show A.image (g ∘ f) = A.image id from image_congr fun x hx => hgf x hx, image_id]
  rw [himg] at hrev
  have hrev' : threePartDistance (A.image f) ≤ threePartDistance A * ∏ x ∈ A, l x := by
    rw [inv_mul_le_iff₀ hP] at hrev
    linarith
  linarith

/-- If `d(f x, f y) = c d(x, y)` on `A` with `c > 0`, then `S(f A) = c^|A| S(A)`. -/
theorem threePartDistance_image_of_dist_eq_mul {f : X → Y} {c : ℝ} (hc : 0 < c)
    {A : Finset X} (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = c * dist x y) :
    threePartDistance (A.image f) = c ^ A.card * threePartDistance A := by
  have hinj : Set.InjOn f A := fun x hx y hy hxy => by
    have h := hf x hx y hy
    rw [hxy, dist_self] at h
    exact dist_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left hc.ne')
  rw [threePartDistance_image_eq_mul_prod (l := fun _ => c) (fun _ _ => hc) hinj
    fun x hx y hy => by rw [hf x hx y hy]; ring, prod_const, mul_comm]

/-- **Similarities.** In a real normed space, `S(c U A + v) = c^|A| S(A)` for `c > 0`, a linear
isometry `U` and a translation `v`. -/
theorem threePartDistance_image_smul_linearIsometry_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] {c : ℝ} (hc : 0 < c) (U : E →ₗᵢ[ℝ] E) (v : E)
    (A : Finset E) :
    threePartDistance (A.image fun x => c • U x + v) = c ^ A.card * threePartDistance A :=
  threePartDistance_image_of_dist_eq_mul hc fun x _ y _ => by
    rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hc, U.dist_map]

end Covariance

end PercLib.Percolation.Bond
