/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on this library's bond-percolation interface and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied.
Mathematical reference: T. Hutchcroft, *Sharp hierarchical upper bounds on the critical
two-point function for long-range percolation on ℤ^d*, arXiv:2202.07634v2, Section 2
(selection of a good hierarchy, Proposition 2.2 and Lemma 2.3).
-/
module

public import PercLib.Models.HierarchicalComparison
public import PercLib.Percolation.Bond.ThresholdConvergence
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.Embedding
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Percolation.Bond.IntensityMonotone
public import PercLib.Percolation.Bond.Tightness.Hyperscaling

/-!
# Choosing a good digit hierarchy

Every block has at least half of its children good, by ordering the expected maxima. The block
quantities `E Z_B` and `S_B` depend continuously on the digits at subcritical intensity: all
restricted models are coupled below the full model, whose clusters are almost surely finite,
and the restricted kernel of each pair converges. Choosing good children downwards from a
high level, translating to the origin and passing to a limit of digits gives a hierarchy in
which every block containing the origin is good.

## Main results

* `PercLib.Models.card_le_two_mul_card_filter_le_and_exists_le`: the counting argument.
* `PercLib.Models.DigitHierarchy.card_le_two_mul_card_image_filter_isGoodBlock`: at least half
  of the children of every block are good.
* `PercLib.Models.DigitHierarchy.tendsto_expectedBlockMax`,
  `PercLib.Models.DigitHierarchy.tendsto_blockPairSum`: continuity in the digits.
* `PercLib.Models.DigitHierarchy.isGoodBlock_of_tendsto`: goodness is a closed condition.
* `PercLib.Models.DigitHierarchy.isGoodBlock_translate_add`: goodness is translation covariant.
* `PercLib.Models.DigitHierarchy.exists_isAncestrallyGood_zero`: a hierarchy in which the
  origin is ancestrally good.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V W : Type*}

/-- The largest intersection is carried along a vertex bijection. -/
theorem maxClusterIntersection_map_image (e : V ≃ W) (Λ : Finset V) (ω : Config V) :
    maxClusterIntersection (Λ.map e.toEmbedding) (Sym2.map e '' ω) =
      maxClusterIntersection Λ ω := by
  unfold maxClusterIntersection
  rw [Finset.sup_map]
  congr 1
  funext v
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  rw [cluster_image, Finset.coe_map, Equiv.coe_toEmbedding, ← Set.image_inter e.injective,
    Set.ncard_image_of_injective _ e.injective]

/-- The largest intersection with `Λ` is at most `|Λ|`. -/
theorem maxClusterIntersection_le_card (Λ : Finset V) (ω : Config V) :
    maxClusterIntersection Λ ω ≤ Λ.card := by
  unfold maxClusterIntersection
  refine Finset.sup_le fun v _ => ?_
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard Set.inter_subset_right Λ.finite_toSet

/-- The largest intersection with `Λ` only depends on the clusters of the points of `Λ`. -/
theorem maxClusterIntersection_congr {Λ : Finset V} {ω ω' : Config V}
    (h : ∀ x ∈ Λ, cluster ω x = cluster ω' x) :
    maxClusterIntersection Λ ω = maxClusterIntersection Λ ω' := by
  unfold maxClusterIntersection
  exact Finset.sup_congr rfl fun v hv => by rw [h v hv]

/-- The canonical profile at intensity `β` is continuous in the kernel, pairwise. -/
theorem tendsto_intensityProfile_apply {ι : Type*} {l : Filter ι} {K : ι → Sym2 V → ℝ≥0}
    {K₀ : Sym2 V → ℝ≥0} {e : Sym2 V} (h : Tendsto (fun i => K i e) l (𝓝 (K₀ e))) (β : ℝ≥0) :
    Tendsto (fun i => intensityProfile (K i) β e) l (𝓝 (intensityProfile K₀ β e)) := by
  rw [tendsto_subtype_rng]
  exact ((by fun_prop : Continuous fun t : ℝ≥0 => 1 - Real.exp (-(β : ℝ) * (t : ℝ))).tendsto
    _).comp h

end PercLib.Percolation.Bond

namespace PercLib.Models

/-- **Counting good elements.** Among `Q ≥ 2` elements with values `f`, `g` in a linear order,
at least `Q/2` satisfy both: at least `⌊Q/2⌋ - 1` others have a larger or equal `f`, and some
other has a larger or equal `g`. -/
theorem card_le_two_mul_card_filter_le_and_exists_le {κ α : Type*} [DecidableEq κ]
    [LinearOrder α] (K : Finset κ) (hK : 2 ≤ K.card) (f g : κ → α) :
    K.card ≤ 2 * (K.filter fun k => K.card / 2 - 1 ≤ (K.filter fun k' => k' ≠ k ∧ f k ≤ f k').card ∧
      ∃ k' ∈ K, k' ≠ k ∧ g k ≤ g k').card := by
  set m := K.card / 2 - 1
  set G := K.filter fun k => m ≤ (K.filter fun k' => k' ≠ k ∧ f k ≤ f k').card ∧
      ∃ k' ∈ K, k' ≠ k ∧ g k ≤ g k'
  set B1 := K.filter fun k => ¬ m ≤ (K.filter fun k' => k' ≠ k ∧ f k ≤ f k').card
  set B2 := K.filter fun k => ¬ ∃ k' ∈ K, k' ≠ k ∧ g k ≤ g k'
  have hB1 : B1.card ≤ m := by
    by_contra h
    push Not at h
    have hne : B1.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨k, hk, hmin⟩ := B1.exists_min_image f hne
    have hkB := Finset.mem_filter.1 hk
    apply hkB.2
    have hsub : B1.erase k ⊆ K.filter fun k' => k' ≠ k ∧ f k ≤ f k' := by
      intro k' hk'
      obtain ⟨hne', hk'B⟩ := Finset.mem_erase.1 hk'
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hk'B).1, hne', hmin k' hk'B⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hk] at this
    omega
  have hB2 : B2.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha' := Finset.mem_filter.1 ha
    have hb' := Finset.mem_filter.1 hb
    push Not at ha' hb'
    exact lt_asymm (ha'.2 b hb'.1 (Ne.symm hab)) (hb'.2 a ha'.1 hab)
  have hcov : K ⊆ G ∪ B1 ∪ B2 := by
    intro k hk
    by_cases h1 : m ≤ (K.filter fun k' => k' ≠ k ∧ f k ≤ f k').card
    · by_cases h2 : ∃ k' ∈ K, k' ≠ k ∧ g k ≤ g k'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hk, h1, h2⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hk, h2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hk, h1⟩))
  have h := (Finset.card_le_card hcov).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  omega

namespace DigitHierarchy

variable {d L : ℕ} (σ : DigitHierarchy d L)

/-! ### Dependence on the block only -/

theorem block_congr {n : ℕ} {y z : Fin d → ℤ} (h : σ.blockIndex n y = σ.blockIndex n z) :
    σ.block n y = σ.block n z := by
  unfold block; rw [h]

variable [NeZero L]

theorem blockIndex_blockCorner (n : ℕ) (k : Fin d → ℤ) :
    σ.blockIndex n (σ.blockCorner n k) = k := by
  have hp : (L : ℤ) ^ n ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 (NeZero.ne L))
  funext i
  simp only [blockIndex, blockCorner, add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left _ hp

variable {J : Sym2 (Fin d → ℤ) → ℝ≥0} {c : ℝ≥0} {s : ℝ} {β : ℝ≥0}

theorem expectedBlockMax_congr {n : ℕ} {y z : Fin d → ℤ}
    (h : σ.blockIndex n y = σ.blockIndex n z) :
    σ.expectedBlockMax J c s β n y = σ.expectedBlockMax J c s β n z := by
  unfold expectedBlockMax
  rw [σ.block_congr h,
    σ.restrictedKernel_eq_of_blockIndex_succ_eq J c s (σ.blockIndex_succ_eq_of_eq h)]

theorem blockPairSum_congr {n : ℕ} {y z : Fin d → ℤ}
    (h : σ.blockIndex n y = σ.blockIndex n z) :
    σ.blockPairSum J c s β n y = σ.blockPairSum J c s β n z := by
  unfold blockPairSum
  rw [σ.block_congr h,
    σ.restrictedKernel_eq_of_blockIndex_succ_eq J c s (σ.blockIndex_succ_eq_of_eq h)]

/-- Goodness of the level-`n` block of `y` only depends on that block. -/
theorem isGoodBlock_congr {n : ℕ} {y z : Fin d → ℤ} (h : σ.blockIndex n y = σ.blockIndex n z) :
    σ.IsGoodBlock J c s β n y ↔ σ.IsGoodBlock J c s β n z := by
  unfold IsGoodBlock
  rw [σ.block_congr (σ.blockIndex_succ_eq_of_eq h), h, σ.expectedBlockMax_congr h,
    σ.blockPairSum_congr h]

/-! ### Half of the children are good -/

open Classical in
/-- **At least half of the children of every block are good**: among the `Q = L^d ≥ 2`
children of the level-`(n+1)` block of `z`, counted by block index, at least `Q/2` are good. -/
theorem card_le_two_mul_card_image_filter_isGoodBlock (hQ : 2 ≤ L ^ d)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (β : ℝ≥0) (n : ℕ) (z : Fin d → ℤ) :
    L ^ d ≤ 2 * (((σ.block (n + 1) z).filter fun y => σ.IsGoodBlock J c s β n y).image
      (σ.blockIndex n)).card := by
  classical
  set P := σ.block (n + 1) z
  set K := P.image (σ.blockIndex n) with hKdef
  have hK : K.card = L ^ d := σ.card_image_blockIndex_block_succ n z
  set f : (Fin d → ℤ) → ℝ≥0∞ := fun k => σ.expectedBlockMax J c s β n (σ.blockCorner n k)
  set g : (Fin d → ℤ) → ℝ≥0∞ := fun k => σ.blockPairSum J c s β n (σ.blockCorner n k)
  have hF : ∀ y, σ.expectedBlockMax J c s β n y = f (σ.blockIndex n y) := fun y =>
    σ.expectedBlockMax_congr (σ.blockIndex_blockCorner n _).symm
  have hG : ∀ y, σ.blockPairSum J c s β n y = g (σ.blockIndex n y) := fun y =>
    σ.blockPairSum_congr (σ.blockIndex_blockCorner n _).symm
  have key : ∀ y ∈ P, σ.IsGoodBlock J c s β n y ↔
      (K.card / 2 - 1 ≤ (K.filter fun k' => k' ≠ σ.blockIndex n y ∧
          f (σ.blockIndex n y) ≤ f k').card ∧
        ∃ k' ∈ K, k' ≠ σ.blockIndex n y ∧ g (σ.blockIndex n y) ≤ g k') := by
    intro y hy
    have hPy : σ.block (n + 1) y = P :=
      σ.block_congr (σ.mem_block.1 hy)
    unfold IsGoodBlock
    rw [hPy, hK]
    simp only [hF, hG]
    have himg : ((P.filter fun y' => σ.blockIndex n y' ≠ σ.blockIndex n y ∧
          f (σ.blockIndex n y) ≤ f (σ.blockIndex n y')).image (σ.blockIndex n)) =
        K.filter fun k' => k' ≠ σ.blockIndex n y ∧ f (σ.blockIndex n y) ≤ f k' := by
      ext k'
      simp only [Finset.mem_image, Finset.mem_filter, hKdef]
      constructor
      · rintro ⟨y', ⟨hy'P, hne, hle⟩, rfl⟩
        exact ⟨⟨y', hy'P, rfl⟩, hne, hle⟩
      · rintro ⟨⟨y', hy'P, rfl⟩, hne, hle⟩
        exact ⟨y', ⟨hy'P, hne, hle⟩, rfl⟩
    rw [himg]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨y', hy'P, hne, hle⟩
      exact ⟨σ.blockIndex n y', Finset.mem_image_of_mem _ hy'P, hne, hle⟩
    · rintro ⟨k', hk', hne, hle⟩
      obtain ⟨y', hy'P, rfl⟩ := Finset.mem_image.1 hk'
      exact ⟨y', hy'P, hne, hle⟩
  have himg : ((P.filter fun y => σ.IsGoodBlock J c s β n y).image (σ.blockIndex n)) =
      K.filter fun k => K.card / 2 - 1 ≤ (K.filter fun k' => k' ≠ k ∧ f k ≤ f k').card ∧
        ∃ k' ∈ K, k' ≠ k ∧ g k ≤ g k' := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hyP, hgood⟩, rfl⟩
      exact ⟨Finset.mem_image_of_mem _ hyP, (key y hyP).1 hgood⟩
    · rintro ⟨hk, hgood⟩
      obtain ⟨y, hyP, rfl⟩ := Finset.mem_image.1 hk
      exact ⟨y, ⟨hyP, (key y hyP).2 hgood⟩, rfl⟩
  rw [himg, ← hK]
  exact card_le_two_mul_card_filter_le_and_exists_le K (hK ▸ hQ) f g

/-- Every block has a good child. -/
theorem exists_mem_block_isGoodBlock (hQ : 2 ≤ L ^ d) (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0)
    (s : ℝ) (β : ℝ≥0) (n : ℕ) (z : Fin d → ℤ) :
    ∃ y ∈ σ.block (n + 1) z, σ.IsGoodBlock J c s β n y := by
  classical
  have h := σ.card_le_two_mul_card_image_filter_isGoodBlock hQ J c s β n z
  obtain ⟨k, hk⟩ := Finset.card_pos.1 (by omega : 0 < (((σ.block (n + 1) z).filter
    fun y => σ.IsGoodBlock J c s β n y).image (σ.blockIndex n)).card)
  obtain ⟨y, hy, -⟩ := Finset.mem_image.1 hk
  exact ⟨y, (Finset.mem_filter.1 hy).1, (Finset.mem_filter.1 hy).2⟩

/-- For every `N` some point has good blocks at all levels `n ≤ N`. -/
theorem exists_forall_isGoodBlock_le (hQ : 2 ≤ L ^ d) (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0)
    (s : ℝ) (β : ℝ≥0) (N : ℕ) : ∃ z, ∀ n ≤ N, σ.IsGoodBlock J c s β n z := by
  have key : ∀ k ≤ N + 1, ∃ z, ∀ n, N + 1 - k ≤ n → n ≤ N → σ.IsGoodBlock J c s β n z := by
    intro k
    induction k with
    | zero => intro _; exact ⟨0, fun n h1 h2 => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := ih (by omega)
      obtain ⟨y, hy, hgood⟩ := σ.exists_mem_block_isGoodBlock hQ J c s β (N - k) z
      refine ⟨y, fun n h1 h2 => ?_⟩
      by_cases hn : n = N - k
      · subst hn; exact hgood
      · have hbI : σ.blockIndex n y = σ.blockIndex n z :=
          σ.blockIndex_eq_of_le (by omega : N - k + 1 ≤ n) (σ.mem_block.1 hy)
        exact (σ.isGoodBlock_congr hbI).2 (hz n (by omega) h2)
  obtain ⟨z, hz⟩ := key (N + 1) le_rfl
  exact ⟨z, fun n hn => hz n (by omega) hn⟩

/-! ### Translation covariance -/

omit [NeZero L] in
/-- First common levels of hierarchies with the same block relations agree. -/
theorem commonLevel_eq_of_forall_iff {τ : DigitHierarchy d L} {x y x' y' : Fin d → ℤ}
    (h : ∀ n, τ.blockIndex n x' = τ.blockIndex n y' ↔ σ.blockIndex n x = σ.blockIndex n y) :
    τ.commonLevel x' y' = σ.commonLevel x y := by
  classical
  unfold commonLevel
  have he : (∃ n, τ.blockIndex n x' = τ.blockIndex n y') ↔
      ∃ n, σ.blockIndex n x = σ.blockIndex n y := exists_congr h
  by_cases hσ : ∃ n, σ.blockIndex n x = σ.blockIndex n y
  · have hτ' := he.2 hσ
    simp only [hσ, hτ', ↓reduceDIte]
    congr 1
    exact_mod_cast Nat.find_congr' fun {n} => h n
  · have hτ' := mt he.1 hσ
    simp only [hσ, hτ', ↓reduceDIte]

variable (x : Fin d → ℤ)

theorem translate_blockIndex_add_eq_iff (n : ℕ) (u v : Fin d → ℤ) :
    (σ.translate x).blockIndex n (u + x) = (σ.translate x).blockIndex n (v + x) ↔
      σ.blockIndex n u = σ.blockIndex n v := by
  rw [blockIndex_translate_add, blockIndex_translate_add, add_left_inj]

theorem commonLevel_translate_add (u v : Fin d → ℤ) :
    (σ.translate x).commonLevel (u + x) (v + x) = σ.commonLevel u v :=
  σ.commonLevel_eq_of_forall_iff fun n => σ.translate_blockIndex_add_eq_iff x n u v

theorem inStrictAncestor_translate_add (n : ℕ) (z u v : Fin d → ℤ) :
    (σ.translate x).InStrictAncestor n (z + x) (u + x) (v + x) ↔ σ.InStrictAncestor n z u v := by
  simp only [InStrictAncestor, commonLevel_translate_add, translate_blockIndex_add_eq_iff]

theorem layerKernel_translate_add (c : ℝ≥0) (s : ℝ) (u v : Fin d → ℤ) :
    (σ.translate x).layerKernel c s s(u + x, v + x) = σ.layerKernel c s s(u, v) := by
  rw [layerKernel_apply, layerKernel_apply, commonLevel_translate_add]
  by_cases h : u = v
  · simp [h]
  · simp [h]

theorem ancestorKernel_translate_add (c : ℝ≥0) (s : ℝ) (n : ℕ) (z u v : Fin d → ℤ) :
    (σ.translate x).ancestorKernel c s n (z + x) s(u + x, v + x) =
      σ.ancestorKernel c s n z s(u, v) := by
  rw [ancestorKernel_apply, ancestorKernel_apply, layerKernel_translate_add]
  by_cases h : σ.InStrictAncestor n z u v
  · have h' := (σ.inStrictAncestor_translate_add x n z u v).2 h
    simp [h, h']
  · have h' := mt (σ.inStrictAncestor_translate_add x n z u v).1 h
    simp [h, h']

theorem restrictedKernel_translate_add (hJ : ∀ u v x, J s(u + x, v + x) = J s(u, v))
    (n : ℕ) (z u v : Fin d → ℤ) :
    (σ.translate x).restrictedKernel J c s n (z + x) s(u + x, v + x) =
      σ.restrictedKernel J c s n z s(u, v) := by
  rw [restrictedKernel_apply, restrictedKernel_apply, hJ, ancestorKernel_translate_add]

theorem block_translate_add (n : ℕ) (z : Fin d → ℤ) :
    (σ.translate x).block n (z + x) = (σ.block n z).map (Equiv.addRight x).toEmbedding := by
  ext u
  rw [mem_block, Finset.mem_map_equiv, mem_block]
  conv_lhs => rw [← sub_add_cancel u x]
  rw [translate_blockIndex_add_eq_iff]
  simp [sub_eq_add_neg]

theorem law_translate_add (hJ : ∀ u v x, J s(u + x, v + x) = J s(u, v)) (n : ℕ)
    (z : Fin d → ℤ) :
    (law (intensityProfile (σ.restrictedKernel J c s n z) β)).map
        (fun ω => Sym2.map (Equiv.addRight x) '' ω) =
      law (intensityProfile ((σ.translate x).restrictedKernel J c s n (z + x)) β) := by
  have himg : (fun ω : Config (Fin d → ℤ) => Sym2.map (Equiv.addRight x) '' ω) =
      fun ω => (Sym2.map (Equiv.addRight x).symm.toEmbedding ⁻¹' ω : Config _) := by
    funext ω
    ext f
    exact mem_image_sym2Map_iff (Equiv.addRight x) ω f
  rw [himg, law_map_preimage_sym2Map]
  congr 1
  funext f
  induction f using Sym2.ind with
  | _ u v =>
    have h := σ.restrictedKernel_translate_add (c := c) (s := s) x hJ n z (u - x) (v - x)
    simp only [sub_add_cancel] at h
    simp [intensityProfile, Sym2.map_mk, h, ← sub_eq_add_neg]

theorem expectedBlockMax_translate_add (hJ : ∀ u v x, J s(u + x, v + x) = J s(u, v))
    (n : ℕ) (z : Fin d → ℤ) :
    (σ.translate x).expectedBlockMax J c s β n (z + x) = σ.expectedBlockMax J c s β n z := by
  unfold expectedBlockMax
  rw [← σ.law_translate_add x hJ, lintegral_map_image_sym2Map, block_translate_add]
  simp only [maxClusterIntersection_map_image]

theorem blockPairSum_translate_add (hJ : ∀ u v x, J s(u + x, v + x) = J s(u, v))
    (n : ℕ) (z : Fin d → ℤ) :
    (σ.translate x).blockPairSum J c s β n (z + x) = σ.blockPairSum J c s β n z := by
  unfold blockPairSum
  rw [block_translate_add, Finset.sum_map]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact tau_eq_of_map_law (Equiv.addRight x) (σ.law_translate_add x hJ n z) u v

/-- Goodness is carried along translations of the hierarchy. -/
theorem isGoodBlock_translate_add (hJ : ∀ u v x, J s(u + x, v + x) = J s(u, v)) {n : ℕ}
    {z : Fin d → ℤ} (h : σ.IsGoodBlock J c s β n z) :
    (σ.translate x).IsGoodBlock J c s β n (z + x) := by
  classical
  obtain ⟨h1, y, hy, hne, hle⟩ := h
  refine ⟨h1.trans (le_of_eq ?_), y + x, ?_, ?_, ?_⟩
  · rw [block_translate_add, Finset.filter_map, Finset.map_eq_image, Finset.image_image]
    have hfil : ((σ.block (n + 1) z).filter ((fun y => (σ.translate x).blockIndex n y ≠
          (σ.translate x).blockIndex n (z + x) ∧
          (σ.translate x).expectedBlockMax J c s β n (z + x) ≤
            (σ.translate x).expectedBlockMax J c s β n y) ∘ (Equiv.addRight x).toEmbedding)) =
        (σ.block (n + 1) z).filter fun y => σ.blockIndex n y ≠ σ.blockIndex n z ∧
          σ.expectedBlockMax J c s β n z ≤ σ.expectedBlockMax J c s β n y := by
      refine Finset.filter_congr fun y _ => ?_
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.coe_addRight, ne_eq,
        translate_blockIndex_add_eq_iff, expectedBlockMax_translate_add σ x hJ]
    rw [hfil]
    have hcomp : ((σ.translate x).blockIndex n ∘ (Equiv.addRight x).toEmbedding) =
        (fun k => k + fun i => (σ.offset n i + x i) / (L : ℤ) ^ n) ∘ σ.blockIndex n := by
      funext u
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.coe_addRight,
        blockIndex_translate_add]
    rw [hcomp, ← Finset.image_image, Finset.card_image_of_injective _ (add_left_injective _)]
  · rw [block_translate_add]
    exact Finset.mem_map_of_mem _ hy
  · rwa [ne_eq, translate_blockIndex_add_eq_iff]
  · rwa [blockPairSum_translate_add σ x hJ, blockPairSum_translate_add σ x hJ]

/-! ### Continuity in the digits -/

section Continuity

variable {ι : Type*} {l : Filter ι} {τ : ι → DigitHierarchy d L}
  (hτ : ∀ m, ∀ᶠ i in l, (τ i).digit m = σ.digit m)
include hτ

omit [NeZero L] in
theorem eventually_offset_eq (n : ℕ) : ∀ᶠ i in l, (τ i).offset n = σ.offset n := by
  filter_upwards [(Filter.eventually_all_finset (Finset.range n)).2 fun m _ => hτ m] with i hi
  funext j
  simp only [offset]
  exact Finset.sum_congr rfl fun m hm => by rw [hi m hm]

omit [NeZero L] in
theorem eventually_blockIndex_eq (n : ℕ) : ∀ᶠ i in l, (τ i).blockIndex n = σ.blockIndex n := by
  filter_upwards [σ.eventually_offset_eq hτ n] with i hi
  funext x j
  simp only [blockIndex, hi]

omit [NeZero L] in
theorem eventually_block_eq (n : ℕ) : ∀ᶠ i in l, (τ i).block n = σ.block n := by
  filter_upwards [σ.eventually_offset_eq hτ n, σ.eventually_blockIndex_eq hτ n] with i hi hi'
  funext z
  simp only [block, hi, hi']

omit [NeZero L] in
theorem eventually_forall_le_blockIndex_eq (N : ℕ) :
    ∀ᶠ i in l, ∀ n ≤ N, (τ i).blockIndex n = σ.blockIndex n := by
  filter_upwards [(Filter.eventually_all_finset (Finset.range (N + 1))).2
    fun n _ => σ.eventually_blockIndex_eq hτ n] with i hi n hn
  exact hi n (Finset.mem_range.2 (by omega))

omit hτ [NeZero L] in
theorem commonLevel_eq_coe_iff {x y : Fin d → ℤ} {m : ℕ} :
    σ.commonLevel x y = m ↔
      σ.blockIndex m x = σ.blockIndex m y ∧ ∀ n < m, σ.blockIndex n x ≠ σ.blockIndex n y := by
  constructor
  · intro h
    exact ⟨σ.blockIndex_eq_of_commonLevel_eq h, fun n hn =>
      σ.blockIndex_ne_of_lt_commonLevel (by rw [h]; exact_mod_cast hn)⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (σ.commonLevel_le h1) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [← hk] at hlt
    exact h2 k (by exact_mod_cast hlt) (σ.blockIndex_eq_of_commonLevel_eq hk.symm)

omit hτ [NeZero L] in
theorem le_commonLevel_of_forall_lt {x y : Fin d → ℤ} {N : ℕ}
    (h : ∀ n < N, σ.blockIndex n x ≠ σ.blockIndex n y) : (N : ℕ∞) ≤ σ.commonLevel x y := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  rw [← hk] at hlt
  exact h k (by exact_mod_cast hlt) (σ.blockIndex_eq_of_commonLevel_eq hk.symm)

omit hτ [NeZero L] in
theorem layerWeight_le_of_le (hL : 1 ≤ L) (hs : 0 ≤ s) {N : ℕ} {k : ℕ∞} (h : (N : ℕ∞) ≤ k) :
    layerWeight L c s k ≤ c * (L : ℝ≥0) ^ (-(s * (N : ℝ))) := by
  by_cases hk : k = ⊤
  · simp [hk]
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hk
  rw [layerWeight_coe]
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast (by exact_mod_cast h : N ≤ m)
  exact mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL)
    (neg_le_neg (mul_le_mul_of_nonneg_left hNm hs))) zero_le

omit hτ [NeZero L] in
theorem tendsto_layerWeight_bound (hL : 1 < L) (hs : 0 < s) :
    Tendsto (fun N : ℕ => c * (L : ℝ≥0) ^ (-(s * (N : ℝ)))) atTop (𝓝 0) := by
  have h1 : (L : ℝ≥0) ^ (-s) < 1 :=
    NNReal.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hL) (neg_lt_zero.2 hs)
  have h2 : (fun N : ℕ => c * (L : ℝ≥0) ^ (-(s * (N : ℝ)))) =
      fun N : ℕ => c * ((L : ℝ≥0) ^ (-s)) ^ N := by
    funext N
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul]
  rw [h2, ← mul_zero c]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one zero_le h1).const_mul c

omit hτ [NeZero L] in
theorem inStrictAncestor_iff_of_commonLevel_eq {n m : ℕ} {z x y : Fin d → ℤ}
    (h : σ.commonLevel x y = m) :
    σ.InStrictAncestor n z x y ↔ n < m ∧ σ.blockIndex m x = σ.blockIndex m z := by
  constructor
  · rintro ⟨m', h1, h2, h3⟩
    have : m = m' := by exact_mod_cast h.symm.trans h2
    subst this
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨m, h1, h, h2⟩

omit [NeZero L] in
/-- The strict-ancestor kernel of each pair converges along converging digits. -/
theorem tendsto_ancestorKernel (hL : 1 < L) (hs : 0 < s) (n : ℕ) (z : Fin d → ℤ)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun i => (τ i).ancestorKernel c s n z e) l (𝓝 (σ.ancestorKernel c s n z e)) := by
  induction e using Sym2.ind with
  | _ x y =>
  by_cases htop : σ.commonLevel x y = ⊤
  · have h0 : σ.ancestorKernel c s n z s(x, y) = 0 := by
      rw [ancestorKernel_apply]
      split_ifs with h
      · obtain ⟨m', _, h2, _⟩ := h
        rw [htop] at h2
        exact absurd h2 (ENat.top_ne_natCast m')
      · rfl
    rw [h0]
    have hne : ∀ k, σ.blockIndex k x ≠ σ.blockIndex k y := fun k hk =>
      htop.not_lt ((σ.commonLevel_le hk).trans_lt (ENat.natCast_ne_top k).lt_top)
    refine tendsto_order.2 ⟨fun a ha => absurd ha (not_lt.2 zero_le), fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := ((tendsto_layerWeight_bound (c := c) hL hs).eventually
      (gt_mem_nhds ha)).exists
    filter_upwards [σ.eventually_forall_le_blockIndex_eq hτ N] with i hi
    have hle : (N : ℕ∞) ≤ (τ i).commonLevel x y :=
      (τ i).le_commonLevel_of_forall_lt fun k hk => by rw [hi k hk.le]; exact hne k
    refine lt_of_le_of_lt ?_ hN
    refine ((τ i).ancestorKernel_le_layerKernel c s n z s(x, y)).trans ?_
    rw [layerKernel_apply]
    split_ifs
    · exact zero_le
    · exact layerWeight_le_of_le hL.le hs.le hle
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 htop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [σ.eventually_forall_le_blockIndex_eq hτ m] with i hi
    have hcl : (τ i).commonLevel x y = m := by
      obtain ⟨h1, h2⟩ := (σ.commonLevel_eq_coe_iff).1 hm.symm
      refine ((τ i).commonLevel_eq_coe_iff).2 ⟨?_, fun k hk => ?_⟩
      · rw [hi m le_rfl]; exact h1
      · rw [hi k hk.le]; exact h2 k hk
    rw [ancestorKernel_apply, ancestorKernel_apply, layerKernel_apply, layerKernel_apply, hcl,
      ← hm, (τ i).inStrictAncestor_iff_of_commonLevel_eq hcl,
      σ.inStrictAncestor_iff_of_commonLevel_eq hm.symm, hi m le_rfl]

omit [NeZero L] in
theorem tendsto_restrictedKernel (hL : 1 < L) (hs : 0 < s) (n : ℕ) (z : Fin d → ℤ)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun i => (τ i).restrictedKernel J c s n z e) l
      (𝓝 (σ.restrictedKernel J c s n z e)) :=
  tendsto_const_nhds.sub (σ.tendsto_ancestorKernel hτ hL hs n z e)

variable [l.IsCountablyGenerated]

omit [NeZero L] in
/-- **Continuity of `E Z_B` in the digits** below the critical intensity. -/
theorem tendsto_expectedBlockMax (hL : 1 < L) (hs : 0 < s)
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J) (n : ℕ) (z : Fin d → ℤ) :
    Tendsto (fun i => (τ i).expectedBlockMax J c s β n z) l
      (𝓝 (σ.expectedBlockMax J c s β n z)) := by
  have hfin : ∀ᵐ ω ∂law (intensityProfile J β), ∀ x ∈ σ.block n z, (cluster ω x).Finite := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (law_exists_cluster_infinite_eq_zero_of_lt_globalCriticalIntensity J hβ)] with ω hω x _
    by_contra hx
    exact hω ⟨x, hx⟩
  refine Tendsto.congr' ?_ (tendsto_lintegral_law_of_tendsto
    (q := fun i => intensityProfile ((τ i).restrictedKernel J c s n z) β)
    (fun e => tendsto_intensityProfile_apply (σ.tendsto_restrictedKernel hτ hL hs n z e) β)
    (fun i => intensityProfile_le_of_le (fun _ => tsub_le_self) β)
    (intensityProfile_le_of_le (fun _ => tsub_le_self) β) (σ.block n z) hfin
    (measurable_from_nat.comp (measurable_maxClusterIntersection _))
    (ENNReal.natCast_ne_top (σ.block n z).card)
    (fun ω => by exact_mod_cast maxClusterIntersection_le_card _ ω)
    (fun ω ω' h => by rw [maxClusterIntersection_congr h]))
  filter_upwards [σ.eventually_block_eq hτ n] with i hi
  simp only [expectedBlockMax, hi]

omit [NeZero L] in
/-- **Continuity of `S_B` in the digits** below the critical intensity. -/
theorem tendsto_blockPairSum (hL : 1 < L) (hs : 0 < s)
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J) (n : ℕ) (z : Fin d → ℤ) :
    Tendsto (fun i => (τ i).blockPairSum J c s β n z) l (𝓝 (σ.blockPairSum J c s β n z)) := by
  have htau : ∀ x y, Tendsto
      (fun i => tau (intensityProfile ((τ i).restrictedKernel J c s n z) β) x y) l
      (𝓝 (tau (intensityProfile (σ.restrictedKernel J c s n z) β) x y)) := by
    intro x y
    have hfin : ∀ᵐ ω ∂law (intensityProfile J β), ∀ x' ∈ ({x} : Finset _),
        (cluster ω x').Finite := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (law_exists_cluster_infinite_eq_zero_of_lt_globalCriticalIntensity J hβ)] with ω hω x' _
      by_contra hx
      exact hω ⟨x', hx⟩
    have h := tendsto_lintegral_law_of_tendsto
      (q := fun i => intensityProfile ((τ i).restrictedKernel J c s n z) β)
      (fun e => tendsto_intensityProfile_apply (σ.tendsto_restrictedKernel hτ hL hs n z e) β)
      (fun i => intensityProfile_le_of_le (fun _ => tsub_le_self) β)
      (intensityProfile_le_of_le (fun _ => tsub_le_self) β) {x} hfin
      (f := (conn x y).indicator 1) ((measurable_one).indicator (measurableSet_conn x y))
      ENNReal.one_ne_top (fun ω => by
        by_cases hω : ω ∈ conn x y <;> simp [hω])
      (fun ω ω' h => by
        have hx := h x (Finset.mem_singleton_self x)
        have hiff : ω ∈ conn x y ↔ ω' ∈ conn x y := by
          change y ∈ cluster ω x ↔ y ∈ cluster ω' x
          rw [hx]
        by_cases hω : ω ∈ conn x y
        · simp [hω, hiff.1 hω]
        · simp [hω, mt hiff.2 hω])
    simp only [lintegral_indicator_one (measurableSet_conn x y)] at h
    exact h
  refine Tendsto.congr' ?_ (tendsto_finsetSum (σ.block n z) fun x _ =>
    tendsto_finsetSum (σ.block n z) fun y _ => htau x y)
  filter_upwards [σ.eventually_block_eq hτ n] with i hi
  simp only [blockPairSum, hi]

omit [NeZero L] in
/-- **Goodness is a closed condition on the digits**: a block of a fixed point that is good
for eventually every hierarchy of a converging family is good for the limit. -/
theorem isGoodBlock_of_tendsto [l.NeBot] (hL : 1 < L) (hs : 0 < s)
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J) {n : ℕ} {z : Fin d → ℤ}
    (hgood : ∀ᶠ i in l, (τ i).IsGoodBlock J c s β n z) : σ.IsGoodBlock J c s β n z := by
  classical
  set P := σ.block (n + 1) z
  have hP := σ.eventually_block_eq hτ (n + 1)
  have hI := σ.eventually_blockIndex_eq hτ n
  have hF := fun y => σ.tendsto_expectedBlockMax hτ (J := J) (c := c) hL hs hβ n y
  have hS := fun y => σ.tendsto_blockPairSum hτ (J := J) (c := c) hL hs hβ n y
  constructor
  · have hsub : ∀ᶠ i in l, ∀ y ∈ P, ¬ σ.expectedBlockMax J c s β n z ≤
        σ.expectedBlockMax J c s β n y →
        ¬ (τ i).expectedBlockMax J c s β n z ≤ (τ i).expectedBlockMax J c s β n y := by
      refine (Filter.eventually_all_finset P).2 fun y _ => ?_
      by_cases h : σ.expectedBlockMax J c s β n z ≤ σ.expectedBlockMax J c s β n y
      · exact Eventually.of_forall fun _ h' => absurd h h'
      · filter_upwards [(hF y).eventually_lt (hF z) (not_le.1 h)] with i hi _
        exact not_le.2 hi
    obtain ⟨i, hi, hPi, hIi, hgi⟩ := (hsub.and (hP.and (hI.and hgood))).exists
    refine le_trans hgi.1 (Finset.card_le_card ?_)
    rw [hPi, hIi]
    refine Finset.image_subset_image fun y hy => ?_
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.1, by_contra fun h => hi y hy.1 h hy.2.2⟩
  · by_contra hno
    push Not at hno
    have hlt : ∀ᶠ i in l, ∀ y ∈ P, σ.blockIndex n y ≠ σ.blockIndex n z →
        (τ i).blockPairSum J c s β n y < (τ i).blockPairSum J c s β n z := by
      refine (Filter.eventually_all_finset P).2 fun y hy => ?_
      by_cases h : σ.blockIndex n y ≠ σ.blockIndex n z
      · filter_upwards [(hS y).eventually_lt (hS z) (hno y hy h)] with i hi _
        exact hi
      · exact Eventually.of_forall fun _ h' => absurd h' h
    obtain ⟨i, hi, hPi, hIi, hgi⟩ := (hlt.and (hP.and (hI.and hgood))).exists
    obtain ⟨y, hy, hne, hle⟩ := hgi.2
    rw [hPi] at hy
    rw [hIi] at hne
    exact not_le.2 (hi y hy hne) hle

end Continuity

/-! ### A good hierarchy through the origin -/

/-- **A subcritical model admits an ancestrally good hierarchy through the origin.** For a
translation-invariant kernel `J` on `ℤ^d` (`d ≥ 1`), base `L ≥ 2`, `s > 0` and intensity
`β` below the critical intensity, some digit hierarchy has every block containing the origin
good. -/
theorem exists_isAncestrallyGood_zero (hL : 2 ≤ L) (hd : 0 < d) (hs : 0 < s)
    (hJ : ∀ u v x, J s(u + x, v + x) = J s(u, v))
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J) :
    ∃ σ : DigitHierarchy d L, σ.IsAncestrallyGood J c s β 0 0 := by
  have hQ : 2 ≤ L ^ d := le_trans hL (Nat.le_self_pow hd.ne' L)
  let σ₀ : DigitHierarchy d L := ⟨fun _ _ => 0⟩
  choose z hz using fun N => σ₀.exists_forall_isGoodBlock_le hQ J c s β N
  set τ : ℕ → DigitHierarchy d L := fun N => σ₀.translate (-z N)
  have hτgood : ∀ N n, n ≤ N → (τ N).IsGoodBlock J c s β n 0 := fun N n hn => by
    have := σ₀.isGoodBlock_translate_add (-z N) hJ (hz N n hn)
    rwa [add_neg_cancel] at this
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    isCompact_univ.tendsto_subseq (x := fun N => (τ N).digit) (fun _ => Set.mem_univ _)
  refine ⟨⟨a⟩, fun n _ => ?_⟩
  have hconv : ∀ m, ∀ᶠ j in atTop, (τ (φ j)).digit m = a m := fun m => by
    have h := ((continuous_apply m).tendsto a).comp hlim
    rw [nhds_discrete, tendsto_pure] at h
    exact h
  refine isGoodBlock_of_tendsto (σ := ⟨a⟩) (τ := fun j => τ (φ j)) hconv
    (by omega) hs hβ ?_
  filter_upwards [eventually_ge_atTop n] with j hj
  exact hτgood (φ j) n (hj.trans (hφ.id_le j))

end DigitHierarchy

end PercLib.Models
