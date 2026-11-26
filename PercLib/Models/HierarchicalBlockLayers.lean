/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs. Reference: T. Hutchcroft, *Critical cluster volumes in hierarchical percolation*,
arXiv:2211.05686 (the decomposition of the exact radial model into independent block layers).
-/
module

public import PercLib.Models.HierarchicalBlockLayers.Defs
public import PercLib.Probability.CountableSuperposition
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Independent complete-block layers of the hierarchical lattice

On `V = ℕ →₀ A`, every pair `e` of distinct vertices has one copy `(m, e)` in each block of level
`m ≥ h(e)` containing it. Give every copy an independent rate-one exponential clock and open it
when the clock rings by the layer time `β L^{-sm}` (`1 < L`, `0 < s`). Then:

* the pairs with an open copy form bond percolation with the exact radial kernel
  `J_∞(x,y) = ∑_{m ≥ h(x,y)} L^{-sm} = L^s/(L^s - 1) L^{-s h(x,y)}`;
* inside a block `B` of level `n`, the union `η_B` of the layers of the blocks inside `B` is
  bond percolation with the truncated kernel `J_n = ∑_{m=h}^n L^{-sm} = J_∞ - L^{-sn}/(L^s - 1)`;
* the graph induced on `B` is `η_B` together with the independent layer of the strict ancestors
  of `B`, which is complete-graph percolation with kernel `L^{-sn}/(L^s - 1)`;
* the clusters of `x` in `η_{B_n}`, `B_n` the block of level `n` containing `x`, increase to
  its cluster in the union of all layers.

## Main results

* `infinitePi_map_openCopies`: the open copies have the product law `layerProfile`.
* `prodBernoulli_map_fullConfig`, `prodBernoulli_map_blockConfig`,
  `prodBernoulli_map_ancestorConfig`, `prodBernoulli_map_blockConfig_ancestorConfig`: the laws
  of the full, block and ancestor configurations, and independence of the last two.
* `infinitePi_map_fullConfig_openCopies` and its siblings: the same for the clock model.
* `fullConfig_inter_eq_blockConfig_union_ancestorConfig`: the induced graph on a block.
* `coe_exactKernel_eq_tsum`, `coe_truncatedKernel_eq_sub`: the kernels as layer sums.
* `monotone_cluster_blockConfig`, `iUnion_cluster_blockConfig`: increasing block clusters.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models.HierarchicalLayers

open PercLib.Percolation.Bond PercLib.Probability

variable {A : Type*} [AddCommGroup A]

/-! ### Geometric sums -/

/-- The tail `∑_{m ≥ k} r^m = r^k/(1 - r)` as a sum over all `m`. -/
theorem hasSum_ite_le_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    HasSum (fun m : ℕ => if k ≤ m then r ^ m else 0) (r ^ k / (1 - r)) := by
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left (r ^ k)
  have hinj : Function.Injective (fun n : ℕ => n + k) := add_left_injective k
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro m hm
    have : ¬ k ≤ m := fun h => hm ⟨m - k, Nat.sub_add_cancel h⟩
    simp [this]
  · rw [div_eq_mul_inv]
    convert hg using 1
    funext n
    simp [pow_add, mul_comm]

open Classical in
/-- A sum over the fibre `{j ∈ S | j.2 = e}` of `ℕ × α` is a sum over the levels `m`. -/
theorem hasSum_fibre_snd {α : Type*} (f : ℕ × α → ℝ) (S : Set (ℕ × α)) (e : α) {a : ℝ}
    (h : HasSum (fun m : ℕ => if (m, e) ∈ S then f (m, e) else 0) a) :
    HasSum (fun j : {j | j ∈ S ∧ j.2 = e} => f j) a := by
  classical
  refine (hasSum_subtype_iff_indicator (s := {j | j ∈ S ∧ j.2 = e})).mpr ?_
  have hinj : Function.Injective (fun m : ℕ => (m, e)) := fun _ _ h => (Prod.ext_iff.mp h).1
  refine (hinj.hasSum_iff ?_).mp ?_
  · rintro ⟨m, e'⟩ hm
    apply Set.indicator_of_notMem
    rintro ⟨_, rfl⟩
    exact hm ⟨m, rfl⟩
  · convert h using 1
    funext m
    simp [Set.indicator_apply]

section Powers

variable {L s : ℝ}

theorem rpow_neg_mul_natCast (hL : 1 < L) (m : ℕ) : L ^ (-(s * m)) = (L ^ (-s)) ^ m := by
  rw [show -(s * m) = (-s) * m by ring, Real.rpow_mul (by linarith), Real.rpow_natCast]

theorem rpow_neg_nonneg (hL : 1 < L) : 0 ≤ L ^ (-s) := Real.rpow_nonneg (by linarith) _

theorem rpow_neg_lt_one (hL : 1 < L) (hs : 0 < s) : L ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

/-- The closed form of `J_∞`: `L^s/(L^s - 1) (L^h)^{-s} = r^h/(1 - r)` with `r = L^{-s}`. -/
theorem exact_closed_form (hL : 1 < L) (hs : 0 < s) (h : ℕ) :
    L ^ s / (L ^ s - 1) * (L ^ h) ^ (-s) = (L ^ (-s)) ^ h / (1 - L ^ (-s)) := by
  have hL0 : 0 ≤ L := by linarith
  have hu : 1 < L ^ s := Real.one_lt_rpow hL hs
  have key : (L ^ h) ^ (-s) = (L ^ (-s)) ^ h := by
    rw [← Real.rpow_natCast L h, ← Real.rpow_mul hL0, mul_comm, Real.rpow_mul hL0,
      Real.rpow_natCast]
  rw [key, Real.rpow_neg hL0]
  have hu0 : L ^ s ≠ 0 := by positivity
  have hu1 : L ^ s - 1 ≠ 0 := by linarith
  have hu2 : 1 - (L ^ s)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact inv_ne_one.mpr (by linarith)
  field_simp

/-- `L^{-sn}/(L^s - 1) = r^{n+1}/(1 - r)` with `r = L^{-s}`. -/
theorem ancestor_closed_form (hL : 1 < L) (hs : 0 < s) (n : ℕ) :
    L ^ (-(s * n)) / (L ^ s - 1) = (L ^ (-s)) ^ (n + 1) / (1 - L ^ (-s)) := by
  have hL0 : 0 ≤ L := by linarith
  have hu : 1 < L ^ s := Real.one_lt_rpow hL hs
  rw [rpow_neg_mul_natCast hL, Real.rpow_neg hL0]
  have hu0 : L ^ s ≠ 0 := by positivity
  have hu1 : L ^ s - 1 ≠ 0 := by linarith
  have hu2 : 1 - (L ^ s)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact inv_ne_one.mpr (by linarith)
  field_simp
  rw [pow_succ, ← mul_assoc, mul_comm (L ^ s), mul_assoc, mul_one_div_cancel hu0, mul_one]

end Powers

/-! ### Geometry of blocks -/

/-- A pair inside a block of level `n` has level at most `n`. -/
theorem pairLevel_le_of_mem_block {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ∀ v ∈ e, v ∈ block n x) : pairLevel e ≤ n := by
  induction e using Sym2.ind with
  | _ y z =>
    have hy := he y (Sym2.mem_mk_left y z)
    have hz := he z (Sym2.mem_mk_right y z)
    rw [mem_block] at hy hz
    rw [pairLevel_mk]
    refine le_trans (level_sub_le_max y x z) (max_le ?_ hz)
    rw [level_sub_comm]
    exact hy

/-! ### The configurations as superpositions -/

theorem fullConfig_eq_image (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    fullConfig ξ = Prod.snd '' (ξ ∩ univ) := by
  ext e
  simp

theorem blockConfig_eq_image (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    blockConfig n x ξ =
      Prod.snd '' (ξ ∩ {i | i.1 ≤ n ∧ ∀ v ∈ i.2, v ∈ block n x}) := by
  ext e
  simp only [mem_blockConfig, mem_image, mem_inter_iff, mem_ofPred_eq, Prod.exists,
    exists_eq_right]
  constructor
  · rintro ⟨m, hm, he, hv⟩
    exact ⟨m, he, hm, hv⟩
  · rintro ⟨m, he, hm, hv⟩
    exact ⟨m, hm, he, hv⟩

theorem ancestorConfig_eq_image (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    ancestorConfig n x ξ =
      Prod.snd '' (ξ ∩ {i | n < i.1 ∧ ∀ v ∈ i.2, v ∈ block n x}) := by
  ext e
  simp only [mem_ancestorConfig, mem_image, mem_inter_iff, mem_ofPred_eq, Prod.exists,
    exists_eq_right]
  constructor
  · rintro ⟨m, hm, he, hv⟩
    exact ⟨m, he, hm, hv⟩
  · rintro ⟨m, he, hm, hv⟩
    exact ⟨m, hm, he, hv⟩

variable [Countable A]

theorem measurable_fullConfig :
    Measurable (fullConfig : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) := by
  rw [show (fullConfig : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) =
    fun ξ => Prod.snd '' (ξ ∩ univ) from funext fullConfig_eq_image]
  exact measurable_image_inter _ _

theorem measurable_blockConfig (n : ℕ) (x : ℕ →₀ A) :
    Measurable (blockConfig n x : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) := by
  rw [show (blockConfig n x : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) =
    fun ξ => Prod.snd '' (ξ ∩ _) from funext (blockConfig_eq_image n x)]
  exact measurable_image_inter _ _

theorem measurable_ancestorConfig (n : ℕ) (x : ℕ →₀ A) :
    Measurable (ancestorConfig n x : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) := by
  rw [show (ancestorConfig n x : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) =
    fun ξ => Prod.snd '' (ξ ∩ _) from funext (ancestorConfig_eq_image n x)]
  exact measurable_image_inter _ _

/-! ### Laws -/

variable {L s : ℝ}

omit [Countable A] in
theorem coe_layerWeight_of_isCopy (hL : 1 < L) {m : ℕ} {e : Sym2 (ℕ →₀ A)}
    (hc : IsCopy (m, e)) : (layerWeight L s (m, e) : ℝ) = (L ^ (-s)) ^ m := by
  rw [layerWeight_of_isCopy hc, Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _),
    rpow_neg_mul_natCast hL]

/-- **Full layer law.** The union of all layers is bond percolation with the exact radial
kernel `J_∞`. -/
theorem prodBernoulli_map_fullConfig (hL : 1 < L) (hs : 0 < s) (β : ℝ≥0) :
    (prodBernoulli (layerProfile (A := A) L s β)).map fullConfig =
      law (intensityProfile (exactKernel L s) β) := by
  rw [show (fullConfig : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) =
    fun ξ => Prod.snd '' (ξ ∩ univ) from funext fullConfig_eq_image]
  unfold law
  refine prodBernoulli_map_image_inter_of_hasSum _ _ _ _ β (layerWeight L s) (exactKernel L s)
    (fun j => coe_layerProfile L s β j) (fun e => rfl) fun e =>
    hasSum_fibre_snd (fun j => (layerWeight L s j : ℝ)) _ e ?_
  by_cases he : e.IsDiag
  · rw [exactKernel_of_isDiag he, NNReal.coe_zero]
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext m
    simp only [mem_univ, ↓reduceIte]
    rw [layerWeight_of_not_isCopy (fun h => h.1 he), NNReal.coe_zero]
  · rw [exactKernel_of_not_isDiag he, exact_closed_form hL hs, Real.coe_toNNReal _
      (div_nonneg (pow_nonneg (rpow_neg_nonneg hL) _) (sub_nonneg.mpr (rpow_neg_lt_one hL hs).le))]
    convert hasSum_ite_le_pow (rpow_neg_nonneg hL) (rpow_neg_lt_one hL hs) (pairLevel e) using 1
    funext m
    simp only [mem_univ, ↓reduceIte]
    by_cases hm : pairLevel e ≤ m
    · simp only [hm, ↓reduceIte]
      exact coe_layerWeight_of_isCopy hL ⟨he, hm⟩
    · simp only [hm, ↓reduceIte]
      rw [layerWeight_of_not_isCopy (fun h : IsCopy (m, e) => hm h.2), NNReal.coe_zero]

/-- **Block layer law.** The union `η_B` of the layers of the blocks inside `B = block n x` is
bond percolation with the truncated kernel `J_n`. -/
theorem prodBernoulli_map_blockConfig (hL : 1 < L) (β : ℝ≥0) (n : ℕ) (x : ℕ →₀ A) :
    (prodBernoulli (layerProfile (A := A) L s β)).map (blockConfig n x) =
      law (intensityProfile (truncatedKernel L s n x) β) := by
  rw [show (blockConfig n x : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) =
    fun ξ => Prod.snd '' (ξ ∩ _) from funext (blockConfig_eq_image n x)]
  unfold law
  refine prodBernoulli_map_image_inter_of_hasSum _ _ _ _ β (layerWeight L s)
    (truncatedKernel L s n x) (fun j => coe_layerProfile L s β j) (fun e => rfl) fun e =>
    hasSum_fibre_snd (fun j => (layerWeight L s j : ℝ)) _ e ?_
  by_cases he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x
  · rw [truncatedKernel_of_mem he, Real.coe_toNNReal _ (Finset.sum_nonneg fun m _ =>
      Real.rpow_nonneg (by linarith) _)]
    have hsum : HasSum (fun m : ℕ => if m ∈ Finset.Icc (pairLevel e) n then (L ^ (-s)) ^ m else 0)
        (∑ m ∈ Finset.Icc (pairLevel e) n,
          if m ∈ Finset.Icc (pairLevel e) n then (L ^ (-s)) ^ m else 0) :=
      hasSum_sum_of_ne_finset_zero fun m hm => by simp only [hm, ↓reduceIte]
    convert hsum using 1
    · funext m
      by_cases hm : m ∈ Finset.Icc (pairLevel e) n
      · have hm' := Finset.mem_Icc.mp hm
        have hS : (m, e) ∈ {i : ℕ × Sym2 (ℕ →₀ A) | i.1 ≤ n ∧ ∀ v ∈ i.2, v ∈ block n x} :=
          ⟨hm'.2, he.2⟩
        simp only [hS, hm, ↓reduceIte]
        exact coe_layerWeight_of_isCopy hL ⟨he.1, hm'.1⟩
      · simp only [hm, ↓reduceIte]
        by_cases hS : (m, e) ∈ {i : ℕ × Sym2 (ℕ →₀ A) | i.1 ≤ n ∧ ∀ v ∈ i.2, v ∈ block n x}
        · simp only [hS, ↓reduceIte]
          rw [layerWeight_of_not_isCopy (fun hc : IsCopy (m, e) =>
            hm (Finset.mem_Icc.mpr ⟨hc.2, hS.1⟩)), NNReal.coe_zero]
        · simp only [hS, ↓reduceIte]
    · exact Finset.sum_congr rfl fun m hm => by
        simp only [hm, ↓reduceIte, rpow_neg_mul_natCast hL]
  · rw [truncatedKernel_of_not_mem he, NNReal.coe_zero]
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext m
    by_cases hS : (m, e) ∈ {i : ℕ × Sym2 (ℕ →₀ A) | i.1 ≤ n ∧ ∀ v ∈ i.2, v ∈ block n x}
    · simp only [hS, ↓reduceIte]
      rw [layerWeight_of_not_isCopy (fun hc : IsCopy (m, e) => he ⟨hc.1, hS.2⟩), NNReal.coe_zero]
    · simp only [hS, ↓reduceIte]

/-- **Ancestor layer law.** The layers of the strict ancestors of `B = block n x`, seen on the
pairs of `B`, form complete-graph percolation on `B` with kernel `L^{-sn}/(L^s - 1)`. -/
theorem prodBernoulli_map_ancestorConfig (hL : 1 < L) (hs : 0 < s) (β : ℝ≥0) (n : ℕ)
    (x : ℕ →₀ A) :
    (prodBernoulli (layerProfile (A := A) L s β)).map (ancestorConfig n x) =
      law (intensityProfile (ancestorKernel L s n x) β) := by
  rw [show (ancestorConfig n x : Set (ℕ × Sym2 (ℕ →₀ A)) → Config (ℕ →₀ A)) =
    fun ξ => Prod.snd '' (ξ ∩ _) from funext (ancestorConfig_eq_image n x)]
  unfold law
  refine prodBernoulli_map_image_inter_of_hasSum _ _ _ _ β (layerWeight L s)
    (ancestorKernel L s n x) (fun j => coe_layerProfile L s β j) (fun e => rfl) fun e =>
    hasSum_fibre_snd (fun j => (layerWeight L s j : ℝ)) _ e ?_
  by_cases he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x
  · have hlev := pairLevel_le_of_mem_block he.2
    rw [ancestorKernel_of_mem he, ancestor_closed_form hL hs, Real.coe_toNNReal _
      (div_nonneg (pow_nonneg (rpow_neg_nonneg hL) _) (sub_nonneg.mpr (rpow_neg_lt_one hL hs).le))]
    convert hasSum_ite_le_pow (rpow_neg_nonneg hL) (rpow_neg_lt_one hL hs) (n + 1) using 1
    funext m
    by_cases hm : n + 1 ≤ m
    · have hS : (m, e) ∈ {i : ℕ × Sym2 (ℕ →₀ A) | n < i.1 ∧ ∀ v ∈ i.2, v ∈ block n x} :=
        ⟨hm, he.2⟩
      simp only [hS, hm, ↓reduceIte]
      exact coe_layerWeight_of_isCopy hL ⟨he.1, show pairLevel e ≤ m by omega⟩
    · have hS : (m, e) ∉ {i : ℕ × Sym2 (ℕ →₀ A) | n < i.1 ∧ ∀ v ∈ i.2, v ∈ block n x} :=
        fun h => hm h.1
      simp only [hS, hm, ↓reduceIte]
  · rw [ancestorKernel_of_not_mem he, NNReal.coe_zero]
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext m
    by_cases hS : (m, e) ∈ {i : ℕ × Sym2 (ℕ →₀ A) | n < i.1 ∧ ∀ v ∈ i.2, v ∈ block n x}
    · simp only [hS, ↓reduceIte]
      rw [layerWeight_of_not_isCopy (fun hc : IsCopy (m, e) => he ⟨hc.1, hS.2⟩), NNReal.coe_zero]
    · simp only [hS, ↓reduceIte]

/-- **Independence of the block and ancestor layers.** -/
theorem prodBernoulli_map_blockConfig_ancestorConfig (hL : 1 < L) (hs : 0 < s) (β : ℝ≥0)
    (n : ℕ) (x : ℕ →₀ A) :
    (prodBernoulli (layerProfile (A := A) L s β)).map
        (fun ξ => (blockConfig n x ξ, ancestorConfig n x ξ)) =
      (law (intensityProfile (truncatedKernel L s n x) β)).prod
        (law (intensityProfile (ancestorKernel L s n x) β)) := by
  have hd : Disjoint {i : ℕ × Sym2 (ℕ →₀ A) | i.1 ≤ n ∧ ∀ v ∈ i.2, v ∈ block n x}
      {i | n < i.1 ∧ ∀ v ∈ i.2, v ∈ block n x} :=
    Set.disjoint_left.mpr fun i h1 h2 => absurd h1.1 (not_le.mpr h2.1)
  have h := prodBernoulli_map_image_inter_prod (layerProfile (A := A) L s β) Prod.snd hd
  simp only [← blockConfig_eq_image, ← ancestorConfig_eq_image] at h
  rw [h, prodBernoulli_map_blockConfig hL β, prodBernoulli_map_ancestorConfig hL hs β]

omit [Countable A] in
/-- **The induced graph on a block.** The pairs of `B = block n x` with an open copy are the
union of `η_B` and the ancestor layers on `B`. -/
theorem fullConfig_inter_eq_blockConfig_union_ancestorConfig (n : ℕ) (x : ℕ →₀ A)
    (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    fullConfig ξ ∩ {e | ∀ v ∈ e, v ∈ block n x} = blockConfig n x ξ ∪ ancestorConfig n x ξ := by
  ext e
  simp only [mem_inter_iff, mem_fullConfig, mem_ofPred_eq, mem_union, mem_blockConfig,
    mem_ancestorConfig]
  constructor
  · rintro ⟨⟨m, hm⟩, hv⟩
    rcases le_or_gt m n with h | h
    · exact Or.inl ⟨m, h, hm, hv⟩
    · exact Or.inr ⟨m, h, hm, hv⟩
  · rintro (⟨m, _, hm, hv⟩ | ⟨m, _, hm, hv⟩)
    · exact ⟨⟨m, hm⟩, hv⟩
    · exact ⟨⟨m, hm⟩, hv⟩

/-! ### Exponential clocks -/

omit [Countable A] in
/-- **Clock layers.** The copies opened by independent rate-one exponential clocks at the layer
times `β L^{-sm}` have the product law `layerProfile`. -/
theorem infinitePi_map_openCopies (hL : 0 ≤ L) (β : ℝ≥0) :
    (Measure.infinitePi fun _ : ℕ × Sym2 (ℕ →₀ A) => expMeasure 1).map
        (openCopies L s β) = prodBernoulli (layerProfile L s β) := by
  classical
  refine infinitePi_expMeasure_map_setOf_le {i | IsCopy i} (fun i => β * L ^ (-(s * i.1))) _
    fun i => ?_
  rw [coe_layerProfile]
  by_cases hc : IsCopy i
  · have hcond : i ∈ {i | IsCopy i} ∧ 0 ≤ (β : ℝ) * L ^ (-(s * i.1)) :=
      ⟨hc, mul_nonneg β.coe_nonneg (Real.rpow_nonneg hL _)⟩
    simp only [hcond, and_self, ↓reduceIte]
    rw [layerWeight_of_isCopy hc, Real.coe_toNNReal _ (Real.rpow_nonneg hL _)]
    ring_nf
  · have hcond : ¬ (i ∈ {i | IsCopy i} ∧ 0 ≤ (β : ℝ) * L ^ (-(s * i.1))) := fun h => hc h.1
    simp only [hcond, ↓reduceIte]
    rw [layerWeight_of_not_isCopy hc]
    simp

omit [Countable A] in
theorem measurable_openCopies (L s β : ℝ) :
    Measurable (openCopies (A := A) L s β) :=
  measurable_setOf_mem_and_le _ _

theorem infinitePi_map_fullConfig_openCopies (hL : 1 < L) (hs : 0 < s) (β : ℝ≥0) :
    (Measure.infinitePi fun _ : ℕ × Sym2 (ℕ →₀ A) => expMeasure 1).map
        (fun T => fullConfig (openCopies L s β T)) =
      law (intensityProfile (exactKernel L s) β) := by
  rw [show (fun T => fullConfig (openCopies L s β T)) = fullConfig ∘ openCopies (A := A) L s β
    from rfl, ← Measure.map_map measurable_fullConfig (measurable_openCopies L s β),
    infinitePi_map_openCopies (by linarith), prodBernoulli_map_fullConfig hL hs]

theorem infinitePi_map_blockConfig_openCopies (hL : 1 < L) (β : ℝ≥0) (n : ℕ)
    (x : ℕ →₀ A) :
    (Measure.infinitePi fun _ : ℕ × Sym2 (ℕ →₀ A) => expMeasure 1).map
        (fun T => blockConfig n x (openCopies L s β T)) =
      law (intensityProfile (truncatedKernel L s n x) β) := by
  rw [show (fun T => blockConfig n x (openCopies L s β T)) =
    blockConfig n x ∘ openCopies (A := A) L s β from rfl,
    ← Measure.map_map (measurable_blockConfig n x) (measurable_openCopies L s β),
    infinitePi_map_openCopies (by linarith), prodBernoulli_map_blockConfig hL]

theorem infinitePi_map_blockConfig_ancestorConfig_openCopies (hL : 1 < L) (hs : 0 < s)
    (β : ℝ≥0) (n : ℕ) (x : ℕ →₀ A) :
    (Measure.infinitePi fun _ : ℕ × Sym2 (ℕ →₀ A) => expMeasure 1).map
        (fun T => (blockConfig n x (openCopies L s β T),
          ancestorConfig n x (openCopies L s β T))) =
      (law (intensityProfile (truncatedKernel L s n x) β)).prod
        (law (intensityProfile (ancestorKernel L s n x) β)) := by
  rw [show (fun T => (blockConfig n x (openCopies L s β T),
      ancestorConfig n x (openCopies L s β T))) =
      (fun ξ => (blockConfig n x ξ, ancestorConfig n x ξ)) ∘ openCopies (A := A) L s β from rfl,
    ← Measure.map_map (g := fun ξ => (blockConfig n x ξ, ancestorConfig n x ξ))
    ((measurable_blockConfig n x).prodMk (measurable_ancestorConfig n x))
    (measurable_openCopies L s β), infinitePi_map_openCopies (by linarith),
    prodBernoulli_map_blockConfig_ancestorConfig hL hs]

/-! ### The kernels as layer sums -/

omit [Countable A] in
/-- `J_∞(x,y) = ∑_{m ≥ h(x,y)} L^{-sm}`. -/
theorem coe_exactKernel_eq_tsum (hL : 1 < L) (hs : 0 < s) {e : Sym2 (ℕ →₀ A)}
    (he : ¬ e.IsDiag) :
    (exactKernel L s e : ℝ) = ∑' m : ℕ, if pairLevel e ≤ m then L ^ (-(s * m)) else 0 := by
  have h := hasSum_ite_le_pow (rpow_neg_nonneg hL) (rpow_neg_lt_one hL hs) (pairLevel e)
  rw [exactKernel_of_not_isDiag he, exact_closed_form hL hs, Real.coe_toNNReal _
    (div_nonneg (pow_nonneg (rpow_neg_nonneg hL) _) (sub_nonneg.mpr (rpow_neg_lt_one hL hs).le)),
    ← h.tsum_eq]
  congr 1
  funext m
  rw [rpow_neg_mul_natCast hL]

omit [Countable A] in
/-- `J_n = J_∞ - L^{-sn}/(L^s - 1)` on the pairs of a block of level `n`. -/
theorem coe_truncatedKernel_eq_sub (hL : 1 < L) (hs : 0 < s) {n : ℕ} {x y z : ℕ →₀ A}
    (hy : y ∈ block n x) (hz : z ∈ block n x) (hyz : y ≠ z) :
    (truncatedKernel L s n x s(y, z) : ℝ) =
      exactKernel L s s(y, z) - L ^ (-(s * n)) / (L ^ s - 1) := by
  classical
  have hd : ¬ s(y, z).IsDiag := by simpa using hyz
  have hv : ∀ v ∈ s(y, z), v ∈ block n x := by
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    exacts [hy, hz]
  have hlev := pairLevel_le_of_mem_block hv
  set h := pairLevel s(y, z)
  set r := L ^ (-s)
  have h0 := rpow_neg_nonneg (s := s) hL
  have h1 := rpow_neg_lt_one hL hs
  have hall := hasSum_ite_le_pow h0 h1 h
  have htail := hasSum_ite_le_pow h0 h1 (n + 1)
  have hfin : HasSum (fun m : ℕ => if m ∈ Finset.Icc h n then r ^ m else 0)
      (∑ m ∈ Finset.Icc h n, if m ∈ Finset.Icc h n then r ^ m else 0) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by simp [hm]
  have hsplit : (fun m : ℕ => if h ≤ m then r ^ m else 0) =
      (fun m => if m ∈ Finset.Icc h n then r ^ m else 0) +
        fun m => if n + 1 ≤ m then r ^ m else 0 := by
    funext m
    simp only [Pi.add_apply, Finset.mem_Icc]
    by_cases h1 : h ≤ m <;> by_cases h2 : m ≤ n <;> by_cases h3 : n + 1 ≤ m <;>
      simp [h1, h2, h3] <;> omega
  rw [hsplit] at hall
  have heq := hall.unique (hfin.add htail)
  rw [truncatedKernel_of_mem ⟨hd, hv⟩, Real.coe_toNNReal _ (Finset.sum_nonneg fun m _ =>
      Real.rpow_nonneg (by linarith) _), exactKernel_of_not_isDiag hd, exact_closed_form hL hs,
    Real.coe_toNNReal _ (div_nonneg (pow_nonneg h0 _) (sub_nonneg.mpr h1.le)),
    ancestor_closed_form hL hs, heq]
  have hs' : ∑ m ∈ Finset.Icc h n, L ^ (-(s * m)) =
      ∑ m ∈ Finset.Icc h n, (if m ∈ Finset.Icc h n then r ^ m else 0) :=
    Finset.sum_congr rfl fun m hm => by simp only [hm, ↓reduceIte, rpow_neg_mul_natCast hL, r]
  rw [hs']
  ring

/-! ### Increasing block clusters -/

omit [Countable A] in
theorem blockConfig_mono (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    Monotone fun n => blockConfig n x ξ := by
  intro n n' hn e ⟨m, hm, he, hv⟩
  exact ⟨m, hm.trans hn, he, fun v hv' => block_mono hn x (hv v hv')⟩

omit [Countable A] in
theorem blockConfig_subset_fullConfig (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    blockConfig n x ξ ⊆ fullConfig ξ :=
  fun _ ⟨m, _, he, _⟩ => ⟨m, he⟩

omit [Countable A] in
/-- The clusters of `x` in `η_{B_n}` increase with `n`. -/
theorem monotone_cluster_blockConfig (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    Monotone fun n => cluster (blockConfig n x ξ) x :=
  fun _ _ hn _ hy => SimpleGraph.Reachable.mono (openGraph_mono (blockConfig_mono x ξ hn)) hy

omit [Countable A] in
/-- The clusters of `x` in `η_{B_n}` exhaust its cluster in the union of all layers. -/
theorem iUnion_cluster_blockConfig (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) :
    ⋃ n, cluster (blockConfig n x ξ) x = cluster (fullConfig ξ) x := by
  apply Subset.antisymm
  · exact iUnion_subset fun n y hy =>
      SimpleGraph.Reachable.mono (openGraph_mono (blockConfig_subset_fullConfig n x ξ)) hy
  · intro y hy
    have hy' : (openGraph (fullConfig ξ)).Reachable x y := hy
    clear hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy'
    induction hy' with
    | refl => exact mem_iUnion.mpr ⟨0, mem_cluster_self _ _⟩
    | @tail b c _ hadj ih =>
      obtain ⟨N, hN⟩ := mem_iUnion.mp ih
      rw [openGraph_adj_iff] at hadj
      obtain ⟨⟨m, hm⟩, hbc⟩ := hadj
      set N' := max N (max m (max ((b - x).support.sup Nat.succ)
        ((c - x).support.sup Nat.succ))) with hN'
      refine mem_iUnion.mpr ⟨N', ?_⟩
      have h1 : (openGraph (blockConfig N' x ξ)).Reachable x b :=
        SimpleGraph.Reachable.mono (openGraph_mono (blockConfig_mono x ξ (le_max_left N _))) hN
      have h2 : (openGraph (blockConfig N' x ξ)).Adj b c := by
        rw [openGraph_adj_iff]
        refine ⟨⟨m, le_max_of_le_right (le_max_left _ _), hm, fun v hv => ?_⟩, hbc⟩
        rw [mem_block]
        rcases Sym2.mem_iff.mp hv with h | h <;> rw [h, hN'] <;> omega
      exact h1.trans h2.reachable

end PercLib.Models.HierarchicalLayers
