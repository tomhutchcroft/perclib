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
(translated hierarchical decomposition), with the digit weight `L^{m-1}`.
-/
module

public import PercLib.Models.HierarchicalComparison.Defs
public import PercLib.Models.LongRange.OmittedLayer

/-!
# Translated hierarchical edge layers on `ℤ^d`

Properties of the digit hierarchies and hierarchical layers of
`PercLib.Models.HierarchicalComparison.Defs`.

## Main results

* `blockIndex_succ`, `blockIndex_eq_of_le`: the partitions are nested.
* `card_image_blockIndex_block_succ`: every block has `L^d` children.
* `exists_blockIndex_add_iff`: translates of a hierarchy are hierarchies.
* `norm_sub_lt_of_blockIndex_eq`: a level-`n` block has `ℓ^∞` diameter less than `L^n`.
* `layerKernel_le`: `H_σ ≤ J` under the power-law lower envelope.
* `law_intensityProfile_eq_map_union_layerKernel`: the bond law is the union of independent
  hierarchical and remainder configurations.
* `blockLayerKernel_succ_apply`: the layer of a block opens pairs in different children.
* `restrictedKernel_succ`, `law_restrictedKernel_succ`: `η_P = η_B ∪ ω_P`.
* `restrictedKernel_eq_of_blockIndex_succ_eq`: siblings have the same restricted
  configuration.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal
open MeasureTheory PercLib.Percolation.Bond

namespace PercLib.Models

namespace DigitHierarchy

variable {d L : ℕ} (σ : DigitHierarchy d L)

theorem offset_zero : σ.offset 0 = 0 := by
  funext i; simp [offset]

theorem offset_succ (n : ℕ) (i : Fin d) :
    σ.offset (n + 1) i = σ.offset n i + (L : ℤ) ^ n * (σ.digit n i : ℤ) := by
  simp [offset, Finset.sum_range_succ]

variable [NeZero L]

/-- The block index one level up: `k_{n+1} = ⌊(k_n - σ_n) / L⌋`. -/
theorem blockIndex_succ (n : ℕ) (x : Fin d → ℤ) (i : Fin d) :
    σ.blockIndex (n + 1) x i = (σ.blockIndex n x i - σ.digit n i) / L := by
  have hp : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) n
  simp only [blockIndex, offset_succ]
  rw [pow_succ, ← Int.ediv_ediv_of_nonneg hp.le,
    show x i - (σ.offset n i + (L : ℤ) ^ n * (σ.digit n i : ℤ)) =
      x i - σ.offset n i + (L : ℤ) ^ n * (-(σ.digit n i : ℤ)) by ring,
    Int.add_mul_ediv_left _ _ hp.ne', ← sub_eq_add_neg]

/-- Nestedness: vertices in a common level-`n` block share their level-`(n+1)` block. -/
theorem blockIndex_succ_eq_of_eq {n : ℕ} {x y : Fin d → ℤ}
    (h : σ.blockIndex n x = σ.blockIndex n y) :
    σ.blockIndex (n + 1) x = σ.blockIndex (n + 1) y := by
  funext i; rw [blockIndex_succ, blockIndex_succ, h]

theorem blockIndex_eq_of_le {m n : ℕ} (hmn : m ≤ n) {x y : Fin d → ℤ}
    (h : σ.blockIndex m x = σ.blockIndex m y) : σ.blockIndex n x = σ.blockIndex n y := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact σ.blockIndex_succ_eq_of_eq ih

theorem block_eq_of_le {m n : ℕ} (hmn : m ≤ n) {x z : Fin d → ℤ} (hx : x ∈ σ.block m z) :
    x ∈ σ.block n z :=
  σ.mem_block.2 (σ.blockIndex_eq_of_le hmn (σ.mem_block.1 hx))

omit [NeZero L] in
theorem blockIndex_childHierarchy (n : ℕ) (k : Fin d → ℤ) (i : Fin d) :
    (σ.childHierarchy n).blockIndex 1 k i = (k i - σ.digit n i) / L := by
  simp [blockIndex, offset, childHierarchy]

/-- Every level-`(n+1)` block has exactly `L^d` children. -/
theorem card_image_blockIndex_block_succ (n : ℕ) (z : Fin d → ℤ) :
    ((σ.block (n + 1) z).image (σ.blockIndex n)).card = L ^ d := by
  have hp : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) n
  have himage : (σ.block (n + 1) z).image (σ.blockIndex n) =
      (σ.childHierarchy n).block 1 (σ.blockIndex n z) := by
    ext k
    rw [Finset.mem_image, mem_block]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := σ.mem_block.1 hy
      funext i
      rw [blockIndex_childHierarchy, blockIndex_childHierarchy, ← blockIndex_succ,
        ← blockIndex_succ, this]
    · intro hk
      refine ⟨fun i => σ.offset n i + (L : ℤ) ^ n * k i, ?_, ?_⟩
      · have hy : σ.blockIndex n (fun i => σ.offset n i + (L : ℤ) ^ n * k i) = k := by
          funext i
          simp only [blockIndex, add_sub_cancel_left]
          exact Int.mul_ediv_cancel_left _ hp.ne'
        rw [mem_block]
        funext i
        rw [blockIndex_succ, blockIndex_succ, hy, ← blockIndex_childHierarchy, hk,
          blockIndex_childHierarchy]
      · funext i
        simp only [blockIndex, add_sub_cancel_left]
        exact Int.mul_ediv_cancel_left _ hp.ne'
  rw [himage, card_block, pow_one]

/-- Vertices in a common level-`n` block differ by less than `L^n` in every coordinate. -/
theorem abs_sub_lt_of_blockIndex_eq {n : ℕ} {x y : Fin d → ℤ}
    (h : σ.blockIndex n x = σ.blockIndex n y) (i : Fin d) : |x i - y i| < (L : ℤ) ^ n := by
  have hp : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) n
  have hi := congrFun h i
  simp only [blockIndex] at hi
  have hx := Int.emod_add_mul_ediv (x i - σ.offset n i) ((L : ℤ) ^ n)
  have hy := Int.emod_add_mul_ediv (y i - σ.offset n i) ((L : ℤ) ^ n)
  have h1 := Int.emod_nonneg (x i - σ.offset n i) hp.ne'
  have h2 := Int.emod_lt_of_pos (x i - σ.offset n i) hp
  have h3 := Int.emod_nonneg (y i - σ.offset n i) hp.ne'
  have h4 := Int.emod_lt_of_pos (y i - σ.offset n i) hp
  rw [hi] at hx
  rw [abs_lt]
  constructor <;> linarith

/-- A level-`n` block has `ℓ^∞` diameter less than `L^n`. -/
theorem norm_sub_lt_of_blockIndex_eq {n : ℕ} {x y : Fin d → ℤ}
    (h : σ.blockIndex n x = σ.blockIndex n y) : ‖x - y‖ < (L : ℝ) ^ n := by
  rw [pi_norm_lt_iff (pow_pos (by exact_mod_cast NeZero.pos L) n)]
  intro i
  rw [Pi.sub_apply, Int.norm_eq_abs]
  exact_mod_cast σ.abs_sub_lt_of_blockIndex_eq h i

omit [NeZero L] in
theorem one_le_norm_sub {x y : Fin d → ℤ} (h : x ≠ y) : 1 ≤ ‖x - y‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  calc (1 : ℝ) ≤ |((x i - y i : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hi)
    _ = ‖(x - y) i‖ := by rw [Pi.sub_apply, Int.norm_eq_abs]
    _ ≤ ‖x - y‖ := norm_le_pi_norm _ i

/-- Under the lower envelope `J(x, y) ≥ c ‖x - y‖_∞^{-s}` (`s ≥ 0`), the hierarchical kernel
is dominated: `H_σ ≤ J`. -/
theorem layerKernel_le {J : Sym2 (Fin d → ℤ) → ℝ≥0} {c : ℝ≥0} {s : ℝ} (hs : 0 ≤ s)
    (hJ : ∀ x y : Fin d → ℤ, x ≠ y → (c : ℝ) * ‖x - y‖ ^ (-s) ≤ J s(x, y)) :
    σ.layerKernel c s ≤ J := by
  intro e
  induction e using Sym2.ind with
  | _ x y =>
  rw [layerKernel_apply]
  split_ifs with hxy
  · exact bot_le
  by_cases hk : σ.commonLevel x y = ⊤
  · rw [hk, layerWeight_top]; exact bot_le
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hk
  have hn' : σ.commonLevel x y = n := hn.symm
  rw [hn', layerWeight_coe, ← NNReal.coe_le_coe]
  refine le_trans ?_ (hJ x y hxy)
  have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hlt := σ.norm_sub_lt_of_blockIndex_eq (σ.blockIndex_eq_of_commonLevel_eq hn')
  have h1 := one_le_norm_sub hxy
  push_cast
  rw [show -(s * (n : ℝ)) = (n : ℝ) * -s by ring, Real.rpow_mul hL.le, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos h1) hlt.le (neg_nonpos.2 hs)) c.coe_nonneg

omit [NeZero L] in
/-- The bond law of `J` is the law of the union of independent configurations with kernels
`H_σ` and `R_σ = J - H_σ`, whenever `H_σ ≤ J`. -/
theorem law_intensityProfile_eq_map_union_layerKernel {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    {c : ℝ≥0} {s : ℝ} (hHJ : σ.layerKernel c s ≤ J) (β : ℝ≥0) :
    law (intensityProfile J β) =
      ((law (intensityProfile (σ.layerKernel c s) β)).prod
        (law (intensityProfile (J - σ.layerKernel c s) β))).map (fun ω => ω.1 ∪ ω.2) := by
  rw [← LongRange.law_intensityProfile_add_kernel]
  congr 2
  funext e
  exact (add_tsub_cancel_of_le (hHJ e)).symm

/-- The layer of the level-`(m+1)` block `B` of `z` opens exactly the pairs of `B` lying in
different children, with intensity `c L^{-s(m+1)}`. -/
theorem blockLayerKernel_succ_apply (c : ℝ≥0) (s : ℝ) (m : ℕ) (z x y : Fin d → ℤ) :
    σ.blockLayerKernel c s (m + 1) z s(x, y) =
      if x ∈ σ.block (m + 1) z ∧ y ∈ σ.block (m + 1) z ∧ σ.blockIndex m x ≠ σ.blockIndex m y
      then c * (L : ℝ≥0) ^ (-(s * ((m + 1 : ℕ) : ℝ))) else 0 := by
  classical
  rw [blockLayerKernel_apply]
  by_cases hB : σ.InBlockLayer (m + 1) z x y
  · obtain ⟨hl, hb⟩ := hB
    have hne : σ.blockIndex m x ≠ σ.blockIndex m y :=
      σ.blockIndex_ne_of_lt_commonLevel (by rw [hl]; exact_mod_cast Nat.lt_succ_self m)
    have hxy : x ≠ y := fun h => hne (by rw [h])
    have hy : y ∈ σ.block (m + 1) z := σ.mem_block.2
      ((σ.blockIndex_eq_of_commonLevel_eq hl).symm.trans hb)
    rw [ite_eq_left ⟨hl, hb⟩, ite_eq_left ⟨σ.mem_block.2 hb, hy, hne⟩, layerKernel_apply,
      ite_eq_right hxy, hl, layerWeight_coe]
  · rw [ite_eq_right hB, ite_eq_right]
    rintro ⟨hx, hy, hne⟩
    apply hB
    have hxy := (σ.mem_block.1 hx).trans (σ.mem_block.1 hy).symm
    have hle := σ.commonLevel_le hxy
    have hge : ((m + 1 : ℕ) : ℕ∞) ≤ σ.commonLevel x y := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hkm : k ≤ m := by
        rw [← hk] at hlt; have := (Nat.cast_lt (α := ℕ∞)).1 hlt; omega
      exact hne (σ.blockIndex_eq_of_le hkm (σ.blockIndex_eq_of_commonLevel_eq hk.symm))
    exact ⟨le_antisymm hle hge, σ.mem_block.1 hx⟩

omit [NeZero L] in
theorem ancestorKernel_le_layerKernel (c : ℝ≥0) (s : ℝ) (n : ℕ) (z : Fin d → ℤ) :
    σ.ancestorKernel c s n z ≤ σ.layerKernel c s := by
  intro e
  induction e using Sym2.ind with
  | _ x y =>
  classical
  rw [ancestorKernel_apply]
  split_ifs
  · exact le_rfl
  · exact bot_le

omit [NeZero L] in
/-- The strict-ancestor layers of a block are those of its parent's strict ancestors and the
parent's own layer. -/
theorem ancestorKernel_eq_add (c : ℝ≥0) (s : ℝ) (n : ℕ) (z : Fin d → ℤ) :
    σ.ancestorKernel c s n z =
      σ.ancestorKernel c s (n + 1) z + σ.blockLayerKernel c s (n + 1) z := by
  classical
  funext e
  induction e using Sym2.ind with
  | _ x y =>
  rw [Pi.add_apply, ancestorKernel_apply, ancestorKernel_apply, blockLayerKernel_apply]
  by_cases h1 : σ.InStrictAncestor (n + 1) z x y
  · have h0 : σ.InStrictAncestor n z x y := by
      obtain ⟨m, hm, hl, hb⟩ := h1; exact ⟨m, by omega, hl, hb⟩
    have h2 : ¬σ.InBlockLayer (n + 1) z x y := by
      obtain ⟨m, hm, hl, _⟩ := h1
      rintro ⟨hl', _⟩
      rw [hl] at hl'
      have : m = n + 1 := by exact_mod_cast hl'
      omega
    rw [ite_eq_left h0, ite_eq_left h1, ite_eq_right h2, add_zero]
  · rw [ite_eq_right h1, zero_add]
    by_cases h2 : σ.InBlockLayer (n + 1) z x y
    · rw [ite_eq_left h2, ite_eq_left ⟨n + 1, Nat.lt_succ_self n, h2.1, h2.2⟩]
    · rw [ite_eq_right h2, ite_eq_right]
      rintro ⟨m, hm, hl, hb⟩
      rcases Nat.lt_or_ge (n + 1) m with h | h
      · exact h1 ⟨m, h, hl, hb⟩
      · have : m = n + 1 := by omega
        subst this
        exact h2 ⟨hl, hb⟩

omit [NeZero L] in
/-- `η_P = η_B ∪ ω_P` at the level of kernels: the restricted kernel of the parent is that of
the child plus the parent layer, whenever `H_σ ≤ J`. -/
theorem restrictedKernel_succ {J : Sym2 (Fin d → ℤ) → ℝ≥0} {c : ℝ≥0} {s : ℝ}
    (hHJ : σ.layerKernel c s ≤ J) (n : ℕ) (z : Fin d → ℤ) :
    σ.restrictedKernel J c s (n + 1) z =
      σ.restrictedKernel J c s n z + σ.blockLayerKernel c s (n + 1) z := by
  funext e
  have hle : σ.ancestorKernel c s (n + 1) z e + σ.blockLayerKernel c s (n + 1) z e ≤ J e := by
    have := (σ.ancestorKernel_le_layerKernel c s n z).trans hHJ e
    rwa [ancestorKernel_eq_add, Pi.add_apply] at this
  simp only [Pi.add_apply, restrictedKernel_apply, σ.ancestorKernel_eq_add c s n z]
  rw [tsub_add_eq_tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hle)]

omit [NeZero L] in
/-- `η_P = η_B ∪ ω_P` in law: the restricted configuration of the parent is the union of the
child's restricted configuration and the independent parent layer. -/
theorem law_restrictedKernel_succ {J : Sym2 (Fin d → ℤ) → ℝ≥0} {c : ℝ≥0} {s : ℝ}
    (hHJ : σ.layerKernel c s ≤ J) (β : ℝ≥0) (n : ℕ) (z : Fin d → ℤ) :
    law (intensityProfile (σ.restrictedKernel J c s (n + 1) z) β) =
      ((law (intensityProfile (σ.restrictedKernel J c s n z) β)).prod
        (law (intensityProfile (σ.blockLayerKernel c s (n + 1) z) β))).map
          (fun ω => ω.1 ∪ ω.2) := by
  rw [← LongRange.law_intensityProfile_add_kernel, σ.restrictedKernel_succ hHJ]

/-- Siblings have the same restricted configuration: the restricted kernel of a level-`n`
block depends only on its parent. -/
theorem restrictedKernel_eq_of_blockIndex_succ_eq (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0)
    (s : ℝ) {n : ℕ} {z z' : Fin d → ℤ}
    (h : σ.blockIndex (n + 1) z = σ.blockIndex (n + 1) z') :
    σ.restrictedKernel J c s n z = σ.restrictedKernel J c s n z' := by
  classical
  have hA : σ.ancestorKernel c s n z = σ.ancestorKernel c s n z' := by
    funext e
    induction e using Sym2.ind with
    | _ x y =>
    rw [ancestorKernel_apply, ancestorKernel_apply]
    have hiff : σ.InStrictAncestor n z x y ↔ σ.InStrictAncestor n z' x y := by
      constructor <;> rintro ⟨m, hm, hl, hb⟩ <;> refine ⟨m, hm, hl, ?_⟩
      · rw [hb, σ.blockIndex_eq_of_le (Nat.succ_le_of_lt hm) h]
      · rw [hb, σ.blockIndex_eq_of_le (Nat.succ_le_of_lt hm) h.symm]
    simp only [hiff]
  simp only [restrictedKernel, hA]

theorem offset_translate (x : Fin d → ℤ) (n : ℕ) (i : Fin d) :
    (σ.translate x).offset n i = (σ.offset n i + x i) % (L : ℤ) ^ n := by
  induction n with
  | zero => simp [offset]
  | succ n ih =>
    have hp : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) n
    have hp1 : (0 : ℤ) < (L : ℤ) ^ (n + 1) := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) (n + 1)
    rw [offset_succ, ih]
    have h0 : 0 ≤ (σ.offset (n + 1) i + x i) % (L : ℤ) ^ (n + 1) / (L : ℤ) ^ n :=
      Int.ediv_nonneg (Int.emod_nonneg _ hp1.ne') hp.le
    have hd : ((σ.translate x).digit n i : ℤ) =
        (σ.offset (n + 1) i + x i) % (L : ℤ) ^ (n + 1) / (L : ℤ) ^ n := by
      simp only [translate]
      exact Int.toNat_of_nonneg h0
    rw [hd]
    have hdvd : (L : ℤ) ^ n ∣ (L : ℤ) ^ (n + 1) := pow_dvd_pow _ (Nat.le_succ n)
    have h1 := Int.emod_add_mul_ediv ((σ.offset (n + 1) i + x i) % (L : ℤ) ^ (n + 1))
      ((L : ℤ) ^ n)
    rw [Int.emod_emod_of_dvd _ hdvd, offset_succ,
      show σ.offset n i + (L : ℤ) ^ n * (σ.digit n i : ℤ) + x i =
        σ.offset n i + x i + (L : ℤ) ^ n * (σ.digit n i : ℤ) by ring,
      Int.add_mul_emod_self_left] at h1
    rw [offset_succ, show σ.offset n i + (L : ℤ) ^ n * (σ.digit n i : ℤ) + x i =
        σ.offset n i + x i + (L : ℤ) ^ n * (σ.digit n i : ℤ) by ring] at *
    linarith

theorem blockIndex_translate_add (x : Fin d → ℤ) (n : ℕ) (u : Fin d → ℤ) :
    (σ.translate x).blockIndex n (u + x) =
      σ.blockIndex n u + fun i => (σ.offset n i + x i) / (L : ℤ) ^ n := by
  have hp : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) n
  funext i
  simp only [blockIndex, offset_translate, Pi.add_apply]
  have h := Int.emod_add_mul_ediv (σ.offset n i + x i) ((L : ℤ) ^ n)
  rw [show u i + x i - (σ.offset n i + x i) % (L : ℤ) ^ n =
      u i - σ.offset n i + (L : ℤ) ^ n * ((σ.offset n i + x i) / (L : ℤ) ^ n) by linarith,
    Int.add_mul_ediv_left _ _ hp.ne']

/-- Translation closure: the partitions of `σ` translated by `x` are those of another digit
hierarchy. -/
theorem exists_blockIndex_add_iff (x : Fin d → ℤ) :
    ∃ τ : DigitHierarchy d L, ∀ n (u v : Fin d → ℤ),
      τ.blockIndex n (u + x) = τ.blockIndex n (v + x) ↔ σ.blockIndex n u = σ.blockIndex n v :=
  ⟨σ.translate x, fun n u v => by
    rw [blockIndex_translate_add, blockIndex_translate_add, add_left_inj]⟩

end DigitHierarchy

end PercLib.Models
