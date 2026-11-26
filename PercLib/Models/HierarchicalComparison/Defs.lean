/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions on this library's bond-percolation interface and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied.
Mathematical reference: T. Hutchcroft, *Sharp hierarchical upper bounds on the critical
two-point function for long-range percolation on ℤ^d*, arXiv:2202.07634v2, Section 2
(translated hierarchical decomposition, good blocks), with the digit weight `L^{m-1}`.
-/
module

public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.Tightness.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ENat.Basic

/-!
# Translated hierarchical edge layers and good blocks (definitions)

A *digit hierarchy* `σ` on `ℤ^d = Fin d → ℤ` with base `L` is a sequence of digits
`σ_m ∈ {0, …, L - 1}^d`. Its offsets are `t_n = ∑_{m < n} L^m σ_m` (the digit `σ.digit m` is the
source's `σ_{m+1}`), and its level-`n` blocks are the translates `t_n + L^n k + {0, …, L^n-1}^d`.

## Main definitions

* `DigitHierarchy d L`: digit sequences; `DigitHierarchy.offset σ n`: `t_n`.
* `σ.blockIndex n x`: the index `k` of the level-`n` block of `x`, `⌊(x - t_n) / L^n⌋`.
* `σ.block n z`: the level-`n` block containing `z`, as a finset.
* `σ.commonLevel x y : ℕ∞`: the first level at which `x` and `y` share a block (`⊤` if none).
* `layerWeight L c s k`: `c L^{-s k}`, with `L^{-∞} = 0`.
* `σ.layerKernel c s`: `H_σ(x, y) = c L^{-s h_σ(x, y)}` off the diagonal.
* `σ.blockLayerKernel c s m z`: the kernel of the layer `ω_B` of the block `B` of `z` at level
  `m`: `H_σ` on pairs whose first common block is `B`.
* `σ.ancestorKernel c s n z`: `H_σ` on pairs whose first common block is a strict ancestor of
  the level-`n` block of `z`.
* `σ.restrictedKernel J c s n z`: `J` minus the strict-ancestor layers, the kernel of `η_B`.
* `σ.expectedBlockMax`, `σ.blockScale`, `σ.blockPairSum`: `E Z_B`, `M_B` and `S_B` at
  intensity `β`.
* `σ.IsGoodBlock`, `σ.IsAncestrallyGood`: good and ancestrally good blocks.
* `σ.childHierarchy n`: the one-digit hierarchy whose level-`1` blocks index the children of
  the level-`(n+1)` blocks of `σ`.
* `σ.translate x`: the hierarchy whose offsets are `t_n + x` modulo `L^n`.

## Main results

* `mem_block`, `card_block`: the block is `{x | blockIndex x = blockIndex z}` and has
  `(L^n)^d` points.
* `commonLevel_comm`, `commonLevel_le`, `blockIndex_eq_of_commonLevel_eq`,
  `blockIndex_ne_of_lt_commonLevel`: the first common level.
* `layerKernel_apply`, `blockLayerKernel_apply`, `ancestorKernel_apply`,
  `restrictedKernel_apply`: evaluation of the kernels.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal
open MeasureTheory PercLib.Percolation.Bond

namespace PercLib.Models

/-- A digit hierarchy on `ℤ^d` with base `L`: the digit `digit m ∈ {0, …, L-1}^d` has weight
`L^m` in the offsets. -/
structure DigitHierarchy (d L : ℕ) where
  /-- The digit of weight `L^m`. -/
  digit : ℕ → Fin d → Fin L

namespace DigitHierarchy

variable {d L : ℕ} (σ : DigitHierarchy d L)

/-- The offset `t_n = ∑_{m < n} L^m σ_m` of the level-`n` partition. -/
def offset (n : ℕ) : Fin d → ℤ := fun i => ∑ m ∈ Finset.range n, (L : ℤ) ^ m * (σ.digit m i : ℤ)

/-- The index `⌊(x - t_n) / L^n⌋` of the level-`n` block containing `x`. -/
def blockIndex (n : ℕ) (x : Fin d → ℤ) : Fin d → ℤ := fun i => (x i - σ.offset n i) / (L : ℤ) ^ n

/-- The corner `t_n + L^n k` of the level-`n` block with index `k`. -/
def blockCorner (n : ℕ) (k : Fin d → ℤ) : Fin d → ℤ := fun i => σ.offset n i + (L : ℤ) ^ n * k i

theorem blockCorner_apply (n : ℕ) (k : Fin d → ℤ) (i : Fin d) :
    σ.blockCorner n k i = σ.offset n i + (L : ℤ) ^ n * k i := rfl

/-- The level-`n` block `t_n + L^n k + {0, …, L^n-1}^d` containing `z`. -/
def block (n : ℕ) (z : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Ico (0 : ℤ) ((L : ℤ) ^ n)).image
    fun r i => σ.offset n i + (L : ℤ) ^ n * σ.blockIndex n z i + r i

open Classical in
/-- The first level `h_σ(x, y)` at which `x` and `y` lie in a common block, `⊤` if there is
none. -/
def commonLevel (x y : Fin d → ℤ) : ℕ∞ :=
  if h : ∃ n, σ.blockIndex n x = σ.blockIndex n y then (Nat.find h : ℕ∞) else ⊤

/-- The weight `c L^{-s k}` of a pair with first common level `k`, with `L^{-∞} = 0`. -/
def layerWeight (L : ℕ) (c : ℝ≥0) (s : ℝ) (k : ℕ∞) : ℝ≥0 :=
  if k = ⊤ then 0 else c * (L : ℝ≥0) ^ (-(s * (k.toNat : ℝ)))

/-- Strict-ancestor predicate: the first common block of `x` and `y` is a strict ancestor of
the level-`n` block of `z`. -/
def InStrictAncestor (n : ℕ) (z x y : Fin d → ℤ) : Prop :=
  ∃ m : ℕ, n < m ∧ σ.commonLevel x y = m ∧ σ.blockIndex m x = σ.blockIndex m z

/-- Block predicate: the first common block of `x` and `y` is the level-`m` block of `z`. -/
def InBlockLayer (m : ℕ) (z x y : Fin d → ℤ) : Prop :=
  σ.commonLevel x y = m ∧ σ.blockIndex m x = σ.blockIndex m z

theorem commonLevel_comm (x y : Fin d → ℤ) : σ.commonLevel x y = σ.commonLevel y x := by
  classical
  unfold commonLevel
  have he : (∃ n, σ.blockIndex n x = σ.blockIndex n y) ↔ ∃ n, σ.blockIndex n y = σ.blockIndex n x :=
    exists_congr fun _ => eq_comm
  by_cases h : ∃ n, σ.blockIndex n x = σ.blockIndex n y
  · have h' := he.1 h
    simp only [h, h', ↓reduceDIte]
    congr 1
    exact_mod_cast (Nat.find_congr' fun {_} => eq_comm)
  · have h' : ¬∃ n, σ.blockIndex n y = σ.blockIndex n x := fun h' => h (he.2 h')
    simp only [h, h', ↓reduceDIte]

theorem commonLevel_le {x y : Fin d → ℤ} {n : ℕ} (h : σ.blockIndex n x = σ.blockIndex n y) :
    σ.commonLevel x y ≤ n := by
  classical
  have he : ∃ n, σ.blockIndex n x = σ.blockIndex n y := ⟨n, h⟩
  simp only [commonLevel, he, ↓reduceDIte]
  exact_mod_cast Nat.find_min' he h

theorem blockIndex_eq_of_commonLevel_eq {x y : Fin d → ℤ} {n : ℕ}
    (h : σ.commonLevel x y = n) : σ.blockIndex n x = σ.blockIndex n y := by
  classical
  unfold commonLevel at h
  split_ifs at h with he
  · rw [← (Nat.cast_inj (R := ℕ∞)).1 h]
    exact Nat.find_spec he
  · exact absurd h.symm (ENat.natCast_ne_top n)

theorem blockIndex_ne_of_lt_commonLevel {x y : Fin d → ℤ} {n : ℕ}
    (h : (n : ℕ∞) < σ.commonLevel x y) : σ.blockIndex n x ≠ σ.blockIndex n y :=
  fun he => (σ.commonLevel_le he).not_gt h

theorem inStrictAncestor_comm (n : ℕ) (z x y : Fin d → ℤ) :
    σ.InStrictAncestor n z x y ↔ σ.InStrictAncestor n z y x := by
  constructor <;> rintro ⟨m, hm, hl, hb⟩ <;> refine ⟨m, hm, ?_, ?_⟩
  · rwa [commonLevel_comm]
  · rw [← σ.blockIndex_eq_of_commonLevel_eq hl, hb]
  · rwa [commonLevel_comm]
  · rw [← σ.blockIndex_eq_of_commonLevel_eq hl, hb]

theorem inBlockLayer_comm (m : ℕ) (z x y : Fin d → ℤ) :
    σ.InBlockLayer m z x y ↔ σ.InBlockLayer m z y x := by
  constructor <;> rintro ⟨hl, hb⟩ <;> refine ⟨?_, ?_⟩
  · rwa [commonLevel_comm]
  · rw [← σ.blockIndex_eq_of_commonLevel_eq hl, hb]
  · rwa [commonLevel_comm]
  · rw [← σ.blockIndex_eq_of_commonLevel_eq hl, hb]

open Classical in
/-- The hierarchical kernel `H_σ(x, y) = c L^{-s h_σ(x, y)}` on distinct vertices, `0` on the
diagonal. -/
def layerKernel (c : ℝ≥0) (s : ℝ) : Sym2 (Fin d → ℤ) → ℝ≥0 :=
  Sym2.lift ⟨fun x y => if x = y then 0 else layerWeight L c s (σ.commonLevel x y),
    fun x y => by simp only [eq_comm (a := x), commonLevel_comm]⟩

open Classical in
/-- The kernel of the layer `ω_B` of the level-`m` block `B` of `z`: `H_σ` on the pairs whose
first common block is `B`, and `0` elsewhere. -/
def blockLayerKernel (c : ℝ≥0) (s : ℝ) (m : ℕ) (z : Fin d → ℤ) : Sym2 (Fin d → ℤ) → ℝ≥0 :=
  Sym2.lift ⟨fun x y => if σ.InBlockLayer m z x y then σ.layerKernel c s s(x, y) else 0,
    fun x y => by simp only [inBlockLayer_comm σ m z x y, Sym2.eq_swap]⟩

open Classical in
/-- `H_σ` restricted to the pairs whose first common block is a strict ancestor of the
level-`n` block of `z`: the union of the layers `ω_P` over strict ancestors `P`. -/
def ancestorKernel (c : ℝ≥0) (s : ℝ) (n : ℕ) (z : Fin d → ℤ) : Sym2 (Fin d → ℤ) → ℝ≥0 :=
  Sym2.lift ⟨fun x y => if σ.InStrictAncestor n z x y then σ.layerKernel c s s(x, y) else 0,
    fun x y => by simp only [inStrictAncestor_comm σ n z x y, Sym2.eq_swap]⟩

/-- The kernel of the restricted configuration `η_B` of the level-`n` block `B` of `z`: the
union of `ω_R` and every hierarchical layer except those of strict ancestors of `B`. When
`H_σ ≤ J` this is `R_σ + H_σ - (strict-ancestor layers)`. -/
def restrictedKernel (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (n : ℕ)
    (z : Fin d → ℤ) : Sym2 (Fin d → ℤ) → ℝ≥0 :=
  J - σ.ancestorKernel c s n z

/-- `E Z_B`: the expected largest intersection `max_x |K_B(x) ∩ B|` of a restricted cluster
with the level-`n` block `B` of `z`, at intensity `β`. -/
def expectedBlockMax (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (β : ℝ≥0) (n : ℕ)
    (z : Fin d → ℤ) : ℝ≥0∞ :=
  ∫⁻ ω, (maxClusterIntersection (σ.block n z) ω : ℝ≥0∞)
    ∂law (intensityProfile (σ.restrictedKernel J c s n z) β)

/-- `M_B = min {m ≥ 1 : P(Z_B ≥ m) ≤ e⁻¹}` for the level-`n` block of `z`, at intensity `β`. -/
def blockScale (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (β : ℝ≥0) (n : ℕ)
    (z : Fin d → ℤ) : ℕ :=
  tightnessScale (intensityProfile (σ.restrictedKernel J c s n z) β) (σ.block n z)

/-- `S_B = ∑_{x, y ∈ B} P(x ↔ y in η_B)` for the level-`n` block `B` of `z`, at intensity
`β`. -/
def blockPairSum (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (β : ℝ≥0) (n : ℕ)
    (z : Fin d → ℤ) : ℝ≥0∞ :=
  ∑ x ∈ σ.block n z, ∑ y ∈ σ.block n z,
    tau (intensityProfile (σ.restrictedKernel J c s n z) β) x y

open Classical in
/-- The level-`n` block `B` of `z` is *good* (at intensity `β`): at least `⌊L^d / 2⌋ - 1` of
its siblings `B'` have `E Z_{B'} ≥ E Z_B`, and some sibling `B'` has `S_{B'} ≥ S_B`. Siblings
are counted by block index; the sibling of `y` is the level-`n` block of `y`. -/
def IsGoodBlock (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (β : ℝ≥0) (n : ℕ)
    (z : Fin d → ℤ) : Prop :=
  L ^ d / 2 - 1 ≤
      (((σ.block (n + 1) z).filter fun y => σ.blockIndex n y ≠ σ.blockIndex n z ∧
          σ.expectedBlockMax J c s β n z ≤ σ.expectedBlockMax J c s β n y).image
        (σ.blockIndex n)).card ∧
    ∃ y ∈ σ.block (n + 1) z, σ.blockIndex n y ≠ σ.blockIndex n z ∧
      σ.blockPairSum J c s β n z ≤ σ.blockPairSum J c s β n y

/-- The level-`n` block of `z` is *ancestrally good*: it and every strict ancestor are good. -/
def IsAncestrallyGood (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (β : ℝ≥0) (n : ℕ)
    (z : Fin d → ℤ) : Prop :=
  ∀ m, n ≤ m → σ.IsGoodBlock J c s β m z

/-- The digit hierarchy with the single digit `σ_n`; its level-`1` blocks are the children of
the level-`(n+1)` blocks of `σ`, indexed by `blockIndex n`. -/
def childHierarchy (n : ℕ) : DigitHierarchy d L := ⟨fun _ => σ.digit n⟩

/-! ### Basic API -/

@[simp] theorem layerWeight_top (c : ℝ≥0) (s : ℝ) : layerWeight L c s ⊤ = 0 := by
  simp [layerWeight]

@[simp] theorem layerWeight_coe (c : ℝ≥0) (s : ℝ) (n : ℕ) :
    layerWeight L c s n = c * (L : ℝ≥0) ^ (-(s * (n : ℝ))) := by
  simp [layerWeight]

theorem layerKernel_apply (c : ℝ≥0) (s : ℝ) (x y : Fin d → ℤ) :
    σ.layerKernel c s s(x, y) = if x = y then 0 else layerWeight L c s (σ.commonLevel x y) := by
  classical
  simp [layerKernel]

open Classical in
theorem blockLayerKernel_apply (c : ℝ≥0) (s : ℝ) (m : ℕ) (z x y : Fin d → ℤ) :
    σ.blockLayerKernel c s m z s(x, y) =
      if σ.InBlockLayer m z x y then σ.layerKernel c s s(x, y) else 0 := by
  classical
  simp [blockLayerKernel]

open Classical in
theorem ancestorKernel_apply (c : ℝ≥0) (s : ℝ) (n : ℕ) (z x y : Fin d → ℤ) :
    σ.ancestorKernel c s n z s(x, y) =
      if σ.InStrictAncestor n z x y then σ.layerKernel c s s(x, y) else 0 := by
  classical
  simp [ancestorKernel]

theorem restrictedKernel_apply (J : Sym2 (Fin d → ℤ) → ℝ≥0) (c : ℝ≥0) (s : ℝ) (n : ℕ)
    (z : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    σ.restrictedKernel J c s n z e = J e - σ.ancestorKernel c s n z e := rfl

variable [NeZero L]

/-- Membership in a block: `x` lies in the level-`n` block of `z` iff their block indices
agree. -/
theorem mem_block {n : ℕ} {z x : Fin d → ℤ} :
    x ∈ σ.block n z ↔ σ.blockIndex n x = σ.blockIndex n z := by
  have hp : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (by exact_mod_cast NeZero.pos L) n
  simp only [block, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Ico]
  constructor
  · rintro ⟨r, hr, rfl⟩
    funext i
    simp only [blockIndex]
    rw [show ∀ a k b : ℤ, a + (L : ℤ) ^ n * k + b - a = b + (L : ℤ) ^ n * k from
      fun _ _ _ => by ring, Int.add_mul_ediv_left _ _ hp.ne',
      Int.ediv_eq_zero_of_lt (hr i).1 (hr i).2, zero_add]
  · intro h
    refine ⟨fun i => (x i - σ.offset n i) % (L : ℤ) ^ n, fun i =>
      ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩, ?_⟩
    funext i
    have := Int.emod_add_mul_ediv (x i - σ.offset n i) ((L : ℤ) ^ n)
    rw [← h]
    simp only [blockIndex]
    linarith

theorem self_mem_block (n : ℕ) (z : Fin d → ℤ) : z ∈ σ.block n z := σ.mem_block.2 rfl

omit [NeZero L] in
/-- A level-`n` block has `(L^n)^d` points. -/
theorem card_block (n : ℕ) (z : Fin d → ℤ) : (σ.block n z).card = (L ^ n) ^ d := by
  rw [block, Finset.card_image_of_injective]
  · simp only [Fintype.card_piFinset, Int.card_Ico, sub_zero, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_pow, Int.toNat_natCast]
  · intro r r' h
    funext i
    have := congrFun h i
    simpa using this

/-- The translate of `σ` by `x`: its offsets are `t_n + x` reduced modulo `L^n`. -/
def translate (x : Fin d → ℤ) : DigitHierarchy d L :=
  ⟨fun m i => ⟨((σ.offset (m + 1) i + x i) % (L : ℤ) ^ (m + 1) / (L : ℤ) ^ m).toNat, by
    have hp : (0 : ℤ) < (L : ℤ) ^ m := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) m
    have hp1 : (0 : ℤ) < (L : ℤ) ^ (m + 1) := pow_pos (Int.natCast_pos.2 (NeZero.pos L)) (m + 1)
    have h0 : 0 ≤ (σ.offset (m + 1) i + x i) % (L : ℤ) ^ (m + 1) / (L : ℤ) ^ m :=
      Int.ediv_nonneg (Int.emod_nonneg _ hp1.ne') hp.le
    have h1 : (σ.offset (m + 1) i + x i) % (L : ℤ) ^ (m + 1) / (L : ℤ) ^ m < L := by
      refine Int.ediv_lt_of_lt_mul hp ?_
      rw [← pow_succ']
      exact Int.emod_lt_of_pos _ hp1
    omega⟩⟩

end DigitHierarchy

end PercLib.Models
