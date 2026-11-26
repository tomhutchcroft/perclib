/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions. Reference: T. Hutchcroft, *Critical cluster volumes in hierarchical
percolation*, arXiv:2211.05686 (the exact radial kernel and its block layers).
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.Basic

/-! # Block layers of the hierarchical lattice (definitions)

The lattice is `V = ℕ →₀ A` for an abelian group `A` (for the hierarchical lattice,
`A = Fin d → ZMod L`); the level of `z` is `h z = z.support.sup Nat.succ`. Two distinct
vertices first share a block at level `h(y - x)`.

* `pairLevel e`: the level `h(x, y) = h(y - x)` of the pair `e = s(x, y)`.
* `block n x`: the block of level `n` containing `x`, `{y | h(y - x) ≤ n}`.
* `IsCopy i`: the index `i = (m, e)` is a copy of a genuine pair `e` in its common block of
  level `m`, that is `e` is not a loop and `h(e) ≤ m`. Copies of `e` correspond to the blocks
  containing both endpoints, one per level `m ≥ h(e)`.
* `layerWeight L s i`: the weight `L^{-sm}` of a copy `i = (m, e)` (`0` for other indices), and
  `layerProfile L s β i = 1 - exp(-β L^{-sm})` the open probability of its layer edge.
* `openCopies L s β T`: the copies whose clock `T i` rings by the layer time `β L^{-sm}`.
* `fullConfig ξ`, `blockConfig n x ξ`, `ancestorConfig n x ξ`: the pairs with some open copy;
  with an open copy at a level `≤ n` inside `block n x` (the union `η_B` of the layers of the
  blocks inside `B = block n x`); with an open copy at a level `> n` inside `block n x`.
* `exactKernel L s`, `truncatedKernel L s n x`, `ancestorKernel L s n x`: the kernels
  `J_∞(x,y) = L^s/(L^s - 1) ‖x - y‖^{-s}` with `‖x - y‖ = L^{h(x,y)}`,
  `J_n(x,y) = ∑_{m=h(x,y)}^n L^{-sm}` on pairs of `block n x`, and the constant
  `L^{-sn}/(L^s - 1)` on pairs of `block n x`.
* `projFibre n y`: the fibre over `y` of the projection `π_n` keeping the coordinates below `n`.
* `periodicKernel L s n`: the periodic kernel `J_n^per(x,y) = ∑_{π_n z = y} J_∞(x,z)` on the
  pairs of `block n 0`.
* `completeKernel n x c`: the constant kernel `c` on the pairs of `block n x`.
-/

@[expose] public section
noncomputable section

open scoped NNReal ENNReal

namespace PercLib.Models.HierarchicalLayers

open PercLib.Percolation.Bond

variable {A : Type*} [AddCommGroup A]

/-- The level `h(x, y) = h(y - x)` of a pair. -/
def pairLevel : Sym2 (ℕ →₀ A) → ℕ :=
  Sym2.lift ⟨fun x y => (y - x).support.sup Nat.succ, fun x y => level_sub_comm x y⟩

@[simp] theorem pairLevel_mk (x y : ℕ →₀ A) :
    pairLevel s(x, y) = (y - x).support.sup Nat.succ := rfl

/-- The block of level `n` containing `x`. -/
def block (n : ℕ) (x : ℕ →₀ A) : Set (ℕ →₀ A) := {y | (y - x).support.sup Nat.succ ≤ n}

@[simp] theorem mem_block {n : ℕ} {x y : ℕ →₀ A} :
    y ∈ block n x ↔ (y - x).support.sup Nat.succ ≤ n := Iff.rfl

theorem mem_block_self (n : ℕ) (x : ℕ →₀ A) : x ∈ block n x := by simp

theorem block_mono {n m : ℕ} (h : n ≤ m) (x : ℕ →₀ A) : block n x ⊆ block m x :=
  fun _ hy => le_trans hy h

/-- `(m, e)` is a copy of the genuine pair `e` in its common block of level `m`. -/
def IsCopy (i : ℕ × Sym2 (ℕ →₀ A)) : Prop := ¬ i.2.IsDiag ∧ pairLevel i.2 ≤ i.1

theorem isCopy_iff (i : ℕ × Sym2 (ℕ →₀ A)) : IsCopy i ↔ ¬ i.2.IsDiag ∧ pairLevel i.2 ≤ i.1 :=
  Iff.rfl

open Classical in
/-- The weight `L^{-sm}` of a copy `(m, e)`, and `0` for other indices. -/
def layerWeight (L s : ℝ) (i : ℕ × Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if IsCopy i then (L ^ (-(s * i.1))).toNNReal else 0

theorem layerWeight_of_isCopy {L s : ℝ} {i : ℕ × Sym2 (ℕ →₀ A)} (hi : IsCopy i) :
    layerWeight L s i = (L ^ (-(s * i.1))).toNNReal := by
  classical
  simp [layerWeight, hi]

theorem layerWeight_of_not_isCopy {L s : ℝ} {i : ℕ × Sym2 (ℕ →₀ A)} (hi : ¬ IsCopy i) :
    layerWeight L s i = 0 := by
  classical
  simp [layerWeight, hi]

/-- The open probability `1 - exp(-β L^{-sm})` of the layer edge of a copy `(m, e)`. -/
def layerProfile (L s : ℝ) (β : ℝ≥0) (i : ℕ × Sym2 (ℕ →₀ A)) : unitInterval :=
  ⟨1 - Real.exp (-(β : ℝ) * layerWeight L s i), by
    constructor
    · apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr β.coe_nonneg) (layerWeight L s i).2
    · exact sub_le_self _ (Real.exp_pos _).le⟩

@[simp] theorem coe_layerProfile (L s : ℝ) (β : ℝ≥0) (i : ℕ × Sym2 (ℕ →₀ A)) :
    (layerProfile L s β i : ℝ) = 1 - Real.exp (-(β : ℝ) * layerWeight L s i) := rfl

/-- The copies whose rate-one clocks ring by the layer times `β L^{-sm}`. -/
def openCopies (L s β : ℝ) (T : ℕ × Sym2 (ℕ →₀ A) → ℝ) : Set (ℕ × Sym2 (ℕ →₀ A)) :=
  {i | i ∈ {i | IsCopy i} ∧ T i ≤ β * L ^ (-(s * i.1))}

@[simp] theorem mem_openCopies {L s β : ℝ} {T : ℕ × Sym2 (ℕ →₀ A) → ℝ}
    {i : ℕ × Sym2 (ℕ →₀ A)} :
    i ∈ openCopies L s β T ↔ IsCopy i ∧ T i ≤ β * L ^ (-(s * i.1)) := Iff.rfl

/-- The union of all layers: the pairs with some open copy. -/
def fullConfig (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) : Config (ℕ →₀ A) := {e | ∃ m, (m, e) ∈ ξ}

@[simp] theorem mem_fullConfig {ξ : Set (ℕ × Sym2 (ℕ →₀ A))} {e : Sym2 (ℕ →₀ A)} :
    e ∈ fullConfig ξ ↔ ∃ m, (m, e) ∈ ξ := Iff.rfl

/-- The union `η_B` of the layers of the blocks inside `B = block n x`: the pairs of `B` with an
open copy at a level `≤ n`. -/
def blockConfig (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) : Config (ℕ →₀ A) :=
  {e | ∃ m ≤ n, (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x}

@[simp] theorem mem_blockConfig {n : ℕ} {x : ℕ →₀ A} {ξ : Set (ℕ × Sym2 (ℕ →₀ A))}
    {e : Sym2 (ℕ →₀ A)} :
    e ∈ blockConfig n x ξ ↔ ∃ m ≤ n, (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x := Iff.rfl

/-- The layers of the strict ancestors of `B = block n x`, seen on the pairs of `B`. -/
def ancestorConfig (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) : Config (ℕ →₀ A) :=
  {e | ∃ m, n < m ∧ (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x}

@[simp] theorem mem_ancestorConfig {n : ℕ} {x : ℕ →₀ A} {ξ : Set (ℕ × Sym2 (ℕ →₀ A))}
    {e : Sym2 (ℕ →₀ A)} :
    e ∈ ancestorConfig n x ξ ↔ ∃ m, n < m ∧ (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x := Iff.rfl

open Classical in
/-- The exact radial kernel `J_∞(x,y) = L^s/(L^s - 1) (L^{h(x,y)})^{-s}`, `0` on loops. -/
def exactKernel (L s : ℝ) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if e.IsDiag then 0 else (L ^ s / (L ^ s - 1) * ((L ^ pairLevel e) ^ (-s))).toNNReal

theorem exactKernel_of_not_isDiag {L s : ℝ} {e : Sym2 (ℕ →₀ A)} (he : ¬ e.IsDiag) :
    exactKernel L s e = (L ^ s / (L ^ s - 1) * ((L ^ pairLevel e) ^ (-s))).toNNReal := by
  classical
  simp [exactKernel, he]

@[simp] theorem exactKernel_of_isDiag {L s : ℝ} {e : Sym2 (ℕ →₀ A)} (he : e.IsDiag) :
    exactKernel L s e = 0 := by
  classical
  simp [exactKernel, he]

open Classical in
/-- The truncated kernel `J_n(x,y) = ∑_{m=h(x,y)}^n L^{-sm}` on the pairs of `block n x`,
`0` elsewhere. -/
def truncatedKernel (L s : ℝ) (n : ℕ) (x : ℕ →₀ A) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x then
    (∑ m ∈ Finset.Icc (pairLevel e) n, L ^ (-(s * m))).toNNReal
  else 0

theorem truncatedKernel_of_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x) :
    truncatedKernel L s n x e = (∑ m ∈ Finset.Icc (pairLevel e) n, L ^ (-(s * m))).toNNReal := by
  classical
  rw [truncatedKernel, ite_eq_left_iff.mpr fun h => absurd he h]

theorem truncatedKernel_of_not_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ (¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x)) : truncatedKernel L s n x e = 0 := by
  classical
  rw [truncatedKernel, ite_eq_right_iff.mpr fun h => absurd h he]

open Classical in
/-- The kernel of the ancestor layers on `block n x`: `L^{-sn}/(L^s - 1)` on its pairs. -/
def ancestorKernel (L s : ℝ) (n : ℕ) (x : ℕ →₀ A) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x then (L ^ (-(s * n)) / (L ^ s - 1)).toNNReal else 0

theorem ancestorKernel_of_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x) :
    ancestorKernel L s n x e = (L ^ (-(s * n)) / (L ^ s - 1)).toNNReal := by
  classical
  rw [ancestorKernel, ite_eq_left_iff.mpr fun h => absurd he h]

theorem ancestorKernel_of_not_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ (¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x)) : ancestorKernel L s n x e = 0 := by
  classical
  rw [ancestorKernel, ite_eq_right_iff.mpr fun h => absurd h he]

/-! ### The periodic block kernel -/

/-- The fibre `{z | π_n z = y}` of the coordinate projection `π_n` that keeps the coordinates
below `n` and forgets the others. -/
def projFibre (n : ℕ) (y : ℕ →₀ A) : Set (ℕ →₀ A) := {z | z.filter (· < n) = y}

@[simp] theorem mem_projFibre {n : ℕ} {y z : ℕ →₀ A} :
    z ∈ projFibre n y ↔ z.filter (· < n) = y := Iff.rfl

/-- A vertex of `block n 0` is fixed by the projection `π_n`. -/
theorem filter_eq_self_of_mem_block {n : ℕ} {y : ℕ →₀ A} (hy : y ∈ block n 0) :
    y.filter (· < n) = y := by
  rw [Finsupp.filter_eq_self_iff]
  intro i hi
  have h := mem_block.mp hy
  rw [sub_zero] at h
  exact (level_le_iff_support y n).mp h i (Finsupp.mem_support_iff.mpr hi)

/-- The reflection `z ↦ x + y - z` maps the fibre over `y` onto the fibre over `x`. -/
def projFibreReflect {n : ℕ} {x y : ℕ →₀ A} (hx : x ∈ block n 0) (hy : y ∈ block n 0) :
    projFibre n y ≃ projFibre n x :=
  (Equiv.subLeft (x + y)).subtypeEquiv fun z => by
    simp only [mem_projFibre, Equiv.subLeft_apply, Finsupp.filter_sub, Finsupp.filter_add,
      filter_eq_self_of_mem_block hx, filter_eq_self_of_mem_block hy]
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      rw [sub_eq_iff_eq_add] at h
      exact (add_left_cancel h).symm

@[simp] theorem coe_projFibreReflect_apply {n : ℕ} {x y : ℕ →₀ A} (hx : x ∈ block n 0)
    (hy : y ∈ block n 0) (z : projFibre n y) :
    (projFibreReflect hx hy z : ℕ →₀ A) = x + y - z := rfl

/-- `J_∞` is invariant under the reflection `z ↦ x + y - z` exchanging `x` and `y`. -/
theorem exactKernel_mk_add_sub (L s : ℝ) (x y z : ℕ →₀ A) :
    exactKernel L s s(y, x + y - z) = exactKernel L s s(x, z) := by
  classical
  have hl : pairLevel s(y, x + y - z) = pairLevel s(x, z) := by
    simp only [pairLevel_mk]
    rw [show x + y - z - y = x - z by abel]
    exact level_sub_comm z x
  have hd : s(y, x + y - z).IsDiag ↔ s(x, z).IsDiag := by
    simp only [Sym2.mk_isDiag_iff]
    rw [eq_sub_iff_add_eq, add_comm y z, add_left_inj, eq_comm]
  simp only [exactKernel, hl, hd]

/-- The fibre sums defining the periodic kernel are symmetric in `x, y ∈ block n 0`. -/
theorem tsum_projFibre_exactKernel_comm (L s : ℝ) {n : ℕ} {x y : ℕ →₀ A}
    (hx : x ∈ block n 0) (hy : y ∈ block n 0) :
    ∑' z : projFibre n y, (exactKernel L s s(x, z) : ℝ≥0∞) =
      ∑' z : projFibre n x, (exactKernel L s s(y, z) : ℝ≥0∞) := by
  rw [← (projFibreReflect hx hy).tsum_eq]
  congr 1
  funext z
  rw [coe_projFibreReflect_apply, exactKernel_mk_add_sub]

open Classical in
/-- The periodic kernel `J_n^per(x,y) = ∑_{z : π_n z = y} J_∞(x,z)` on the pairs of distinct
vertices of `block n 0` (the quotient of the lattice by the coordinates `≥ n`), and `0` on all
other pairs. The fibre sum is taken in `ℝ≥0∞`; it is finite for the hierarchical lattice. -/
def periodicKernel (L s : ℝ) (n : ℕ) : Sym2 (ℕ →₀ A) → ℝ≥0 :=
  Sym2.lift ⟨fun x y => if x ≠ y ∧ x ∈ block n 0 ∧ y ∈ block n 0 then
      (∑' z : projFibre n y, (exactKernel L s s(x, z) : ℝ≥0∞)).toNNReal else 0, by
    intro x y
    by_cases h : x ≠ y ∧ x ∈ block n 0 ∧ y ∈ block n 0
    · have h' : y ≠ x ∧ y ∈ block n 0 ∧ x ∈ block n 0 := ⟨h.1.symm, h.2.2, h.2.1⟩
      dsimp only
      rw [ite_eq_left h, ite_eq_left h', tsum_projFibre_exactKernel_comm L s h.2.1 h.2.2]
    · have h' : ¬ (y ≠ x ∧ y ∈ block n 0 ∧ x ∈ block n 0) :=
        fun h' => h ⟨h'.1.symm, h'.2.2, h'.2.1⟩
      dsimp only
      rw [ite_eq_right h, ite_eq_right h']⟩

theorem periodicKernel_mk_of_mem {L s : ℝ} {n : ℕ} {x y : ℕ →₀ A} (hxy : x ≠ y)
    (hx : x ∈ block n 0) (hy : y ∈ block n 0) :
    periodicKernel L s n s(x, y) =
      (∑' z : projFibre n y, (exactKernel L s s(x, z) : ℝ≥0∞)).toNNReal := by
  classical
  simp only [periodicKernel, Sym2.lift_mk]
  rw [ite_eq_left ⟨hxy, hx, hy⟩]

theorem periodicKernel_mk_of_not_mem {L s : ℝ} {n : ℕ} {x y : ℕ →₀ A}
    (h : ¬ (x ≠ y ∧ x ∈ block n 0 ∧ y ∈ block n 0)) : periodicKernel L s n s(x, y) = 0 := by
  classical
  simp only [periodicKernel, Sym2.lift_mk]
  rw [ite_eq_right h]

open Classical in
/-- The complete-graph kernel with the constant value `c` on the pairs of `block n x`. -/
def completeKernel (n : ℕ) (x : ℕ →₀ A) (c : ℝ≥0) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x then c else 0

theorem completeKernel_of_mem {n : ℕ} {x : ℕ →₀ A} {c : ℝ≥0} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x) : completeKernel n x c e = c := by
  classical
  rw [completeKernel, ite_eq_left he]

theorem completeKernel_of_not_mem {n : ℕ} {x : ℕ →₀ A} {c : ℝ≥0} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ (¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x)) : completeKernel n x c e = 0 := by
  classical
  rw [completeKernel, ite_eq_right he]

/-- The ancestor kernel is the complete-graph kernel with value `L^{-sn}/(L^s - 1)`. -/
theorem ancestorKernel_eq_completeKernel (L s : ℝ) (n : ℕ) (x : ℕ →₀ A) :
    ancestorKernel L s n x = completeKernel n x (L ^ (-(s * n)) / (L ^ s - 1)).toNNReal := rfl

end PercLib.Models.HierarchicalLayers
