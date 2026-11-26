/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Names for the hierarchical lattice and its metric notions, on the finite-support lattice used
throughout the hierarchical modules. New code; uses mathlib's direct sums of finitely supported
functions. Mathematical reference: T. Hutchcroft, *The critical two-point function for
long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1, Section 1.
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Models.HierarchicalBlockLayers.Defs
public import Mathlib.Algebra.DirectSum.Finsupp

/-!
# The hierarchical lattice, its distance and its balls

The hierarchical lattice `ℍ_L^d = ⨁_{i ≥ 1} (ℤ/Lℤ)^d` is represented as the finitely supported
sequences `ℕ →₀ (Fin d → ZMod L)` (coordinate `i ≥ 1` of the source is index `i - 1` here). The
level of a vertex is `0` at the origin and otherwise one more than its largest nonzero index, so
the hierarchical distance of `x ≠ y` is `L ^ level (x - y)`.

## Main definitions

* `HierarchicalLattice d L`: the lattice, with `toDirectSum` identifying it with the direct sum.
* `HierarchicalLattice.level`, `hierNorm`, `hierDist`: level, norm and distance.
* `HierarchicalLattice.ball x n`: the closed ball of radius `L ^ n` about `x`.
* `HierarchicalLattice.commonBall x y`: the smallest ball containing `x` and `y`.
* `HierarchicalLattice.regDist x y = max 1 (hierDist x y)`.
* `HierarchicalLattice.IsRadial J`: the kernel `J` depends only on the distance.

## Main results

* `HierarchicalLattice.exists_hierDist_eq_pow_of_ne`: `hierDist x y = L ^ (i + 1)` for the largest
  index `i` at which `x` and `y` differ.
* `HierarchicalLattice.ball_eq_setOf_hierDist_le`, `HierarchicalLattice.card_ball`.
* `HierarchicalLattice.commonBall_subset_of_mem`: minimality of the common ball.
* `HierarchicalLattice.regDist_eq_pow`, `HierarchicalLattice.isRadial_iff_level`.
-/

@[expose] public section
noncomputable section

open DirectSum

namespace PercLib.Models

/-- The hierarchical lattice `ℍ_L^d = ⨁_{i ≥ 1} (ℤ/Lℤ)^d`, as finitely supported sequences of
elements of `(ℤ/Lℤ)^d`; index `i` here is coordinate `i + 1` of the direct sum. -/
abbrev HierarchicalLattice (d L : ℕ) : Type := ℕ →₀ (Fin d → ZMod L)

namespace HierarchicalLattice

variable {d L : ℕ}

/-- The identification of the hierarchical lattice with the direct sum of copies of
`(ℤ/Lℤ)^d`. -/
def toDirectSum : HierarchicalLattice d L ≃+ ⨁ _ : ℕ, (Fin d → ZMod L) :=
  (finsuppLEquivDirectSum ℤ (Fin d → ZMod L) ℕ).toAddEquiv

@[simp]
theorem toDirectSum_apply (x : HierarchicalLattice d L) (i : ℕ) : toDirectSum x i = x i :=
  rfl

/-- The level of a vertex: `0` at the origin, otherwise one more than its largest nonzero
index. -/
def level (x : HierarchicalLattice d L) : ℕ := x.support.sup Nat.succ

theorem level_def (x : HierarchicalLattice d L) : level x = x.support.sup Nat.succ := rfl

@[simp]
theorem level_zero : level (0 : HierarchicalLattice d L) = 0 := by simp [level]

@[simp]
theorem level_eq_zero {x : HierarchicalLattice d L} : level x = 0 ↔ x = 0 :=
  level_eq_zero_iff x

theorem level_sub_comm (x y : HierarchicalLattice d L) : level (x - y) = level (y - x) :=
  (PercLib.Models.level_sub_comm x y).symm

/-- The level of a nonzero vertex is one more than its largest nonzero index. -/
theorem level_eq_max'_add_one {x : HierarchicalLattice d L} (hx : x.support.Nonempty) :
    level x = x.support.max' hx + 1 :=
  le_antisymm (Finset.sup_le fun j hj => Nat.succ_le_succ (Finset.le_max' _ j hj))
    (Finset.le_sup (f := Nat.succ) (Finset.max'_mem _ hx))

/-- The hierarchical norm `‖x‖`: `0` at the origin and `L ^ level x` otherwise. -/
def hierNorm (x : HierarchicalLattice d L) : ℕ := if x = 0 then 0 else L ^ level x

@[simp]
theorem hierNorm_zero : hierNorm (0 : HierarchicalLattice d L) = 0 := by simp [hierNorm]

theorem hierNorm_of_ne_zero {x : HierarchicalLattice d L} (hx : x ≠ 0) :
    hierNorm x = L ^ level x := by simp [hierNorm, hx]

/-- The hierarchical distance `‖x - y‖`. -/
def hierDist (x y : HierarchicalLattice d L) : ℕ := hierNorm (x - y)

theorem hierDist_def (x y : HierarchicalLattice d L) : hierDist x y = hierNorm (x - y) := rfl

@[simp]
theorem hierDist_self (x : HierarchicalLattice d L) : hierDist x x = 0 := by simp [hierDist]

theorem hierDist_of_ne {x y : HierarchicalLattice d L} (h : x ≠ y) :
    hierDist x y = L ^ level (x - y) :=
  hierNorm_of_ne_zero (sub_ne_zero.mpr h)

theorem hierDist_comm (x y : HierarchicalLattice d L) : hierDist x y = hierDist y x := by
  by_cases h : x = y
  · rw [h]
  · rw [hierDist_of_ne h, hierDist_of_ne (Ne.symm h), level_sub_comm]

/-- For `x ≠ y` the distance is `L ^ (i + 1)`, where `i` is the largest index at which `x` and
`y` differ (coordinate `i + 1` of the direct sum). -/
theorem exists_hierDist_eq_pow_of_ne {x y : HierarchicalLattice d L} (h : x ≠ y) :
    ∃ i, x i ≠ y i ∧ (∀ j, x j ≠ y j → j ≤ i) ∧ hierDist x y = L ^ (i + 1) := by
  have hne : (x - y).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (sub_ne_zero.mpr h)
  refine ⟨(x - y).support.max' hne, ?_, fun j hj => ?_, ?_⟩
  · have := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hne)
    rwa [Finsupp.sub_apply, sub_ne_zero] at this
  · exact Finset.le_max' _ j (Finsupp.mem_support_iff.mpr (by simpa [sub_eq_zero] using hj))
  · rw [hierDist_of_ne h, level_eq_max'_add_one hne]

/-- A level bound on the displacement is a bound by the corresponding power of `L`. -/
theorem level_sub_le_iff_hierDist_le (hL : 2 ≤ L) (x z : HierarchicalLattice d L) (n : ℕ) :
    level (z - x) ≤ n ↔ hierDist z x ≤ L ^ n := by
  by_cases h : z = x
  · simp [h]
  · rw [hierDist_of_ne h, pow_le_pow_iff_right₀ (by omega : 1 < L)]

/-- The closed hierarchical ball of radius `L ^ n` about `x`. -/
def ball (x : HierarchicalLattice d L) (n : ℕ) : Set (HierarchicalLattice d L) :=
  {z | level (z - x) ≤ n}

@[simp]
theorem mem_ball {x z : HierarchicalLattice d L} {n : ℕ} : z ∈ ball x n ↔ level (z - x) ≤ n :=
  Iff.rfl

theorem center_mem_ball (x : HierarchicalLattice d L) (n : ℕ) : x ∈ ball x n := by simp

/-- The ball of radius `L ^ n` about `x` is the level-`n` block of `x`. -/
theorem ball_eq_block (x : HierarchicalLattice d L) (n : ℕ) :
    ball x n = HierarchicalLayers.block n x :=
  rfl

theorem ball_eq_setOf_hierDist_le (hL : 2 ≤ L) (x : HierarchicalLattice d L) (n : ℕ) :
    ball x n = {z | hierDist z x ≤ L ^ n} := by
  ext z
  exact level_sub_le_iff_hierDist_le hL x z n

/-- A hierarchical ball of radius `L ^ n` has `L ^ (d n)` vertices. -/
theorem card_ball [NeZero L] (x : HierarchicalLattice d L) (n : ℕ) :
    Nat.card (ball x n) = L ^ (d * n) := by
  rw [pow_mul, ← _root_.PercLib.Models.card_ball (d := d) (L := L) n]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.subRight x) fun _ => Iff.rfl)

/-- For `L ≥ 2`, the vertices within distance `L ^ n` of `x` number `L ^ (d n)`. -/
theorem card_setOf_hierDist_le (hL : 2 ≤ L) (x : HierarchicalLattice d L) (n : ℕ) :
    Nat.card {z : HierarchicalLattice d L | hierDist z x ≤ L ^ n} = L ^ (d * n) := by
  have : NeZero L := ⟨by omega⟩
  rw [← ball_eq_setOf_hierDist_le hL, card_ball]

/-- The smallest hierarchical ball `Λ(x, y)` containing `x` and `y`. -/
def commonBall (x y : HierarchicalLattice d L) : Set (HierarchicalLattice d L) :=
  ball x (level (y - x))

theorem commonBall_def (x y : HierarchicalLattice d L) :
    commonBall x y = ball x (level (y - x)) := rfl

theorem left_mem_commonBall (x y : HierarchicalLattice d L) : x ∈ commonBall x y :=
  center_mem_ball x _

theorem right_mem_commonBall (x y : HierarchicalLattice d L) : y ∈ commonBall x y :=
  le_refl (level (y - x))

/-- Every ball containing `x` and `y` contains `Λ(x, y)`. -/
theorem commonBall_subset_of_mem {x y z : HierarchicalLattice d L} {n : ℕ}
    (hx : x ∈ ball z n) (hy : y ∈ ball z n) : commonBall x y ⊆ ball z n := by
  intro w hw
  have hyx : level (y - x) ≤ n :=
    (level_sub_le_max x z y).trans (max_le ((level_sub_comm z x).trans_le hx) hy)
  exact (level_sub_le_max z x w).trans (max_le hx (hw.trans hyx))

theorem commonBall_comm (x y : HierarchicalLattice d L) : commonBall x y = commonBall y x :=
  (commonBall_subset_of_mem (right_mem_commonBall y x) (left_mem_commonBall y x)).antisymm
    (commonBall_subset_of_mem (right_mem_commonBall x y) (left_mem_commonBall x y))

/-- The regularized distance `⟨x - y⟩ = max 1 ‖x - y‖`. -/
def regDist (x y : HierarchicalLattice d L) : ℕ := max 1 (hierDist x y)

theorem regDist_def (x y : HierarchicalLattice d L) : regDist x y = max 1 (hierDist x y) := rfl

/-- The regularized distance is `L` to the level of the displacement. -/
theorem regDist_eq_pow [NeZero L] (x y : HierarchicalLattice d L) :
    regDist x y = L ^ level (x - y) := by
  by_cases h : x = y
  · simp [regDist, h]
  · rw [regDist, hierDist_of_ne h]
    exact max_eq_right (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L)))

/-- A kernel on pairs of vertices is radial if it depends only on the hierarchical distance. -/
def IsRadial {β : Type*} (J : Sym2 (HierarchicalLattice d L) → β) : Prop :=
  ∃ f : ℕ → β, ∀ x y, J s(x, y) = f (hierDist x y)

/-- For `L ≥ 2`, a kernel is radial exactly when it depends only on the level of the
displacement. -/
theorem isRadial_iff_level (hL : 2 ≤ L) {β : Type*} (J : Sym2 (HierarchicalLattice d L) → β) :
    IsRadial J ↔ ∃ f : ℕ → β, ∀ x y, J s(x, y) = f (level (y - x)) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun k => f (if k = 0 then 0 else L ^ k), fun x y => ?_⟩
    rw [hf]
    by_cases h : x = y
    · simp [h]
    · have hk : level (y - x) ≠ 0 := fun h0 => h (sub_eq_zero.mp (level_eq_zero.mp h0)).symm
      simp only [hk, ite_false, hierDist_of_ne h, level_sub_comm x y]
  · rintro ⟨f, hf⟩
    refine ⟨fun m => f (Nat.log L m), fun x y => ?_⟩
    rw [hf]
    by_cases h : x = y
    · simp [h]
    · dsimp only
      rw [hierDist_of_ne h, Nat.log_pow (by omega : 1 < L), level_sub_comm x y]

end HierarchicalLattice

end PercLib.Models
