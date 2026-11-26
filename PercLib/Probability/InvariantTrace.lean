/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, from pinned mathlib's series lemmas. The statements are the trace step of the wiki tags
IZAO and 87W3 (connection kernels). No source text or code is copied.
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The trace identity for invariant kernels on a group

A kernel `M : Γ → Γ → R` on a group is *invariant* when `M (g * x) (g * y) = M x y` for all
`g x y` (an explicit hypothesis; no new definition).

* `tsum_mul_eq_tsum_mul_of_invariant` (trace step of IZAO / 87W3): for invariant real
  kernels, `tr₁(MN) = ∑' v, M 1 v * N v 1` equals `tr₁(NM) = ∑' v, N 1 v * M v 1`; with
  square-summable row of `M` and column of `N` at `1`, the series converges absolutely
  (`summable_abs_mul_of_sq`).
* `invariant_tsum_mul`, `invariant_hadamard`: products and Hadamard products of invariant
  kernels are invariant.
* `tsum_iterate_row` and `tsum_iterate_col`: for an invariant `M ≥ 0` (in `ℝ≥0∞`) with row
  sum `χ` at `1`, every row and every column of the `n`-th kernel power sums to `χ^n`. The
  power is written as the iterate of `K ↦ (x, y) ↦ ∑' z, K x z * M z y` from the identity
  kernel.

Each has an additive version.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Probability

variable {Γ : Type*} [Group Γ]

/-- An invariant kernel satisfies `M v 1 = M 1 v⁻¹`. -/
@[to_additive /-- An invariant kernel satisfies `M v 0 = M 0 (-v)`. -/]
theorem invariant_apply_one {R : Type*} (M : Γ → Γ → R)
    (hM : ∀ g x y, M (g * x) (g * y) = M x y) (v : Γ) : M v 1 = M 1 v⁻¹ := by
  have := hM v⁻¹ v 1
  rwa [inv_mul_cancel, mul_one, eq_comm] at this

/-- **Trace step.** For invariant kernels, `tr₁(MN) = tr₁(NM)`:
`∑' v, M 1 v * N v 1 = ∑' v, N 1 v * M v 1`. No summability is needed for the identity of
the two `tsum`s. -/
@[to_additive /-- Additive version of the trace identity. -/]
theorem tsum_mul_eq_tsum_mul_of_invariant (M N : Γ → Γ → ℝ)
    (hM : ∀ g x y, M (g * x) (g * y) = M x y) (hN : ∀ g x y, N (g * x) (g * y) = N x y) :
    ∑' v, M 1 v * N v 1 = ∑' v, N 1 v * M v 1 := by
  simp_rw [invariant_apply_one M hM, invariant_apply_one N hN]
  rw [← (Equiv.inv Γ).tsum_eq]
  refine tsum_congr fun v => ?_
  simp only [Equiv.inv_apply, inv_inv]
  exact mul_comm _ _

/-- With a square-summable row of `M` and column of `N` at `1`, the trace series converges
absolutely. -/
@[to_additive /-- Additive version of absolute convergence of the trace series. -/]
theorem summable_abs_mul_of_sq (M N : Γ → Γ → ℝ) (hM : Summable fun v => M 1 v ^ 2)
    (hN : Summable fun v => N v 1 ^ 2) : Summable fun v => |M 1 v * N v 1| := by
  refine Summable.of_nonneg_of_le (fun v => abs_nonneg _) (fun v => ?_)
    ((hM.add hN).div_const 2)
  rw [abs_mul]
  nlinarith [sq_abs (M 1 v), sq_abs (N v 1), sq_nonneg (|M 1 v| - |N v 1|)]

/-- **Trace step, with convergence.** For invariant real kernels with
square-summable rows and columns, both trace series converge absolutely and are equal. -/
@[to_additive trace_comm_of_invariant_add
    /-- Additive version of the trace identity with convergence. -/]
theorem trace_comm_of_invariant (M N : Γ → Γ → ℝ)
    (hM : ∀ g x y, M (g * x) (g * y) = M x y) (hN : ∀ g x y, N (g * x) (g * y) = N x y)
    (hMr : ∀ x, Summable fun y => M x y ^ 2) (hMc : ∀ y, Summable fun x => M x y ^ 2)
    (hNr : ∀ x, Summable fun y => N x y ^ 2) (hNc : ∀ y, Summable fun x => N x y ^ 2) :
    Summable (fun v => |M 1 v * N v 1|) ∧ Summable (fun v => |N 1 v * M v 1|) ∧
      ∑' v, M 1 v * N v 1 = ∑' v, N 1 v * M v 1 :=
  ⟨summable_abs_mul_of_sq M N (hMr 1) (hNc 1), summable_abs_mul_of_sq N M (hNr 1) (hMc 1),
    tsum_mul_eq_tsum_mul_of_invariant M N hM hN⟩

/-- The kernel product of invariant kernels is invariant. -/
@[to_additive /-- The kernel product of invariant kernels is invariant. -/]
theorem invariant_tsum_mul {R : Type*} [Mul R] [AddCommMonoid R] [TopologicalSpace R]
    (M N : Γ → Γ → R) (hM : ∀ g x y, M (g * x) (g * y) = M x y)
    (hN : ∀ g x y, N (g * x) (g * y) = N x y) (g x y : Γ) :
    ∑' z, M (g * x) z * N z (g * y) = ∑' z, M x z * N z y := by
  rw [← (Equiv.mulLeft g).tsum_eq]
  exact tsum_congr fun z => by simp only [Equiv.coe_mulLeft, hM, hN]

/-- The Hadamard product of invariant kernels is invariant. -/
@[to_additive invariant_hadamard_add /-- The Hadamard product of invariant kernels is invariant. -/]
theorem invariant_hadamard {R : Type*} [Mul R] (M N : Γ → Γ → R)
    (hM : ∀ g x y, M (g * x) (g * y) = M x y) (hN : ∀ g x y, N (g * x) (g * y) = N x y)
    (g x y : Γ) : M (g * x) (g * y) * N (g * x) (g * y) = M x y * N x y := by
  rw [hM, hN]

/-- Every row of an invariant `M ≥ 0` sums to its row sum at `1`. -/
@[to_additive tsum_row_eq_add /-- Every row of an invariant `M ≥ 0` sums to its row sum at `0`. -/]
theorem tsum_row_eq (M : Γ → Γ → ℝ≥0∞) (hM : ∀ g x y, M (g * x) (g * y) = M x y) (x : Γ) :
    ∑' y, M x y = ∑' y, M 1 y := by
  rw [← (Equiv.mulLeft x).tsum_eq]
  refine tsum_congr fun y => ?_
  simpa using hM x 1 y

/-- Every column of an invariant `M ≥ 0` sums to its row sum at `1`. -/
@[to_additive tsum_col_eq_add
    /-- Every column of an invariant `M ≥ 0` sums to its row sum at `0`. -/]
theorem tsum_col_eq (M : Γ → Γ → ℝ≥0∞) (hM : ∀ g x y, M (g * x) (g * y) = M x y) (y : Γ) :
    ∑' x, M x y = ∑' x, M 1 x := by
  rw [← (Equiv.mulLeft y).tsum_eq, ← (Equiv.inv Γ).tsum_eq]
  refine tsum_congr fun x => ?_
  simp only [Equiv.coe_mulLeft, Equiv.inv_apply]
  have h := hM (y * x⁻¹)⁻¹ (y * x⁻¹) y
  rw [inv_mul_cancel, show (y * x⁻¹)⁻¹ * y = x by simp [mul_assoc]] at h
  exact h.symm

open Classical in
/-- **Rows of kernel powers.** For an invariant `M ≥ 0` whose row at `1` sums to `χ`, every
row of the `n`-th power of `M` sums to `χ^n`. -/
@[to_additive tsum_iterate_row_add /-- Rows of kernel powers, additive version. -/]
theorem tsum_iterate_row (M : Γ → Γ → ℝ≥0∞) (hM : ∀ g x y, M (g * x) (g * y) = M x y)
    {χ : ℝ≥0∞} (hχ : ∑' y, M 1 y = χ) (n : ℕ) (x : Γ) :
    ∑' y, (fun K : Γ → Γ → ℝ≥0∞ => fun a b => ∑' z, K a z * M z b)^[n]
      (fun a b => if a = b then 1 else 0) x y = χ ^ n := by
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero]
    rw [tsum_eq_single x (fun y hy => by simp [hy.symm])]
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, tsum_row_eq M hM, hχ, ENNReal.tsum_mul_right, ih, pow_succ]

open Classical in
/-- **Columns of kernel powers.** For an invariant `M ≥ 0` whose row at `1` sums to `χ`,
every column of the `n`-th power of `M` sums to `χ^n`. -/
@[to_additive tsum_iterate_col_add /-- Columns of kernel powers, additive version. -/]
theorem tsum_iterate_col (M : Γ → Γ → ℝ≥0∞) (hM : ∀ g x y, M (g * x) (g * y) = M x y)
    {χ : ℝ≥0∞} (hχ : ∑' y, M 1 y = χ) (n : ℕ) (y : Γ) :
    ∑' x, (fun K : Γ → Γ → ℝ≥0∞ => fun a b => ∑' z, K a z * M z b)^[n]
      (fun a b => if a = b then 1 else 0) x y = χ ^ n := by
  induction n generalizing y with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero]
    rw [tsum_eq_single y (fun x hx => by simp [hx])]
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right, ih, ENNReal.tsum_mul_left, tsum_col_eq M hM, hχ, pow_succ]

/-! ### Non-vacuity -/

/-- Non-vacuity on `ℤ` (additive): `M x y = 2^{-|x-y|}` is invariant with square-summable rows and
columns, so the trace identity applies, with absolute convergence. -/
example : Summable (fun v : ℤ => |(1 / 2 : ℝ) ^ (v - 0).natAbs * (1 / 2 : ℝ) ^ (0 - v).natAbs|) ∧
    ∑' v : ℤ, (1 / 2 : ℝ) ^ (v - 0).natAbs * (1 / 2 : ℝ) ^ (0 - v).natAbs =
      ∑' v : ℤ, (1 / 2 : ℝ) ^ (v - 0).natAbs * (1 / 2 : ℝ) ^ (0 - v).natAbs := by
  have hsq : ∀ x : ℤ, Summable fun y : ℤ => ((1 / 2 : ℝ) ^ (y - x).natAbs) ^ 2 := by
    intro x
    have h : Summable fun n : ℕ => ((1 / 2 : ℝ) ^ 2) ^ n :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h' : Summable fun y : ℤ => ((1 / 2 : ℝ) ^ y.natAbs) ^ 2 := by
      refine Summable.of_nat_of_neg_add_one ?_ ?_
      · simpa [← pow_mul, mul_comm] using h
      · refine (h.mul_left ((1 / 2 : ℝ) ^ 2)).congr fun n => ?_
        have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
        rw [this]
        simp only [← pow_mul, ← pow_add]
        congr 1
        ring
    exact (h'.comp_injective (sub_left_injective (b := x))).congr fun y => rfl
  have hsq' : ∀ y : ℤ, Summable fun x : ℤ => ((1 / 2 : ℝ) ^ (y - x).natAbs) ^ 2 := by
    intro y
    refine (hsq y).congr fun x => ?_
    rw [← Int.natAbs_neg, neg_sub]
  have h := trace_comm_of_invariant_add (fun x y : ℤ => (1 / 2 : ℝ) ^ (y - x).natAbs)
    (fun x y : ℤ => (1 / 2 : ℝ) ^ (y - x).natAbs)
    (fun g x y => by simp) (fun g x y => by simp) hsq hsq' hsq hsq'
  exact ⟨h.1, h.2.2⟩

/-- Non-vacuity on `ZMod 3` (written `Fin 3`, the same type) with circulant kernels
`M x y = c(y - x)`, `N x y = d(y - x)`: both traces are `7`, computed as finite sums. -/
example :
    ∑' v : Fin 3, ![(2 : ℝ), 1, 0] (v - 0) * ![(1 : ℝ), 3, 5] (0 - v) = 7 ∧
      ∑' v : Fin 3, ![(1 : ℝ), 3, 5] (v - 0) * ![(2 : ℝ), 1, 0] (0 - v) = 7 ∧
      ∑' v : Fin 3, ![(2 : ℝ), 1, 0] (v - 0) * ![(1 : ℝ), 3, 5] (0 - v) =
        ∑' v : Fin 3, ![(1 : ℝ), 3, 5] (v - 0) * ![(2 : ℝ), 1, 0] (0 - v) := by
  refine ⟨?_, ?_, tsum_add_eq_tsum_add_of_invariant
    (fun x y : Fin 3 => ![(2 : ℝ), 1, 0] (y - x)) (fun x y : Fin 3 => ![(1 : ℝ), 3, 5] (y - x))
    (fun g x y => by simp only [add_sub_add_left_eq_sub])
    (fun g x y => by simp only [add_sub_add_left_eq_sub])⟩
  all_goals
    rw [tsum_fintype, Fin.sum_univ_three]
    have h1 : ((1 : Fin 3) - 0) = 1 := rfl
    have h2 : ((2 : Fin 3) - 0) = 2 := rfl
    have h3 : ((0 : Fin 3) - 1) = 2 := rfl
    have h4 : ((0 : Fin 3) - 2) = 1 := rfl
    have h0 : ((0 : Fin 3) - 0) = 0 := rfl
    rw [h0, h1, h2, h3, h4]
    norm_num

/-- Non-vacuity witness for kernel powers: on `ZMod 3` the all-ones kernel has row sum `3`, and
every row and column of its `n`-th power sums to `3^n`. -/
example (n : ℕ) (x : ZMod 3) :
    ∑' y, (fun K : ZMod 3 → ZMod 3 → ℝ≥0∞ => fun a b => ∑' z, K a z * (fun _ _ => 1) z b)^[n]
      (fun a b => if a = b then 1 else 0) x y = 3 ^ n := by
  convert tsum_iterate_row_add (Γ := ZMod 3) (fun _ _ => (1 : ℝ≥0∞)) (fun _ _ _ => rfl)
    (χ := 3) ?_ n x
  rw [tsum_fintype]
  simp

end PercLib.Probability
