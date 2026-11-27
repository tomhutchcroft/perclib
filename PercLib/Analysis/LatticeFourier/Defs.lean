/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions and proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.Ring

/-!
# Lattice cosine transforms and nearest-neighbour resolvents

The frequencies are real vectors, so the formulas are periodic without requiring a
choice of representatives. In dimension zero the normalized symbol is zero.

## Main results

* `latticeCosineTransform`: the real cosine transform of an integer-lattice kernel.
* `latticeCharacter`: the canonical unitary character in physical frequencies.
* `nearestNeighborSymbol`: the average coordinate cosine.
* `nearestNeighborResolvent`: the reciprocal `1 / (1 - lambda D)`.
* `fwdDiff_two_at_sub`: the existing forward difference gives the symmetric second difference.
-/

@[expose] public section

noncomputable section

namespace PercLib.Analysis

/-- The canonical lattice character in physical frequencies, using mathlib's
probabilistic character convention `exp(i k·x)`. -/
def latticeCharacter {ι : Type*} [Fintype ι] (k : ι → ℝ) : AddChar (ι → ℤ) Circle :=
  Real.probChar.compAddMonoidHom
    { toFun := fun x => ∑ i, k i * (x i : ℝ)
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib] }

theorem latticeCharacter_apply {ι : Type*} [Fintype ι] (k : ι → ℝ) (x : ι → ℤ) :
    latticeCharacter k x = Real.probChar (∑ i, k i * (x i : ℝ)) := rfl

/-- The complex value of the canonical character is the usual exponential. -/
theorem latticeCharacter_coe_apply {ι : Type*} [Fintype ι] (k : ι → ℝ) (x : ι → ℤ) :
    (latticeCharacter k x : ℂ) =
      Complex.exp ((∑ i, k i * (x i : ℝ) : ℝ) * Complex.I) := rfl

@[simp] theorem latticeCharacter_re {ι : Type*} [Fintype ι] (k : ι → ℝ) (x : ι → ℤ) :
    (latticeCharacter k x : ℂ).re = Real.cos (∑ i, k i * (x i : ℝ)) := by
  simp [latticeCharacter_coe_apply, Complex.exp_re]

@[simp] theorem latticeCharacter_im {ι : Type*} [Fintype ι] (k : ι → ℝ) (x : ι → ℤ) :
    (latticeCharacter k x : ℂ).im = Real.sin (∑ i, k i * (x i : ℝ)) := by
  simp [latticeCharacter_coe_apply, Complex.exp_im]

@[simp] theorem latticeCharacter_zero_frequency {ι : Type*} [Fintype ι] :
    latticeCharacter (0 : ι → ℝ) = 1 := by
  ext x
  simp [latticeCharacter_apply]

@[simp] theorem latticeCharacter_neg_frequency {ι : Type*} [Fintype ι] (k : ι → ℝ) :
    latticeCharacter (-k) = (latticeCharacter k)⁻¹ := by
  ext x
  simp [AddChar.inv_apply, latticeCharacter_apply, Finset.sum_neg_distrib]

/-- The real cosine transform of a kernel on an integer lattice. -/
def latticeCosineTransform {ι : Type*} [Fintype ι] (f : (ι → ℤ) → ℝ) (k : ι → ℝ) : ℝ :=
  ∑' x, f x * Real.cos (∑ i, k i * (x i : ℝ))

theorem latticeCosineTransform_def {ι : Type*} [Fintype ι]
    (f : (ι → ℤ) → ℝ) (k : ι → ℝ) :
    latticeCosineTransform f k = ∑' x, f x * Real.cos (∑ i, k i * (x i : ℝ)) := rfl

@[simp] theorem latticeCosineTransform_zero_kernel {ι : Type*} [Fintype ι] (k : ι → ℝ) :
    latticeCosineTransform (fun _ => 0) k = 0 := by simp [latticeCosineTransform]

@[simp] theorem latticeCosineTransform_at_zero {ι : Type*} [Fintype ι]
    (f : (ι → ℤ) → ℝ) : latticeCosineTransform f 0 = ∑' x, f x := by
  simp [latticeCosineTransform]

@[simp] theorem latticeCosineTransform_neg_frequency {ι : Type*} [Fintype ι]
    (f : (ι → ℤ) → ℝ) (k : ι → ℝ) :
    latticeCosineTransform f (-k) = latticeCosineTransform f k := by
  simp [latticeCosineTransform, neg_mul, Finset.sum_neg_distrib]

/-- The symbol of the ordinary nearest-neighbour walk. The zero-dimensional value is zero. -/
def nearestNeighborSymbol {d : ℕ} (k : Fin d → ℝ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ i, Real.cos (k i)

theorem nearestNeighborSymbol_def {d : ℕ} (k : Fin d → ℝ) :
    nearestNeighborSymbol k = (d : ℝ)⁻¹ * ∑ i, Real.cos (k i) := rfl

@[simp] theorem nearestNeighborSymbol_dim_zero (k : Fin 0 → ℝ) :
    nearestNeighborSymbol k = 0 := by simp [nearestNeighborSymbol]

@[simp] theorem nearestNeighborSymbol_at_zero {d : ℕ} (hd : 0 < d) :
    nearestNeighborSymbol (0 : Fin d → ℝ) = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [nearestNeighborSymbol, hd0]

@[simp] theorem nearestNeighborSymbol_neg {d : ℕ} (k : Fin d → ℝ) :
    nearestNeighborSymbol (-k) = nearestNeighborSymbol k := by
  simp [nearestNeighborSymbol]

/-- The massive nearest-neighbour resolvent, with real inversion giving its total extension. -/
def nearestNeighborResolvent {d : ℕ} (lam : ℝ) (k : Fin d → ℝ) : ℝ :=
  (1 - lam * nearestNeighborSymbol k)⁻¹

theorem nearestNeighborResolvent_def {d : ℕ} (lam : ℝ) (k : Fin d → ℝ) :
    nearestNeighborResolvent lam k = (1 - lam * nearestNeighborSymbol k)⁻¹ := rfl

@[simp] theorem nearestNeighborResolvent_zero_parameter {d : ℕ} (k : Fin d → ℝ) :
    nearestNeighborResolvent 0 k = 1 := by simp [nearestNeighborResolvent]

@[simp] theorem nearestNeighborResolvent_dim_zero (lam : ℝ) (k : Fin 0 → ℝ) :
    nearestNeighborResolvent lam k = 1 := by simp [nearestNeighborResolvent]

@[simp] theorem nearestNeighborResolvent_at_zero {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    nearestNeighborResolvent lam (0 : Fin d → ℝ) = (1 - lam)⁻¹ := by
  simp [nearestNeighborResolvent, nearestNeighborSymbol_at_zero hd]

@[simp] theorem nearestNeighborResolvent_neg {d : ℕ} (lam : ℝ) (k : Fin d → ℝ) :
    nearestNeighborResolvent lam (-k) = nearestNeighborResolvent lam k := by
  simp [nearestNeighborResolvent]

/-- The second forward difference at `l - k` is the symmetric second difference at `l`. -/
theorem fwdDiff_two_at_sub {G : Type*} [AddCommGroup G] (F : G → ℝ) (l k : G) :
    (fwdDiff k)^[2] F (l - k) = F (l - k) + F (l + k) - 2 * F l := by
  change (F ((l - k + k) + k) - F (l - k + k)) -
    (F (l - k + k) - F (l - k)) = _
  rw [sub_add_cancel]
  ring

end PercLib.Analysis
