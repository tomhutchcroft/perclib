/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, from pinned mathlib's spectral theorem for Hermitian matrices and the positive
semidefinite cone. The statement follows the wiki tag CS16 (connection kernels). No source text or
code is copied.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Algebra.Order.Star.Real
public import PercLib.Meta.Tag

/-!
# Entrywise products of powers of a positive semidefinite matrix

For a real symmetric matrix `S` on a finite index type, with eigenvalues `λ_k` and
orthonormal eigenvectors `u_k` (the columns of `hS.eigenvectorUnitary`), put
`w_{kl} = u_k ⊙ u_l`. Then

* `hadamard_pow_sub_eq` (CS16, identity):
  `S ⊙ S³ - S² ⊙ S² = ½ ∑_{k,l} λ_k λ_l (λ_k - λ_l)² w_{kl} w_{klᵀ}`;
* `posSemidef_hadamard_pow_sub` (CS16): if `S` is positive semidefinite then
  `S ⊙ S³ - S² ⊙ S²` is positive semidefinite, i.e. `S² ⊙ S² ≤ S ⊙ S³` in the Loewner order.

No entrywise sign hypothesis on `S` is made.
-/

@[expose] public section
noncomputable section

open Matrix
open scoped Matrix

namespace PercLib.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entries of a real matrix that acts diagonally on the eigenbasis of `S`. -/
theorem apply_eq_sum_of_mulVec_eigenvectorBasis {S M : Matrix n n ℝ} (hS : S.IsHermitian)
    (μ : n → ℝ) (hM : ∀ k, M *ᵥ ⇑(hS.eigenvectorBasis k) = μ k • ⇑(hS.eigenvectorBasis k))
    (i j : n) :
    M i j = ∑ k, μ k * (hS.eigenvectorUnitary : Matrix n n ℝ) i k *
      (hS.eigenvectorUnitary : Matrix n n ℝ) j k := by
  set U : Matrix n n ℝ := (↑hS.eigenvectorUnitary : Matrix n n ℝ)
  have hU : U * star U = 1 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hcol : ∀ k, (M * U) i k = μ k * U i k := by
    intro k
    have h := congrFun (hM k) i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [mulVec, dotProduct] at h
    simpa [U, Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  calc M i j = (M * (U * star U)) i j := by rw [hU, Matrix.mul_one]
    _ = ∑ k, (M * U) i k * (star U) k j := by rw [← Matrix.mul_assoc, Matrix.mul_apply]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcol, Matrix.star_apply, star_trivial]

/-- Powers of `S` act on its eigenbasis by powers of the eigenvalues. -/
theorem pow_mulVec_eigenvectorBasis {S : Matrix n n ℝ} (hS : S.IsHermitian) (m : ℕ) (k : n) :
    (S ^ m) *ᵥ ⇑(hS.eigenvectorBasis k) = hS.eigenvalues k ^ m • ⇑(hS.eigenvectorBasis k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hS.mulVec_eigenvectorBasis, smul_smul]
    congr 1

/-- Entries of a power of `S` in its eigenbasis. -/
theorem pow_apply_eq_sum {S : Matrix n n ℝ} (hS : S.IsHermitian) (m : ℕ) (i j : n) :
    (S ^ m) i j = ∑ k, hS.eigenvalues k ^ m * (hS.eigenvectorUnitary : Matrix n n ℝ) i k *
      (hS.eigenvectorUnitary : Matrix n n ℝ) j k :=
  apply_eq_sum_of_mulVec_eigenvectorBasis hS _ (pow_mulVec_eigenvectorBasis hS m) i j

/-- **Identity.** For a real symmetric `S`, with `w_{kl} = u_k ⊙ u_l`,
`S ⊙ S³ - S² ⊙ S² = ½ ∑_{k,l} λ_k λ_l (λ_k - λ_l)² w_{kl} w_{kl}ᵀ`. -/
theorem hadamard_pow_sub_eq {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S ⊙ (S ^ 3) - (S ^ 2) ⊙ (S ^ 2) = (1 / 2 : ℝ) • ∑ k, ∑ l,
      (hS.eigenvalues k * hS.eigenvalues l * (hS.eigenvalues k - hS.eigenvalues l) ^ 2) •
        vecMulVec (fun i => (hS.eigenvectorUnitary : Matrix n n ℝ) i k *
            (hS.eigenvectorUnitary : Matrix n n ℝ) i l)
          (fun i => (hS.eigenvectorUnitary : Matrix n n ℝ) i k *
            (hS.eigenvectorUnitary : Matrix n n ℝ) i l) := by
  ext i j
  set U : Matrix n n ℝ := (↑hS.eigenvectorUnitary : Matrix n n ℝ)
  set ev := hS.eigenvalues
  have h1 : S i j = (S ^ 1) i j := by rw [pow_one]
  have e1 : (S ⊙ (S ^ 3)) i j =
      ∑ k, ∑ l, ev k * ev l ^ 3 * (U i k * U j k * (U i l * U j l)) := by
    rw [hadamard_apply, h1, pow_apply_eq_sum hS 1, pow_apply_eq_sum hS 3, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have e2 : ((S ^ 2) ⊙ (S ^ 2)) i j =
      ∑ k, ∑ l, ev k ^ 2 * ev l ^ 2 * (U i k * U j k * (U i l * U j l)) := by
    rw [hadamard_apply, pow_apply_eq_sum hS 2, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsym : ∀ f : n → n → ℝ, ∑ k, ∑ l, f k l = (1 / 2 : ℝ) * ∑ k, ∑ l, (f k l + f l k) := by
    intro f
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun k l => f l k)]
    ring
  rw [Matrix.sub_apply, e1, e2, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [hsym]
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **CS16.** For a real positive semidefinite `S`, `S ⊙ S³ - S² ⊙ S²` is positive
semidefinite: `S² ⊙ S² ≤ S ⊙ S³` in the Loewner order. -/
@[tag "CS16"]
theorem posSemidef_hadamard_pow_sub {S : Matrix n n ℝ} (hS : S.PosSemidef) :
    (S ⊙ (S ^ 3) - (S ^ 2) ⊙ (S ^ 2)).PosSemidef := by
  rw [hadamard_pow_sub_eq hS.isHermitian]
  refine PosSemidef.smul (posSemidef_sum _ fun k _ => posSemidef_sum _ fun l _ => ?_)
    (by norm_num)
  refine PosSemidef.smul ?_ ?_
  · simpa using posSemidef_vecMulVec_self_star
      (fun i => (hS.isHermitian.eigenvectorUnitary : Matrix n n ℝ) i k *
        (hS.isHermitian.eigenvectorUnitary : Matrix n n ℝ) i l)
  · have hk := hS.eigenvalues_nonneg k
    have hl := hS.eigenvalues_nonneg l
    positivity

/-! ### Non-vacuity -/

/-- `S = 1`: both sides are the identity, and the difference is zero. -/
example : ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊙ (1 ^ 3) - (1 ^ 2) ⊙ (1 ^ 2)) = 0 ∧
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊙ (1 ^ 3) - (1 ^ 2) ⊙ (1 ^ 2)).PosSemidef := by
  refine ⟨by simp, posSemidef_hadamard_pow_sub PosSemidef.one⟩

/-- `S = 0`. -/
example : ((0 : Matrix (Fin 2) (Fin 2) ℝ) ⊙ (0 ^ 3) - (0 ^ 2) ⊙ (0 ^ 2)).PosSemidef :=
  posSemidef_hadamard_pow_sub PosSemidef.zero

/-- A `2 × 2` example with distinct eigenvalues `1` and `3`: for `S = !![2, 1; 1, 2]`,
`S² = !![5, 4; 4, 5]`, `S³ = !![14, 13; 13, 14]`, and the difference is
`!![3, -3; -3, 3] ≠ 0`, positive semidefinite. -/
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ⊙ (!![2, 1; 1, 2] ^ 3) -
      (!![2, 1; 1, 2] ^ 2) ⊙ (!![2, 1; 1, 2] ^ 2) = !![3, -3; -3, 3] ∧
    ((!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ⊙ (!![2, 1; 1, 2] ^ 3) -
      (!![2, 1; 1, 2] ^ 2) ⊙ (!![2, 1; 1, 2] ^ 2)).PosSemidef := by
  have hS : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    have : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) =
        vecMulVec ![1, 1] (star ![1, 1]) + 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
    rw [this]
    exact (posSemidef_vecMulVec_self_star _).add PosSemidef.one
  refine ⟨?_, posSemidef_hadamard_pow_sub hS⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, hadamard_apply] <;> norm_num

end PercLib.Analysis
