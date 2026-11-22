/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference: the
Loewner comparison `S² ⊙ S² ≤ S ⊙ S³` for a positive semidefinite matrix, extended to infinite
nonnegative kernels by exhaustion with finite principal submatrices.
-/
module

public import PercLib.Analysis.HadamardPowers

/-!
# Quadratic forms of the entrywise products `S² ⊙ S²` and `S ⊙ S³`

For a real positive semidefinite matrix `S`, `S ⊙ S³ - S² ⊙ S²` is positive semidefinite
(`posSemidef_hadamard_pow_sub`). This file records the corresponding inequality between the
quadratic forms, first for a finite matrix, then for a principal submatrix of a kernel on an
arbitrary type, and finally for a nonnegative kernel `T : V → V → [0, ∞]` all of whose finite
principal submatrices are positive semidefinite. In the last case, with
`T²(x,y) = ∑_u T(x,u) T(u,y)` and `T³(x,y) = ∑_{u,w} T(x,u) T(u,w) T(w,y)` as sums in `[0, ∞]`,
every finite-valued `b : V → [0, ∞)` satisfies

`∑_{x,y} b(x) T²(x,y)² b(y) ≤ ∑_{x,y} b(x) T(x,y) T³(x,y) b(y)`.

No summability or boundedness of `T` is assumed: the left side is the limit of its finite
truncations, each of which is bounded by the right side.

## Main results

* `quadForm_hadamard_sq_le_of_posSemidef`: the finite matrix inequality.
* `sum_quadForm_hadamard_sq_le_of_posSemidef`: the inequality for a principal submatrix on a
  finset, with matrix powers written as finite sums.
* `tsum_quadForm_hadamard_sq_le_of_posSemidef`: the inequality for an infinite nonnegative
  kernel.
-/

@[expose] public section

open Matrix Filter Topology
open scoped Matrix ENNReal NNReal

namespace PercLib.Analysis

/-- **Finite quadratic-form comparison.** For a real positive semidefinite `S` and every real
vector `c`, `∑_{i,j} cᵢ (S²)ᵢⱼ² cⱼ ≤ ∑_{i,j} cᵢ Sᵢⱼ (S³)ᵢⱼ cⱼ`. -/
theorem quadForm_hadamard_sq_le_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.PosSemidef) (c : n → ℝ) :
    ∑ i, ∑ j, c i * (S ^ 2) i j ^ 2 * c j ≤ ∑ i, ∑ j, c i * (S i j * (S ^ 3) i j) * c j := by
  have h := (posSemidef_hadamard_pow_sub hS).dotProduct_mulVec_nonneg c
  simp only [star_trivial, dotProduct, mulVec, Matrix.sub_apply, hadamard_apply] at h
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Quadratic-form comparison on a principal submatrix.** If the principal submatrix of a real
kernel `t` on the finset `F` is positive semidefinite, then for every real `c`,
`∑_{x,y ∈ F} c(x) (∑_{u ∈ F} t(x,u) t(u,y))² c(y)` is at most
`∑_{x,y ∈ F} c(x) t(x,y) (∑_{u,w ∈ F} t(x,u) t(u,w) t(w,y)) c(y)`. -/
theorem sum_quadForm_hadamard_sq_le_of_posSemidef {V : Type*} [DecidableEq V] (t : V → V → ℝ)
    (F : Finset V) (hF : (Matrix.of fun i j : F => t i j).PosSemidef) (c : V → ℝ) :
    ∑ x ∈ F, ∑ y ∈ F, c x * (∑ u ∈ F, t x u * t u y) ^ 2 * c y ≤
      ∑ x ∈ F, ∑ y ∈ F, c x * (t x y * ∑ u ∈ F, ∑ w ∈ F, t x u * t u w * t w y) * c y := by
  set S : Matrix F F ℝ := Matrix.of fun i j : F => t i j
  have h2 : ∀ i j : F, (S ^ 2) i j = ∑ u ∈ F, t i u * t u j := by
    intro i j
    rw [sq, mul_apply]
    exact F.sum_coe_sort fun u => t i u * t u j
  have h3 : ∀ i j : F, (S ^ 3) i j = ∑ u ∈ F, ∑ w ∈ F, t i u * t u w * t w j := by
    intro i j
    rw [pow_succ', mul_apply]
    simp only [h2, S, of_apply, Finset.mul_sum, mul_assoc]
    exact F.sum_coe_sort fun u => ∑ w ∈ F, t i u * (t u w * t w j)
  have key : ∀ g : V → V → ℝ, ∑ i : F, ∑ j : F, g i j = ∑ x ∈ F, ∑ y ∈ F, g x y := fun g =>
    calc ∑ i : F, ∑ j : F, g i j = ∑ i : F, ∑ y ∈ F, g i y :=
          Finset.sum_congr rfl fun i _ => F.sum_coe_sort (g i)
      _ = _ := F.sum_coe_sort fun x => ∑ y ∈ F, g x y
  have h := quadForm_hadamard_sq_le_of_posSemidef hF fun i : F => c i
  simp only [h2, h3, S, of_apply] at h
  rw [← key, ← key]
  exact h

/-- The finite truncations of the right-hand form are bounded by the full form. -/
theorem sum_hadamard_cube_le_tsum {V : Type*} (T : V → V → ℝ≥0∞) (b : V → ℝ≥0∞)
    (F : Finset V) :
    ∑ x ∈ F, ∑ y ∈ F, b x * (T x y * ∑ u ∈ F, ∑ w ∈ F, T x u * T u w * T w y) * b y ≤
      ∑' x, ∑' y, b x * (T x y * ∑' u, ∑' w, T x u * T u w * T w y) * b y := by
  calc _ ≤ ∑ x ∈ F, ∑ y ∈ F, b x * (T x y * ∑' u, ∑' w, T x u * T u w * T w y) * b y := by
        gcongr with x _ y _
        exact (Finset.sum_le_sum fun u _ => ENNReal.sum_le_tsum F).trans (ENNReal.sum_le_tsum F)
    _ ≤ _ := (Finset.sum_le_sum fun x _ => ENNReal.sum_le_tsum F).trans (ENNReal.sum_le_tsum F)

/-- **Quadratic-form comparison for an infinite nonnegative kernel.** Let `T : V → V → [0, ∞]`
have finite entries and positive semidefinite finite principal submatrices. Then for every
finite-valued `b`, `∑_{x,y} b(x) T²(x,y)² b(y) ≤ ∑_{x,y} b(x) T(x,y) T³(x,y) b(y)` in `[0, ∞]`. -/
theorem tsum_quadForm_hadamard_sq_le_of_posSemidef {V : Type*} (T : V → V → ℝ≥0∞)
    (hT : ∀ x y, T x y ≠ ⊤)
    (hpos : ∀ F : Finset V, (Matrix.of fun i j : F => (T i j).toReal).PosSemidef)
    (b : V → ℝ≥0∞) (hb : ∀ x, b x ≠ ⊤) :
    ∑' x, ∑' y, b x * (∑' u, T x u * T u y) ^ 2 * b y ≤
      ∑' x, ∑' y, b x * (T x y * ∑' u, ∑' w, T x u * T u w * T w y) * b y := by
  classical
  set R := ∑' x, ∑' y, b x * (T x y * ∑' u, ∑' w, T x u * T u w * T w y) * b y
  -- Finite version on a finset `F`, in `[0, ∞]`.
  have hfin : ∀ F : Finset V,
      ∑ x ∈ F, ∑ y ∈ F, b x * (∑ u ∈ F, T x u * T u y) ^ 2 * b y ≤ R := by
    intro F
    refine le_trans ?_ (sum_hadamard_cube_le_tsum T b F)
    obtain ⟨t, rfl⟩ : ∃ t : V → V → ℝ≥0, T = fun x y => (t x y : ℝ≥0∞) :=
      ⟨fun x y => (T x y).toNNReal, by ext x y; simp [hT]⟩
    obtain ⟨c, rfl⟩ : ∃ c : V → ℝ≥0, b = fun x => (c x : ℝ≥0∞) :=
      ⟨fun x => (b x).toNNReal, by ext x; simp [hb]⟩
    have hF := hpos F
    simp only [ENNReal.coe_toReal] at hF
    have h := sum_quadForm_hadamard_sq_le_of_posSemidef (fun x y => (t x y : ℝ)) F hF
      (fun x => (c x : ℝ))
    beta_reduce
    norm_cast
    rw [← NNReal.coe_le_coe]
    push_cast
    exact h
  -- Pass to the limit in the inner sum, for finite outer index sets.
  have hst : ∀ s t : Finset V,
      ∑ x ∈ s, ∑ y ∈ t, b x * (∑' u, T x u * T u y) ^ 2 * b y ≤ R := by
    intro s t
    have hlim : Tendsto (fun r : Finset V =>
        ∑ x ∈ s, ∑ y ∈ t, b x * (∑ u ∈ r, T x u * T u y) ^ 2 * b y) atTop
        (𝓝 (∑ x ∈ s, ∑ y ∈ t, b x * (∑' u, T x u * T u y) ^ 2 * b y)) := by
      refine tendsto_finsetSum s fun x _ => tendsto_finsetSum t fun y _ => ?_
      have h1 : Tendsto (fun r : Finset V => ∑ u ∈ r, T x u * T u y) atTop
          (𝓝 (∑' u, T x u * T u y)) := ENNReal.summable.hasSum
      have h2 := ((ENNReal.continuous_pow 2).tendsto _).comp h1
      exact ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul h2 (Or.inr (hb x))) (Or.inr (hb y))
    refine le_of_tendsto' hlim fun r => le_trans ?_ (hfin (s ∪ t ∪ r))
    calc ∑ x ∈ s, ∑ y ∈ t, b x * (∑ u ∈ r, T x u * T u y) ^ 2 * b y
        ≤ ∑ x ∈ s, ∑ y ∈ t, b x * (∑ u ∈ s ∪ t ∪ r, T x u * T u y) ^ 2 * b y := by
          gcongr with x _ y _
          exact Finset.subset_union_right
      _ ≤ ∑ x ∈ s, ∑ y ∈ s ∪ t ∪ r, b x * (∑ u ∈ s ∪ t ∪ r, T x u * T u y) ^ 2 * b y :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset
            (Finset.subset_union_right.trans Finset.subset_union_left)
      _ ≤ _ := Finset.sum_le_sum_of_subset
            (Finset.subset_union_left.trans Finset.subset_union_left)
  -- Pass to the limit in the outer sums.
  rw [← ENNReal.tsum_prod, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun P => le_trans ?_ (hst (P.image Prod.fst) (P.image Prod.snd))
  rw [← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset Finset.subset_product

end PercLib.Analysis
