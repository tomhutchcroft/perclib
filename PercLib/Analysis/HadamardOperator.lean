/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, from pinned mathlib's `lp` spaces, Hilbert adjoints and the Schur product theorem.
Mathematical reference: I. Schur, J. Reine Angew. Math. 140 (1911); the operator bound is the
standard weighted Cauchy–Schwarz estimate. No source text or code is copied.
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Entrywise products of bounded operators on `ℓ²`

For a bounded real operator `S` on `ℓ²(V)` write `S(x,y) = (S δ_y)(x)` for its matrix entries,
where `δ_y = lp.single 2 y 1`. The row `y ↦ S(x,y)` is the vector `S† δ_x`, and the column
`x ↦ S(x,y)` is `S δ_y`; both have norm at most `‖S‖`.

If `S` and `T` are bounded, the entrywise (Hadamard, Schur) product `S ∘ T` is again a bounded
operator, of norm at most `‖S‖ ‖T‖`: by Cauchy–Schwarz in `y`,
`|∑_y S(x,y) T(x,y) f(y)|² ≤ ‖S‖² ∑_y T(x,y)² f(y)²`, and summing over `x` uses the column
bound for `T`.

## Main results

* `PercLib.Analysis.hasSum_sq_apply_ell2`: `∑ₓ f(x)² = ‖f‖²` on real `ℓ²`.
* `PercLib.Analysis.apply_single_eq_adjoint_apply`: rows of a bounded operator.
* `PercLib.Analysis.exists_hadamard_ell2`: the entrywise product of two bounded operators on
  `ℓ²(V)` is a bounded operator, given by the absolutely convergent row sums, with
  `‖S ∘ T‖ ≤ ‖S‖ ‖T‖`; `exists_hadamard_ell2_norm_le` keeps the entries and the bound.
-/

@[expose] public section
noncomputable section

open scoped ENNReal InnerProductSpace

namespace PercLib.Analysis

variable {V : Type*}

/-- On real `ℓ²(V)`, `∑ₓ f(x)² = ‖f‖²`. -/
theorem hasSum_sq_apply_ell2 (f : lp (fun _ : V => ℝ) 2) :
    HasSum (fun x => f x ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) f
  simpa [Real.norm_eq_abs, sq_abs] using h

variable [DecidableEq V]

/-- Inner product with a unit coordinate vector of real `ℓ²` evaluates the other vector. -/
theorem inner_single_one_left_ell2 (x : V) (f : lp (fun _ : V => ℝ) 2) :
    ⟪lp.single 2 x (1 : ℝ), f⟫_ℝ = f x := by
  rw [lp.inner_single_left]; simp

/-- Inner product with a unit coordinate vector of real `ℓ²` evaluates the other vector. -/
theorem inner_single_one_right_ell2 (x : V) (f : lp (fun _ : V => ℝ) 2) :
    ⟪f, lp.single 2 x (1 : ℝ)⟫_ℝ = f x := by
  rw [real_inner_comm, inner_single_one_left_ell2]

/-- The rows of a bounded operator on real `ℓ²`: `S(x,y) = (S† δ_x)(y)`. -/
theorem apply_single_eq_adjoint_apply
    (S : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) (x y : V) :
    S (lp.single 2 y 1) x = (ContinuousLinearMap.adjoint S (lp.single 2 x 1)) y := by
  rw [← inner_single_one_left_ell2, ← inner_single_one_right_ell2,
    ContinuousLinearMap.adjoint_inner_left]

/-- A unit coordinate vector of `ℓ²` is mapped to a vector of norm at most `‖S‖`. -/
theorem norm_apply_single_le
    (S : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) (y : V) :
    ‖S (lp.single 2 y 1)‖ ≤ ‖S‖ := by
  simpa [lp.norm_single] using S.le_opNorm (lp.single 2 y (1 : ℝ))

/-- Every matrix entry of a bounded operator on real `ℓ²` is at most its norm. -/
theorem abs_apply_single_le
    (S : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) (x y : V) :
    |S (lp.single 2 y 1) x| ≤ ‖S‖ :=
  (lp.norm_apply_le_norm (by norm_num) _ x).trans (norm_apply_single_le S y)

/-- The rows of a bounded operator on real `ℓ²` have norm at most the operator norm. -/
theorem norm_adjoint_apply_single_le
    (S : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) (x : V) :
    ‖ContinuousLinearMap.adjoint S (lp.single 2 x 1)‖ ≤ ‖S‖ := by
  simpa [LinearIsometryEquiv.norm_map] using
    norm_apply_single_le (ContinuousLinearMap.adjoint S) x

/-- **Entrywise products of bounded operators.** If `S, T` are bounded real operators on
`ℓ²(V)`, there is a bounded operator `R` with matrix entries `R(x,y) = S(x,y) T(x,y)`, acting by
the convergent row sums `(R f)(x) = ∑_y S(x,y) T(x,y) f(y)`, and `‖R‖ ≤ ‖S‖ ‖T‖`. -/
theorem exists_hadamard_ell2
    (S T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) :
    ∃ R : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
      (∀ x y, R (lp.single 2 y 1) x = S (lp.single 2 y 1) x * T (lp.single 2 y 1) x) ∧
      (∀ f x, HasSum (fun y => S (lp.single 2 y 1) x * T (lp.single 2 y 1) x * f y) (R f x)) ∧
      ‖R‖ ≤ ‖S‖ * ‖T‖ := by
  set s : V → V → ℝ := fun x y => S (lp.single 2 y 1) x with hs
  set t : V → V → ℝ := fun x y => T (lp.single 2 y 1) x with ht
  set a : V → lp (fun _ : V => ℝ) 2 := fun x =>
    ContinuousLinearMap.adjoint S (lp.single 2 x 1) with ha
  have hsa : ∀ x y, s x y = a x y := apply_single_eq_adjoint_apply S
  -- the rows of the entrywise product
  have hmem_u : ∀ x, Memℓp (fun y => s x y * t x y) 2 := fun x =>
    ((lp.memℓp (a x)).norm.const_mul ‖T‖).mono fun y => by
      rw [norm_mul, hsa, mul_comm, Real.norm_eq_abs (t x y)]
      exact mul_le_mul_of_nonneg_right (abs_apply_single_le T x y) (norm_nonneg _)
  let u : V → lp (fun _ : V => ℝ) 2 := fun x => ⟨fun y => s x y * t x y, hmem_u x⟩
  have hu : ∀ x y, u x y = s x y * t x y := fun _ _ => rfl
  -- the products `t(x,·) f`
  have hmem_g : ∀ (f : lp (fun _ : V => ℝ) 2) x, Memℓp (fun y => t x y * f y) 2 := fun f x =>
    ((lp.memℓp f).norm.const_mul ‖T‖).mono fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (abs_apply_single_le T x y) (norm_nonneg _)
  let g : lp (fun _ : V => ℝ) 2 → V → lp (fun _ : V => ℝ) 2 := fun f x =>
    ⟨fun y => t x y * f y, hmem_g f x⟩
  have hg : ∀ f x y, g f x y = t x y * f y := fun _ _ _ => rfl
  have hug : ∀ f x, ⟪u x, f⟫_ℝ = ⟪a x, g f x⟫_ℝ := by
    intro f x
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun y => ?_
    simp only [hu, hg, RCLike.inner_apply, conj_trivial, hsa]
    ring
  -- the key estimate
  have hkey : ∀ (f : lp (fun _ : V => ℝ) 2) (A : Finset V),
      ∑ x ∈ A, ⟪u x, f⟫_ℝ ^ 2 ≤ (‖S‖ * ‖T‖ * ‖f‖) ^ 2 := by
    intro f A
    have hgx : ∀ x, HasSum (fun y => t x y ^ 2 * f y ^ 2) (‖g f x‖ ^ 2) := fun x => by
      simpa [hg, mul_pow] using hasSum_sq_apply_ell2 (g f x)
    have hf2 := hasSum_sq_apply_ell2 f
    have hcol : ∀ y, ∑ x ∈ A, t x y ^ 2 ≤ ‖T‖ ^ 2 := fun y => by
      have h := hasSum_sq_apply_ell2 (T (lp.single 2 y 1))
      refine (sum_le_hasSum A (fun _ _ => sq_nonneg _) h).trans ?_
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_apply_single_le T y) 2
    calc ∑ x ∈ A, ⟪u x, f⟫_ℝ ^ 2
        ≤ ∑ x ∈ A, ‖S‖ ^ 2 * ‖g f x‖ ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [hug, ← mul_pow, ← sq_abs]
          refine pow_le_pow_left₀ (abs_nonneg _) ((abs_real_inner_le_norm _ _).trans ?_) 2
          exact mul_le_mul_of_nonneg_right (norm_adjoint_apply_single_le S x) (norm_nonneg _)
      _ = ‖S‖ ^ 2 * ∑' y, (∑ x ∈ A, t x y ^ 2) * f y ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_congr rfl fun x _ => (hgx x).tsum_eq.symm,
            ← Summable.tsum_finsetSum fun x _ => (hgx x).summable]
          exact tsum_congr fun y => by rw [Finset.sum_mul]
      _ ≤ ‖S‖ ^ 2 * ∑' y, ‖T‖ ^ 2 * f y ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          refine Summable.tsum_le_tsum (fun y => ?_) ?_ (hf2.summable.mul_left _)
          · exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
          · exact (hasSum_sum fun x _ => hgx x).summable.congr fun y => by
              rw [Finset.sum_mul]
      _ = (‖S‖ * ‖T‖ * ‖f‖) ^ 2 := by
          rw [tsum_mul_left, hf2.tsum_eq]; ring
  have hmem_R : ∀ f : lp (fun _ : V => ℝ) 2, Memℓp (fun x => ⟪u x, f⟫_ℝ) 2 := fun f =>
    memℓp_gen' (C := (‖S‖ * ‖T‖ * ‖f‖) ^ 2) fun A => by
      simpa [Real.norm_eq_abs, sq_abs] using hkey f A
  let L : lp (fun _ : V => ℝ) 2 →ₗ[ℝ] lp (fun _ : V => ℝ) 2 :=
    { toFun := fun f => ⟨fun x => ⟪u x, f⟫_ℝ, hmem_R f⟩
      map_add' := fun f f' => by
        ext x
        exact inner_add_right _ _ _
      map_smul' := fun c f => by
        ext x
        exact inner_smul_right _ _ _ }
  have hL : ∀ f x, L f x = ⟪u x, f⟫_ℝ := fun _ _ => rfl
  have hLbound : ∀ f, ‖L f‖ ≤ ‖S‖ * ‖T‖ * ‖f‖ := fun f =>
    lp.norm_le_of_forall_sum_le (p := 2) (by norm_num) (by positivity) fun A => by
      simpa [hL, Real.norm_eq_abs, sq_abs] using hkey f A
  refine ⟨L.mkContinuous _ hLbound, fun x y => ?_, fun f x => ?_, ?_⟩
  · rw [LinearMap.mkContinuous_apply, hL, inner_single_one_right_ell2]
  · rw [LinearMap.mkContinuous_apply, hL]
    convert lp.hasSum_inner (u x) f using 1
    ext y
    simp only [RCLike.inner_apply, conj_trivial, hu]
    ring
  · exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The entrywise product of two bounded operators on real `ℓ²(V)` is the matrix of a bounded
operator of norm at most `‖S‖ ‖T‖`. -/
theorem exists_hadamard_ell2_norm_le
    (S T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) :
    ∃ R : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
      (∀ x y, R (lp.single 2 y 1) x = S (lp.single 2 y 1) x * T (lp.single 2 y 1) x) ∧
      ‖R‖ ≤ ‖S‖ * ‖T‖ :=
  (exists_hadamard_ell2 S T).imp fun _ h => ⟨h.1, h.2.2⟩

end PercLib.Analysis
