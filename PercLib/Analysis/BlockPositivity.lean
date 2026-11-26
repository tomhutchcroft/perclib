/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, from pinned mathlib's positive semidefinite matrices, `lp` spaces, Hilbert adjoints
and the Lax–Milgram theorem. Mathematical reference: the Schur complement criterion for positive
block operators (e.g. R. Bhatia, *Positive Definite Matrices*, Princeton 2007, §1.3). No source
text or code is copied.
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Order.Star.Real

/-!
# Positive block matrices and Schur complements

Two criteria for positivity of a `2 × 2` block matrix.

* For arbitrary real matrices `A, B` on any index set `V` (positive semidefiniteness is
  `Matrix.PosSemidef`, a condition on finitely supported vectors, so no boundedness is involved),
  `[[A, B], [B, A]] ≥ δ I` if and only if `A + B ≥ δ I` and `A - B ≥ δ I`. On a finite index set
  this is conjugation by the invertible matrix `[[1, 1], [1, -1]]`; in general, positive
  semidefiniteness is decided by finite principal submatrices.
* For bounded operators on `ℓ²(V)` with `T ≥ δ I`, `δ > 0`, the block operator
  `[[S, X], [X†, T]]` is positive if and only if the Schur complement `S - X T⁻¹ X†` is. Positivity
  is tested on finitely supported vectors (those `f` with `Memℓp f 0`), and the inverse of `T`
  is `Ring.inverse T`, which is a genuine inverse by the Lax–Milgram theorem.

## Main results

* `PercLib.Analysis.posSemidef_iff_forall_finset_submatrix`
* `PercLib.Analysis.posSemidef_fromBlocks_sub_smul_one_iff`
* `PercLib.Analysis.posSemidef_fromBlocks_iff`
* `PercLib.Analysis.nonneg_of_forall_memℓp_zero_ell2`: density of finitely supported vectors.
* `PercLib.Analysis.isUnit_of_inner_self_ge_ell2`
* `PercLib.Analysis.block_nonneg_iff_schur_complement_nonneg_ell2`
-/

@[expose] public section
noncomputable section

open Matrix Filter Topology
open scoped InnerProductSpace

namespace PercLib.Analysis

/-! ### Matrices on an arbitrary index set -/

section Matrices

/-- A real matrix on any index set is positive semidefinite if and only if all its finite
principal submatrices are. -/
theorem posSemidef_iff_forall_finset_submatrix {ι : Type*} (M : Matrix ι ι ℝ) :
    M.PosSemidef ↔ ∀ s : Finset ι, (M.submatrix ((↑) : s → ι) (↑)).PosSemidef := by
  classical
  refine ⟨fun h s => h.submatrix _, fun h => ⟨IsHermitian.ext fun i j => ?_, fun x => ?_⟩⟩
  · have := (h {i, j}).1.apply ⟨i, by simp⟩ ⟨j, by simp⟩
    simpa using this
  · simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
      ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using (h x.support).2 _

variable {m n : Type*}

/-- A block-diagonal real matrix on a finite index set is positive semidefinite if and only if
both diagonal blocks are. -/
theorem posSemidef_fromBlocks_zero_iff [Fintype m] [Fintype n] (D₁ : Matrix m m ℝ)
    (D₂ : Matrix n n ℝ) :
    (fromBlocks D₁ 0 0 D₂).PosSemidef ↔ D₁.PosSemidef ∧ D₂.PosSemidef := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · convert h.submatrix Sum.inl using 1
    ext i j; rfl
  · convert h.submatrix Sum.inr using 1
    ext i j; rfl
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨h.1.1.fromBlocks (by simp) h.2.1, fun x => ?_⟩
    have h₁ := h.1.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h₂ := h.2.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by ext (i | i) <;> rfl
    rw [hx, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add]
    simpa [dotProduct, Fintype.sum_sum_type] using add_nonneg h₁ h₂

/-- **Equal-diagonal block matrices, finite case.** For real matrices `A, B` on a finite index
set and any real `δ`, `[[A, B], [B, A]] - δ I` is positive semidefinite if and only if
`A + B - δ I` and `A - B - δ I` are. -/
theorem posSemidef_fromBlocks_sub_smul_one_iff_of_fintype [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (δ : ℝ) :
    (fromBlocks A B B A - δ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).PosSemidef ↔
      (A + B - δ • (1 : Matrix n n ℝ)).PosSemidef ∧
        (A - B - δ • (1 : Matrix n n ℝ)).PosSemidef := by
  set U : Matrix (n ⊕ n) (n ⊕ n) ℝ := fromBlocks 1 1 1 (-1)
  have hUU : U * U = (2 : ℝ) • 1 := by
    simp only [U, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
    congr 1 <;> simp <;> module
  have hU : IsUnit U := ⟨⟨U, (1 / 2 : ℝ) • U, by
    rw [mul_smul_comm, hUU, smul_smul]; norm_num, by
    rw [smul_mul_assoc, hUU, smul_smul]; norm_num⟩, rfl⟩
  have hsU : star U = U := by
    simp only [U, star_eq_conjTranspose, fromBlocks_conjTranspose]
    simp
  have key : star U * (fromBlocks A B B A - δ • 1) * U =
      fromBlocks ((2 : ℝ) • (A + B - δ • 1)) 0 0 ((2 : ℝ) • (A - B - δ • 1)) := by
    have hM : fromBlocks A B B A - δ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        fromBlocks (A - δ • 1) B B (A - δ • 1) := by
      rw [← fromBlocks_one, fromBlocks_smul]
      ext (i | i) (j | j) <;> simp
    rw [hsU, hM]
    simp only [U, fromBlocks_multiply]
    congr 1 <;> simp <;> module
  rw [← Matrix.IsUnit.posSemidef_star_left_conjugate_iff hU, key,
    posSemidef_fromBlocks_zero_iff]
  have h2 : ∀ M : Matrix n n ℝ, ((2 : ℝ) • M).PosSemidef ↔ M.PosSemidef := fun M =>
    ⟨fun h => by simpa [smul_smul] using h.smul (a := (1 / 2 : ℝ)) (by norm_num),
      fun h => h.smul (by norm_num)⟩
  rw [h2, h2]

/-- **Equal-diagonal block matrices.** For real matrices `A, B` on any index set `V` and any
real `δ`, `[[A, B], [B, A]] ≥ δ I` if and only if `A + B ≥ δ I` and `A - B ≥ δ I`, where
`M ≥ δ I` means that `M - δ I` is positive semidefinite (nonnegative quadratic form on finitely
supported vectors, and symmetric). -/
theorem posSemidef_fromBlocks_sub_smul_one_iff {V : Type*} [DecidableEq V]
    (A B : Matrix V V ℝ) (δ : ℝ) :
    (fromBlocks A B B A - δ • (1 : Matrix (V ⊕ V) (V ⊕ V) ℝ)).PosSemidef ↔
      (A + B - δ • (1 : Matrix V V ℝ)).PosSemidef ∧
        (A - B - δ • (1 : Matrix V V ℝ)).PosSemidef := by
  -- the restriction of `M` to `s ⊕ s`
  have hres : ∀ s : Finset V,
      (fromBlocks A B B A - δ • (1 : Matrix (V ⊕ V) (V ⊕ V) ℝ)).submatrix
          (Sum.map Subtype.val Subtype.val) (Sum.map Subtype.val Subtype.val) =
        fromBlocks (A.submatrix Subtype.val Subtype.val) (B.submatrix Subtype.val Subtype.val)
          (B.submatrix Subtype.val Subtype.val)
          (A.submatrix Subtype.val Subtype.val) - δ • (1 : Matrix (s ⊕ s) (s ⊕ s) ℝ) := by
    intro s
    ext (i | i) (j | j) <;> simp [one_apply]
  have hsub : ∀ (s : Finset V) (C : Matrix V V ℝ),
      (C - δ • (1 : Matrix V V ℝ)).submatrix Subtype.val Subtype.val =
        C.submatrix Subtype.val Subtype.val - δ • (1 : Matrix s s ℝ) := by
    intro s C
    ext i j
    simp [one_apply]
  have hfin : ∀ s : Finset V,
      ((fromBlocks A B B A - δ • (1 : Matrix (V ⊕ V) (V ⊕ V) ℝ)).submatrix
        (Sum.map (Subtype.val : s → V) (Subtype.val : s → V))
        (Sum.map (Subtype.val : s → V) (Subtype.val : s → V))).PosSemidef ↔
        ((A + B - δ • (1 : Matrix V V ℝ)).submatrix (Subtype.val : s → V) Subtype.val).PosSemidef ∧
        ((A - B - δ • (1 : Matrix V V ℝ)).submatrix (Subtype.val : s → V)
          Subtype.val).PosSemidef := by
    intro s
    rw [hres, posSemidef_fromBlocks_sub_smul_one_iff_of_fintype, hsub, hsub]
    simp [submatrix_add, submatrix_sub]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [posSemidef_iff_forall_finset_submatrix, posSemidef_iff_forall_finset_submatrix]
    exact ⟨fun s => ((hfin s).1 (h.submatrix _)).1, fun s => ((hfin s).1 (h.submatrix _)).2⟩
  · obtain ⟨h₁, h₂⟩ := h
    rw [posSemidef_iff_forall_finset_submatrix] at h₁ h₂ ⊢
    intro t
    classical
    set s : Finset V := t.image (Sum.elim id id)
    let e : t → s ⊕ s := fun p =>
      match p with
      | ⟨Sum.inl v, hv⟩ => Sum.inl ⟨v, Finset.mem_image.2 ⟨_, hv, rfl⟩⟩
      | ⟨Sum.inr v, hv⟩ => Sum.inr ⟨v, Finset.mem_image.2 ⟨_, hv, rfl⟩⟩
    have he : Sum.map Subtype.val Subtype.val ∘ e = (↑) := by
      funext p
      rcases p with ⟨v | v, hv⟩ <;> rfl
    have := ((hfin s).2 ⟨h₁ s, h₂ s⟩).submatrix e
    rwa [submatrix_submatrix, he] at this

/-- **Equal-diagonal block matrices, `δ = 0`.** For real matrices `A, B` on any index set,
`[[A, B], [B, A]]` is positive semidefinite if and only if `A + B` and `A - B` are. -/
theorem posSemidef_fromBlocks_iff {V : Type*} (A B : Matrix V V ℝ) :
    (fromBlocks A B B A).PosSemidef ↔ (A + B).PosSemidef ∧ (A - B).PosSemidef := by
  classical
  simpa using posSemidef_fromBlocks_sub_smul_one_iff A B 0

end Matrices

/-! ### Bounded operators on `ℓ²` -/

section Operators

variable {V : Type*}

/-- The partial sums `∑_{i ∈ s} f(i) δ_i` are finitely supported. -/
theorem memℓp_zero_sum_single_ell2 [DecidableEq V] (f : lp (fun _ : V => ℝ) 2) (s : Finset V) :
    Memℓp (⇑(∑ i ∈ s, lp.single 2 i (f i))) 0 := by
  refine memℓp_zero_iff.2 (s.finite_toSet.subset fun j hj => ?_)
  by_contra hjs
  apply hj
  rw [lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi => by
    rw [lp.single_apply, Pi.single_eq_of_ne]; rintro rfl; exact hjs hi

/-- **Density of finitely supported vectors.** A continuous real function on `ℓ²(V) × ℓ²(V)`
which is nonnegative at all pairs of finitely supported vectors is nonnegative. -/
theorem nonneg_of_forall_memℓp_zero_ell2
    {Φ : lp (fun _ : V => ℝ) 2 × lp (fun _ : V => ℝ) 2 → ℝ} (hΦ : Continuous Φ)
    (h : ∀ f g : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 → Memℓp (⇑g) 0 → 0 ≤ Φ (f, g))
    (f g : lp (fun _ : V => ℝ) 2) : 0 ≤ Φ (f, g) := by
  classical
  have hf := (lp.hasSum_single (p := 2) (by simp) f)
  have hg := (lp.hasSum_single (p := 2) (by simp) g)
  have ht : Tendsto (fun s : Finset V =>
      Φ (∑ i ∈ s, lp.single 2 i (f i), ∑ i ∈ s, lp.single 2 i (g i))) atTop (𝓝 (Φ (f, g))) :=
    (hΦ.tendsto _).comp (hf.prodMk_nhds hg)
  exact ge_of_tendsto' ht fun s =>
    h _ _ (memℓp_zero_sum_single_ell2 f s) (memℓp_zero_sum_single_ell2 g s)

/-- A bounded operator on real `ℓ²(V)` with `⟪f, T f⟫ ≥ δ ‖f‖²`, `δ > 0`, is invertible
(Lax–Milgram). -/
theorem isUnit_of_inner_self_ge_ell2
    (T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) {δ : ℝ} (hδ : 0 < δ)
    (hT : ∀ f, δ * ‖f‖ ^ 2 ≤ ⟪f, T f⟫_ℝ) : IsUnit T := by
  have hB : IsCoercive ((innerSL ℝ).comp T) := ⟨δ, hδ, fun u => by
    simpa [sq, mul_assoc, real_inner_comm] using hT u⟩
  set e := hB.continuousLinearEquivOfBilin
  have he : (e : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) = T := by
    ext1 v
    refine ext_inner_right ℝ fun w => ?_
    rw [ContinuousLinearEquiv.coe_coe, hB.continuousLinearEquivOfBilin_apply]
    simp [real_inner_comm]
  exact he ▸ ⟨⟨e, e.symm, by ext1 v; simp, by ext1 v; simp⟩, rfl⟩

/-- **Schur complements.** Let `S, T, X` be bounded operators on real `ℓ²(V)`, `T` self-adjoint
with `⟪f, T f⟫ ≥ δ ‖f‖²` for finitely supported `f`, where `δ > 0`. Then the block operator
`[[S, X], [X†, T]]` has nonnegative quadratic form on finitely supported pairs if and only if the
Schur complement `S - X T⁻¹ X†` does. Here `T⁻¹ = Ring.inverse T`, a genuine inverse by
`isUnit_of_inner_self_ge_ell2`. -/
theorem block_nonneg_iff_schur_complement_nonneg_ell2
    (S T X : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) (hT : IsSelfAdjoint T)
    {δ : ℝ} (hδ : 0 < δ)
    (hTδ : ∀ f : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 → δ * ‖f‖ ^ 2 ≤ ⟪f, T f⟫_ℝ) :
    (∀ f g : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 → Memℓp (⇑g) 0 →
        0 ≤ ⟪f, S f + X g⟫_ℝ + ⟪g, ContinuousLinearMap.adjoint X f + T g⟫_ℝ) ↔
      ∀ f : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 →
        0 ≤ ⟪f, (S - X * Ring.inverse T * ContinuousLinearMap.adjoint X) f⟫_ℝ := by
  set Xa := ContinuousLinearMap.adjoint X
  -- `T ≥ δ I` on all vectors, by density
  have hTδ' : ∀ f, δ * ‖f‖ ^ 2 ≤ ⟪f, T f⟫_ℝ := fun f => by
    have := nonneg_of_forall_memℓp_zero_ell2 (Φ := fun p => ⟪p.1, T p.1⟫_ℝ - δ * ‖p.1‖ ^ 2)
      (by fun_prop) (fun f _ hf _ => sub_nonneg.2 (hTδ f hf)) f f
    linarith
  obtain ⟨u, hu⟩ := isUnit_of_inner_self_ge_ell2 T hδ hTδ'
  set Ti := Ring.inverse T
  have hinv : Ti = ↑u⁻¹ := by simp only [Ti, ← hu, Ring.inverse_unit]
  have hTi : ∀ y, T (Ti y) = y := fun y => by
    rw [← hu, hinv]
    change ((↑u : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) * ↑u⁻¹) y = y
    rw [u.mul_inv]
    rfl
  have hT0 : ∀ k, 0 ≤ ⟪k, T k⟫_ℝ := fun k => (by positivity : 0 ≤ δ * ‖k‖ ^ 2).trans (hTδ' k)
  -- completing the square
  have hid : ∀ f g, ⟪f, S f + X g⟫_ℝ + ⟪g, Xa f + T g⟫_ℝ =
      ⟪f, (S - X * Ti * Xa) f⟫_ℝ + ⟪g + Ti (Xa f), T (g + Ti (Xa f))⟫_ℝ := by
    intro f g
    have h1 : ⟪Ti (Xa f), T g⟫_ℝ = ⟪f, X g⟫_ℝ := by
      rw [← hT.adjoint_eq, ContinuousLinearMap.adjoint_inner_right, hTi,
        ContinuousLinearMap.adjoint_inner_left]
    have h2 : ⟪Ti (Xa f), Xa f⟫_ℝ = ⟪f, X (Ti (Xa f))⟫_ℝ :=
      (real_inner_comm _ _).trans (ContinuousLinearMap.adjoint_inner_left X (Ti (Xa f)) f)
    have hC : (S - X * Ti * Xa) f = S f - X (Ti (Xa f)) := rfl
    rw [hC]
    simp only [map_add, inner_add_left, inner_add_right, inner_sub_right, hTi, h1, h2]
    ring
  constructor
  · intro h f _
    have hall := nonneg_of_forall_memℓp_zero_ell2
      (Φ := fun p => ⟪p.1, S p.1 + X p.2⟫_ℝ + ⟪p.2, Xa p.1 + T p.2⟫_ℝ) (by fun_prop)
      (fun f g hf hg => h f g hf hg) f (-Ti (Xa f))
    dsimp only at hall
    rwa [hid, neg_add_cancel, map_zero, inner_zero_left, add_zero] at hall
  · intro h f g hf _
    rw [hid]
    exact add_nonneg (h f hf) (hT0 _)

end Operators

end PercLib.Analysis
