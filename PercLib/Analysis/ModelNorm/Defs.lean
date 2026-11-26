/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
A norm on a real vector space, bundled as a seminorm that vanishes only at `0`: the model norm
`‖·‖` on `ℝ^d` of Definition I.1.3 of T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, where any norm is allowed. New definitions and proofs. Mathlib at the pinned
revision has no bundled norm-as-a-function type (`AddGroupNorm` has no homogeneity, and
`NormedSpace.Core` needs a `Norm` instance).
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Model norms

A `ModelNorm E` is a seminorm `N : Seminorm ℝ E` together with definiteness,
`N x = 0 → x = 0`. It coerces to `Seminorm ℝ E`, so every definition that takes a seminorm
(the long-range kernels, the Lévy densities) accepts a model norm unchanged, and it is a
`SeminormClass`, so the seminorm API (`map_smul_eq_mul`, `apply_nonneg`, `map_sub_rev`,
`map_add_le_add`) applies to it directly.

The type synonym `WithModelNorm N` of `E` carries `N` as its norm instance. It is a proof
device that gives access to mathlib's normed-space theory; on `ℝ^d` it yields the continuity
of `N` and its comparability with the sup norm from finite-dimensional theory.

## Main definitions

* `ModelNorm E`: a norm on the real vector space `E`, as a definite seminorm.
* `ModelNorm.ofNorm F`: the norm of a normed space `F`.
* `ModelNorm.comp N e`: the norm `N` transported along a linear equivalence `e`.
* `WithModelNorm N`: `E` with the norm `N` as its normed-space structure, and
  `WithModelNorm.equiv N : E ≃ₗ[ℝ] WithModelNorm N`.

## Main results

* `ModelNorm.map_eq_zero_iff`, `ModelNorm.pos_iff_ne_zero`: definiteness (a model norm is an
  `AddGroupNormClass`, so mathlib's `map_eq_zero_iff_eq_zero` and `map_pos_of_ne_zero` apply).
* `ModelNorm.continuous`: a model norm on a finite-dimensional space is continuous.
* `ModelNorm.exists_le_mul_norm`, `ModelNorm.exists_pos_mul_norm_le`: on a finite-dimensional
  normed space, a model norm is comparable with the ambient norm.
-/

@[expose] public section

noncomputable section

namespace PercLib.Analysis

/-- A norm on a real vector space: a seminorm that vanishes only at `0`. -/
structure ModelNorm (E : Type*) [AddCommGroup E] [Module ℝ E] extends Seminorm ℝ E where
  eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0

namespace ModelNorm

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]

instance : FunLike (ModelNorm E) E ℝ where
  coe N := N.toFun
  coe_injective := by
    rintro ⟨N, _⟩ ⟨N', _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : SeminormClass (ModelNorm E) ℝ E where
  map_zero N := map_zero N.toSeminorm
  map_add_le_add N := map_add_le_add N.toSeminorm
  map_neg_eq_map N := map_neg_eq_map N.toSeminorm
  map_smul_eq_mul N := map_smul_eq_mul N.toSeminorm

instance : AddGroupNormClass (ModelNorm E) E ℝ :=
  { (inferInstance : SeminormClass (ModelNorm E) ℝ E).toAddGroupSeminormClass with
    eq_zero_of_map_eq_zero := fun N {x} h => N.eq_zero_of_map_eq_zero' x h }

instance : Coe (ModelNorm E) (Seminorm ℝ E) := ⟨toSeminorm⟩

@[simp] theorem coe_toSeminorm (N : ModelNorm E) : ⇑N.toSeminorm = N := rfl

theorem toSeminorm_injective : Function.Injective (toSeminorm : ModelNorm E → Seminorm ℝ E) := by
  rintro ⟨N, _⟩ ⟨N', _⟩ h
  congr

@[ext] theorem ext {N N' : ModelNorm E} (h : ∀ x, N x = N' x) : N = N' :=
  DFunLike.ext _ _ h

theorem eq_zero_of_map_eq_zero (N : ModelNorm E) {x : E} (h : N x = 0) : x = 0 :=
  N.eq_zero_of_map_eq_zero' x h

/-- Definiteness in the form of a hypothesis on the underlying seminorm. -/
theorem forall_eq_zero (N : ModelNorm E) : ∀ x, N.toSeminorm x = 0 → x = 0 :=
  N.eq_zero_of_map_eq_zero'

@[simp] theorem map_eq_zero_iff (N : ModelNorm E) {x : E} : N x = 0 ↔ x = 0 :=
  map_eq_zero_iff_eq_zero N

theorem pos_iff_ne_zero (N : ModelNorm E) {x : E} : 0 < N x ↔ x ≠ 0 :=
  (apply_nonneg N x).lt_iff_ne'.trans (map_ne_zero_iff_ne_zero N)

/-- The norm of a normed space as a model norm. -/
def ofNorm (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] : ModelNorm F :=
  { normSeminorm ℝ F with eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.1 }

@[simp] theorem coe_ofNorm (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ⇑(ofNorm F) = norm := rfl

@[simp] theorem toSeminorm_ofNorm (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ofNorm F).toSeminorm = normSeminorm ℝ F := rfl

/-- A model norm transported along a linear equivalence: `x ↦ N (e x)`. -/
def comp [AddCommGroup F] [Module ℝ F] (N : ModelNorm F) (e : E ≃ₗ[ℝ] F) : ModelNorm E :=
  { N.toSeminorm.comp e.toLinearMap with
    eq_zero_of_map_eq_zero' := fun _ hx => e.map_eq_zero_iff.1 (N.eq_zero_of_map_eq_zero hx) }

@[simp] theorem coe_comp [AddCommGroup F] [Module ℝ F] (N : ModelNorm F) (e : E ≃ₗ[ℝ] F) :
    ⇑(N.comp e) = N ∘ e := rfl

theorem comp_apply [AddCommGroup F] [Module ℝ F] (N : ModelNorm F) (e : E ≃ₗ[ℝ] F) (x : E) :
    N.comp e x = N (e x) := rfl

@[simp] theorem toSeminorm_comp [AddCommGroup F] [Module ℝ F] (N : ModelNorm F)
    (e : E ≃ₗ[ℝ] F) : (N.comp e).toSeminorm = N.toSeminorm.comp e.toLinearMap := rfl

end ModelNorm

/-! ### The synonym carrying a model norm as its norm -/

/-- `E` with the norm `N` as its norm, and the topology, distance and bornology of `N`. -/
def WithModelNorm {E : Type*} [AddCommGroup E] [Module ℝ E] (_N : ModelNorm E) : Type _ := E

namespace WithModelNorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (N : ModelNorm E)

instance : AddCommGroup (WithModelNorm N) := ‹AddCommGroup E›
instance : Module ℝ (WithModelNorm N) := ‹Module ℝ E›

/-- The identity, as a linear equivalence into the synonym. -/
def equiv : E ≃ₗ[ℝ] WithModelNorm N := LinearEquiv.refl ℝ E

instance : Norm (WithModelNorm N) := ⟨fun x => N ((equiv N).symm x)⟩

@[simp] theorem norm_equiv (x : E) : ‖equiv N x‖ = N x := rfl

theorem norm_def (x : WithModelNorm N) : ‖x‖ = N ((equiv N).symm x) := rfl

/-- The normed-space axioms of the synonym. -/
theorem normedSpaceCore : NormedSpace.Core ℝ (WithModelNorm N) where
  norm_nonneg x := apply_nonneg N ((equiv N).symm x)
  norm_smul c x := map_smul_eq_mul N c ((equiv N).symm x)
  norm_triangle x y := map_add_le_add N ((equiv N).symm x) ((equiv N).symm y)
  norm_eq_zero_iff _ := N.map_eq_zero_iff

instance : NormedAddCommGroup (WithModelNorm N) := .ofCore (normedSpaceCore N)
instance : NormedSpace ℝ (WithModelNorm N) := .ofCore (normedSpaceCore N)

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ (WithModelNorm N) :=
  inferInstanceAs (FiniteDimensional ℝ E)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- On a finite-dimensional normed space, the identity into the synonym is a continuous linear
equivalence. -/
def toCLE (N : ModelNorm E) : E ≃L[ℝ] WithModelNorm N :=
  (equiv N).toContinuousLinearEquiv

@[simp] theorem toCLE_apply (N : ModelNorm E) (x : E) : toCLE N x = equiv N x := rfl

@[simp] theorem toCLE_symm_apply (N : ModelNorm E) (x : WithModelNorm N) :
    (toCLE N).symm x = (equiv N).symm x := rfl

end WithModelNorm

namespace ModelNorm

open WithModelNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A model norm on a finite-dimensional normed space is continuous. -/
protected theorem continuous (N : ModelNorm E) : Continuous N :=
  continuous_norm.comp (toCLE N).continuous

/-- On a finite-dimensional normed space, a model norm is bounded by a multiple of the
ambient norm. -/
theorem exists_le_mul_norm (N : ModelNorm E) : ∃ C, 0 < C ∧ ∀ v : E, N v ≤ C * ‖v‖ :=
  ⟨‖(toCLE N : E →L[ℝ] WithModelNorm N)‖ + 1, by positivity, fun v =>
    ((toCLE N : E →L[ℝ] WithModelNorm N).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v))⟩

/-- **Equivalence of norms**: on a finite-dimensional normed space, a model norm dominates a
positive multiple of the ambient norm. -/
theorem exists_pos_mul_norm_le (N : ModelNorm E) : ∃ κ, 0 < κ ∧ ∀ v : E, κ * ‖v‖ ≤ N v := by
  set C := ‖((toCLE N).symm : WithModelNorm N →L[ℝ] E)‖ + 1
  have hC : 0 < C := by positivity
  refine ⟨C⁻¹, inv_pos.2 hC, fun v => ?_⟩
  have h := ((toCLE N).symm : WithModelNorm N →L[ℝ] E).le_opNorm (equiv N v)
  have h' : ‖v‖ ≤ C * N v :=
    h.trans (mul_le_mul_of_nonneg_right (by simp [C]) (apply_nonneg N v))
  rw [inv_mul_le_iff₀ hC]
  exact h'

end ModelNorm

end PercLib.Analysis
