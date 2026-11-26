/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the connection-kernels assertion 530W, proved from
`BlockPositivity.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.BlockPositivity

/-!
# Positive block matrices: correspondence

Wiki correspondence for the Schur complement criterion for bounded block operators on `ℓ²(V)`
and the criterion for equal-diagonal block matrices on an arbitrary index set, from
`PercLib/Analysis/BlockPositivity.lean`.

## Main results

* `block_nonneg_iff_schur_complement_and_posSemidef_fromBlocks_iff`
-/

@[expose] public section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PercLib.Analysis

/-- **530W.** Let `S, T` be bounded self-adjoint real operators on `ℓ²(V)`, `X` bounded, and
`T ≥ δ I` with `δ > 0` (as quadratic forms on finitely supported vectors). Then the block
operator `[[S, X], [X†, T]]` is positive (nonnegative quadratic form on finitely supported pairs)
if and only if the Schur complement `S - X T⁻¹ X†` is, with `T⁻¹ = Ring.inverse T`. For
symmetric real matrices `A, B` on `V` (no boundedness), `[[A, B], [B, A]]` is positive
semidefinite if and only if `A + B` and `A - B` are; more generally, for every real `δ`,
`[[A, B], [B, A]] ≥ δ I` if and only if `A + B ≥ δ I` and `A - B ≥ δ I`. -/
@[tag "530W"]
theorem block_nonneg_iff_schur_complement_and_posSemidef_fromBlocks_iff {V : Type*}
    [DecidableEq V] :
    (∀ S T X : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
      IsSelfAdjoint S → IsSelfAdjoint T → ∀ δ : ℝ, 0 < δ →
      (∀ f : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 → δ * ‖f‖ ^ 2 ≤ ⟪f, T f⟫_ℝ) →
      ((∀ f g : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 → Memℓp (⇑g) 0 →
          0 ≤ ⟪f, S f + X g⟫_ℝ + ⟪g, ContinuousLinearMap.adjoint X f + T g⟫_ℝ) ↔
        ∀ f : lp (fun _ : V => ℝ) 2, Memℓp (⇑f) 0 →
          0 ≤ ⟪f, (S - X * Ring.inverse T * ContinuousLinearMap.adjoint X) f⟫_ℝ)) ∧
    (∀ A B : Matrix V V ℝ, A.IsHermitian → B.IsHermitian →
      ((fromBlocks A B B A).PosSemidef ↔ (A + B).PosSemidef ∧ (A - B).PosSemidef)) ∧
    (∀ A B : Matrix V V ℝ, A.IsHermitian → B.IsHermitian → ∀ δ : ℝ,
      ((fromBlocks A B B A - δ • (1 : Matrix (V ⊕ V) (V ⊕ V) ℝ)).PosSemidef ↔
        (A + B - δ • (1 : Matrix V V ℝ)).PosSemidef ∧
          (A - B - δ • (1 : Matrix V V ℝ)).PosSemidef)) :=
  ⟨fun S T X _ hT _ hδ hTδ => block_nonneg_iff_schur_complement_nonneg_ell2 S T X hT hδ hTδ,
    fun A B _ _ => posSemidef_fromBlocks_iff A B,
    fun A B _ _ δ => posSemidef_fromBlocks_sub_smul_one_iff A B δ⟩

end PercLib.Analysis
