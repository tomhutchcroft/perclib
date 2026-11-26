/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the connection-kernels assertion TAB8, proved from pinned mathlib's
Schur product theorem and `HadamardOperator.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.HadamardOperator
public import Mathlib.Analysis.Matrix.Order

/-!
# Schur products: correspondence

Wiki correspondence for Schur positivity of entrywise products of positive semidefinite
matrices on an arbitrary index set (`Matrix.PosSemidef` quantifies over finitely supported
vectors, so no finiteness or boundedness is needed) and for the operator-norm bound of the
entrywise product of bounded operators on `ℓ²(V)`, from
`PercLib/Analysis/HadamardOperator.lean`.

## Main results

* `posSemidef_hadamard_and_exists_hadamard_ell2_norm_le`
-/

@[expose] public section
noncomputable section

open Matrix

namespace PercLib.Analysis

/-- **TAB8.** If `S, T` are positive semidefinite real matrices on an index set `V` (quadratic
forms nonnegative on finitely supported vectors), then so is the entrywise product `S ⊙ T`.
If instead `S, T` are bounded real operators on `ℓ²(V)`, with matrix entries
`S(x,y) = (S δ_y)(x)`, then the entrywise product is the matrix of a bounded operator `R` and
`‖R‖ ≤ ‖S‖ ‖T‖`. -/
@[tag "TAB8"]
theorem posSemidef_hadamard_and_exists_hadamard_ell2_norm_le {V : Type*} [DecidableEq V] :
    (∀ S T : Matrix V V ℝ, S.PosSemidef → T.PosSemidef → (S ⊙ T).PosSemidef) ∧
    ∀ S T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
      ∃ R : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
        (∀ x y, R (lp.single 2 y 1) x = S (lp.single 2 y 1) x * T (lp.single 2 y 1) x) ∧
        ‖R‖ ≤ ‖S‖ * ‖T‖ :=
  ⟨fun _ _ hS hT => hS.hadamard hT, exists_hadamard_ell2_norm_le⟩

end PercLib.Analysis
