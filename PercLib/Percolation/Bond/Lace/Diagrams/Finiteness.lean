/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Convergence

/-!
# Finite-order expansion under finite diagram norms

## Main results

A finite transfer norm suffices for every fixed coefficient order. The stricter
condition that this norm is below one is needed only to sum all orders. Here
the finite signed expansion is justified directly from the proved finite
pair-state diagram bounds.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

/-- Finite initial, transfer, and terminal norms imply finiteness of each
actual coefficient row, without a contraction hypothesis. -/
theorem laceCoefficient_mass_ne_top_of_finite_diagram_bounds
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V) (ρ κ : ℝ≥0∞)
    (hρfinite : ρ ≠ ⊤) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    (∑' y, laceCoefficient q n x y) ≠ ⊤ := by
  classical
  cases n with
  | zero =>
      exact ne_top_of_le_ne_top hinitial (tsum_piZero_le_diagramInitial q x)
  | succ n =>
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top hinitial (ENNReal.pow_ne_top hρfinite))
          hκfinite)
        (laceCoefficient_mass_le_diagram_geometric q x ρ κ hρ hκ n)

open scoped Classical in
/-- The actual finite signed lace expansion follows from finite diagram
norms. The transfer norm need not be less than one, and coefficient-mass
finiteness is a conclusion of the proved diagram bounds. -/
theorem finite_lace_expansion_of_finite_diagram_bounds
    (q : Sym2 V → unitInterval) (N : ℕ) (x y : V) (ρ κ : ℝ≥0∞)
    (hρfinite : ρ ≠ ⊤) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' z, diagramTerminal q p z) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤)
    (hfin : ∀ a u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C) :
    (tau q x y).toReal = (if x = y then 1 else 0) + partialLaceSum q N x y +
      (∑' v, (offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
      (∑' u, ∑' v, partialLaceSum q N x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal) +
      signedLaceRemainder q N x y :=
  finite_lace_expansion q N x y hfin C hCfinite hC
    (fun n _ => laceCoefficient_mass_ne_top_of_finite_diagram_bounds
      q n x ρ κ hρfinite hκfinite hρ hκ hinitial)

end PercLib.Percolation.Bond.Lace
