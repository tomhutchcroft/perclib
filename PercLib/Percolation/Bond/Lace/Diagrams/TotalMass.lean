/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Convergence
public import PercLib.Percolation.Bond.Lace.Diagrams.TriangleBounds
public import PercLib.Percolation.Bond.Lace.DiagramBounds

/-!
# Total coefficient mass with the sharp zeroth-order factor

## Main results

Combines the factor-four zeroth coefficient bound with the actual geometric
positive-order diagram bound. The additive form is valid in extended
nonnegative reals, even without a contraction assumption.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

/-- Retain the sharp zeroth-order factor when summing all coefficient orders. -/
theorem one_add_four_mul_all_coefficient_mass_le
    (q : Sym2 V → unitInterval) (x : V) (Δ ρ κ : ℝ≥0∞)
    (hΔ : (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) ≤ Δ)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) :
    1 + 4 * (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≤
      Δ + 4 * Δ * (1 - ρ)⁻¹ * κ := by
  have hi : (∑' p, diagramInitial q x p) ≤ Δ := by
    apply (diagramInitial_mass_le_triangle q x).trans
    simpa only [tau_comm q x, mul_assoc, mul_left_comm, mul_comm] using hΔ
  have hz := (one_add_four_mul_tsum_piZero_le_triangle q x).trans hΔ
  calc
    _ ≤ 1 + 4 * ((∑' y, piZero q x y) +
        (∑' p, diagramInitial q x p) * (1 - ρ)⁻¹ * κ) :=
      add_le_add le_rfl (mul_le_mul' le_rfl
        (tsum_laceCoefficient_all_mass_le_diagram q x ρ κ hρ hκ))
    _ = (1 + 4 * (∑' y, piZero q x y)) +
        4 * (∑' p, diagramInitial q x p) * (1 - ρ)⁻¹ * κ := by ring
    _ ≤ _ := add_le_add hz
      (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hi) le_rfl) le_rfl)

end PercLib.Percolation.Bond.Lace
