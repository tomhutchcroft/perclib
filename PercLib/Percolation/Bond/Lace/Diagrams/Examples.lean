/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original finite-model computations; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Convergence
public import PercLib.Percolation.Bond.Lace.FirstDiagramRefined
public import Mathlib.Tactic.Basify

/-!
# A nonzero example of diagram contraction

On two vertices with bond probability `1/4`, the exact uniform transfer norm
is `1365/4096`, the exact uniform terminal norm is `35/128`, and the initial
mass is `9/8`. These finite computations verify the hypotheses of the actual
coefficient convergence theorem. The first positive coefficient is `1/16`.
Loop probabilities do not enter any of these quantities.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal Classical

namespace PercLib.Percolation.Bond.Lace

/-- Exact transfer row masses on two vertices with sole bond probability
`1/4`. The larger value is attained at either off-diagonal pair state. -/
theorem diagramTransfer_mass_bool_quarter
    (q : Sym2 Bool → unitInterval)
    (hq : (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) = 1 / 4)
    (p : Bool × Bool) :
    (∑' r, diagramTransfer q p r) =
      if p.1 = p.2 then 195 / 1024 else 1365 / 4096 := by
  have ht : tau q true false = 1 / 4 := by
    rw [tau_comm, tau_bool_cross, hq]
  rcases p with ⟨b, c⟩
  cases b <;> cases c <;>
    norm_num [diagramTransfer, diagramConnector, diagramInterior,
      ENNReal.tsum_prod', tsum_fintype, Fintype.sum_prod_type, offDiagonal, Sym2.eq_swap,
      law_bool_deleted, tau_self, tau_bool_cross, ht, hq, ← ENNReal.mul_inv] <;>
    (basify; norm_num)

/-- Exact terminal row masses at probability `1/4`, without replacing the
terminal factor by another interior transfer. -/
theorem diagramTerminal_mass_bool_quarter
    (q : Sym2 Bool → unitInterval)
    (hq : (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) = 1 / 4)
    (p : Bool × Bool) :
    (∑' y, diagramTerminal q p y) =
      if p.1 = p.2 then 25 / 256 else 35 / 128 := by
  have ht : tau q true false = 1 / 4 := by
    rw [tau_comm, tau_bool_cross, hq]
  rcases p with ⟨b, c⟩
  cases b <;> cases c <;>
    norm_num [diagramTerminal, diagramConnector,
      ENNReal.tsum_prod', tsum_fintype, Fintype.sum_prod_type, offDiagonal, Sym2.eq_swap,
      law_bool_deleted, tau_self, tau_bool_cross, ht, hq, ← ENNReal.mul_inv] <;>
    (basify; norm_num)

/-- Keeping the certain initial diagonal gives exactly `9/8` on the
two-vertex quarter-probability model. -/
theorem diagramInitial_mass_bool_quarter
    (q : Sym2 Bool → unitInterval)
    (hq : (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) = 1 / 4)
    (x : Bool) :
    (∑' p, diagramInitial q x p) = 9 / 8 := by
  have ht : tau q true false = 1 / 4 := by
    rw [tau_comm, tau_bool_cross, hq]
  cases x <;>
    norm_num [diagramInitial, ENNReal.tsum_prod', tsum_fintype, Fintype.sum_prod_type,
      tau_self, tau_bool_cross, ht, hq, ← ENNReal.mul_inv] <;>
    (basify; norm_num)

/-- The exact maximum transfer and terminal row constants are finite, and
the transfer is strictly contracting. -/
theorem diagram_bounds_bool_quarter
    (q : Sym2 Bool → unitInterval)
    (hq : (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) = 1 / 4) :
    (1365 / 4096 : ℝ≥0∞) < 1 ∧ (35 / 128 : ℝ≥0∞) ≠ ⊤ ∧
      (∀ p, (∑' r, diagramTransfer q p r) ≤ 1365 / 4096) ∧
      (∀ p, (∑' y, diagramTerminal q p y) ≤ 35 / 128) ∧
      (∀ x, (∑' p, diagramInitial q x p) ≠ ⊤) := by
  refine ⟨by basify; norm_num, by basify, ?_, ?_, ?_⟩
  · intro p
    rw [diagramTransfer_mass_bool_quarter q hq]
    split_ifs <;> (basify; norm_num)
  · intro p
    rw [diagramTerminal_mass_bool_quarter q hq]
    split_ifs <;> (basify; norm_num)
  · intro x
    rw [diagramInitial_mass_bool_quarter q hq]
    basify

/-- The all-order canonical coefficient mass is finite on the nonzero
two-vertex model by the proved diagram contraction criterion. -/
theorem tsum_laceCoefficient_all_mass_bool_quarter_ne_top
    (q : Sym2 Bool → unitInterval)
    (hq : (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) = 1 / 4)
    (x : Bool) :
    (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤ := by
  obtain ⟨hρone, hκfinite, hρ, hκ, hinitial⟩ := diagram_bounds_bool_quarter q hq
  exact tsum_laceCoefficient_all_mass_ne_top_of_diagram q x
    (1365 / 4096) (35 / 128) hρone hκfinite hρ hκ (hinitial x)

/-- A concrete positive-probability profile has a nonzero lace coefficient
and finite total coefficient mass at every root. This witnesses the diagram
convergence hypotheses beyond the zero profile. -/
theorem bool_quarter_has_nonzero_summable_coefficients :
    let q : Sym2 Bool → unitInterval := fun _ => ⟨1 / 4, by norm_num⟩
    laceCoefficient q 1 false false = 1 / 16 ∧
      0 < laceCoefficient q 1 false false ∧
      ∀ x, (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤ := by
  let q : Sym2 Bool → unitInterval := fun _ => ⟨1 / 4, by norm_num⟩
  change laceCoefficient q 1 false false = 1 / 16 ∧
    0 < laceCoefficient q 1 false false ∧
    ∀ x, (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤
  have hq : (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) = 1 / 4 := by
    change ((1 / 4 : ℝ≥0) : ℝ≥0∞) = _
    simp
  have hfirst : laceCoefficient q 1 false false = 1 / 16 := by
    rw [laceCoefficient_one_bool, hq]
    norm_num [pow_two, ← ENNReal.mul_inv]
  exact ⟨hfirst, by rw [hfirst]; norm_num,
    tsum_laceCoefficient_all_mass_bool_quarter_ne_top q hq⟩

end PercLib.Percolation.Bond.Lace
