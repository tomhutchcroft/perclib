/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Row bounds for pair-state lace diagrams

## Main results

The transfer and terminal row constants are kept separate. Iterating the
transfer costs `ρ^n`; the final step costs only its own row bound `κ`.
These deterministic estimates concern the defined diagrams and do not assume
any unproved comparison with lace coefficients.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Each interior transfer multiplies the initial row mass by at most `ρ`. -/
theorem diagramIterate_mass_le_geometric (q : Sym2 V → unitInterval)
    (x : V) (ρ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ) (n : ℕ) :
    (∑' p, diagramIterate q x n p) ≤ (∑' p, diagramInitial q x p) * ρ ^ n := by
  classical
  induction n with
  | zero => simp [diagramIterate]
  | succ n ih =>
      calc
        _ = ∑' r, diagramIterate q x n r * (∑' p, diagramTransfer q r p) := by
          simp only [diagramIterate]
          rw [ENNReal.tsum_comm]
          simp_rw [ENNReal.tsum_mul_left]
        _ ≤ ∑' r, diagramIterate q x n r * ρ :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hρ r) _
        _ = (∑' r, diagramIterate q x n r) * ρ := ENNReal.tsum_mul_right
        _ ≤ ((∑' p, diagramInitial q x p) * ρ ^ n) * ρ := mul_le_mul' ih le_rfl
        _ = _ := by rw [pow_succ, mul_assoc]

/-- The final terminal factor retains its separate row constant `κ`. -/
theorem laceDiagram_mass_le_geometric (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) (n : ℕ) :
    (∑' y, laceDiagram q n x y) ≤ (∑' p, diagramInitial q x p) * ρ ^ n * κ := by
  classical
  calc
    _ = ∑' p, diagramIterate q x n p * (∑' y, diagramTerminal q p y) := by
      unfold laceDiagram
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' p, diagramIterate q x n p * κ :=
      ENNReal.tsum_le_tsum fun p => mul_le_mul_right (hκ p) _
    _ = (∑' p, diagramIterate q x n p) * κ := ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_mul' (diagramIterate_mass_le_geometric q x ρ hρ n) le_rfl

/-- The full diagram series has the geometric denominator, with no loss in
the initial or terminal constants. -/
theorem tsum_laceDiagram_mass_le (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) :
    (∑' n : ℕ, ∑' y, laceDiagram q n x y) ≤
      (∑' p, diagramInitial q x p) * (1 - ρ)⁻¹ * κ := by
  classical
  calc
    _ ≤ ∑' n : ℕ, (∑' p, diagramInitial q x p) * ρ ^ n * κ :=
      ENNReal.tsum_le_tsum (laceDiagram_mass_le_geometric q x ρ κ hρ hκ)
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- A subunit transfer constant makes the full diagram mass finite whenever
the initial mass and the terminal constant are finite. -/
theorem tsum_laceDiagram_mass_ne_top (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞) (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    (∑' n : ℕ, ∑' y, laceDiagram q n x y) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hinitial
        (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hρone)))) hκfinite)
    (tsum_laceDiagram_mass_le q x ρ κ hρ hκ)

/-- The real diagram values are summable jointly in order and endpoint. -/
theorem summable_laceDiagram_toReal (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞) (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    Summable (fun p : ℕ × V => (laceDiagram q p.1 x p.2).toReal) := by
  classical
  apply ENNReal.summable_toReal
  rw [ENNReal.tsum_prod']
  exact tsum_laceDiagram_mass_ne_top q x ρ κ hρone hκfinite hρ hκ hinitial

end PercLib.Percolation.Bond.Lace
