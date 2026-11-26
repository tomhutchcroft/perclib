/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Basic
public import PercLib.Percolation.Bond.Lace.ThroughSet

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Dropping deletion gives the usual product of the branch connection and
the one-step continuation. The actual diagram keeps the smaller connector. -/
theorem diagramConnector_le (q : Sym2 V → unitInterval) (p r : V × V) :
    diagramConnector q p r ≤ tau q p.1 r.1 *
      ∑' v, offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v * tau q v r.2 := by
  calc
    _ ≤ ∑' v, offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v *
          tau q p.1 r.1 * tau q v r.2 := by
      apply ENNReal.tsum_le_tsum
      intro v
      apply mul_le_mul' _ le_rfl
      apply mul_le_mul' le_rfl
      exact measure_mono (fun _ h => conn_mono sdiff_subset h)
    _ = _ := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      ac_rfl

/-- The initial diagonal is exact, rather than being inflated to a bubble. -/
theorem diagramInitial_mass_eq (q : Sym2 V → unitInterval) (x : V) :
    (∑' p, diagramInitial q x p) = 1 + ∑' h,
      if h = x then 0 else ∑' s, tau q x s * tau q x h * tau q s h := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp only [diagramInitial]
  simp
  apply tsum_congr
  intro h
  by_cases hh : h = x <;> simp [hh]

theorem diagramInitial_le_triangle_term (q : Sym2 V → unitInterval)
    (x : V) (p : V × V) :
    diagramInitial q x p ≤ tau q x p.1 * tau q x p.2 * tau q p.1 p.2 := by
  unfold diagramInitial
  split_ifs with h hx
  · simp [h, hx, tau_self]
  · exact bot_le
  · exact le_rfl

/-- The exact initial mass never exceeds the full triangle. -/
theorem diagramInitial_mass_le_triangle (q : Sym2 V → unitInterval) (x : V) :
    (∑' p, diagramInitial q x p) ≤ ∑' s, ∑' h,
      tau q x s * tau q x h * tau q s h := by
  calc
    _ ≤ ∑' p : V × V, tau q x p.1 * tau q x p.2 * tau q p.1 p.2 :=
      ENNReal.tsum_le_tsum (diagramInitial_le_triangle_term q x)
    _ = _ := ENNReal.tsum_prod'

/-- The terminal norm is bounded separately, with constant one, using the
bubble and the deleted connector-triangle mass. No extra interior transfer is
inserted at the last layer. -/
theorem diagramTerminal_mass_le (q : Sym2 V → unitInterval)
    (p : V × V) (B M : ℝ≥0∞)
    (hB : ∀ z t, (∑' y, tau q z y * tau q t y) ≤ B)
    (hM : (∑' s : V × V, diagramConnector q p s * tau q s.1 s.2) ≤ M) :
    (∑' y, diagramTerminal q p y) ≤ M * B := by
  calc
    _ = ∑' s : V × V, (diagramConnector q p s * tau q s.1 s.2) *
        (∑' y, tau q s.1 y * tau q s.2 y) := by
      unfold diagramTerminal
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro s
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' s : V × V, (diagramConnector q p s * tau q s.1 s.2) * B :=
      ENNReal.tsum_le_tsum fun s => mul_le_mul_right (hB s.1 s.2) _
    _ = (∑' s : V × V, diagramConnector q p s * tau q s.1 s.2) * B :=
      ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_mul' hM le_rfl

end PercLib.Percolation.Bond.Lace
