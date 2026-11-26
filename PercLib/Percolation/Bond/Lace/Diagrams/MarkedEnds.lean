/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original refinements of the endpoint marks in Heydenreich and van der
Hofstad (2017), Section 7.5, retaining the actual deleted connector masses.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedJoiningBounds

/-!
# Endpoint marks with deleted connector masses

## Main results

The initial route marks the outgoing second coordinate, as in the primitive
chain. Its certain diagonal contributes zero. Both endpoint cores retain
the exact shifted weighted pairs; taking their supremum costs the reverse
deleted mass at the initial end and the forward deleted mass at the terminal
end, with constant one. Only vanishing of the weight at zero is required.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The marked initial row equals the marked full triangle: its special
diagonal is killed by the zero weight. -/
theorem weight_mul_diagramInitial_eq_triangle
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) (hw : w 0 = 0)
    (x : G) (s : G × G) :
    w (s.2 - x) * diagramInitial q x s =
      w (s.2 - x) * (tau q x s.1 * tau q x s.2 * tau q s.1 s.2) := by
  classical
  by_cases hs : s.2 = x <;> simp [diagramInitial, hs, hw]

/-- The initial core retains the exact shifted weighted pair and the actual
backward connector. Its marked coordinate is the second coordinate. -/
theorem diagramMarkedInitialCore_le_tsum_weightedPair [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (x : G) (r : G × G) :
    diagramMarkedInitialCore q w x r ≤
      ∑' t : G × G, diagramConnector q t r * tau q t.1 t.2 *
        diagramWeightedPair q w (t.1 - t.2) := by
  classical
  have hp (g : G) : ∀ a, q (Sym2.map (Equiv.addRight g) a) = q a := by
    intro a
    induction a using Sym2.ind with
    | _ a b => exact hq a b g
  unfold diagramMarkedInitialCore
  simp_rw [weight_mul_diagramInitial_eq_triangle q w hw]
  calc
    _ = ∑' y, ∑' t : G × G, (diagramConnector q t r * tau q t.1 t.2) *
        (w (t.2 + y - x) * tau q x (t.2 + y) * tau q x (t.1 + y)) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro y
      rw [← (Equiv.prodCongr (Equiv.addRight y) (Equiv.addRight y)).tsum_eq]
      apply tsum_congr
      intro t
      change w (t.2 + y - x) *
        (tau q x (t.1 + y) * tau q x (t.2 + y) * tau q (t.1 + y) (t.2 + y)) *
        diagramConnector q (t.1 + y, t.2 + y) (r.1 + y, r.2 + y) = _
      have hC := diagramConnector_apply_equiv q (Equiv.addRight y) (hp y) t r
      change diagramConnector q (t.1 + y, t.2 + y) (r.1 + y, r.2 + y) =
        diagramConnector q t r at hC
      have hτ := tau_eq_of_map_law (Equiv.addRight y)
        (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q _ (hp y)) t.1 t.2
      change tau q (t.1 + y) (t.2 + y) = tau q t.1 t.2 at hτ
      rw [hC, hτ]
      ac_rfl
    _ = ∑' t : G × G, (diagramConnector q t r * tau q t.1 t.2) *
        (∑' y, w (t.2 + y - x) * tau q x (t.2 + y) * tau q x (t.1 + y)) := by
      rw [ENNReal.tsum_comm]
      simp only [ENNReal.tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply mul_le_mul' le_rfl
      have h := tsum_weight_mul_tau_mul_tau_le_weightedPair q hq w hw x x t.2 t.1
      have hs : x + t.1 - t.2 - x = t.1 - t.2 := by abel
      rwa [hs] at h

/-- The initial mark costs the exact reverse deleted mass, with constant one. -/
theorem diagramMarkedInitialCore_le_reverse_deleted_mass [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (x : G) (r : G × G) :
    diagramMarkedInitialCore q w x r ≤
      (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) *
        ⨆ a, diagramWeightedPair q w a := by
  calc
    _ ≤ ∑' t : G × G, diagramConnector q t r * tau q t.1 t.2 *
        diagramWeightedPair q w (t.1 - t.2) :=
      diagramMarkedInitialCore_le_tsum_weightedPair q hq w hw x r
    _ ≤ ∑' t : G × G, diagramConnector q t r * tau q t.1 t.2 *
        (⨆ a, diagramWeightedPair q w a) :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (le_iSup _ _)
    _ = _ := ENNReal.tsum_mul_right

private theorem terminal_arms_le_weightedPair [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (s : G × G) :
    (∑' y, tau q s.1 y * tau q s.2 y * w (y - (if ε then s.2 else s.1))) ≤
      diagramWeightedPair q w (if ε then s.2 - s.1 else s.1 - s.2) := by
  cases ε
  · calc
      _ = ∑' y, w (y - s.1) * tau q s.1 y * tau q s.2 y := by
        apply tsum_congr
        intro y
        simp only [Bool.false_eq_true, ite_false]
        ac_rfl
      _ ≤ _ := by
        simpa using tsum_weight_mul_tau_mul_tau_le_weightedPair q hq w hw s.1 s.2 0 0
  · calc
      _ = ∑' y, w (y - s.2) * tau q s.2 y * tau q s.1 y := by
        apply tsum_congr
        intro y
        simp only [ite_true]
        ac_rfl
      _ ≤ _ := by
        simpa using tsum_weight_mul_tau_mul_tau_le_weightedPair q hq w hw s.2 s.1 0 0

/-- The terminal mark retains the exact shifted weighted pair for either
selected coordinate, together with the actual forward deleted connector. -/
theorem diagramMarkedTerminalCore_le_tsum_weightedPair [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (p : G × G) :
    diagramMarkedTerminalCore q w ε p ≤
      ∑' s : G × G, diagramConnector q p s * tau q s.1 s.2 *
        diagramWeightedPair q w (if ε then s.2 - s.1 else s.1 - s.2) := by
  classical
  unfold diagramMarkedTerminalCore
  calc
    _ = ∑' s : G × G, (diagramConnector q p s * tau q s.1 s.2) *
        (∑' y, tau q s.1 y * tau q s.2 y * w (y - (if ε then s.2 else s.1))) := by
      simp only [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ _ := ENNReal.tsum_le_tsum fun s =>
      mul_le_mul' le_rfl (terminal_arms_le_weightedPair q hq w hw ε s)

/-- The terminal mark costs the exact forward deleted mass, with constant one. -/
theorem diagramMarkedTerminalCore_le_deleted_mass [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (p : G × G) :
    diagramMarkedTerminalCore q w ε p ≤
      (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) *
        ⨆ a, diagramWeightedPair q w a := by
  calc
    _ ≤ ∑' s : G × G, diagramConnector q p s * tau q s.1 s.2 *
        diagramWeightedPair q w (if ε then s.2 - s.1 else s.1 - s.2) :=
      diagramMarkedTerminalCore_le_tsum_weightedPair q hq w hw ε p
    _ ≤ ∑' s : G × G, diagramConnector q p s * tau q s.1 s.2 *
        (⨆ a, diagramWeightedPair q w a) :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (le_iSup _ _)
    _ = _ := ENNReal.tsum_mul_right

end PercLib.Percolation.Bond.Lace
