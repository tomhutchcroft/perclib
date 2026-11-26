/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original refinements of the marked intermediate diagrams of Heydenreich
and van der Hofstad (2017), Section 7.5, retaining both deleted connectors.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedConnectorBounds

/-!
# Local marked joining bounds with two deleted connectors

## Main results

The first joining geometry costs the exact forward deleted mass times the
exact backward deleted mass times the weighted-pair norm. Translating both
outgoing coordinates proves this without a reversal identity. The second
geometry vanishes for a second-to-first mark and is retained explicitly for
the other mark. Only vanishing of the weight at zero is required.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- A weighted pair of translated ordinary arms is bounded by the specified
weighted continuation pair. No symmetry of the weight is needed. -/
theorem tsum_weight_mul_tau_mul_tau_le_weightedPair [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (a b c d : G) :
    (∑' y, w (c + y - a) * tau q a (c + y) * tau q b (d + y)) ≤
      diagramWeightedPair q w (a + d - c - b) := by
  classical
  rw [← (Equiv.addRight (a - c)).tsum_eq]
  unfold diagramWeightedPair
  apply ENNReal.tsum_le_tsum
  intro z
  change w (c + (z + (a - c)) - a) * tau q a (c + (z + (a - c))) *
    tau q b (d + (z + (a - c))) ≤ _
  have hm : c + (z + (a - c)) - a = z := by abel
  have hs : d + (z + (a - c)) - b = z + (a + d - c - b) := by abel
  rw [tau_eq_rooted_of_add_right q hq a, tau_eq_rooted_of_add_right q hq b, hm, hs]
  exact mul_le_mul' (weight_mul_tau_le_weight_mul_continuation q w hw z) le_rfl

private theorem joining_cross_arms_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (s t : G × G) :
    (∑' y, tau q s.1 (t.2 + y) * tau q s.2 (t.1 + y) *
      w (if ε then t.1 + y - s.2 else t.2 + y - s.1)) ≤
        ⨆ a, diagramWeightedPair q w a := by
  cases ε
  · calc
      _ = ∑' y, w (t.2 + y - s.1) * tau q s.1 (t.2 + y) * tau q s.2 (t.1 + y) := by
        apply tsum_congr
        intro y
        simp only [Bool.false_eq_true, ite_false]
        ac_rfl
      _ ≤ _ := (tsum_weight_mul_tau_mul_tau_le_weightedPair q hq w hw s.1 s.2 t.2 t.1).trans
        (le_iSup _ _)
  · calc
      _ = ∑' y, w (t.1 + y - s.2) * tau q s.2 (t.1 + y) * tau q s.1 (t.2 + y) := by
        apply tsum_congr
        intro y
        simp only [ite_true]
        ac_rfl
      _ ≤ _ := (tsum_weight_mul_tau_mul_tau_le_weightedPair q hq w hw s.2 s.1 t.1 t.2).trans
        (le_iSup _ _)

private theorem joining_first_row_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (s r : G × G) :
    (∑' t, ∑' y,
      (tau q s.1 s.2 * tau q s.1 t.2 * tau q s.2 t.1 * tau q t.1 t.2) *
        diagramConnector q t (r.1 + y, r.2 + y) *
          w (if ε then t.1 - s.2 else t.2 - s.1)) ≤
      tau q s.1 s.2 * (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) *
        ⨆ a, diagramWeightedPair q w a := by
  classical
  have hp (g : G) : ∀ a, q (Sym2.map (Equiv.addRight g) a) = q a := by
    intro a
    induction a using Sym2.ind with
    | _ a b => exact hq a b g
  calc
    _ = ∑' y, ∑' t : G × G,
        (tau q s.1 s.2 * tau q s.1 (t.2 + y) * tau q s.2 (t.1 + y) * tau q t.1 t.2) *
          diagramConnector q t r *
            w (if ε then t.1 + y - s.2 else t.2 + y - s.1) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro y
      rw [← (Equiv.prodCongr (Equiv.addRight y) (Equiv.addRight y)).tsum_eq]
      apply tsum_congr
      intro t
      change (tau q s.1 s.2 * tau q s.1 (t.2 + y) * tau q s.2 (t.1 + y) *
        tau q (t.1 + y) (t.2 + y)) *
        diagramConnector q (t.1 + y, t.2 + y) (r.1 + y, r.2 + y) *
          w (if ε then t.1 + y - s.2 else t.2 + y - s.1) = _
      have hC := diagramConnector_apply_equiv q (Equiv.addRight y) (hp y) t r
      change diagramConnector q (t.1 + y, t.2 + y) (r.1 + y, r.2 + y) =
        diagramConnector q t r at hC
      have hτ := tau_eq_of_map_law (Equiv.addRight y)
        (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q _ (hp y)) t.1 t.2
      change tau q (t.1 + y) (t.2 + y) = tau q t.1 t.2 at hτ
      rw [hC, hτ]
    _ = ∑' t : G × G, (tau q s.1 s.2 * diagramConnector q t r * tau q t.1 t.2) *
        (∑' y, tau q s.1 (t.2 + y) * tau q s.2 (t.1 + y) *
          w (if ε then t.1 + y - s.2 else t.2 + y - s.1)) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro t
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y
      ac_rfl
    _ ≤ ∑' t : G × G, (tau q s.1 s.2 * diagramConnector q t r * tau q t.1 t.2) *
        (⨆ a, diagramWeightedPair q w a) :=
      ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl (joining_cross_arms_le q hq w hw ε s t)
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      simp only [mul_assoc, ENNReal.tsum_mul_left]

/-- The first joining geometry retains two distinct deleted connector masses.
Only the cross arms are bounded by the weighted-pair norm. -/
theorem markedJoining_first_le_deleted_masses [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (p r : G × G) :
    (∑' s, ∑' t, ∑' y, diagramConnector q p s *
      (tau q s.1 s.2 * tau q s.1 t.2 * tau q s.2 t.1 * tau q t.1 t.2) *
        diagramConnector q t (r.1 + y, r.2 + y) *
          w (if ε then t.1 - s.2 else t.2 - s.1)) ≤
      (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) *
        (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) *
          ⨆ a, diagramWeightedPair q w a := by
  classical
  calc
    _ = ∑' s, diagramConnector q p s * (∑' t, ∑' y,
        (tau q s.1 s.2 * tau q s.1 t.2 * tau q s.2 t.1 * tau q t.1 t.2) *
          diagramConnector q t (r.1 + y, r.2 + y) *
            w (if ε then t.1 - s.2 else t.2 - s.1)) := by
      simp only [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' s, diagramConnector q p s * (tau q s.1 s.2 *
        (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) *
          (⨆ a, diagramWeightedPair q w a)) :=
      ENNReal.tsum_le_tsum fun s => mul_le_mul' le_rfl (joining_first_row_le q hq w hw ε s r)
    _ = _ := by simp only [← mul_assoc, ENNReal.tsum_mul_right]

/-- Exact separation of the joining geometries. The second-to-first mark
annihilates the second geometry; the other mark keeps its actual core. -/
theorem diagramMarkedJoiningCore_eq_first_add_second
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) (hw : w 0 = 0)
    (ε : Bool) (p r : G × G) :
    diagramMarkedJoiningCore q w ε p r =
      (∑' s, ∑' t, ∑' y, diagramConnector q p s *
        (tau q s.1 s.2 * tau q s.1 t.2 * tau q s.2 t.1 * tau q t.1 t.2) *
          diagramConnector q t (r.1 + y, r.2 + y) *
            w (if ε then t.1 - s.2 else t.2 - s.1)) +
      if ε then 0 else diagramMarkedJoiningSecondCore q w p r := by
  classical
  unfold diagramMarkedJoiningCore
  simp only [diagramInterior, mul_add, add_mul, ENNReal.tsum_add]
  congr 1
  cases ε
  · simp only [Bool.false_eq_true, ite_false]
    unfold diagramMarkedJoiningSecondCore
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro u
    apply tsum_congr
    intro v
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    apply tsum_congr
    intro t
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro y
    simp only [mul_ite, ite_mul, zero_mul, mul_zero, tsum_ite_eq', mul_assoc]
  · simp only [ite_true]
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    apply ENNReal.tsum_eq_zero.mpr
    intro t
    apply ENNReal.tsum_eq_zero.mpr
    intro y
    by_cases h : s.2 = t.1 <;> simp [h, hw]

/-- The actual joining-core estimate keeps both deleted masses and charges
the second-geometry core only to the first-to-second mark. -/
theorem diagramMarkedJoiningCore_le_deleted_masses [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (p r : G × G) :
    diagramMarkedJoiningCore q w ε p r ≤
      (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) *
        (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) *
          (⨆ a, diagramWeightedPair q w a) +
      if ε then 0 else diagramMarkedJoiningSecondCore q w p r := by
  rw [diagramMarkedJoiningCore_eq_first_add_second q w hw ε p r]
  exact add_le_add (markedJoining_first_le_deleted_masses q hq w hw ε p r) le_rfl

end PercLib.Percolation.Bond.Lace
