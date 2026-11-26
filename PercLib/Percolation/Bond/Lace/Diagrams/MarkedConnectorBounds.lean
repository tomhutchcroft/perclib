/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs of the local weighted connector bounds used in the
two-sided summation of Heydenreich and van der Hofstad (2017), Section 7.5.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedSums
public import PercLib.Percolation.Bond.Lace.Expansion.Fourier
public import PercLib.Percolation.Bond.BoundarySusceptibility

/-!
# Local marked connector bounds

## Main results

The actual deleted connector is bounded by an explicit shifted weighted
pair. Marking its second coordinate costs one weighted pair; marking its
first coordinate costs the step mass times that pair norm. The latter uses
the proved singleton last-exit inequality and a weight vanishing at zero.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The last exit from a singleton gives the off-diagonal first-step bound. -/
theorem tau_le_tsum_offDiagonal_mul_tau [Countable V]
    (q : Sym2 V → unitInterval) {x y : V} (hxy : x ≠ y) :
    tau q x y ≤ ∑' v, offDiagonal (fun a b : V =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y := by
  classical
  have h := tau_le_lastExit q {x} (u := x) (w := y) (by simp) (by simpa using Ne.symm hxy)
  simp only [mem_singleton_iff, tsum_ite_eq, tau_self, mul_one] at h
  refine h.trans (ENNReal.tsum_le_tsum fun v => ?_)
  by_cases hv : v = x
  · subst v
    rw [localConn_of_notMem_right (by simp : x ∉ ({x} : Set V)ᶜ) y]
    simp
  · rw [offDiagonal_apply, ite_eq_right hv]
    have hlocal : law q (localConn ({x} : Set V)ᶜ y v) ≤ tau q y v :=
      measure_mono fun ω hω => conn_of_localConn ω _ ⟨y, hω.1⟩ ⟨v, hω.2.1⟩ hω.2.2
    calc
      _ ≤ tau q y v * (unitInterval.toNNReal (q s(v, x)) : ℝ≥0∞) :=
        mul_le_mul' hlocal le_rfl
      _ = _ := by rw [tau_comm q y v, Sym2.eq_swap]; ac_rfl

namespace Lace

variable {G : Type*} [AddCommGroup G]

/-- A nonnegative weight vanishing at zero can use the first-step bound on
every displacement, including the certain diagonal connection. -/
theorem weight_mul_tau_le_weight_mul_continuation [Countable G]
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) (hw : w 0 = 0) (z : G) :
    w z * tau q 0 z ≤ w z * ∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v z := by
  by_cases hz : z = 0
  · simp [hz, hw]
  · exact mul_le_mul' le_rfl (tau_le_tsum_offDiagonal_mul_tau q (Ne.symm hz))

/-- A mark on the second connector coordinate costs a single shifted weighted
pair. The deleted connector is retained on the left side. -/
theorem diagramMarkedConnectorCore_true_le_weightedPair
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (p r : G × G) :
    diagramMarkedConnectorCore q w true p r ≤
      diagramWeightedPair q w (r.1 + p.2 - r.2 - p.1) := by
  classical
  let T : G → G → ℝ≥0∞ := fun a b => ∑' v,
    offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) a v *
      tau q v b
  rw [diagramMarkedConnectorCore_true]
  calc
    _ ≤ ∑' y, w (r.2 + y - p.2) * (tau q p.1 (r.1 + y) * T p.2 (r.2 + y)) :=
      ENNReal.tsum_le_tsum fun y =>
        mul_le_mul' le_rfl (diagramConnector_le q p (r.1 + y, r.2 + y))
    _ = _ := by
      unfold diagramWeightedPair
      rw [← (Equiv.addRight (p.2 - r.2)).tsum_eq]
      apply tsum_congr
      intro z
      change w (r.2 + (z + (p.2 - r.2)) - p.2) *
        (tau q p.1 (r.1 + (z + (p.2 - r.2))) * T p.2 (r.2 + (z + (p.2 - r.2)))) =
        w z * T 0 z * tau q 0 (z + (r.1 + p.2 - r.2 - p.1))
      have hm : r.2 + (z + (p.2 - r.2)) - p.2 = z := by abel
      have hsecond : r.2 + (z + (p.2 - r.2)) = z + p.2 := by abel
      have hfirst : r.1 + (z + (p.2 - r.2)) - p.1 =
          z + (r.1 + p.2 - r.2 - p.1) := by abel
      have hT : T p.2 (z + p.2) = T 0 z := by
        simpa only [zero_add] using tsum_offDiagonal_mul_tau_add_right q hq 0 z p.2
      rw [hm, hsecond, hT, tau_eq_rooted_of_add_right q hq, hfirst]
      ac_rfl

/-- The second coordinate costs the supremum of the actual weighted pairs,
with constant one and no finiteness assumption. -/
theorem diagramMarkedConnectorCore_true_le_iSup
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (p r : G × G) :
    diagramMarkedConnectorCore q w true p r ≤ ⨆ a, diagramWeightedPair q w a :=
  (diagramMarkedConnectorCore_true_le_weightedPair q hq w p r).trans (le_iSup _ _)

/-- A mark on the first coordinate is bounded by a step-weighted sum of
shifted weighted pairs, retaining their exact shifts before taking a norm. -/
theorem diagramMarkedConnectorCore_false_le_tsum_weightedPair [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (p r : G × G) :
    diagramMarkedConnectorCore q w false p r ≤
      ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v *
        diagramWeightedPair q w (p.1 + r.2 - r.1 - v) := by
  classical
  let J : G → G → ℝ≥0∞ := offDiagonal (fun a b : G =>
    (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  rw [diagramMarkedConnectorCore_false]
  calc
    _ ≤ ∑' y, w (r.1 + y - p.1) *
        (tau q p.1 (r.1 + y) * ∑' v, J p.2 v * tau q v (r.2 + y)) :=
      ENNReal.tsum_le_tsum fun y =>
        mul_le_mul' le_rfl (diagramConnector_le q p (r.1 + y, r.2 + y))
    _ = ∑' v, J p.2 v * ∑' z, w z * tau q 0 z *
        tau q 0 (z + (p.1 + r.2 - r.1 - v)) := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro v
      rw [← (Equiv.addRight (p.1 - r.1)).tsum_eq]
      apply tsum_congr
      intro z
      change w (r.1 + (z + (p.1 - r.1)) - p.1) *
        (tau q p.1 (r.1 + (z + (p.1 - r.1))) *
          (J p.2 v * tau q v (r.2 + (z + (p.1 - r.1))))) =
        J p.2 v * (w z * tau q 0 z * tau q 0 (z + (p.1 + r.2 - r.1 - v)))
      have hm : r.1 + (z + (p.1 - r.1)) - p.1 = z := by abel
      have hs : r.2 + (z + (p.1 - r.1)) - v = z + (p.1 + r.2 - r.1 - v) := by abel
      rw [tau_eq_rooted_of_add_right q hq p.1,
        tau_eq_rooted_of_add_right q hq v, hm, hs]
      ac_rfl
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro v
      apply mul_le_mul' le_rfl
      unfold diagramWeightedPair
      exact ENNReal.tsum_le_tsum fun z =>
        mul_le_mul' (weight_mul_tau_le_weight_mul_continuation q w hw z) le_rfl

/-- The first coordinate costs the rooted step mass times the weighted-pair
supremum. Translation invariance roots the step mass, not the deleted connector. -/
theorem diagramMarkedConnectorCore_false_le_step_mass_mul_iSup [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (p r : G × G) :
    diagramMarkedConnectorCore q w false p r ≤
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) *
        ⨆ a, diagramWeightedPair q w a := by
  classical
  calc
    _ ≤ ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v *
          diagramWeightedPair q w (p.1 + r.2 - r.1 - v) :=
      diagramMarkedConnectorCore_false_le_tsum_weightedPair q hq w hw p r
    _ ≤ ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v *
          (⨆ a, diagramWeightedPair q w a) :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (le_iSup _ _)
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      simp_rw [offDiagonal_eq_rooted_of_add_right q hq p.2]
      simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
        (Equiv.addRight (-p.2)).tsum_eq
          (offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0)

/-- For the character mark, the first coordinate incurs precisely the step
mass and the second incurs one; the local core estimate is a conclusion. -/
theorem diagramMarkedConnectorCore_character_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (ε : Bool) (p r : G × G) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    diagramMarkedConnectorCore q w ε p r ≤
      (if ε then 1 else ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) *
        ⨆ a, diagramWeightedPair q w a := by
  dsimp only
  cases ε
  · exact diagramMarkedConnectorCore_false_le_step_mass_mul_iSup q hq _ (by simp) p r
  · simpa using
      diagramMarkedConnectorCore_true_le_iSup q hq
        (fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)) p r

end Lace

end PercLib.Percolation.Bond
