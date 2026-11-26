/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs for character-weighted deleted-bond diagrams; no upstream
proof is copied. The alternating routes refine the diagram-marking argument
of Heydenreich and van der Hofstad (2017), Section 7.4.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Coefficients
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Tactic.Ring

/-!
# Character weights on the actual pair-state diagrams

## Main results

The nonnegative mark is written inline as `ofReal (1 - Re ψ)`. A finite route
costs only its length, and zero displacements can be excluded from that length.
Splitting an alternating route across one transfer retains the deleted connector. For the
route from the incoming second coordinate to the outgoing first coordinate,
the joining mark annihilates the second interior geometry exactly.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- Splitting a unitary-character displacement costs at most two. -/
theorem character_weight_add_le (ψ : AddChar G Circle) (a b : G) :
    ENNReal.ofReal (1 - (ψ (a + b) : ℂ).re) ≤
      2 * (ENNReal.ofReal (1 - (ψ a : ℂ).re) +
        ENNReal.ofReal (1 - (ψ b : ℂ).re)) := by
  have hn : ‖(ψ (a + b) : ℂ) - 1‖ ≤
      ‖(ψ a : ℂ) - 1‖ + ‖(ψ b : ℂ) - 1‖ := by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
    calc
      _ = ‖((ψ a : ℂ) - 1) * (ψ b : ℂ) + ((ψ b : ℂ) - 1)‖ := by
        congr 1
        ring
      _ ≤ ‖((ψ a : ℂ) - 1) * (ψ b : ℂ)‖ + ‖(ψ b : ℂ) - 1‖ :=
        norm_add_le _ _
      _ = _ := by rw [norm_mul, Circle.norm_coe, mul_one]
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (add_sq_le (a := ‖(ψ a : ℂ) - 1‖) (b := ‖(ψ b : ℂ) - 1‖))
  rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (Circle.norm_coe _),
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Circle.norm_coe _),
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Circle.norm_coe _)] at hs
  have hr : 1 - (ψ (a + b) : ℂ).re ≤
      2 * ((1 - (ψ a : ℂ).re) + (1 - (ψ b : ℂ).re)) := by linarith
  calc
    _ ≤ ENNReal.ofReal (2 * ((1 - (ψ a : ℂ).re) + (1 - (ψ b : ℂ).re))) :=
      ENNReal.ofReal_le_ofReal hr
    _ = 2 * ENNReal.ofReal ((1 - (ψ a : ℂ).re) + (1 - (ψ b : ℂ).re)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ _ := mul_le_mul' le_rfl ENNReal.ofReal_add_le

/-- The same character bound along a route through an intermediate vertex. -/
theorem character_weight_sub_le (ψ : AddChar G Circle) (a b c : G) :
    ENNReal.ofReal (1 - (ψ (c - a) : ℂ).re) ≤
      2 * (ENNReal.ofReal (1 - (ψ (b - a) : ℂ).re) +
        ENNReal.ofReal (1 - (ψ (c - b) : ℂ).re)) := by
  have h : (b - a) + (c - b) = c - a := by abel
  simpa only [h] using character_weight_add_le ψ (b - a) (c - b)

/-- One application of Cauchy–Schwarz marks a whole finite route with its
length as the constant, rather than repeated factors of two. -/
theorem character_weight_sum_le {ι : Type*} (ψ : AddChar G Circle)
    (s : Finset ι) (d : ι → G) :
    ENNReal.ofReal (1 - (ψ (∑ i ∈ s, d i) : ℂ).re) ≤
      (s.card : ℝ≥0∞) * ∑ i ∈ s, ENNReal.ofReal (1 - (ψ (d i) : ℂ).re) := by
  classical
  have hstep (a b : G) : ‖(ψ (a + b) : ℂ) - 1‖ ≤
      ‖(ψ a : ℂ) - 1‖ + ‖(ψ b : ℂ) - 1‖ := by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
    calc
      _ = ‖((ψ a : ℂ) - 1) * (ψ b : ℂ) + ((ψ b : ℂ) - 1)‖ := by
        congr 1
        ring
      _ ≤ ‖((ψ a : ℂ) - 1) * (ψ b : ℂ)‖ + ‖(ψ b : ℂ) - 1‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, Circle.norm_coe, mul_one]
  have hn : ‖(ψ (∑ i ∈ s, d i) : ℂ) - 1‖ ≤
      ∑ i ∈ s, ‖(ψ (d i) : ℂ) - 1‖ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hstep (d i) _).trans (add_le_add le_rfl ih)
  have hcs : (∑ i ∈ s, ‖(ψ (d i) : ℂ) - 1‖) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖(ψ (d i) : ℂ) - 1‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s
      (fun _ => (1 : ℝ)) (fun i => ‖(ψ (d i) : ℂ) - 1‖)
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  simp_rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (Circle.norm_coe _)] at hs
  rw [← Finset.mul_sum] at hs
  have hr : 1 - (ψ (∑ i ∈ s, d i) : ℂ).re ≤
      (s.card : ℝ) * ∑ i ∈ s, (1 - (ψ (d i) : ℂ).re) := by nlinarith
  have hnonneg (i : ι) : 0 ≤ 1 - (ψ (d i) : ℂ).re := by
    have h := Complex.re_le_norm (ψ (d i) : ℂ)
    rw [Circle.norm_coe] at h
    exact sub_nonneg.mpr h
  have h := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)] at h
  exact h

open scoped Classical in
/-- Zero displacements need not count toward the route constant. In
particular, coincident joining coordinates give a further exact gain. -/
theorem character_weight_sum_le_nonzero_card {ι : Type*} (ψ : AddChar G Circle)
    (s : Finset ι) (d : ι → G) :
    ENNReal.ofReal (1 - (ψ (∑ i ∈ s, d i) : ℂ).re) ≤
      ((s.filter fun i => d i ≠ 0).card : ℝ≥0∞) *
        ∑ i ∈ s, ENNReal.ofReal (1 - (ψ (d i) : ℂ).re) := by
  have h := character_weight_sum_le ψ (s.filter fun i => d i ≠ 0) d
  rw [Finset.sum_filter_ne_zero] at h
  refine h.trans (mul_le_mul' le_rfl ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => bot_le)

/-- Character-weighted actual coefficients are still dominated by the proved
canonical diagram, before any marked-diagram estimate is used. -/
theorem laceCoefficient_succ_character_weight_le_diagram [Countable G]
    (q : Sym2 G → unitInterval) (ψ : AddChar G Circle) (n : ℕ) (x : G) :
    (∑' y, ENNReal.ofReal (1 - (ψ (y - x) : ℂ).re) *
      laceCoefficient q (n + 1) x y) ≤
      ∑' y, ENNReal.ofReal (1 - (ψ (y - x) : ℂ).re) * laceDiagram q n x y :=
  ENNReal.tsum_le_tsum fun y =>
    mul_le_mul' le_rfl (laceCoefficient_succ_le_laceDiagram q n x y)

/-- A joining mark from the incoming second to outgoing first coordinate
vanishes on the second interior geometry, whose two coordinates coincide. -/
theorem character_weight_diagramInterior_eq_first
    (q : Sym2 G → unitInterval) (ψ : AddChar G Circle) (s r : G × G) :
    ENNReal.ofReal (1 - (ψ (r.1 - s.2) : ℂ).re) * diagramInterior q s r =
      ENNReal.ofReal (1 - (ψ (r.1 - s.2) : ℂ).re) *
        (tau q s.1 s.2 * tau q s.1 r.2 * tau q s.2 r.1 * tau q r.1 r.2) := by
  classical
  by_cases h : s.2 = r.1
  · simp [h, diagramInterior]
  · simp only [diagramInterior, ite_eq_right h, add_zero]

/-- The odd alternating route crosses the second connector arm and then the
joining arm. The latter sees only the first interior geometry. -/
theorem diagramTransfer_character_weight_odd_le
    (q : Sym2 G → unitInterval) (ψ : AddChar G Circle) (p r : G × G) :
    ENNReal.ofReal (1 - (ψ (r.1 - p.2) : ℂ).re) * diagramTransfer q p r ≤
      2 * (∑' s : G × G, ENNReal.ofReal (1 - (ψ (s.2 - p.2) : ℂ).re) *
        diagramConnector q p s * diagramInterior q s r) +
      2 * (∑' s : G × G, ENNReal.ofReal (1 - (ψ (r.1 - s.2) : ℂ).re) *
        diagramConnector q p s *
          (tau q s.1 s.2 * tau q s.1 r.2 * tau q s.2 r.1 * tau q r.1 r.2)) := by
  classical
  unfold diagramTransfer
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro s
  calc
    _ ≤ (2 * (ENNReal.ofReal (1 - (ψ (s.2 - p.2) : ℂ).re) +
        ENNReal.ofReal (1 - (ψ (r.1 - s.2) : ℂ).re))) *
          (diagramConnector q p s * diagramInterior q s r) :=
      mul_le_mul' (character_weight_sub_le ψ p.2 s.2 r.1) le_rfl
    _ = 2 * (ENNReal.ofReal (1 - (ψ (s.2 - p.2) : ℂ).re) *
        diagramConnector q p s * diagramInterior q s r) +
      2 * (diagramConnector q p s *
        (ENNReal.ofReal (1 - (ψ (r.1 - s.2) : ℂ).re) * diagramInterior q s r)) := by ring
    _ = _ := by
      rw [character_weight_diagramInterior_eq_first]
      ac_rfl

/-- The even alternating route crosses the deleted connector arm and then
the first-to-second-coordinate interior arm. Deletion is retained in both terms. -/
theorem diagramTransfer_character_weight_even_le
    (q : Sym2 G → unitInterval) (ψ : AddChar G Circle) (p r : G × G) :
    ENNReal.ofReal (1 - (ψ (r.2 - p.1) : ℂ).re) * diagramTransfer q p r ≤
      2 * (∑' s : G × G,
        (ENNReal.ofReal (1 - (ψ (s.1 - p.1) : ℂ).re) +
          ENNReal.ofReal (1 - (ψ (r.2 - s.1) : ℂ).re)) *
            diagramConnector q p s * diagramInterior q s r) := by
  classical
  unfold diagramTransfer
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  calc
    _ ≤ (2 * (ENNReal.ofReal (1 - (ψ (s.1 - p.1) : ℂ).re) +
        ENNReal.ofReal (1 - (ψ (r.2 - s.1) : ℂ).re))) *
          (diagramConnector q p s * diagramInterior q s r) :=
      mul_le_mul' (character_weight_sub_le ψ p.1 s.1 r.2) le_rfl
    _ = _ := by ac_rfl

end PercLib.Percolation.Bond.Lace
