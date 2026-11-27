/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the forward and backward lace-diagram estimates of
Heydenreich and van der Hofstad (2017), Section 7.5.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.OriginTriangle
public import PercLib.Percolation.Bond.Lace.DiagramBounds

/-!
# Actual diagram norms from the continuation triangle

The forward and backward deleted connector masses are bounded separately.
Neither connector reversal nor equality of the two masses is asserted. The
initial and terminal bounds retain the smaller continuation value at zero.

## Main results

* `shifted_continuation_triangle_eq_step_tau_three`: the exact shifted identity.
* `diagramConnector_mass_le_step_tau_three`: the forward deleted mass bound.
* `diagramConnector_reverse_mass_le_step_tau_three`: the backward deleted mass bound.
* `diagramInitial_mass_le_min_triangle_step`: the exact diagonal improves the initial norm.
* `bubble_le_one_add_half_step_tau_three`: the sharper terminal bubble constant.
-/

@[expose] public section
noncomputable section

open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The shifted continuation triangle is the actual step-weighted triple
convolution at the displacement between its two starting vertices. -/
theorem shifted_continuation_triangle_eq_step_tau_three
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) :
    (∑' z, ∑' t, tau q a z * (∑' v, offDiagonal (fun c e : G =>
      (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) b v * tau q v t) * tau q z t) =
      (offDiagonal (fun c e : G =>
        (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) (a - b) := by
  have hrow (v : G) : (∑' z, ∑' t, tau q a z * tau q z t * tau q v t) =
      (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0)) (a - v) := by
    rw [show a - v = 0 - (v - a) by abel, tau_three_neg_eq_triangle q hq]
    rw [← (Equiv.addRight a).tsum_eq]
    apply tsum_congr
    intro z
    rw [← (Equiv.addRight a).tsum_eq]
    apply tsum_congr
    intro t
    simp only [Equiv.coe_addRight]
    have h1 : tau q a (z + a) = tau q 0 z := by
      rw [tau_eq_rooted_of_add_right q hq a (z + a), add_sub_cancel_right]
    have h2 : tau q (z + a) (t + a) = tau q z t := by
      rw [tau_eq_rooted_of_add_right q hq (z + a) (t + a),
        tau_eq_rooted_of_add_right q hq z t]
      congr 1
      abel
    have h3 : tau q v (t + a) = tau q (v - a) t := by
      rw [tau_eq_rooted_of_add_right q hq v (t + a),
        tau_eq_rooted_of_add_right q hq (v - a) t]
      congr 1
      abel
    rw [h1, h2, h3]
  calc
    _ = ∑' v, offDiagonal (fun c e : G =>
        (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) b v *
          (∑' z, ∑' t, tau q a z * tau q z t * tau q v t) := by
      simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      trans ∑' z, ∑' v, ∑' t, tau q a z * (offDiagonal (fun c e : G =>
        (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) b v * tau q v t) * tau q z t
      · apply tsum_congr
        intro z
        rw [ENNReal.tsum_comm]
      · rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro v
        apply tsum_congr
        intro z
        apply tsum_congr
        intro t
        ac_rfl
    _ = _ := by
      simp_rw [hrow]
      rw [addRingConvolution_eq_tsum_sub, ← (Equiv.addRight b).tsum_eq]
      apply tsum_congr
      intro v
      simp only [Equiv.coe_addRight]
      rw [offDiagonal_eq_rooted_of_add_right q hq b (v + b), add_sub_cancel_right]
      congr 2
      abel

/-- The forward deleted connector mass is bounded by its actual shifted
continuation triangle. -/
theorem diagramConnector_mass_le_step_tau_three (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (p : G × G) :
    (∑' r : G × G, diagramConnector q p r * tau q r.1 r.2) ≤
      (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) (p.1 - p.2) := by
  rw [← shifted_continuation_triangle_eq_step_tau_three q hq p.1 p.2,
    ENNReal.tsum_prod']
  exact ENNReal.tsum_le_tsum fun z => ENNReal.tsum_le_tsum fun t =>
    mul_le_mul' (diagramConnector_le q p (z, t)) le_rfl

/-- The backward deleted connector mass has its own comparison. The proof
uses symmetry only after dropping deletion, and does not reverse the connector. -/
theorem diagramConnector_reverse_mass_le_step_tau_three (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (p : G × G) :
    (∑' r : G × G, diagramConnector q r p * tau q r.1 r.2) ≤
      (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) (p.1 - p.2) := by
  rw [← shifted_continuation_triangle_eq_step_tau_three q hq p.1 p.2,
    ENNReal.tsum_prod']
  apply ENNReal.tsum_le_tsum
  intro z
  apply ENNReal.tsum_le_tsum
  intro t
  have h := diagramConnector_le q (z, t) p
  simp only at h
  rw [tau_comm q z p.1, tsum_offDiagonal_mul_tau_comm q hq t p.2] at h
  exact mul_le_mul' h le_rfl

/-- Removing the joining diagonal retains an actual nonnegative subdiagram. -/
theorem offDiagonal_continuation_triangle_le_step_tau_three
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) :
    (∑' z, ∑' t, tau q a z * (∑' v, offDiagonal (fun c e : G =>
      (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) b v * tau q v t) *
        offDiagonal (tau q) z t) ≤
      (offDiagonal (fun c e : G =>
        (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) (a - b) := by
  rw [← shifted_continuation_triangle_eq_step_tau_three q hq a b]
  classical
  apply ENNReal.tsum_le_tsum
  intro z
  apply ENNReal.tsum_le_tsum
  intro t
  apply mul_le_mul' le_rfl
  by_cases ht : t = z <;> simp [offDiagonal, ht]

open Classical in
/-- The nontrivial initial mass is controlled by the continuation at zero. -/
theorem nontrivial_initial_mass_le_step_tau_three_zero [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    (∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p) ≤
      (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0 := by
  simpa only [continuation_triangle_eq_step_tau_three q hq] using
    nontrivial_initial_mass_le_continuation_triangle q

/-- The exact initial diagonal costs only one; the rest keeps the smaller
continuation value at zero. The ordinary triangle estimate is also retained. -/
theorem diagramInitial_mass_le_min_triangle_step [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    (∑' p, diagramInitial q 0 p) ≤ min
      (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0)
      (1 + (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0) := by
  classical
  apply le_min
  · refine (diagramInitial_mass_le_triangle q 0).trans_eq ?_
    apply tsum_congr
    intro u
    apply tsum_congr
    intro v
    rw [tau_comm q v 0]
    ac_rfl
  · have heq := tsum_diagramInitial_mul_eq_diagonal_add q 0 (fun _ => 1)
    simp only [mul_one] at heq
    rw [heq]
    exact add_le_add le_rfl (nontrivial_initial_mass_le_step_tau_three_zero q hq)

/-- Every shifted bubble is bounded by the rooted bubble, by the existing
nonnegative Cauchy–Schwarz inequality and translation invariance. -/
theorem bubble_le_rooted_bubble (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) :
    (∑' z, tau q a z * tau q b z) ≤ ∑' z, tau q 0 z ^ 2 := by
  have hrow (x : G) : (∑' z, tau q x z ^ 2) = ∑' z, tau q 0 z ^ 2 := by
    rw [← (Equiv.addRight x).tsum_eq]
    apply tsum_congr
    intro z
    simp only [Equiv.coe_addRight]
    rw [tau_eq_rooted_of_add_right q hq x (z + x), add_sub_cancel_right]
  have h := PercLib.Analysis.tsum_mul_le_Lp_mul_Lq (tau q a) (tau q b)
    Real.HolderConjugate.two_two
  simp only [ENNReal.rpow_two, hrow] at h
  refine h.trans_eq ?_
  rw [← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
  norm_num

/-- The two distinct bubble contributions in the initial row improve the
terminal bubble factor to one plus half the origin continuation triangle. -/
theorem bubble_le_one_add_half_step_tau_three [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) :
    (∑' z, tau q a z * tau q b z) ≤
      1 + (1 / 2 : ℝ≥0∞) * (offDiagonal (fun c e : G =>
        (unitInterval.toNNReal (q s(c, e)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0 := by
  classical
  refine (bubble_le_rooted_bubble q hq a b).trans ?_
  rw [tsum_tau_sq_eq_one_add_offDiagonal]
  apply add_le_add le_rfl
  have h := (two_mul_offDiagonal_bubble_le_nontrivial_initial q).trans
    (nontrivial_initial_mass_le_step_tau_three_zero q hq)
  have he (c : ℝ≥0∞) : c = (1 / 2 : ℝ≥0∞) * (2 * c) := by
    rw [one_div, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
      one_mul]
  calc
    _ = (1 / 2 : ℝ≥0∞) * (2 * ∑' z, if z = 0 then 0 else tau q 0 z ^ 2) := he _
    _ ≤ _ := mul_le_mul' le_rfl h

/-- The forward transfer retains its actual deleted mass; only the second
geometry uses the uniform continuation-triangle bound. -/
theorem diagramTransfer_mass_le_continuation_bound [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (Δ M : ℝ≥0∞)
    (hΔ : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ Δ)
    (hM : ∀ x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ M) (p : G × G) :
    (∑' r, diagramTransfer q p r) ≤
      Δ * ((∑' r : G × G, diagramConnector q p r * tau q r.1 r.2) + M) := by
  apply diagramTransfer_mass_le_deleted_of_add_right q hq p Δ _ M hΔ le_rfl
  intro a b
  exact (offDiagonal_continuation_triangle_le_step_tau_three q hq a b).trans (hM _)

/-- Backward summation retains the reverse deleted mass separately from the
forward mass. This is a bound on `B C`, not a reversal of `C B`. -/
theorem diagramInterior_connector_mass_le_continuation_bound [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (Δ M : ℝ≥0∞)
    (hΔ : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ Δ)
    (hM : ∀ x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ M) (p : G × G) :
    (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤
      Δ * ((∑' r : G × G, diagramConnector q r p * tau q r.1 r.2) + M) := by
  apply diagramInterior_connector_mass_le_deleted_of_add_right q hq p Δ _ M hΔ le_rfl
  intro a b
  exact (offDiagonal_continuation_triangle_le_step_tau_three q hq a b).trans (hM _)

/-- The final factor costs the actual forward deleted mass times the sharper
origin bubble bound; it is not replaced by another full transfer. -/
theorem diagramTerminal_mass_le_origin_continuation [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (p : G × G) :
    (∑' y, diagramTerminal q p y) ≤
      (∑' r : G × G, diagramConnector q p r * tau q r.1 r.2) *
        (1 + (1 / 2 : ℝ≥0∞) * (offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
            (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0) :=
  diagramTerminal_mass_le q p _ _ (bubble_le_one_add_half_step_tau_three q hq) le_rfl

/-- The proved uniform continuation bound yields the scalar forward row constant. -/
theorem diagramTransfer_mass_le_two_mul_triangle_continuation [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (Δ M : ℝ≥0∞)
    (hΔ : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ Δ)
    (hM : ∀ x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ M) (p : G × G) :
    (∑' r, diagramTransfer q p r) ≤ 2 * Δ * M := by
  refine (diagramTransfer_mass_le_continuation_bound q hq Δ M hΔ hM p).trans ?_
  calc
    _ ≤ Δ * (M + M) := mul_le_mul' le_rfl (add_le_add
      ((diagramConnector_mass_le_step_tau_three q hq p).trans (hM _)) le_rfl)
    _ = _ := by ring

/-- The scalar backward constant follows from its separately proved reverse
connector comparison. -/
theorem diagramInterior_connector_mass_le_two_mul_triangle_continuation [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (Δ M : ℝ≥0∞)
    (hΔ : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ Δ)
    (hM : ∀ x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ M) (p : G × G) :
    (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ 2 * Δ * M := by
  refine (diagramInterior_connector_mass_le_continuation_bound q hq Δ M hΔ hM p).trans ?_
  calc
    _ ≤ Δ * (M + M) := mul_le_mul' le_rfl (add_le_add
      ((diagramConnector_reverse_mass_le_step_tau_three q hq p).trans (hM _)) le_rfl)
    _ = _ := by ring

/-- The scalar terminal constant keeps the exact origin value separately
from the uniform continuation bound. -/
theorem diagramTerminal_mass_le_continuation_bound [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (M : ℝ≥0∞)
    (hM : ∀ x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ M) (p : G × G) :
    (∑' y, diagramTerminal q p y) ≤
      M * (1 + (1 / 2 : ℝ≥0∞) * (offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0) :=
  (diagramTerminal_mass_le_origin_continuation q hq p).trans (mul_le_mul'
    ((diagramConnector_mass_le_step_tau_three q hq p).trans (hM _)) le_rfl)

end PercLib.Percolation.Bond.Lace
