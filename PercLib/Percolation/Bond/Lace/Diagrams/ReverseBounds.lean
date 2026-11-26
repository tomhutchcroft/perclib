/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs refining the backward summation of Heydenreich and van der
Hofstad (2017), Section 7.5, by retaining the excluded joining diagonal.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.TransferBounds

/-!
# Backward bounds for the deleted pair-state diagrams

## Main results

The interior column is evaluated exactly. Summing the backward product
`B C_d` retains the deleted connector mass in its first geometry and the
off-diagonal convolution norm in its second geometry. No reversal identity
for the deleted connector or the forward transfer is assumed.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The exact interior column separates an open triangle from the geometry
with an excluded joining diagonal. -/
theorem diagramInterior_column_mass_eq (q : Sym2 V → unitInterval) (r : V × V) :
    (∑' s, diagramInterior q s r) =
      tau q r.1 r.2 * (∑' u, ∑' v, tau q r.1 u * tau q u v * tau q v r.2) +
      ∑' z, offDiagonal (tau q) r.1 z * tau q z r.2 *
        (∑' u, tau q z u * tau q u r.2) := by
  classical
  rw [ENNReal.tsum_prod']
  simp only [diagramInterior, ENNReal.tsum_add]
  congr 1
  · rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro u
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro v
    rw [tau_comm q v u, tau_comm q u r.1]
    ac_rfl
  · simp only [tsum_ite_eq]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro z
    apply tsum_congr
    intro u
    by_cases hz : z = r.1
    · simp [hz, offDiagonal]
    · simp only [ite_eq_right hz, offDiagonal]
      ac_rfl

/-- Exact backward decomposition. The connector is still the actual deleted
one, with its arguments in their original order. -/
theorem diagramInterior_connector_mass_eq (q : Sym2 V → unitInterval) (p : V × V) :
    (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) =
      (∑' r : V × V, diagramConnector q r p * tau q r.1 r.2 *
        (∑' u, ∑' v, tau q r.1 u * tau q u v * tau q v r.2)) +
      ∑' r : V × V, ∑' z, diagramConnector q r p * offDiagonal (tau q) r.1 z *
        tau q z r.2 * (∑' u, tau q z u * tau q u r.2) := by
  classical
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right, diagramInterior_column_mass_eq, add_mul]
  rw [ENNReal.tsum_add]
  congr 1
  · apply tsum_congr
    intro r
    ac_rfl
  · apply tsum_congr
    intro r
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro z
    ac_rfl

section Translation

variable {G : Type*} [AddCommGroup G]

omit [AddCommGroup G] in
/-- The one-step continuation is carried by every profile-preserving vertex
equivalence. This follows from the existing bond-law transport API. -/
theorem tsum_offDiagonal_mul_tau_apply_equiv
    (q : Sym2 G → unitInterval) (e : G ≃ G)
    (hq : ∀ a, q (Sym2.map e a) = q a) (x y : G) :
    (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) (e x) v * tau q v (e y)) =
      ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y := by
  classical
  rw [← e.tsum_eq]
  apply tsum_congr
  intro v
  rw [offDiagonal_apply_equiv q e hq]
  rw [tau_eq_of_map_law e
    (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q e hq)]

/-- Translation covariance of the one-step continuation. -/
theorem tsum_offDiagonal_mul_tau_add_right
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x y g : G) :
    (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) (x + g) v * tau q v (y + g)) =
      ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y := by
  apply tsum_offDiagonal_mul_tau_apply_equiv q (Equiv.addRight g)
  intro a
  induction a using Sym2.ind with
  | _ u v => exact hq u v g

/-- The continuation `J * tau` is symmetric for a translation-invariant
undirected profile. This does not assert symmetry of the deleted connector. -/
theorem tsum_offDiagonal_mul_tau_comm
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x y : G) :
    (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y) =
      ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) y v * tau q v x := by
  let e := (Equiv.neg G).trans (Equiv.addRight (x + y))
  have he : ∀ a, q (Sym2.map e a) = q a := by
    intro a
    induction a using Sym2.ind with
    | _ u v =>
      change q s(-u + (x + y), -v + (x + y)) = q s(u, v)
      rw [hq]
      exact profile_neg_eq_of_add_right q hq s(u, v)
  have h := tsum_offDiagonal_mul_tau_apply_equiv q e he x y
  have hex : e x = y := by simp [e]
  have hey : e y = x := by simp [e, add_comm x y]
  rw [hex, hey] at h
  exact h.symm

/-- The second backward geometry retains the off-diagonal convolution norm.
Its free arm is summed before the remaining triangle is translated. -/
theorem diagramInterior_connector_second_mass_le_of_add_right
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (p : G × G) (Moff : ℝ≥0∞)
    (hMoff : ∀ s h, (∑' z, ∑' t, tau q s z *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t) *
          offDiagonal (tau q) z t) ≤ Moff) :
    (∑' r : G × G, ∑' z, diagramConnector q r p * offDiagonal (tau q) r.1 z *
      tau q z r.2 * (∑' u, tau q z u * tau q u r.2)) ≤
      (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * Moff := by
  classical
  let T : G → G → ℝ≥0∞ := fun x y => ∑' v,
    offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v *
      tau q v y
  have hTcomm (x y : G) : T x y = T y x :=
    tsum_offDiagonal_mul_tau_comm q hq x y
  have hTshift (z w : G) : T p.2 (z + w) = T (p.2 - w) z := by
    simpa only [sub_add_cancel] using
      tsum_offDiagonal_mul_tau_add_right q hq (p.2 - w) z w
  have hτ (x y g : G) : tau q (x + g) (y + g) = tau q x y := by
    apply tau_eq_of_map_law (Equiv.addRight g)
    apply PercLib.Probability.prodBernoulli_map_image_sym2_invariant
    intro a
    induction a using Sym2.ind with
    | _ u v => exact hq u v g
  have hC (a b : G) : diagramConnector q (a, b) p ≤ tau q p.1 a * T p.2 b := by
    have h := diagramConnector_le q (a, b) p
    change diagramConnector q (a, b) p ≤ tau q a p.1 * T b p.2 at h
    rwa [tau_comm q a p.1, hTcomm b p.2] at h
  have hinner (w : G) :
      (∑' z, ∑' a, tau q p.1 a * T p.2 (z + w) * offDiagonal (tau q) a z) ≤ Moff := by
    rw [ENNReal.tsum_comm]
    simp_rw [hTshift]
    exact hMoff p.1 (p.2 - w)
  calc
    _ ≤ ∑' a, ∑' b, ∑' z, ∑' u, tau q p.1 a * T p.2 b *
        offDiagonal (tau q) a z * tau q z b * tau q z u * tau q u b := by
      rw [ENNReal.tsum_prod']
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro b
      apply ENNReal.tsum_le_tsum
      intro z
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro u
      calc
        _ ≤ (tau q p.1 a * T p.2 b * offDiagonal (tau q) a z * tau q z b) *
            (tau q z u * tau q u b) :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' (hC a b) le_rfl) le_rfl) le_rfl
        _ = _ := by ac_rfl
    _ = ∑' z, ∑' b, ∑' u, ∑' a, tau q p.1 a * T p.2 b *
        offDiagonal (tau q) a z * tau q z b * tau q z u * tau q u b := by
      rw [ENNReal.tsum_comm]
      trans ∑' b, ∑' z, ∑' u, ∑' a, tau q p.1 a * T p.2 b *
        offDiagonal (tau q) a z * tau q z b * tau q z u * tau q u b
      · apply tsum_congr
        intro b
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro z
        rw [ENNReal.tsum_comm]
      · exact ENNReal.tsum_comm
    _ = ∑' z, ∑' w, ∑' v, ∑' a,
        (tau q 0 w * tau q 0 v * tau q v w) *
          (tau q p.1 a * T p.2 (z + w) * offDiagonal (tau q) a z) := by
      apply tsum_congr
      intro z
      rw [← (Equiv.addRight z).tsum_eq]
      apply tsum_congr
      intro w
      rw [← (Equiv.addRight z).tsum_eq]
      apply tsum_congr
      intro v
      apply tsum_congr
      intro a
      change tau q p.1 a * T p.2 (w + z) * offDiagonal (tau q) a z *
        tau q z (w + z) * tau q z (v + z) * tau q (v + z) (w + z) = _
      have hw := hτ 0 w z
      have hv := hτ 0 v z
      simp only [zero_add] at hw hv
      rw [hw, hv, hτ, add_comm w z]
      ac_rfl
    _ = ∑' w, ∑' v, (tau q 0 w * tau q 0 v * tau q v w) *
        (∑' z, ∑' a, tau q p.1 a * T p.2 (z + w) * offDiagonal (tau q) a z) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro w
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro v
      simp only [ENNReal.tsum_mul_left]
    _ ≤ ∑' w, ∑' v, (tau q 0 w * tau q 0 v * tau q v w) * Moff :=
      ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun _ =>
        mul_le_mul' le_rfl (hinner w)
    _ = _ := by
      simp only [ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro w
      apply tsum_congr
      intro v
      rw [tau_comm q 0 v, tau_comm q v w]
      ac_rfl

/-- Backward summation costs the deleted reverse connector mass and the
off-diagonal norm separately. This concerns `B C_d`, not the forward transfer. -/
theorem diagramInterior_connector_mass_le_deleted_of_add_right [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (p : G × G) (Δ Mrev Moff : ℝ≥0∞)
    (hΔ : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ Δ)
    (hMrev : (∑' r : G × G, diagramConnector q r p * tau q r.1 r.2) ≤ Mrev)
    (hMoff : ∀ s h, (∑' z, ∑' t, tau q s z *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t) *
          offDiagonal (tau q) z t) ≤ Moff) :
    (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤
      Δ * (Mrev + Moff) := by
  classical
  have hdiag (x : G) : (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) ≤ Δ := by
    rw [diagonal_triangle_eq_rooted q hq]
    exact hΔ
  rw [diagramInterior_connector_mass_eq]
  calc
    _ ≤ (∑' r : G × G, diagramConnector q r p * tau q r.1 r.2) * Δ +
        (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * Moff := by
      apply add_le_add
      · rw [← ENNReal.tsum_mul_right]
        exact ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl
          (open_triangle_le_of_diagonal_bound q Δ hdiag r.1 r.2)
      · exact diagramInterior_connector_second_mass_le_of_add_right q hq p Moff hMoff
    _ ≤ Mrev * Δ + Δ * Moff := add_le_add (mul_le_mul' hMrev le_rfl)
      (mul_le_mul' hΔ le_rfl)
    _ = _ := by rw [mul_add, mul_comm Mrev Δ]

end Translation

end PercLib.Percolation.Bond.Lace
