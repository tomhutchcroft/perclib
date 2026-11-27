/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.TripleClusterMoments

/-!
# Spatial contraction of the four-point cluster diagrams

## Main results

The three tree pairings for the weighted third cluster moment contract to one
cube of the two-step kernel and two weighted triangles. The identities retain
extended-real infinite sums and use only symmetry and translation invariance.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-- Summing the two terminal branches contracts the three tree pairings to
one squared two-step kernel and two cross pairings. -/
theorem tsum_four_point_pairings_eq {V : Type*} (K : V → V → ℝ≥0∞)
    (hs : ∀ x y, K x y = K y x) (u : V) :
    (∑' a, ∑' b, ∑' c, ∑' v, K a b * K a c *
      (K u a * K u v * K v b * K v c +
        K u b * K u v * K v a * K v c +
        K u c * K u v * K v a * K v b)) =
      (∑' a, ∑' v, K u a * K u v * (∑' b, K a b * K b v) ^ 2) +
        2 * ∑' a, ∑' v, K u v * K v a *
          (∑' b, K u b * K b a) * (∑' b, K a b * K b v) := by
  have hp (a v : V) :
      (∑' b, ∑' c, K a b * K a c *
        (K u a * K u v * K v b * K v c +
          K u b * K u v * K v a * K v c +
          K u c * K u v * K v a * K v b)) =
        K u a * K u v * (∑' b, K a b * K b v) ^ 2 +
          2 * (K u v * K v a *
            (∑' b, K u b * K b a) * (∑' b, K a b * K b v)) := by
    calc
      _ = (∑' b, K a b * K v b) * (∑' c, K a c * K v c) * (K u a * K u v) +
          (∑' b, K a b * K u b) * (∑' c, K a c * K v c) * (K u v * K v a) +
          (∑' b, K a b * K v b) * (∑' c, K a c * K u c) * (K u v * K v a) := by
        simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right,
          ← ENNReal.tsum_add]
        apply tsum_congr
        intro b
        apply tsum_congr
        intro c
        ring
      _ = _ := by
        have h₁ : (∑' b, K a b * K v b) = ∑' b, K a b * K b v := by
          apply tsum_congr
          intro b
          rw [hs v b]
        have h₂ : (∑' b, K a b * K u b) = ∑' b, K u b * K b a := by
          apply tsum_congr
          intro b
          rw [hs a b]
          ac_rfl
        rw [h₁, h₂]
        ring
  calc
    _ = ∑' a, ∑' v, ∑' b, ∑' c, K a b * K a c *
        (K u a * K u v * K v b * K v c +
          K u b * K u v * K v a * K v c +
          K u c * K u v * K v a * K v b) := by
      apply tsum_congr
      intro a
      rw [show (∑' b, ∑' c, ∑' v, K a b * K a c *
          (K u a * K u v * K v b * K v c +
            K u b * K u v * K v a * K v c +
            K u c * K u v * K v a * K v b)) =
          ∑' b, ∑' v, ∑' c, K a b * K a c *
          (K u a * K u v * K v b * K v c +
            K u b * K u v * K v a * K v c +
            K u c * K u v * K v a * K v b) from
        tsum_congr fun b => ENNReal.tsum_comm]
      exact ENNReal.tsum_comm
    _ = _ := by
      simp_rw [hp, ENNReal.tsum_add, ENNReal.tsum_mul_left]

/-- At every root, the four-point sum is the same cube plus twice the same
weighted triangle. No finite-sum approximation is needed. -/
theorem tsum_four_point_pairings_eq_rooted {G : Type*} [AddCommGroup G]
    (K : G → G → ℝ≥0∞) (hs : ∀ x y, K x y = K y x)
    (ht : ∀ x y g, K (x + g) (y + g) = K x y) (u : G) :
    (∑' a, ∑' b, ∑' c, ∑' v, K a b * K a c *
      (K u a * K u v * K v b * K v c +
        K u b * K u v * K v a * K v c +
        K u c * K u v * K v a * K v b)) =
      (∑' w, (∑' b, K 0 b * K b w) ^ 3) +
        2 * ∑' w, K 0 w * (∑' b, K 0 b * K b w) *
          (∑' z, ∑' v, K 0 z * K z v * K v w) := by
  have hk (x : G) : K u (x + u) = K 0 x := by
    simpa only [zero_add] using ht 0 x u
  calc
    _ = ∑' a, ∑' b, ∑' c, ∑' v, K a b * K a c *
        (K 0 a * K 0 v * K v b * K v c +
          K 0 b * K 0 v * K v a * K v c +
          K 0 c * K 0 v * K v a * K v b) := by
      rw [← (Equiv.addRight u).tsum_eq]
      apply tsum_congr
      intro a
      rw [← (Equiv.addRight u).tsum_eq]
      apply tsum_congr
      intro b
      rw [← (Equiv.addRight u).tsum_eq]
      apply tsum_congr
      intro c
      rw [← (Equiv.addRight u).tsum_eq]
      apply tsum_congr
      intro v
      simp only [Equiv.coe_addRight, ht, hk]
    _ = _ := by
      rw [tsum_four_point_pairings_eq K hs, tsum_pairing_eq_tsum_cube K hs ht,
        tsum_cross_pairing_eq_weighted_triangle K hs ht]

/-- The actual weighted third cluster moment is bounded by susceptibility times
one two-step cube and two weighted triangles. Translation invariance is the only
additional model hypothesis beyond the independent bond law. -/
theorem lintegral_cluster_triple_tau_le_chi_diagrams
    {G : Type*} [AddCommGroup G] [Countable G] (q : Sym2 G → unitInterval)
    (ht : ∀ x y g, tau q (x + g) (y + g) = tau q x y) :
    (∫⁻ ω, ∑' a, ∑' b, ∑' c,
      (conn 0 a ∩ (conn 0 b ∩ conn 0 c)).indicator
        (fun _ => tau q a b * tau q a c) ω ∂law q) ≤
      chi q 0 * ((∑' w, (∑' b, tau q 0 b * tau q b w) ^ 3) +
        2 * ∑' w, tau q 0 w * (∑' b, tau q 0 b * tau q b w) *
          (∑' z, ∑' v, tau q 0 z * tau q z v * tau q v w)) := by
  let F : G → G → G → G → G → ℝ≥0∞ := fun a b c u v =>
    tau q a b * tau q a c * (tau q 0 u *
      (tau q u a * tau q u v * tau q v b * tau q v c +
        tau q u b * tau q u v * tau q v a * tau q v c +
        tau q u c * tau q u v * tau q v a * tau q v b))
  refine (lintegral_cluster_triple_tau_le_pairings q 0).trans ?_
  have hexpand : (∑' a, ∑' b, ∑' c, (tau q a b * tau q a c) *
      ∑' u, ∑' v, tau q 0 u *
        (tau q u a * tau q u v * tau q v b * tau q v c +
          tau q u b * tau q u v * tau q v a * tau q v c +
          tau q u c * tau q u v * tau q v a * tau q v b)) =
      ∑' a, ∑' b, ∑' c, ∑' u, ∑' v, F a b c u v := by
    simp only [F, ← ENNReal.tsum_mul_left]
  rw [hexpand]
  have hrotate : (∑' a, ∑' b, ∑' c, ∑' u, ∑' v, F a b c u v) =
      ∑' u, ∑' a, ∑' b, ∑' c, ∑' v, F a b c u v := by
    calc
      _ = ∑' a, ∑' b, ∑' u, ∑' c, ∑' v, F a b c u v :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
      _ = ∑' a, ∑' u, ∑' b, ∑' c, ∑' v, F a b c u v :=
        tsum_congr fun a => ENNReal.tsum_comm
      _ = _ := ENNReal.tsum_comm
  rw [hrotate, chi_eq_tsum_tau, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro u
  have hfactor : (∑' a, ∑' b, ∑' c, ∑' v, F a b c u v) =
      tau q 0 u * ∑' a, ∑' b, ∑' c, ∑' v, tau q a b * tau q a c *
        (tau q u a * tau q u v * tau q v b * tau q v c +
          tau q u b * tau q u v * tau q v a * tau q v c +
          tau q u c * tau q u v * tau q v a * tau q v b) := by
    simp only [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro a
    apply tsum_congr
    intro b
    apply tsum_congr
    intro c
    apply tsum_congr
    intro v
    dsimp only [F]
    ring
  rw [hfactor, tsum_four_point_pairings_eq_rooted (tau q) (tau_comm q) ht]

end PercLib.Percolation.Bond
