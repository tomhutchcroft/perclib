/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.TreeGraph.FourPoint

/-!
# Four-point bounds on the weighted third cluster moment

## Main results

The actual connection-weighted third cluster moment is bounded by the three
four-terminal tree pairings. All sums and expectations are nonnegative extended
real quantities; neither finite susceptibility nor finite clusters are assumed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- The weighted third cluster moment is the corresponding joint-connection sum. -/
theorem lintegral_cluster_triple_tau_eq (q : Sym2 V → unitInterval) (o : V) :
    (∫⁻ ω, ∑' a, ∑' b, ∑' c,
      (conn o a ∩ (conn o b ∩ conn o c)).indicator
        (fun _ => tau q a b * tau q a c) ω ∂law q) =
      ∑' a, ∑' b, ∑' c, (tau q a b * tau q a c) *
        law q (conn o a ∩ (conn o b ∩ conn o c)) := by
  have hm : ∀ a b c, Measurable
      ((conn o a ∩ (conn o b ∩ conn o c)).indicator
        (fun _ => tau q a b * tau q a c)) := fun a b c =>
    measurable_const.indicator ((measurableSet_conn o a).inter
      ((measurableSet_conn o b).inter (measurableSet_conn o c)))
  rw [lintegral_tsum fun a => (Measurable.tsum fun b =>
    Measurable.tsum fun c => hm a b c).aemeasurable]
  apply tsum_congr
  intro a
  rw [lintegral_tsum fun b => (Measurable.tsum fun c => hm a b c).aemeasurable]
  apply tsum_congr
  intro b
  rw [lintegral_tsum fun c => (hm a b c).aemeasurable]
  apply tsum_congr
  intro c
  exact lintegral_indicator_const ((measurableSet_conn o a).inter
    ((measurableSet_conn o b).inter (measurableSet_conn o c))) _

/-- The three tree pairings bound the actual weighted third cluster moment,
with coefficient one for each pairing. -/
theorem lintegral_cluster_triple_tau_le_pairings (q : Sym2 V → unitInterval) (o : V) :
    (∫⁻ ω, ∑' a, ∑' b, ∑' c,
      (conn o a ∩ (conn o b ∩ conn o c)).indicator
        (fun _ => tau q a b * tau q a c) ω ∂law q) ≤
      ∑' a, ∑' b, ∑' c, (tau q a b * tau q a c) *
        ∑' u, ∑' v, tau q o u *
          (tau q u a * tau q u v * tau q v b * tau q v c +
            tau q u b * tau q u v * tau q v a * tau q v c +
            tau q u c * tau q u v * tau q v a * tau q v b) := by
  rw [lintegral_cluster_triple_tau_eq]
  exact ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b =>
    ENNReal.tsum_le_tsum fun c =>
      mul_le_mul' le_rfl (law_three_conn_le_three_pairings q o a b c)

/-- Translation and symmetry reroot the exceptional four-point pairing as the
cube of the two-step kernel. The identity holds for infinite nonnegative sums. -/
theorem tsum_pairing_eq_tsum_cube {G : Type*} [AddCommGroup G]
    (K : G → G → ℝ≥0∞) (hs : ∀ x y, K x y = K y x)
    (ht : ∀ x y g, K (x + g) (y + g) = K x y) :
    (∑' a, ∑' v, K 0 a * K 0 v * (∑' b, K a b * K b v) ^ 2) =
      ∑' w, (∑' b, K 0 b * K b w) ^ 3 := by
  have hb (a w : G) : (∑' b, K a b * K b (w + a)) =
      ∑' b, K 0 b * K b w := by
    rw [← (Equiv.addRight a).tsum_eq]
    apply tsum_congr
    intro b
    simp only [Equiv.coe_addRight]
    have hk : K a (b + a) = K 0 b := by
      simpa only [zero_add] using ht 0 b a
    rw [hk, ht]
  have hn (a : G) : K 0 (-a) = K 0 a := by
    calc
      K 0 (-a) = K a 0 := by simpa using (ht 0 (-a) a).symm
      _ = K 0 a := hs a 0
  have hc (w : G) : (∑' a, K 0 a * K 0 (w + a)) =
      ∑' b, K 0 b * K b w := by
    rw [← (Equiv.neg G).tsum_eq]
    apply tsum_congr
    intro b
    simp only [Equiv.neg_apply, hn]
    congr 1
    simpa using (ht 0 (w + -b) b).symm
  calc
    _ = ∑' a, ∑' w, K 0 a * K 0 (w + a) *
        (∑' b, K 0 b * K b w) ^ 2 := by
      apply tsum_congr
      intro a
      rw [← (Equiv.addRight a).tsum_eq]
      simp only [Equiv.coe_addRight, hb]
    _ = ∑' w, ∑' a, K 0 a * K 0 (w + a) *
        (∑' b, K 0 b * K b w) ^ 2 := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro w
      rw [ENNReal.tsum_mul_right, hc]
      ring

/-- The other four-point pairing is the triangle weighted by the two-step and
three-step kernels. Translation invariance removes the second branch location. -/
theorem tsum_cross_pairing_eq_weighted_triangle {G : Type*} [AddCommGroup G]
    (K : G → G → ℝ≥0∞) (hs : ∀ x y, K x y = K y x)
    (ht : ∀ x y g, K (x + g) (y + g) = K x y) :
    (∑' a, ∑' v, K 0 v * K v a *
      (∑' b, K 0 b * K b a) * (∑' b, K a b * K b v)) =
      ∑' w, K 0 w * (∑' b, K 0 b * K b w) *
        (∑' u, ∑' z, K 0 u * K u z * K z w) := by
  let B : G → G → ℝ≥0∞ := fun x y => ∑' b, K x b * K b y
  have hbs (x y : G) : B x y = B y x := by
    apply tsum_congr
    intro b
    rw [hs x b, hs b y]
    ac_rfl
  have hbt (x y g : G) : B (x + g) (y + g) = B x y := by
    change (∑' b, K (x + g) b * K b (y + g)) = _
    rw [← (Equiv.addRight g).tsum_eq]
    apply tsum_congr
    intro b
    simp only [Equiv.coe_addRight, ht]
  have hn (v : G) : K 0 (-v) = K 0 v := by
    calc
      K 0 (-v) = K v 0 := by simpa using (ht 0 (-v) v).symm
      _ = K 0 v := hs v 0
  have hb (v w : G) : B (w + v) v = B 0 w := by
    rw [hbs]
    simpa only [zero_add] using hbt 0 w v
  have hc (w : G) : (∑' v, K 0 v * B 0 (w + v)) =
      ∑' u, ∑' z, K 0 u * K u z * K z w := by
    rw [← (Equiv.neg G).tsum_eq]
    calc
      (∑' v, K 0 (-v) * B 0 (w + -v)) = ∑' v, K 0 v * B v w := by
        apply tsum_congr
        intro v
        rw [hn]
        congr 1
        simpa using (hbt 0 (w + -v) v).symm
      _ = _ := by
        simp only [B, ← ENNReal.tsum_mul_left, mul_assoc]
  change (∑' a, ∑' v, K 0 v * K v a * B 0 a * B a v) = _
  calc
    _ = ∑' v, ∑' a, K 0 v * K v a * B 0 a * B a v := ENNReal.tsum_comm
    _ = ∑' v, ∑' w, K 0 w * B 0 w * (K 0 v * B 0 (w + v)) := by
      apply tsum_congr
      intro v
      rw [← (Equiv.addRight v).tsum_eq]
      apply tsum_congr
      intro w
      simp only [Equiv.coe_addRight, hb]
      have hk : K v (w + v) = K 0 w := by
        simpa only [zero_add] using ht 0 w v
      rw [hk]
      ac_rfl
    _ = ∑' w, ∑' v, K 0 w * B 0 w * (K 0 v * B 0 (w + v)) :=
      ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro w
      rw [ENNReal.tsum_mul_left, hc]

end PercLib.Percolation.Bond
