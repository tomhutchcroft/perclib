/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original bounds for the actual second joining core. Mathematical reference:
Heydenreich and van der Hofstad (2017), Section 8.3, retaining both step masses.
No upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.WeightedPair
public import PercLib.Percolation.Bond.Lace.Diagrams.ZeroWeighted

/-!
# The actual second joining core

## Main results

Dropping the connector deletions and the excluded joining diagonal gives the
seven-edge spatial diagram used in its Fourier estimate. The two actual step
kernels remain present, so their two masses are retained in subsequent bounds.
-/

@[expose] public section
noncomputable section

open DiscreteConvolution
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The actual continuation between two vertices is the rooted step/two-point
convolution evaluated at their displacement. -/
theorem continuation_eq_rooted_convolution
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) :
    (∑' v, offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) a v * tau q v b) =
      ((offDiagonal (fun x y : G =>
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0) (b - a) := by
  have h := tsum_offDiagonal_mul_tau_add_right q hq a b (-a)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at h
  rw [← h, addRingConvolution_eq_tsum_sub]
  apply tsum_congr
  intro v
  rw [tau_eq_rooted_of_add_right q hq v (b - a)]

private theorem continuation_convolution_even
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    Function.Even ((offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0) := by
  intro z
  have h := tsum_offDiagonal_mul_tau_comm q hq 0 z
  rw [continuation_eq_rooted_convolution q hq,
    continuation_eq_rooted_convolution q hq] at h
  simpa only [sub_zero, zero_sub] using h.symm

/-- Summing the common translation of the final deleted connector costs the
actual step/two-point/two-point convolution, with its relative endpoint retained. -/
theorem tsum_diagramConnector_translate_le_convolution
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) (r : G × G) :
    (∑' y, diagramConnector q (a, b) (r.1 + y, r.2 + y)) ≤
      (tau q 0 ⋆ᵣ₊ ((offDiagonal (fun x y : G =>
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0))
          (b - a - (r.2 - r.1)) := by
  let U := (offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0
  calc
    _ ≤ ∑' y, tau q a (r.1 + y) * U (r.2 + y - b) := by
      apply ENNReal.tsum_le_tsum
      intro y
      simpa only [continuation_eq_rooted_convolution q hq, U] using
        diagramConnector_le q (a, b) (r.1 + y, r.2 + y)
    _ = _ := by
      rw [← (Equiv.addRight (a - r.1)).tsum_eq, addRingConvolution_eq_tsum_sub]
      apply tsum_congr
      intro z
      change tau q a (r.1 + (z + (a - r.1))) * U (r.2 + (z + (a - r.1)) - b) =
        tau q 0 z * U (b - a - (r.2 - r.1) - z)
      have hfirst : r.1 + (z + (a - r.1)) - a = z := by abel
      have hsecond : r.2 + (z + (a - r.1)) - b =
          -(b - a - (r.2 - r.1) - z) := by abel
      have hU : Function.Even U := continuation_convolution_even q hq
      rw [tau_eq_rooted_of_add_right q hq, hfirst, hsecond, hU]

/-- The actual second joining core is bounded by its seven-edge convolution
diagram. The weight is arbitrary and the two actual step kernels are preserved. -/
theorem diagramMarkedJoiningSecondCore_le_spatial_sum
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (p r : G × G) :
    let J := offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
    let T := tau q 0
    let U := J ⋆ᵣ₊ T
    let L := T ⋆ᵣ₊ U
    diagramMarkedJoiningSecondCore q w p r ≤
      ∑' u, ∑' s, ∑' t, ∑' z,
        T u * U (s - (p.2 - p.1)) * T (z - s) * T (u - z) * T (t - z) *
          (w (t - u) * T (t - u)) * L (t - s - (r.2 - r.1)) := by
  classical
  dsimp only
  let J := offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  let U := J ⋆ᵣ₊ tau q 0
  let L := tau q 0 ⋆ᵣ₊ U
  have hgroup (u v t : G) :
      (∑' y, diagramConnector q p (u, v) * tau q u t *
        (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) *
          diagramConnector q (v, t) (r.1 + y, r.2 + y) * w (t - u)) =
      (diagramConnector q p (u, v) * tau q u t *
        (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) * w (t - u)) *
          ∑' y, diagramConnector q (v, t) (r.1 + y, r.2 + y) := by
    conv_rhs => rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro y
    ring
  have hinner (u v t : G) :
      (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) ≤
        ∑' z, tau q v z * tau q z u * tau q z t := by
    apply ENNReal.tsum_le_tsum
    intro z
    split_ifs <;> first | exact zero_le | exact le_rfl
  have hfirst (u v : G) : diagramConnector q p (u, v) ≤
      tau q p.1 u * U (v - p.2) := by
    simpa only [continuation_eq_rooted_convolution q hq, U, J] using
      diagramConnector_le q p (u, v)
  calc
    _ = ∑' u, ∑' v, ∑' t,
        (diagramConnector q p (u, v) * tau q u t *
          (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) * w (t - u)) *
            ∑' y, diagramConnector q (v, t) (r.1 + y, r.2 + y) := by
      unfold diagramMarkedJoiningSecondCore
      simp_rw [hgroup]
    _ ≤ ∑' u, ∑' v, ∑' t,
        ((tau q p.1 u * U (v - p.2)) * tau q u t *
          (∑' z, tau q v z * tau q z u * tau q z t) * w (t - u)) *
            L (t - v - (r.2 - r.1)) := by
      apply ENNReal.tsum_le_tsum
      intro u
      apply ENNReal.tsum_le_tsum
      intro v
      apply ENNReal.tsum_le_tsum
      intro t
      exact mul_le_mul'
        (mul_le_mul' (mul_le_mul' (mul_le_mul' (hfirst u v) le_rfl) (hinner u v t)) le_rfl)
        (tsum_diagramConnector_translate_le_convolution q hq v t r)
    _ = ∑' u, ∑' v, ∑' t, ∑' z,
        tau q p.1 u * U (v - p.2) * tau q v z * tau q z u * tau q z t *
          (w (t - u) * tau q u t) * L (t - v - (r.2 - r.1)) := by
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      apply tsum_congr
      intro t
      simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro z
      ring
    _ = _ := by
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro u
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro s
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro t
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro z
      change tau q p.1 (u + p.1) * U (s + p.1 - p.2) *
        tau q (s + p.1) (z + p.1) * tau q (z + p.1) (u + p.1) *
          tau q (z + p.1) (t + p.1) *
            (w (t + p.1 - (u + p.1)) * tau q (u + p.1) (t + p.1)) *
              L (t + p.1 - (s + p.1) - (r.2 - r.1)) = _
      have hs : s + p.1 - p.2 = s - (p.2 - p.1) := by abel
      rw [tau_eq_rooted_of_add_right q hq p.1 (u + p.1),
        tau_eq_rooted_of_add_right q hq (s + p.1) (z + p.1),
        tau_eq_rooted_of_add_right q hq (z + p.1) (u + p.1),
        tau_eq_rooted_of_add_right q hq (z + p.1) (t + p.1),
        tau_eq_rooted_of_add_right q hq (u + p.1) (t + p.1)]
      simp only [add_sub_add_right_eq_sub, add_sub_cancel_right, hs, L, U, J]

end PercLib.Percolation.Bond.Lace
