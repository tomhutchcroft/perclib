/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the lazy-walk threshold assertion E9BP, proved from
`LazyWalkThresholds.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.LazyWalkThresholds

/-!
# Green, bubble and triangle thresholds for lazy walk: correspondence

Wiki correspondence for the Green, bubble and triangle thresholds of lazy nearest-neighbour
walk on `ℤ^d`, from `PercLib/Analysis/LazyWalkThresholds.lean`.

## Main results

* `lazyWalk_green_bubble_triangle_thresholds`
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Analysis

open Classical in
/-- **E9BP.** Let `p` be the lazy nearest-neighbour step distribution on `ℤ^d` (`d ≥ 1`):
`p(0) = 1/2` and `p(±eⱼ) = 1/(4d)` for each of the `2d` unit vectors. With the convolution
powers `P⁰ = δ₀`, `Pⁿ⁺¹(z) = ∑_y Pⁿ(y) p(z - y)` and the Green function
`G(u) = ∑ₙ Pⁿ(0,u)` in `ℝ≥0∞`, the bubble `B = ∑ᵤ G(u)²` and the triangle
`T = ∑ᵤ,ᵥ G(u) G(v - u) G(v)` (extended sums):
`G(0) < ∞ ↔ d > 2`, `B < ∞ ↔ d > 4` and `T < ∞ ↔ d > 6`. -/
@[tag "E9BP"]
theorem lazyWalk_green_bubble_triangle_thresholds {d : ℕ} (hd : 0 < d)
    (p : (Fin d → ℤ) → ℝ≥0∞)
    (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (G : (Fin d → ℤ) → ℝ≥0∞)
    (hG : ∀ u, G u = ∑' n, (Nat.rec (fun z => if z = 0 then 1 else 0)
      (fun _ ν z => ∑' y, ν y * p (z - y)) n : (Fin d → ℤ) → ℝ≥0∞) u) :
    (G 0 < ∞ ↔ 2 < d) ∧ (∑' u, G u ^ 2 < ∞ ↔ 4 < d) ∧
      (∑' u, ∑' v, G u * G (v - u) * G v < ∞ ↔ 6 < d) := by
  set P : ℕ → (Fin d → ℤ) → ℝ≥0∞ := fun n => Nat.rec (fun z => if z = 0 then 1 else 0)
    (fun _ ν z => ∑' y, ν y * p (z - y)) n with hP
  have h0 : ∀ z, P 0 z = if z = 0 then 1 else 0 := fun z => rfl
  have hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z) := fun n z =>
    tsum_congr fun y => by rw [sub_eq_neg_add]
  have hGP : G = fun u => ∑' n, P n u := funext hG
  subst hGP
  exact ⟨lazyWalk_green_lt_top_iff hd hp h0 hs, lazyWalk_bubble_lt_top_iff hd hp h0 hs,
    lazyWalk_triangle_lt_top_iff hd hp h0 hs⟩

end PercLib.Analysis
