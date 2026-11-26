/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the small-set formulas and the covariance of the recursive
three-part distance `S(A)` (T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, §I.2). All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Multipoint.Sweep

/-!
# The three-part distance on small sets and its covariance: correspondence

Wiki correspondence for the explicit three- and four-point values of the recursive three-part
distance `S = threePartDistance` on `ℝ^n` with the Euclidean norm, its covariance under maps
that scale squared distances by `l x l y`, and its scaling under similarities.

## Main results

* `threePartDistance_small_sets_and_covariance`
-/

@[expose] public section
noncomputable section
open Finset

namespace PercLib.Percolation.Bond

open Classical in
/-- In `ℝ^n` with the Euclidean norm: (i) `S({x, y, z}) = ‖x - y‖ ‖y - z‖ ‖z - x‖` for distinct
points; (ii) for distinct `a, b, c, d`, `S({a, b, c, d})` is the minimum over the three unordered
pairings `{u, v} ⊔ {w, z}` of `‖u - v‖ ‖w - z‖ √(‖u - w‖ ‖u - z‖ ‖v - w‖ ‖v - z‖)`; (iii) if `φ`
is injective on `A`, `l > 0` on `A` and `‖φ x - φ y‖² = l x l y ‖x - y‖²` on `A`, then
`S(φ(A)) = S(A) ∏_{x ∈ A} l x`; (iv) for a similarity `φ x = c U x + v` with `c > 0` and `U` a
linear isometry, `S(φ(A)) = c^{|A|} S(A)`. -/
@[tag "9YE6"]
theorem threePartDistance_small_sets_and_covariance (n : ℕ) :
    (∀ x y z : EuclideanSpace ℝ (Fin n), x ≠ y → y ≠ z → x ≠ z →
      threePartDistance ({x, y, z} : Finset _) = ‖x - y‖ * ‖y - z‖ * ‖z - x‖) ∧
    (∀ a b c d : EuclideanSpace ℝ (Fin n), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      threePartDistance ({a, b, c, d} : Finset _) =
        min (min (‖a - b‖ * ‖c - d‖ * Real.sqrt (‖a - c‖ * ‖a - d‖ * ‖b - c‖ * ‖b - d‖))
          (‖a - c‖ * ‖b - d‖ * Real.sqrt (‖a - b‖ * ‖a - d‖ * ‖c - b‖ * ‖c - d‖)))
          (‖a - d‖ * ‖b - c‖ * Real.sqrt (‖a - b‖ * ‖a - c‖ * ‖d - b‖ * ‖d - c‖))) ∧
    (∀ (A : Finset (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)) (l : EuclideanSpace ℝ (Fin n) → ℝ),
      Set.InjOn φ A → (∀ x ∈ A, 0 < l x) →
      (∀ x ∈ A, ∀ y ∈ A, ‖φ x - φ y‖ ^ 2 = l x * l y * ‖x - y‖ ^ 2) →
      threePartDistance (A.image φ) = threePartDistance A * ∏ x ∈ A, l x) ∧
    (∀ (A : Finset (EuclideanSpace ℝ (Fin n))) (c : ℝ)
        (U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (v : EuclideanSpace ℝ (Fin n)), 0 < c →
      threePartDistance (A.image fun x => c • U x + v) = c ^ A.card * threePartDistance A) := by
  refine ⟨fun x y z hxy hyz hxz => ?_, fun a b c d hab hac had hbc hbd hcd => ?_,
    fun A φ l hinj hl hφ => ?_, fun A c U v hc => ?_⟩
  · simpa only [dist_eq_norm] using threePartDistance_triple hxy hyz hxz
  · simpa only [dist_eq_norm] using threePartDistance_quad hab hac had hbc hbd hcd
  · exact threePartDistance_image_eq_mul_prod hl hinj fun x hx y hy => by
      simpa only [dist_eq_norm] using hφ x hx y hy
  · exact threePartDistance_image_smul_linearIsometry_add hc U v A

end PercLib.Percolation.Bond
