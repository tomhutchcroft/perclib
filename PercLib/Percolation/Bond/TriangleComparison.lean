/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
Cauchy–Schwarz for the positive semidefinite connection kernel and rearrangement of
nonnegative sums.
-/
module

public import PercLib.Percolation.Bond.TriangleDecay

/-!
# Finiteness of the kernel powers and the transitive triangle comparison

For a probability law on configurations, write `T(x,y)` for the connection probability,
`T²(x,y) = ∑_u T(x,u) T(u,y)`, `T³(x,y) = ∑_{u,w} T(x,u) T(u,w) T(w,y)`, `Δₓ = T³(x,x)` and
`D = ⨆ x, Δₓ`. Keeping the term `w = y` in `T³` shows `T² ≤ T³` (because `T(y,y) = 1`), and
Cauchy–Schwarz gives `T³(x,y) ≤ D`. Hence every entry of `T²` and `T³` is finite when
`D < ∞`. If bijections preserving `T` act transitively, `Δ` is constant, so the weighted
triangle `∑_v T(o,v) T²(o,v) T³(o,v)` is at most `Δₒ²`.

## Main results

* `connProb_sq_entry_le_triangle`: `T²(x,y) ≤ T³(x,y)`.
* `triangle_le_iSup_triangle`: `T³(x,y) ≤ D`.
* `connProb_sq_entry_lt_top`, `triangle_lt_top_of_iSup_lt_top`: finiteness of the entries
  when `D < ∞`.
* `triangle_diag_eq_of_transitive`: `Δₓ = Δₒ` under a transitive kernel-preserving action.
* `triangle_weighted_le_sq_of_transitive`: the weighted triangle is at most `Δₒ²`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **`T² ≤ T³` entrywise**, keeping the term `w = y` of the cubic sum (`T(y,y) = 1`). -/
theorem connProb_sq_entry_le_triangle (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (x y : V) :
    ∑' u, connProb μ x u * connProb μ u y ≤
      ∑' u, ∑' w, connProb μ x u * connProb μ u w * connProb μ w y := by
  refine ENNReal.tsum_le_tsum fun u => ?_
  calc connProb μ x u * connProb μ u y = connProb μ x u * connProb μ u y * connProb μ y y := by
        rw [connProb_self, mul_one]
    _ ≤ ∑' w, connProb μ x u * connProb μ u w * connProb μ w y :=
        ENNReal.le_tsum (f := fun w => connProb μ x u * connProb μ u w * connProb μ w y) y

/-- **`T³(x,y) ≤ D`**, from `T³(x,y) ≤ (Δₓ Δ_y)^{1/2}`. -/
theorem triangle_le_iSup_triangle [Countable V] (μ : Measure (Config V)) [IsFiniteMeasure μ]
    (x y : V) :
    ∑' u, ∑' w, connProb μ x u * connProb μ u w * connProb μ w y ≤
      ⨆ z, ∑' u, ∑' v, connProb μ z u * connProb μ u v * connProb μ v z := by
  set Δ : V → ℝ≥0∞ := fun z => ∑' u, ∑' v, connProb μ z u * connProb μ u v * connProb μ v z
  set D := ⨆ z, Δ z
  have hΔD : ∀ z, Δ z ≤ D := fun z => le_iSup Δ z
  have hDD : (D * D) ^ (1 / 2 : ℝ) = D := by
    have := ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) D
    simpa [one_div, sq] using this
  calc _ ≤ (Δ x * Δ y) ^ (1 / 2 : ℝ) := triangle_le_rpow μ x y
    _ ≤ (D * D) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul' (hΔD x) (hΔD y)) (by norm_num)
    _ = D := hDD

/-- Every entry of `T³` is finite when `D < ∞`. -/
theorem triangle_lt_top_of_iSup_lt_top [Countable V] (μ : Measure (Config V)) [IsFiniteMeasure μ]
    (hD : (⨆ z, ∑' u, ∑' v, connProb μ z u * connProb μ u v * connProb μ v z) < ⊤) (x y : V) :
    ∑' u, ∑' w, connProb μ x u * connProb μ u w * connProb μ w y < ⊤ :=
  (triangle_le_iSup_triangle μ x y).trans_lt hD

/-- Every entry of `T²` is finite when `D < ∞`. -/
theorem connProb_sq_entry_lt_top [Countable V] (μ : Measure (Config V))
    [IsProbabilityMeasure μ]
    (hD : (⨆ z, ∑' u, ∑' v, connProb μ z u * connProb μ u v * connProb μ v z) < ⊤) (x y : V) :
    ∑' u, connProb μ x u * connProb μ u y < ⊤ :=
  (connProb_sq_entry_le_triangle μ x y).trans_lt (triangle_lt_top_of_iSup_lt_top μ hD x y)

/-- Under a transitive family of kernel-preserving bijections, `Δₓ = Δₒ` for every `x`. -/
theorem triangle_diag_eq_of_transitive (μ : Measure (Config V))
    (htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ a b, connProb μ (σ a) (σ b) = connProb μ a b)
    (o x : V) :
    ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x =
      ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o := by
  obtain ⟨σ, hσx, hσq⟩ := htrans o x
  rw [← hσx, triangle_map_eq μ σ hσq]

/-- Under a transitive family of kernel-preserving bijections, `D = Δₒ`. -/
theorem iSup_triangle_eq_of_transitive (μ : Measure (Config V))
    (htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ a b, connProb μ (σ a) (σ b) = connProb μ a b)
    (o : V) :
    (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) =
      ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o := by
  simp_rw [triangle_diag_eq_of_transitive μ htrans o]
  exact ciSup_const (hι := ⟨o⟩)

/-- **Transitive weighted triangle.** Under a transitive family of kernel-preserving
bijections, `∑_v T(o,v) T²(o,v) T³(o,v) ≤ Δₒ²`. -/
theorem triangle_weighted_le_sq_of_transitive [Countable V] (μ : Measure (Config V))
    [IsFiniteMeasure μ]
    (htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ a b, connProb μ (σ a) (σ b) = connProb μ a b)
    (o : V) :
    ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
        (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
      (∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o) ^ 2 := by
  have h := triangle_weighted_le μ o
  rw [iSup_triangle_eq_of_transitive μ htrans o] at h
  exact h.1.trans h.2

end PercLib.Percolation.Bond
