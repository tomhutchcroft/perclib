/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ConnectionKernel

/-!
# Correspondence wrappers for the connection kernel

Tagged restatements of the positivity and triangle bounds for the connection kernel
`T(x,y) = connProb μ x y` of a probability measure `μ` on bond configurations of a countable
vertex set; no independence is assumed. All mathematical inputs are proved in
`PercLib.Percolation.Bond.ConnectionKernel`.

## Main results

* `connProb_quadratic_form_eq_integral_and_nonneg_and_posSemidef`: the quadratic form of `T`
  against a finitely supported real family is the expected sum of squared cluster masses,
  hence nonnegative, and every finite principal submatrix of `T` is positive semidefinite.
* `triangle_le_sqrt_and_lt_top_and_tsum_connProb_sq_le`: finite diagonal triangles `Δₓ, Δ_y`
  give `T³(x,y) ≤ √(Δₓ Δ_y) < ∞`, and `∑ᵤ T(x,u)² ≤ Δₓ` for every `x`.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

open Classical in
/-- For every finitely supported real family `a`,
`∑_{x,y} a_x a_y T(x,y) = E[∑_C (∑_{x ∈ C} a_x)²] ≥ 0`, the sum over the open clusters `C`;
consequently every finite principal submatrix of `T` is positive semidefinite. -/
@[tag "70KD"]
theorem connProb_quadratic_form_eq_integral_and_nonneg_and_posSemidef [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    (∀ a : V →₀ ℝ,
      ∑ x ∈ a.support, ∑ y ∈ a.support, a x * a y * (connProb μ x y).toReal =
          ∫ ω, ∑' C : (openGraph ω).ConnectedComponent,
            (∑ x ∈ a.support with (openGraph ω).connectedComponentMk x = C, a x) ^ 2 ∂μ ∧
        0 ≤ ∑ x ∈ a.support, ∑ y ∈ a.support, a x * a y * (connProb μ x y).toReal) ∧
    ∀ F : Finset V, (Matrix.of fun i j : F => (connProb μ i j).toReal).PosSemidef :=
  ⟨fun a => ⟨sum_finset_mul_connProb_eq_integral μ a.support a,
      sum_finset_mul_connProb_nonneg μ a.support a⟩,
    fun F => posSemidef_connProb μ (fun u : F => (u : V))⟩

/-- With `T³(x,y) = ∑_{u,v} T(x,u) T(u,v) T(v,y)` and `Δₓ = T³(x,x)` as sums in `[0, ∞]`:
if `Δₓ` and `Δ_y` are finite then `T³(x,y) ≤ √(Δₓ Δ_y) < ∞`; and `∑ᵤ T(x,u)² ≤ Δₓ` for
every `x`. -/
@[tag "UZ7J"]
theorem triangle_le_sqrt_and_lt_top_and_tsum_connProb_sq_le [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    (∀ x y : V,
      ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x < ⊤ →
      ∑' u, ∑' v, connProb μ y u * connProb μ u v * connProb μ v y < ⊤ →
      ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v y ≤
          ENNReal.ofReal (Real.sqrt
            ((∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x).toReal *
              (∑' u, ∑' v, connProb μ y u * connProb μ u v * connProb μ v y).toReal)) ∧
        ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v y < ⊤) ∧
    ∀ x : V,
      ∑' u, connProb μ x u ^ 2 ≤ ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x :=
  ⟨fun x y hx hy => ⟨triangle_le_sqrt μ x y hx hy, triangle_lt_top μ x y hx hy⟩,
    tsum_connProb_sq_le_triangle μ⟩

end PercLib.Percolation.Bond
