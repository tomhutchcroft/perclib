/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference: the
second triangle-diagram comparison through positivity of `T ⊙ T³ - T² ⊙ T²` and the invariant
trace given by mass transport.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.TriangleInvariant

/-!
# The second triangle-diagram comparison: correspondence

Wiki correspondence for the comparison `B ≤ A ≤ Δ²` of the triangle diagrams, for a connection
kernel invariant under a transitive action with the mass-transport property and for a
connection kernel on a countable group invariant under left multiplication. All mathematics is
in `PercLib/Percolation/Bond/TriangleInvariant.lean`.

## Main results

* `triangle_cube_le_weighted_le_sq_of_hasMassTransport`
* `triangle_cube_le_weighted_le_sq_of_group`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Let a group `Γ` act transitively on the countable vertex set `V` with the mass-transport
property, and let the connection kernel `T` be invariant, `T(g x, g y) = T(x, y)`. With
`T²(x,y) = ∑_u T(x,u) T(u,y)`, `T³(x,y) = ∑_{u,w} T(x,u) T(u,w) T(w,y)`, `Δ = T³(o,o)`,
`A = ∑_v T(o,v) T²(o,v) T³(o,v)` and `B = ∑_v T²(o,v)³` (sums in `[0, ∞]`; `T²` is symmetric),
one has `B ≤ A ≤ Δ²`. The finite-susceptibility hypothesis of the assertion is carried but
not used by the proof. -/
@[tag "IZAO"]
theorem triangle_cube_le_weighted_le_sq_of_hasMassTransport [Countable V] {Γ : Type*}
    [Group Γ] [MulAction Γ V] [MulAction.IsPretransitive Γ V] (μ : Measure (Config V))
    [IsProbabilityMeasure μ] (hMT : HasMassTransport Γ V)
    (hinv : ∀ (g : Γ) (x y : V), connProb μ (g • x) (g • y) = connProb μ x y) (o : V)
    (_hχ : ∑' v, connProb μ o v < ∞) :
    ∑' v, (∑' u, connProb μ o u * connProb μ u v) ^ 3 ≤
        ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
          (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ∧
      ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
          (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
        (∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o) ^ 2 :=
  ⟨tsum_connProb_sq_entry_pow_three_le_triangle_weighted μ hMT hinv o,
    triangle_weighted_le_sq_of_isPretransitive μ hinv o⟩

/-- Let the vertex set be a countable group `G` and the connection kernel be invariant under
simultaneous left translation, `T(g x, g y) = T(x, y)`. With `A_o = ∑_v T(o,v) T²(o,v) T³(o,v)`,
`B_o = ∑_v T²(o,v)³` and `Δ_o = T³(o,o)` (sums in `[0, ∞]`), one has `B_o ≤ A_o ≤ Δ_o²`. The
finite-susceptibility hypothesis of the assertion is carried but not used by the proof. -/
@[tag "87W3"]
theorem triangle_cube_le_weighted_le_sq_of_group {G : Type*} [Group G] [Countable G]
    (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (hinv : ∀ g x y : G, connProb μ (g * x) (g * y) = connProb μ x y) (o : G)
    (_hχ : ∑' v, connProb μ o v < ∞) :
    ∑' v, (∑' u, connProb μ o u * connProb μ u v) ^ 3 ≤
        ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
          (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ∧
      ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
          (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
        (∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o) ^ 2 :=
  ⟨tsum_connProb_sq_entry_pow_three_le_triangle_weighted_of_group μ hinv o,
    triangle_weighted_le_sq_of_group μ hinv o⟩

end PercLib.Percolation.Bond
