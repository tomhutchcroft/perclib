/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
Cauchy–Schwarz for the positive semidefinite connection kernel, tails of nonnegative sums
and rearrangement of nonnegative sums.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.TriangleComparison

/-!
# Open-triangle decay and the first diagram comparison: correspondence

Wiki correspondence for the decay of `T³` under a uniform diagonal triangle bound and for the
first triangle-diagram comparison, for an arbitrary probability law on configurations of a
countable vertex set. All mathematics is in `PercLib/Percolation/Bond/ConnectionKernel.lean`,
`PercLib/Percolation/Bond/TriangleDecay.lean` and
`PercLib/Percolation/Bond/TriangleComparison.lean`.

## Main results

* `triangle_eventually_lt_and_tendsto_iSup_triangle`
* `triangle_entries_lt_top_and_triangle_weighted_le`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Let `T` be the connection kernel of a probability law on configurations of a countable
vertex set, `T³(x,y) = ∑_{u,v} T(x,u) T(u,v) T(v,y)` and `Δₓ = T³(x,x)`. If
`D = ⨆ x, Δₓ < ∞`, then for every root `o` and every `ε > 0` there is a finite set `E` with
`T³(o,x) < ε` for `x ∉ E`. If bijections of `V` preserving both `T` and a real-valued
function `d` act transitively, then `Δₒ < ∞` at one root already gives
`⨆_{d(u,v) ≥ r} T³(u,v) → 0` as `r → ∞` (the empty supremum being `0`). -/
@[tag "96A2"]
theorem triangle_eventually_lt_and_tendsto_iSup_triangle [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    ((⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) < ⊤ →
      ∀ (o : V) (ε : ℝ≥0∞), 0 < ε → ∃ E : Finset V, ∀ x ∉ E,
        ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v x < ε) ∧
    (∀ d : V → V → ℝ, (∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧
        (∀ a b, connProb μ (σ a) (σ b) = connProb μ a b) ∧ ∀ a b, d (σ a) (σ b) = d a b) →
      ∀ o : V, ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o < ⊤ →
        Tendsto (fun r : ℝ => ⨆ u, ⨆ v, ⨆ (_ : r ≤ d u v),
          ∑' w, ∑' z, connProb μ u w * connProb μ w z * connProb μ z v) atTop (𝓝 0)) :=
  ⟨fun hD o _ hε => exists_finset_triangle_lt μ hD o hε,
    fun d htrans o ho => tendsto_iSup_triangle μ d htrans o ho⟩

/-- Let `T` be the connection kernel of a probability law on configurations of a countable
vertex set, `T²(x,y) = ∑_u T(x,u) T(u,y)`, `T³(x,y) = ∑_{u,w} T(x,u) T(u,w) T(w,y)` and
`Δₓ = T³(x,x)`. Suppose `D = ⨆ x, Δₓ < ∞` and fix a root `o`. Then every entry `T²(o,v)` and
`T³(o,v)` is finite, and `A_o = ∑_v T(o,v) T²(o,v) T³(o,v)` satisfies `A_o ≤ D Δₒ ≤ D²`. If
bijections of `V` preserving `T` act transitively, then `A_o ≤ Δₒ²`. -/
@[tag "C2YT"]
theorem triangle_entries_lt_top_and_triangle_weighted_le [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (hD : (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) < ⊤) (o : V) :
    (∀ v : V, ∑' u, connProb μ o u * connProb μ u v < ⊤ ∧
      ∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v < ⊤) ∧
    ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
        (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
      (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) *
        ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o ∧
    (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) *
        ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o ≤
      (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) ^ 2 ∧
    ((∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ a b, connProb μ (σ a) (σ b) = connProb μ a b) →
      ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
          (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
        (∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o) ^ 2) :=
  ⟨fun v => ⟨connProb_sq_entry_lt_top μ hD o v, triangle_lt_top_of_iSup_lt_top μ hD o v⟩,
    (triangle_weighted_le μ o).1, (triangle_weighted_le μ o).2,
    fun htrans => triangle_weighted_le_sq_of_transitive μ htrans o⟩

end PercLib.Percolation.Bond
