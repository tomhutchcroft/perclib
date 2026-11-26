/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the consistent choice of geodesics on the lattice. All mathematical
inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ConsistentGeodesics

/-!
# Consistent geodesics: correspondence

Wiki correspondence for the translation-equivariant choice of shortest paths on `ℤ^d` that is
consistent under restriction to subgraphs.

## Main results

* `exists_consistent_geodesics_int`
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace PercLib.Percolation.Bond

/-- For graphs `H` on `ℤ^d` (vertices outside the graph's vertex subset are isolated), a
shortest path `γ H u v`, given by its vertex list, can be chosen for every connected pair so
that the choice is translation-equivariant, measurable in the open graph of a bond
configuration, and unchanged on a subgraph `H' ≤ H` that contains all edges of
`γ H u v`. -/
@[tag "BN7Z"]
theorem exists_consistent_geodesics_int (d : ℕ) :
    ∃ γ : SimpleGraph (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → List (Fin d → ℤ),
      (∀ (H : SimpleGraph (Fin d → ℤ)) (u v : Fin d → ℤ), H.Reachable u v →
        ∃ p : H.Walk u v, p.IsPath ∧ p.length = H.dist u v ∧ p.support = γ H u v) ∧
      (∀ (H : SimpleGraph (Fin d → ℤ)) (a u v : Fin d → ℤ),
        γ (H.map (Equiv.addLeft a).toEmbedding) (a + u) (a + v) = (γ H u v).map (a + ·)) ∧
      (∀ (H H' : SimpleGraph (Fin d → ℤ)) (u v : Fin d → ℤ), H' ≤ H →
        (γ H u v).IsChain H'.Adj → γ H' u v = γ H u v) ∧
      (∀ (u v : Fin d → ℤ) (l : List (Fin d → ℤ)),
        MeasurableSet {ω : Config (Fin d → ℤ) | γ (openGraph ω) u v = l}) :=
  exists_consistent_geodesics

end PercLib.Percolation.Bond
