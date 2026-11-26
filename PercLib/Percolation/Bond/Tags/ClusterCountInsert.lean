/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
the elementary merging argument for components of a finite graph and the monotone product
coupling.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterCountInsert

/-!
# Opening a pair and the expected number of clusters: correspondence

Wiki correspondence for the exact change in the number of clusters when one pair is opened,
and for the comparison of expected cluster counts. All mathematics is in
`PercLib/Percolation/Bond/ClusterCount.lean` and
`PercLib/Percolation/Bond/ClusterCountInsert.lean`.

## Main results

* `card_connectedComponent_insert_and_integral_anti`
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace PercLib.Percolation.Bond

variable {V : Type*}

open scoped Classical in
/-- On a finite vertex set, write `κ(ω)` for the number of open clusters. Opening the pair
`s(a, b)` gives `κ(ω ∪ {ab}) + 1{a ↮ b in ω} = κ(ω)`; consequently `ω ⊆ ω'` implies
`κ(ω') ≤ κ(ω)`. For Bernoulli product profiles with `q ≤ q'`, and more generally with
`q e ≤ q' e` only for non-diagonal pairs `e`, `E_{q'} κ ≤ E_q κ`. -/
@[tag "NW8B"]
theorem card_connectedComponent_insert_and_integral_anti [Fintype V] :
    (∀ (ω : Config V) (a b : V),
      Nat.card (openGraph (insert s(a, b) ω)).ConnectedComponent +
          (if (openGraph ω).Reachable a b then 0 else 1) =
        Nat.card (openGraph ω).ConnectedComponent) ∧
    (∀ ω ω' : Config V, ω ⊆ ω' →
      Nat.card (openGraph ω').ConnectedComponent ≤ Nat.card (openGraph ω).ConnectedComponent) ∧
    (∀ q q' : Sym2 V → unitInterval, q ≤ q' →
      ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q' ≤
        ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q) ∧
    (∀ q q' : Sym2 V → unitInterval, (∀ e, ¬ e.IsDiag → q e ≤ q' e) →
      ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q' ≤
        ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q) :=
  ⟨fun ω a b => card_connectedComponent_insert ω a b, fun _ _ h => card_connectedComponent_anti h,
    fun _ _ h => integral_card_connectedComponent_anti h,
    fun _ _ h => integral_card_connectedComponent_anti_of_offDiagonal h⟩

end PercLib.Percolation.Bond
