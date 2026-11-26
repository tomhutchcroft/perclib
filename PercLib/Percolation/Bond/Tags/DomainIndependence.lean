/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for independence of percolation on disjoint vertex domains.
All mathematical inputs are proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.DomainIndependence

/-!
# Independence on disjoint vertex domains: statement form

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `law_disjoint_domains_independent`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Measurable events determined by the internal pairs of finitely many pairwise disjoint
vertex domains are mutually independent. Internal connection events of a countable domain
are measurable and determined by its internal pairs, and those of two disjoint countable
domains are independent. -/
@[tag "RDX7"]
theorem law_disjoint_domains_independent (q : Sym2 V → unitInterval) :
    (∀ (n : ℕ) (S : Fin n → Set V) (A : Fin n → Set (Config V)),
      Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ i, MeasurableSet (A i)) →
      (∀ i, ∀ ω ω' : Config V,
        ω ∩ {e | ∀ v ∈ e, v ∈ S i} = ω' ∩ {e | ∀ v ∈ e, v ∈ S i} → (ω ∈ A i ↔ ω' ∈ A i)) →
      law q (⋂ i, A i) = ∏ i, law q (A i)) ∧
    (∀ (S : Set V) [Countable S] (x y : S),
      MeasurableSet {ω : Config V | ((openGraph ω).induce S).Reachable x y} ∧
      ∀ ω ω' : Config V, ω ∩ {e | ∀ v ∈ e, v ∈ S} = ω' ∩ {e | ∀ v ∈ e, v ∈ S} →
        (ω ∈ {ω : Config V | ((openGraph ω).induce S).Reachable x y} ↔
          ω' ∈ {ω : Config V | ((openGraph ω).induce S).Reachable x y})) ∧
    (∀ (S T : Set V) [Countable S] [Countable T], Disjoint S T → ∀ (x y : S) (u v : T),
      law q {ω | ((openGraph ω).induce S).Reachable x y ∧
          ((openGraph ω).induce T).Reachable u v} =
        law q {ω | ((openGraph ω).induce S).Reachable x y} *
          law q {ω | ((openGraph ω).induce T).Reachable u v}) :=
  ⟨fun _ _ _ hS hAm hA => law_iInter_fin_of_determined_internalPairs q hS hAm hA,
    fun S _ x y => ⟨measurableSet_setOf_reachable_induce S x y, localConn_determined S x y⟩,
    fun _ _ _ _ hST x y u v => law_localConn_inter_eq_mul q hST x y u v⟩

end PercLib.Percolation.Bond
