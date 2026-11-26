/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
This is the through-set expansion step of Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2.
-/
module

public import PercLib.Percolation.Bond.Lace.InitialExpansion

/-!
# Expanding a connection through a fixed vertex set

## Main results

The through-set partition and cutting-bond factorization give the exact
nonnegative identity used at every later stage of the lace expansion. The
residual event keeps `E'` in the current layer and tests a through-set connection
against its deleted cluster in a fresh independent layer.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- A measurable first-layer event can be retained while a second-layer
connection is split according to the first layer's deleted cluster. -/
theorem prod_event_tau_eq_avoiding_add_through [Countable V]
    (q : Sym2 V → unitInterval) (E : Set (Config V)) (hE : MeasurableSet E)
    (x y u v : V) :
    law q E * tau q v y =
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ E ∧
        ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
          ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
            ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
              ⟨v, hv⟩ ⟨y, hy⟩} +
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ E ∧ p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y} := by
  classical
  let B : Set (Config V × Config V) := {p | p.1 ∈ E ∧
    ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
      ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
        ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
          ⟨v, hv⟩ ⟨y, hy⟩}
  let T : Set (Config V × Config V) := {p | p.1 ∈ E ∧
    p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y}
  have hmT : MeasurableSet T := (hE.preimage measurable_fst).inter
    (measurableSet_throughSet_of_measurable
      ((measurable_deleted_cluster s(u, v) x).comp measurable_fst) measurable_snd v y)
  have hD : Disjoint B T := Set.disjoint_left.mpr fun _ hb ht => ht.2.2 hb.2
  have hdec : E ×ˢ conn v y = B ∪ T := by
    ext p
    constructor
    · rintro ⟨he, hc⟩
      by_cases ha : ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
          ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
            ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
              ⟨v, hv⟩ ⟨y, hy⟩
      · exact Or.inl ⟨he, ha⟩
      · exact Or.inr ⟨he, hc, ha⟩
    · rintro (⟨he, hv, hy, hc⟩ | ⟨he, ht⟩)
      · exact ⟨he, conn_of_localConn _ _ _ _ hc⟩
      · exact ⟨he, ht.1⟩
  change law q E * law q (conn v y) = _
  rw [← Measure.prod_prod, hdec, measure_union hD hmT]

/-- Exact one-pair expansion with an arbitrary fixed through-set. -/
theorem cuttingEvent_add_through_remainder_eq_step [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y u v : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (cuttingEvent A x y u v) +
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        ((law q).prod (law q)) {p : Config V × Config V |
          p.1 ∈ laceEPrime A x u ∧
          p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y} =
      law q (laceEPrime A x u) *
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y := by
  classical
  by_cases huv : u = v
  · subst v
    simp [cuttingEvent_diag, offDiagonal_self]
  · simp only [offDiagonal_apply, Ne.symm huv, ite_false]
    rw [law_cuttingEvent_eq_prod_laceEPrime q A x y u v hfin, ← mul_add,
      ← prod_event_tau_eq_avoiding_add_through q (laceEPrime A x u)
        (measurableSet_laceEPrime A x u) x y u v]
    ac_rfl

/-- The exact through-set expansion step. This identity is pointwise in the
vertex set `A`, so earlier independent layers can subsequently be integrated.
All terms are nonnegative, and no finite-sum assumption is needed. -/
theorem law_throughSet_add_remainder_eq_laceEPrime_add_step [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y : V)
    (hfin : ∀ u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (throughSet A x y) +
      (∑' u, ∑' v,
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          ((law q).prod (law q)) {p : Config V × Config V |
            p.1 ∈ laceEPrime A x u ∧
            p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y}) =
      law q (laceEPrime A x y) +
        ∑' u, ∑' v, law q (laceEPrime A x u) *
          offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y := by
  classical
  rw [law_throughSet_eq_add_tsum_cuttingEvent, add_assoc, ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro u
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun v => cuttingEvent_add_through_remainder_eq_step q A x y u v (hfin u v)

end PercLib.Percolation.Bond.Lace
