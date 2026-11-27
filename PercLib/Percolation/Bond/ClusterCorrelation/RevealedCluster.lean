/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Conditioning on the revealed cluster of a vertex, for an independent bond profile on a countable
vertex set. Reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
proof of Lemma I.4.12 (the restoration coupling of `ClusterCorrelation/Defs.lean`).
-/
module

public import PercLib.Percolation.Bond.ClusterCorrelation.CovarianceGap
public import PercLib.Percolation.Bond.ClusterCorrelation.TwoClusterGap

/-!
# Connections off a revealed cluster

For an independent bond profile `q` on a countable vertex set, write `K_x` for the open cluster
of `x` and `τ^S(y, w) = P(y ↔ w inside V \ S)` (zero when an endpoint lies in `S`). Revealing
`K_x` leaves the pairs with no endpoint in `K_x` with their product law, so

`P(x ↔ z, y ↔ w, x ↮ y) = E[1{z ∈ K_x} τ^{K_x}(y, w)]`.

The proof uses the restoration map `restoreMap x` of `ClusterCorrelation/Defs.lean`, which
pushes `law q ⊗ law q` to `law q`, keeps the cluster of `x` of its first argument and equals its
second argument off that cluster. No finiteness of `K_x` is needed.

## Main results

* `restoreMap_mem_conn_iff_of_notMem`: off the revealed cluster, connections of the restored
  configuration are internal connections of the second argument.
* `law_conn_inter_conn_inter_compl_conn_eq_lintegral`: the expectation identity above.
* `law_conn_inter_conn_inter_compl_conn_le_mul`: `P(x ↔ z, y ↔ w, x ↮ y) ≤ τ(x, z) τ(y, w)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Internal connections off the cluster `K_o(ω)` are the same in the restored configuration
and in `ω'`. -/
theorem restoreMap_mem_localConn_compl_iff (o : V) (p : Config V × Config V) (y w : V) :
    restoreMap o p ∈ localConn (cluster p.1 o)ᶜ y w ↔
      p.2 ∈ localConn (cluster p.1 o)ᶜ y w := by
  have hag : ∀ a ∈ (cluster p.1 o)ᶜ, ∀ b ∈ (cluster p.1 o)ᶜ,
      (s(a, b) ∈ restoreMap o p ↔ s(a, b) ∈ p.2) := by
    intro a ha b hb
    have hn : ¬∃ v ∈ s(a, b), v ∈ cluster p.1 o := by
      rintro ⟨v, hv, hvS⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      exacts [ha hvS, hb hvS]
    exact mem_restoreMap_of_not_touch hn
  simp only [mem_localConn]
  constructor
  · rintro ⟨hy, hw, h⟩
    exact ⟨hy, hw, (localConn_iff_of_agree _ _ _ hag).1 h⟩
  · rintro ⟨hy, hw, h⟩
    exact ⟨hy, hw, (localConn_iff_of_agree _ _ _ hag).2 h⟩

/-- If `y ∉ K_o(ω)`, then `y ↔ w` in the restored configuration exactly when `y` and `w` are
joined in `ω'` by an open path avoiding `K_o(ω)`. -/
theorem restoreMap_mem_conn_iff_of_notMem {o y : V} {p : Config V × Config V}
    (hy : y ∉ cluster p.1 o) (w : V) :
    restoreMap o p ∈ conn y w ↔ p.2 ∈ localConn (cluster p.1 o)ᶜ y w := by
  classical
  rw [← restoreMap_mem_localConn_compl_iff]
  refine ⟨fun h => ?_, fun h => localConn_subset_conn _ _ _ h⟩
  obtain ⟨W⟩ := h
  have hW : ∀ v ∈ W.support, v ∈ (cluster p.1 o)ᶜ := fun v hv =>
    (cluster_restoreMap_subset_snd hy (show v ∈ cluster (restoreMap o p) y from
      ⟨W.takeUntil v hv⟩)).2
  exact ⟨hW _ W.start_mem_support, hW _ W.end_mem_support, ⟨W.induce _ hW⟩⟩

/-- **Connections off a revealed cluster.** For every profile on a countable vertex type,
`P(x ↔ z, y ↔ w, x ↮ y) = E[1{z ∈ K_x} τ^{K_x}(y, w)]`, where `τ^S(y, w)` is the probability
that `y` and `w` are joined inside `Sᶜ` (zero if `y ∈ S` or `w ∈ S`). -/
theorem law_conn_inter_conn_inter_compl_conn_eq_lintegral [Countable V]
    (q : Sym2 V → unitInterval) (x y z w : V) :
    law q (conn x z ∩ conn y w ∩ (conn x y)ᶜ) =
      ∫⁻ ω, {ω : Config V | z ∈ cluster ω x}.indicator
        (fun ω => law q (localConn (cluster ω x)ᶜ y w)) ω ∂law q := by
  set E : Set (Config V) := conn x z ∩ conn y w ∩ (conn x y)ᶜ with hEdef
  have hE : MeasurableSet E :=
    ((measurableSet_conn x z).inter (measurableSet_conn y w)).inter
      (measurableSet_conn x y).compl
  calc law q E = ((law q).prod (law q)) (restoreMap x ⁻¹' E) := by
        rw [← Measure.map_apply (measurable_restoreMap x) hE, map_restoreMap]
    _ = ∫⁻ ω, law q (Prod.mk ω ⁻¹' (restoreMap x ⁻¹' E)) ∂law q :=
        Measure.prod_apply (measurable_restoreMap x hE)
    _ = _ := lintegral_congr fun ω => ?_
  have hsec : Prod.mk ω ⁻¹' (restoreMap x ⁻¹' E) =
      {ω' | z ∈ cluster ω x ∧ ω' ∈ localConn (cluster ω x)ᶜ y w} := by
    ext ω'
    have hc := cluster_restoreMap x (ω, ω')
    have hz : restoreMap x (ω, ω') ∈ conn x z ↔ z ∈ cluster ω x := by
      change z ∈ cluster (restoreMap x (ω, ω')) x ↔ _
      rw [hc]
    have hyc : restoreMap x (ω, ω') ∈ conn x y ↔ y ∈ cluster ω x := by
      change y ∈ cluster (restoreMap x (ω, ω')) x ↔ _
      rw [hc]
    simp only [hEdef, mem_preimage, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, hz, hyc]
    by_cases hy : y ∈ cluster ω x
    · simp [hy, localConn_of_notMem (show y ∉ (cluster ω x)ᶜ from fun h => h hy)]
    · rw [restoreMap_mem_conn_iff_of_notMem (p := (ω, ω')) hy w]
      simp [hy]
  rw [hsec]
  by_cases hz : z ∈ cluster ω x
  · rw [indicator_of_mem (show ω ∈ {ω : Config V | z ∈ cluster ω x} from hz)]
    simp only [hz, true_and, ofPred_mem_eq]
  · simp [hz]

/-- On `{x ↮ y}`, the connections `x ↔ z` and `y ↔ w` are negatively correlated:
`P(x ↔ z, y ↔ w, x ↮ y) ≤ τ(x, z) τ(y, w)`. -/
theorem law_conn_inter_conn_inter_compl_conn_le_mul [Countable V] (q : Sym2 V → unitInterval)
    (x y z w : V) :
    law q (conn x z ∩ conn y w ∩ (conn x y)ᶜ) ≤ tau q x z * tau q y w :=
  law_inter_inter_compl_conn_le_mul q (measurableSet_conn x z) (measurableSet_conn y w)
    (fun ω ω' h => by change z ∈ cluster ω x ↔ z ∈ cluster ω' x; rw [h])
    (isUpperSet_conn y w)
    (fun ω ω' h => by change w ∈ cluster ω y ↔ w ∈ cluster ω' y; rw [h])

end PercLib.Percolation.Bond
