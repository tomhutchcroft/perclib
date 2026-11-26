/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.HarrisLocal

/-! Correspondence wrappers for exhaustion by induced domains and the local Harris corollary.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Along an increasing sequence of domains covering `V`, the internal clusters increase to
the cluster with volume the supremum; on countable `V` the susceptibility is the supremum of
the internal expected volumes; escape probabilities are the suprema of internal escape
probabilities. -/
@[tag "6QN7"]
theorem induced_domains_recover_cluster (q : Sym2 V → unitInterval) {S : ℕ → Set V}
    (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (x : V) :
    (∀ ω : Config V, Monotone fun n => localCluster ω (S n) x) ∧
    (∀ ω : Config V, (⋃ n, localCluster ω (S n) x) = cluster ω x) ∧
    (∀ ω : Config V, (cluster ω x).encard = ⨆ n, (localCluster ω (S n) x : Set V).encard) ∧
    (Countable V → chi q x = ⨆ n, ∫⁻ ω, ((localCluster ω (S n) x : Set V).encard : ℝ≥0∞)
        ∂law q) ∧
    (∀ F : Set V, law q (⋃ y ∈ Fᶜ, conn x y) = ⨆ n, law q {ω | ∃ y ∉ F,
      y ∈ localCluster ω (S n) x}) :=
  ⟨fun ω => monotone_induce_cluster hS ω x, fun ω => iUnion_induce_cluster hS hcover ω x,
    fun ω => encard_cluster_eq_iSup_induce hS hcover ω x,
    fun _ => chi_eq_iSup_lintegral_induce q hS hcover x,
    fun F => escape_eq_iSup_induce q hS hcover x F⟩

/-- Harris's inequality for a connection and an escape event inside a domain `S`, and its
full-graph form. -/
@[tag "EWMP"]
theorem harris_connection_escape_local [Countable V] (q : Sym2 V → unitInterval)
    (S : Set V) (F : Set V) :
    (∀ x y : S,
      law q {ω | ((openGraph ω).induce S).Reachable x y} *
          law q {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable y w} ≤
        law q {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable x w}) ∧
    (∀ x y : V, tau q x y * law q (⋃ w ∈ Fᶜ, conn y w) ≤ law q (⋃ w ∈ Fᶜ, conn x w)) :=
  ⟨fun x y => law_localConn_mul_localEscape_le q S x y F,
    fun x y => tau_mul_law_escape_le q x y F⟩

end PercLib.Percolation.Bond
