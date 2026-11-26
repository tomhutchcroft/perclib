/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterCorrelation.RevealedCluster

/-!
# Revealed clusters: correspondence

Correspondence wrapper for the five-factor bound on the loss of two distinct cluster
connections, from `PercLib/Percolation/Bond/ClusterCorrelation/RevealedCluster.lean` and
`PercLib/Percolation/Bond/ClusterCorrelation/TwoClusterGap.lean`. No new definitions.

## Main results

* `revealed_cluster_identity_and_five_factor_bound`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Five-factor bound for two distinct cluster connections.** Let `x` have an almost surely
finite cluster and put `Q(x,z;y,w) = P(x ↔ z, y ↔ w, x ↮ y)`. Then
`Q(x,z;y,w) = E[1{z ∈ K_x} τ^{K_x}(y,w)]`, where `τ^S(y,w)` is the probability that `y` and `w`
are joined inside `Sᶜ` (zero when an endpoint lies in `S`), and
`0 ≤ τ(x,z) τ(y,w) - Q(x,z;y,w) ≤ ∑_{a,c} τ(x,a) τ(a,z) τ(a,c) τ(y,c) τ(c,w)`, stated in
`ℝ≥0∞` as `Q ≤ τ(x,z) τ(y,w) ≤ Q + ∑_{a,c} …`. The finiteness hypothesis is not needed by the
proof. -/
@[tag "J1LW"]
theorem revealed_cluster_identity_and_five_factor_bound [Countable V]
    (q : Sym2 V → unitInterval) (x : V) (_hfin : ∀ᵐ ω ∂law q, (cluster ω x).Finite)
    (y z w : V) :
    law q (conn x z ∩ conn y w ∩ (conn x y)ᶜ) =
        ∫⁻ ω, {ω : Config V | z ∈ cluster ω x}.indicator
          (fun ω => law q (localConn (cluster ω x)ᶜ y w)) ω ∂law q ∧
      law q (conn x z ∩ conn y w ∩ (conn x y)ᶜ) ≤ tau q x z * tau q y w ∧
      tau q x z * tau q y w ≤ law q (conn x z ∩ conn y w ∩ (conn x y)ᶜ) +
        ∑' a, ∑' c, tau q x a * tau q a z * tau q a c * tau q y c * tau q c w :=
  ⟨law_conn_inter_conn_inter_compl_conn_eq_lintegral q x y z w,
    law_conn_inter_conn_inter_compl_conn_le_mul q x y z w, twoClusterGap q x z y w⟩

end PercLib.Percolation.Bond
