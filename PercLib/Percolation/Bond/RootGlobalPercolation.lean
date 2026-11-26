/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, from the zero-one law, root-independence and transport
theorems of this library. No upstream proof is copied. Mathematical reference: the standard
argument from the Kolmogorov zero-one law and countable subadditivity.
-/
module

public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.ZeroOne

/-! # Root and global percolation

Write `θ(x) = law q {ω | (cluster ω x).Infinite}` and `I = {ω | ∃ x, (cluster ω x).Infinite}`.
On a countable vertex set, `law q I` is `0` or `1`, and it is positive exactly when some
`θ(x)` is. Under transitivity of the law all `θ(x)` agree, so each of these is equivalent to
`θ(o) > 0` for any fixed root `o`.

Transitivity is stated in law form, for every pair of vertices:
`∀ x y, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q`.
This is the all-pairs spelling (as for `chi_eq_of_transitive`), with the profile invariance
replaced by invariance of the law; the profile form is a corollary.

## Main results

* `law_exists_cluster_infinite_eq_one_iff_pos`: `law q I = 1 ↔ 0 < law q I`.
* `law_exists_cluster_infinite_eq_one_iff`: `law q I = 1 ↔ ∃ x, 0 < θ(x)`.
* `law_cluster_infinite_eq_of_transitive_law`: under transitivity, `θ(x) = θ(y)`.
* `law_exists_cluster_infinite_pos_iff_of_transitive_law` and
  `law_exists_cluster_infinite_eq_one_iff_of_transitive_law`: under transitivity,
  `0 < law q I ↔ 0 < θ(o)` and `law q I = 1 ↔ 0 < θ(o)`.
* `setOf_law_cluster_infinite_pos_eq_of_transitive_law`,
  `setOf_law_cluster_infinite_pos_eq_setOf_eq_one_of_transitive_law` and the `sInf` forms:
  for a family of transitive laws the three parameter sets coincide, and so do their infima.
* `law_exists_cluster_infinite_eq_one_iff_of_transitive`: the corollary for a transitive
  profile.

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Countable models -/

/-- On a countable vertex set an infinite cluster exists almost surely exactly when it exists
with positive probability. -/
theorem law_exists_cluster_infinite_eq_one_iff_pos [Countable V] (q : Sym2 V → unitInterval) :
    law q {ω | ∃ x, (cluster ω x).Infinite} = 1 ↔
      0 < law q {ω | ∃ x, (cluster ω x).Infinite} := by
  refine ⟨fun h => h ▸ zero_lt_one, fun h => ?_⟩
  exact (law_exists_cluster_infinite_eq_zero_or_one q).resolve_left h.ne'

/-- **Root and global percolation.** On a countable vertex set an infinite cluster exists
almost surely exactly when the cluster of some vertex is infinite with positive probability. -/
theorem law_exists_cluster_infinite_eq_one_iff [Countable V] (q : Sym2 V → unitInterval) :
    law q {ω | ∃ x, (cluster ω x).Infinite} = 1 ↔
      ∃ x, 0 < law q {ω | (cluster ω x).Infinite} :=
  (law_exists_cluster_infinite_eq_one_iff_pos q).trans (law_exists_cluster_infinite_pos_iff q)

/-! ### Transitive laws -/

/-- Under transitivity of the law, the probability that the cluster of a vertex is infinite
does not depend on the vertex. No countability is needed. -/
theorem law_cluster_infinite_eq_of_transitive_law (q : Sym2 V → unitInterval)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (x y : V) :
    law q {ω | (cluster ω x).Infinite} = law q {ω | (cluster ω y).Infinite} := by
  obtain ⟨σ, rfl, hσ⟩ := hT x y
  exact (law_cluster_infinite_apply_eq_of_map_law_eq σ hσ x).symm

/-- Under transitivity of the law, an infinite cluster exists with positive probability
exactly when the cluster of a given root is infinite with positive probability. -/
theorem law_exists_cluster_infinite_pos_iff_of_transitive_law [Countable V]
    (q : Sym2 V → unitInterval)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (o : V) :
    0 < law q {ω | ∃ x, (cluster ω x).Infinite} ↔ 0 < law q {ω | (cluster ω o).Infinite} := by
  rw [law_exists_cluster_infinite_pos_iff]
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => ⟨o, h⟩⟩
  rwa [law_cluster_infinite_eq_of_transitive_law q hT o x]

/-- **Root and global percolation under transitivity.** Under transitivity of the law, an
infinite cluster exists almost surely exactly when the cluster of a given root is infinite with
positive probability. -/
theorem law_exists_cluster_infinite_eq_one_iff_of_transitive_law [Countable V]
    (q : Sym2 V → unitInterval)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (o : V) :
    law q {ω | ∃ x, (cluster ω x).Infinite} = 1 ↔ 0 < law q {ω | (cluster ω o).Infinite} :=
  (law_exists_cluster_infinite_eq_one_iff_pos q).trans
    (law_exists_cluster_infinite_pos_iff_of_transitive_law q hT o)

/-- The profile form of `law_exists_cluster_infinite_eq_one_iff_of_transitive_law`: for a
profile invariant under a transitive family of vertex bijections, an infinite cluster exists
almost surely exactly when the cluster of a given root is infinite with positive probability. -/
theorem law_exists_cluster_infinite_eq_one_iff_of_transitive [Countable V]
    (q : Sym2 V → unitInterval)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V) :
    law q {ω | ∃ x, (cluster ω x).Infinite} = 1 ↔ 0 < law q {ω | (cluster ω o).Infinite} :=
  law_exists_cluster_infinite_eq_one_iff_of_transitive_law q
    (fun x y => (hT x y).imp fun σ hσ => ⟨hσ.1, law_map_image_of_invariant σ hσ.2⟩) o

/-! ### Families of transitive laws -/

section Family

variable {ι : Type*} [Countable V] (p : ι → Sym2 V → unitInterval)

/-- For a family of transitive laws, the parameters with positive root percolation are those
with positive global percolation. No monotonicity in the parameter is used. -/
theorem setOf_law_cluster_infinite_pos_eq_of_transitive_law
    (hT : ∀ i, ∀ x y : V, ∃ σ : V ≃ V,
      σ x = y ∧ (law (p i)).map (fun ω => Sym2.map σ '' ω) = law (p i))
    (o : V) :
    {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
      {i | 0 < law (p i) {ω | ∃ x, (cluster ω x).Infinite}} := by
  ext i
  exact (law_exists_cluster_infinite_pos_iff_of_transitive_law (p i) (hT i) o).symm

/-- For a family of transitive laws, the parameters with positive root percolation are those
at which an infinite cluster exists almost surely. -/
theorem setOf_law_cluster_infinite_pos_eq_setOf_eq_one_of_transitive_law
    (hT : ∀ i, ∀ x y : V, ∃ σ : V ≃ V,
      σ x = y ∧ (law (p i)).map (fun ω => Sym2.map σ '' ω) = law (p i))
    (o : V) :
    {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
      {i | law (p i) {ω | ∃ x, (cluster ω x).Infinite} = 1} := by
  ext i
  exact (law_exists_cluster_infinite_eq_one_iff_of_transitive_law (p i) (hT i) o).symm

/-- For a family of transitive laws, the infimum of the parameters with positive root
percolation is the infimum of those with positive global percolation, whatever the value of
`sInf ∅`. -/
theorem sInf_setOf_law_cluster_infinite_pos_eq_of_transitive_law [InfSet ι]
    (hT : ∀ i, ∀ x y : V, ∃ σ : V ≃ V,
      σ x = y ∧ (law (p i)).map (fun ω => Sym2.map σ '' ω) = law (p i))
    (o : V) :
    sInf {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
      sInf {i | 0 < law (p i) {ω | ∃ x, (cluster ω x).Infinite}} := by
  rw [setOf_law_cluster_infinite_pos_eq_of_transitive_law p hT o]

/-- For a family of transitive laws, the infimum of the parameters with positive root
percolation is the infimum of those at which an infinite cluster exists almost surely,
whatever the value of `sInf ∅`. -/
theorem sInf_setOf_law_cluster_infinite_pos_eq_setOf_eq_one_of_transitive_law [InfSet ι]
    (hT : ∀ i, ∀ x y : V, ∃ σ : V ≃ V,
      σ x = y ∧ (law (p i)).map (fun ω => Sym2.map σ '' ω) = law (p i))
    (o : V) :
    sInf {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
      sInf {i | law (p i) {ω | ∃ x, (cluster ω x).Infinite} = 1} := by
  rw [setOf_law_cluster_infinite_pos_eq_setOf_eq_one_of_transitive_law p hT o]

end Family

end PercLib.Percolation.Bond
