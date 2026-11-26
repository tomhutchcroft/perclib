/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Correlation/HgapDisjointConnections.lean`,
`PercLib/CriticalLRP/Correlation/CovarianceGapGeneral.lean`,
`PercLib/CriticalLRP/Correlation/HgapClusterWeights.lean` and
`PercLib/CriticalLRP/Correlation/SquareWitness.lean`; licence Apache-2.0 as declared in those
file headers; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Contributor: yujinhkim.
Modified: the canonical-model events `connSet`, `disjSet`, `allConnSet`, `pairDisjSet`,
`pairAllSet` are written as `conn`, `disjointOccurrence` and intersections of `conn` on the
bond interface; `edgeMeasure` is `law q` for an arbitrary profile, and the hypothesis
`∀ e, π e < 1` is dropped; the finite-witness hypotheses on cluster events are replaced by
measurability, and the first event need not be increasing.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, Lemma I.2.1 and its corollary for disjoint connections.
-/
module

public import PercLib.Percolation.Bond.ClusterCorrelation.TwoClusterGap
public import PercLib.Percolation.Bond.Intensity.Defs

/-! # Covariance gaps for connection events and cluster events

For independent bond percolation `law q` with an arbitrary profile `q` on a countable vertex
type, the disjoint occurrence `x ↔ y ∘ z ↔ w` of two connection events differs from the product
`P(x ↔ y) P(z ↔ w)` by at most the probability that all four points lie in one cluster. The
lower half is BK; the upper half is Harris together with the deterministic fact that two
connections that do not occur disjointly share an open pair, so that all four points are
connected.

## Main results

* `mem_conn_of_notMem_disjointOccurrence`, `conn_inter_conn_subset_disjointOccurrence_union`:
  the deterministic overlap lemma and the resulting inclusion
  `{x ↔ y} ∩ {z ↔ w} ⊆ {x ↔ y ∘ z ↔ w} ∪ {x ↔ y ↔ z ↔ w}`;
* `tau_mul_tau_le_law_disjointOccurrence_add`,
  `measureReal_conn_mul_le_measureReal_disjointOccurrence_add`: the upper half;
* `abs_measureReal_disjointOccurrence_conn_sub_le`: the two-sided bound
  `|P(x ↔ y ∘ z ↔ w) - P(x ↔ y) P(z ↔ w)| ≤ P(x ↔ y ↔ z ↔ w)`;
* `law_inter_inter_compl_conn_le_mul`: BK for an event determined by the cluster of `x` and an
  increasing event determined by the cluster of `y`;
* `measureReal_inter_le_mul_add_measureReal_inter_conn`,
  `measureReal_inter_sub_mul_nonneg_and_le`: the covariance gap for events determined by the
  clusters of `x` and `y`;
* `conn_inter_compl_conn_inter_conn_eq_disjointOccurrence_inter`,
  `abs_measureReal_conn_inter_compl_conn_inter_conn_sub_le_two_mul`,
  `abs_measureReal_conn_inter_compl_conn_inter_conn_sub_le_of_le`: the gap in cluster
  coordinates `{x ∈ K_o, y ∉ K_o, z ∈ K_y}`, with constant `2` unconditionally and with
  constant `1` given the restoration inequality;
* `not_disjointOccurrence_conn_subset_conn_inter_compl_conn_inter_conn`: the event inclusion
  that would give constant `1` directly fails.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The deterministic overlap lemma -/

/-- **Two connections that do not occur disjointly join the four points.** If `x ↔ y` and
`z ↔ w` hold in `ω` but not disjointly, an open `x`–`y` path and an open `z`–`w` path share a
pair, so `y ↔ z`. -/
theorem mem_conn_of_notMem_disjointOccurrence {ω : Config V} {x y z w : V}
    (hxy : ω ∈ conn x y) (hzw : ω ∈ conn z w)
    (hnd : ω ∉ disjointOccurrence (conn x y) (conn z w)) : ω ∈ conn y z := by
  classical
  obtain ⟨p⟩ := (show (openGraph ω).Reachable x y from hxy)
  obtain ⟨r⟩ := (show (openGraph ω).Reachable z w from hzw)
  have hshare : ∃ e, e ∈ p.edges ∧ e ∈ r.edges := by
    by_contra hcon
    push Not at hcon
    refine hnd ((mem_disjointOccurrence_iff_open (isUpperSet_conn x y)
      (isUpperSet_conn z w) ω).2 ⟨{e | e ∈ p.edges}, {e | e ∈ r.edges}, p.edges.finite_toSet,
      r.edges.finite_toSet, Set.disjoint_left.2 fun e h₁ h₂ => hcon e h₁ h₂,
      walk_edges_subset p, walk_edges_subset r, mem_conn_of_walk_edges p fun e he => he,
      mem_conn_of_walk_edges r fun e he => he⟩)
  obtain ⟨e, hep, her⟩ := hshare
  induction e using Sym2.ind with
  | _ u v =>
    have hxu : (openGraph ω).Reachable x u := ⟨p.takeUntil u (p.fst_mem_support_of_mem_edges hep)⟩
    have hzu : (openGraph ω).Reachable z u := ⟨r.takeUntil u (r.fst_mem_support_of_mem_edges her)⟩
    exact (show (openGraph ω).Reachable x y from hxy).symm.trans (hxu.trans hzu.symm)

/-- `{x ↔ y} ∩ {z ↔ w} ⊆ {x ↔ y ∘ z ↔ w} ∪ {x ↔ y ↔ z ↔ w}`. -/
theorem conn_inter_conn_subset_disjointOccurrence_union (x y z w : V) :
    conn x y ∩ conn z w ⊆
      disjointOccurrence (conn x y) (conn z w) ∪ (conn x y ∩ conn y z ∩ conn z w) := by
  intro ω hω
  by_cases hd : ω ∈ disjointOccurrence (conn x y) (conn z w)
  · exact Or.inl hd
  · exact Or.inr ⟨⟨hω.1, mem_conn_of_notMem_disjointOccurrence hω.1 hω.2 hd⟩, hω.2⟩

/-! ### The gap for two connection events -/

variable [Countable V]

/-- **Upper half of the gap, `ℝ≥0∞` form**:
`τ(x,y) τ(z,w) ≤ P(x ↔ y ∘ z ↔ w) + P(x ↔ y ↔ z ↔ w)`. -/
theorem tau_mul_tau_le_law_disjointOccurrence_add (q : Sym2 V → unitInterval) (x y z w : V) :
    tau q x y * tau q z w ≤
      law q (disjointOccurrence (conn x y) (conn z w)) + law q (conn x y ∩ conn y z ∩ conn z w) :=
  (law_harris_conn q x y z w).trans ((measure_mono
    (conn_inter_conn_subset_disjointOccurrence_union x y z w)).trans (measure_union_le _ _))

/-- **Upper half of the gap, real form**:
`P(x ↔ y) P(z ↔ w) ≤ P(x ↔ y ∘ z ↔ w) + P(x ↔ y ↔ z ↔ w)`. -/
theorem measureReal_conn_mul_le_measureReal_disjointOccurrence_add (q : Sym2 V → unitInterval)
    (x y z w : V) :
    (law q).real (conn x y) * (law q).real (conn z w) ≤
      (law q).real (disjointOccurrence (conn x y) (conn z w)) +
        (law q).real (conn x y ∩ conn y z ∩ conn z w) := by
  simp only [measureReal_def, ← ENNReal.toReal_mul,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (tau_mul_tau_le_law_disjointOccurrence_add q x y z w)

/-- **The gap for two connection events** (Lemma I.2.1 applied to `1{x ↔ y}`, `1{z ↔ w}`):
`|P(x ↔ y ∘ z ↔ w) - P(x ↔ y) P(z ↔ w)| ≤ P(x ↔ y ↔ z ↔ w)`, for every profile. -/
theorem abs_measureReal_disjointOccurrence_conn_sub_le (q : Sym2 V → unitInterval)
    (x y z w : V) :
    |(law q).real (disjointOccurrence (conn x y) (conn z w)) -
        (law q).real (conn x y) * (law q).real (conn z w)| ≤
      (law q).real (conn x y ∩ conn y z ∩ conn z w) := by
  have hupper := measureReal_conn_mul_le_measureReal_disjointOccurrence_add q x y z w
  have hlower : (law q).real (disjointOccurrence (conn x y) (conn z w)) ≤
      (law q).real (conn x y) * (law q).real (conn z w) :=
    countable_profile_bk_real q (isUpperSet_conn x y) (isUpperSet_conn z w)
  have hnonneg : 0 ≤ (law q).real (conn x y ∩ conn y z ∩ conn z w) := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-! ### The covariance gap for cluster events -/

/-- **BK for cluster events.** If `A` is determined by the cluster of `x` and `B` is increasing
and determined by the cluster of `y`, then `P(A ∩ B ∩ {x ↮ y}) ≤ P(A) P(B)`. The event `A`
need not be increasing. -/
theorem law_inter_inter_compl_conn_le_mul (q : Sym2 V → unitInterval) {x y : V}
    {A B : Set (Config V)} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAx : ∀ ω ω' : Config V, cluster ω x = cluster ω' x → (ω ∈ A ↔ ω' ∈ A))
    (hB : IsUpperSet B) (hBy : ∀ ω ω' : Config V, cluster ω y = cluster ω' y → (ω ∈ B ↔ ω' ∈ B)) :
    law q (A ∩ B ∩ (conn x y)ᶜ) ≤ law q A * law q B := by
  have hE : MeasurableSet (A ∩ B ∩ (conn x y)ᶜ) :=
    (hAm.inter hBm).inter (measurableSet_conn x y).compl
  calc law q (A ∩ B ∩ (conn x y)ᶜ)
      = ((law q).prod (law q)) (restoreMap x ⁻¹' (A ∩ B ∩ (conn x y)ᶜ)) := by
        rw [← Measure.map_apply (measurable_restoreMap x) hE, map_restoreMap]
    _ ≤ ((law q).prod (law q)) (A ×ˢ B) := by
        refine measure_mono fun p hp => ?_
        obtain ⟨⟨hA', hB'⟩, hc⟩ := hp
        set ωr := restoreMap x p
        have hy : y ∉ cluster p.1 x := by
          rw [← cluster_restoreMap x p]; exact hc
        refine ⟨(hAx ωr p.1 (cluster_restoreMap x p)).1 hA', ?_⟩
        -- the cluster of `y` in `ωr` uses only pairs of `p.2`
        have hcl : cluster (ωr ∩ p.2) y = cluster ωr y := by
          refine cluster_eq_of_eqOn_touch fun e he => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
          obtain ⟨v, hv, hvy⟩ := he
          have hnt : ¬∃ u ∈ e, u ∈ cluster p.1 x := by
            rintro ⟨u, hu, huK⟩
            have huy : u ∈ cluster ωr y := by
              by_cases huv : v = u
              · exact huv ▸ hvy
              · have he' : e = s(v, u) := (Sym2.mem_and_mem_iff huv).1 ⟨hv, hu⟩
                subst he'
                exact (show (openGraph ωr).Reachable y v from hvy).trans
                  (SimpleGraph.Adj.reachable ((openGraph_adj_iff ωr v u).2 ⟨h, huv⟩))
            exact (cluster_restoreMap_subset_snd hy huy).2 huK
          exact (mem_restoreMap_of_not_touch hnt).1 h
        exact hB inter_subset_right ((hBy ωr (ωr ∩ p.2) hcl.symm).1 hB')
    _ = law q A * law q B := Measure.prod_prod _ _

/-- **The covariance gap for cluster events, upper half**:
`P(A ∩ B) ≤ P(A) P(B) + P(A ∩ B ∩ {x ↔ y})` for `A` determined by the cluster of `x` and `B`
increasing and determined by the cluster of `y`. -/
theorem measureReal_inter_le_mul_add_measureReal_inter_conn (q : Sym2 V → unitInterval)
    {x y : V} {A B : Set (Config V)} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAx : ∀ ω ω' : Config V, cluster ω x = cluster ω' x → (ω ∈ A ↔ ω' ∈ A))
    (hB : IsUpperSet B) (hBy : ∀ ω ω' : Config V, cluster ω y = cluster ω' y → (ω ∈ B ↔ ω' ∈ B)) :
    (law q).real (A ∩ B) ≤
      (law q).real A * (law q).real B + (law q).real (A ∩ B ∩ conn x y) := by
  have hbk : (law q).real (A ∩ B ∩ (conn x y)ᶜ) ≤ (law q).real A * (law q).real B := by
    simp only [measureReal_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (law_inter_inter_compl_conn_le_mul q hAm hBm hAx hB hBy)
  have hsplit : (law q).real (A ∩ B) =
      (law q).real (A ∩ B ∩ conn x y) + (law q).real (A ∩ B ∩ (conn x y)ᶜ) :=
    (measureReal_inter_add_sdiff (s := A ∩ B) (measurableSet_conn x y)).symm
  linarith

/-- **The covariance gap for cluster events** (the third display of Lemma I.2.1 for
indicators): for increasing measurable events `A`, `B` determined by the clusters of `x` and
`y`, `0 ≤ P(A ∩ B) - P(A) P(B) ≤ P(A ∩ B ∩ {x ↔ y})`. -/
theorem measureReal_inter_sub_mul_nonneg_and_le (q : Sym2 V → unitInterval) {x y : V}
    {A B : Set (Config V)} (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : IsUpperSet A)
    (hAx : ∀ ω ω' : Config V, cluster ω x = cluster ω' x → (ω ∈ A ↔ ω' ∈ A))
    (hB : IsUpperSet B) (hBy : ∀ ω ω' : Config V, cluster ω y = cluster ω' y → (ω ∈ B ↔ ω' ∈ B)) :
    0 ≤ (law q).real (A ∩ B) - (law q).real A * (law q).real B ∧
      (law q).real (A ∩ B) - (law q).real A * (law q).real B ≤
        (law q).real (A ∩ B ∩ conn x y) := by
  have hfkg : (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) :=
    prodBernoulli_harris_real q hA hB hAm hBm
  have hupper := measureReal_inter_le_mul_add_measureReal_inter_conn q hAm hBm hAx hB hBy
  constructor <;> linarith

/-! ### The gap in cluster coordinates

With `K_o` the cluster of `o` and `K_y` that of `y`, the event `{x ∈ K_o, y ∉ K_o, z ∈ K_y}`
is `conn o x ∩ (conn o y)ᶜ ∩ conn y z`, and `{x, y, z ∈ K_o}` is
`conn o x ∩ conn o y ∩ conn o z`. -/

omit [Countable V] in
/-- `{x ∈ K_o, y ∉ K_o, z ∈ K_y} ⊆ {o ↔ x ∘ y ↔ z}`: with `y ∉ K_o`, a pair shared by an
`o`–`x` path and a `y`–`z` path would join `o` to `y`. -/
theorem conn_inter_compl_conn_inter_conn_subset_disjointOccurrence (o x y z : V) :
    conn o x ∩ (conn o y)ᶜ ∩ conn y z ⊆ disjointOccurrence (conn o x) (conn y z) := by
  rintro ω ⟨⟨hox, hoy⟩, hyz⟩
  by_contra hnot
  exact hoy (conn_trans hox (mem_conn_of_notMem_disjointOccurrence hox hyz hnot))

omit [Countable V] in
/-- `{o ↔ x ∘ y ↔ z} ∩ {y ∈ K_o} ⊆ {x, y, z ∈ K_o}`. -/
theorem disjointOccurrence_conn_inter_conn_subset (o x y z : V) :
    disjointOccurrence (conn o x) (conn y z) ∩ conn o y ⊆ conn o x ∩ conn o y ∩ conn o z := by
  rintro ω ⟨hω, hoy⟩
  have h := disjointOccurrence_subset_inter _ _ hω
  exact ⟨⟨h.1, hoy⟩, conn_trans hoy h.2⟩

omit [Countable V] in
/-- `{x, y, z ∈ K_o}` is the four-point event `{o ↔ x ↔ y ↔ z}`. -/
theorem conn_inter_conn_inter_conn_eq (o x y z : V) :
    conn o x ∩ conn o y ∩ conn o z = conn o x ∩ conn x y ∩ conn y z := by
  ext ω
  simp only [mem_inter_iff, mem_conn_iff]
  constructor
  · rintro ⟨⟨hox, hoy⟩, hoz⟩
    exact ⟨⟨hox, hox.symm.trans hoy⟩, hoy.symm.trans hoz⟩
  · rintro ⟨⟨hox, hxy⟩, hyz⟩
    exact ⟨⟨hox, hox.trans hxy⟩, hox.trans (hxy.trans hyz)⟩

omit [Countable V] in
/-- **The cluster-coordinate event is the disjoint occurrence with `y ∉ K_o` imposed**:
`{x ∈ K_o, y ∉ K_o, z ∈ K_y} = {o ↔ x ∘ y ↔ z} ∩ {y ∉ K_o}`. -/
theorem conn_inter_compl_conn_inter_conn_eq_disjointOccurrence_inter (o x y z : V) :
    conn o x ∩ (conn o y)ᶜ ∩ conn y z =
      disjointOccurrence (conn o x) (conn y z) ∩ (conn o y)ᶜ := by
  refine Subset.antisymm (fun ω hω => ⟨?_, hω.1.2⟩) fun ω ⟨hω, hy⟩ => ?_
  · exact conn_inter_compl_conn_inter_conn_subset_disjointOccurrence o x y z hω
  · have h := disjointOccurrence_subset_inter _ _ hω
    exact ⟨⟨h.1, hy⟩, h.2⟩

omit [Countable V] in
/-- `{o ↔ x ∘ y ↔ z} ⊆ {x ∈ K_o, y ∉ K_o, z ∈ K_y} ∪ {x, y, z ∈ K_o}`. -/
theorem disjointOccurrence_conn_subset_union (o x y z : V) :
    disjointOccurrence (conn o x) (conn y z) ⊆
      conn o x ∩ (conn o y)ᶜ ∩ conn y z ∪ conn o x ∩ conn o y ∩ conn o z := by
  intro ω hω
  by_cases hy : ω ∈ conn o y
  · exact Or.inr (disjointOccurrence_conn_inter_conn_subset o x y z ⟨hω, hy⟩)
  · have h := disjointOccurrence_subset_inter _ _ hω
    exact Or.inl ⟨⟨h.1, hy⟩, h.2⟩

/-- **The gap in cluster coordinates with constant `2`**, for every profile:
`|P(x ∈ K_o, y ∉ K_o, z ∈ K_y) - P(o ↔ x) P(y ↔ z)| ≤ 2 P(x, y, z ∈ K_o)`. -/
theorem abs_measureReal_conn_inter_compl_conn_inter_conn_sub_le_two_mul
    (q : Sym2 V → unitInterval) (o x y z : V) :
    |(law q).real (conn o x ∩ (conn o y)ᶜ ∩ conn y z) -
        (law q).real (conn o x) * (law q).real (conn y z)| ≤
      2 * (law q).real (conn o x ∩ conn o y ∩ conn o z) := by
  have hupper := measureReal_conn_mul_le_measureReal_disjointOccurrence_add q o x y z
  have hlower : (law q).real (disjointOccurrence (conn o x) (conn y z)) ≤
      (law q).real (conn o x) * (law q).real (conn y z) :=
    countable_profile_bk_real q (isUpperSet_conn o x) (isUpperSet_conn y z)
  have hUD := measureReal_mono (μ := law q)
    (conn_inter_compl_conn_inter_conn_subset_disjointOccurrence o x y z)
  have hall : (law q).real (conn o x ∩ conn x y ∩ conn y z) =
      (law q).real (conn o x ∩ conn o y ∩ conn o z) := by
    rw [conn_inter_conn_inter_conn_eq]
  have hDF := (measureReal_mono (μ := law q) (disjointOccurrence_conn_subset_union o x y z)).trans
    (measureReal_union_le _ _)
  rw [abs_le]
  constructor <;> linarith

/-- **The gap in cluster coordinates with constant `1`, from the restoration inequality**
`P(o ↔ x ∘ y ↔ z) ≤ P(x ∈ K_o, y ∉ K_o, z ∈ K_y)`. The event inclusion behind that
inequality is false
(`not_disjointOccurrence_conn_subset_conn_inter_compl_conn_inter_conn`). -/
theorem abs_measureReal_conn_inter_compl_conn_inter_conn_sub_le_of_le
    (q : Sym2 V → unitInterval) (o x y z : V)
    (hrest : (law q).real (disjointOccurrence (conn o x) (conn y z)) ≤
      (law q).real (conn o x ∩ (conn o y)ᶜ ∩ conn y z)) :
    |(law q).real (conn o x ∩ (conn o y)ᶜ ∩ conn y z) -
        (law q).real (conn o x) * (law q).real (conn y z)| ≤
      (law q).real (conn o x ∩ conn o y ∩ conn o z) := by
  have hupper := measureReal_conn_mul_le_measureReal_disjointOccurrence_add q o x y z
  have hlower : (law q).real (disjointOccurrence (conn o x) (conn y z)) ≤
      (law q).real (conn o x) * (law q).real (conn y z) :=
    countable_profile_bk_real q (isUpperSet_conn o x) (isUpperSet_conn y z)
  have hUD := measureReal_mono (μ := law q)
    (conn_inter_compl_conn_inter_conn_subset_disjointOccurrence o x y z)
  have hall : (law q).real (conn o x ∩ conn x y ∩ conn y z) =
      (law q).real (conn o x ∩ conn o y ∩ conn o z) := by
    rw [conn_inter_conn_inter_conn_eq]
  rw [abs_le]
  constructor <;> linarith

/-! ### The event inclusion fails (D-5 witness) -/

/-- **`y ∉ K_o` cannot be dropped.** On `Fin 4` with the pairs `0—1, 1—2, 2—3, 0—3` open,
`0 ↔ 1` and `2 ↔ 3` occur disjointly, but `2` is in the cluster of `0`. So
`{o ↔ x ∘ y ↔ z} ⊆ {x ∈ K_o, y ∉ K_o, z ∈ K_y}` fails. -/
theorem not_disjointOccurrence_conn_subset_conn_inter_compl_conn_inter_conn :
    ¬ disjointOccurrence (conn (0 : Fin 4) 1) (conn 2 3) ⊆
      conn 0 1 ∩ (conn 0 2)ᶜ ∩ conn 2 3 := by
  intro h
  set ω : Config (Fin 4) := {s(0, 1), s(1, 2), s(2, 3), s(0, 3)}
  have hmem : ω ∈ disjointOccurrence (conn (0 : Fin 4) 1) (conn 2 3) := by
    refine (mem_disjointOccurrence_iff_open (isUpperSet_conn _ _) (isUpperSet_conn _ _) ω).2
      ⟨{s(0, 1)}, {s(2, 3)}, finite_singleton _, finite_singleton _, ?_, ?_, ?_,
        mem_conn_of_mem (by decide) rfl, mem_conn_of_mem (by decide) rfl⟩
    · rw [disjoint_singleton]; decide
    · simp [ω]
    · simp [ω]
  have h02 : ω ∈ conn (0 : Fin 4) 2 :=
    conn_trans (y := 1) (mem_conn_of_mem (by decide) (by simp [ω]))
      (mem_conn_of_mem (by decide) (by simp [ω]))
  exact (h hmem).1.2 h02

/-! ### Witnesses (D-5) -/

/-- The gap for two connection events under the law `P_β` of the long-range model with
intensities `J`, at four distinct vertices of `ℤ`. -/
example (J : Sym2 ℤ → NNReal) (β : NNReal) :
    |(law (intensityProfile J β)).real (disjointOccurrence (conn 0 1) (conn 2 3)) -
        (law (intensityProfile J β)).real (conn 0 1) *
          (law (intensityProfile J β)).real (conn 2 3)| ≤
      (law (intensityProfile J β)).real (conn 0 1 ∩ conn 1 2 ∩ conn 2 3) :=
  abs_measureReal_disjointOccurrence_conn_sub_le _ 0 1 2 3

/-- The covariance gap for the cluster events `{1 ∈ K_0}` and `{3 ∈ K_2}` on `ℕ`. -/
example (q : Sym2 ℕ → unitInterval) :=
  measureReal_inter_sub_mul_nonneg_and_le q (x := 0) (y := 2) (measurableSet_conn 0 1)
    (measurableSet_conn 2 3) (isUpperSet_conn 0 1)
    (fun ω ω' h => by simp only [← mem_cluster_iff, h]) (isUpperSet_conn 2 3)
    (fun ω ω' h => by simp only [← mem_cluster_iff, h])

end PercLib.Percolation.Bond
