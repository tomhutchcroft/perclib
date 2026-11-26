/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions and proofs, written on 2026-11-21 and 2026-11-22. No upstream code is copied.
Mathematical references: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (one-arm bounds, pp. 23-24); P. Nolin, Near-critical
percolation in two dimensions, Electron. J. Probab. 13 (2008), paper no. 55, Sections 3.1,
4.1-4.3 and 4.6 (crossing bounds below the characteristic length, arm events, landing sequences
and half-plane arm events, pp. 1570-1576 and 1586).
-/
module

public import Mathlib.Order.Circular.ZMod
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import PercLib.Models.Planar.Defs
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.FirstExit

/-!
# Arm events, box boundaries and crossing bounds

Events and notions of bond percolation on `ℤ^d` used by the arm estimates, on the bond interface
of the library: a configuration is a `Set (Sym2 (LatticeSite d))`, and only its
nearest-neighbour pairs are read.

* **The one-arm event.** `armEvent x r` is the event that the centre `x` of the box
  `x + [-r, r]^d` is joined to the boundary of the box, the points at sup distance exactly `r`
  from `x`, by a path of open nearest-neighbour edges all of whose vertices lie in the box. It
  is an event on the edges inside the box. An arm that leaves the box can be stopped on first
  reaching the boundary, so it is also the event that `x` is joined to the boundary by an open
  path confined to no box (`mem_armEvent_iff_exists_conn`). Its probability is the one-arm
  probability `π(r)`.
* **The four-strip event.** `fourStrip z n` is the event that the four strips of the annulus
  `2n ≤ ‖v - z‖∞ ≤ 4n` of `ℤ²` are crossed in their long direction by open paths: left-right
  crossings of the top and bottom strips, bottom-top crossings of the right and left strips.
  It stands for the open circuit of the one-arm bounds: two adjacent strips share a corner
  square, which their crossings cross in perpendicular directions, so the four crossings
  together surround the box of radius `2n - 1` (proved where the event is used).
* **The boundary of a box.** `boxBoundary lo hi` is the set of points of the box `Icc lo hi` of
  `ℤ^d` with some coordinate at an end of its range. For the box `x + [-r, r]^d` it is the
  boundary that the one-arm event reaches (`mem_armEvent_iff_exists_mem_boxBoundary`), the
  sphere of radius `r` about `x` for the sup metric (`boxBoundary_sub_add_eq_sphere`).
* **Perimeter positions.** `perimeterPos lo hi v` is the position of a boundary point `v` of a
  box of `ℤ²` along the boundary, counted counterclockwise from the lower-left corner `lo`.
  Distinct boundary points have distinct positions, all in `[0, 2(hi₀ - lo₀) + 2(hi₁ - lo₁))`,
  so the counterclockwise cyclic order of boundary points is the cyclic order of their
  positions (mathlib's `CircularOrder ℤ`).
* **Crossing bounds.** `CrossingBounds q L c` says that under `law q`, for every aspect ratio
  `k`, every `k n × n` box of `ℤ²` with `1 ≤ n ≤ L`, in either orientation and at any position,
  is crossed in its long direction by open edges and by dual-open edges with probability at
  least `c k > 0`. It is the hypothesis under which arm estimates hold uniformly in the law.
* **Crossing walks.** `p.IsCrossing S T`, for a walk `p` of any graph, says that `p` starts in
  `S` and never returns to it, and stays in `T` up to its last vertex, which is outside `T`.
* **Arms.** An open arm `IsOpenArm ω z r lo hi γ` is a walk of `ℤ²` along edges open in `ω`
  crossing from `B_r(z) = z + [-r, r]²` out of the interior of the box `Icc lo hi`: it leaves
  `B_r(z)` at its first step and stops on first reaching the boundary of `Icc lo hi`. A dual arm
  `IsDualArm ω z r lo hi γ` is a walk of faces (the dual vertex `f` is the unit square with
  lower-left corner `f`) along dual edges open in `dualConfig ω`, from a face touching `B_r(z)`,
  never touching it again, through faces of `Icc lo hi` up to its last face, which is outside
  the box. `IsArm ω c …` is the open arm for `c = true` and the dual arm for `c = false`.
* **Disjoint families.** `ArmsDisjoint σ γ`: two open arms share no vertex except possibly
  their first, two dual arms share no face.
* **Positions.** In the doubled lattice (a point `v` becomes `2v`, a face its centre `2f + 1`,
  an edge its midpoint), `innerPos z r c γ` is the position of the first edge of an open arm or
  the first face of a dual arm on the box `2z + [-(2r + 1), 2r + 1]²`, and `landingPos lo hi c γ`
  the position of the last vertex of an open arm or of the boundary edge crossed by the last
  dual edge of a dual arm on the box `Icc (2 lo) (2 hi)`. Both colours land on one cycle.
* **Multi-arm events.** `multiArmEventTo σ z r lo hi J I`: a disjoint family of arms with
  colours `σ`, inner positions in the windows `J`, landing positions in the windows `I`, landing
  in counterclockwise order (`sbtw` for every increasing triple). `multiArmEventIn σ z r R J I`
  is the centred case, `multiArmEvent σ z r R` the event `A_σ(r, R)` without windows. The
  half-plane events `halfArmEventTo`, `halfArmEventIn`, `halfArmEvent` keep the arms in
  `{v | z 1 ≤ v 1}` and order them from the right end: their landing positions increase.
* **Landing data.** `IsLanding η θ`: `j` windows `[θ i, θ i + η]` of the circle `[0, 1)` in
  counterclockwise order, separated by gaps of length at least `η` (Nolin's separated landing
  sequences). `window P θ η i` is the set of positions of a cycle of perimeter `P` in the
  window `i`.

Boxes stay `Set.Icc lo hi`, with `(r : LatticeSite d)` the constant vector `r`;
`Site.closedBall_eq_Icc` identifies the box `x + [-r, r]^d` with the closed ball of the sup
metric.

## Main definitions

* `PercLib.Models.Planar.armEvent`
* `PercLib.Models.Planar.fourStrip`
* `PercLib.Models.Planar.boxBoundary`
* `PercLib.Models.Planar.perimeterPos`
* `PercLib.Models.Planar.CrossingBounds`
* `SimpleGraph.Walk.IsCrossing`
* `PercLib.Models.Planar.IsOpenArm`, `PercLib.Models.Planar.IsDualArm`,
  `PercLib.Models.Planar.IsArm`, `PercLib.Models.Planar.ArmsDisjoint`
* `PercLib.Models.Planar.innerPos`, `PercLib.Models.Planar.landingPos`
* `PercLib.Models.Planar.multiArmEventTo`, `PercLib.Models.Planar.multiArmEventIn`,
  `PercLib.Models.Planar.multiArmEvent`
* `PercLib.Models.Planar.halfArmEventTo`, `PercLib.Models.Planar.halfArmEventIn`,
  `PercLib.Models.Planar.halfArmEvent`
* `PercLib.Models.Planar.IsLanding`, `PercLib.Models.Planar.window`

## Main results

* `mem_armEvent_iff_exists_conn`, `mem_armEvent_iff_exists_notMem_conn`,
  `mem_armEvent_of_mem_conn`: the arm may be stopped on first reaching the boundary, so the
  one-arm event is the event that `x` is joined to the boundary of the box, or to any point
  outside the box of radius `r - 1`, by open nearest-neighbour edges.
* `armEvent_anti` (decreasing in the radius), `armEvent_zero`, `armEvent_mono`,
  `isUpperSet_armEvent`, `measurableSet_armEvent`, `mem_armEvent_iff_of_inter_eq`
  (determined by the pairs inside the box), `image_add_mem_armEvent_iff` (translation).
* `fourStrip_mono`, `isUpperSet_fourStrip`, `measurableSet_fourStrip`,
  `mem_fourStrip_iff_of_inter_eq` (determined by the pairs inside the annulus),
  `image_add_mem_fourStrip_iff` (translation), `univ_mem_fourStrip`.
* `mem_armEvent_iff_exists_mem_boxBoundary`, `boxBoundary_sub_add_eq_sphere`: the one-arm event
  joins `x` to `boxBoundary (x - r) (x + r)`, the sphere of radius `r` of the sup metric.
* `boxBoundary_eq_Icc_diff_Icc` (the box minus the box one step inside it),
  `image_add_const_boxBoundary` (translation), `rotate_mem_boxBoundary_iff` (quarter turn).
* `perimeterPos_injOn`, `perimeterPos_nonneg`, `perimeterPos_lt`, the values on each side
  (`perimeterPos_of_bottom`, `perimeterPos_of_right`, `perimeterPos_of_top`,
  `perimeterPos_of_left`), `perimeterPos_add` (translation) and `perimeterPos_rotate` (a quarter
  turn shifts positions by the height of the box, modulo the perimeter).
* `CrossingBounds.mono`, `CrossingBounds.translate`, `crossingBounds_zero` (the trivial case),
  and the four orientations `CrossingBounds.le_law_crossing_zero` and its companions.
* `edgeSet_mem_localConn_Icc`: any two points of a box of `ℤ^d` are joined by nearest-neighbour
  edges inside the box.
* `image_add_inter_edgeSet_mem_localConn_iff`, `image_add_mem_crossing_iff`,
  `dualConfig_image_add`: translations carry connections inside a set and crossings of boxes,
  and commute with taking the dual configuration.
* `Bond.inter_mem_localConn_iff_of_inter_eq`: a connection inside `S` is determined by the pairs
  inside any `T ⊇ S`.
* `Site.closedBall_eq_Icc`, `Site.apply_le_apply_add_one_of_adj`: sup-metric balls of `ℤ^d` are
  boxes, and a nearest-neighbour step moves each coordinate by at most one.
* `IsOpenArm.start_mem_boxBoundary`, `IsOpenArm.end_mem_boxBoundary`, `IsOpenArm.mem_Icc`,
  `IsOpenArm.eq_start_of_mem`, `IsOpenArm.eq_end_of_mem_boxBoundary`: an open arm starts on the
  boundary of `B_r(z)`, lies in the outer box and meets `B_r(z)` and the boundary of the outer
  box only at its ends; `IsDualArm.start_mem_boxBoundary`, `IsDualArm.end_mem_boxBoundary`,
  `IsDualArm.mem_Icc` are the dual forms, and `IsDualArm.exists_mem_edgeSet_of_mem_edges`: a dual
  arm crosses only closed edges with both ends in the outer box.
* `mem_multiArmEventTo_iff`, `multiArmEventTo_mono` (windows), `measurableSet_multiArmEventTo`,
  `mem_multiArmEventTo_iff_of_agree` and `mem_multiArmEventTo_iff_of_inter_eq` (determined by
  the edges of the outer box with an end outside `B_r(z)`), `image_add_mem_multiArmEventTo_iff`
  (translation), `empty_notMem_multiArmEventTo`, `univ_notMem_multiArmEventTo`, and the same for
  the half-plane events; `halfArmEventTo_subset_multiArmEventTo`.
* `multiArmEvent_true_eq_armEvent`: one open arm from the centre is the one-arm event.
* `dualConfig_dualConfig`, `isOpenArm_dualConfig_iff`, `isDualArm_dualConfig_iff`: colour
  inversion; the dual of the dual configuration is the configuration translated by `(-1, -1)`.
* `innerPos_map_add`, `landingPos_map_add`, `landingPos_true`, `perimeterPos_two_smul`.
* `IsLanding.disjoint_window`, `nonempty_window`, `isLanding_div` (landing data exist for every
  number of arms).

## Implementation notes

* Positions live on the doubled lattice, so that open and dual arms land on one cycle: an open
  arm landing at `v` has position `2 · perimeterPos lo hi v`, a dual arm crossing the boundary
  edge from `x` to the next point `y` has position `2 · perimeterPos lo hi x + 1`. The inner
  positions use the box of half-integer radius `r + 1/2` between `B_r(z)` and the faces around
  it, which every arm crosses at its first step; for `r = 0` they record the first edge or face
  of each arm at `z`.
* Dual arms run from the faces touching `B_r(z)` (for `r = 0` the four faces at `z`) to the first
  face outside the outer box. Every dual edge they use crosses an edge with both ends in the
  outer box, the dual paths of quad duality.
* Arms of one family share no vertex or face, except that open arms may share their first vertex
  (all open arms from `z` when `r = 0`); an open arm and a dual arm never cross.
* The counterclockwise order of a family is stated by triples, with mathlib's strict cyclic
  betweenness `sbtw` on `ℤ` (`Int.sbtw_iff`), as the order-invariance theorems are.
-/

@[expose] public section

noncomputable section

open Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

/-! ### Connections inside a set are determined by the pairs inside it -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A connection inside `S` by the open pairs of `ω` that lie in `E` is determined by the pairs
of `ω` inside any set `T` containing `S`. -/
theorem inter_mem_localConn_iff_of_inter_eq {S T : Set V} (hST : S ⊆ T) (E : Set (Sym2 V))
    {ω ω' : Config V} (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) (a b : V) :
    ω ∩ E ∈ localConn S a b ↔ ω' ∩ E ∈ localConn S a b := by
  have hagree : ∀ x ∈ S, ∀ y ∈ S, (s(x, y) ∈ ω ∩ E ↔ s(x, y) ∈ ω' ∩ E) := by
    intro x hx y hy
    have hxy : s(x, y) ∈ {e : Sym2 V | ∀ v ∈ e, v ∈ T} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hST hx
      · exact hST hy
    have hmem := congrArg (s(x, y) ∈ ·) h
    simp only [eq_iff_iff, mem_inter_iff] at hmem
    simp only [mem_inter_iff]
    exact and_congr_left fun _ =>
      ⟨fun h₁ => (hmem.1 ⟨h₁, hxy⟩).1, fun h₁ => (hmem.2 ⟨h₁, hxy⟩).1⟩
  constructor
  · rintro ⟨ha, hb, hr⟩
    exact ⟨ha, hb, (localConn_iff_of_agree S ⟨a, ha⟩ ⟨b, hb⟩ hagree).1 hr⟩
  · rintro ⟨ha, hb, hr⟩
    exact ⟨ha, hb, (localConn_iff_of_agree S ⟨a, ha⟩ ⟨b, hb⟩ hagree).2 hr⟩

end PercLib.Percolation.Bond

/-! ### Coordinates and balls of `ℤ^d` -/

namespace PercLib.Models.Site

variable {d : ℕ}

/-- One nearest-neighbour step changes each coordinate by at most one. -/
theorem apply_le_apply_add_one_of_adj {u v : LatticeSite d} (h : (zdGraph d).Adj u v)
    (j : Fin d) : v j ≤ u j + 1 := by
  obtain ⟨i, hi, hj⟩ := (zdGraph_adj_iff_exists u v).1 h
  by_cases hji : j = i
  · rw [hji]
    omega
  · have := hj j hji
    omega

/-- The closed ball of radius `r` about `x` for the sup metric of `Fin d → ℤ` is the box
`x + [-r, r]^d`. -/
theorem closedBall_eq_Icc (x : LatticeSite d) (r : ℕ) :
    Metric.closedBall x r = Icc (x - r) (x + r) := by
  rw [closedBall_pi x (Nat.cast_nonneg r), ← pi_univ_Icc]
  refine pi_congr rfl fun i _ => ?_
  have h₁ : (x i : ℝ) - (r : ℝ) = ((x i - r : ℤ) : ℝ) := by simp
  have h₂ : (x i : ℝ) + (r : ℝ) = ((x i + r : ℤ) : ℝ) := by simp
  rw [Int.closedBall_eq_Icc, h₁, h₂, Int.ceil_intCast, Int.floor_intCast, Pi.sub_apply,
    Pi.add_apply, Pi.natCast_apply]

end PercLib.Models.Site

namespace PercLib.Models.Planar

variable {d : ℕ}

/-! ### Translations and boxes of `ℤ^d` -/

/-- **Translations carry connections.** Translating the configuration and the set by `c` carries
a connection by open nearest-neighbour edges inside the set to one between the translated
points. -/
theorem image_add_inter_edgeSet_mem_localConn_iff (c : LatticeSite d)
    (ω : Config (LatticeSite d)) (S : Set (LatticeSite d)) (a b : LatticeSite d) :
    Sym2.map (· + c) '' ω ∩ (zdGraph d).edgeSet ∈ localConn ((· + c) '' S) (a + c) (b + c) ↔
      ω ∩ (zdGraph d).edgeSet ∈ localConn S a b := by
  set σ : LatticeSite d ≃ LatticeSite d := Equiv.addRight c with hσ
  -- translations preserve the nearest-neighbour edges
  have hL : ∀ e, Sym2.map (· + c) e ∈ (zdGraph d).edgeSet ↔ e ∈ (zdGraph d).edgeSet := by
    intro e
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      exact zdGraph_adj_iff_of_sub fun i => by
        simp only [Pi.add_apply, add_sub_add_right_eq_sub]
  have himage : Sym2.map (· + c) '' ω ∩ (zdGraph d).edgeSet =
      Sym2.map σ '' (ω ∩ (zdGraph d).edgeSet) := by
    ext e
    constructor
    · rintro ⟨⟨e₀, he₀, rfl⟩, he⟩
      exact ⟨e₀, ⟨he₀, (hL e₀).1 he⟩, rfl⟩
    · rintro ⟨e₀, ⟨he₀, he⟩, rfl⟩
      exact ⟨⟨e₀, he₀, rfl⟩, (hL e₀).2 he⟩
  rw [himage]
  constructor
  · intro h'
    refine localConn_of_image (a := a) (b := b) σ _ (fun v hv => ?_) h'
    obtain ⟨w, hw, rfl⟩ := hv
    change σ.symm (σ w) ∈ S
    rw [Equiv.symm_apply_apply]
    exact hw
  · intro h'
    have ha : σ.symm (a + c) = a := σ.symm_apply_apply a
    have hb : σ.symm (b + c) = b := σ.symm_apply_apply b
    refine localConn_of_image (a := a + c) (b := b + c) σ.symm _ (S := (· + c) '' S) (T := S)
      (fun v hv => ⟨v, hv, rfl⟩) ?_
    rw [image_sym2Map_symm_image, ha, hb]
    exact h'

/-- **Boxes are connected.** Any two points of a box of `ℤ^d` are joined by a path of
nearest-neighbour edges all of whose vertices lie in the box. -/
theorem edgeSet_mem_localConn_Icc {lo hi a b : LatticeSite d} (ha : a ∈ Icc lo hi)
    (hb : b ∈ Icc lo hi) : (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b := by
  suffices h : ∀ N : ℕ, ∀ a ∈ Icc lo hi, ∑ i, (b i - a i).natAbs = N →
      (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b from h _ a ha rfl
  intro N
  induction N with
  | zero =>
    intro a ha hN
    have hab : a = b := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 hN) i (Finset.mem_univ i)
      omega
    subst hab
    rw [localConn_self ha]
    exact mem_univ _
  | succ N ih =>
    intro a ha hN
    obtain ⟨i, -, hne⟩ : ∃ i ∈ (Finset.univ : Finset (Fin d)), (b i - a i).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero hc] at hN
      exact Nat.zero_ne_add_one N hN
    set a' := Function.update a i (a i + if a i < b i then 1 else -1) with ha'
    have hadj : (zdGraph d).Adj a a' := (zdGraph_adj_iff_eq_update a a').2
      ⟨(i, decide (a i < b i)), by simp [ha']⟩
    have hsum : ∑ j, (b j - a j).natAbs = ∑ j, (b j - a' j).natAbs + 1 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i, (b j - a j).natAbs =
          ∑ j ∈ Finset.univ.erase i, (b j - a' j).natAbs :=
        Finset.sum_congr rfl fun j hj => by
          rw [ha', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest, ha', Function.update_self]
      split_ifs <;> omega
    have ha'mem : a' ∈ Icc lo hi := by
      simp only [mem_Icc, Pi.le_def] at ha hb ⊢
      refine ⟨fun j => ?_, fun j => ?_⟩
      · by_cases hj : j = i
        · rw [hj, ha', Function.update_self]
          have := ha.1 i
          have := hb.1 i
          split_ifs <;> omega
        · rw [ha', Function.update_of_ne hj]
          exact ha.1 j
      · by_cases hj : j = i
        · rw [hj, ha', Function.update_self]
          have := ha.2 i
          have := hb.2 i
          split_ifs <;> omega
        · rw [ha', Function.update_of_ne hj]
          exact ha.2 j
    have hstep : (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a a' :=
      ⟨ha, ha'mem, SimpleGraph.Adj.reachable
        ((openGraph_adj_iff _ a a').2 ⟨(SimpleGraph.mem_edgeSet _).2 hadj, hadj.ne⟩)⟩
    exact localConn_trans hstep (ih a' ha'mem (by omega))

/-! ### Translations of crossings and of the dual configuration -/

/-- **Translations carry crossings.** Translating the configuration and the box by `c` carries a
crossing of the box in direction `i` to a crossing of the translated box. -/
theorem image_add_mem_crossing_iff (c : LatticeSite d) (i : Fin d) (lo hi : LatticeSite d)
    (ω : Config (LatticeSite d)) :
    Sym2.map (· + c) '' ω ∈ crossing i (lo + c) (hi + c) ↔ ω ∈ crossing i lo hi := by
  rw [mem_crossing_iff, mem_crossing_iff, ← image_add_const_Icc]
  constructor
  · rintro ⟨a', ⟨a, ha, rfl⟩, hai, b', ⟨b, hb, rfl⟩, hbi, hab⟩
    refine ⟨a, ha, ?_, b, hb, ?_, (image_add_inter_edgeSet_mem_localConn_iff c ω _ a b).1 hab⟩
    · simpa only [Pi.add_apply, add_left_inj] using hai
    · simpa only [Pi.add_apply, add_left_inj] using hbi
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    refine ⟨a + c, ⟨a, ha, rfl⟩, ?_, b + c, ⟨b, hb, rfl⟩, ?_,
      (image_add_inter_edgeSet_mem_localConn_iff c ω _ a b).2 hab⟩
    · simp only [Pi.add_apply, hai]
    · simp only [Pi.add_apply, hbi]

/-- **The dual configuration commutes with translations.** The dual edges open in the
translated configuration are the translates of those open in the configuration. -/
theorem dualConfig_image_add (c : LatticeSite 2) (ω : Config (LatticeSite 2)) :
    dualConfig (Sym2.map (· + c) '' ω) = Sym2.map (· + c) '' dualConfig ω := by
  have hinj : Function.Injective (Sym2.map (· + c) : Sym2 (LatticeSite 2) → _) :=
    Sym2.map.injective (add_left_injective c)
  have hback : ∀ e : Sym2 (LatticeSite 2), Sym2.map (· + c) (Sym2.map (· + -c) e) = e := by
    intro e
    have h : ((fun v : LatticeSite 2 => v + c) ∘ fun v => v + -c) = id := by
      funext v
      simp
    rw [Sym2.map_map, h, Sym2.map_id, id]
  ext f
  rw [mem_dualConfig_iff']
  constructor
  · rintro ⟨e, he, heω, rfl⟩
    refine ⟨dualEdge (Sym2.map (· + -c) e), (mem_dualConfig_iff' ω _).2
      ⟨Sym2.map (· + -c) e, map_add_mem_edgeSet (-c) he, fun h => heω ⟨_, h, hback e⟩, rfl⟩, ?_⟩
    rw [← dualEdge_map_add, hback]
  · rintro ⟨f₀, hf₀, rfl⟩
    obtain ⟨e₀, he₀, heω, rfl⟩ := (mem_dualConfig_iff' ω f₀).1 hf₀
    refine ⟨Sym2.map (· + c) e₀, map_add_mem_edgeSet c he₀, ?_, dualEdge_map_add c e₀⟩
    rintro ⟨e', he', hee'⟩
    rw [hinj hee'] at he'
    exact heω he'

/-! ### The one-arm event -/

/-- The **one-arm event** of radius `r` at `x`: the centre `x` of the box `x + [-r, r]^d` is
joined to the boundary of the box, the points `v` of the box with `v i = x i - r` or
`v i = x i + r` for some `i`, by a path of open nearest-neighbour edges all of whose vertices
lie in the box. Open pairs that are not edges of `zdGraph d` are ignored. It is an event on the
edges inside the box; since an arm can be stopped on first reaching the boundary, it is also
the event that `x` is joined to the boundary by an open path confined to no box
(`mem_armEvent_iff_exists_conn`). Here `(r : LatticeSite d)` is the constant vector `r`, and
the box is the closed ball of radius `r` of the sup metric (`closedBall_eq_Icc`). In dimension
zero the box has no boundary and the event is empty. -/
def armEvent (x : LatticeSite d) (r : ℕ) : Set (Config (LatticeSite d)) :=
  {ω | ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
    ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v}

theorem mem_armEvent_iff {x : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v :=
  Iff.rfl

/-- The one-arm event depends only on the nearest-neighbour edges. -/
@[simp]
theorem inter_edgeSet_mem_armEvent_iff {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∩ (zdGraph d).edgeSet ∈ armEvent x r ↔ ω ∈ armEvent x r := by
  simp only [mem_armEvent_iff, inter_assoc, inter_self]

/-- The one-arm event is an increasing event. -/
theorem armEvent_mono {x : LatticeSite d} {r : ℕ} {ω ω' : Config (LatticeSite d)}
    (h : ω ⊆ ω') (hω : ω ∈ armEvent x r) : ω' ∈ armEvent x r := by
  obtain ⟨v, hv, hvx, hc⟩ := hω
  exact ⟨v, hv, hvx, localConn_mono (inter_subset_inter_left _ h) hc⟩

theorem isUpperSet_armEvent (x : LatticeSite d) (r : ℕ) : IsUpperSet (armEvent x r) :=
  fun _ _ h hω => armEvent_mono h hω

/-- The one-arm event is a measurable event. -/
theorem measurableSet_armEvent (x : LatticeSite d) (r : ℕ) : MeasurableSet (armEvent x r) := by
  have h : armEvent x r =
      ⋃ v ∈ {v | v ∈ Icc (x - r) (x + r) ∧ ∃ i, v i = x i - r ∨ v i = x i + r},
        (fun ω : Config (LatticeSite d) => ω ∩ (zdGraph d).edgeSet) ⁻¹'
          localConn (Icc (x - r) (x + r)) x v := by
    ext ω
    simp only [mem_armEvent_iff, mem_iUnion, mem_preimage, mem_ofPred_eq, exists_prop, and_assoc]
  rw [h]
  exact MeasurableSet.biUnion (to_countable _) fun v _ =>
    (measurableSet_localConn _ x v).preimage (by fun_prop)

/-- In the box of radius zero the centre is on the boundary, so the one-arm event of radius
zero holds in every configuration as soon as there is a coordinate. -/
theorem mem_armEvent_zero (x : LatticeSite d) (i : Fin d) (ω : Config (LatticeSite d)) :
    ω ∈ armEvent x 0 := by
  have hx : x ∈ Icc (x - ((0 : ℕ) : LatticeSite d)) (x + ((0 : ℕ) : LatticeSite d)) := by
    simp
  refine ⟨x, hx, ⟨i, Or.inl (by simp)⟩, ?_⟩
  rw [localConn_self hx]
  exact mem_univ _

/-- **The trivial case.** In positive dimension the one-arm event of radius zero is
everything. -/
@[simp]
theorem armEvent_zero [NeZero d] (x : LatticeSite d) : armEvent x 0 = univ :=
  eq_univ_of_forall (mem_armEvent_zero x 0)

/-- **Stopping on first reaching the boundary.** An open nearest-neighbour path from `x` to a
point `y` outside the box `x + [-(r - 1), r - 1]^d` (to any point when `r = 0`), confined to no
box, gives an arm from `x` to the boundary of `x + [-r, r]^d` inside that box. -/
theorem mem_armEvent_of_mem_conn {x y : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)}
    (hy : y ∉ Icc (x - r + 1) (x + r - 1)) (h : ω ∩ (zdGraph d).edgeSet ∈ conn x y) :
    ω ∈ armEvent x r := by
  by_cases hx : x ∈ Icc (x - r + 1) (x + r - 1)
  · obtain ⟨u, hu, w, hw, hxu, huw⟩ := exists_first_exit _ hx hy h
    have hadj : (zdGraph d).Adj u w := (SimpleGraph.mem_edgeSet _).1 huw.2
    have hwu := apply_le_apply_add_one_of_adj hadj
    have huw' := apply_le_apply_add_one_of_adj hadj.symm
    have hSB : Icc (x - r + 1) (x + r - 1) ⊆ Icc (x - r) (x + r) := by
      intro v hv
      simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
        Pi.one_apply] at hv ⊢
      exact ⟨fun j => by have := hv.1 j; omega, fun j => by have := hv.2 j; omega⟩
    have hu' := hu
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      Pi.one_apply, not_and_or, not_forall, not_le] at hu' hw
    have hwB : w ∈ Icc (x - r) (x + r) := by
      simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      exact ⟨fun j => by have := hu'.1 j; have := huw' j; omega,
        fun j => by have := hu'.2 j; have := hwu j; omega⟩
    have hwbd : ∃ i, w i = x i - r ∨ w i = x i + r := by
      rcases hw with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, Or.inl (by have := hu'.1 i; have := huw' i; omega)⟩
      · exact ⟨i, Or.inr (by have := hu'.2 i; have := hwu i; omega)⟩
    refine ⟨w, hwB, hwbd, localConn_trans (localConn_mono_set hSB x u ⟨hx, hu, hxu⟩) ?_⟩
    exact ⟨hSB hu, hwB, SimpleGraph.Adj.reachable ((openGraph_adj_iff _ u w).2 ⟨huw, hadj.ne⟩)⟩
  · simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      Pi.one_apply, not_and_or, not_forall, not_le] at hx
    obtain ⟨i, hr⟩ : ∃ _ : Fin d, (r : ℤ) = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, by omega⟩
      · exact ⟨i, by omega⟩
    obtain rfl : r = 0 := by omega
    exact mem_armEvent_zero x i ω

/-- **The one-arm event as an escape event.** `ω` has the one-arm event of radius `r` at `x`
exactly when an open nearest-neighbour path, confined to no box, joins `x` to a point outside
the box `x + [-(r - 1), r - 1]^d`. -/
theorem mem_armEvent_iff_exists_notMem_conn {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔
      ∃ y ∉ Icc (x - r + 1) (x + r - 1), ω ∩ (zdGraph d).edgeSet ∈ conn x y := by
  constructor
  · rintro ⟨v, -, ⟨i, hvi⟩, hc⟩
    refine ⟨v, fun hv => ?_, localConn_subset_conn _ x v hc⟩
    have h₁ := hv.1 i
    have h₂ := hv.2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h₁ h₂
    omega
  · rintro ⟨y, hy, hc⟩
    exact mem_armEvent_of_mem_conn hy hc

/-- **The one-arm event is the event `x ↔ ∂B_r(x)`.** Since an arm can be stopped on first
reaching the boundary, `ω` has the one-arm event exactly when `x` is joined to a point of the
boundary of the box by an open nearest-neighbour path confined to no box. -/
theorem mem_armEvent_iff_exists_conn {x : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
      ω ∩ (zdGraph d).edgeSet ∈ conn x v := by
  constructor
  · rintro ⟨v, hv, hvx, hc⟩
    exact ⟨v, hv, hvx, localConn_subset_conn _ x v hc⟩
  · rintro ⟨v, -, ⟨i, hvi⟩, hc⟩
    refine mem_armEvent_of_mem_conn (y := v) (fun hv => ?_) hc
    have h₁ := hv.1 i
    have h₂ := hv.2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h₁ h₂
    omega

/-- For a configuration of nearest-neighbour edges, the one-arm event is the event that `x` is
joined to the boundary of the box by an open path. -/
theorem mem_armEvent_iff_exists_conn_of_subset {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} (hω : ω ⊆ (zdGraph d).edgeSet) :
    ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
      ω ∈ conn x v := by
  rw [mem_armEvent_iff_exists_conn, inter_eq_left.2 hω]

/-- **Monotonicity in the radius.** The one-arm event decreases as the radius grows: an arm to
the boundary of a box, stopped on first reaching the boundary of a smaller box, is an arm of
the smaller box. -/
theorem armEvent_anti (x : LatticeSite d) : Antitone (armEvent x) := by
  intro r s hrs ω hω
  obtain ⟨y, hy, hc⟩ := mem_armEvent_iff_exists_notMem_conn.1 hω
  refine mem_armEvent_of_mem_conn (fun hyr => hy ?_) hc
  have hrs' : (r : ℤ) ≤ s := Nat.cast_le.2 hrs
  simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Pi.one_apply] at hyr ⊢
  exact ⟨fun j => by have := hyr.1 j; omega, fun j => by have := hyr.2 j; omega⟩

/-- **Determination.** The one-arm event is determined by the pairs inside any set containing
the box. -/
theorem mem_armEvent_iff_of_inter_eq {x : LatticeSite d} {r : ℕ} {T : Set (LatticeSite d)}
    (hT : Icc (x - r) (x + r) ⊆ T) {ω ω' : Config (LatticeSite d)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ armEvent x r ↔ ω' ∈ armEvent x r := by
  simp only [mem_armEvent_iff, inter_mem_localConn_iff_of_inter_eq hT (zdGraph d).edgeSet h]

/-- **Translation.** Translating the configuration by `c` carries the one-arm event at `x` to the
one-arm event at `x + c`. -/
theorem image_add_mem_armEvent_iff (c x : LatticeSite d) (r : ℕ) (ω : Config (LatticeSite d)) :
    Sym2.map (· + c) '' ω ∈ armEvent (x + c) r ↔ ω ∈ armEvent x r := by
  have hbox : Icc (x + c - r) (x + c + r) = (· + c) '' Icc (x - r) (x + r) := by
    rw [image_add_const_Icc, add_sub_right_comm, add_right_comm x c]
  rw [mem_armEvent_iff, mem_armEvent_iff, hbox]
  constructor
  · rintro ⟨v', ⟨v, hv, rfl⟩, ⟨i, hvi⟩, hc⟩
    refine ⟨v, hv, ⟨i, ?_⟩, (image_add_inter_edgeSet_mem_localConn_iff c ω _ x v).1 hc⟩
    simp only [Pi.add_apply] at hvi
    omega
  · rintro ⟨v, hv, ⟨i, hvi⟩, hc⟩
    refine ⟨v + c, ⟨v, hv, rfl⟩, ⟨i, ?_⟩,
      (image_add_inter_edgeSet_mem_localConn_iff c ω _ x v).2 hc⟩
    simp only [Pi.add_apply]
    omega

/-- Translation, as an identity of events. -/
theorem preimage_image_add_armEvent (c x : LatticeSite d) (r : ℕ) :
    (fun ω : Config (LatticeSite d) => Sym2.map (· + c) '' ω) ⁻¹' armEvent (x + c) r =
      armEvent x r :=
  ext fun ω => image_add_mem_armEvent_iff c x r ω

/-- With every edge closed there is no arm of positive radius. -/
theorem empty_notMem_armEvent {x : LatticeSite d} {r : ℕ} (hr : 1 ≤ r) :
    (∅ : Config (LatticeSite d)) ∉ armEvent x r := by
  rintro ⟨v, -, ⟨i, hvi⟩, hc⟩
  rw [empty_inter] at hc
  have hxv := (empty_mem_conn_iff x v).1 (localConn_subset_conn _ x v hc)
  subst hxv
  omega

/-- With every edge open, every box of positive dimension has an arm. -/
theorem univ_mem_armEvent [NeZero d] (x : LatticeSite d) (r : ℕ) :
    (univ : Config (LatticeSite d)) ∈ armEvent x r := by
  have hx : x ∈ Icc (x - r) (x + r) := by
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    exact ⟨fun j => by omega, fun j => by omega⟩
  have hxr : x + r ∈ Icc (x - r) (x + r) := by
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    exact ⟨fun j => by omega, fun j => le_rfl⟩
  refine ⟨x + r, hxr, ⟨0, Or.inr (by simp)⟩, ?_⟩
  rw [univ_inter]
  exact edgeSet_mem_localConn_Icc hx hxr

/-! ### The four-strip event -/

/-- The **four-strip event** of the annulus `2n ≤ ‖v - z‖∞ ≤ 4n` of `ℤ²`: open crossings of its
four strips in their long direction, namely left-right crossings of the top strip
`z + [-4n, 4n] × [2n, 4n]` and of the bottom strip `z + [-4n, 4n] × [-4n, -2n]`, and bottom-top
crossings of the right strip `z + [2n, 4n] × [-4n, 4n]` and of the left strip
`z + [-4n, -2n] × [-4n, 4n]`. Two adjacent strips share a corner square, which their crossings
cross in perpendicular directions; the event stands for the open circuit around the box of
radius `2n - 1` in the one-arm bounds. For `n = 0` every strip is a single point and the event
is everything. -/
def fourStrip (z : LatticeSite 2) (n : ℕ) : Set (Config (LatticeSite 2)) :=
  crossing 0 (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∩
  crossing 0 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) ∩
  crossing 1 (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∩
  crossing 1 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n])

theorem mem_fourStrip_iff {z : LatticeSite 2} {n : ℕ} {ω : Config (LatticeSite 2)} :
    ω ∈ fourStrip z n ↔
      ω ∈ crossing 0 (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∧
      ω ∈ crossing 0 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) ∧
      ω ∈ crossing 1 (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∧
      ω ∈ crossing 1 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n]) := by
  simp only [fourStrip, mem_inter_iff, and_assoc]

/-- The four-strip event depends only on the nearest-neighbour edges. -/
@[simp]
theorem inter_edgeSet_mem_fourStrip_iff {z : LatticeSite 2} {n : ℕ}
    {ω : Config (LatticeSite 2)} :
    ω ∩ (zdGraph 2).edgeSet ∈ fourStrip z n ↔ ω ∈ fourStrip z n := by
  simp only [mem_fourStrip_iff, inter_edgeSet_mem_crossing_iff]

/-- The four-strip event is an increasing event. -/
theorem fourStrip_mono {z : LatticeSite 2} {n : ℕ} {ω ω' : Config (LatticeSite 2)}
    (h : ω ⊆ ω') (hω : ω ∈ fourStrip z n) : ω' ∈ fourStrip z n := by
  rw [mem_fourStrip_iff] at hω ⊢
  exact ⟨crossing_mono h hω.1, crossing_mono h hω.2.1, crossing_mono h hω.2.2.1,
    crossing_mono h hω.2.2.2⟩

theorem isUpperSet_fourStrip (z : LatticeSite 2) (n : ℕ) : IsUpperSet (fourStrip z n) :=
  fun _ _ h hω => fourStrip_mono h hω

/-- The four-strip event is a measurable event. -/
theorem measurableSet_fourStrip (z : LatticeSite 2) (n : ℕ) : MeasurableSet (fourStrip z n) :=
  (((measurableSet_crossing _ _ _).inter (measurableSet_crossing _ _ _)).inter
    (measurableSet_crossing _ _ _)).inter (measurableSet_crossing _ _ _)

/-- **Determination.** The four-strip event is determined by the pairs inside any set containing
the annulus `2n ≤ ‖v - z‖∞ ≤ 4n`. -/
theorem mem_fourStrip_iff_of_inter_eq {z : LatticeSite 2} {n : ℕ} {T : Set (LatticeSite 2)}
    (hT : {v : LatticeSite 2 | z 0 - 4 * n ≤ v 0 ∧ v 0 ≤ z 0 + 4 * n ∧ z 1 - 4 * n ≤ v 1 ∧
      v 1 ≤ z 1 + 4 * n ∧
      (v 0 ≤ z 0 - 2 * n ∨ z 0 + 2 * n ≤ v 0 ∨ v 1 ≤ z 1 - 2 * n ∨ z 1 + 2 * n ≤ v 1)} ⊆ T)
    {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ fourStrip z n ↔ ω' ∈ fourStrip z n := by
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2), Icc lo hi ⊆ T →
      (ω ∈ crossing i lo hi ↔ ω' ∈ crossing i lo hi) := fun i lo hi hsub => by
    simp only [mem_crossing_iff,
      inter_mem_localConn_iff_of_inter_eq hsub (zdGraph 2).edgeSet h]
  have hsub : ∀ lo hi : LatticeSite 2, (∀ v : LatticeSite 2, lo 0 ≤ v 0 → v 0 ≤ hi 0 →
      lo 1 ≤ v 1 → v 1 ≤ hi 1 → v ∈ T) → Icc lo hi ⊆ T := fun lo hi hT' v hv => by
    rw [mem_Icc_two_iff] at hv
    exact hT' v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  rw [mem_fourStrip_iff, mem_fourStrip_iff]
  refine and_congr (hcross 0 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_)) (and_congr
    (hcross 0 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_)) (and_congr
    (hcross 1 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_))
    (hcross 1 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_)))) <;>
  · simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **Translation.** Translating the configuration by `c` carries the four-strip event at `z` to
the four-strip event at `z + c`. -/
theorem image_add_mem_fourStrip_iff (c z : LatticeSite 2) (n : ℕ) (ω : Config (LatticeSite 2)) :
    Sym2.map (· + c) '' ω ∈ fourStrip (z + c) n ↔ ω ∈ fourStrip z n := by
  simp only [mem_fourStrip_iff, add_right_comm z c, image_add_mem_crossing_iff]

/-- With every edge open, the four strips are crossed. -/
theorem univ_mem_fourStrip (z : LatticeSite 2) (n : ℕ) :
    (univ : Config (LatticeSite 2)) ∈ fourStrip z n := by
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2), lo ≤ hi →
      (univ : Config (LatticeSite 2)) ∈ crossing i lo hi := by
    intro i lo hi hle
    have hb : Function.update lo i (hi i) ∈ Icc lo hi := by
      simp only [mem_Icc, Pi.le_def]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · by_cases hj : j = i
        · rw [hj, Function.update_self]
          exact hle i
        · rw [Function.update_of_ne hj]
      · by_cases hj : j = i
        · rw [hj, Function.update_self]
        · rw [Function.update_of_ne hj]
          exact hle j
    refine ⟨lo, left_mem_Icc.2 hle, rfl, _, hb, Function.update_self .., ?_⟩
    rw [univ_inter]
    exact edgeSet_mem_localConn_Icc (left_mem_Icc.2 hle) hb
  have hle : ∀ a b a' b' : ℤ, a ≤ a' → b ≤ b' → z + ![a, b] ≤ z + ![a', b'] := by
    intro a b a' b' ha hb
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rw [mem_fourStrip_iff]
  exact ⟨hcross 0 _ _ (hle _ _ _ _ (by omega) (by omega)),
    hcross 0 _ _ (hle _ _ _ _ (by omega) (by omega)),
    hcross 1 _ _ (hle _ _ _ _ (by omega) (by omega)),
    hcross 1 _ _ (hle _ _ _ _ (by omega) (by omega))⟩

/-! ### The boundary of a box -/

/-- The **boundary of the box** `Icc lo hi` of `ℤ^d`: the points of the box with some coordinate
at an end of its range, `v i = lo i` or `v i = hi i`. For the box `x + [-r, r]^d` it is the
boundary reached by the one-arm event (`mem_armEvent_iff_exists_mem_boxBoundary`) and the sphere
of radius `r` about `x` for the sup metric (`boxBoundary_sub_add_eq_sphere`). In dimension zero
it is empty. -/
def boxBoundary (lo hi : LatticeSite d) : Set (LatticeSite d) :=
  {v | v ∈ Icc lo hi ∧ ∃ i, v i = lo i ∨ v i = hi i}

theorem mem_boxBoundary_iff {lo hi v : LatticeSite d} :
    v ∈ boxBoundary lo hi ↔ v ∈ Icc lo hi ∧ ∃ i, v i = lo i ∨ v i = hi i :=
  Iff.rfl

theorem boxBoundary_subset_Icc (lo hi : LatticeSite d) : boxBoundary lo hi ⊆ Icc lo hi :=
  fun _ hv => hv.1

/-- The boundary of a box is the box minus the box one step inside it. -/
theorem boxBoundary_eq_Icc_diff_Icc (lo hi : LatticeSite d) :
    boxBoundary lo hi = Icc lo hi \ Icc (lo + 1) (hi - 1) := by
  ext v
  simp only [mem_boxBoundary_iff, mem_sdiff, mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply,
    Pi.one_apply, not_and_or, not_forall, not_le]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, i, hvi | hvi⟩
    · exact ⟨⟨h₁, h₂⟩, Or.inl ⟨i, by omega⟩⟩
    · exact ⟨⟨h₁, h₂⟩, Or.inr ⟨i, by omega⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨i, hvi⟩ | ⟨i, hvi⟩⟩
    · exact ⟨⟨h₁, h₂⟩, i, Or.inl (by have := h₁ i; omega)⟩
    · exact ⟨⟨h₁, h₂⟩, i, Or.inr (by have := h₂ i; omega)⟩

/-- **The trivial case.** In positive dimension the boundary of a one-point box is the point. -/
@[simp]
theorem boxBoundary_self [NeZero d] (v : LatticeSite d) : boxBoundary v v = {v} := by
  ext w
  simp only [mem_boxBoundary_iff, Icc_self, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, 0, Or.inl rfl⟩

/-- The lower corner of a nonempty box of positive dimension is on its boundary. -/
theorem left_mem_boxBoundary [NeZero d] {lo hi : LatticeSite d} (h : lo ≤ hi) :
    lo ∈ boxBoundary lo hi :=
  ⟨left_mem_Icc.2 h, 0, Or.inl rfl⟩

/-- The upper corner of a nonempty box of positive dimension is on its boundary. -/
theorem right_mem_boxBoundary [NeZero d] {lo hi : LatticeSite d} (h : lo ≤ hi) :
    hi ∈ boxBoundary lo hi :=
  ⟨right_mem_Icc.2 h, 0, Or.inr rfl⟩

/-- **Translation.** Translating a point and the box by `c` keeps the point on the boundary. -/
@[simp]
theorem add_mem_boxBoundary_add_iff {lo hi v : LatticeSite d} (c : LatticeSite d) :
    v + c ∈ boxBoundary (lo + c) (hi + c) ↔ v ∈ boxBoundary lo hi := by
  simp only [mem_boxBoundary_iff, mem_Icc, Pi.le_def, Pi.add_apply, add_le_add_iff_right,
    add_left_inj]

/-- **Translation.** The translate of the boundary of a box is the boundary of the translated
box. -/
theorem image_add_const_boxBoundary (c lo hi : LatticeSite d) :
    (· + c) '' boxBoundary lo hi = boxBoundary (lo + c) (hi + c) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (add_mem_boxBoundary_add_iff c).2 hv
  · intro hw
    refine ⟨w - c, ?_, sub_add_cancel w c⟩
    rw [← add_mem_boxBoundary_add_iff c, sub_add_cancel]
    exact hw

/-- The boundary of the box `x + [-r, r]^d`, coordinate by coordinate: the points of the box
with some coordinate at distance exactly `r` from that of `x`. This is the boundary used by
`armEvent x r`. -/
theorem mem_boxBoundary_sub_add_iff {x v : LatticeSite d} {r : ℕ} :
    v ∈ boxBoundary (x - r : LatticeSite d) (x + r) ↔
      v ∈ Icc (x - r) (x + r) ∧ ∃ i, v i = x i - r ∨ v i = x i + r := by
  simp only [mem_boxBoundary_iff, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]

/-- In positive dimension the boundary of the box `x + [-r, r]^d` is the sphere of radius `r`
about `x` for the sup metric of `Fin d → ℤ` (compare `Site.closedBall_eq_Icc`). -/
theorem boxBoundary_sub_add_eq_sphere [NeZero d] (x : LatticeSite d) (r : ℕ) :
    boxBoundary (x - r : LatticeSite d) (x + r) = Metric.sphere x r := by
  rw [sphere_pi x (Or.inr inferInstance), closedBall_eq_Icc]
  ext v
  have key : ∀ a b : ℤ, dist a b = (r : ℝ) ↔ a = b - r ∨ a = b + r := by
    intro a b
    rw [Int.dist_eq, abs_eq (Nat.cast_nonneg r)]
    constructor
    · rintro (h | h)
      · right
        have h' : ((a - b : ℤ) : ℝ) = ((r : ℤ) : ℝ) := by push_cast; linarith
        have := Int.cast_injective h'
        omega
      · left
        have h' : ((a - b : ℤ) : ℝ) = ((-(r : ℤ) : ℤ) : ℝ) := by push_cast; linarith
        have := Int.cast_injective h'
        omega
    · rintro (h | h)
      · right
        rw [h]
        push_cast
        ring
      · left
        rw [h]
        push_cast
        ring
  simp only [mem_boxBoundary_sub_add_iff, mem_inter_iff, mem_iUnion, mem_preimage,
    Function.eval, Metric.mem_sphere, key]
  exact and_comm

/-- **The one-arm event reaches the boundary of the box.** `ω` has the one-arm event of radius
`r` at `x` exactly when `x` is joined to a point of `boxBoundary (x - r) (x + r)` by open
nearest-neighbour edges inside the box. This restates `armEvent` with `boxBoundary`. -/
theorem mem_armEvent_iff_exists_mem_boxBoundary {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ boxBoundary (x - r : LatticeSite d) (x + r),
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v := by
  simp only [mem_armEvent_iff, mem_boxBoundary_sub_add_iff, and_assoc]

/-- **The one-arm event as `x ↔ ∂B_r(x)`, with `boxBoundary`.** The path to the boundary may be
confined to no box (`mem_armEvent_iff_exists_conn`). -/
theorem mem_armEvent_iff_exists_mem_boxBoundary_conn {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ boxBoundary (x - r : LatticeSite d) (x + r),
      ω ∩ (zdGraph d).edgeSet ∈ conn x v := by
  simp only [mem_armEvent_iff_exists_conn, mem_boxBoundary_sub_add_iff, and_assoc]

/-- The boundary of a box of `ℤ²`, coordinate by coordinate. -/
theorem mem_boxBoundary_two_iff {lo hi v : LatticeSite 2} :
    v ∈ boxBoundary lo hi ↔ (lo 0 ≤ v 0 ∧ v 0 ≤ hi 0 ∧ lo 1 ≤ v 1 ∧ v 1 ≤ hi 1) ∧
      (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = lo 1 ∨ v 1 = hi 1) := by
  rw [mem_boxBoundary_iff, mem_Icc_two_iff, Fin.exists_fin_two, or_assoc]

/-- **Quarter turn.** The counterclockwise quarter turn `(x, y) ↦ (-y, x)` of `ℤ²` maps the
boundary of `Icc lo hi` onto the boundary of the turned box `[-hi₁, -lo₁] × [lo₀, hi₀]`. -/
@[simp]
theorem rotate_mem_boxBoundary_iff {lo hi v : LatticeSite 2} :
    ![-v 1, v 0] ∈ boxBoundary (d := 2) ![-hi 1, lo 0] ![-lo 1, hi 0] ↔
      v ∈ boxBoundary lo hi := by
  simp only [mem_boxBoundary_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> omega

/-! ### Perimeter positions on the boundary of a box of `ℤ²` -/

/-- The **perimeter position** of a point `v` of the boundary of the box `Icc lo hi` of `ℤ²`:
its distance from the lower-left corner `lo` along the boundary, counterclockwise. The bottom
side, both corners included, has positions `0` to `hi₀ - lo₀`; then come the right side above
the lower-right corner, the top side left of the upper-right corner, and the left side strictly
between the upper-left and lower-left corners. Each corner other than `lo` belongs to the side
that ends at it. Distinct boundary points have distinct positions (`perimeterPos_injOn`), all in
`[0, 2(hi₀ - lo₀) + 2(hi₁ - lo₁))` unless the box is a point (`perimeterPos_nonneg`,
`perimeterPos_lt`), so the counterclockwise cyclic order of boundary points is the cyclic order
of their positions (mathlib's `CircularOrder ℤ`). Off the boundary the value is that of the last
case and has no meaning. -/
def perimeterPos (lo hi v : LatticeSite 2) : ℤ :=
  if v 1 = lo 1 then v 0 - lo 0
  else if v 0 = hi 0 then (hi 0 - lo 0) + (v 1 - lo 1)
  else if v 1 = hi 1 then (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 0 - v 0)
  else 2 * (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 1 - v 1)

/-- The position of a point of the bottom side. -/
theorem perimeterPos_of_bottom {lo hi v : LatticeSite 2} (h : v 1 = lo 1) :
    perimeterPos lo hi v = v 0 - lo 0 :=
  ite_eq_left h

/-- The position of a point of the right side above the lower-right corner. -/
theorem perimeterPos_of_right {lo hi v : LatticeSite 2} (h₀ : v 0 = hi 0) (h₁ : v 1 ≠ lo 1) :
    perimeterPos lo hi v = (hi 0 - lo 0) + (v 1 - lo 1) := by
  rw [perimeterPos, ite_eq_right h₁, ite_eq_left h₀]

/-- The position of a point of the top side left of the upper-right corner. -/
theorem perimeterPos_of_top {lo hi v : LatticeSite 2} (h₁ : v 1 = hi 1) (h₀ : v 0 ≠ hi 0)
    (h₁' : v 1 ≠ lo 1) :
    perimeterPos lo hi v = (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 0 - v 0) := by
  rw [perimeterPos, ite_eq_right h₁', ite_eq_right h₀, ite_eq_left h₁]

/-- The position of a point off the bottom, right and top sides, in particular of a point of the
left side strictly between its corners. -/
theorem perimeterPos_of_left {lo hi v : LatticeSite 2} (h₀ : v 0 ≠ hi 0) (h₁ : v 1 ≠ lo 1)
    (h₁' : v 1 ≠ hi 1) :
    perimeterPos lo hi v = 2 * (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 1 - v 1) := by
  rw [perimeterPos, ite_eq_right h₁, ite_eq_right h₀, ite_eq_right h₁']

/-- The lower-left corner has position zero. -/
@[simp]
theorem perimeterPos_self (lo hi : LatticeSite 2) : perimeterPos lo hi lo = 0 := by
  rw [perimeterPos_of_bottom rfl, sub_self]

/-- Positions of points of the box are nonnegative. -/
theorem perimeterPos_nonneg {lo hi v : LatticeSite 2} (hv : v ∈ Icc lo hi) :
    0 ≤ perimeterPos lo hi v := by
  rw [mem_Icc_two_iff] at hv
  unfold perimeterPos
  split_ifs <;> omega

/-- **Bound by the perimeter.** Positions of points of a box that is not a point are smaller than
its perimeter `2(hi₀ - lo₀) + 2(hi₁ - lo₁)`. -/
theorem perimeterPos_lt {lo hi v : LatticeSite 2} (hne : lo ≠ hi) (hv : v ∈ Icc lo hi) :
    perimeterPos lo hi v < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) := by
  rw [mem_Icc_two_iff] at hv
  have hlt : lo 0 < hi 0 ∨ lo 1 < hi 1 := by
    by_contra hc
    refine hne (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)) <;> omega
  unfold perimeterPos
  split_ifs <;> omega

/-- **Injectivity.** Distinct points of the boundary of a box have distinct positions. -/
theorem perimeterPos_injOn (lo hi : LatticeSite 2) :
    InjOn (perimeterPos lo hi) (boxBoundary lo hi) := by
  intro u hu v hv huv
  rw [mem_boxBoundary_two_iff] at hu hv
  unfold perimeterPos at huv
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> split_ifs at huv <;> omega

/-- **Translation.** Translating a point and the box by `c` keeps its position. -/
@[simp]
theorem perimeterPos_add (c lo hi v : LatticeSite 2) :
    perimeterPos (lo + c) (hi + c) (v + c) = perimeterPos lo hi v := by
  simp only [perimeterPos, Pi.add_apply, add_left_inj, add_sub_add_right_eq_sub]

/-- **Quarter turn.** The counterclockwise quarter turn `(x, y) ↦ (-y, x)` maps the box
`Icc lo hi` onto `[-hi₁, -lo₁] × [lo₀, hi₀]` and its lower-left corner to the lower-right corner
of the turned box, so it shifts the position of each boundary point by the height
`hi₁ - lo₁` of the box, modulo the perimeter. The box must have positive width and height: on a
segment the positions run along it only once. -/
theorem perimeterPos_rotate {lo hi v : LatticeSite 2} (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    (hv : v ∈ boxBoundary lo hi) :
    perimeterPos ![-hi 1, lo 0] ![-lo 1, hi 0] ![-v 1, v 0] =
      (perimeterPos lo hi v + (hi 1 - lo 1)) % (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) := by
  rw [mem_boxBoundary_two_iff] at hv
  have key : ∀ X Y P : ℤ, 0 ≤ X → X < P → (Y = X ∨ Y = X + P) → X = Y % P := by
    rintro X Y P hX hXP (rfl | rfl)
    · exact (Int.emod_eq_of_lt hX hXP).symm
    · rw [Int.add_emod_right, Int.emod_eq_of_lt hX hXP]
  unfold perimeterPos
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine key _ _ _ ?_ ?_ ?_ <;> split_ifs <;> omega

/-! ### Crossing bounds -/

/-- **Crossing bounds of both colours up to scale `L`.** Under `law q`, for every aspect ratio
`k`, every box of `ℤ²` of size `k n × n` with `1 ≤ n ≤ L`, in either orientation and at any
position, is crossed in its long direction with probability at least `c k > 0`, both by open
edges and by dual-open edges, the edges open in `dualConfig ω` (the box is then a box of faces,
the dual vertex `f` standing for the face with lower-left corner `f`). Direction `i = 0` is the
box `[lo, lo + (k n, n)]` crossed from left to right, direction `i = 1` the box
`[lo, lo + (n, k n)]` crossed from bottom to top. At `1/2` such bounds hold at every scale,
`L = ⊤`, by the Russo–Seymour–Welsh bounds; near `1/2` they hold below the characteristic
length. The case `k = 0` is a box of width zero, crossed by every configuration, so only
`1 ≤ k` constrains `c`. -/
structure CrossingBounds (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞) (c : ℕ → ℝ≥0∞) :
    Prop where
  /-- The bounds are positive. -/
  pos : ∀ k, 0 < c k
  /-- Open crossings in the long direction. -/
  le_law_crossing : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n → (n : ℕ∞) ≤ L →
    c k ≤ law q (crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]))
  /-- Dual-open crossings in the long direction. -/
  le_law_dualConfig_crossing : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n →
    (n : ℕ∞) ≤ L →
    c k ≤ law q (dualConfig ⁻¹'
      crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]))

namespace CrossingBounds

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- Left-right open crossings of the boxes `[lo, lo + (k n, n)]`. -/
theorem le_law_crossing_zero (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2) {n : ℕ}
    (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (crossing 0 lo (lo + ![(k : ℤ) * n, n])) :=
  h.le_law_crossing k 0 lo n hn hnL

/-- Bottom-top open crossings of the boxes `[lo, lo + (n, k n)]`. -/
theorem le_law_crossing_one (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2) {n : ℕ}
    (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (crossing 1 lo (lo + ![(n : ℤ), k * n])) :=
  h.le_law_crossing k 1 lo n hn hnL

/-- Left-right dual-open crossings of the boxes of faces `[lo, lo + (k n, n)]`. -/
theorem le_law_dualConfig_crossing_zero (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (dualConfig ⁻¹' crossing 0 lo (lo + ![(k : ℤ) * n, n])) :=
  h.le_law_dualConfig_crossing k 0 lo n hn hnL

/-- Bottom-top dual-open crossings of the boxes of faces `[lo, lo + (n, k n)]`. -/
theorem le_law_dualConfig_crossing_one (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (dualConfig ⁻¹' crossing 1 lo (lo + ![(n : ℤ), k * n])) :=
  h.le_law_dualConfig_crossing k 1 lo n hn hnL

/-- **Monotonicity.** Crossing bounds up to scale `L` give smaller positive bounds up to any
smaller scale. -/
theorem mono {L' : ℕ∞} {c' : ℕ → ℝ≥0∞} (h : CrossingBounds q L c) (hL : L' ≤ L) (hc : c' ≤ c)
    (hpos : ∀ k, 0 < c' k) : CrossingBounds q L' c' where
  pos := hpos
  le_law_crossing k i lo n hn hnL :=
    (hc k).trans (h.le_law_crossing k i lo n hn (hnL.trans hL))
  le_law_dualConfig_crossing k i lo n hn hnL :=
    (hc k).trans (h.le_law_dualConfig_crossing k i lo n hn (hnL.trans hL))

/-- **Translation.** Crossing bounds pass to the law seen from `a`, with profile
`e ↦ q (e + a)`: its configuration is that of `law q` translated by `-a`. -/
theorem translate (h : CrossingBounds q L c) (a : LatticeSite 2) :
    CrossingBounds (fun e => q (Sym2.map (· + a) e)) L c := by
  have hlaw : ∀ A : Set (Config (LatticeSite 2)),
      law (fun e => q (Sym2.map (· + a) e)) A =
        law q ((fun ω => Sym2.map (· + -a) '' ω) ⁻¹' A) := by
    intro A
    have hmap := PercLib.Probability.prodBernoulli_map_image_sym2 q (Equiv.addRight (-a))
    have hq : (q ∘ Sym2.map (Equiv.addRight (-a)).symm) = fun e => q (Sym2.map (· + a) e) := by
      funext e
      simp only [Function.comp_apply, Equiv.addRight_symm, neg_neg, Equiv.coe_addRight]
    rw [hq] at hmap
    unfold law
    rw [← hmap]
    exact map_image_sym2Map_apply _ _ _
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      (fun ω => Sym2.map (· + -a) '' ω) ⁻¹' crossing i lo hi = crossing i (lo + a) (hi + a) := by
    intro i lo hi
    ext ω
    have := image_add_mem_crossing_iff (-a) i (lo + a) (hi + a) ω
    rw [add_neg_cancel_right, add_neg_cancel_right] at this
    rw [mem_preimage]
    exact this
  have hdual : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      (fun ω => Sym2.map (· + -a) '' ω) ⁻¹' (dualConfig ⁻¹' crossing i lo hi) =
        dualConfig ⁻¹' crossing i (lo + a) (hi + a) := by
    intro i lo hi
    ext ω
    have := image_add_mem_crossing_iff (-a) i (lo + a) (hi + a) (dualConfig ω)
    rw [add_neg_cancel_right, add_neg_cancel_right, ← dualConfig_image_add] at this
    simp only [mem_preimage]
    exact this
  refine ⟨h.pos, fun k i lo n hn hnL => ?_, fun k i lo n hn hnL => ?_⟩
  · rw [hlaw, hcross, add_right_comm lo]
    exact h.le_law_crossing k i (lo + a) n hn hnL
  · rw [hlaw, hdual, add_right_comm lo]
    exact h.le_law_dualConfig_crossing k i (lo + a) n hn hnL

end CrossingBounds

/-- **The trivial case.** Every law has crossing bounds up to scale zero, with any positive
bounds: no box has `1 ≤ n ≤ 0`. -/
theorem crossingBounds_zero (q : Sym2 (LatticeSite 2) → unitInterval) {c : ℕ → ℝ≥0∞}
    (hc : ∀ k, 0 < c k) : CrossingBounds q 0 c where
  pos := hc
  le_law_crossing _ _ _ n hn hn0 := by
    have : n ≤ 0 := by exact_mod_cast hn0
    omega
  le_law_dualConfig_crossing _ _ _ n hn hn0 := by
    have : n ≤ 0 := by exact_mod_cast hn0
    omega

end PercLib.Models.Planar

/-! ### Walks crossing from one set out of another -/

namespace SimpleGraph.Walk

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

/-- A walk **crosses from `S` out of `T`**: it starts in `S` and never returns to `S`, and it
stays in `T` up to its last vertex, which lies outside `T`. For a box `S` inside a box `T` it is
a crossing of the annulus between them, stopped when it first leaves `T`. -/
structure IsCrossing (S T : Set V) {u v : V} (p : G.Walk u v) : Prop where
  /-- The walk starts in `S`. -/
  start_mem : u ∈ S
  /-- After its first vertex the walk avoids `S`. -/
  notMem_of_mem_tail : ∀ w ∈ p.support.tail, w ∉ S
  /-- The walk ends outside `T`. -/
  end_notMem : v ∉ T
  /-- Before its last vertex the walk stays in `T`. -/
  mem_of_mem_dropLast : ∀ w ∈ p.support.dropLast, w ∈ T

variable {S T : Set V} {u v : V} {p : G.Walk u v}

/-- A walk of length zero crosses from `S` out of `T` when its vertex is in `S` and not in
`T`. -/
@[simp]
theorem isCrossing_nil_iff : (nil : G.Walk u u).IsCrossing S T ↔ u ∈ S ∧ u ∉ T :=
  ⟨fun h => ⟨h.start_mem, h.end_notMem⟩, fun h => ⟨h.1, by simp, h.2, by simp⟩⟩

/-- A crossing from a set out of a set containing it has at least one step. -/
theorem IsCrossing.not_nil (h : p.IsCrossing S T) (hST : S ⊆ T) : ¬p.Nil := fun hp => by
  obtain rfl := hp.eq
  exact h.end_notMem (hST h.start_mem)

/-- The second vertex of a crossing is outside `S`. -/
theorem IsCrossing.snd_notMem (h : p.IsCrossing S T) (hp : ¬p.Nil) : p.snd ∉ S :=
  h.notMem_of_mem_tail _ (snd_mem_tail_support hp)

/-- The last vertex but one of a crossing is in `T`. -/
theorem IsCrossing.penultimate_mem (h : p.IsCrossing S T) (hp : ¬p.Nil) : p.penultimate ∈ T :=
  h.mem_of_mem_dropLast _ (penultimate_mem_dropLast_support hp)

/-- Every vertex of a crossing other than its first is outside `S`. -/
theorem IsCrossing.eq_start_of_mem (h : p.IsCrossing S T) {w : V} (hw : w ∈ p.support)
    (hwS : w ∈ S) : w = u := by
  rcases (mem_support_iff p).1 hw with hw | hw
  · exact hw
  · exact absurd hwS (h.notMem_of_mem_tail w hw)

/-- Every vertex of a crossing other than its last is in `T`. -/
theorem IsCrossing.eq_end_of_notMem (h : p.IsCrossing S T) {w : V} (hw : w ∈ p.support)
    (hwT : w ∉ T) : w = v := by
  rw [← dropLast_support_concat p, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | hw
  · exact absurd (h.mem_of_mem_dropLast w hw) hwT
  · exact hw

/-- **Images.** An injective homomorphism of graphs carries the crossings from `S` out of `T` to
the crossings from the image of `S` out of the image of `T`. -/
theorem isCrossing_map_iff {f : G →g G'} (hf : Function.Injective f) :
    (p.map f).IsCrossing (f '' S) (f '' T) ↔ p.IsCrossing S T := by
  have hmem : ∀ (w : V) (X : Set V), f w ∈ f '' X ↔ w ∈ X := fun w X => hf.mem_set_image
  constructor
  · intro h
    refine ⟨(hmem _ _).1 h.start_mem, fun w hw => ?_, fun hv => h.end_notMem ((hmem _ _).2 hv),
      fun w hw => (hmem _ _).1 (h.mem_of_mem_dropLast _ ?_)⟩
    · rw [← hmem]
      refine h.notMem_of_mem_tail _ ?_
      rw [support_map, ← List.map_tail]
      exact List.mem_map_of_mem hw
    · rw [support_map, ← List.map_dropLast]
      exact List.mem_map_of_mem hw
  · intro h
    refine ⟨(hmem _ _).2 h.start_mem, fun w hw => ?_, fun hv => h.end_notMem ((hmem _ _).1 hv),
      fun w hw => ?_⟩
    · rw [support_map, ← List.map_tail] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      rw [hmem]
      exact h.notMem_of_mem_tail w' hw'
    · rw [support_map, ← List.map_dropLast] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      exact (hmem _ _).2 (h.mem_of_mem_dropLast w' hw')

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Boundaries of boxes and nearest-neighbour steps -/

/-- A point of a box of `ℤ^d` with a neighbour outside the box lies on its boundary. -/
theorem mem_boxBoundary_of_adj {d : ℕ} {lo hi u v : LatticeSite d} (h : (zdGraph d).Adj u v)
    (hu : u ∈ Icc lo hi) (hv : v ∉ Icc lo hi) : u ∈ boxBoundary lo hi := by
  refine ⟨hu, ?_⟩
  simp only [mem_Icc, Pi.le_def, not_and_or, not_forall, not_le] at hu hv
  rcases hv with ⟨i, hi⟩ | ⟨i, hi⟩
  · have := apply_le_apply_add_one_of_adj h.symm i
    have := hu.1 i
    exact ⟨i, Or.inl (by omega)⟩
  · have := apply_le_apply_add_one_of_adj h i
    have := hu.2 i
    exact ⟨i, Or.inr (by omega)⟩

/-! ### Faces of boxes and of dual edges -/

section Faces

variable {d : ℕ}

/-- A corner `x` of a face `f` of the box `Icc lo hi`, the face `f` read as a dual vertex in the
box `Icc lo (hi - 1)` of the faces of the box, lies in the box. -/
theorem mem_Icc_of_mem_Icc_sub_one {lo hi f x : LatticeSite d} (hf : f ∈ Icc lo (hi - 1))
    (hx : x ∈ Icc f (f + 1)) : x ∈ Icc lo hi :=
  ⟨hf.1.trans hx.1, fun i => by
    have h₁ : x i ≤ f i + 1 := hx.2 i
    have h₂ : f i ≤ hi i - 1 := hf.2 i
    change x i ≤ hi i
    omega⟩

/-- A face with a corner in the box `Icc lo hi` lies in the box `Icc (lo - 1) hi` of the faces
touching it. -/
theorem mem_Icc_sub_one_of_mem_Icc {lo hi f x : LatticeSite d} (hx : x ∈ Icc lo hi)
    (hxf : x ∈ Icc f (f + 1)) : f ∈ Icc (lo - 1) hi :=
  ⟨fun i => by
    have h₁ : lo i ≤ x i := hx.1 i
    have h₂ : x i ≤ f i + 1 := hxf.2 i
    change lo i - 1 ≤ f i
    omega, fun i => (hxf.1 i).trans (hx.2 i)⟩

end Faces

/-- The ends of an edge are corners of both faces of its dual edge. -/
theorem mem_Icc_of_mem_dualEdge {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    {x h : LatticeSite 2} (hx : x ∈ e) (hh : h ∈ dualEdge e) : x ∈ Icc h (h + 1) := by
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.one_apply]
  obtain ⟨a, b, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hh
    rw [Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hx
    omega
  · rw [dualEdge_vertical, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hh
    rw [Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hx
    omega

/-! ### Arms -/

section Arms

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}

/-- An **open arm** of `ω` from `B_r(z)` to the boundary of the box `Icc lo hi`: a walk of `ℤ²`
along edges open in `ω` that starts in the box `B_r(z) = z + [-r, r]²` and never returns to it,
and stays in the interior `Icc (lo + 1) (hi - 1)` of the outer box up to its last vertex, which
is outside the interior. When `B_r(z)` lies in the interior, the arm starts on the boundary of
`B_r(z)`, lies in `Icc lo hi`, and meets the boundary of `Icc lo hi` exactly at its last vertex
(`IsOpenArm.start_mem_boxBoundary`, `IsOpenArm.mem_Icc`, `IsOpenArm.end_mem_boxBoundary`). For
`r = 0` the box `B_0(z)` is the vertex `z`. -/
structure IsOpenArm (ω : Config (LatticeSite 2)) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) : Prop where
  /-- The walk crosses from `B_r(z)` out of the interior of the outer box. -/
  isCrossing : γ.IsCrossing (Icc (z - r) (z + r)) (Icc (lo + 1) (hi - 1))
  /-- Its edges are open. -/
  mem_of_mem_edges : ∀ e ∈ γ.edges, e ∈ ω

/-- A **dual arm** of `ω` from `B_r(z)` to the boundary of the box `Icc lo hi`: a walk of faces
(the dual vertex `f` standing for the unit square with lower-left corner `f`) along dual edges
open in `dualConfig ω`, that starts at a face touching `B_r(z)` (a face of
`Icc (z - r - 1) (z + r)`) and never touches `B_r(z)` again, and runs through faces of the outer
box (faces of `Icc lo (hi - 1)`) up to its last face, which is outside the outer box. Its last
dual edge crosses an edge of the boundary of `Icc lo hi`; every dual edge it uses crosses an edge
with both ends in `Icc lo hi`, as in quad duality. For `r = 0` the first face is one of the four
faces at `z`. -/
structure IsDualArm (ω : Config (LatticeSite 2)) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) {f g : LatticeSite 2} (γ : (zdGraph 2).Walk f g) : Prop where
  /-- The walk of faces crosses from the faces touching `B_r(z)` out of the faces of the outer
  box. -/
  isCrossing : γ.IsCrossing (Icc (z - r - 1) (z + r)) (Icc lo (hi - 1))
  /-- Its dual edges are open. -/
  mem_of_mem_edges : ∀ e ∈ γ.edges, e ∈ dualConfig ω

/-- An **arm of colour `c`**: an open arm when `c = true`, a dual arm when `c = false`. -/
def IsArm (ω : Config (LatticeSite 2)) (c : Bool) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) : Prop :=
  cond c (IsOpenArm ω z r lo hi γ) (IsDualArm ω z r lo hi γ)

section ArmsAPI

variable {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

@[simp]
theorem isArm_true : IsArm ω true z r lo hi γ ↔ IsOpenArm ω z r lo hi γ :=
  Iff.rfl

@[simp]
theorem isArm_false : IsArm ω false z r lo hi γ ↔ IsDualArm ω z r lo hi γ :=
  Iff.rfl

theorem isOpenArm_iff : IsOpenArm ω z r lo hi γ ↔
    γ.IsCrossing (Icc (z - r) (z + r)) (Icc (lo + 1) (hi - 1)) ∧ ∀ e ∈ γ.edges, e ∈ ω :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem isDualArm_iff : IsDualArm ω z r lo hi γ ↔
    γ.IsCrossing (Icc (z - r - 1) (z + r)) (Icc lo (hi - 1)) ∧
      ∀ e ∈ γ.edges, e ∈ dualConfig ω :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The box `B_r(z)` lies in the interior of `Icc lo hi` exactly when the faces touching it are
faces of `Icc lo hi`. -/
theorem Icc_sub_one_subset_iff :
    Icc (z - r - 1) (z + r) ⊆ Icc lo (hi - 1) ↔ Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1) := by
  have hne₁ : z - r - 1 ≤ z + r := fun i => by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hne₂ : z - r ≤ z + r := fun i => by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    omega
  rw [Icc_subset_Icc_iff hne₁, Icc_subset_Icc_iff hne₂]
  simp only [Pi.le_def, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i => by have := h₁ i; omega, fun i => h₂ i⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i => by have := h₁ i; omega, fun i => h₂ i⟩

/-- A neighbour of a point of the interior `Icc (lo + 1) (hi - 1)` lies in `Icc lo hi`. -/
theorem mem_Icc_of_adj_of_mem_Icc_sub_one {u v : LatticeSite 2}
    (huv : (zdGraph 2).Adj u v) (hu : u ∈ Icc (lo + 1) (hi - 1)) : v ∈ Icc lo hi := by
  have h₀ := apply_le_apply_add_one_of_adj huv
  have h₁ := apply_le_apply_add_one_of_adj huv.symm
  rw [mem_Icc_two_iff] at hu ⊢
  have a0 := h₀ 0
  have a1 := h₀ 1
  have b0 := h₁ 0
  have b1 := h₁ 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hu
  omega

namespace IsOpenArm

variable (h : IsOpenArm ω z r lo hi γ)
include h

/-- An open arm meets `B_r(z)` only at its first vertex. -/
theorem eq_start_of_mem {v : LatticeSite 2} (hv : v ∈ γ.support)
    (hvB : v ∈ Icc (z - r) (z + r)) : v = a :=
  h.isCrossing.eq_start_of_mem hv hvB

/-- An open arm meets the boundary of the outer box only at its last vertex. -/
theorem eq_end_of_mem_boxBoundary {v : LatticeSite 2} (hv : v ∈ γ.support)
    (hvO : v ∈ boxBoundary lo hi) : v = b := by
  refine h.isCrossing.eq_end_of_notMem hv fun hv' => ?_
  rw [boxBoundary_eq_Icc_diff_Icc] at hvO
  exact hvO.2 hv'

/-- An open arm from a box inside the interior of the outer box has at least one step. -/
theorem not_nil (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) : ¬γ.Nil :=
  h.isCrossing.not_nil hB

/-- An open arm with at least one step starts on the boundary of `B_r(z)`. -/
theorem start_mem_boxBoundary (hγ : ¬γ.Nil) :
    a ∈ boxBoundary (z - r : LatticeSite 2) (z + r) :=
  mem_boxBoundary_of_adj (SimpleGraph.Walk.adj_snd hγ) h.isCrossing.start_mem
    (h.isCrossing.snd_notMem hγ)

/-- An open arm with at least one step ends on the boundary of the outer box. -/
theorem end_mem_boxBoundary (hγ : ¬γ.Nil) : b ∈ boxBoundary lo hi := by
  rw [boxBoundary_eq_Icc_diff_Icc]
  exact ⟨mem_Icc_of_adj_of_mem_Icc_sub_one (SimpleGraph.Walk.adj_penultimate hγ)
    (h.isCrossing.penultimate_mem hγ), h.isCrossing.end_notMem⟩

/-- An open arm with at least one step lies in the outer box. -/
theorem mem_Icc (hγ : ¬γ.Nil) {v : LatticeSite 2} (hv : v ∈ γ.support) : v ∈ Icc lo hi := by
  by_cases hvb : v = b
  · rw [hvb]
    exact boxBoundary_subset_Icc _ _ (h.end_mem_boxBoundary hγ)
  · have hv' : v ∈ Icc (lo + 1) (hi - 1) := by
      by_contra hc
      exact hvb (h.isCrossing.eq_end_of_notMem hv hc)
    rw [mem_Icc_two_iff] at hv' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hv'
    omega

/-- Each edge of an open arm has both ends in the outer box and an end outside `B_r(z)`. -/
theorem exists_notMem_of_mem_edges {e : Sym2 (LatticeSite 2)} (he : e ∈ γ.edges) :
    (∀ v ∈ e, v ∈ Icc lo hi) ∧ ∃ v ∈ e, v ∉ Icc (z - r) (z + r) := by
  unfold SimpleGraph.Walk.edges at he
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 he
  have hfst : δ.fst ∈ Icc (lo + 1) (hi - 1) := h.isCrossing.mem_of_mem_dropLast _ (by
    rw [← SimpleGraph.Walk.map_fst_darts]
    exact List.mem_map_of_mem hδ)
  have hsnd : δ.snd ∉ Icc (z - r) (z + r) := h.isCrossing.notMem_of_mem_tail _ (by
    rw [← SimpleGraph.Walk.map_snd_darts]
    exact List.mem_map_of_mem hδ)
  have hfst' : δ.fst ∈ Icc lo hi := by
    rw [mem_Icc_two_iff] at hfst ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hfst
    omega
  have hsnd' : δ.snd ∈ Icc lo hi := mem_Icc_of_adj_of_mem_Icc_sub_one δ.adj hfst
  refine ⟨fun v hv => ?_, δ.snd, by simp [SimpleGraph.Dart.edge], hsnd⟩
  rw [SimpleGraph.Dart.edge, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact hfst'
  · exact hsnd'

end IsOpenArm

namespace IsDualArm

variable (h : IsDualArm ω z r lo hi γ)
include h

/-- A dual arm touches `B_r(z)` only at its first face. -/
theorem eq_start_of_mem {f : LatticeSite 2} (hf : f ∈ γ.support)
    (hfB : f ∈ Icc (z - r - 1) (z + r)) : f = a :=
  h.isCrossing.eq_start_of_mem hf hfB

/-- A dual arm leaves the faces of the outer box only at its last face. -/
theorem eq_end_of_notMem {f : LatticeSite 2} (hf : f ∈ γ.support)
    (hfO : f ∉ Icc lo (hi - 1)) : f = b :=
  h.isCrossing.eq_end_of_notMem hf hfO

/-- A dual arm from a box inside the interior of the outer box has at least one step. -/
theorem not_nil (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) : ¬γ.Nil :=
  h.isCrossing.not_nil (Icc_sub_one_subset_iff.2 hB)

/-- A dual arm with at least one step starts at a face touching `B_r(z)` but not inside it. -/
theorem start_mem_boxBoundary (hγ : ¬γ.Nil) :
    a ∈ boxBoundary (z - r - 1 : LatticeSite 2) (z + r) :=
  mem_boxBoundary_of_adj (SimpleGraph.Walk.adj_snd hγ) h.isCrossing.start_mem
    (h.isCrossing.snd_notMem hγ)

/-- A dual arm with at least one step ends at a face outside the outer box with an edge on its
boundary. -/
theorem end_mem_boxBoundary (hγ : ¬γ.Nil) : b ∈ boxBoundary (lo - 1) hi := by
  have hpen := h.isCrossing.penultimate_mem hγ
  have hadj := SimpleGraph.Walk.adj_penultimate hγ
  have hb := h.isCrossing.end_notMem
  have h₀ := apply_le_apply_add_one_of_adj hadj
  have h₁ := apply_le_apply_add_one_of_adj hadj.symm
  rw [boxBoundary_eq_Icc_diff_Icc, mem_sdiff]
  rw [mem_Icc_two_iff] at hpen hb ⊢
  rw [mem_Icc_two_iff]
  have a0 := h₀ 0
  have a1 := h₀ 1
  have b0 := h₁ 0
  have b1 := h₁ 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, sub_add_cancel] at hpen hb ⊢
  omega

/-- A dual arm with at least one step runs through faces touching the outer box. -/
theorem mem_Icc (hγ : ¬γ.Nil) {f : LatticeSite 2} (hf : f ∈ γ.support) :
    f ∈ Icc (lo - 1) hi := by
  by_cases hfb : f = b
  · rw [hfb]
    exact boxBoundary_subset_Icc _ _ (h.end_mem_boxBoundary hγ)
  · have hf' : f ∈ Icc lo (hi - 1) := by
      by_contra hc
      exact hfb (h.isCrossing.eq_end_of_notMem hf hc)
    rw [mem_Icc_two_iff] at hf' ⊢
    simp only [Pi.sub_apply, Pi.one_apply] at hf' ⊢
    omega

/-- **Dual arms cross only edges of the outer box.** Each dual edge of a dual arm is the dual of
a closed edge of `ℤ²` with both ends in the outer box `Icc lo hi` and no end in `B_r(z)`. So a
dual arm is a dual-open path for the dual configuration restricted to the edges of the box, as
in quad duality. -/
theorem exists_mem_edgeSet_of_mem_edges {E : Sym2 (LatticeSite 2)} (hE : E ∈ γ.edges) :
    ∃ e ∈ (zdGraph 2).edgeSet, e ∉ ω ∧ dualEdge e = E ∧ (∀ v ∈ e, v ∈ Icc lo hi) ∧
      ∀ v ∈ e, v ∉ Icc (z - r) (z + r) := by
  obtain ⟨e, he, heω, rfl⟩ := (mem_dualConfig_iff' ω E).1 (h.mem_of_mem_edges E hE)
  unfold SimpleGraph.Walk.edges at hE
  obtain ⟨δ, hδ, hδe⟩ := List.mem_map.1 hE
  have hfst : δ.fst ∈ Icc lo (hi - 1) := h.isCrossing.mem_of_mem_dropLast _ (by
    rw [← SimpleGraph.Walk.map_fst_darts]
    exact List.mem_map_of_mem hδ)
  have hsnd : δ.snd ∉ Icc (z - r - 1) (z + r) := h.isCrossing.notMem_of_mem_tail _ (by
    rw [← SimpleGraph.Walk.map_snd_darts]
    exact List.mem_map_of_mem hδ)
  have hfst' : δ.fst ∈ dualEdge e := by
    rw [← hδe, SimpleGraph.Dart.edge]
    exact Sym2.mem_mk_left _ _
  have hsnd' : δ.snd ∈ dualEdge e := by
    rw [← hδe, SimpleGraph.Dart.edge]
    exact Sym2.mem_mk_right _ _
  refine ⟨e, he, heω, rfl, fun v hv => ?_, fun v hv hvB => ?_⟩
  · exact mem_Icc_of_mem_Icc_sub_one hfst (mem_Icc_of_mem_dualEdge he hv hfst')
  · exact hsnd (mem_Icc_sub_one_of_mem_Icc hvB (mem_Icc_of_mem_dualEdge he hv hsnd'))

end IsDualArm

/-! #### Determination by the annulus -/

/-- **Determination.** An open arm of `ω` is an open arm of every `ω'` that agrees with `ω` on
the edges of the outer box with an end outside `B_r(z)`. -/
theorem IsOpenArm.of_agree {ω' : Config (LatticeSite 2)} (h : IsOpenArm ω z r lo hi γ)
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc lo hi) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω')) :
    IsOpenArm ω' z r lo hi γ := by
  refine ⟨h.isCrossing, fun e he => ?_⟩
  obtain ⟨h₁, h₂⟩ := h.exists_notMem_of_mem_edges he
  exact (hω e (γ.edges_subset_edgeSet he) h₁ h₂).1 (h.mem_of_mem_edges e he)

/-- **Determination.** A dual arm of `ω` is a dual arm of every `ω'` that agrees with `ω` on
the edges of the outer box with an end outside `B_r(z)`. -/
theorem IsDualArm.of_agree {ω' : Config (LatticeSite 2)} (h : IsDualArm ω z r lo hi γ)
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc lo hi) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω')) :
    IsDualArm ω' z r lo hi γ := by
  refine ⟨h.isCrossing, fun E hE => ?_⟩
  obtain ⟨e, he, heω, rfl, h₁, h₂⟩ := h.exists_mem_edgeSet_of_mem_edges hE
  have hne : ∃ v ∈ e, v ∉ Icc (z - r) (z + r) := by
    induction e using Sym2.ind with
    | h x y => exact ⟨x, Sym2.mem_mk_left x y, h₂ x (Sym2.mem_mk_left x y)⟩
  rw [dualEdge_mem_dualConfig_iff he, ← hω e he h₁ hne]
  exact heω

/-- **Determination.** An arm of `ω` is an arm of every `ω'` that agrees with `ω` on the edges
of the outer box with an end outside `B_r(z)`. -/
theorem IsArm.of_agree {ω' : Config (LatticeSite 2)} {c : Bool} (h : IsArm ω c z r lo hi γ)
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc lo hi) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω')) :
    IsArm ω' c z r lo hi γ := by
  cases c
  · exact IsDualArm.of_agree h hω
  · exact IsOpenArm.of_agree h hω

/-! #### Translation -/

/-- **Translation.** Translating the configuration, the walk and the boxes by `c` carries arms to
arms. Here `f` is the translation by `c`, as a homomorphism of `ℤ²`. -/
theorem IsArm.map_add {col : Bool} {f : zdGraph 2 →g zdGraph 2} {c : LatticeSite 2}
    (hf : ∀ x, f x = x + c) (h : IsArm ω col z r lo hi γ) :
    IsArm (Sym2.map (· + c) '' ω) col (z + c) r (lo + c) (hi + c) (γ.map f) := by
  have hf' : (⇑f : LatticeSite 2 → LatticeSite 2) = (· + c) := funext hf
  have hinj : Function.Injective f := by
    rw [hf']
    exact add_left_injective c
  have himage : ∀ p q : LatticeSite 2, ⇑f '' Icc p q = Icc (p + c) (q + c) := fun p q => by
    rw [hf', image_add_const_Icc]
  have hedges : ∀ (ω₀ : Config (LatticeSite 2)), (∀ e ∈ γ.edges, e ∈ ω₀) →
      ∀ e ∈ (γ.map f).edges, e ∈ Sym2.map (· + c) '' ω₀ := by
    intro ω₀ h₀ e he
    rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    rw [hf']
    exact ⟨e₀, h₀ e₀ he₀, rfl⟩
  cases col
  · refine ⟨?_, ?_⟩
    · have := (SimpleGraph.Walk.isCrossing_map_iff hinj).2 h.isCrossing
      rwa [himage, himage, show z - r - 1 + c = z + c - r - 1 by abel,
        show z + r + c = z + c + r by abel, show hi - 1 + c = hi + c - 1 by abel] at this
    · rw [dualConfig_image_add]
      exact hedges _ h.mem_of_mem_edges
  · refine ⟨?_, ?_⟩
    · have := (SimpleGraph.Walk.isCrossing_map_iff hinj).2 h.isCrossing
      rwa [himage, himage, show z - r + c = z + c - r by abel,
        show z + r + c = z + c + r by abel, show lo + 1 + c = lo + c + 1 by abel,
        show hi - 1 + c = hi + c - 1 by abel] at this
    · exact hedges _ h.mem_of_mem_edges

end ArmsAPI

end Arms

/-! ### Disjoint families of arms -/

/-- A family of arms with colours `σ` is **disjoint** when two open arms share no vertex except
possibly their first one and two dual arms share no face. (An open arm and a dual arm of one
configuration never cross: an open edge is not crossed by an open dual edge.) For `r = 0` the
open arms all start at the centre. Two open arms may share their first vertex for every `r`, so
for `r ≥ 1` this is weaker than vertex-disjointness: two arms may leave `B_r(z)` from the same
boundary vertex. -/
def ArmsDisjoint {j : ℕ} (σ : Fin j → Bool) {a b : Fin j → LatticeSite 2}
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)) : Prop :=
  (∀ i k, i ≠ k → σ i = true → σ k = true → ∀ v ∈ (γ i).support.tail, v ∉ (γ k).support) ∧
    ∀ i k, i ≠ k → σ i = false → σ k = false → ∀ v ∈ (γ i).support, v ∉ (γ k).support

/-- **Images.** An injective map of `ℤ²` keeps a family of arms disjoint. -/
theorem ArmsDisjoint.map {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (h : ArmsDisjoint σ γ) {f : zdGraph 2 →g zdGraph 2}
    (hf : Function.Injective f) : ArmsDisjoint σ fun i => (γ i).map f := by
  refine ⟨fun i k hik hi hk v hv hv' => ?_, fun i k hik hi hk v hv hv' => ?_⟩
  · rw [SimpleGraph.Walk.support_map, ← List.map_tail] at hv
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    obtain ⟨w', hw', hww'⟩ := List.mem_map.1 hv'
    rw [hf hww'] at hw'
    exact h.1 i k hik hi hk w hw hw'
  · rw [SimpleGraph.Walk.support_map] at hv hv'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    obtain ⟨w', hw', hww'⟩ := List.mem_map.1 hv'
    rw [hf hww'] at hw'
    exact h.2 i k hik hi hk w hw hw'

/-- A family of at most one arm is disjoint. -/
theorem armsDisjoint_of_subsingleton {j : ℕ} (hj : j ≤ 1) (σ : Fin j → Bool)
    {a b : Fin j → LatticeSite 2} (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)) : ArmsDisjoint σ γ :=
  ⟨fun i k hik => absurd (Fin.ext (by omega)) hik, fun i k hik => absurd (Fin.ext (by omega)) hik⟩

/-! ### Positions of arms on the doubled lattice -/

/-- The **inner position** of an arm of colour `c` from `B_r(z)`: in the doubled lattice, where
the point `v` of `ℤ²` becomes `2v`, the face `f` becomes its centre `2f + (1, 1)` and an edge
becomes its midpoint (the sum of its ends), the perimeter position on the boundary of the box
`2z + [-(2r + 1), 2r + 1]²` of the midpoint of the first edge of an open arm, or of the centre of
the first face of a dual arm. Open and dual arms leaving `B_r(z)` pass there, between the
doubled box `2 B_r(z)` and the doubled faces around it, so the positions of the arms of a family
lie on one cycle (of perimeter `16 r + 8`). -/
def innerPos (z : LatticeSite 2) (r : ℕ) (c : Bool) {a b : LatticeSite 2}
    (γ : (zdGraph 2).Walk a b) : ℤ :=
  perimeterPos (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
    (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) (cond c (a + γ.snd) (2 • a + 1))

/-- The **landing position** of an arm of colour `c` on the boundary of `Icc lo hi`: in the
doubled lattice, the perimeter position on the boundary of `Icc (2 lo) (2 hi)` of twice the last
vertex of an open arm, or of the midpoint of the boundary edge crossed by the last dual edge of a
dual arm (the sum of its last two faces plus `(1, 1)`). The positions of the arms of a family lie
on one cycle (of perimeter `4 (hi₀ - lo₀) + 4 (hi₁ - lo₁)`); an open arm landing at `v` has
position `2 · perimeterPos lo hi v`, and a dual arm crossing the boundary edge `{x, y}` has
position `2 · perimeterPos lo hi x + 1` when `y` follows `x` counterclockwise. -/
def landingPos (lo hi : LatticeSite 2) (c : Bool) {a b : LatticeSite 2}
    (γ : (zdGraph 2).Walk a b) : ℤ :=
  perimeterPos (2 • lo) (2 • hi) (cond c (2 • b) (γ.penultimate + b + 1))

section Positions

variable {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b)

@[simp]
theorem innerPos_true (z : LatticeSite 2) (r : ℕ) :
    innerPos z r true γ = perimeterPos (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) (a + γ.snd) :=
  rfl

@[simp]
theorem innerPos_false (z : LatticeSite 2) (r : ℕ) :
    innerPos z r false γ = perimeterPos (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) (2 • a + 1) :=
  rfl

/-- **Doubling.** Doubling a box and a point doubles its perimeter position. -/
@[simp]
theorem perimeterPos_two_smul (lo hi v : LatticeSite 2) :
    perimeterPos (2 • lo) (2 • hi) (2 • v) = 2 * perimeterPos lo hi v := by
  unfold perimeterPos
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> omega

/-- An open arm landing at `b` has landing position `2 · perimeterPos lo hi b`. -/
@[simp]
theorem landingPos_true (lo hi : LatticeSite 2) :
    landingPos lo hi true γ = 2 * perimeterPos lo hi b :=
  perimeterPos_two_smul lo hi b

@[simp]
theorem landingPos_false (lo hi : LatticeSite 2) :
    landingPos lo hi false γ = perimeterPos (2 • lo) (2 • hi) (γ.penultimate + b + 1) :=
  rfl

/-- **Translation.** Translating a walk and the centre by `c` keeps the inner position. -/
theorem innerPos_map_add {f : zdGraph 2 →g zdGraph 2} {c : LatticeSite 2} (hf : ∀ x, f x = x + c)
    (z : LatticeSite 2) (r : ℕ) (col : Bool) :
    innerPos (z + c) r col (γ.map f) = innerPos z r col γ := by
  have hsnd : (γ.map f).snd = γ.snd + c := by
    rw [SimpleGraph.Walk.snd, SimpleGraph.Walk.getVert_map, hf]
  have e₁ : 2 • (z + c) - ((2 * r + 1 : ℕ) : LatticeSite 2) =
      2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2) + 2 • c := by
    rw [smul_add]
    abel
  have e₂ : 2 • (z + c) + ((2 * r + 1 : ℕ) : LatticeSite 2) =
      2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2) + 2 • c := by
    rw [smul_add]
    abel
  cases col
  · rw [innerPos_false, innerPos_false, e₁, e₂, hf, show 2 • (a + c) + 1 = 2 • a + 1 + 2 • c by
      rw [smul_add]
      abel, perimeterPos_add]
  · rw [innerPos_true, innerPos_true, e₁, e₂, hsnd, hf, show a + c + (γ.snd + c) =
      a + γ.snd + 2 • c by rw [two_smul]; abel, perimeterPos_add]

/-- **Translation.** Translating a walk and the box by `c` keeps the landing position. -/
theorem landingPos_map_add {f : zdGraph 2 →g zdGraph 2} {c : LatticeSite 2}
    (hf : ∀ x, f x = x + c) (lo hi : LatticeSite 2) (col : Bool) :
    landingPos (lo + c) (hi + c) col (γ.map f) = landingPos lo hi col γ := by
  have hpen : (γ.map f).penultimate = γ.penultimate + c := by
    rw [SimpleGraph.Walk.penultimate, SimpleGraph.Walk.getVert_map, SimpleGraph.Walk.length_map,
      hf]
  cases col
  · rw [landingPos_false, landingPos_false, hpen, hf, smul_add, smul_add,
      show γ.penultimate + c + (b + c) + 1 = γ.penultimate + b + 1 + 2 • c by
        rw [two_smul]; abel, perimeterPos_add]
  · rw [landingPos_true, landingPos_true, hf, perimeterPos_add]

end Positions


/-! ### Colour inversion -/

/-- **The dual of the dual configuration** is the configuration translated by `(-1, -1)`, on the
edges of `ℤ²`: the dual of the dual lattice is `ℤ²` shifted by twice half a lattice step
(`dualEdge_dualEdge`). -/
theorem dualConfig_dualConfig (ω : Config (LatticeSite 2)) :
    dualConfig (dualConfig ω) = Sym2.map (· - 1) '' (ω ∩ (zdGraph 2).edgeSet) := by
  have hback : ∀ e : Sym2 (LatticeSite 2), Sym2.map (· - 1) (Sym2.map (· + 1) e) = e := by
    intro e
    have h : ((fun v : LatticeSite 2 => v - 1) ∘ fun v => v + 1) = id := by
      funext v
      simp
    rw [Sym2.map_map, h, Sym2.map_id, id]
  ext E
  rw [mem_dualConfig_iff']
  constructor
  · rintro ⟨e, he, heω, rfl⟩
    have hg : Sym2.map (· + 1) (dualEdge e) ∈ ω := by
      by_contra hc
      exact heω ((mem_dualConfig_iff ω e).2 ⟨he, hc⟩)
    exact ⟨_, ⟨hg, map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet he)⟩, hback _⟩
  · rintro ⟨g, ⟨hgω, hg⟩, rfl⟩
    refine ⟨dualEdge g, dualEdge_mem_edgeSet hg, fun h => ?_, dualEdge_dualEdge hg⟩
    have := ((mem_dualConfig_iff ω _).1 h).2
    rw [map_add_one_dualEdge_dualEdge hg] at this
    exact this hgω

section ColourInversion

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **Colour inversion for open arms.** The open arms of the dual configuration are the walks of
faces with dual edges open in `dualConfig ω` that cross from `B_r(z)` out of the interior of the
outer box (read as boxes of faces). -/
theorem isOpenArm_dualConfig_iff : IsOpenArm (dualConfig ω) z r lo hi γ ↔
    γ.IsCrossing (Icc (z - r) (z + r)) (Icc (lo + 1) (hi - 1)) ∧
      ∀ e ∈ γ.edges, e ∈ dualConfig ω :=
  isOpenArm_iff

/-- **Colour inversion for dual arms.** A walk `γ` of faces is a dual arm of the dual
configuration exactly when its translate by `(1, 1)` is a walk of `ℤ²` along edges open in `ω`
crossing from the box `Icc (z - r) (z + r + 1)` out of the box `Icc (lo + 1) hi`: the boxes of
an open arm of `ω`, moved by half a lattice step towards `(1, 1)` at their upper corners. Here
`f` is the translation by `(1, 1)`. -/
theorem isDualArm_dualConfig_iff {f : zdGraph 2 →g zdGraph 2} (hf : ∀ x, f x = x + 1) :
    IsDualArm (dualConfig ω) z r lo hi γ ↔
      (γ.map f).IsCrossing (Icc (z - r) (z + r + 1)) (Icc (lo + 1) hi) ∧
        ∀ e ∈ (γ.map f).edges, e ∈ ω := by
  have hf' : (⇑f : LatticeSite 2 → LatticeSite 2) = (· + 1) := funext hf
  have hinj : Function.Injective f := by
    rw [hf']
    exact add_left_injective 1
  have himage : ∀ p q : LatticeSite 2, ⇑f '' Icc p q = Icc (p + 1) (q + 1) := fun p q => by
    rw [hf', image_add_const_Icc]
  have hcross : γ.IsCrossing (Icc (z - r - 1) (z + r)) (Icc lo (hi - 1)) ↔
      (γ.map f).IsCrossing (Icc (z - r) (z + r + 1)) (Icc (lo + 1) hi) := by
    rw [← SimpleGraph.Walk.isCrossing_map_iff hinj, himage, himage, sub_add_cancel,
      sub_add_cancel]
  have hedge : ∀ e ∈ γ.edges, (e ∈ dualConfig (dualConfig ω) ↔ Sym2.map (· + 1) e ∈ ω) := by
    intro e he
    have heE := γ.edges_subset_edgeSet he
    rw [dualConfig_dualConfig]
    constructor
    · rintro ⟨g, ⟨hgω, -⟩, rfl⟩
      have h : ((fun v : LatticeSite 2 => v + 1) ∘ fun v => v - 1) = id := by
        funext v
        simp
      rwa [Sym2.map_map, h, Sym2.map_id, id]
    · intro h
      refine ⟨_, ⟨h, map_add_mem_edgeSet 1 heE⟩, ?_⟩
      have h' : ((fun v : LatticeSite 2 => v - 1) ∘ fun v => v + 1) = id := by
        funext v
        simp
      rw [Sym2.map_map, h', Sym2.map_id, id]
  rw [isDualArm_iff, hcross]
  refine and_congr_right fun _ => ?_
  rw [SimpleGraph.Walk.edges_map, hf']
  constructor
  · intro h e he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    exact (hedge e₀ he₀).1 (h e₀ he₀)
  · intro h e he
    exact (hedge e he).2 (h _ (List.mem_map_of_mem he))

end ColourInversion

/-! ### Multi-arm events -/

/-- The **`j`-arm event with colours `σ` and windows**, from `B_r(z)` to the boundary of the
box `Icc lo hi`: there is a disjoint family of `j` arms (`ArmsDisjoint`), arm `i` open when
`σ i = true` and dual when `σ i = false`, the inner position of arm `i` in the window `J i` and
its landing position in the window `I i`, landing in counterclockwise order: for `i < k < l`
the landing positions of the arms `i`, `k`, `l` are in strict cyclic order (`sbtw`, for the
circular order of `ℤ`). Positions are perimeter positions on the doubled lattice (`innerPos`,
`landingPos`). The event is meant for `B_r(z)` inside `Icc (lo + 1) (hi - 1)`; otherwise a walk
of length zero at a vertex of `B_r(z)` outside that box is an open arm, so that for example
`multiArmEvent (fun _ : Fin 1 => true) z r R = univ` when `R ≤ r`. -/
def multiArmEventTo {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) (J I : Fin j → Set ℤ) : Set (Config (LatticeSite 2)) :=
  {ω | ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, IsArm ω (σ i) z r lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
    (∀ i, innerPos z r (σ i) (γ i) ∈ J i ∧ landingPos lo hi (σ i) (γ i) ∈ I i) ∧
    ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
      (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))}

/-- The `j`-arm event with colours `σ` and windows in the annulus between `B_r(z)` and
`B_R(z)`. -/
abbrev multiArmEventIn {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ)
    (J I : Fin j → Set ℤ) : Set (Config (LatticeSite 2)) :=
  multiArmEventTo σ z r (z - R) (z + R) J I

/-- The **`j`-arm event** `A_σ(r, R)` at `z`: `j` disjoint arms of colours `σ` in
counterclockwise order, from `B_r(z)` to the boundary of `B_R(z)`. -/
abbrev multiArmEvent {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) :
    Set (Config (LatticeSite 2)) :=
  multiArmEventIn σ z r R (fun _ => univ) (fun _ => univ)

/-- The **half-plane `j`-arm event with colours `σ` and windows**, from `B_r(z)` to the boundary
of the box `Icc lo hi`, in the upper half-plane `{v | z 1 ≤ v 1}` through `z`: as
`multiArmEventTo`, with every arm in the half-plane (the vertices of an open arm, the lower-left
corners of the faces of a dual arm) and the landing positions increasing with `i`. For a box
reaching below the line, so that `lo 1 < z 1`, the part of its boundary in the half-plane runs
counterclockwise from its right end to its left end, and the arms are ordered from the right
end. -/
def halfArmEventTo {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) (J I : Fin j → Set ℤ) : Set (Config (LatticeSite 2)) :=
  {ω | ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, IsArm ω (σ i) z r lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
    (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
    (∀ i, innerPos z r (σ i) (γ i) ∈ J i ∧ landingPos lo hi (σ i) (γ i) ∈ I i) ∧
    StrictMono fun i => landingPos lo hi (σ i) (γ i)}

/-- The half-plane `j`-arm event with colours `σ` and windows in the half-annulus between
`B_r(z)` and `B_R(z)`. -/
abbrev halfArmEventIn {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ)
    (J I : Fin j → Set ℤ) : Set (Config (LatticeSite 2)) :=
  halfArmEventTo σ z r (z - R) (z + R) J I

/-- The **half-plane `j`-arm event** at `z`: `j` disjoint arms of colours `σ` in the upper
half-plane through `z`, from `B_r(z)` to the boundary of `B_R(z)`, ordered from the right. -/
abbrev halfArmEvent {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) :
    Set (Config (LatticeSite 2)) :=
  halfArmEventIn σ z r R (fun _ => univ) (fun _ => univ)

section Events

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
  {J I : Fin j → Set ℤ} {ω : Config (LatticeSite 2)}

theorem mem_multiArmEventTo_iff : ω ∈ multiArmEventTo σ z r lo hi J I ↔
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, innerPos z r (σ i) (γ i) ∈ J i ∧ landingPos lo hi (σ i) (γ i) ∈ I i) ∧
      ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
        (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l)) :=
  Iff.rfl

theorem mem_multiArmEvent_iff {R : ℕ} : ω ∈ multiArmEvent σ z r R ↔
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      ∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l)) := by
  constructor
  · rintro ⟨a, b, γ, hγ, hd, -, ho⟩
    exact ⟨a, b, γ, hγ, hd, ho⟩
  · rintro ⟨a, b, γ, hγ, hd, ho⟩
    exact ⟨a, b, γ, hγ, hd, fun _ => ⟨mem_univ _, mem_univ _⟩, ho⟩

theorem mem_halfArmEvent_iff {R : ℕ} : ω ∈ halfArmEvent σ z r R ↔
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i) := by
  constructor
  · rintro ⟨a, b, γ, hγ, hd, hH, -, ho⟩
    exact ⟨a, b, γ, hγ, hd, hH, ho⟩
  · rintro ⟨a, b, γ, hγ, hd, hH, ho⟩
    exact ⟨a, b, γ, hγ, hd, hH, fun _ => ⟨mem_univ _, mem_univ _⟩, ho⟩

theorem mem_halfArmEventTo_iff : ω ∈ halfArmEventTo σ z r lo hi J I ↔
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (∀ i, innerPos z r (σ i) (γ i) ∈ J i ∧ landingPos lo hi (σ i) (γ i) ∈ I i) ∧
      StrictMono fun i => landingPos lo hi (σ i) (γ i) :=
  Iff.rfl

/-- **Monotonicity in the windows.** -/
theorem multiArmEventTo_mono {J' I' : Fin j → Set ℤ} (hJ : ∀ i, J i ⊆ J' i)
    (hI : ∀ i, I i ⊆ I' i) : multiArmEventTo σ z r lo hi J I ⊆ multiArmEventTo σ z r lo hi J' I' :=
  fun _ ⟨a, b, γ, hγ, hd, hw, ho⟩ =>
    ⟨a, b, γ, hγ, hd, fun i => ⟨hJ i (hw i).1, hI i (hw i).2⟩, ho⟩

/-- **Monotonicity in the windows.** -/
theorem halfArmEventTo_mono {J' I' : Fin j → Set ℤ} (hJ : ∀ i, J i ⊆ J' i)
    (hI : ∀ i, I i ⊆ I' i) : halfArmEventTo σ z r lo hi J I ⊆ halfArmEventTo σ z r lo hi J' I' :=
  fun _ ⟨a, b, γ, hγ, hd, hH, hw, ho⟩ =>
    ⟨a, b, γ, hγ, hd, hH, fun i => ⟨hJ i (hw i).1, hI i (hw i).2⟩, ho⟩

/-- Arms landing in windows are arms. -/
theorem multiArmEventIn_subset_multiArmEvent {R : ℕ} :
    multiArmEventIn σ z r R J I ⊆ multiArmEvent σ z r R :=
  multiArmEventTo_mono (fun _ => subset_univ _) fun _ => subset_univ _

/-- Arms landing in windows are arms. -/
theorem halfArmEventIn_subset_halfArmEvent {R : ℕ} :
    halfArmEventIn σ z r R J I ⊆ halfArmEvent σ z r R :=
  halfArmEventTo_mono (fun _ => subset_univ _) fun _ => subset_univ _

/-- **Half-plane arms are arms.** Arms in the half-plane landing in increasing order land in
counterclockwise order. -/
theorem halfArmEventTo_subset_multiArmEventTo :
    halfArmEventTo σ z r lo hi J I ⊆ multiArmEventTo σ z r lo hi J I :=
  fun _ ⟨a, b, γ, hγ, hd, _, hw, ho⟩ =>
    ⟨a, b, γ, hγ, hd, hw, fun _ _ _ hik hkl => Int.sbtw_iff.2 (Or.inl ⟨ho hik, ho hkl⟩)⟩

/-- **Measurability.** The configurations for which a walk is an arm form a measurable set. -/
theorem measurableSet_setOf_isArm (c : Bool) (z : LatticeSite 2) (r : ℕ) (lo hi : LatticeSite 2)
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) :
    MeasurableSet {ω | IsArm ω c z r lo hi γ} := by
  have hl : ∀ l : List (Sym2 (LatticeSite 2)),
      MeasurableSet {ω : Config (LatticeSite 2) | ∀ e ∈ l, e ∈ ω} := by
    intro l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.mem_cons, forall_eq_or_imp, ofPred_and]
      exact (measurableSet_setOfPred.2 (measurable_set_mem e)).inter ih
  cases c
  · have h : {ω | IsArm ω false z r lo hi γ} =
        {_ω | γ.IsCrossing (Icc (z - r - 1) (z + r)) (Icc lo (hi - 1))} ∩
          dualConfig ⁻¹' {ω | ∀ e ∈ γ.edges, e ∈ ω} := by
      ext ω
      simp only [isArm_false, isDualArm_iff, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    rw [h]
    exact (MeasurableSet.const _).inter (measurable_dualConfig (hl _))
  · have h : {ω | IsArm ω true z r lo hi γ} =
        {_ω | γ.IsCrossing (Icc (z - r) (z + r)) (Icc (lo + 1) (hi - 1))} ∩
          {ω | ∀ e ∈ γ.edges, e ∈ ω} := by
      ext ω
      simp only [isArm_true, isOpenArm_iff, mem_inter_iff, mem_ofPred_eq]
    rw [h]
    exact (MeasurableSet.const _).inter (hl _)

/-- **Measurability.** The multi-arm event is a countable union of cylinder events. -/
theorem measurableSet_multiArmEventTo (σ : Fin j → Bool) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) (J I : Fin j → Set ℤ) :
    MeasurableSet (multiArmEventTo σ z r lo hi J I) := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  exact (Measurable.forall fun i =>
    measurableSet_setOfPred.1 (measurableSet_setOf_isArm _ z r lo hi (γ i))).and measurable_const

/-- **Measurability.** -/
theorem measurableSet_multiArmEvent (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) :
    MeasurableSet (multiArmEvent σ z r R) :=
  measurableSet_multiArmEventTo σ z r _ _ _ _

/-- **Measurability.** The half-plane multi-arm event is a countable union of cylinder
events. -/
theorem measurableSet_halfArmEventTo (σ : Fin j → Bool) (z : LatticeSite 2) (r : ℕ)
    (lo hi : LatticeSite 2) (J I : Fin j → Set ℤ) :
    MeasurableSet (halfArmEventTo σ z r lo hi J I) := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  exact (Measurable.forall fun i =>
    measurableSet_setOfPred.1 (measurableSet_setOf_isArm _ z r lo hi (γ i))).and measurable_const

/-- **Measurability.** -/
theorem measurableSet_halfArmEvent (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) :
    MeasurableSet (halfArmEvent σ z r R) :=
  measurableSet_halfArmEventTo σ z r _ _ _ _

/-- **Determination by the annulus.** The multi-arm event is determined by the edges of the outer
box with an end outside `B_r(z)`: its open arms use only such edges, and its dual arms cross only
such edges. In particular it is determined by the edges with both ends in the annulus
`Icc lo hi \ Icc (z - r + 1) (z + r - 1)` (`mem_multiArmEventTo_iff_of_inter_eq`). -/
theorem mem_multiArmEventTo_iff_of_agree {ω' : Config (LatticeSite 2)}
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc lo hi) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω')) :
    ω ∈ multiArmEventTo σ z r lo hi J I ↔ ω' ∈ multiArmEventTo σ z r lo hi J I := by
  constructor
  · rintro ⟨a, b, γ, hγ, hd, hw, ho⟩
    exact ⟨a, b, γ, fun i => (hγ i).of_agree hω, hd, hw, ho⟩
  · rintro ⟨a, b, γ, hγ, hd, hw, ho⟩
    exact ⟨a, b, γ, fun i => (hγ i).of_agree fun e he h₁ h₂ => (hω e he h₁ h₂).symm, hd, hw, ho⟩

/-- **Determination by the annulus.** The half-plane multi-arm event is determined by the edges of
the outer box with an end outside `B_r(z)`. -/
theorem mem_halfArmEventTo_iff_of_agree {ω' : Config (LatticeSite 2)}
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc lo hi) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω')) :
    ω ∈ halfArmEventTo σ z r lo hi J I ↔ ω' ∈ halfArmEventTo σ z r lo hi J I := by
  constructor
  · rintro ⟨a, b, γ, hγ, hd, hH, hw, ho⟩
    exact ⟨a, b, γ, fun i => (hγ i).of_agree hω, hd, hH, hw, ho⟩
  · rintro ⟨a, b, γ, hγ, hd, hH, hw, ho⟩
    exact ⟨a, b, γ, fun i => (hγ i).of_agree fun e he h₁ h₂ => (hω e he h₁ h₂).symm, hd, hH,
      hw, ho⟩

/-- An edge with both ends in `Icc lo hi` and an end outside `B_r(z)` has both ends in the
annulus `Icc lo hi \ Icc (z - r + 1) (z + r - 1)`. -/
theorem mem_annulus_of_mem_edgeSet {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    (h₁ : ∀ v ∈ e, v ∈ Icc lo hi) (h₂ : ∃ v ∈ e, v ∉ Icc (z - r) (z + r)) :
    ∀ v ∈ e, v ∈ Icc lo hi \ Icc (z - r + 1) (z + r - 1) := by
  induction e using Sym2.ind with
  | h x y =>
    have hxy : (zdGraph 2).Adj x y := he
    have hx₀ := apply_le_apply_add_one_of_adj hxy
    have hy₀ := apply_le_apply_add_one_of_adj hxy.symm
    obtain ⟨w, hw, hwB⟩ := h₂
    have hx := h₁ x (Sym2.mem_mk_left x y)
    have hy := h₁ y (Sym2.mem_mk_right x y)
    intro v hv
    refine ⟨h₁ v hv, fun hvB => hwB ?_⟩
    rw [mem_Icc_two_iff] at hvB ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvB ⊢
    have a0 := hx₀ 0
    have a1 := hx₀ 1
    have b0 := hy₀ 0
    have b1 := hy₀ 1
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> rcases Sym2.mem_iff.1 hw with rfl | rfl <;> omega

/-- **Determination by the annulus.** The multi-arm event is determined by the pairs inside any
set containing the annulus `Icc lo hi \ Icc (z - r + 1) (z + r - 1)`. -/
theorem mem_multiArmEventTo_iff_of_inter_eq {T : Set (LatticeSite 2)}
    (hT : Icc lo hi \ Icc (z - r + 1) (z + r - 1) ⊆ T) {ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ multiArmEventTo σ z r lo hi J I ↔ ω' ∈ multiArmEventTo σ z r lo hi J I := by
  refine mem_multiArmEventTo_iff_of_agree fun e he h₁ h₂ => ?_
  have heT : e ∈ {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ T} := fun v hv =>
    hT (mem_annulus_of_mem_edgeSet he h₁ h₂ v hv)
  have hmem := congrArg (e ∈ ·) h
  simp only [eq_iff_iff, mem_inter_iff] at hmem
  exact ⟨fun h' => (hmem.1 ⟨h', heT⟩).1, fun h' => (hmem.2 ⟨h', heT⟩).1⟩

/-- **Translation**, one direction. -/
theorem image_add_mem_multiArmEventTo (c : LatticeSite 2)
    (h : ω ∈ multiArmEventTo σ z r lo hi J I) :
    Sym2.map (· + c) '' ω ∈ multiArmEventTo σ (z + c) r (lo + c) (hi + c) J I := by
  obtain ⟨a, b, γ, hγ, hd, hw, ho⟩ := h
  let f : zdGraph 2 →g zdGraph 2 := ⟨(· + c), fun {x y} hxy =>
    (zdGraph_adj_iff_of_sub fun i => by simp only [Pi.add_apply, add_sub_add_right_eq_sub]).2 hxy⟩
  have hf : ∀ x, f x = x + c := fun _ => rfl
  refine ⟨fun i => f (a i), fun i => f (b i), fun i => (γ i).map f, fun i => (hγ i).map_add hf,
    hd.map (add_left_injective c), fun i => ?_, fun i k l hik hkl => ?_⟩
  · rw [innerPos_map_add _ hf, landingPos_map_add _ hf]
    exact hw i
  · simp only [landingPos_map_add _ hf]
    exact ho i k l hik hkl

/-- Translating by `c` and back by `-c` gives the configuration back. -/
theorem image_add_neg_image_add (c : LatticeSite 2) (ω : Config (LatticeSite 2)) :
    Sym2.map (· + -c) '' (Sym2.map (· + c) '' ω) = ω := by
  rw [image_image]
  have h : ∀ e : Sym2 (LatticeSite 2), Sym2.map (· + -c) (Sym2.map (· + c) e) = e := by
    intro e
    have h' : ((fun v : LatticeSite 2 => v + -c) ∘ fun v => v + c) = id := by
      funext v
      simp
    rw [Sym2.map_map, h', Sym2.map_id, id]
  simp only [h, image_id']

/-- **Translation.** Translating the configuration by `c` carries the multi-arm event at `z` with
outer box `Icc lo hi` to the event at `z + c` with outer box `Icc (lo + c) (hi + c)`. -/
theorem image_add_mem_multiArmEventTo_iff (c : LatticeSite 2) :
    Sym2.map (· + c) '' ω ∈ multiArmEventTo σ (z + c) r (lo + c) (hi + c) J I ↔
      ω ∈ multiArmEventTo σ z r lo hi J I := by
  refine ⟨fun h => ?_, image_add_mem_multiArmEventTo c⟩
  have := image_add_mem_multiArmEventTo (-c) h
  rwa [image_add_neg_image_add, add_neg_cancel_right, add_neg_cancel_right,
    add_neg_cancel_right] at this

/-- **Translation.** -/
theorem image_add_mem_multiArmEvent_iff (c : LatticeSite 2) {R : ℕ} :
    Sym2.map (· + c) '' ω ∈ multiArmEvent σ (z + c) r R ↔ ω ∈ multiArmEvent σ z r R := by
  have := image_add_mem_multiArmEventTo_iff (σ := σ) (z := z) (r := r) (lo := z - R)
    (hi := z + R) (J := fun _ => univ) (I := fun _ => univ) (ω := ω) c
  rwa [show z - (R : LatticeSite 2) + c = z + c - R by abel,
    show z + (R : LatticeSite 2) + c = z + c + R by abel] at this

/-- **Translation**, one direction. -/
theorem image_add_mem_halfArmEventTo (c : LatticeSite 2)
    (h : ω ∈ halfArmEventTo σ z r lo hi J I) :
    Sym2.map (· + c) '' ω ∈ halfArmEventTo σ (z + c) r (lo + c) (hi + c) J I := by
  obtain ⟨a, b, γ, hγ, hd, hH, hw, ho⟩ := h
  let f : zdGraph 2 →g zdGraph 2 := ⟨(· + c), fun {x y} hxy =>
    (zdGraph_adj_iff_of_sub fun i => by simp only [Pi.add_apply, add_sub_add_right_eq_sub]).2 hxy⟩
  have hf : ∀ x, f x = x + c := fun _ => rfl
  refine ⟨fun i => f (a i), fun i => f (b i), fun i => (γ i).map f, fun i => (hγ i).map_add hf,
    hd.map (add_left_injective c), fun i v hv => ?_, fun i => ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hv
    simp only [hf, Pi.add_apply, add_le_add_iff_right]
    exact hH i w hw'
  · rw [innerPos_map_add _ hf, landingPos_map_add _ hf]
    exact hw i
  · simp only [landingPos_map_add _ hf]
    exact ho

/-- **Translation.** Translating the configuration by `c` carries the half-plane multi-arm event
at `z` with outer box `Icc lo hi` to the event at `z + c` with outer box `Icc (lo + c) (hi + c)`. -/
theorem image_add_mem_halfArmEventTo_iff (c : LatticeSite 2) :
    Sym2.map (· + c) '' ω ∈ halfArmEventTo σ (z + c) r (lo + c) (hi + c) J I ↔
      ω ∈ halfArmEventTo σ z r lo hi J I := by
  refine ⟨fun h => ?_, image_add_mem_halfArmEventTo c⟩
  have := image_add_mem_halfArmEventTo (-c) h
  rwa [image_add_neg_image_add, add_neg_cancel_right, add_neg_cancel_right,
    add_neg_cancel_right] at this

/-- **Without open edges** there is no open arm from a box inside the interior of the outer
box. -/
theorem empty_notMem_multiArmEventTo (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hσ : ∃ i, σ i = true) : (∅ : Config (LatticeSite 2)) ∉ multiArmEventTo σ z r lo hi J I := by
  rintro ⟨a, b, γ, hγ, -⟩
  obtain ⟨i, hi⟩ := hσ
  have h := hγ i
  rw [hi, isArm_true] at h
  exact h.mem_of_mem_edges _ (SimpleGraph.Walk.mk_start_snd_mem_edges (h.not_nil hB))

/-- **With every edge open** there is no dual arm from a box inside the interior of the outer
box. -/
theorem univ_notMem_multiArmEventTo (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hσ : ∃ i, σ i = false) :
    (univ : Config (LatticeSite 2)) ∉ multiArmEventTo σ z r lo hi J I := by
  rintro ⟨a, b, γ, hγ, -⟩
  obtain ⟨i, hi⟩ := hσ
  have h := hγ i
  rw [hi, isArm_false] at h
  have := h.mem_of_mem_edges _ (SimpleGraph.Walk.mk_start_snd_mem_edges (h.not_nil hB))
  rw [dualConfig_univ] at this
  exact this

end Events

/-! ### The one-arm event as a multi-arm event -/

/-- **The one-arm event is the multi-arm event with one open arm from the centre.** -/
theorem multiArmEvent_true_eq_armEvent (z : LatticeSite 2) (R : ℕ) :
    multiArmEvent ![true] z 0 R = armEvent z R := by
  ext ω
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · rw [armEvent_zero]
    simp only [mem_univ, iff_true]
    refine ⟨fun _ => z, fun _ => z, fun _ => SimpleGraph.Walk.nil, fun i => ?_,
      armsDisjoint_of_subsingleton le_rfl _ _, fun _ => ⟨mem_univ _, mem_univ _⟩,
      fun i k l hik => absurd hik (by omega)⟩
    rw [Fin.fin_one_eq_zero i]
    refine ⟨SimpleGraph.Walk.isCrossing_nil_iff.2 ⟨by simp, fun h => ?_⟩, by simp⟩
    have h₁ := h.1 0
    have h₂ := h.2 0
    simp only [Pi.add_apply, Pi.sub_apply, Nat.cast_zero, Pi.zero_apply, Pi.one_apply] at h₁ h₂
    omega
  have hzS : z ∈ Icc (z - R + 1) (z + R - 1) := by
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    exact ⟨fun i => by omega, fun i => by omega⟩
  have hB : Icc (z - ((0 : ℕ) : LatticeSite 2)) (z + ((0 : ℕ) : LatticeSite 2)) ⊆
      Icc (z - R + 1) (z + R - 1) := by
    simp only [Nat.cast_zero, sub_zero, add_zero, Icc_self, singleton_subset_iff]
    exact hzS
  constructor
  · rintro ⟨a, b, γ, hγ, -, -, -⟩
    have h : IsOpenArm ω z 0 (z - R) (z + R) (γ 0) := hγ 0
    have hnil := h.not_nil hB
    have ha : a 0 = z := by
      have := h.isCrossing.start_mem
      simpa only [Nat.cast_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff] using this
    rw [mem_armEvent_iff_exists_mem_boxBoundary]
    refine ⟨b 0, h.end_mem_boxBoundary hnil, ?_⟩
    have hsupp : ∀ v ∈ (γ 0).support, v ∈ Icc (z - R) (z + R) := fun v hv => h.mem_Icc hnil hv
    have hedges : ∀ e ∈ (γ 0).edges, e ∈ (openGraph (ω ∩ (zdGraph 2).edgeSet)).edgeSet := by
      intro e he
      have heE := (γ 0).edges_subset_edgeSet he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨⟨h.mem_of_mem_edges e he, heE⟩, SimpleGraph.not_isDiag_of_mem_edgeSet _ heE⟩
    have hc : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - R) (z + R)) (a 0) (b 0) :=
      ⟨hsupp _ (γ 0).start_mem_support, hsupp _ (γ 0).end_mem_support,
        ⟨((γ 0).transfer _ hedges).induce _ (by rwa [SimpleGraph.Walk.support_transfer])⟩⟩
    rwa [ha] at hc
  · intro hω
    obtain ⟨v, hv, hc⟩ := mem_armEvent_iff_exists_mem_boxBoundary.1 hω
    have hvS : v ∉ Icc (z - R + 1) (z + R - 1) := by
      rw [boxBoundary_eq_Icc_diff_Icc] at hv
      exact hv.2
    obtain ⟨y, hy, w, hw, ⟨q⟩, hyw⟩ :=
      exists_first_exit _ hzS hvS (localConn_subset_conn _ z v hc)
    classical
    -- the walk to `y` inside the interior, as a path of `ℤ²`
    set q₁ := q.map (SimpleGraph.Embedding.induce (Icc (z - R + 1) (z + R - 1))).toHom
      with hq₁
    have hq₁S : ∀ u ∈ q₁.support, u ∈ Icc (z - R + 1) (z + R - 1) := by
      intro u hu
      rw [hq₁, SimpleGraph.Walk.support_map] at hu
      obtain ⟨u', -, rfl⟩ := List.mem_map.1 hu
      exact u'.2
    have hq₂E : ∀ e ∈ q₁.bypass.edges, e ∈ (zdGraph 2).edgeSet := by
      intro e he
      have := q₁.bypass.edges_subset_edgeSet he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
      exact this.1.2
    set p := q₁.bypass.transfer (zdGraph 2) hq₂E with hp
    have hpS : ∀ u ∈ p.support, u ∈ Icc (z - R + 1) (z + R - 1) := by
      intro u hu
      rw [hp, SimpleGraph.Walk.support_transfer] at hu
      exact hq₁S u (SimpleGraph.Walk.support_bypass_subset_support _ hu)
    have hpω : ∀ e ∈ p.edges, e ∈ ω := by
      intro e he
      rw [hp, SimpleGraph.Walk.edges_transfer] at he
      have := q₁.bypass.edges_subset_edgeSet he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
      exact this.1.1
    have hpath : p.support.Nodup := by
      rw [hp, SimpleGraph.Walk.support_transfer]
      exact (SimpleGraph.Walk.bypass_isPath q₁).support_nodup
    have hadj : (zdGraph 2).Adj y w := hyw.2
    set γ₀ := p.append (SimpleGraph.Adj.toWalk hadj) with hγ₀
    have hγ₀ : IsOpenArm ω z 0 (z - R) (z + R) γ₀ := by
      refine ⟨⟨by simp, fun u hu => ?_, ?_, fun u hu => ?_⟩, fun e he => ?_⟩
      · rw [hγ₀, SimpleGraph.Walk.tail_support_append, List.mem_append] at hu
        simp only [Nat.cast_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff]
        rcases hu with hu | hu
        · rintro rfl
          rw [← p.cons_tail_support] at hpath
          exact (List.nodup_cons.1 hpath).1 hu
        · change u ∈ [w] at hu
          rw [List.mem_singleton] at hu
          rintro rfl
          exact hw (hu ▸ hzS)
      · exact hw
      · rw [hγ₀, SimpleGraph.Walk.support_append] at hu
        change u ∈ (p.support ++ [w]).dropLast at hu
        rw [List.dropLast_concat] at hu
        exact hpS u hu
      · rw [hγ₀, SimpleGraph.Walk.edges_append, List.mem_append] at he
        rcases he with he | he
        · exact hpω e he
        · change e ∈ [s(y, w)] at he
          rw [List.mem_singleton] at he
          rw [he]
          exact hyw.1
    refine ⟨fun _ => z, fun _ => w, fun _ => γ₀, fun i => ?_,
      armsDisjoint_of_subsingleton le_rfl _ _, fun _ => ⟨mem_univ _, mem_univ _⟩,
      fun i k l hik => absurd hik (by omega)⟩
    rw [Fin.fin_one_eq_zero i]
    exact hγ₀

/-! ### Landing data -/

/-- **Landing data** for `j` arms: `j` windows `[θ i, θ i + η]` of the circle `[0, 1)`, measured in
fractions of a turn, of length `η > 0`, inside `[0, 1]`, in counterclockwise order, with a gap of
at least `η` between consecutive windows, also between the last and the first around the circle.
These are Nolin's `η`-separated landing sequences, with windows of length exactly `η`. -/
structure IsLanding {j : ℕ} (η : ℚ) (θ : Fin j → ℚ) : Prop where
  /-- The windows have positive length. -/
  pos : 0 < η
  /-- The windows start in `[0, 1)`. -/
  nonneg : ∀ i, 0 ≤ θ i
  /-- The windows end by `1`. -/
  add_le_one : ∀ i, θ i + η ≤ 1
  /-- Consecutive windows are separated by a gap of length at least `η`. -/
  add_two_mul_le : ∀ i k, i < k → θ i + 2 * η ≤ θ k
  /-- The last and the first windows are separated by a gap of length at least `η` around the
  circle. -/
  add_two_mul_le_add_one : ∀ i k, θ i + 2 * η ≤ θ k + 1

/-- The **windows** of landing data on a cycle of perimeter `P`: the positions `p` with
`θ i ≤ p / P ≤ θ i + η`. For the landing positions of arms to the boundary of `B_R(z)` the
perimeter is `16 R`, for their inner positions on `B_r(z)` it is `16 r + 8` (positions on the
doubled lattice). -/
def window {j : ℕ} (P : ℕ) (θ : Fin j → ℚ) (η : ℚ) (i : Fin j) : Set ℤ :=
  {p | θ i * P ≤ p ∧ (p : ℚ) ≤ (θ i + η) * P}

section Landing

variable {j : ℕ} {P : ℕ} {θ : Fin j → ℚ} {η : ℚ}

theorem mem_window_iff {i : Fin j} {p : ℤ} :
    p ∈ window P θ η i ↔ θ i * P ≤ p ∧ (p : ℚ) ≤ (θ i + η) * P :=
  Iff.rfl

/-- **Monotonicity.** Windows grow with their length. -/
theorem window_mono {η' : ℚ} (h : η ≤ η') (i : Fin j) : window P θ η i ⊆ window P θ η' i :=
  fun p hp => ⟨hp.1, hp.2.trans (by gcongr)⟩

/-- Windows of landing data lie in `[0, P]`. -/
theorem IsLanding.mem_Icc_of_mem_window (h : IsLanding η θ) {i : Fin j} {p : ℤ}
    (hp : p ∈ window P θ η i) : p ∈ Icc 0 (P : ℤ) := by
  have h₁ : (0 : ℚ) ≤ θ i * P := mul_nonneg (h.nonneg i) (Nat.cast_nonneg P)
  have h₂ : (θ i + η) * P ≤ P := by
    have := h.add_le_one i
    nlinarith [(Nat.cast_nonneg P : (0 : ℚ) ≤ P)]
  constructor
  · exact_mod_cast h₁.trans hp.1
  · exact_mod_cast hp.2.trans h₂

/-- **Disjointness.** On a cycle of positive perimeter the windows of landing data are pairwise
disjoint. -/
theorem IsLanding.disjoint_window (h : IsLanding η θ) (hP : 0 < P) {i k : Fin j} (hik : i ≠ k) :
    Disjoint (window P θ η i) (window P θ η k) := by
  have hP' : (0 : ℚ) < P := by exact_mod_cast hP
  rw [Set.disjoint_left]
  rintro p ⟨hi₁, hi₂⟩ ⟨hk₁, hk₂⟩
  rcases lt_or_gt_of_ne hik with hlt | hlt
  · have := h.add_two_mul_le i k hlt
    have hη := h.pos
    nlinarith
  · have := h.add_two_mul_le k i hlt
    have hη := h.pos
    nlinarith

/-- A window that is long enough on its cycle contains a position. -/
theorem nonempty_window (hP : 1 ≤ η * P) (i : Fin j) : (window P θ η i).Nonempty := by
  refine ⟨⌈θ i * P⌉, Int.le_ceil _, ?_⟩
  have := Int.ceil_lt_add_one (θ i * P)
  linarith

/-- **Landing data exist** for every number of arms: the windows `[i/j, i/j + 1/(4j)]`. -/
theorem isLanding_div (hj : 0 < j) : IsLanding (1 / (4 * j)) fun i : Fin j => (i : ℚ) / j := by
  have hj' : (0 : ℚ) < j := by exact_mod_cast hj
  refine ⟨by positivity, fun i => by positivity, fun i => ?_, fun i k hik => ?_, fun i k => ?_⟩
  · have hi : ((i : ℕ) : ℚ) + 1 ≤ j := by exact_mod_cast i.2
    rw [div_add_div _ _ hj'.ne' (by positivity), div_le_one (by positivity)]
    nlinarith
  · have hik' : ((i : ℕ) : ℚ) + 1 ≤ k := by exact_mod_cast hik
    have e : ((i : ℕ) : ℚ) / j + 2 * (1 / (4 * j)) = (((i : ℕ) : ℚ) + 1 / 2) / j := by
      field_simp
      ring
    rw [e, div_le_div_iff_of_pos_right hj']
    linarith
  · have hi : ((i : ℕ) : ℚ) + 1 ≤ j := by exact_mod_cast i.2
    have hk : (0 : ℚ) ≤ (k : ℕ) := Nat.cast_nonneg _
    have e : ((i : ℕ) : ℚ) / j + 2 * (1 / (4 * j)) = (((i : ℕ) : ℚ) + 1 / 2) / j := by
      field_simp
      ring
    have e' : ((k : ℕ) : ℚ) / j + 1 = (((k : ℕ) : ℚ) + j) / j := by
      field_simp
    rw [e, e', div_le_div_iff_of_pos_right hj']
    linarith

end Landing


/-! ### Arms of one step -/

section OneStep

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi u v : LatticeSite 2}

/-- **The trivial case.** A single open edge from `B_r(z)` to the outside of the interior of the
outer box is an open arm. -/
theorem isOpenArm_toWalk_iff (h : (zdGraph 2).Adj u v) : IsOpenArm ω z r lo hi h.toWalk ↔
    u ∈ Icc (z - r) (z + r) ∧ v ∉ Icc (z - r) (z + r) ∧ v ∉ Icc (lo + 1) (hi - 1) ∧
      u ∈ Icc (lo + 1) (hi - 1) ∧ s(u, v) ∈ ω := by
  simp only [isOpenArm_iff, SimpleGraph.Adj.edges_toWalk]
  constructor
  · rintro ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩
    exact ⟨h₁, h₂ v (by simp), h₃, h₄ u (by simp), h₅ _ (by simp)⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨⟨h₁, by simpa using h₂, h₃, by simpa using h₄⟩, by simpa using h₅⟩

/-- **The trivial case.** A single dual-open dual edge from a face touching `B_r(z)` to a face
outside the outer box, from a face of the outer box, is a dual arm. -/
theorem isDualArm_toWalk_iff (h : (zdGraph 2).Adj u v) : IsDualArm ω z r lo hi h.toWalk ↔
    u ∈ Icc (z - r - 1) (z + r) ∧ v ∉ Icc (z - r - 1) (z + r) ∧ v ∉ Icc lo (hi - 1) ∧
      u ∈ Icc lo (hi - 1) ∧ s(u, v) ∈ dualConfig ω := by
  simp only [isDualArm_iff, SimpleGraph.Adj.edges_toWalk]
  constructor
  · rintro ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩
    exact ⟨h₁, h₂ v (by simp), h₃, h₄ u (by simp), h₅ _ (by simp)⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨⟨h₁, by simpa using h₂, h₃, by simpa using h₄⟩, by simpa using h₅⟩

end OneStep

/-! ### Non-vacuity -/

/-- With no open edge there is no arm of radius one in `ℤ²`. -/
example : (∅ : Config (LatticeSite 2)) ∉ armEvent 0 1 :=
  empty_notMem_armEvent le_rfl

/-- With every edge open there is an arm of radius one in `ℤ²`. -/
example : (univ : Config (LatticeSite 2)) ∈ armEvent 0 1 :=
  univ_mem_armEvent 0 1

/-- With every edge open the four strips of an annulus are crossed. -/
example (z : LatticeSite 2) : (univ : Config (LatticeSite 2)) ∈ fourStrip z 1 :=
  univ_mem_fourStrip z 1

/-- With no open edge the four strips of an annulus are not crossed: the event is not
everything. -/
example (z : LatticeSite 2) : (∅ : Config (LatticeSite 2)) ∉ fourStrip z 1 := fun h =>
  empty_notMem_crossing (by simp) (mem_fourStrip_iff.1 h).1

/-- The corners of `[0, 2]²` are on its boundary and its centre is not. -/
example : ![0, 2] ∈ boxBoundary (0 : LatticeSite 2) ![2, 2] ∧
    ![1, 1] ∉ boxBoundary (0 : LatticeSite 2) ![2, 2] := by
  norm_num [mem_boxBoundary_two_iff]

/-- Counterclockwise around the unit square: the corners `(0, 0)`, `(1, 0)`, `(1, 1)` and
`(0, 1)` have positions `0`, `1`, `2` and `3`. -/
example : perimeterPos 0 1 ![0, 0] = 0 ∧ perimeterPos 0 1 ![1, 0] = 1 ∧
    perimeterPos 0 1 ![1, 1] = 2 ∧ perimeterPos 0 1 ![0, 1] = 3 := by
  norm_num [perimeterPos]

/-- Crossing bounds can hold: every law has them up to scale zero. The bounds at `1/2` at every
scale need the Russo–Seymour–Welsh bounds and are proved with them. -/
example (q : Sym2 (LatticeSite 2) → unitInterval) : CrossingBounds q 0 fun _ => 1 :=
  crossingBounds_zero q fun _ => one_pos

/-! ### Non-vacuity of the multi-arm events -/

/-- With every edge open there is an open arm from a vertex. -/
example : (univ : Config (LatticeSite 2)) ∈ multiArmEvent ![true] 0 0 1 := by
  rw [multiArmEvent_true_eq_armEvent]
  exact univ_mem_armEvent 0 1

/-- With no open edge there is no open arm. -/
example : (∅ : Config (LatticeSite 2)) ∉ multiArmEvent ![true] 0 0 1 :=
  empty_notMem_multiArmEventTo (by simp) ⟨0, rfl⟩

/-- With every edge open there is no dual arm. -/
example : (univ : Config (LatticeSite 2)) ∉ multiArmEvent ![false] 0 0 1 :=
  univ_notMem_multiArmEventTo (by simp) ⟨0, rfl⟩

/-- With no open edge there is a dual arm from a vertex: from the face `[0, 1]²` to the face on
its right, across the closed edge `{(1, 0), (1, 1)}`. -/
example : (∅ : Config (LatticeSite 2)) ∈ multiArmEvent ![false] 0 0 1 := by
  have hadj : (zdGraph 2).Adj ![0, 0] ![1, 0] := by
    rw [zdGraph_two_adj_iff]
    simp
  refine ⟨fun _ => ![0, 0], fun _ => ![1, 0], fun _ => hadj.toWalk, fun i => ?_,
    armsDisjoint_of_subsingleton le_rfl _ _, fun _ => ⟨mem_univ _, mem_univ _⟩,
    fun i k l hik => absurd hik (by omega)⟩
  rw [Fin.fin_one_eq_zero i]
  refine (isDualArm_toWalk_iff hadj).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [mem_Icc_two_iff, -mem_Icc]
  · simp [mem_Icc_two_iff, -mem_Icc]
  · simp [mem_Icc_two_iff, -mem_Icc]
  · simp [mem_Icc_two_iff, -mem_Icc]
  · rw [dualConfig_empty]
    exact hadj


/-- **Five arms from a vertex**, with the colours open, dual, open, open, dual of the five-arm
exponent: the open edges from the origin downwards, to the right and upwards, and the dual edges
downwards from the two faces below the origin, which cross the closed edges
`{(0, -1), (1, -1)}` and `{(-1, -1), (0, -1)}`. -/
example : ({s(0, ![0, -1]), s(0, ![1, 0]), s(0, ![0, 1])} : Config (LatticeSite 2)) ∈
    multiArmEvent ![true, false, true, true, false] 0 0 1 := by
  set ω₅ : Config (LatticeSite 2) := {s(0, ![0, -1]), s(0, ![1, 0]), s(0, ![0, 1])} with hω₅
  set a : Fin 5 → LatticeSite 2 := ![0, ![0, -1], 0, 0, ![-1, -1]] with ha
  set b : Fin 5 → LatticeSite 2 := ![![0, -1], ![0, -2], ![1, 0], ![0, 1], ![-1, -2]] with hb
  have hadj : ∀ i, (zdGraph 2).Adj (a i) (b i) := by
    intro i
    rw [zdGraph_two_adj_iff]
    fin_cases i <;> simp [a, b]
  have hd₁ : s(![0, -1], ![0, -2]) ∈ dualConfig ω₅ := by
    rw [show s(![0, -1], ![0, -2]) = dualEdge s(![0, -1], ![0 + 1, -1]) by
      rw [dualEdge_horizontal, Sym2.eq_swap]
      norm_num, dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet 0 (-1))]
    simp [ω₅, funext_iff, Fin.forall_fin_two]
  have hd₄ : s(![-1, -1], ![-1, -2]) ∈ dualConfig ω₅ := by
    rw [show s(![-1, -1], ![-1, -2]) = dualEdge s(![-1, -1], ![-1 + 1, -1]) by
      rw [dualEdge_horizontal, Sym2.eq_swap]
      norm_num, dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet (-1) (-1))]
    simp [ω₅, funext_iff, Fin.forall_fin_two]
  refine (mem_multiArmEvent_iff (R := 1)).2 ⟨a, b, fun i => (hadj i).toWalk, fun i => ?_, ⟨?_, ?_⟩,
    ?_⟩
  · fin_cases i
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₅, a, b, -mem_Icc]
    · exact (isDualArm_toWalk_iff _).2 ⟨by simp [a, mem_Icc_two_iff, -mem_Icc],
        by simp [b, mem_Icc_two_iff, -mem_Icc], by simp [b, mem_Icc_two_iff, -mem_Icc],
        by simp [a, mem_Icc_two_iff, -mem_Icc], hd₁⟩
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₅, a, b, -mem_Icc]
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₅, a, b, -mem_Icc]
    · exact (isDualArm_toWalk_iff _).2 ⟨by simp [a, mem_Icc_two_iff, -mem_Icc],
        by simp [b, mem_Icc_two_iff, -mem_Icc], by simp [b, mem_Icc_two_iff, -mem_Icc],
        by simp [a, mem_Icc_two_iff, -mem_Icc], hd₄⟩
  · have key : ∀ i k : Fin 5, i ≠ k → ![true, false, true, true, false] i = true →
        ![true, false, true, true, false] k = true → ∀ v ∈ [a i, b i].tail, v ∉ [a k, b k] := by
      decide
    intro i k hik hi hk v hv hv'
    rw [SimpleGraph.Adj.support_toWalk] at hv hv'
    exact key i k hik hi hk v hv hv'
  · have key : ∀ i k : Fin 5, i ≠ k → ![true, false, true, true, false] i = false →
        ![true, false, true, true, false] k = false → ∀ v ∈ [a i, b i], v ∉ [a k, b k] := by
      decide
    intro i k hik hi hk v hv hv'
    rw [SimpleGraph.Adj.support_toWalk] at hv hv'
    exact key i k hik hi hk v hv hv'
  · have hpos : ∀ i, landingPos (0 - ((1 : ℕ) : LatticeSite 2)) (0 + ((1 : ℕ) : LatticeSite 2))
        (![true, false, true, true, false] i) (hadj i).toWalk = ![2, 3, 6, 10, 1] i := by
      intro i
      have hpen : ((hadj i).toWalk).penultimate = a i := rfl
      simp only [landingPos, hpen]
      fin_cases i <;> simp [a, b, perimeterPos, Matrix.vecHead, Matrix.vecTail]
    intro i k l hik hkl
    rw [hpos, hpos, hpos, Int.sbtw_iff]
    revert i k l
    decide

/-- **Four alternating arms from a vertex** (open, dual, open, dual): the open edges from the
origin downwards and to the right, the dual edge downwards from the face below-right of the
origin and the dual edge upwards from the face above-right of it. -/
example : ({s(0, ![0, -1]), s(0, ![1, 0])} : Config (LatticeSite 2)) ∈
    multiArmEvent ![true, false, true, false] 0 0 1 := by
  set ω₄ : Config (LatticeSite 2) := {s(0, ![0, -1]), s(0, ![1, 0])} with hω₄
  set a : Fin 4 → LatticeSite 2 := ![0, ![0, -1], 0, ![0, 0]] with ha
  set b : Fin 4 → LatticeSite 2 := ![![0, -1], ![0, -2], ![1, 0], ![0, 1]] with hb
  have hadj : ∀ i, (zdGraph 2).Adj (a i) (b i) := by
    intro i
    rw [zdGraph_two_adj_iff]
    fin_cases i <;> simp [a, b]
  have hd₁ : s(![0, -1], ![0, -2]) ∈ dualConfig ω₄ := by
    rw [show s(![0, -1], ![0, -2]) = dualEdge s(![0, -1], ![0 + 1, -1]) by
      rw [dualEdge_horizontal, Sym2.eq_swap]
      norm_num, dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet 0 (-1))]
    simp [ω₄, funext_iff, Fin.forall_fin_two]
  have hd₃ : s(![0, 0], ![0, 1]) ∈ dualConfig ω₄ := by
    rw [show s(![0, 0], ![0, 1]) = dualEdge s(![0, 1], ![0 + 1, 1]) by
      rw [dualEdge_horizontal]
      norm_num, dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet 0 1)]
    simp [ω₄, funext_iff, Fin.forall_fin_two]
  refine (mem_multiArmEvent_iff (R := 1)).2 ⟨a, b, fun i => (hadj i).toWalk, fun i => ?_, ⟨?_, ?_⟩,
    ?_⟩
  · fin_cases i
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₄, a, b, -mem_Icc]
    · exact (isDualArm_toWalk_iff _).2 ⟨by simp [a, mem_Icc_two_iff, -mem_Icc],
        by simp [b, mem_Icc_two_iff, -mem_Icc], by simp [b, mem_Icc_two_iff, -mem_Icc],
        by simp [a, mem_Icc_two_iff, -mem_Icc], hd₁⟩
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₄, a, b, -mem_Icc]
    · exact (isDualArm_toWalk_iff _).2 ⟨by simp [a, mem_Icc_two_iff, -mem_Icc],
        by simp [b, mem_Icc_two_iff, -mem_Icc], by simp [b, mem_Icc_two_iff, -mem_Icc],
        by simp [a, mem_Icc_two_iff, -mem_Icc], hd₃⟩
  · have key : ∀ i k : Fin 4, i ≠ k → ![true, false, true, false] i = true →
        ![true, false, true, false] k = true → ∀ v ∈ [a i, b i].tail, v ∉ [a k, b k] := by
      decide
    intro i k hik hi hk v hv hv'
    rw [SimpleGraph.Adj.support_toWalk] at hv hv'
    exact key i k hik hi hk v hv hv'
  · have key : ∀ i k : Fin 4, i ≠ k → ![true, false, true, false] i = false →
        ![true, false, true, false] k = false → ∀ v ∈ [a i, b i], v ∉ [a k, b k] := by
      decide
    intro i k hik hi hk v hv hv'
    rw [SimpleGraph.Adj.support_toWalk] at hv hv'
    exact key i k hik hi hk v hv hv'
  · have hpos : ∀ i, landingPos (0 - ((1 : ℕ) : LatticeSite 2)) (0 + ((1 : ℕ) : LatticeSite 2))
        (![true, false, true, false] i) (hadj i).toWalk = ![2, 3, 6, 9] i := by
      intro i
      have hpen : ((hadj i).toWalk).penultimate = a i := rfl
      simp only [landingPos, hpen]
      fin_cases i <;> simp [a, b, perimeterPos, Matrix.vecHead, Matrix.vecTail]
    intro i k l hik hkl
    rw [hpos, hpos, hpos, Int.sbtw_iff]
    revert i k l
    decide

/-- **Three arms from a boundary vertex in the half-plane** (open, dual, open): the open edges from
the origin to the right and to the left, and the dual edge upwards from the face above-right of
the origin, ordered counterclockwise from the right. -/
example : ({s(0, ![1, 0]), s(0, ![-1, 0])} : Config (LatticeSite 2)) ∈
    halfArmEvent ![true, false, true] 0 0 1 := by
  set ω₃ : Config (LatticeSite 2) := {s(0, ![1, 0]), s(0, ![-1, 0])} with hω₃
  set a : Fin 3 → LatticeSite 2 := ![0, ![0, 0], 0] with ha
  set b : Fin 3 → LatticeSite 2 := ![![1, 0], ![0, 1], ![-1, 0]] with hb
  have hadj : ∀ i, (zdGraph 2).Adj (a i) (b i) := by
    intro i
    rw [zdGraph_two_adj_iff]
    fin_cases i <;> simp [a, b]
  have hd₁ : s(![0, 0], ![0, 1]) ∈ dualConfig ω₃ := by
    rw [show s(![0, 0], ![0, 1]) = dualEdge s(![0, 1], ![0 + 1, 1]) by
      rw [dualEdge_horizontal]
      norm_num, dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet 0 1)]
    simp [ω₃, funext_iff, Fin.forall_fin_two]
  refine (mem_halfArmEvent_iff (R := 1)).2 ⟨a, b, fun i => (hadj i).toWalk, fun i => ?_, ⟨?_, ?_⟩,
    fun i v hv => ?_, ?_⟩
  · fin_cases i
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₃, a, b, -mem_Icc]
    · exact (isDualArm_toWalk_iff _).2 ⟨by simp [a, mem_Icc_two_iff, -mem_Icc],
        by simp [b, mem_Icc_two_iff, -mem_Icc], by simp [b, mem_Icc_two_iff, -mem_Icc],
        by simp [a, mem_Icc_two_iff, -mem_Icc], hd₁⟩
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ω₃, a, b, -mem_Icc]
  · have key : ∀ i k : Fin 3, i ≠ k → ![true, false, true] i = true →
        ![true, false, true] k = true → ∀ v ∈ [a i, b i].tail, v ∉ [a k, b k] := by
      decide
    intro i k hik hi hk v hv hv'
    rw [SimpleGraph.Adj.support_toWalk] at hv hv'
    exact key i k hik hi hk v hv hv'
  · have key : ∀ i k : Fin 3, i ≠ k → ![true, false, true] i = false →
        ![true, false, true] k = false → ∀ v ∈ [a i, b i], v ∉ [a k, b k] := by
      decide
    intro i k hik hi hk v hv hv'
    rw [SimpleGraph.Adj.support_toWalk] at hv hv'
    exact key i k hik hi hk v hv hv'
  · have key : ∀ i : Fin 3, ∀ v ∈ [a i, b i], (0 : LatticeSite 2) 1 ≤ v 1 := by
      decide
    rw [SimpleGraph.Adj.support_toWalk] at hv
    exact key i v hv
  · have hpos : ∀ i, landingPos (0 - ((1 : ℕ) : LatticeSite 2)) (0 + ((1 : ℕ) : LatticeSite 2))
        (![true, false, true] i) (hadj i).toWalk = ![6, 9, 14] i := by
      intro i
      have hpen : ((hadj i).toWalk).penultimate = a i := rfl
      simp only [landingPos, hpen]
      fin_cases i <;> simp [a, b, perimeterPos, Matrix.vecHead, Matrix.vecTail]
    intro i k hik
    simp only [hpos]
    revert i k
    decide

/-- **Two arms from a boundary vertex in the half-plane** (open, dual). -/
example : ({s(0, ![1, 0])} : Config (LatticeSite 2)) ∈ halfArmEvent ![true, false] 0 0 1 := by
  set a : Fin 2 → LatticeSite 2 := ![0, ![0, 0]] with ha
  set b : Fin 2 → LatticeSite 2 := ![![1, 0], ![0, 1]] with hb
  have hadj : ∀ i, (zdGraph 2).Adj (a i) (b i) := by
    intro i
    rw [zdGraph_two_adj_iff]
    fin_cases i <;> simp [a, b]
  have hd₁ : s(![0, 0], ![0, 1]) ∈ dualConfig {s(0, ![1, 0])} := by
    rw [show s(![0, 0], ![0, 1]) = dualEdge s(![0, 1], ![0 + 1, 1]) by
      rw [dualEdge_horizontal]
      norm_num, dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet 0 1)]
    simp [funext_iff, Fin.forall_fin_two]
  refine (mem_halfArmEvent_iff (R := 1)).2 ⟨a, b, fun i => (hadj i).toWalk, fun i => ?_, ⟨?_, ?_⟩,
    fun i v hv => ?_, ?_⟩
  · fin_cases i
    · refine (isOpenArm_toWalk_iff _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [a, b, -mem_Icc]
    · exact (isDualArm_toWalk_iff _).2 ⟨by simp [a, mem_Icc_two_iff, -mem_Icc],
        by simp [b, mem_Icc_two_iff, -mem_Icc], by simp [b, mem_Icc_two_iff, -mem_Icc],
        by simp [a, mem_Icc_two_iff, -mem_Icc], hd₁⟩
  · intro i k hik hi hk
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i k hik hi hk
    fin_cases i <;> fin_cases k <;> simp_all
  · have key : ∀ i : Fin 2, ∀ v ∈ [a i, b i], (0 : LatticeSite 2) 1 ≤ v 1 := by
      decide
    rw [SimpleGraph.Adj.support_toWalk] at hv
    exact key i v hv
  · have hpos : ∀ i, landingPos (0 - ((1 : ℕ) : LatticeSite 2)) (0 + ((1 : ℕ) : LatticeSite 2))
        (![true, false] i) (hadj i).toWalk = ![6, 9] i := by
      intro i
      have hpen : ((hadj i).toWalk).penultimate = a i := rfl
      simp only [landingPos, hpen]
      fin_cases i <;> simp [a, b, perimeterPos, Matrix.vecHead, Matrix.vecTail]
    intro i k hik
    simp only [hpos]
    revert i k
    decide

/-- Landing data for five arms: windows of length `1/20` starting at `0, 1/5, …, 4/5`. -/
example : IsLanding (1 / 20) fun i : Fin 5 => (i : ℚ) / 5 := by
  have := isLanding_div (j := 5) (by norm_num)
  norm_num at this ⊢
  exact this

/-- On the boundary of `B_5(z)` (doubled perimeter `80`) the windows of length `1/20` contain
positions. -/
example : (window 80 (fun i : Fin 5 => (i : ℚ) / 5) (1 / 20) 2).Nonempty :=
  nonempty_window (by norm_num) 2

end PercLib.Models.Planar
