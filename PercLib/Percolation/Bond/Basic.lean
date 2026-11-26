/-
Bond percolation interface for this project, written on 2026-11-13.

The proofs of `measurableSet_isChain_openGraph`, `conn_eq_iUnion`, `measurableSet_conn`,
`cluster_infinite_eq_iInter` and `measurableSet_cluster_infinite` are adapted from the
site-percolation proofs in Percolation after Anthropic, prompted by Ahmed Bou-Rabee
(full attribution in third_party/percolation/NOTICE), Apache License 2.0, at pinned revision
a5cc72bd7627f313abbb00bcb47616678abbeb35:
https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/Hypergraph/SiteStatements.lean
(lines 308-374 at that revision). They reach this file through this project's adapted
copy, PercLib/Models/Site/Basic.lean. The upstream licence and the retained notices are
in third_party/percolation/LICENSE and third_party/percolation/NOTICE.

Modified for this project: site configurations (sets of open vertices) replaced by bond
configurations (sets of open unordered pairs); the open site graph replaced by
SimpleGraph.fromEdgeSet, so a walk step needs an open pair of distinct vertices instead of
a host edge with two open endpoints; the closed-vertex case removed, because a bond
cluster always contains its base vertex. The other declarations in this file are new.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Bond percolation: configurations, connections and clusters

This module fixes the bond interface of the library.

* A bond configuration on a vertex type `V` is a set of unordered pairs, `Set (Sym2 V)`:
  the set of open pairs.
* The law is `PercLib.Probability.prodBernoulli q` for `q : Sym2 V → unitInterval`.
* The open graph is `SimpleGraph.fromEdgeSet ω`. That construction discards loops, so
  the value of `q` on the diagonal never matters and is never a hypothesis.
* There is no host graph. Every pair of distinct vertices is a potential edge.
* `Countable V` is a hypothesis of the measurability statements only.
* The cluster of a vertex always contains that vertex, so its volume is at least one.
  The volume is `ℕ∞`-valued and the susceptibility is `ℝ≥0∞`-valued.

The measurability arguments follow those for site percolation in
`PercLib.Models.Site.Basic`: a connection is a countable union, over lists of vertices,
of finite intersections of one-edge cylinder events.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A bond configuration: the set of open unordered pairs of vertices. -/
abbrev Config (V : Type*) : Type _ := Set (Sym2 V)

/-- Independent bond percolation: the pair `e` is open with probability `q e`,
independently over pairs. -/
def law (q : Sym2 V → unitInterval) : Measure (Config V) := prodBernoulli q

instance instIsProbabilityMeasureLaw (q : Sym2 V → unitInterval) :
    IsProbabilityMeasure (law q) :=
  instIsProbabilityMeasureProdBernoulli q

/-- The graph of open edges. Open loops are discarded. -/
def openGraph (ω : Config V) : SimpleGraph V := SimpleGraph.fromEdgeSet ω

/-- The event that `x` and `y` are joined by a path of open edges. -/
@[tag "T90E"]
def conn (x y : V) : Set (Config V) := {ω | (openGraph ω).Reachable x y}

/-- The open cluster of `x`: the vertices joined to `x` by a path of open edges.
It always contains `x`. -/
def cluster (ω : Config V) (x : V) : Set V := {y | (openGraph ω).Reachable x y}

/-- The two-point function: the probability that `x` and `y` are connected. -/
def tau (q : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ := law q (conn x y)

/-- The susceptibility at `x`: the expected number of vertices in the cluster of `x`. -/
def chi (q : Sym2 V → unitInterval) (x : V) : ℝ≥0∞ :=
  ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂(law q)

/-! ### The conventions, pinned down -/

/-- Two vertices are adjacent in the open graph exactly when they are distinct and the
pair is open. -/
theorem openGraph_adj_iff (ω : Config V) (x y : V) :
    (openGraph ω).Adj x y ↔ s(x, y) ∈ ω ∧ x ≠ y :=
  SimpleGraph.fromEdgeSet_adj ω

/-- The open graph grows with the configuration. -/
theorem openGraph_mono {ω ω' : Config V} (h : ω ⊆ ω') : openGraph ω ≤ openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono h

/-- With no open pair, the open graph has no edge. -/
theorem openGraph_empty : openGraph (∅ : Config V) = ⊥ :=
  SimpleGraph.fromEdgeSet_empty

theorem mem_conn_iff (ω : Config V) (x y : V) :
    ω ∈ conn x y ↔ (openGraph ω).Reachable x y := Iff.rfl

theorem mem_cluster_iff (ω : Config V) (x y : V) :
    y ∈ cluster ω x ↔ ω ∈ conn x y := Iff.rfl

/-- Connection is reflexive: every vertex is connected to itself in every
configuration. -/
theorem conn_self (x : V) : conn x x = (Set.univ : Set (Config V)) :=
  Set.eq_univ_of_forall fun _ => SimpleGraph.Reachable.refl x

/-- Connection is symmetric. -/
theorem conn_symm (x y : V) : (conn x y : Set (Config V)) = conn y x := by
  ext ω
  exact SimpleGraph.reachable_comm

/-- Connection is transitive. -/
theorem conn_trans {ω : Config V} {x y z : V} (hxy : ω ∈ conn x y) (hyz : ω ∈ conn y z) :
    ω ∈ conn x z :=
  SimpleGraph.Reachable.trans hxy hyz

/-- Connection is an increasing event. -/
theorem conn_mono {ω ω' : Config V} (h : ω ⊆ ω') {x y : V} (hxy : ω ∈ conn x y) :
    ω' ∈ conn x y :=
  SimpleGraph.Reachable.mono (openGraph_mono h) hxy

/-- An open pair of distinct vertices connects its endpoints: the connection event is
not empty when it should not be. -/
theorem mem_conn_of_mem {ω : Config V} {x y : V} (hxy : x ≠ y) (h : s(x, y) ∈ ω) :
    ω ∈ conn x y :=
  SimpleGraph.Adj.reachable ((openGraph_adj_iff ω x y).2 ⟨h, hxy⟩)

/-- With no open pair, a vertex is connected only to itself: the connection event is not
everything when it should not be. -/
theorem empty_mem_conn_iff (x y : V) : (∅ : Config V) ∈ conn x y ↔ x = y := by
  rw [mem_conn_iff, openGraph_empty]
  exact SimpleGraph.reachable_bot

/-- A vertex belongs to its own cluster. -/
theorem mem_cluster_self (ω : Config V) (x : V) : x ∈ cluster ω x :=
  SimpleGraph.Reachable.refl x

/-- Membership in a cluster is symmetric. -/
theorem mem_cluster_comm (ω : Config V) (x y : V) : y ∈ cluster ω x ↔ x ∈ cluster ω y :=
  SimpleGraph.reachable_comm

/-- With no open pair, every cluster is a single vertex. -/
theorem cluster_empty (x : V) : cluster (∅ : Config V) x = {x} := by
  ext y
  rw [mem_cluster_iff, empty_mem_conn_iff, Set.mem_singleton_iff, eq_comm]

/-- A cluster has at least one vertex. -/
theorem one_le_encard_cluster (ω : Config V) (x : V) : 1 ≤ (cluster ω x).encard :=
  Set.one_le_encard_iff_nonempty.2 ⟨x, mem_cluster_self ω x⟩

/-! ### Connection probability under a general measure -/

/-- The connection probability of `x` and `y` under a measure `μ` on bond configurations,
`μ {x ↔ y}`. No independence is assumed; under the independent law it is `tau q`. -/
def connProb (μ : Measure (Config V)) (x y : V) : ℝ≥0∞ := μ (conn x y)

theorem connProb_def (μ : Measure (Config V)) (x y : V) : connProb μ x y = μ (conn x y) :=
  rfl

@[simp] theorem connProb_law (q : Sym2 V → unitInterval) (x y : V) :
    connProb (law q) x y = tau q x y :=
  rfl

@[simp] theorem connProb_zero (x y : V) : connProb (0 : Measure (Config V)) x y = 0 :=
  rfl

/-- A vertex is connected to itself with probability one. -/
@[simp] theorem connProb_self (μ : Measure (Config V)) [IsProbabilityMeasure μ] (x : V) :
    connProb μ x x = 1 := by
  rw [connProb, conn_self, measure_univ]

/-- The connection probability is symmetric. -/
theorem connProb_comm (μ : Measure (Config V)) (x y : V) : connProb μ x y = connProb μ y x := by
  rw [connProb, connProb, conn_symm]

/-- The connection probability is at most one. -/
theorem connProb_le_one (μ : Measure (Config V)) [IsZeroOrProbabilityMeasure μ] (x y : V) :
    connProb μ x y ≤ 1 :=
  prob_le_one

theorem connProb_ne_top (μ : Measure (Config V)) [IsFiniteMeasure μ] (x y : V) :
    connProb μ x y ≠ ⊤ :=
  measure_ne_top μ _

theorem connProb_mono {μ ν : Measure (Config V)} (h : μ ≤ ν) (x y : V) :
    connProb μ x y ≤ connProb ν x y :=
  h _

/-- A vertex is connected to itself with probability one. -/
theorem tau_self (q : Sym2 V → unitInterval) (x : V) : tau q x x = 1 :=
  connProb_self (law q) x

/-- The two-point function is symmetric. -/
theorem tau_comm (q : Sym2 V → unitInterval) (x y : V) : tau q x y = tau q y x :=
  connProb_comm (law q) x y

/-- The two-point function is at most one. -/
theorem tau_le_one (q : Sym2 V → unitInterval) (x y : V) : tau q x y ≤ 1 :=
  connProb_le_one (law q) x y

/-! ### Measurability -/

/-- An open walk along a given list of vertices is a finite intersection of one-edge
cylinder events. -/
theorem measurableSet_isChain_openGraph (a : V) (l : List V) :
    MeasurableSet {ω : Config V | List.IsChain (openGraph ω).Adj (a :: l)} := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hset : {ω : Config V | List.IsChain (openGraph ω).Adj (a :: b :: l)} =
        ({ω : Config V | s(a, b) ∈ ω} ∩ {_ω : Config V | a ≠ b}) ∩
          {ω | List.IsChain (openGraph ω).Adj (b :: l)} := by
      ext ω
      simp only [List.isChain_cons_cons, openGraph_adj_iff, Set.mem_ofPred_eq,
        Set.mem_inter_iff]
    rw [hset]
    exact ((measurableSet_mem _).inter (MeasurableSet.const _)).inter (ih b)

/-- The connection event as a union over the lists of vertices that witness an open
walk. -/
theorem conn_eq_iUnion (x y : V) :
    (conn x y : Set (Config V)) =
      ⋃ l : List V, {ω : Config V | List.IsChain (openGraph ω).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
  ext ω
  simp only [conn, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · exact List.exists_isChain_cons_of_relationReflTransGen
  · rintro ⟨l, hl, hy⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hl hy

/-- The connection event is measurable when there are countably many vertices. -/
@[tag "7QJG"]
theorem measurableSet_conn [Countable V] (x y : V) :
    MeasurableSet (conn x y : Set (Config V)) := by
  rw [conn_eq_iUnion]
  refine MeasurableSet.iUnion fun l => ?_
  have hset : {ω : Config V | List.IsChain (openGraph ω).Adj (x :: l) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = y} =
        {ω : Config V | List.IsChain (openGraph ω).Adj (x :: l)} ∩
          {_ω | (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
    ext ω; simp
  rw [hset]
  exact (measurableSet_isChain_openGraph x l).inter (MeasurableSet.const _)

/-- The cluster of `x` is infinite exactly when it leaves every finite set of
vertices. -/
theorem cluster_infinite_eq_iInter (x : V) :
    {ω : Config V | (cluster ω x).Infinite} =
      ⋂ F : Finset V, ⋃ y ∈ (↑F : Set V)ᶜ, conn x y := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff,
    Finset.mem_coe, exists_prop, ← mem_cluster_iff]
  constructor
  · intro hinf F
    obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.2 hy)

/-- The event that the cluster of `x` is infinite is measurable when there are countably
many vertices. -/
@[tag "5SII"]
theorem measurableSet_cluster_infinite [Countable V] (x : V) :
    MeasurableSet {ω : Config V | (cluster ω x).Infinite} := by
  rw [cluster_infinite_eq_iInter]
  exact MeasurableSet.iInter fun F =>
    MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_conn x y

/-! ### Non-vacuity

Compiled witnesses that the definitions are neither empty nor trivial in the smallest
relevant case, the two-point vertex type `Bool`. -/

/-- With every pair open, the two vertices of `Bool` are connected. -/
example : (Set.univ : Config Bool) ∈ conn false true :=
  mem_conn_of_mem (by decide) (Set.mem_univ _)

/-- With no pair open, the two vertices of `Bool` are not connected. -/
example : (∅ : Config Bool) ∉ conn false true := by
  rw [empty_mem_conn_iff]
  decide

/-- With no pair open, the cluster of a vertex has exactly one element. -/
example : (cluster (∅ : Config Bool) false).encard = 1 := by
  rw [cluster_empty, Set.encard_singleton]

/-! ### Row sums

The row sum of an edge weight `a : Sym2 V → ℝ≥0∞` at `v` sums `a s(v, w)` over the
vertices `w ≠ v`. The diagonal is excluded because a profile `q` is arbitrary on the
diagonal: the open graph discards loops. The named map `unitInterval.toENNReal` turns a
profile into an edge weight. -/

section RowSum

/-- A probability, as an extended nonnegative real. -/
def _root_.unitInterval.toENNReal (p : unitInterval) : ℝ≥0∞ :=
  (unitInterval.toNNReal p : ℝ≥0∞)

theorem _root_.unitInterval.toENNReal_apply (p : unitInterval) :
    unitInterval.toENNReal p = (unitInterval.toNNReal p : ℝ≥0∞) :=
  rfl

theorem _root_.unitInterval.coe_toNNReal_eq_toENNReal (p : unitInterval) :
    (unitInterval.toNNReal p : ℝ≥0∞) = unitInterval.toENNReal p :=
  rfl

@[simp]
theorem _root_.unitInterval.toENNReal_zero : unitInterval.toENNReal 0 = 0 := by
  simp [unitInterval.toENNReal_apply]

@[simp]
theorem _root_.unitInterval.toENNReal_one : unitInterval.toENNReal 1 = 1 := by
  simp [unitInterval.toENNReal_apply]

@[simp]
theorem _root_.unitInterval.toENNReal_ne_top (p : unitInterval) :
    unitInterval.toENNReal p ≠ ⊤ :=
  ENNReal.coe_ne_top

@[simp]
theorem _root_.unitInterval.toENNReal_lt_top (p : unitInterval) :
    unitInterval.toENNReal p < ⊤ :=
  ENNReal.coe_lt_top

@[simp]
theorem _root_.unitInterval.toENNReal_le_one (p : unitInterval) :
    unitInterval.toENNReal p ≤ 1 := by
  rw [unitInterval.toENNReal_apply, ENNReal.coe_le_one_iff, ← NNReal.coe_le_coe,
    unitInterval.coe_toNNReal, NNReal.coe_one]
  exact p.2.2

@[simp]
theorem _root_.unitInterval.toENNReal_toReal (p : unitInterval) :
    (unitInterval.toENNReal p).toReal = p :=
  rfl

@[simp]
theorem _root_.unitInterval.toENNReal_le_toENNReal {p p' : unitInterval} :
    unitInterval.toENNReal p ≤ unitInterval.toENNReal p' ↔ p ≤ p' := by
  rw [unitInterval.toENNReal_apply, unitInterval.toENNReal_apply, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, unitInterval.coe_toNNReal, unitInterval.coe_toNNReal]
  rfl

theorem _root_.unitInterval.toENNReal_mono : Monotone unitInterval.toENNReal :=
  fun _ _ h => unitInterval.toENNReal_le_toENNReal.2 h

/-- The row sum of an edge weight `a` at `v`: the sum of `a s(v, w)` over `w ≠ v`.

The diagonal term is excluded: a profile `q : Sym2 V → unitInterval` is arbitrary
on the diagonal, because the open graph discards loops, so `a s(v, v)` never enters. For
a profile the weight is `fun e => unitInterval.toENNReal (q e)` (`rowSum_toENNReal`). -/
def rowSum (a : Sym2 V → ℝ≥0∞) (v : V) : ℝ≥0∞ := by
  classical
  exact ∑' w, if w = v then 0 else a s(v, w)

/-- Unfolding `rowSum`, for any decidability instance on `V`. -/
theorem rowSum_def [DecidableEq V] (a : Sym2 V → ℝ≥0∞) (v : V) :
    rowSum a v = ∑' w, if w = v then 0 else a s(v, w) := by
  simp only [rowSum]
  exact tsum_congr fun w => by congr

/-- The row sum is the sum over the vertices other than `v`. -/
theorem rowSum_eq_tsum_ne (a : Sym2 V → ℝ≥0∞) (v : V) :
    rowSum a v = ∑' w : {w // w ≠ v}, a s(v, w.1) := by
  classical
  rw [rowSum_def]
  symm
  refine (tsum_subtype {w | w ≠ v} (fun w => a s(v, w))).trans ?_
  refine tsum_congr fun w => ?_
  by_cases h : w = v <;> simp [h]

/-- The row sum depends only on the weight off the diagonal. -/
theorem rowSum_congr_offDiag {a b : Sym2 V → ℝ≥0∞} {v : V}
    (h : ∀ w, w ≠ v → a s(v, w) = b s(v, w)) : rowSum a v = rowSum b v := by
  simp only [rowSum_eq_tsum_ne]
  exact tsum_congr fun w => h w.1 w.2

/-- Comparison off the diagonal suffices for comparing row sums. -/
theorem rowSum_le_rowSum {a b : Sym2 V → ℝ≥0∞} {v : V}
    (h : ∀ w, w ≠ v → a s(v, w) ≤ b s(v, w)) : rowSum a v ≤ rowSum b v := by
  simp only [rowSum_eq_tsum_ne]
  exact ENNReal.tsum_le_tsum fun w => h w.1 w.2

theorem rowSum_mono {a b : Sym2 V → ℝ≥0∞} (h : a ≤ b) (v : V) :
    rowSum a v ≤ rowSum b v :=
  rowSum_le_rowSum fun w _ => h s(v, w)

@[simp]
theorem rowSum_zero (v : V) : rowSum (0 : Sym2 V → ℝ≥0∞) v = 0 := by
  simp [rowSum_eq_tsum_ne]

@[simp]
theorem rowSum_fun_zero (v : V) : rowSum (fun _ : Sym2 V => (0 : ℝ≥0∞)) v = 0 :=
  rowSum_zero v

theorem rowSum_add (a b : Sym2 V → ℝ≥0∞) (v : V) :
    rowSum (a + b) v = rowSum a v + rowSum b v := by
  simp only [rowSum_eq_tsum_ne, Pi.add_apply]
  exact ENNReal.tsum_add

theorem rowSum_const_mul (c : ℝ≥0∞) (a : Sym2 V → ℝ≥0∞) (v : V) :
    rowSum (fun e => c * a e) v = c * rowSum a v := by
  simp only [rowSum_eq_tsum_ne]
  exact ENNReal.tsum_mul_left

/-- Transport of a row sum along a bijection of the vertices. -/
theorem rowSum_comp_equiv {W : Type*} (σ : V ≃ W) (a : Sym2 W → ℝ≥0∞) (v : V) :
    rowSum (a ∘ Sym2.map σ) v = rowSum a (σ v) := by
  classical
  rw [rowSum_def, rowSum_def, ← σ.tsum_eq]
  refine tsum_congr fun w => ?_
  simp [σ.injective.eq_iff]

/-- The row sum of a profile, unfolded to the explicit `∑'` spelling. -/
theorem rowSum_toENNReal [DecidableEq V] (q : Sym2 V → unitInterval) (v : V) :
    rowSum (fun e => unitInterval.toENNReal (q e)) v =
      ∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) :=
  rowSum_def _ v

end RowSum

/-! ### Connection inside a set

The event `localConn S x y` that `x` and `y` are joined by an open path all of whose
vertices lie in `S`, the restricted cluster `localCluster ω S x`, ordered cuts `IsCut`, and
the boundary flux `boundaryFlux q S o` of a finite set. -/

section LocalConn

/-- The event that `x` and `y` are joined by a path of open edges all of whose vertices lie
in `S`: both endpoints lie in `S`, and they are joined in the open graph induced on `S`.
It is empty unless `x ∈ S` and `y ∈ S`, and for `S = univ` it is `conn x y`. -/
def localConn (S : Set V) (x y : V) : Set (Config V) :=
  {ω | ∃ hx : x ∈ S, ∃ hy : y ∈ S, ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

@[simp]
theorem mem_localConn {S : Set V} {x y : V} {ω : Config V} :
    ω ∈ localConn S x y ↔
      ∃ hx : x ∈ S, ∃ hy : y ∈ S, ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  Iff.rfl

/-- For endpoints in `S`, the event is reachability in the induced open graph. -/
theorem mem_localConn_iff_reachable {S : Set V} {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (ω : Config V) :
    ω ∈ localConn S x y ↔ ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hx, hy, h⟩⟩

/-- Inside the whole vertex set, connection inside the set is connection. -/
theorem localConn_univ (x y : V) : localConn (Set.univ : Set V) x y = conn x y := by
  ext ω
  rw [mem_localConn_iff_reachable (Set.mem_univ x) (Set.mem_univ y), mem_conn_iff,
    ← SimpleGraph.Iso.reachable_iff (φ := SimpleGraph.induceUnivIso (openGraph ω))]
  rfl

/-- A connection inside a set is a connection. -/
theorem localConn_subset_conn (S : Set V) (x y : V) : localConn S x y ⊆ conn x y :=
  fun _ ⟨_, _, h⟩ => h.map (SimpleGraph.Embedding.induce S).toHom

/-- Connection inside a set grows with the set. -/
theorem localConn_mono_set {S T : Set V} (h : S ⊆ T) (x y : V) :
    localConn S x y ⊆ localConn T x y :=
  fun ω ⟨hx, hy, hxy⟩ => ⟨h hx, h hy, hxy.map ((openGraph ω).induceHomOfLE h).toHom⟩

/-- Connection inside a set is symmetric. -/
theorem localConn_comm (S : Set V) (x y : V) : localConn S x y = localConn S y x := by
  ext ω
  exact ⟨fun ⟨hx, hy, h⟩ => ⟨hy, hx, h.symm⟩, fun ⟨hy, hx, h⟩ => ⟨hx, hy, h.symm⟩⟩

/-- Connection inside a set is transitive. -/
theorem localConn_trans {S : Set V} {x y z : V} {ω : Config V} (hxy : ω ∈ localConn S x y)
    (hyz : ω ∈ localConn S y z) : ω ∈ localConn S x z := by
  obtain ⟨hx, hy, h₁⟩ := hxy
  obtain ⟨_, hz, h₂⟩ := hyz
  exact ⟨hx, hz, h₁.trans h₂⟩

/-- A vertex of `S` is connected to itself inside `S` in every configuration: the event is
not empty when it should not be. -/
theorem localConn_self {S : Set V} {x : V} (hx : x ∈ S) :
    localConn S x x = (Set.univ : Set (Config V)) :=
  Set.eq_univ_of_forall fun _ => ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

/-- No vertex outside `S` is connected to anything inside `S`. -/
theorem localConn_of_notMem {S : Set V} {x : V} (hx : x ∉ S) (y : V) :
    localConn S x y = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨h, _, _⟩ => hx h

/-- No vertex is connected to a vertex outside `S` inside `S`. -/
theorem localConn_of_notMem_right {S : Set V} {y : V} (hy : y ∉ S) (x : V) :
    localConn S x y = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => hy h

/-- Inside the empty set nothing is connected. -/
@[simp]
theorem localConn_empty (x y : V) : localConn (∅ : Set V) x y = ∅ :=
  localConn_of_notMem (Set.notMem_empty x) y

/-- Connection inside a set is an increasing event. -/
theorem localConn_mono {S : Set V} {x y : V} {ω ω' : Config V} (h : ω ⊆ ω')
    (hxy : ω ∈ localConn S x y) : ω' ∈ localConn S x y := by
  obtain ⟨hx, hy, hr⟩ := hxy
  exact ⟨hx, hy, hr.mono fun _ _ hadj => openGraph_mono h hadj⟩

/-- Connection inside a set is an upper set of configurations. -/
theorem isUpperSet_localConn (S : Set V) (x y : V) : IsUpperSet (localConn S x y) :=
  fun _ _ h hxy => localConn_mono h hxy

/-- Connection inside a countable set is measurable, whatever the cardinality of the
vertex type. -/
theorem measurableSet_localConn (S : Set V) [Countable S] (x y : V) :
    MeasurableSet (localConn S x y) := by
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · have hmeas : Measurable fun ω : Config V => Sym2.map (Subtype.val : S → V) ⁻¹' ω :=
        measurable_set_iff.mpr fun e => measurable_set_mem (Sym2.map Subtype.val e)
      have hset : localConn S x y =
          (fun ω : Config V => Sym2.map (Subtype.val : S → V) ⁻¹' ω) ⁻¹'
            conn (⟨x, hx⟩ : S) ⟨y, hy⟩ := by
        ext ω
        rw [mem_localConn_iff_reachable hx hy, Set.mem_preimage, mem_conn_iff]
        have hG : (openGraph ω).induce S =
            openGraph (Sym2.map (Subtype.val : S → V) ⁻¹' ω) := by
          ext a b
          simp [SimpleGraph.induce, SimpleGraph.comap_adj, openGraph_adj_iff, Subtype.coe_inj]
        rw [hG]
      rw [hset]
      exact (measurableSet_conn _ _).preimage hmeas
    · rw [localConn_of_notMem_right hy]
      exact MeasurableSet.empty
  · rw [localConn_of_notMem hx]
    exact MeasurableSet.empty

/-- The restricted cluster `K_x^S` of `x` in `S`: the vertices joined to `x` by an open path
all of whose vertices lie in `S`. It is empty when `x ∉ S`, and contains `x` when
`x ∈ S`. -/
@[tag "OG96"]
def localCluster (ω : Config V) (S : Set V) (x : V) : Set V := {y | ω ∈ localConn S x y}

@[simp]
theorem mem_localCluster {ω : Config V} {S : Set V} {x y : V} :
    y ∈ localCluster ω S x ↔ ω ∈ localConn S x y :=
  Iff.rfl

/-- A vertex of `S` belongs to its own restricted cluster. -/
theorem mem_localCluster_self (ω : Config V) {S : Set V} {x : V} (hx : x ∈ S) :
    x ∈ localCluster ω S x := by
  rw [mem_localCluster, localConn_self hx]
  exact Set.mem_univ ω

/-- The restricted cluster in the whole vertex set is the cluster. -/
theorem localCluster_univ (ω : Config V) (x : V) :
    localCluster ω Set.univ x = cluster ω x := by
  ext y
  rw [mem_localCluster, localConn_univ, mem_cluster_iff]

/-- The restricted cluster lies in the intersection of the cluster with the set. -/
theorem localCluster_subset (ω : Config V) (S : Set V) (x : V) :
    localCluster ω S x ⊆ cluster ω x ∩ S :=
  fun y hy => ⟨(mem_cluster_iff ω x y).2 (localConn_subset_conn S x y hy), hy.2.1⟩

/-- The restricted cluster grows with the set. -/
theorem localCluster_mono_set (ω : Config V) {S T : Set V} (h : S ⊆ T) (x : V) :
    localCluster ω S x ⊆ localCluster ω T x :=
  fun _ hy => localConn_mono_set h _ _ hy

/-- The restricted cluster of a vertex outside the set is empty. -/
theorem localCluster_of_notMem (ω : Config V) {S : Set V} {x : V} (hx : x ∉ S) :
    localCluster ω S x = ∅ := by
  ext y
  rw [mem_localCluster, localConn_of_notMem hx]
  simp

/-! #### Ordered cuts -/

section IsCut

variable [Preorder V]

/-- `k` is a cut of the configuration `ω`: no open pair joins a vertex `a ≤ k` to a vertex
`b > k`. -/
def IsCut (ω : Config V) (k : V) : Prop := ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω

theorem isCut_iff {ω : Config V} {k : V} :
    IsCut ω k ↔ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω :=
  Iff.rfl

/-- A cut of a configuration is a cut of every smaller configuration. -/
theorem IsCut.mono {ω ω' : Config V} {k : V} (h : ω' ⊆ ω) (hk : IsCut ω k) : IsCut ω' k :=
  fun a b ha hb hab => hk a b ha hb (h hab)

/-- Every vertex is a cut of the empty configuration. -/
@[simp]
theorem isCut_empty (k : V) : IsCut (∅ : Config V) k :=
  fun _ _ _ _ h => h

/-- Being a cut at `k` is a measurable event when there are countably many vertices. -/
theorem measurableSet_setOf_isCut [Countable V] (k : V) :
    MeasurableSet {ω : Config V | IsCut ω k} := by
  simp only [IsCut, Set.ofPred_forall]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (measurableSet_mem s(a, b)).compl

end IsCut

/-! #### Boundary flux -/

open Classical in
/-- The boundary flux of a finite set `S` seen from `o`:
`∑_{u ∈ S} ∑_{v ∉ S} P_q(o ↔ u inside S) q(u, v)`, the expected weight of the pairs leaving
`S` from a vertex joined to `o` inside `S`. It is `0` when `o ∉ S`. For `q` equal to `p`
on the nearest-neighbour edges and `0` elsewhere it is
`p ∑_{u ∈ S, v ∉ S, u ∼ v} P_p(o ↔ u inside S)`. -/
@[tag "6EIM"]
def boundaryFlux (q : Sym2 V → unitInterval) (S : Finset V) (o : V) : ℝ≥0∞ :=
  ∑ u ∈ S, ∑' v, (if v ∈ S then 0 else
    law q (localConn (S : Set V) o u) * (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))

open Classical in
theorem boundaryFlux_def (q : Sym2 V → unitInterval) (S : Finset V) (o : V) :
    boundaryFlux q S o = ∑ u ∈ S, ∑' v, (if v ∈ S then 0 else
      law q (localConn (S : Set V) o u) * (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) :=
  rfl

/-- Unfolding `boundaryFlux`, for any decidability instance on `V`. -/
theorem boundaryFlux_eq [DecidableEq V] (q : Sym2 V → unitInterval) (S : Finset V) (o : V) :
    boundaryFlux q S o = ∑ u ∈ S, ∑' v, (if v ∈ S then 0 else
      law q (localConn (S : Set V) o u) * (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) := by
  simp only [boundaryFlux]
  exact Finset.sum_congr rfl fun u _ => tsum_congr fun v => by congr

/-- The boundary flux of a set not containing `o` vanishes. -/
theorem boundaryFlux_of_notMem (q : Sym2 V → unitInterval) {S : Finset V} {o : V}
    (ho : o ∉ S) : boundaryFlux q S o = 0 := by
  classical
  rw [boundaryFlux_eq]
  simp [localConn_of_notMem (Finset.mem_coe.not.2 ho)]

@[simp]
theorem boundaryFlux_empty (q : Sym2 V → unitInterval) (o : V) :
    boundaryFlux q (∅ : Finset V) o = 0 :=
  boundaryFlux_of_notMem q (Finset.notMem_empty o)

/-- For `S = {o}` the boundary flux is the row sum of the profile at `o`: the boundary
flux is not identically zero. -/
theorem boundaryFlux_singleton (q : Sym2 V → unitInterval) (o : V) :
    boundaryFlux q {o} o = rowSum (fun e => unitInterval.toENNReal (q e)) o := by
  classical
  rw [boundaryFlux_eq, Finset.sum_singleton, rowSum_def, Finset.coe_singleton,
    localConn_self (Set.mem_singleton o), measure_univ]
  refine tsum_congr fun v => ?_
  simp only [Finset.mem_singleton, one_mul]
  rfl

end LocalConn

/-! ### Non-vacuity of the restricted notions -/

/-- On the path `0 - 1 - 2` with both edges open, `0` and `2` are connected, but not inside
`{0, 2}`: connection inside a set is not connection of two vertices of the set. -/
example : ({s(0, 1), s(1, 2)} : Config (Fin 3)) ∈ conn 0 2 ∧
    ({s(0, 1), s(1, 2)} : Config (Fin 3)) ∉ localConn {0, 2} 0 2 := by
  refine ⟨conn_trans (y := 1) (mem_conn_of_mem (by decide) (by simp))
    (mem_conn_of_mem (by decide) (by simp)), ?_⟩
  rintro ⟨h0, h2, hr⟩
  have hbot : (openGraph ({s(0, 1), s(1, 2)} : Config (Fin 3))).induce {0, 2} = ⊥ := by
    ext a b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj_iff,
      SimpleGraph.bot_adj, iff_false, not_and]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  rw [hbot, SimpleGraph.reachable_bot] at hr
  exact absurd (congrArg Subtype.val hr) (show (0 : Fin 3) ≠ 2 by decide)

/-- The connection probability is computed for a law that is not a product law: under
the Dirac mass at the configuration with the single open pair `{false, true}` the two
vertices of `Bool` are connected with probability one, and under the Dirac mass at the
empty configuration with probability zero. -/
example : connProb (Measure.dirac ({s(false, true)} : Config Bool)) false true = 1 ∧
    connProb (Measure.dirac (∅ : Config Bool)) false true = 0 := by
  refine ⟨Measure.dirac_apply_of_mem (mem_conn_of_mem (by decide) rfl), ?_⟩
  rw [connProb, Measure.dirac_apply' _ (measurableSet_conn false true),
    Set.indicator_of_notMem (by rw [empty_mem_conn_iff]; decide)]

/-- With every pair open, `0` is not a cut of the integers. -/
example : ¬ IsCut (Set.univ : Config ℤ) 0 :=
  fun h => h 0 1 le_rfl zero_lt_one (Set.mem_univ _)


end PercLib.Percolation.Bond

end
