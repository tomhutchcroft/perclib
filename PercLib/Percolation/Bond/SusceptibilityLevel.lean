/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written for this project. Mathematical reference: the finite-graph
susceptibility normalization of Borgs, Chayes, van der Hofstad, Slade and Spencer, as
presented in Heydenreich and van der Hofstad, "Progress in high-dimensional percolation and
random graphs" (Springer, 2017).
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Russo
public import PercLib.Probability.VarianceTensorization
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Susceptibility levels on a finite connected graph

Independent bond percolation with parameter `p` on the edges of a finite graph `G` is the law
`law (fun e => if e ∈ G.edgeSet then p else 0)`. Its susceptibility at `v` is a polynomial in
`p`. When `G` is connected and has at least two vertices it is continuous and strictly
increasing on `[0, 1]`, from `1` to the number of vertices, so each level in between is attained
at exactly one parameter.

## Main results

* `FiniteProfile.expectation_indicator_profile`: at a `{0,1}`-valued profile the cube
  expectation is the value at the corresponding configuration.
* `toReal_chi_edgeSet_eq_expectation`: the susceptibility as a cube expectation.
* `exists_polynomial_toReal_chi_edgeSet`, `continuous_toReal_chi_edgeSet`: it is a polynomial
  in `p`, hence continuous.
* `toReal_chi_edgeSet_zero`, `toReal_chi_edgeSet_one`: the values `1` at `p = 0` and `|V|` at
  `p = 1` on a connected graph.
* `strictMono_toReal_chi_edgeSet`, `strictMono_toReal_chi_edgeSet_of_connected`: strict
  monotonicity in `p` when `v` has a neighbour, in particular on a connected graph with at least
  two vertices.
* `existsUnique_toReal_chi_edgeSet_eq`, `toReal_chi_edgeSet_mem_Icc` and
  `pos_and_lt_one_iff_of_toReal_chi_edgeSet`: each level in `[1, |V|]` is attained at exactly
  one parameter, no other level is attained, and the parameter is interior exactly when the
  level is.
* `eventually_one_lt_mul_rpow_and_lt`: for fixed `λ > 0` the level `λ N^{1/3}` is interior for
  all large `N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial PercLib.Probability PercLib.Probability.FiniteProfile
open scoped ENNReal unitInterval

namespace PercLib.Probability.FiniteProfile

variable {E : Type*} [Fintype E]

/-- At a profile taking only the values `0` and `1`, the cube expectation is the value of the
observable at the configuration that opens exactly the coordinates of value `1`. -/
theorem expectation_indicator_profile (b : E → Bool) (f : (E → Bool) → ℝ) :
    expectation (fun e => if b e then 1 else 0) f = f b := by
  classical
  unfold expectation
  rw [Finset.sum_eq_single b]
  · unfold weight
    rw [Finset.prod_eq_one (fun e _ => by cases h : b e <;> simp [h]), mul_one]
  · intro ω _ hω
    obtain ⟨e, he⟩ : ∃ e, ω e ≠ b e := by
      by_contra h
      push Not at h
      exact hω (funext h)
    unfold weight
    rw [Finset.prod_eq_zero (Finset.mem_univ e) (by cases h : b e <;> simp_all), mul_zero]
  · simp

end PercLib.Probability.FiniteProfile

namespace PercLib.Percolation.Bond

variable {V : Type*} [Fintype V]

open Classical in
/-- On a finite vertex set, the susceptibility (as a real number) is the cube expectation of
the cluster size. -/
theorem toReal_chi_eq_expectation (q : Sym2 V → unitInterval) (v : V) :
    (chi q v).toReal =
      expectation (fun e => (q e : ℝ)) (fun ω => ((cluster (toSet ω) v).ncard : ℝ)) := by
  have h := integral_prodBernoulli_eq_expectation q (fun s => ((cluster s v).ncard : ℝ))
  rw [← h, chi, law,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity)
      (Measurable.of_discrete).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun ω => ?_
  simp only [ENNReal.ofReal_natCast]
  rw [← (Set.toFinite (cluster ω v)).cast_ncard_eq]
  rfl

open Classical in
/-- The susceptibility of bond percolation with parameter `p` on the edges of `G`, as a cube
expectation of the cluster size. -/
theorem toReal_chi_edgeSet_eq_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (p : I) (v : V) :
    (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal =
      expectation (fun e => if e ∈ G.edgeSet then (p : ℝ) else 0)
        (fun ω => ((cluster (toSet ω) v).ncard : ℝ)) := by
  rw [toReal_chi_eq_expectation]
  congr 1
  funext e
  split_ifs <;> simp

open Classical in
/-- The susceptibility of bond percolation with parameter `p` on the edges of a finite graph
is a polynomial in `p`. -/
theorem exists_polynomial_toReal_chi_edgeSet (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ∃ P : ℝ[X], ∀ p : I,
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal = P.eval (p : ℝ) := by
  refine ⟨∑ ω : Sym2 V → Bool, C ((cluster (toSet ω) v).ncard : ℝ) *
    ∏ e, (if ω e then (if e ∈ G.edgeSet then X else 0)
      else 1 - (if e ∈ G.edgeSet then X else 0)), fun p => ?_⟩
  rw [toReal_chi_edgeSet_eq_expectation]
  simp only [expectation, weight, eval_finsetSum, eval_mul, eval_C, eval_prod]
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _)
    fun ω _ => congrArg _ (Finset.prod_congr rfl fun e _ => ?_)
  split_ifs <;> simp

/-- The susceptibility of bond percolation on the edges of a finite graph is continuous in the
parameter. -/
theorem continuous_toReal_chi_edgeSet (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Continuous fun p : I =>
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal := by
  classical
  obtain ⟨P, hP⟩ := exists_polynomial_toReal_chi_edgeSet G v
  simp_rw [hP]
  exact P.continuous.comp continuous_subtype_val

/-- At parameter `0` the susceptibility is `1`. -/
theorem toReal_chi_edgeSet_zero (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (chi (fun e => if e ∈ G.edgeSet then (0 : I) else 0) v).toReal = 1 := by
  classical
  rw [toReal_chi_edgeSet_eq_expectation]
  have h := expectation_indicator_profile (fun _ : Sym2 V => false)
    (fun ω => ((cluster (toSet ω) v).ncard : ℝ))
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  simp only [Set.Icc.coe_zero, ite_self]
  rw [h]
  have : cluster (toSet (fun _ : Sym2 V => false)) v = {v} := by
    ext y
    simp only [toSet, Bool.false_eq_true, Set.ofPred_false, Set.mem_singleton_iff]
    rw [mem_cluster_iff, empty_mem_conn_iff, eq_comm]
  rw [this, Set.ncard_singleton, Nat.cast_one]

/-- At parameter `1` the susceptibility of a connected graph is its number of vertices. -/
theorem toReal_chi_edgeSet_one {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected) (v : V) :
    (chi (fun e => if e ∈ G.edgeSet then (1 : I) else 0) v).toReal = Fintype.card V := by
  classical
  rw [toReal_chi_edgeSet_eq_expectation]
  have h := expectation_indicator_profile (fun e : Sym2 V => decide (e ∈ G.edgeSet))
    (fun ω => ((cluster (toSet ω) v).ncard : ℝ))
  simp only [decide_eq_true_eq] at h
  simp only [Set.Icc.coe_one]
  rw [h]
  have : cluster (toSet fun e : Sym2 V => decide (e ∈ G.edgeSet)) v = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hs : toSet (fun e : Sym2 V => decide (e ∈ G.edgeSet)) = G.edgeSet := by
      ext e; simp [toSet]
    rw [hs, mem_cluster_iff, mem_conn_iff, openGraph, SimpleGraph.fromEdgeSet_edgeSet]
    exact hG.preconnected v y
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card]

open Classical in
/-- Russo's formula for the parameter of bond percolation on the edges of `G`, in the cube
expectation form, at every real parameter. -/
theorem hasDerivAt_expectation_edgeSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : (Sym2 V → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => expectation (fun e => if e ∈ G.edgeSet then u else 0) f)
      (∑ e, (if e ∈ G.edgeSet then 1 else 0) *
        expectation (fun j => if j ∈ G.edgeSet then t else 0) (difference e f)) t :=
  expectation_hasDerivAt (fun e u => if e ∈ G.edgeSet then u else 0)
    (fun e => if e ∈ G.edgeSet then 1 else 0) t
    (fun e => by
      by_cases h : e ∈ G.edgeSet
      · simpa [h] using hasDerivAt_id' t
      · simpa [h] using hasDerivAt_const t (0 : ℝ)) f

open Classical in
/-- The cluster size of `v` grows when a coordinate is forced open. -/
theorem ncard_cluster_toSet_force_le (v : V) (e : Sym2 V) (ω : Sym2 V → Bool) :
    (cluster (toSet (force e false ω)) v).ncard ≤ (cluster (toSet (force e true ω)) v).ncard :=
  Set.ncard_le_ncard (fun _ hy => conn_mono (force_false_subset_true e ω) hy) (Set.toFinite _)

open Classical in
/-- The derivative of the susceptibility in the edge parameter is positive on `[0, 1)` when
`v` has a neighbour. -/
theorem expectation_edgeSet_deriv_pos {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} (hvw : G.Adj v w) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < ∑ e, (if e ∈ G.edgeSet then 1 else 0) *
        expectation (fun j => if j ∈ G.edgeSet then t else 0)
          (difference e fun ω => ((cluster (toSet ω) v).ncard : ℝ)) := by
  set g : (Sym2 V → Bool) → ℝ := fun ω => ((cluster (toSet ω) v).ncard : ℝ)
  set q : Sym2 V → ℝ := fun j => if j ∈ G.edgeSet then t else 0
  have hq0 : ∀ j, 0 ≤ q j := fun j => by simp only [q]; split_ifs <;> linarith
  have hq1 : ∀ j, q j ≤ 1 := fun j => by simp only [q]; split_ifs <;> linarith
  have hdiff : ∀ e ω, 0 ≤ difference e g ω := fun e ω => by
    simp only [difference, g, sub_nonneg, Nat.cast_le]
    exact ncard_cluster_toSet_force_le v e ω
  have hterm : ∀ e, 0 ≤ expectation q (difference e g) := fun e =>
    Finset.sum_nonneg fun ω _ =>
      mul_nonneg (hdiff e ω) (weight_nonneg (fun j => ⟨hq0 j, hq1 j⟩) ω)
  have he : s(v, w) ∈ G.edgeSet := hvw
  refine Finset.sum_pos' (fun e _ => mul_nonneg (by split_ifs <;> norm_num) (hterm e))
    ⟨s(v, w), Finset.mem_univ _, ?_⟩
  simp only [he, ↓reduceIte, one_mul]
  set ω₀ : Sym2 V → Bool := fun _ => false
  have hw : 0 < weight q ω₀ :=
    Finset.prod_pos fun j _ => by
      simp only [ω₀, q, Bool.false_eq_true, ↓reduceIte]; split_ifs <;> linarith
  have hd : 0 < difference (s(v, w)) g ω₀ := by
    have hfalse : toSet (force (s(v, w)) false ω₀) = ∅ := by
      ext j; simp [toSet, force, ω₀, Function.update_apply]
    have htrue : s(v, w) ∈ toSet (force (s(v, w)) true ω₀) := by
      simp [toSet, force]
    have h1 : cluster (toSet (force (s(v, w)) false ω₀)) v = {v} := by
      ext y
      rw [hfalse, Set.mem_singleton_iff, mem_cluster_iff, empty_mem_conn_iff, eq_comm]
    have h2 : {v, w} ⊆ cluster (toSet (force (s(v, w)) true ω₀)) v := by
      rintro y (rfl | rfl)
      · exact SimpleGraph.Reachable.refl _
      · exact mem_conn_of_mem hvw.ne htrue
    have h3 : 2 ≤ (cluster (toSet (force (s(v, w)) true ω₀)) v).ncard := by
      rw [← Set.ncard_pair hvw.ne]
      exact Set.ncard_le_ncard h2 (Set.toFinite _)
    simp only [difference, g, h1, Set.ncard_singleton, sub_pos]
    exact_mod_cast h3
  calc 0 < difference (s(v, w)) g ω₀ * weight q ω₀ := mul_pos hd hw
    _ ≤ expectation q (difference (s(v, w)) g) :=
      Finset.single_le_sum (f := fun ω => difference (s(v, w)) g ω * weight q ω)
        (fun ω _ => mul_nonneg (hdiff _ ω) (weight_nonneg (fun j => ⟨hq0 j, hq1 j⟩) ω))
        (by simp)

/-- When `v` has a neighbour in `G`, the susceptibility at `v` is strictly increasing in the
parameter. -/
theorem strictMono_toReal_chi_edgeSet {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} (hvw : G.Adj v w) :
    StrictMono fun p : I =>
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal := by
  classical
  set F : ℝ → ℝ := fun u => expectation (fun e => if e ∈ G.edgeSet then u else 0)
    (fun ω => ((cluster (toSet ω) v).ncard : ℝ))
  have hD := hasDerivAt_expectation_edgeSet G (fun ω => ((cluster (toSet ω) v).ncard : ℝ))
  have hF : StrictMonoOn F (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun u _ => (hD u).continuousAt.continuousWithinAt) fun u hu => ?_
    rw [interior_Icc] at hu
    rw [(hD u).deriv]
    exact expectation_edgeSet_deriv_pos hvw hu.1.le hu.2
  intro a b hab
  simp only [toReal_chi_edgeSet_eq_expectation]
  exact hF a.2 b.2 hab

/-- On a connected graph with at least two vertices, the susceptibility at every vertex is
strictly increasing in the parameter. -/
theorem strictMono_toReal_chi_edgeSet_of_connected {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Connected) (hcard : 1 < Fintype.card V) (v : V) :
    StrictMono fun p : I =>
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal :=
  haveI := Fintype.one_lt_card_iff_nontrivial.mp hcard
  strictMono_toReal_chi_edgeSet (hG.preconnected.exists_adj_of_nontrivial v).choose_spec

/-- Every value of the susceptibility of a connected graph with at least two vertices lies in
`[1, |V|]`. -/
theorem toReal_chi_edgeSet_mem_Icc {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected)
    (hcard : 1 < Fintype.card V) (v : V) (p : I) :
    (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal ∈
      Icc (1 : ℝ) (Fintype.card V) := by
  obtain ⟨w, hvw⟩ := (haveI := Fintype.one_lt_card_iff_nontrivial.mp hcard
    hG.preconnected.exists_adj_of_nontrivial v)
  have hm := (strictMono_toReal_chi_edgeSet (G := G) hvw).monotone
  exact ⟨toReal_chi_edgeSet_zero G v ▸ hm p.2.1, toReal_chi_edgeSet_one hG v ▸ hm p.2.2⟩

/-- Each level in `[1, |V|]` is attained by the susceptibility of a connected graph with at
least two vertices at exactly one parameter. -/
theorem existsUnique_toReal_chi_edgeSet_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Connected)
    (hcard : 1 < Fintype.card V) (v : V) {c : ℝ} (hc : c ∈ Icc (1 : ℝ) (Fintype.card V)) :
    ∃! p : I, (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal = c := by
  obtain ⟨w, hvw⟩ := (haveI := Fintype.one_lt_card_iff_nontrivial.mp hcard
    hG.preconnected.exists_adj_of_nontrivial v)
  have hc' : c ∈ Icc ((chi (fun e => if e ∈ G.edgeSet then (0 : I) else 0) v).toReal)
      ((chi (fun e => if e ∈ G.edgeSet then (1 : I) else 0) v).toReal) := by
    rwa [toReal_chi_edgeSet_zero, toReal_chi_edgeSet_one hG]
  obtain ⟨p, hp⟩ := intermediate_value_univ 0 1 (continuous_toReal_chi_edgeSet G v) hc'
  exact ⟨p, hp, fun r hr => (strictMono_toReal_chi_edgeSet hvw).injective (hr.trans hp.symm)⟩

/-- For a connected graph with at least two vertices, the parameter at which the susceptibility
takes a value lies in `(0, 1)` exactly when the value lies in `(1, |V|)`. -/
theorem pos_and_lt_one_iff_of_toReal_chi_edgeSet {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Connected)
    (hcard : 1 < Fintype.card V) (v : V) (p : I) :
    (0 < p ∧ p < 1) ↔
      (1 < (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal ∧
        (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal < Fintype.card V) := by
  obtain ⟨w, hvw⟩ := (haveI := Fintype.one_lt_card_iff_nontrivial.mp hcard
    hG.preconnected.exists_adj_of_nontrivial v)
  have hs := strictMono_toReal_chi_edgeSet (G := G) hvw
  have h0 := toReal_chi_edgeSet_zero G v
  have h1 := toReal_chi_edgeSet_one hG v
  rw [← hs.lt_iff_lt (a := 0) (b := p), ← hs.lt_iff_lt (a := p) (b := 1)]
  simp only [h0, h1]

/-- For a fixed `λ > 0`, the level `λ N^{1/3}` lies strictly between `1` and `N` for all
sufficiently large `N`. -/
theorem eventually_one_lt_mul_rpow_and_lt {lam : ℝ} (hlam : 0 < lam) :
    ∀ᶠ N : ℕ in Filter.atTop,
      1 < lam * (N : ℝ) ^ (1 / 3 : ℝ) ∧ lam * (N : ℝ) ^ (1 / 3 : ℝ) < N := by
  have h3 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h23 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [(h3.const_mul_atTop hlam).eventually_gt_atTop 1,
    h23.eventually_gt_atTop lam, h3.eventually_gt_atTop 0] with N h1 h2 h0
  refine ⟨h1, ?_⟩
  have hN : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) N.cast_nonneg
    simp [this] at h0
  calc lam * (N : ℝ) ^ (1 / 3 : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right h2 h0
    _ = N := by rw [← Real.rpow_add hN]; norm_num

end PercLib.Percolation.Bond
