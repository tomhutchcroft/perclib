/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Uniform positivity of the connection kernel from singleton-cluster probabilities (wiki article
`connection-kernels`). New proofs; nothing is copied, no definition is added.
-/
module

public import PercLib.Percolation.Bond.ConnectionKernel
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Percolation.Bond.DegreeGenerating
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Uniform kernel positivity from singleton probabilities

For a law `μ` of bond configurations, `T(x, y) = μ(x ↔ y)` and `p_x = μ(C(x) = {x})`. Every
finitely supported real `f` satisfies `∑_{x,y} f(x) T(x,y) f(y) ≥ ∑_x p_x f(x)^2`: in the
cluster-square identity, only the singleton clusters are kept. Under the product law with
`q(x, y) = 1 - e^{-β J(x,y)}` and `∑_{y ≠ x} J(x, y) ≤ L`, `p_x ≥ e^{-β L}`.

## Main results

* `sum_mul_indicator_conn_ge_sum_isolated`: the pointwise inequality.
* `sum_finset_mul_connProb_ge_sum_isolated`: `∑_{x,y ∈ F} f f T ≥ ∑_{x ∈ F} p_x f(x)^2`.
* `sum_finset_mul_connProb_ge_mul_sum_sq`: `T ⪰ δ I` when `p_x ≥ δ` for every `x`.
* `setOf_cluster_eq_singleton`: `C(x) = {x}` exactly when `x` has no open neighbour.
* `exp_neg_mul_le_law_cluster_eq_singleton`: `p_x ≥ e^{-β L}` for the exponential product law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- Pointwise splitting of one term: with `b = a` off the singleton clusters and `b = 0` on
them, `a_u a_v 1[u ↔ v] = b_u b_v 1[u ↔ v] + 1[u = v, C(u) = {u}] a_u²`. -/
theorem mul_indicator_conn_eq_add (ω : Config V) (a : V → ℝ) (u v : V) :
    a u * a v * (conn u v).indicator (fun _ => (1 : ℝ)) ω =
      (if cluster ω u = {u} then 0 else a u) * (if cluster ω v = {v} then 0 else a v) *
          (conn u v).indicator (fun _ => (1 : ℝ)) ω +
        if u = v then (if cluster ω u = {u} then a u ^ 2 else 0) else 0 := by
  classical
  have hsing : ∀ {x y : V}, cluster ω x = {x} → x ≠ y → ω ∉ conn x y := fun {x y} hx hxy h => by
    have hy : y ∈ cluster ω x := h
    rw [hx, mem_singleton_iff] at hy
    exact hxy hy.symm
  by_cases huv : u = v
  · subst huv
    have h1 : ω ∈ conn u u := SimpleGraph.Reachable.refl u
    by_cases hu : cluster ω u = {u} <;> simp [Set.indicator_of_mem h1, hu, sq]
  · have hc : ∀ h : ω ∈ conn u v, cluster ω u ≠ {u} ∧ cluster ω v ≠ {v} := fun h =>
      ⟨fun hu => hsing hu huv h, fun hv => hsing hv (Ne.symm huv) (SimpleGraph.Reachable.symm h)⟩
    by_cases h : ω ∈ conn u v
    · simp [Set.indicator_of_mem h, huv, (hc h).1, (hc h).2]
    · simp [Set.indicator_of_notMem h, huv]

open Classical in
/-- **Pointwise singleton bound.** For a finite set `F`,
`∑_{u,v ∈ F} a_u a_v 1[u ↔ v] ≥ ∑_{u ∈ F} 1[C(u) = {u}] a_u²`. -/
theorem sum_mul_indicator_conn_ge_sum_isolated (ω : Config V) (F : Finset V) (a : V → ℝ) :
    ∑ u ∈ F, (if cluster ω u = {u} then a u ^ 2 else 0) ≤
      ∑ u ∈ F, ∑ v ∈ F, a u * a v * (conn u v).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  simp_rw [mul_indicator_conn_eq_add ω a, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun u hu => (Finset.sum_ite_eq F u
    (fun _ => if cluster ω u = {u} then a u ^ 2 else 0)).trans
      (ite_eq_left_iff.2 fun h => absurd hu h)]
  refine le_add_of_nonneg_left ?_
  have h := sum_mul_indicator_conn_nonneg ω (fun u : F => (u : V))
    (fun u => if cluster ω u = {(u : V)} then 0 else a u)
  rw [← Finset.sum_coe_sort F]
  convert h using 2 with u
  rw [← Finset.sum_coe_sort F]

open Classical in
/-- **Singleton bound for the connection kernel.** For a finite measure `μ`, a finite set `F`
and real `a`, `∑_{u,v ∈ F} a_u a_v T(u,v) ≥ ∑_{u ∈ F} μ(C(u) = {u}) a_u²`. -/
theorem sum_finset_mul_connProb_ge_sum_isolated [Countable V] (μ : Measure (Config V))
    [IsFiniteMeasure μ] (F : Finset V) (a : V → ℝ) :
    ∑ u ∈ F, (μ {ω | cluster ω u = {u}}).toReal * a u ^ 2 ≤
      ∑ u ∈ F, ∑ v ∈ F, a u * a v * (connProb μ u v).toReal := by
  classical
  have hmeas : ∀ u : V, MeasurableSet {ω : Config V | cluster ω u = {u}} := fun u =>
    measurableSet_setOf_cluster_eq u {u}
  have hint : ∀ u v, Integrable (fun ω => a u * a v *
      (conn u v).indicator (fun _ => (1 : ℝ)) ω) μ := fun u v =>
    ((integrable_const (1 : ℝ)).indicator (measurableSet_conn u v)).const_mul _
  have hint' : ∀ u, Integrable (fun ω => if cluster ω u = {u} then a u ^ 2 else 0) μ := fun u => by
    have : (fun ω => if cluster ω u = {u} then a u ^ 2 else 0) =
        {ω : Config V | cluster ω u = {u}}.indicator (fun _ => a u ^ 2) := by
      funext ω; simp [Set.indicator_apply]
    rw [this]
    exact (integrable_const _).indicator (hmeas u)
  have hlhs : ∑ u ∈ F, (μ {ω | cluster ω u = {u}}).toReal * a u ^ 2 =
      ∫ ω, ∑ u ∈ F, (if cluster ω u = {u} then a u ^ 2 else 0) ∂μ := by
    rw [integral_finsetSum _ fun u _ => hint' u]
    refine Finset.sum_congr rfl fun u _ => ?_
    have : (fun ω => if cluster ω u = {u} then a u ^ 2 else 0) =
        {ω : Config V | cluster ω u = {u}}.indicator (fun _ => a u ^ 2) := by
      funext ω; simp [Set.indicator_apply]
    rw [this, integral_indicator_const _ (hmeas u), smul_eq_mul, measureReal_def]
  have hrhs : ∑ u ∈ F, ∑ v ∈ F, a u * a v * (connProb μ u v).toReal =
      ∫ ω, ∑ u ∈ F, ∑ v ∈ F, a u * a v * (conn u v).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => hint u v]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_finsetSum _ fun v _ => hint u v]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (measurableSet_conn u v),
      smul_eq_mul, mul_one, measureReal_def]
    rfl
  rw [hlhs, hrhs]
  exact integral_mono (integrable_finsetSum _ fun u _ => hint' u)
    (integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => hint u v)
    fun ω => sum_mul_indicator_conn_ge_sum_isolated ω F a

/-- **Uniform kernel positivity.** If `μ(C(x) = {x}) ≥ δ` for every `x`, then
`∑_{u,v ∈ F} a_u a_v T(u,v) ≥ δ ∑_{u ∈ F} a_u²`. -/
theorem sum_finset_mul_connProb_ge_mul_sum_sq [Countable V] (μ : Measure (Config V))
    [IsFiniteMeasure μ] {δ : ℝ} (hδ : ∀ x, δ ≤ (μ {ω | cluster ω x = {x}}).toReal)
    (F : Finset V) (a : V → ℝ) :
    δ * ∑ u ∈ F, a u ^ 2 ≤ ∑ u ∈ F, ∑ v ∈ F, a u * a v * (connProb μ u v).toReal := by
  refine le_trans ?_ (sum_finset_mul_connProb_ge_sum_isolated μ F a)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (hδ u) (sq_nonneg _)

/-- The cluster of `x` is `{x}` exactly when `x` has no open neighbour. -/
theorem setOf_cluster_eq_singleton (x : V) :
    {ω : Config V | cluster ω x = {x}} =
      {ω : Config V | {w | (openGraph ω).Adj x w}.encard = 0} := by
  ext ω
  simp only [mem_ofPred_eq, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h w hw
    have hw' : w ∈ cluster ω x := hw.reachable
    rw [h, mem_singleton_iff] at hw'
    subst hw'
    exact (openGraph ω).loopless.irrefl _ hw
  · intro h
    ext y
    simp only [mem_singleton_iff]
    constructor
    · rintro ⟨p⟩
      cases p with
      | nil => rfl
      | cons hadj _ => exact absurd hadj (h _)
    · rintro rfl
      exact SimpleGraph.Reachable.refl _

/-- **Singleton probability under exponential bond probabilities.** If
`q(x, y) = 1 - e^{-β J(x,y)}` for `x ≠ y`, with `β ≥ 0`, `J ≥ 0` and
`∑_{y ≠ x} J(x, y) ≤ L` (a convergent sum), then `μ(C(x) = {x}) ≥ e^{-β L}`. -/
theorem exp_neg_mul_le_law_cluster_eq_singleton [Countable V] (q : Sym2 V → unitInterval)
    {β L : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (hq : ∀ x y : V, x ≠ y → (q s(x, y) : ℝ) = 1 - Real.exp (-(β * J s(x, y))))
    (x : V) (hJs : Summable fun y : {y // y ≠ x} => J s(x, y.1))
    (hL : ∑' y : {y // y ≠ x}, J s(x, y.1) ≤ L) :
    Real.exp (-(β * L)) ≤ (law q {ω : Config V | cluster ω x = {x}}).toReal := by
  have hfac : ∀ y : {y // y ≠ x}, (1 - (unitInterval.toNNReal (q s(x, y.1)) : ℝ≥0∞)) =
      ENNReal.ofReal (Real.exp (-(β * J s(x, y.1)))) := fun y => by
    rw [← Probability.coe_toNNReal_symm_eq_one_sub, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    change 1 - (q s(x, y.1) : ℝ) = _
    rw [hq x y.1 (Ne.symm y.2)]; ring
  have hle1 : ∀ y : {y // y ≠ x}, (1 - (unitInterval.toNNReal (q s(x, y.1)) : ℝ≥0∞)) ≤ 1 :=
    fun _ => tsub_le_self
  have hbound : ENNReal.ofReal (Real.exp (-(β * L))) ≤
      law q {ω : Config V | cluster ω x = {x}} := by
    rw [setOf_cluster_eq_singleton, law_degree_eq_zero_eq_tprod,
      ENNReal.tprod_eq_iInf_prod hle1]
    refine le_iInf fun s => ?_
    simp_rw [hfac]
    rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le, ← Real.exp_sum]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left ((hJs.sum_le_tsum s fun y _ => hJ _).trans hL) hβ
  have := ENNReal.toReal_mono (measure_ne_top _ _) hbound
  rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

end PercLib.Percolation.Bond
