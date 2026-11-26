/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
C. Borgs, J. T. Chayes, R. van der Hofstad, G. Slade and J. Spencer, *Random subgraphs of
finite graphs: I. The scaling window under the triangle condition*, Random Structures
Algorithms 27 (2005), Section 8 and Appendix A.3 (the marked-volume strategy).
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.Ghost
public import PercLib.Percolation.Bond.TreeGraph.BranchPoint
public import PercLib.Percolation.Bond.ClusterMoments
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.MomentDerivativeBound
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Probability.CountableBK

/-!
# Marked-volume and damped-cluster moments on a finite vertex type

Let `V` be finite with `N` vertices, `q` a bond profile, and mark each vertex independently
with probability `γ ∈ (0,1)`; write `r = 1 - γ` and `μ` for the joint law of bonds and marks.
Put `S = |C_o|`, `M(x) = μ(x ↔ marks)`, `Z = ∑_x 1{x ↔ marks}` and `Q = ∫ Z² dμ`, and
`χ₀(x) = E[S_x r^{S_x}]`, `χ₁(x) = E[S_x (1 - r^{S_x})]`, `B = E[S² r^S]`. Marks are written
as a random set `η : Set V` with law `prodBernoulli (fun _ => γ)`; `x ↔ marks` is
`(cluster ω x ∩ η).Nonempty`. No definition is introduced.

## Main results

* `one_sub_one_sub_pow_le_mul`, `mul_mul_one_sub_pow_le`: the scalar inequalities
  `1 - r^s ≤ γ s` and `γ s r^s ≤ r (1 - r^s)`.
* `prod_setOf_mem_inter_marked_eq_lintegral`: a cluster meets the marks with probability
  `E[1 - r^{S_x}]`, also on a measurable event of the bonds.
* `sum_lintegral_ncard_mul_one_sub_pow_le_lintegral_sq` and
  `lintegral_sq_le_sum_mul_add_sum`: `∑_x χ₁(x) ≤ Q ≤ ∑_{x,y} M(x) M(y) + ∑_x χ₁(x)`; the
  off-diagonal decoupling is the BK inequality on the joint bond-and-mark configuration.
* `lintegral_ncard_sq_le_chi_pow_three`: under a transitive law `E S² ≤ χ³`, from the
  tree-graph inequality.
* Under a transitive law: `card_mul_lintegral_ncard_mul_one_sub_pow_le_lintegral_sq`
  (`N χ₁ ≤ Q`), `lintegral_sq_le_card_sq_mul_add_card_mul` (`Q ≤ N² M² + N χ₁`),
  `lintegral_ncard_mul_one_sub_pow_le` (`χ₁ ≤ γ χ³`), and for any profile
  `lintegral_ncard_mul_pow_le` (`χ₀ ≤ (r/γ) M`) and `lintegral_ncard_sq_mul_pow_le`
  (`B ≤ (r/γ) χ₁`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-! ### Scalar inequalities -/

/-- `1 - (1 - γ)^n ≤ γ n` for `γ ≤ 2` (Bernoulli's inequality). -/
theorem one_sub_one_sub_pow_le_mul {γ : ℝ} (h : γ ≤ 2) (n : ℕ) :
    1 - (1 - γ) ^ n ≤ γ * n := by
  have h' := one_add_mul_le_pow (show (-2 : ℝ) ≤ -γ by linarith) n
  rw [← sub_eq_add_neg] at h'
  linarith

/-- `γ n (1 - γ)^n ≤ (1 - γ)(1 - (1 - γ)^n)` for `γ ∈ [0, 1]`. -/
theorem mul_mul_one_sub_pow_le {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (n : ℕ) :
    γ * n * (1 - γ) ^ n ≤ (1 - γ) * (1 - (1 - γ) ^ n) := by
  have hx0 : 0 ≤ 1 - γ := by linarith
  have hx1 : 1 - γ ≤ 1 := by linarith
  rcases n with _ | k
  · simp
  have hsum : ((k + 1 : ℕ) : ℝ) * (1 - γ) ^ k ≤ ∑ i ∈ range (k + 1), (1 - γ) ^ i := by
    have := Finset.card_nsmul_le_sum (range (k + 1)) (fun i => (1 - γ) ^ i) ((1 - γ) ^ k)
      fun i hi => pow_le_pow_of_le_one hx0 hx1 (Nat.lt_succ_iff.1 (mem_range.1 hi))
    simpa using this
  have hg : (1 - (1 - γ)) * ∑ i ∈ range (k + 1), (1 - γ) ^ i = 1 - (1 - γ) ^ (k + 1) :=
    mul_neg_geom_sum _ _
  rw [← hg, pow_succ]
  have := mul_le_mul_of_nonneg_left hsum (mul_nonneg h0 hx0)
  nlinarith

section ENNRealScalar

variable (γ : unitInterval)

/-- `1 - r^n` as the extended real of `1 - (1 - γ)^n`. -/
theorem one_sub_ofReal_one_sub_pow (n : ℕ) :
    1 - ENNReal.ofReal (1 - γ) ^ n = ENNReal.ofReal (1 - (1 - γ) ^ n) := by
  have hx0 : 0 ≤ 1 - (γ : ℝ) := by linarith [γ.2.2]
  rw [← ENNReal.ofReal_pow hx0, ENNReal.ofReal_sub _ (pow_nonneg hx0 n), ENNReal.ofReal_one]

/-- `1 - r^n ≤ γ n`. -/
theorem one_sub_ofReal_one_sub_pow_le (n : ℕ) :
    1 - ENNReal.ofReal (1 - γ) ^ n ≤ ENNReal.ofReal γ * n := by
  rw [one_sub_ofReal_one_sub_pow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul γ.2.1]
  exact ENNReal.ofReal_le_ofReal (one_sub_one_sub_pow_le_mul (by linarith [γ.2.2]) n)

/-- `γ n r^n ≤ r (1 - r^n)`. -/
theorem ofReal_mul_mul_ofReal_one_sub_pow_le (n : ℕ) :
    ENNReal.ofReal γ * n * ENNReal.ofReal (1 - γ) ^ n ≤
      ENNReal.ofReal (1 - γ) * (1 - ENNReal.ofReal (1 - γ) ^ n) := by
  have hx0 : 0 ≤ 1 - (γ : ℝ) := by linarith [γ.2.2]
  rw [one_sub_ofReal_one_sub_pow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul γ.2.1,
    ← ENNReal.ofReal_pow hx0, ← ENNReal.ofReal_mul (mul_nonneg γ.2.1 n.cast_nonneg),
    ← ENNReal.ofReal_mul hx0]
  exact ENNReal.ofReal_le_ofReal (mul_mul_one_sub_pow_le γ.2.1 γ.2.2 n)

/-- From `γ a ≤ b` with `0 < γ` to `a ≤ b / γ` written as `(r / γ) X` when `b = r X`. -/
theorem le_div_mul_of_mul_le {g r a X : ℝ≥0∞} (hg0 : g ≠ 0) (hgt : g ≠ ⊤)
    (h : g * a ≤ r * X) : a ≤ r / g * X := by
  calc a = g⁻¹ * (g * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hg0 hgt, one_mul]
    _ ≤ g⁻¹ * (r * X) := by gcongr
    _ = r / g * X := by rw [ENNReal.div_eq_inv_mul, mul_assoc]

end ENNRealScalar

/-! ### Cluster facts -/

variable {V : Type*}

/-- The cluster size, as a natural number, is measurable. -/
theorem measurable_ncard_cluster [Countable V] (x : V) :
    Measurable fun ω : Config V => (cluster ω x).ncard := by
  have : (fun ω : Config V => (cluster ω x).ncard) =
      (fun n : ℕ∞ => n.toNat) ∘ fun ω => (cluster ω x).encard := by
    funext ω
    rfl
  rw [this]
  exact (measurable_of_countable _).comp (measurable_encard_cluster x)

/-- On a finite vertex type, the cluster size is the number of vertices connected to `x`. -/
theorem ncard_cluster_eq_sum [Fintype V] (ω : Config V) (x : V) :
    ((cluster ω x).ncard : ℝ≥0∞) = ∑ y, (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [← ENat.toENNReal_coe, Set.Finite.cast_ncard_eq (Set.toFinite _), encard_cluster_eq_tsum,
    tsum_fintype]

/-- A function of the cluster size integrates to the same value at every vertex of an orbit
of a law-preserving vertex bijection. -/
theorem lintegral_ncard_cluster_eq_of_map_law_eq (q : Sym2 V → unitInterval) (e : V ≃ V)
    (h : (law q).map (fun ω => Sym2.map e '' ω) = law q) (F : ℕ → ℝ≥0∞) (x : V) :
    ∫⁻ ω, F (cluster ω (e x)).ncard ∂law q = ∫⁻ ω, F (cluster ω x).ncard ∂law q := by
  conv_lhs => rw [← h, lintegral_map_image_sym2Map]
  simp_rw [cluster_image, Set.ncard_image_of_injective _ e.injective]

/-! ### Marks -/

/-- With marks of probability `γ ∈ (0,1)`, a finite set meets the marks with probability
`1 - (1 - γ)^{|A|}`. -/
theorem prodBernoulli_inter_nonempty_eq_one_sub_pow [Finite V] {γ : unitInterval}
    (hγ0 : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (A : Set V) :
    prodBernoulli (fun _ : V => γ) {g | (A ∩ g).Nonempty} =
      1 - ENNReal.ofReal (1 - γ) ^ A.ncard := by
  have hpos : 0 < 1 - (γ : ℝ) := by linarith
  have hh : 0 < -Real.log (1 - γ) := neg_pos.2 (Real.log_neg hpos (by linarith))
  have hp : ((unitInterval.symm γ : unitInterval) : ℝ) = Real.exp (-(-Real.log (1 - γ))) := by
    rw [neg_neg, Real.exp_log hpos, unitInterval.coe_symm_eq]
  rw [prodBernoulli_inter_nonempty hh hp, ← (Set.toFinite A).cast_ncard_eq,
    exp_neg_mul_natCast, neg_neg, Real.exp_log hpos]

variable [Fintype V] (q : Sym2 V → unitInterval) {γ : unitInterval}

/-- The event that the cluster of `x` meets the marks is measurable. -/
theorem measurableSet_marked (x : V) :
    MeasurableSet {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty} :=
  measurableSet_prod_inter_nonempty fun v => measurableSet_conn x v

/-- **Mark probability on a bond event.** For a measurable event `E` of the bonds,
`μ(E, x ↔ marks) = E[1_E (1 - r^{S_x})]`. -/
theorem prod_setOf_mem_inter_marked_eq_lintegral (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    {E : Set (Config V)} (hE : MeasurableSet E) (x : V) :
    ((law q).prod (prodBernoulli fun _ : V => γ))
        ({z | z.1 ∈ E} ∩ {z | (cluster z.1 x ∩ z.2).Nonempty}) =
      ∫⁻ ω, E.indicator (fun ω => 1 - ENNReal.ofReal (1 - γ) ^ (cluster ω x).ncard) ω
        ∂law q := by
  rw [Measure.prod_apply (show MeasurableSet ({z : Config V × Set V | z.1 ∈ E} ∩
    {z | (cluster z.1 x ∩ z.2).Nonempty}) from (measurable_fst hE).inter (measurableSet_marked x))]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ E
  · rw [indicator_of_mem hω, ← prodBernoulli_inter_nonempty_eq_one_sub_pow hγ0 hγ1]
    congr 1
    ext g
    simp [hω]
  · rw [indicator_of_notMem hω]
    simp [hω]

/-- **Mark probability.** `μ(x ↔ marks) = E[1 - r^{S_x}]`. -/
theorem prod_marked_eq_lintegral (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (x : V) :
    ((law q).prod (prodBernoulli fun _ : V => γ)) {z | (cluster z.1 x ∩ z.2).Nonempty} =
      ∫⁻ ω, 1 - ENNReal.ofReal (1 - γ) ^ (cluster ω x).ncard ∂law q := by
  have h := prod_setOf_mem_inter_marked_eq_lintegral q hγ0 hγ1 MeasurableSet.univ x
  simp only [mem_univ, ofPred_true, univ_inter, indicator_univ] at h
  exact h

/-! ### The second moment of the marked volume -/

/-- `Q` expands as the double sum `∑_{x,y} μ(x ↔ marks, y ↔ marks)`. -/
theorem lintegral_sq_sum_indicator_marked_eq (γ : unitInterval) :
    ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
        (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) =
      ∑ x, ∑ y, ((law q).prod (prodBernoulli fun _ : V => γ))
        ({z | (cluster z.1 x ∩ z.2).Nonempty} ∩ {z | (cluster z.1 y ∩ z.2).Nonempty}) := by
  have key : ∀ (z : Config V × Set V) (s t : Set (Config V × Set V)),
      s.indicator (fun _ => (1 : ℝ≥0∞)) z * t.indicator (fun _ => (1 : ℝ≥0∞)) z =
        (s ∩ t).indicator (fun _ => 1) z := by
    intro z s t
    by_cases hs : z ∈ s
    · by_cases ht : z ∈ t
      · rw [indicator_of_mem hs, indicator_of_mem ht, indicator_of_mem (Set.mem_inter hs ht),
          one_mul]
      · rw [indicator_of_notMem ht, indicator_of_notMem fun h => ht (Set.mem_of_mem_inter_right h),
          mul_zero]
    · rw [indicator_of_notMem hs, indicator_of_notMem fun h => hs (Set.mem_of_mem_inter_left h),
        zero_mul]
  simp_rw [sq, Finset.sum_mul_sum, key]
  rw [lintegral_finsetSum _ fun x _ => Finset.measurable_sum _ fun y _ =>
    measurable_const.indicator ((measurableSet_marked x).inter (measurableSet_marked y))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lintegral_finsetSum _ fun y _ =>
    measurable_const.indicator ((measurableSet_marked x).inter (measurableSet_marked y))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [lintegral_indicator_const ((measurableSet_marked x).inter (measurableSet_marked y)),
    one_mul]

/-- The diagonal part: `∑_y μ(x ↔ y, x ↔ marks) = χ₁(x)`. -/
theorem sum_prod_conn_inter_marked_eq (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (x : V) :
    ∑ y, ((law q).prod (prodBernoulli fun _ : V => γ))
        ({z | z.1 ∈ conn x y} ∩ {z | (cluster z.1 x ∩ z.2).Nonempty}) =
      ∫⁻ ω, ((cluster ω x).ncard : ℝ≥0∞) *
        (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω x).ncard) ∂law q := by
  simp_rw [prod_setOf_mem_inter_marked_eq_lintegral q hγ0 hγ1 (measurableSet_conn x _) x]
  have hf : Measurable fun ω : Config V => 1 - ENNReal.ofReal (1 - γ) ^ (cluster ω x).ncard :=
    (measurable_from_nat (f := fun n : ℕ => 1 - ENNReal.ofReal (1 - γ) ^ n)).comp
      (measurable_ncard_cluster x)
  rw [← lintegral_finsetSum _ fun y _ => hf.indicator (measurableSet_conn x y)]
  refine lintegral_congr fun ω => ?_
  rw [ncard_cluster_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : ω ∈ conn x y <;> simp [h]

/-- **Off-diagonal decoupling.** If `x` and `y` are not connected, the events that their
clusters meet the marks occur disjointly; by the BK inequality on the joint configuration,
`μ(x ↔ marks, y ↔ marks, x ↮ y) ≤ M(x) M(y)`. -/
theorem prod_marked_inter_marked_diff_conn_le (γ : unitInterval) (x y : V) :
    ((law q).prod (prodBernoulli fun _ : V => γ))
        (({z | (cluster z.1 x ∩ z.2).Nonempty} ∩
          {z | (cluster z.1 y ∩ z.2).Nonempty}) \ {z | z.1 ∈ conn x y}) ≤
      ((law q).prod (prodBernoulli fun _ : V => γ)) {z | (cluster z.1 x ∩ z.2).Nonempty} *
        ((law q).prod (prodBernoulli fun _ : V => γ))
          {z | (cluster z.1 y ∩ z.2).Nonempty} := by
  set split : Set (Sym2 V ⊕ V) → Config V × Set V :=
    fun ξ => ((Sum.inl ⁻¹' ξ : Set (Sym2 V)), (Sum.inr ⁻¹' ξ : Set V))
  have hms : Measurable split := measurable_preimage_inl.prodMk measurable_preimage_inr
  have hμ : (law q).prod (prodBernoulli fun _ : V => γ) =
      (prodBernoulli (Sum.elim q fun _ : V => γ)).map split :=
    (prodBernoulli_sum_map_prod q fun _ : V => γ).symm
  have hup : ∀ w : V, IsUpperSet (split ⁻¹' {z | (cluster z.1 w ∩ z.2).Nonempty}) := by
    rintro w ξ ξ' hle ⟨a, ha1, ha2⟩
    exact ⟨a, cluster_mono (preimage_mono hle) w ha1, preimage_mono hle ha2⟩
  have hC : MeasurableSet {z : Config V × Set V | z.1 ∈ conn x y} :=
    measurable_fst (measurableSet_conn x y)
  rw [hμ, Measure.map_apply hms (((measurableSet_marked x).inter
      (measurableSet_marked y)).diff hC),
    Measure.map_apply hms (measurableSet_marked x), Measure.map_apply hms (measurableSet_marked y)]
  refine le_trans (measure_mono ?_) (countable_profile_bk _ (hup x) (hup y))
  rintro ξ ⟨⟨⟨a, ha, haη⟩, ⟨b, hb, hbη⟩⟩, hxy⟩
  set ω : Config V := Sum.inl ⁻¹' ξ
  have hdis : ∀ v, v ∈ cluster ω x → v ∈ cluster ω y → False :=
    fun v hvx hvy => hxy (conn_trans hvx (SimpleGraph.Reachable.symm hvy))
  have hforce : ∀ (w c : V), c ∈ cluster ω w → c ∈ (Sum.inr ⁻¹' ξ : Set V) →
      ForcesOn (split ⁻¹' {z | (cluster z.1 w ∩ z.2).Nonempty}) ξ
        (Sum.inl '' (ω ∩ (cluster ω w).sym2) ∪ {Sum.inr c}) := by
    intro w c hc hcη ξ' hagree
    have hsub : ω ∩ (cluster ω w).sym2 ⊆ (Sum.inl ⁻¹' ξ' : Set (Sym2 V)) :=
      fun e he => (hagree (Sum.inl e) (Or.inl ⟨e, he, rfl⟩)).2 he.1
    refine ⟨c, cluster_mono hsub w ?_, (hagree (Sum.inr c) (Or.inr rfl)).2 hcη⟩
    rw [cluster_inter_sym2_cluster]
    exact hc
  refine ⟨_, _, Set.toFinite _, Set.toFinite _, ?_, hforce x a ha haη, hforce y b hb hbη⟩
  rw [Set.disjoint_left]
  intro i hi hi'
  rcases hi with ⟨e, ⟨-, he⟩, rfl⟩ | hi <;> rcases hi' with ⟨e', ⟨-, he'⟩, h⟩ | hi'
  · have hee : e' = e := Sum.inl_injective h
    rw [hee] at he'
    exact hdis _ (Set.mem_sym2_iff_subset.1 he (Sym2.out_fst_mem e))
      (Set.mem_sym2_iff_subset.1 he' (Sym2.out_fst_mem e))
  · exact Sum.inl_ne_inr (Set.mem_singleton_iff.1 hi')
  · rw [Set.mem_singleton_iff.1 hi] at h
    exact Sum.inl_ne_inr h
  · rw [Set.mem_singleton_iff.1 hi, Set.mem_singleton_iff, Sum.inr.injEq] at hi'
    exact hdis a ha (hi' ▸ hb)

/-- **Lower bound for `Q`.** `∑_x χ₁(x) ≤ Q`. -/
theorem sum_lintegral_ncard_mul_one_sub_pow_le_lintegral_sq (hγ0 : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) :
    ∑ x, ∫⁻ ω, ((cluster ω x).ncard : ℝ≥0∞) *
        (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω x).ncard) ∂law q ≤
      ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
        (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) := by
  rw [lintegral_sq_sum_indicator_marked_eq]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← sum_prod_conn_inter_marked_eq q hγ0 hγ1 x]
  refine Finset.sum_le_sum fun y _ => measure_mono ?_
  rintro z ⟨hz, hm⟩
  refine ⟨hm, ?_⟩
  change (cluster z.1 y ∩ z.2).Nonempty
  rw [← cluster_eq_of_mem_conn hz]
  exact hm

/-- **Upper bound for `Q`.** `Q ≤ ∑_{x,y} M(x) M(y) + ∑_x χ₁(x)`. -/
theorem lintegral_sq_le_sum_mul_add_sum (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
        (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) ≤
      ∑ x, ∑ y, ((law q).prod (prodBernoulli fun _ : V => γ))
          {z | (cluster z.1 x ∩ z.2).Nonempty} *
          ((law q).prod (prodBernoulli fun _ : V => γ)) {z | (cluster z.1 y ∩ z.2).Nonempty} +
        ∑ x, ∫⁻ ω, ((cluster ω x).ncard : ℝ≥0∞) *
          (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω x).ncard) ∂law q := by
  set μ := (law q).prod (prodBernoulli fun _ : V => γ)
  rw [lintegral_sq_sum_indicator_marked_eq]
  simp_rw [← sum_prod_conn_inter_marked_eq q hγ0 hγ1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  have hC : MeasurableSet {z : Config V × Set V | z.1 ∈ conn x y} :=
    measurable_fst (measurableSet_conn x y)
  rw [← measure_inter_add_sdiff _ hC, add_comm]
  refine add_le_add (prod_marked_inter_marked_diff_conn_le q γ x y) (measure_mono ?_)
  intro z hz
  exact Set.mem_inter hz.2 hz.1.1

/-! ### Transitive laws -/

/-- Under a transitive law, `E S² ≤ χ³`: sum the tree-graph inequality over its two
terminal vertices. -/
theorem lintegral_ncard_sq_le_chi_pow_three
    (hT : ∀ x y : V, ∃ e : V ≃ V, e x = y ∧ (law q).map (fun ω => Sym2.map e '' ω) = law q)
    (o : V) :
    ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) ^ 2 ∂law q ≤ chi q o ^ 3 := by
  have h1 : ∀ ω, ((cluster ω o).ncard : ℝ≥0∞) =
      (((cluster ω o ∩ ((Finset.univ : Finset V) : Set V)).encard : ℕ∞) : ℝ≥0∞) := by
    intro ω
    rw [Finset.coe_univ, Set.inter_univ, ← ENat.toENNReal_coe,
      Set.Finite.cast_ncard_eq (Set.toFinite _)]
  simp_rw [h1]
  rw [lintegral_cluster_inter_sq (law q) o Finset.univ]
  have hrow : ∀ z, ∑ x, tau q z x = chi q o := by
    intro z
    obtain ⟨e, he, h⟩ := hT o z
    have := chi_apply_eq_of_map_law_eq e h o
    rw [he, chi_eq_tsum_tau, tsum_fintype] at this
    exact this
  calc ∑ x, ∑ y, law q (conn o x ∩ conn o y)
      ≤ ∑ x, ∑ y, ∑ z, tau q o z * tau q z x * tau q z y := by
        gcongr with x _ y _
        exact (treeGraphInequality V q o x y).trans_eq (tsum_fintype _)
    _ = ∑ x, ∑ z, ∑ y, tau q o z * tau q z x * tau q z y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, tau q o z * tau q z x * tau q z y := Finset.sum_comm
    _ = ∑ z, tau q o z * (∑ x, tau q z x) * (∑ y, tau q z y) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        simp only [Finset.mul_sum, mul_assoc]
    _ = chi q o ^ 3 := by
        simp_rw [hrow]
        have hc : ∑ z, tau q o z = chi q o := by rw [chi_eq_tsum_tau, tsum_fintype]
        rw [← Finset.sum_mul, ← Finset.sum_mul, hc]
        ring

variable (hT : ∀ x y : V, ∃ e : V ≃ V, e x = y ∧ (law q).map (fun ω => Sym2.map e '' ω) = law q)
include hT

omit [Fintype V] in
/-- Under a transitive law, every vertex has the same integral of a function of its cluster
size. -/
theorem lintegral_ncard_cluster_eq_of_transitive (F : ℕ → ℝ≥0∞) (x o : V) :
    ∫⁻ ω, F (cluster ω x).ncard ∂law q = ∫⁻ ω, F (cluster ω o).ncard ∂law q := by
  obtain ⟨e, he, h⟩ := hT o x
  rw [← he, lintegral_ncard_cluster_eq_of_map_law_eq q e h]

/-- **`N χ₁ ≤ Q`** under a transitive law. -/
theorem card_mul_lintegral_ncard_mul_one_sub_pow_le_lintegral_sq (hγ0 : 0 < (γ : ℝ))
    (hγ1 : (γ : ℝ) < 1) (o : V) :
    (Fintype.card V : ℝ≥0∞) * ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
        (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q ≤
      ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
        (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) := by
  refine le_trans (le_of_eq ?_) (sum_lintegral_ncard_mul_one_sub_pow_le_lintegral_sq q hγ0 hγ1)
  rw [Finset.sum_congr rfl fun x _ => lintegral_ncard_cluster_eq_of_transitive q hT
    (fun n => (n : ℝ≥0∞) * (1 - ENNReal.ofReal (1 - γ) ^ n)) x o]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`Q ≤ N² M² + N χ₁`** under a transitive law. -/
theorem lintegral_sq_le_card_sq_mul_add_card_mul (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (o : V) :
    ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
        (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) ≤
      (Fintype.card V : ℝ≥0∞) ^ 2 * ((law q).prod (prodBernoulli fun _ : V => γ))
          {z | (cluster z.1 o ∩ z.2).Nonempty} ^ 2 +
        (Fintype.card V : ℝ≥0∞) * ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
          (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q := by
  refine (lintegral_sq_le_sum_mul_add_sum q hγ0 hγ1).trans (le_of_eq ?_)
  have hM : ∀ x, ((law q).prod (prodBernoulli fun _ : V => γ))
      {z | (cluster z.1 x ∩ z.2).Nonempty} =
      ((law q).prod (prodBernoulli fun _ : V => γ)) {z | (cluster z.1 o ∩ z.2).Nonempty} := by
    intro x
    rw [prod_marked_eq_lintegral q hγ0 hγ1, prod_marked_eq_lintegral q hγ0 hγ1]
    exact lintegral_ncard_cluster_eq_of_transitive q hT
      (fun n => 1 - ENNReal.ofReal (1 - γ) ^ n) x o
  simp_rw [hM]
  rw [Finset.sum_congr rfl fun x _ => lintegral_ncard_cluster_eq_of_transitive q hT
    (fun n => (n : ℝ≥0∞) * (1 - ENNReal.ofReal (1 - γ) ^ n)) x o]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **`χ₁ ≤ γ χ³`** under a transitive law. -/
theorem lintegral_ncard_mul_one_sub_pow_le (o : V) :
    ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
        (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q ≤
      ENNReal.ofReal γ * chi q o ^ 3 := by
  calc ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
        (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q
      ≤ ∫⁻ ω, ENNReal.ofReal γ * ((cluster ω o).ncard : ℝ≥0∞) ^ 2 ∂law q := by
        refine lintegral_mono fun ω => ?_
        calc ((cluster ω o).ncard : ℝ≥0∞) * (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard)
            ≤ ((cluster ω o).ncard : ℝ≥0∞) * (ENNReal.ofReal γ * (cluster ω o).ncard) := by
              gcongr
              exact one_sub_ofReal_one_sub_pow_le γ _
          _ = _ := by ring
    _ = ENNReal.ofReal γ * ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) ^ 2 ∂law q :=
        lintegral_const_mul _ (((measurable_from_nat (f := fun n : ℕ => (n : ℝ≥0∞))).comp
          (measurable_ncard_cluster o)).pow_const 2)
    _ ≤ ENNReal.ofReal γ * chi q o ^ 3 := by
        gcongr
        exact lintegral_ncard_sq_le_chi_pow_three q hT o

omit hT

/-- **`χ₀ ≤ (r/γ) M`**, for any profile. -/
theorem lintegral_ncard_mul_pow_le (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (o : V) :
    ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) * ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard
        ∂law q ≤
      ENNReal.ofReal (1 - γ) / ENNReal.ofReal γ *
        ((law q).prod (prodBernoulli fun _ : V => γ)) {z | (cluster z.1 o ∩ z.2).Nonempty} := by
  have hg0 : ENNReal.ofReal γ ≠ 0 := (ENNReal.ofReal_pos.2 hγ0).ne'
  rw [prod_marked_eq_lintegral q hγ0 hγ1, ← lintegral_const_mul' _ _ (by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top hg0)]
  refine lintegral_mono fun ω => le_div_mul_of_mul_le hg0 ENNReal.ofReal_ne_top ?_
  rw [← mul_assoc]
  exact ofReal_mul_mul_ofReal_one_sub_pow_le γ _

omit [Fintype V] in
/-- **`B ≤ (r/γ) χ₁`**, for any profile. -/
theorem lintegral_ncard_sq_mul_pow_le (hγ0 : 0 < (γ : ℝ)) (o : V) :
    ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard
        ∂law q ≤
      ENNReal.ofReal (1 - γ) / ENNReal.ofReal γ *
        ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
          (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q := by
  have hg0 : ENNReal.ofReal γ ≠ 0 := (ENNReal.ofReal_pos.2 hγ0).ne'
  rw [← lintegral_const_mul' _ _ (ENNReal.div_ne_top ENNReal.ofReal_ne_top hg0)]
  refine lintegral_mono fun ω => le_div_mul_of_mul_le hg0 ENNReal.ofReal_ne_top ?_
  have h : ((cluster ω o).ncard : ℝ≥0∞) * (ENNReal.ofReal γ * (cluster ω o).ncard *
      ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ≤ ((cluster ω o).ncard : ℝ≥0∞) *
      (ENNReal.ofReal (1 - γ) * (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard)) := by
    exact mul_le_mul_of_nonneg_left (ofReal_mul_mul_ofReal_one_sub_pow_le γ _)
      (by positivity)
  calc ENNReal.ofReal γ * (((cluster ω o).ncard : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard)
      = ((cluster ω o).ncard : ℝ≥0∞) * (ENNReal.ofReal γ * (cluster ω o).ncard *
          ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) := by ring
    _ ≤ _ := h
    _ = _ := by ring

end PercLib.Percolation.Bond
