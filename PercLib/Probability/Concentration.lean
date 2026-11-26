/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. An application of mathlib's Hoeffding inequality; no upstream proof is copied.
-/
module

public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.Cylinder
public import PercLib.Probability.ProductExpectation
public import PercLib.Probability.FiniteEnergy.Insertion
public import PercLib.Percolation.Bond.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Concentration of the number of open coordinates

For a finite set `F` of coordinates, the number `N_F(ω) = |ω ∩ F|` of open coordinates is a sum
of independent Bernoulli variables. Its mean is `μ_F = ∑_{i ∈ F} p_i`, and Hoeffding's
inequality gives `P(N_F - μ_F ≥ t) ≤ exp(-2t²/|F|)` and the same for the lower tail. No
countability is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {ι : Type*}

open Classical in
/-- The number of open coordinates in `F` is the sum of their indicators. -/
theorem ncard_inter_finset_eq_sum_ite (ω : Set ι) (F : Finset ι) :
    ((ω ∩ (F : Set ι)).ncard : ℝ) = ∑ i ∈ F, if i ∈ ω then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  have : ω ∩ (F : Set ι) = ((F.filter (· ∈ ω) : Finset ι) : Set ι) := by
    ext i
    simp [and_comm]
  rw [this, Set.ncard_coe_finset]

open Classical in
theorem measurable_indicator_mem (i : ι) :
    Measurable fun ω : Set ι => if i ∈ ω then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_mem i) measurable_const measurable_const

open Classical in
theorem integral_indicator_mem (p : ι → unitInterval) (i : ι) :
    ∫ ω, (if i ∈ ω then (1 : ℝ) else 0) ∂prodBernoulli p = (p i : ℝ) := by
  have : (fun ω : Set ι => if i ∈ ω then (1 : ℝ) else 0) =
      {ω : Set ι | i ∈ ω}.indicator 1 := by
    funext ω
    simp [Set.indicator_apply]
  rw [this, integral_indicator_one (measurableSet_mem i), measureReal_def,
    prodBernoulli_setOf_mem, ENNReal.coe_toReal]
  rfl

open Classical in
/-- **Mean.** The expected number of open coordinates in `F` is `∑_{i ∈ F} p_i`. -/
theorem integral_ncard_inter_finset (p : ι → unitInterval) (F : Finset ι) :
    ∫ ω, ((ω ∩ (F : Set ι)).ncard : ℝ) ∂prodBernoulli p = ∑ i ∈ F, (p i : ℝ) := by
  simp_rw [ncard_inter_finset_eq_sum_ite]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => integral_indicator_mem p i
  · intro i _
    refine Integrable.of_mem_Icc 0 1 (measurable_indicator_mem i).aemeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    split_ifs <;> simp

open Classical in
/-- The centred indicators are independent and `1/4`-sub-Gaussian. -/
theorem iIndepFun_centred_indicator (p : ι → unitInterval) :
    iIndepFun (fun i (ω : Set ι) => (if i ∈ ω then (1 : ℝ) else 0) - (p i : ℝ))
      (prodBernoulli p) :=
  (prodBernoulli_iIndepFun_mem p).comp (fun i (b : Prop) => (if b then (1 : ℝ) else 0) - p i)
    fun _ => Measurable.of_discrete

open Classical in
theorem hasSubgaussianMGF_centred_indicator (p : ι → unitInterval) (i : ι) :
    HasSubgaussianMGF (fun ω : Set ι => (if i ∈ ω then (1 : ℝ) else 0) - (p i : ℝ))
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (prodBernoulli p) := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := prodBernoulli p) (a := 0) (b := 1)
    (measurable_indicator_mem i).aemeasurable
    (Filter.Eventually.of_forall fun ω => by split_ifs <;> simp)
  rwa [integral_indicator_mem] at h

theorem sum_subgaussian_const (F : Finset ι) :
    2 * ((∑ _i ∈ F, ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ) = F.card / 2 := by
  rw [NNReal.coe_sum]
  simp only [sub_zero, nnnorm_one, Finset.sum_const, nsmul_eq_mul, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  ring

/-- **Hoeffding, upper tail.** -/
theorem prodBernoulli_real_sum_sub_ge_le (p : ι → unitInterval) (F : Finset ι)
    {t : ℝ} (ht : 0 ≤ t) :
    (prodBernoulli p).real {ω | t ≤ ((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / F.card) := by
  classical
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (iIndepFun_centred_indicator p)
      (s := F)
    (fun i _ => hasSubgaussianMGF_centred_indicator p i) ht
  rw [sum_subgaussian_const] at h
  have hset : {ω : Set ι | t ≤ ((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ)} =
      {ω | t ≤ ∑ i ∈ F, ((if i ∈ ω then (1 : ℝ) else 0) - (p i : ℝ))} := by
    ext ω
    simp only [mem_ofPred_eq, ncard_inter_finset_eq_sum_ite, Finset.sum_sub_distrib]
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  rcases Nat.eq_zero_or_pos F.card with h0 | hpos
  · simp [h0]
  · field_simp

/-- **Hoeffding, lower tail.** -/
theorem prodBernoulli_real_sub_sum_ge_le (p : ι → unitInterval) (F : Finset ι)
    {t : ℝ} (ht : 0 ≤ t) :
    (prodBernoulli p).real {ω | t ≤ ∑ i ∈ F, (p i : ℝ) - ((ω ∩ (F : Set ι)).ncard : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / F.card) := by
  classical
  have hind : iIndepFun (fun i (ω : Set ι) => -((if i ∈ ω then (1 : ℝ) else 0) - (p i : ℝ)))
      (prodBernoulli p) :=
    (iIndepFun_centred_indicator p).comp (fun _ x => -x) fun _ => measurable_neg
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := F)
    (fun i _ => (hasSubgaussianMGF_centred_indicator p i).neg) ht
  rw [sum_subgaussian_const] at h
  have hset : {ω : Set ι | t ≤ ∑ i ∈ F, (p i : ℝ) - ((ω ∩ (F : Set ι)).ncard : ℝ)} =
      {ω | t ≤ ∑ i ∈ F, -((if i ∈ ω then (1 : ℝ) else 0) - (p i : ℝ))} := by
    ext ω
    simp only [mem_ofPred_eq, ncard_inter_finset_eq_sum_ite,
      Finset.sum_sub_distrib, neg_sub]
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  rcases Nat.eq_zero_or_pos F.card with h0 | hpos
  · simp [h0]
  · field_simp

/-! ### The homogeneous case: the binomial law -/

/-- The number of open coordinates in `F` is the cardinality of the restricted configuration. -/
theorem ncard_preimage_val_eq (ω : Set ι) (F : Finset ι) :
    (Subtype.val ⁻¹' ω : Set F).ncard = (ω ∩ (F : Set ι)).ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext i
  simp [and_comm]

/-- **Homogeneous case.** If every coordinate of `F` is open with probability `r`, the number
of open coordinates in `F` is binomial with parameters `|F|` and `r`. -/
theorem prodBernoulli_real_ncard_inter_finset_eq (p : ι → unitInterval) (F : Finset ι)
    {r : unitInterval} (hp : ∀ i ∈ F, p i = r) (k : ℕ) :
    (prodBernoulli p).real {ω | (ω ∩ (F : Set ι)).ncard = k} =
      (F.card.choose k) * (r : ℝ) ^ k * (1 - (r : ℝ)) ^ (F.card - k) := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set F)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  have hlaw : (prodBernoulli p).map (fun ω => (Subtype.val ⁻¹' ω : Set F)) =
      setBernoulli (Set.univ : Set F) r := by
    rw [prodBernoulli_map_restrict, ← prodBernoulli_const]
    congr 1
    funext i
    exact hp i i.2
  have hset : {ω : Set ι | (ω ∩ (F : Set ι)).ncard = k} =
      (fun ω => (Subtype.val ⁻¹' ω : Set F)) ⁻¹' (Set.ncard ⁻¹' {k}) := by
    ext ω
    simp [ncard_preimage_val_eq]
  rw [hset, ← map_measureReal_apply hm (MeasurableSet.of_discrete), hlaw,
    ← map_measureReal_apply (by fun_prop) (measurableSet_singleton k),
    map_ncard_setBernoulli_real_singleton Set.finite_univ]
  simp [Set.ncard_univ, Nat.card_eq_fintype_card]

/-! ### The inhomogeneous law of the count -/

/-- **Inhomogeneous law.** The number of open coordinates in `F` equals `k` with probability
the sum, over the `k`-subsets `a` of `F`, of the probability that exactly the coordinates of `a`
are open. -/
theorem prodBernoulli_real_ncard_inter_finset_eq_sum [DecidableEq ι] (p : ι → unitInterval)
    (F : Finset ι) (k : ℕ) :
    (prodBernoulli p).real {ω | (ω ∩ (F : Set ι)).ncard = k} =
      ∑ a ∈ F.powersetCard k, (∏ i ∈ a, (p i : ℝ)) * ∏ i ∈ F \ a, (1 - (p i : ℝ)) := by
  classical
  have hset : {ω : Set ι | (ω ∩ (F : Set ι)).ncard = k} =
      ⋃ a ∈ F.powersetCard k, {ω | ω ∩ (F : Set ι) = (a : Set ι)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_powersetCard, exists_prop]
    constructor
    · intro h
      refine ⟨F.filter (· ∈ ω), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · rw [← h, ← Set.ncard_coe_finset]
        congr 1
        ext i; simp [and_comm]
      · ext i; simp [and_comm]
    · rintro ⟨a, ⟨_, hk⟩, h⟩
      rw [h, Set.ncard_coe_finset, hk]
  rw [hset, measureReal_biUnion_finset]
  · exact Finset.sum_congr rfl fun a ha =>
      prodBernoulli_real_inter_finset_eq p F a (Finset.mem_powersetCard.1 ha).1
  · intro a _ b _ hab
    refine Set.disjoint_left.2 fun ω h1 h2 => hab ?_
    exact_mod_cast (h1.symm.trans h2 : (a : Set ι) = b)
  · exact fun a _ => measurableSet_setOf_inter_eq F a

/-- More than `|F|` coordinates of `F` are never open. -/
theorem prodBernoulli_real_ncard_inter_finset_eq_zero_of_card_lt (p : ι → unitInterval)
    (F : Finset ι) {k : ℕ} (hk : F.card < k) :
    (prodBernoulli p).real {ω | (ω ∩ (F : Set ι)).ncard = k} = 0 := by
  classical
  rw [prodBernoulli_real_ncard_inter_finset_eq_sum, Finset.powersetCard_eq_empty.2 hk,
    Finset.sum_empty]

/-! ### Exponential moments and the two-sided bound -/

/-- The centred count of open coordinates in `F` is `|F|/4`-sub-Gaussian. -/
theorem hasSubgaussianMGF_ncard_inter_finset_sub_sum (p : ι → unitInterval) (F : Finset ι) :
    HasSubgaussianMGF (fun ω : Set ι => ((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ))
      (F.card / 4) (prodBernoulli p) := by
  classical
  have hc : (∑ _i ∈ F, (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = F.card / 4 := by
    simp only [sub_zero, nnnorm_one, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← hc]
  refine (HasSubgaussianMGF.sum_of_iIndepFun (iIndepFun_centred_indicator p) (s := F)
    fun i _ => hasSubgaussianMGF_centred_indicator p i).congr (ae_of_all _ fun ω => ?_)
  simp only [ncard_inter_finset_eq_sum_ite, Finset.sum_sub_distrib]

/-- **Centred exponential moment.** For every real `t`,
`E exp(t (N_F - μ_F)) ≤ exp(|F| t² / 8)`. -/
theorem integral_exp_mul_ncard_inter_finset_sub_sum_le (p : ι → unitInterval) (F : Finset ι)
    (t : ℝ) :
    ∫ ω, Real.exp (t * (((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ))) ∂prodBernoulli p ≤
      Real.exp (F.card * t ^ 2 / 8) := by
  refine ((hasSubgaussianMGF_ncard_inter_finset_sub_sum p F).mgf_le t).trans_eq ?_
  congr 1
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
  ring

/-- **Hoeffding, two-sided.** `P(|N_F - μ_F| ≥ t) ≤ min {1, 2 exp(-2t²/|F|)}` for `t ≥ 0`;
for empty `F` the right side is `1`. -/
theorem prodBernoulli_real_abs_sub_ge_le (p : ι → unitInterval) (F : Finset ι)
    {t : ℝ} (ht : 0 ≤ t) :
    (prodBernoulli p).real
        {ω | t ≤ |((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ)|} ≤
      min 1 (2 * Real.exp (-2 * t ^ 2 / F.card)) := by
  refine le_min measureReal_le_one ?_
  have hsub : {ω : Set ι | t ≤ |((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ)|} ⊆
      {ω | t ≤ ((ω ∩ (F : Set ι)).ncard : ℝ) - ∑ i ∈ F, (p i : ℝ)} ∪
        {ω | t ≤ ∑ i ∈ F, (p i : ℝ) - ((ω ∩ (F : Set ι)).ncard : ℝ)} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl h
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ Real.exp (-2 * t ^ 2 / F.card) + Real.exp (-2 * t ^ 2 / F.card) :=
      add_le_add (prodBernoulli_real_sum_sub_ge_le p F ht)
        (prodBernoulli_real_sub_sum_ge_le p F ht)
    _ = _ := by ring

/-- **Empty set, upper tail.** With no coordinates the centred count is `0`. -/
theorem prodBernoulli_real_sum_sub_ge_empty (p : ι → unitInterval) (t : ℝ) :
    (prodBernoulli p).real
        {ω | t ≤ ((ω ∩ ((∅ : Finset ι) : Set ι)).ncard : ℝ) - ∑ i ∈ ∅, (p i : ℝ)} =
      if t ≤ 0 then 1 else 0 := by
  split_ifs with h <;> simp [h]

/-- **Empty set, lower tail.** With no coordinates the centred count is `0`. -/
theorem prodBernoulli_real_sub_sum_ge_empty (p : ι → unitInterval) (t : ℝ) :
    (prodBernoulli p).real
        {ω | t ≤ ∑ i ∈ ∅, (p i : ℝ) - ((ω ∩ ((∅ : Finset ι) : Set ι)).ncard : ℝ)} =
      if t ≤ 0 then 1 else 0 := by
  split_ifs with h <;> simp [h]

/-! ### Non-vacuity -/

/-- Two fair coordinates: exactly one is open with probability `2 · (1/2) · (1/2)`. -/
example : (prodBernoulli (fun _ : Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))).real
    {ω | (ω ∩ ((Finset.univ : Finset Bool) : Set Bool)).ncard = 1} =
      ((Finset.univ : Finset Bool).card.choose 1) * (1 / 2 : ℝ) ^ 1 *
        (1 - 1 / 2 : ℝ) ^ ((Finset.univ : Finset Bool).card - 1) :=
  prodBernoulli_real_ncard_inter_finset_eq _ _ (fun _ _ => rfl) 1

/-- The upper tail bound at `t = 0` on an infinite index type. -/
example (p : ℕ → unitInterval) :
    (prodBernoulli p).real {ω | 0 ≤ ((ω ∩ ((Finset.range 3 : Finset ℕ) : Set ℕ)).ncard : ℝ) -
      ∑ i ∈ Finset.range 3, (p i : ℝ)} ≤ Real.exp (-2 * 0 ^ 2 / (Finset.range 3).card) :=
  prodBernoulli_real_sum_sub_ge_le p _ le_rfl

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- **Bond corollary, mean.** -/
theorem integral_ncard_inter_finset_law (q : Sym2 V → unitInterval) (F : Finset (Sym2 V)) :
    ∫ ω, ((ω ∩ (F : Set (Sym2 V))).ncard : ℝ) ∂law q = ∑ e ∈ F, (q e : ℝ) :=
  integral_ncard_inter_finset q F

/-- **Bond corollary, upper tail.** -/
theorem law_real_sum_sub_ge_le (q : Sym2 V → unitInterval) (F : Finset (Sym2 V))
    {t : ℝ} (ht : 0 ≤ t) :
    (law q).real {ω | t ≤ ((ω ∩ (F : Set (Sym2 V))).ncard : ℝ) - ∑ e ∈ F, (q e : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / F.card) :=
  prodBernoulli_real_sum_sub_ge_le q F ht

/-- **Bond corollary, lower tail.** -/
theorem law_real_sub_sum_ge_le (q : Sym2 V → unitInterval) (F : Finset (Sym2 V))
    {t : ℝ} (ht : 0 ≤ t) :
    (law q).real {ω | t ≤ ∑ e ∈ F, (q e : ℝ) - ((ω ∩ (F : Set (Sym2 V))).ncard : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / F.card) :=
  prodBernoulli_real_sub_sum_ge_le q F ht

end PercLib.Percolation.Bond

end
