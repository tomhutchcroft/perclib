/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Probability.HarrisDecreasing
public import PercLib.Probability.Cylinder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Hierarchical block-quantile amplification: scales and the connection step

The amplification step of 7AER (hierarchical-runaway) chooses a block scale `ℓ` and joins the
large clusters of good sub-blocks by direct edges. This file proves the deterministic and
single-edge-family ingredients:

* `exists_amplification_scale`: since `α < d`, there is `ℓ ≥ 1` with `N = L^{dℓ}`,
  `e^{-N/(8e)} ≤ 1/4` and `L^{(d-α)ℓ} ≥ 16 e²`.
* `law_all_closed_le` (**no direct edge**): for the intensity profile `q_β` and a finite set
  `F` of pairs with `J ≥ j₀` on `F`, the probability that every pair of `F` is closed is at
  most `exp(-β j₀ |F|)`.
* `exp_neg_le_inv_two_mul_sq` (**the connection threshold**): with
  `A = (4/c) L^{(d+α)ℓ} log(2N²)`, sets of size `s` with `4 s² ≥ (A/β) L^{(d+α)n}` at
  kernel level `≥ c L^{-(d+α)(n+ℓ)}` fail to be joined with probability at most `1/(2N²)`.
* `amplified_sq_ge` (**the amplification arithmetic**): `K ≥ N/(2e)` good blocks with clusters
  of size `R - 1 ≥ R/2`, `R² ≥ (A/β) L^{(d+α)n}` and `L^{(d-α)ℓ} ≥ 16e²` give
  `(K(R - 1))² ≥ (A/β) L^{(d+α)(n+ℓ)}`.

* `measure_count_le_le`, `exp_neg_two_mul_sq_le` (**many good blocks**): among independent
  events of probability `≥ p`, at most `|s| p - t` occur with probability `≤ exp(-2t²/|s|)`;
  at `p = e^{-1}`, `t = N/(2e)` this is `≤ exp(-N/(8e))`.

The assembly on the hierarchical lattice (independence of the sub-blocks and of the edges
between them, and the quantile bookkeeping of `tightnessScale`) is part 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Models

/-! ### The scale `ℓ` -/

/-- **Choice of the scale.** For `L ≥ 2`, `d ≥ 1` and `0 < α < d` there is `ℓ ≥ 1` with
`e^{-L^{dℓ}/(8e)} ≤ 1/4` and `16 e² ≤ L^{(d-α)ℓ}`. -/
theorem exists_amplification_scale {L d : ℕ} (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) (hαd : α < d) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4 ∧
      16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hL0 : (0 : ℝ) < L := by linarith
  have hdα : 0 < (d : ℝ) - α := by linarith
  -- `L^{(d-α)ℓ} → ∞`
  have h1 : Tendsto (fun ℓ : ℕ => (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) atTop atTop := by
    have : Tendsto (fun ℓ : ℕ => ((L : ℝ) ^ ((d : ℝ) - α)) ^ ℓ) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_rpow hL1 hdα)
    refine this.congr fun ℓ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  -- `L^{dℓ} ≥ ℓ`, so `e^{-L^{dℓ}/(8e)} → 0`
  have h2 : Tendsto (fun ℓ : ℕ => Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1)))) atTop
      (𝓝 0) := by
    have hd : 1 ≤ d := by
      by_contra h
      have : (d : ℝ) = 0 := by exact_mod_cast (show d = 0 by omega)
      rw [this] at hαd
      linarith
    have hpow : Tendsto (fun ℓ : ℕ => (L : ℝ) ^ (d * ℓ)) atTop atTop := by
      have : Tendsto (fun ℓ : ℕ => ((L : ℝ) ^ d) ^ ℓ) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (one_lt_pow₀ hL1 (by omega))
      exact this.congr fun ℓ => by rw [← pow_mul]
    have := (hpow.atTop_div_const (by positivity : (0 : ℝ) < 8 * Real.exp 1))
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp this
  obtain ⟨ℓ, hℓ⟩ := (((h1.eventually_ge_atTop (16 * Real.exp 1 ^ 2)).and
    (h2.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4)))).and
      (eventually_ge_atTop 1)).exists
  exact ⟨ℓ, hℓ.2, hℓ.1.2, hℓ.1.1⟩

/-! ### No direct edge -/

open PercLib.Percolation.Bond in
/-- **No direct edge.** For the intensity profile `q_β = 1 - e^{-βJ}` and a finite set `F` of
pairs with `J ≥ j₀` on `F`, the probability that every pair of `F` is closed is at most
`exp(-β j₀ |F|)`. -/
theorem law_all_closed_le {V : Type*} (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (F : Finset (Sym2 V))
    {j₀ : ℝ} (hJ : ∀ e ∈ F, j₀ ≤ J e) :
    law (intensityProfile J β) {ω | ∀ e ∈ F, e ∉ ω} ≤
      ENNReal.ofReal (Real.exp (-((β : ℝ) * j₀ * F.card))) := by
  -- complement duality and the all-open product
  have hset : {ω : Config V | ∀ e ∈ F, e ∉ ω} = {ω | ωᶜ ∈
      {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'}} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe, Set.mem_compl_iff]
  have hmeas : MeasurableSet {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'} := by
    have : {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'} = ⋂ e ∈ F, {ω' | e ∈ ω'} := by
      ext ω; simp [Set.subset_def]
    rw [this]
    exact Finset.measurableSet_biInter F fun e _ => measurableSet_mem e
  rw [hset, law, PercLib.Probability.prodBernoulli_preimage_compl _ hmeas,
    PercLib.Probability.prodBernoulli_subset]
  -- each factor is `e^{-βJ} ≤ e^{-βj₀}`
  have hfac : ∀ e ∈ F, (unitInterval.toNNReal (unitInterval.symm (intensityProfile J β e)) :
      ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(β : ℝ) * J e)) := by
    intro e _
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    change 1 - (1 - Real.exp (-(β : ℝ) * J e)) = _
    ring
  rw [Finset.prod_congr rfl hfac, ← ENNReal.ofReal_prod_of_nonneg fun e _ => (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  have : ∑ e ∈ F, -(β : ℝ) * (J e : ℝ) ≤ ∑ _e ∈ F, -(β : ℝ) * j₀ :=
    Finset.sum_le_sum fun e he => by
      have := mul_le_mul_of_nonneg_left (hJ e he) (NNReal.coe_nonneg β)
      linarith
  rw [Finset.sum_const, nsmul_eq_mul] at this
  linarith

/-! ### The connection threshold -/

/-- **Connection threshold.** Let `c, β > 0`, `L ≥ 1`, `N ≥ 1` and
`A = (4/c) L^{(d+α)ℓ} log(2N²)`. If `4 s² ≥ (A/β) L^{(d+α)n}`, then
`exp(-β · c L^{-(d+α)(n+ℓ)} · s²) ≤ 1/(2N²)`. -/
theorem exp_neg_le_inv_two_mul_sq {c β L s a : ℝ} (hc : 0 < c) (hβ : 0 < β) (hL : 0 < L)
    {N : ℝ} (hN : 1 ≤ N) {n ℓ : ℕ}
    (hs : (4 / c) * L ^ (a * ℓ) * Real.log (2 * N ^ 2) / β * L ^ (a * n) ≤ 4 * s ^ 2) :
    Real.exp (-(β * (c * L ^ (-(a * (n + ℓ)))) * s ^ 2)) ≤ 1 / (2 * N ^ 2) := by
  have hN2 : 0 < 2 * N ^ 2 := by positivity
  rw [one_div, ← Real.exp_log hN2, ← Real.exp_neg, Real.exp_le_exp, neg_le_neg_iff]
  -- `L^{a n} L^{a ℓ} L^{-a(n+ℓ)} = 1`
  have hLL : L ^ (a * ℓ) * L ^ (a * n) * L ^ (-(a * (n + ℓ))) = 1 := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    ring_nf
    exact Real.rpow_zero L
  have hpos : 0 < L ^ (-(a * (n + ℓ))) := Real.rpow_pos_of_pos hL _
  have key : Real.log (2 * N ^ 2) =
      ((4 / c) * L ^ (a * ℓ) * Real.log (2 * N ^ 2) / β * L ^ (a * n)) *
        (β * (c * L ^ (-(a * (n + ℓ))))) / 4 := by
    rw [show ((4 / c) * L ^ (a * ℓ) * Real.log (2 * N ^ 2) / β * L ^ (a * n)) *
        (β * (c * L ^ (-(a * (n + ℓ))))) / 4 = Real.log (2 * N ^ 2) *
          (L ^ (a * ℓ) * L ^ (a * n) * L ^ (-(a * (n + ℓ)))) by field_simp, hLL, mul_one]
  rw [key]
  have hm : 0 ≤ β * (c * L ^ (-(a * (n + ℓ)))) := by positivity
  calc ((4 / c) * L ^ (a * ℓ) * Real.log (2 * N ^ 2) / β * L ^ (a * n)) *
        (β * (c * L ^ (-(a * (n + ℓ))))) / 4
      ≤ (4 * s ^ 2) * (β * (c * L ^ (-(a * (n + ℓ))))) / 4 := by
        gcongr
    _ = β * (c * L ^ (-(a * (n + ℓ)))) * s ^ 2 := by ring

/-! ### The amplification arithmetic -/

/-- **Amplification arithmetic.** If `L^{(d-α)ℓ} ≥ 16e²`, `N = L^{dℓ}`, `K ≥ N/(2e)`,
`R ≥ 2` and `R² ≥ B L^{(d+α)n}`, then `(K(R - 1))² ≥ B L^{(d+α)(n+ℓ)}`. -/
theorem amplified_sq_ge {L d α B R K : ℝ} (hL : 0 < L) {n ℓ : ℕ}
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ L ^ ((d - α) * ℓ))
    (hK : L ^ (d * ℓ) / (2 * Real.exp 1) ≤ K) (hR : 2 ≤ R)
    (hRn : B * L ^ ((d + α) * n) ≤ R ^ 2) :
    B * L ^ ((d + α) * (n + ℓ)) ≤ (K * (R - 1)) ^ 2 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hN0 : 0 < L ^ (d * ℓ) := Real.rpow_pos_of_pos hL _
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  -- `(N/(2e))² = L^{(d+α)ℓ} L^{(d-α)ℓ} / (4e²) ≥ 4 L^{(d+α)ℓ}`
  have hsplit : (L ^ (d * ℓ)) ^ 2 = L ^ ((d + α) * ℓ) * L ^ ((d - α) * ℓ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    ring_nf
  have hK2 : 4 * L ^ ((d + α) * ℓ) ≤ K ^ 2 := by
    have h1 : (L ^ (d * ℓ) / (2 * Real.exp 1)) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) hK 2
    rw [div_pow, hsplit] at h1
    have hpos : 0 < L ^ ((d + α) * ℓ) := Real.rpow_pos_of_pos hL _
    calc 4 * L ^ ((d + α) * ℓ) = L ^ ((d + α) * ℓ) * (16 * Real.exp 1 ^ 2) /
        (2 * Real.exp 1) ^ 2 := by
          field_simp; ring
      _ ≤ L ^ ((d + α) * ℓ) * L ^ ((d - α) * ℓ) / (2 * Real.exp 1) ^ 2 := by
          gcongr
      _ ≤ K ^ 2 := h1
  have hR1 : R ^ 2 ≤ 4 * (R - 1) ^ 2 := by nlinarith
  have hsum : L ^ ((d + α) * (n + ℓ)) = L ^ ((d + α) * n) * L ^ ((d + α) * ℓ) := by
    rw [← Real.rpow_add hL]; ring_nf
  rw [hsum, mul_pow]
  have h0 : 0 ≤ L ^ ((d + α) * ℓ) := (Real.rpow_pos_of_pos hL _).le
  calc B * (L ^ ((d + α) * n) * L ^ ((d + α) * ℓ))
      = (B * L ^ ((d + α) * n)) * L ^ ((d + α) * ℓ) := by ring
    _ ≤ R ^ 2 * L ^ ((d + α) * ℓ) := mul_le_mul_of_nonneg_right hRn h0
    _ ≤ (4 * (R - 1) ^ 2) * L ^ ((d + α) * ℓ) := mul_le_mul_of_nonneg_right hR1 h0
    _ = (R - 1) ^ 2 * (4 * L ^ ((d + α) * ℓ)) := by ring
    _ ≤ (R - 1) ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_left hK2 (sq_nonneg _)
    _ = K ^ 2 * (R - 1) ^ 2 := by ring

/-! ### Many good blocks -/

open ProbabilityTheory in
/-- **Hoeffding for independent events.** If the events `E i` (`i ∈ s`) are independent and
each has probability at least `p`, then the number of them that occur is at most
`|s| p - t` with probability at most `exp(-2t²/|s|)`. -/
theorem measure_count_le_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : ι → Set Ω} (hE : ∀ i, MeasurableSet (E i))
    (hind : iIndepSet E μ) (s : Finset ι) {p : ℝ} (hp : ∀ i ∈ s, p ≤ μ.real (E i))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) ω ≤ s.card * p - t} ≤
      Real.exp (-2 * t ^ 2 / s.card) := by
  set X : ι → Ω → ℝ := fun i ω => -((E i).indicator (fun _ => (1 : ℝ)) ω - μ.real (E i))
    with hX
  have hindX : iIndepFun X μ :=
    (hind.iIndepFun_indicator (β := ℝ)).comp (fun i x => -(x - μ.real (E i)))
      fun _ => by fun_prop
  have hint : ∀ i, μ[(E i).indicator (fun _ => (1 : ℝ))] = μ.real (E i) := fun i => by
    rw [integral_indicator_const _ (hE i), smul_eq_mul, mul_one]
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := (E i).indicator fun _ => (1 : ℝ))
      (a := 0) (b := 1) ((measurable_const.indicator (hE i)).aemeasurable)
      (Eventually.of_forall fun ω => by
        by_cases h : ω ∈ E i <;> simp [Set.indicator, h])
    rw [hint] at h
    exact h.neg
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindX hsub ht
  have hc : 2 * ((∑ _i ∈ s, ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ) = s.card / 2 := by
    rw [NNReal.coe_sum]
    simp only [sub_zero, nnnorm_one, Finset.sum_const, nsmul_eq_mul, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    ring
  rw [hc] at h
  refine le_trans (measureReal_mono (fun ω hω => ?_)) (h.trans (le_of_eq ?_))
  · simp only [Set.mem_ofPred_eq] at hω ⊢
    simp only [hX, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    have : ∑ i ∈ s, p ≤ ∑ i ∈ s, μ.real (E i) := Finset.sum_le_sum hp
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  · congr 1
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · simp [h0]
    · field_simp

/-- With `p ≥ e^{-1}`, at most `N/(2e)` of `N` independent events occur with probability at
most `exp(-N/(2e²)) ≤ exp(-N/(8e))`. -/
theorem exp_neg_two_mul_sq_le {N : ℝ} (hN : 0 < N) :
    Real.exp (-2 * (N * Real.exp (-1) - N / (2 * Real.exp 1)) ^ 2 / N) ≤
      Real.exp (-(N / (8 * Real.exp 1))) := by
  refine Real.exp_le_exp.2 ?_
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have hval : N * Real.exp (-1) - N / (2 * Real.exp 1) = N / (2 * Real.exp 1) := by
    rw [he1]; field_simp; ring
  rw [hval]
  have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  rw [div_pow, neg_mul, neg_div, neg_le_neg_iff, mul_div_assoc', div_div, le_div_iff₀
    (by positivity)]
  have : N / (8 * Real.exp 1) * ((2 * Real.exp 1) ^ 2 * N) = N ^ 2 * Real.exp 1 / 2 := by
    field_simp; ring
  rw [this]
  nlinarith [sq_nonneg N]

/-! ### Non-vacuity witnesses -/

/-- The example `L = 2`, `d = 3`, `α = 1`: a scale `ℓ` exists. -/
example : ∃ ℓ : ℕ, 1 ≤ ℓ ∧ Real.exp (-(((2 : ℕ) : ℝ) ^ (3 * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4 ∧
    16 * Real.exp 1 ^ 2 ≤ ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 1) * ℓ) :=
  exists_amplification_scale le_rfl one_pos (by norm_num)

/-- The connection threshold at `n = 0`, `ℓ = 1`, `L = 2`, `a = 4`, `c = β = 1`, `N = 1` and a
large `s`. -/
example : Real.exp (-(1 * (1 * (2 : ℝ) ^ (-((4 : ℝ) * ((0 : ℕ) + (1 : ℕ))))) * (10 : ℝ) ^ 2)) ≤
    1 / (2 * (1 : ℝ) ^ 2) := by
  refine exp_neg_le_inv_two_mul_sq one_pos one_pos (by norm_num) le_rfl ?_
  have hlog : Real.log (2 * (1 : ℝ) ^ 2) ≤ 1 := by
    rw [one_pow, mul_one]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have h16 : (2 : ℝ) ^ ((4 : ℝ) * ((1 : ℕ) : ℝ)) = 16 := by norm_num
  have h1 : (2 : ℝ) ^ ((4 : ℝ) * ((0 : ℕ) : ℝ)) = 1 := by norm_num
  rw [h16, h1]
  have hr : 4 / 1 * 16 * Real.log (2 * (1 : ℝ) ^ 2) / 1 * 1 = 64 * Real.log (2 * (1 : ℝ) ^ 2) := by
    ring
  rw [hr]
  linarith

open ProbabilityTheory in
/-- The count bound for one sure event (`Ω = Bool` with a point mass, `p = 1`): the
independence and probability hypotheses hold. -/
example : (Measure.dirac true : Measure Bool).real
    {ω | ∑ _i ∈ ({()} : Finset Unit), ({true} : Set Bool).indicator (fun _ => (1 : ℝ)) ω ≤
      ({()} : Finset Unit).card * 1 - 0} ≤
      Real.exp (-2 * 0 ^ 2 / ({()} : Finset Unit).card) :=
  measure_count_le_le (E := fun _ : Unit => ({true} : Set Bool))
    (fun _ => measurableSet_singleton true)
    (show iIndep _ _ from iIndep.of_subsingleton) {()}
    (fun _ _ => by simp [measureReal_def]) le_rfl

end PercLib.Models
