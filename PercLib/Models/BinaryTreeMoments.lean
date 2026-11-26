/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16 against pinned mathlib. No upstream proof is copied. The
statements follow the wiki tag GGVG (binary-tree percolation), analytic part.
-/
module

public import Mathlib.Analysis.PSeries
public import PercLib.Analysis.AbelianSums
public import PercLib.Models.BinaryTreeAsymptotics

/-!
# Near-critical moments of the binary-tree cluster law (GGVG, analytic part)

Write `aₙ = Cat(n)/4ⁿ`, `λ(p) = -log(4p(1-p))` and

`M_s(p) = ((1-p)/p) ∑_{n ≥ 1} n^s aₙ e^{-λ(p) n}`,

written out in each statement with the index `n + 1`, `n : ℕ`. As `p → 1/2`, `p ≠ 1/2`:

* `lambda_isEquivalent`: `λ(p) ~ 4(p - 1/2)²`;
* `moment_isEquivalent_of_gt` (`s > 1/2`): `M_s(p) ~ Γ(s-1/2) λ(p)^{-(s-1/2)}/√π`;
* `moment_isEquivalent_half` (`s = 1/2`): `M_{1/2}(p) ~ log(1/λ(p))/√π`;
* `moment_tendsto_of_lt` (`0 ≤ s < 1/2`): the series at `p = 1/2` converges and
  `M_s(p) → M_s(1/2)`;
* `moment_ratio_isEquivalent` (`s > 1/2`): `M_{s+1}(p)/M_s(p) ~ (s-1/2)/(4(p-1/2)²)`.

The inputs are `catalan_div_four_pow_isEquivalent` (`PercLib/Models/BinaryTreeAsymptotics.lean`) and
the Abelian theorems of `PercLib/Analysis/AbelianSums.lean`. The identification of `M_s(p)` with
`E_p[|K|^s; |K| < ∞]` is not part of this file. This file adds no definition.
-/

@[expose] public section

noncomputable section

open Filter Topology Asymptotics Real

namespace PercLib.Models

open PercLib.Analysis

/-! ### The intensity `λ(p) = -log(4p(1-p))` -/

/-- Near `1/2` the parameter lies in `(0, 1)`. -/
theorem eventually_mem_Ioo_half : ∀ᶠ p : ℝ in 𝓝[≠] (1 / 2), 0 < p ∧ p < 1 := by
  have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 (1 / 2 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [nhdsWithin_le_nhds this] with p hp using hp

/-- For `p ∈ (0,1)`, `p ≠ 1/2`, `0 < 4p(1-p) < 1`. -/
theorem four_mul_mem_Ioo {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2) :
    0 < 4 * p * (1 - p) ∧ 4 * p * (1 - p) < 1 := by
  refine ⟨mul_pos (mul_pos (by norm_num) hp0) (by linarith), ?_⟩
  have : 0 < (2 * p - 1) ^ 2 := by
    have : 2 * p - 1 ≠ 0 := fun h => hp (by linarith)
    positivity
  nlinarith

/-- `λ(p) → 0⁺` as `p → 1/2`, `p ≠ 1/2`. -/
theorem tendsto_lambda :
    Tendsto (fun p : ℝ => -log (4 * p * (1 - p))) (𝓝[≠] (1 / 2)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun p : ℝ => -log (4 * p * (1 - p))) (1 / 2) :=
      ((continuousAt_log (by norm_num)).comp
        (by fun_prop : ContinuousAt (fun p : ℝ => 4 * p * (1 - p)) (1 / 2))).neg
    convert hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 / 2 : ℝ)}ᶜ)) using 2
    norm_num
  · filter_upwards [eventually_mem_Ioo_half, self_mem_nhdsWithin] with p hp hne
    obtain ⟨h0, h1⟩ := four_mul_mem_Ioo hp.1 hp.2 hne
    exact neg_pos.2 (log_neg h0 h1)

/-- **Intensity.** `λ(p) ~ 4(p - 1/2)²` as `p → 1/2`. -/
theorem lambda_isEquivalent :
    (fun p : ℝ => -log (4 * p * (1 - p))) ~[𝓝[≠] (1 / 2)] fun p => 4 * (p - 1 / 2) ^ 2 := by
  -- the slope of `log` at `1`
  have hd := (hasDerivAt_log (one_ne_zero (α := ℝ))).tendsto_slope_zero
  simp only [log_one, sub_zero, smul_eq_mul, inv_one] at hd
  have hu : Tendsto (fun p : ℝ => -(4 * (p - 1 / 2) ^ 2)) (𝓝[≠] (1 / 2)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun p : ℝ => -(4 * (p - 1 / 2) ^ 2)) (𝓝 (1 / 2)) (𝓝 0) := by
        have := (by fun_prop : Continuous fun p : ℝ => -(4 * (p - 1 / 2) ^ 2)).tendsto (1 / 2)
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      have : p - 1 / 2 ≠ 0 := sub_ne_zero.2 hp
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero]
      positivity
  refine isEquivalent_of_tendsto_one ((hd.comp hu).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hne : (4 * (p - 1 / 2) ^ 2) ≠ 0 := by
    have : p - 1 / 2 ≠ 0 := sub_ne_zero.2 hp
    positivity
  simp only [Function.comp_apply, Pi.div_apply]
  rw [show 1 + -(4 * (p - 1 / 2) ^ 2) = 4 * p * (1 - p) by ring]
  field_simp

/-! ### The series -/

/-- Dropping the zero term: the sum over `n ≥ 1` is the sum over `n ≥ 0` of the sequence
that vanishes at `0`. -/
theorem tsum_succ_eq_tsum_ite (s t : ℝ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s * ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(t * ((n + 1 : ℕ) : ℝ)))) =
      ∑' n : ℕ, (if n = 0 then 0 else (n : ℝ) ^ s * ((catalan n : ℝ) / 4 ^ n)) *
        exp (-(t * n)) := by
  set f : ℕ → ℝ := fun n =>
    (if n = 0 then 0 else (n : ℝ) ^ s * ((catalan n : ℝ) / 4 ^ n)) * exp (-(t * n))
  have hshift : ∀ n : ℕ, f (n + 1) = ((n + 1 : ℕ) : ℝ) ^ s * ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
      exp (-(t * ((n + 1 : ℕ) : ℝ))) := fun n => by simp [f]
  simp_rw [← hshift]
  by_cases hf : Summable f
  · rw [hf.tsum_eq_zero_add]
    simp [f]
  · rw [tsum_eq_zero_of_not_summable hf,
      tsum_eq_zero_of_not_summable (fun h => hf ((summable_nat_add_iff 1).1 h))]

/-- `n^s aₙ ~ π^{-1/2} n^{(s - 1/2) - 1}` (the zero term is irrelevant). -/
theorem moment_coeff_isEquivalent (s : ℝ) :
    (fun n : ℕ => if n = 0 then 0 else (n : ℝ) ^ s * ((catalan n : ℝ) / 4 ^ n)) ~[atTop]
      fun n => 1 / √π * (n : ℝ) ^ (s - 1 / 2 - 1) := by
  have h := (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ) ^ s)).mul
    catalan_div_four_pow_isEquivalent
  refine (h.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    simp [show n ≠ 0 by omega]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.mul_apply]
    rw [show s - 1 / 2 - 1 = s + -(3 / 2 : ℝ) by ring, Real.rpow_add hn0]
    ring

/-- **`s > 1/2`.** `M_s(p) ~ Γ(s-1/2) λ(p)^{-(s-1/2)}/√π` as `p → 1/2`. -/
theorem moment_isEquivalent_of_gt {s : ℝ} (hs : 1 / 2 < s) :
    (fun p : ℝ => (1 - p) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ)))) ~[𝓝[≠] (1 / 2)]
      fun p => Gamma (s - 1 / 2) * (-log (4 * p * (1 - p))) ^ (-(s - 1 / 2)) / √π := by
  have ha : 0 < s - 1 / 2 := by linarith
  have hG : 0 < Gamma (s - 1 / 2) := Gamma_pos_of_pos ha
  have hpi : 0 < √π := Real.sqrt_pos.2 pi_pos
  have hab := tendsto_rpow_mul_tsum_exp_of_isEquivalent ha (by positivity)
    (moment_coeff_isEquivalent s)
  have hcomp := hab.comp tendsto_lambda
  have hpq : Tendsto (fun p : ℝ => (1 - p) / p) (𝓝[≠] (1 / 2)) (𝓝 1) := by
    have : Tendsto (fun p : ℝ => (1 - p) / p) (𝓝 (1 / 2)) (𝓝 ((1 - 1 / 2) / (1 / 2))) :=
      ((continuous_const.sub continuous_id).tendsto _).div (continuous_id.tendsto _)
        (by norm_num)
    exact (this.mono_left nhdsWithin_le_nhds).trans_eq (by norm_num)
  have hlim := (hpq.mul hcomp).mul (tendsto_const_nhds (x := √π / Gamma (s - 1 / 2)))
  have hone : 1 / √π * Gamma (s - 1 / 2) * (√π / Gamma (s - 1 / 2)) = 1 := by
    calc 1 / √π * Gamma (s - 1 / 2) * (√π / Gamma (s - 1 / 2))
        = (Gamma (s - 1 / 2) / Gamma (s - 1 / 2)) * (√π / √π) := by ring
      _ = 1 := by rw [div_self hG.ne', div_self hpi.ne', one_mul]
  rw [one_mul, hone] at hlim
  refine isEquivalent_of_tendsto_one (hlim.congr' ?_)
  filter_upwards [eventually_mem_Ioo_half, self_mem_nhdsWithin] with p hp hne
  obtain ⟨h0, h1⟩ := four_mul_mem_Ioo hp.1 hp.2 hne
  have hl : 0 < -log (4 * p * (1 - p)) := neg_pos.2 (log_neg h0 h1)
  have hla : 0 < (-log (4 * p * (1 - p))) ^ (s - 1 / 2) := Real.rpow_pos_of_pos hl _
  simp only [Function.comp_apply, Pi.div_apply]
  rw [tsum_succ_eq_tsum_ite, Real.rpow_neg hl.le]
  field_simp

/-- **`s = 1/2`.** `M_{1/2}(p) ~ log(1/λ(p))/√π` as `p → 1/2`. -/
theorem moment_isEquivalent_half :
    (fun p : ℝ => (1 - p) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ)))) ~[𝓝[≠] (1 / 2)]
      fun p => log (1 / -log (4 * p * (1 - p))) / √π := by
  have hpi : 0 < √π := Real.sqrt_pos.2 pi_pos
  have hcoeff : (fun n : ℕ => if n = 0 then 0 else (n : ℝ) ^ (1 / 2 : ℝ) *
      ((catalan n : ℝ) / 4 ^ n)) ~[atTop] fun n => 1 / √π / n := by
    refine (moment_coeff_isEquivalent (1 / 2)).congr_right ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show (1 / 2 : ℝ) - 1 / 2 - 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hab := (tsum_exp_isEquivalent_log_of_isEquivalent (by positivity) hcoeff).comp_tendsto
    tendsto_lambda
  have hpq : (fun p : ℝ => (1 - p) / p) ~[𝓝[≠] (1 / 2)] fun _ => (1 : ℝ) := by
    refine isEquivalent_of_tendsto_one ?_
    have : Tendsto (fun p : ℝ => (1 - p) / p) (𝓝 (1 / 2)) (𝓝 ((1 - 1 / 2) / (1 / 2))) :=
      ((continuous_const.sub continuous_id).tendsto _).div (continuous_id.tendsto _)
        (by norm_num)
    have h2 : Tendsto (fun p : ℝ => (1 - p) / p) (𝓝[≠] (1 / 2)) (𝓝 1) := by
      have h3 := this.mono_left (nhdsWithin_le_nhds (s := {(1 / 2 : ℝ)}ᶜ))
      norm_num at h3 ⊢
      exact h3
    exact h2.congr' (Eventually.of_forall fun p => by simp)
  refine ((hpq.mul hab).congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun p => by
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [tsum_succ_eq_tsum_ite]
  · exact Eventually.of_forall fun p => by
      simp only [Pi.mul_apply, Function.comp_apply]
      ring

/-- **`0 ≤ s < 1/2`.** The series at `p = 1/2` converges, and `M_s(p) → M_s(1/2)` as
`p → 1/2`. -/
theorem moment_tendsto_of_lt {s : ℝ} (hs : s < 1 / 2) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ s * ((catalan (n + 1) : ℝ) / 4 ^ (n + 1))) ∧
    Tendsto (fun p : ℝ => (1 - p) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ)))) (𝓝[≠] (1 / 2))
      (𝓝 ((1 - 1 / 2) / (1 / 2) * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * (1 / 2) * (1 - 1 / 2)) * ((n + 1 : ℕ) : ℝ))))) := by
  set b : ℕ → ℝ := fun n => if n = 0 then 0 else (n : ℝ) ^ s * ((catalan n : ℝ) / 4 ^ n)
  have hb : Summable b := by
    refine summable_of_isBigO_nat' ?_ (moment_coeff_isEquivalent s).isBigO
    exact (Real.summable_nat_rpow.2 (by linarith)).mul_left _
  have hval : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s * ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
      exp (-(-log (4 * (1 / 2) * (1 - 1 / 2)) * ((n + 1 : ℕ) : ℝ)))) = ∑' n, b n := by
    rw [tsum_succ_eq_tsum_ite]
    norm_num [b]
  refine ⟨?_, ?_⟩
  · have := (summable_nat_add_iff 1).2 hb
    refine this.congr fun n => ?_
    simp [b]
  rw [hval, show (1 - 1 / 2 : ℝ) / (1 / 2) = 1 by norm_num]
  have hpq : Tendsto (fun p : ℝ => (1 - p) / p) (𝓝[≠] (1 / 2)) (𝓝 1) := by
    have : Tendsto (fun p : ℝ => (1 - p) / p) (𝓝 (1 / 2)) (𝓝 ((1 - 1 / 2) / (1 / 2))) :=
      ((continuous_const.sub continuous_id).tendsto _).div (continuous_id.tendsto _)
        (by norm_num)
    exact (this.mono_left nhdsWithin_le_nhds).trans_eq (by norm_num)
  refine (hpq.mul ((tendsto_tsum_exp_of_summable hb).comp tendsto_lambda)).congr' ?_
  exact Eventually.of_forall fun p => by
    simp only [Function.comp_apply]
    rw [tsum_succ_eq_tsum_ite]

/-- **Ratio.** For `s > 1/2`, `M_{s+1}(p)/M_s(p) ~ (s-1/2)/(4(p-1/2)²)` as `p → 1/2`. -/
theorem moment_ratio_isEquivalent {s : ℝ} (hs : 1 / 2 < s) :
    (fun p : ℝ => ((1 - p) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (s + 1) *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ)))) /
      ((1 - p) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ))))) ~[𝓝[≠] (1 / 2)]
      fun p => (s - 1 / 2) / (4 * (p - 1 / 2) ^ 2) := by
  have ha : 0 < s - 1 / 2 := by linarith
  have hpi : 0 < √π := Real.sqrt_pos.2 pi_pos
  have h1 := moment_isEquivalent_of_gt (s := s + 1) (by linarith)
  have h0 := moment_isEquivalent_of_gt hs
  have hdiv := h1.div h0
  have hl := ((IsEquivalent.refl (u := fun _ : ℝ => s - 1 / 2)).div lambda_isEquivalent)
  refine (hdiv.trans (IsEquivalent.trans ?_ hl))
  refine IsEquivalent.congr_left IsEquivalent.refl ?_
  filter_upwards [eventually_mem_Ioo_half, self_mem_nhdsWithin] with p hp hne
  obtain ⟨h0, h1⟩ := four_mul_mem_Ioo hp.1 hp.2 hne
  have hl : 0 < -log (4 * p * (1 - p)) := neg_pos.2 (log_neg h0 h1)
  have hG : Gamma (s + 1 - 1 / 2) = (s - 1 / 2) * Gamma (s - 1 / 2) := by
    rw [show s + 1 - 1 / 2 = (s - 1 / 2) + 1 by ring, Gamma_add_one ha.ne']
  have hGpos : 0 < Gamma (s - 1 / 2) := Gamma_pos_of_pos ha
  have hr : (-log (4 * p * (1 - p))) ^ (-(s + 1 - 1 / 2)) =
      (-log (4 * p * (1 - p))) ^ (-(s - 1 / 2)) / (-log (4 * p * (1 - p))) := by
    rw [show -(s + 1 - 1 / 2) = -(s - 1 / 2) - 1 by ring, Real.rpow_sub_one hl.ne']
  have hrpos : 0 < (-log (4 * p * (1 - p))) ^ (-(s - 1 / 2)) := Real.rpow_pos_of_pos hl _
  simp only [Pi.div_apply]
  rw [hG, hr]
  generalize Gamma (s - 1 / 2) = G at hGpos ⊢
  generalize (-log (4 * p * (1 - p))) ^ (-(s - 1 / 2)) = r at hrpos ⊢
  generalize -log (4 * p * (1 - p)) = l at hl ⊢
  field_simp

/-! ### The moments of the cluster-size law -/

section Law

open MeasureTheory PercLib.Percolation.Bond

/-- For `0 < p < 1`, the moment `M_s(p) = ∑_{n ≥ 1} n^s P_p(|K| = n)` of the tree profile
`q p` equals the series of the analytic theorems above. -/
theorem binaryTree_moment_eq_series (q : ℝ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ (p : ℝ) (hp : p ∈ unitInterval), ∀ e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨p, hp⟩ : unitInterval) else 0)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s : ℝ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal) =
      (1 - p) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        exp (-(-log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ))) := by
  rw [← tsum_mul_left]
  congr 1
  funext n
  have hx : 0 < 4 * p * (1 - p) := by
    have : 0 < 1 - p := by linarith
    positivity
  rw [binaryTree_law_cluster_card_toReal ⟨p, hp0.le, hp1.le⟩ (q p) (hq p ⟨hp0.le, hp1.le⟩)
    (by omega : 1 ≤ n + 1)]
  rw [neg_mul, neg_neg, ← Real.rpow_def_of_pos hx, Real.rpow_natCast]
  have h := catalan_div_four_pow_mul_eq hp0.ne' (by omega : 1 ≤ n + 1)
  rw [← h]
  ring

/-- **`s > 1/2`.** `M_s(p) ~ Γ(s-1/2) λ^{-(s-1/2)}/√π` as `p → 1/2`. -/
theorem binaryTree_moment_isEquivalent_of_gt (q : ℝ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ (p : ℝ) (hp : p ∈ unitInterval), ∀ e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨p, hp⟩ : unitInterval) else 0)
    {s : ℝ} (hs : 1 / 2 < s) :
    (fun p : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)
      ~[𝓝[≠] (1 / 2)]
      fun p => Gamma (s - 1 / 2) * (-log (4 * p * (1 - p))) ^ (-(s - 1 / 2)) / √π :=
  (moment_isEquivalent_of_gt hs).congr_left (eventually_mem_Ioo_half.mono fun _ hp =>
    (binaryTree_moment_eq_series q hq hp.1 hp.2 s).symm)

/-- **`s = 1/2`.** `M_{1/2}(p) ~ log(1/λ)/√π` as `p → 1/2`. -/
theorem binaryTree_moment_isEquivalent_half (q : ℝ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ (p : ℝ) (hp : p ∈ unitInterval), ∀ e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨p, hp⟩ : unitInterval) else 0) :
    (fun p : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)
      ~[𝓝[≠] (1 / 2)]
      fun p => log (1 / -log (4 * p * (1 - p))) / √π :=
  moment_isEquivalent_half.congr_left (eventually_mem_Ioo_half.mono fun _ hp =>
    (binaryTree_moment_eq_series q hq hp.1 hp.2 (1 / 2)).symm)

/-- **`s < 1/2`.** `M_s(1/2) < ∞` and `M_s(p) → M_s(1/2)` as `p → 1/2`. -/
theorem binaryTree_moment_tendsto_of_lt (q : ℝ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ (p : ℝ) (hp : p ∈ unitInterval), ∀ e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨p, hp⟩ : unitInterval) else 0)
    {s : ℝ} (hs : s < 1 / 2) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q (1 / 2)) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal) ∧
      Tendsto (fun p : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)
        (𝓝[≠] (1 / 2)) (𝓝 (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q (1 / 2))
            {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)) := by
  obtain ⟨hsum, hlim⟩ := moment_tendsto_of_lt hs
  refine ⟨hsum.congr fun n => ?_, ?_⟩
  · rw [binaryTree_law_cluster_card_toReal ⟨1 / 2, by norm_num, by norm_num⟩ (q (1 / 2))
      (hq (1 / 2) ⟨by norm_num, by norm_num⟩) (by omega : 1 ≤ n + 1)]
    simp only [add_tsub_cancel_right]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc (catalan (n + 1) : ℝ),
      ← pow_add, show n + (n + 1 + 1) = 2 * (n + 1) by ring, pow_mul]
    norm_num
    exact Or.inl (by rw [one_div_pow, mul_one_div])
  · rw [binaryTree_moment_eq_series q hq (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) s]
    exact hlim.congr' (eventually_mem_Ioo_half.mono fun _ hp =>
      (binaryTree_moment_eq_series q hq hp.1 hp.2 s).symm)

/-- **Ratio.** For `s > 1/2`, `M_{s+1}(p)/M_s(p) ~ (s-1/2)/(4(p-1/2)²)`. -/
theorem binaryTree_moment_ratio_isEquivalent (q : ℝ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ (p : ℝ) (hp : p ∈ unitInterval), ∀ e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨p, hp⟩ : unitInterval) else 0)
    {s : ℝ} (hs : 1 / 2 < s) :
    (fun p : ℝ => (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (s + 1) *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal) /
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal))
      ~[𝓝[≠] (1 / 2)]
      fun p => (s - 1 / 2) / (4 * (p - 1 / 2) ^ 2) :=
  (moment_ratio_isEquivalent hs).congr_left (eventually_mem_Ioo_half.mono fun p hp => by
    simp only []
    rw [binaryTree_moment_eq_series q hq hp.1 hp.2 s,
      binaryTree_moment_eq_series q hq hp.1 hp.2 (s + 1)])

end Law

/-! ### Non-vacuity -/

/-- `s = 1`: `M_1(p) ~ Γ(1/2) λ(p)^{-1/2}/√π`. -/
example := moment_isEquivalent_of_gt (s := 1) (by norm_num)

/-- `s = 0`: the series converges at `p = 1/2` and `M_0` is continuous there. -/
example := moment_tendsto_of_lt (s := 0) (by norm_num)

/-- `s = 3/2`: `M_{5/2}/M_{3/2} ~ 1/(4(p-1/2)²)`. -/
example := moment_ratio_isEquivalent (s := 3 / 2) (by norm_num)

end PercLib.Models

end
