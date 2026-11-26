/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The size-biased band estimate and the lower tail up to constants in Proposition I.3.1(1) of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, pp. 28–29.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/VolumeTailUpToConstants.lean` and
`PercLib/CriticalLRP/Analysis/VolumeTailLower.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source's `sizeBiasedBaseLaw μ` and `mean μ` are written out as
`μ.withDensity fun x => ENNReal.ofReal (x / ∫ x, x ∂μ)` and `∫ x, x ∂μ` (the `withDensity`
form of `PercLib/Probability/SizeBias.lean`); the band lemmas are stated for any normaliser
`m > 0` in place of the mean, any level `n > 0` in place of `n ≥ 1` and a finite in place of
a probability size-biased measure; `isProbabilityMeasure_sizeBiasedBaseLaw` is
`isProbabilityMeasure_withDensity_ofReal_div_integral` of `VolumeTail/SizeBiasMGF.lean`; the
unused positivity hypothesis of `inverse_doubling_half_iter` is dropped; the two files are
merged; `import Mathlib`, `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.VolumeTail.SizeBiasMGF

/-! # The lower tail of the volume up to constants

Let `μ` be a law on `ℝ` and `m > 0`, and let `μ̂ = μ.withDensity fun x => ENNReal.ofReal (x / m)`
(for `m = ∫ x dμ` the size-biased law `P̂`).

## Main results

* `measureReal_Ici_eq_mul_setIntegral_inv`: `μ[n, ∞) = m ∫_{[n,∞)} x⁻¹ dμ̂` for `n > 0`.
* `mul_measureReal_Icc_div_le_measureReal_Ici`: the band estimate
  `m μ̂[a, b] / b ≤ μ[n, ∞)` for `0 < n ≤ a`.
* `le_pow_mul_div_two_pow_of_doubling`, `exists_le_mul_div_of_doubling`: doubling of an
  increasing scale `g` gives `g n ≤ K g(n / c)` for large `n`.
* `exists_lower_tail_of_doubling`: the lower bound `κ g(n)^α / n ≤ T(n)` of Proposition
  I.3.1(1) for large `n`, from a uniform size-biased band, a mean lower bound `a r^α` and a
  doubling inverse scale `g` of `f`.

The conclusion holds above an explicit threshold; the source's form for all `n ≥ 1` is not
claimed, and Proposition I.3.1(2) is not treated here.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace PercLib.Analysis

/-! ### The band estimate -/

/-- **Inverse-moment form of the tail**: `μ[n, ∞) = m ∫_{[n,∞)} x⁻¹ dμ̂` for `m, n > 0`, with
`μ̂ = μ.withDensity (x / m)`. -/
theorem measureReal_Ici_eq_mul_setIntegral_inv {μ : Measure ℝ} {m n : ℝ} (hm : 0 < m)
    (hn : 0 < n) :
    μ.real (Ici n) = m * ∫ x in Ici n, x⁻¹ ∂μ.withDensity fun x => ENNReal.ofReal (x / m) := by
  rw [restrict_withDensity measurableSet_Ici,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top), ← integral_const_mul]
  calc μ.real (Ici n) = ∫ _x in Ici n, (1 : ℝ) ∂μ := by simp
    _ = _ := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx0 : 0 < x := hn.trans_le hx
      rw [smul_eq_mul, ENNReal.toReal_ofReal (div_nonneg hx0.le hm.le)]
      field_simp

/-- Restricting the inverse moment to a band `[a, b] ⊆ [n, ∞)`: `μ̂[a, b] / b ≤ ∫_{[n,∞)} x⁻¹ dμ̂`
for a finite measure `μ̂` and `0 < n ≤ a`. -/
theorem measureReal_Icc_div_le_setIntegral_inv {ν : Measure ℝ} [IsFiniteMeasure ν] {n a b : ℝ}
    (hn : 0 < n) (hna : n ≤ a) :
    ν.real (Icc a b) / b ≤ ∫ x in Ici n, x⁻¹ ∂ν := by
  have ha : 0 < a := hn.trans_le hna
  have hsub : Icc a b ⊆ Ici n := fun x hx => hna.trans hx.1
  have hInt : IntegrableOn (fun x : ℝ => x⁻¹) (Ici n) ν := by
    refine IntegrableOn.of_bound (measure_lt_top _ _) (by fun_prop) n⁻¹ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hn.trans_le hx))]
    exact inv_anti₀ hn hx
  calc ν.real (Icc a b) / b = ∫ _x in Icc a b, b⁻¹ ∂ν := by
        simp [div_eq_mul_inv, mul_comm]
    _ ≤ ∫ x in Icc a b, x⁻¹ ∂ν :=
        setIntegral_mono_on integrableOn_const (hInt.mono_set hsub) measurableSet_Icc
          fun x hx => inv_anti₀ (ha.trans_le hx.1) hx.2
    _ ≤ ∫ x in Ici n, x⁻¹ ∂ν := by
        refine setIntegral_mono_set hInt ?_ (Eventually.of_forall hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact inv_nonneg.mpr (hn.le.trans hx)

/-- **The band estimate** of Proposition I.3.1(1): `m μ̂[a, b] / b ≤ μ[n, ∞)` for
`μ̂ = μ.withDensity (x / m)` finite, `m > 0` and `0 < n ≤ a`. -/
theorem mul_measureReal_Icc_div_le_measureReal_Ici {μ : Measure ℝ} {m n a b : ℝ}
    [IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (x / m))] (hm : 0 < m)
    (hn : 0 < n) (hna : n ≤ a) :
    m * ((μ.withDensity fun x => ENNReal.ofReal (x / m)).real (Icc a b) / b) ≤ μ.real (Ici n) := by
  rw [measureReal_Ici_eq_mul_setIntegral_inv hm hn]
  exact mul_le_mul_of_nonneg_left (measureReal_Icc_div_le_setIntegral_inv hn hna) hm.le

/-- The band estimate with a lower bound `q ≤ μ̂[a, b]`: `m q / b ≤ μ[n, ∞)`. -/
theorem mul_div_le_measureReal_Ici_of_le {μ : Measure ℝ} {m n a b q : ℝ}
    [IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (x / m))] (hm : 0 < m)
    (hq : q ≤ (μ.withDensity fun x => ENNReal.ofReal (x / m)).real (Icc a b)) (hn : 0 < n)
    (hna : n ≤ a) (hab : a ≤ b) :
    m * (q / b) ≤ μ.real (Ici n) :=
  (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hq ((hn.trans_le hna).le.trans hab))
    hm.le).trans (mul_measureReal_Icc_div_le_measureReal_Ici hm hn hna)

/-! ### Doubling scales -/

/-- **Iterated doubling**: if `g (2x) ≤ D g(x)` for `x ≥ 1` and `D ≥ 0`, then
`g x ≤ D^k g(x / 2^k)` for `x ≥ 2^k`. -/
theorem le_pow_mul_div_two_pow_of_doubling {g : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x) :
    ∀ {k : ℕ} {x : ℝ}, (2 : ℝ) ^ k ≤ x → g x ≤ D ^ k * g (x / 2 ^ k) := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hx2 : (2 : ℝ) ^ k ≤ x / 2 := by linarith
    have hfirst : g x ≤ D * g (x / 2) := by
      simpa [show 2 * (x / 2) = x by ring] using hd (x / 2) (hk.trans hx2)
    calc g x ≤ D * g (x / 2) := hfirst
      _ ≤ D * (D ^ k * g (x / 2 / 2 ^ k)) := mul_le_mul_of_nonneg_left (ih hx2) hD
      _ = D ^ (k + 1) * g (x / 2 ^ (k + 1)) := by
        rw [div_div, ← pow_succ', pow_succ]
        ring

/-- **Doubling inverse scale**: for a monotone `g` with `g (2x) ≤ D g(x)` on `[1, ∞)` and
every `c > 0` there are `N` and `K > 0` with `g n ≤ K g(n / c)` for `n ≥ N`. -/
theorem exists_le_mul_div_of_doubling {g : ℝ → ℝ} {D c : ℝ} (hgmono : Monotone g)
    (hD : 0 < D) (hc : 0 < c) (hd : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x) :
    ∃ N K : ℝ, 0 < K ∧ ∀ n : ℝ, N ≤ n → g n ≤ K * g (n / c) := by
  by_cases hc1 : c ≤ 1
  · refine ⟨0, 1, one_pos, fun n hn => ?_⟩
    rw [one_mul]
    exact hgmono (le_div_self hn hc hc1)
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt c (by norm_num : (1 : ℝ) < 2)
    refine ⟨2 ^ k, D ^ k, pow_pos hD _, fun n hn => ?_⟩
    have hnpos : 0 < n := (pow_pos two_pos _).trans_le hn
    exact (le_pow_mul_div_two_pow_of_doubling hD.le hd hn).trans
      (mul_le_mul_of_nonneg_left (hgmono (div_le_div_of_nonneg_left hnpos.le hc hk.le))
        (pow_nonneg hD.le k))

/-! ### The lower tail -/

/-- **The lower tail up to constants** (Proposition I.3.1(1), above a threshold). Let `μ_r` be
laws on `ℝ` whose size-biased measures `μ̂_r` are finite for `r ≥ 1`, with
`a r^α ≤ E_{μ_r} X` and `q ≤ μ̂_r[c f(r), C f(r)]` for `r ≥ 1`, and let `T n` bound every
`μ_r[n, ∞)`. If `g` is monotone, positive, doubling on `[1, ∞)`, tends to `∞` and inverts `f`
on `(0, ∞)`, then `κ g(n)^α / n ≤ T n` for some `κ > 0` and all large `n`. -/
theorem exists_lower_tail_of_doubling {μ : ℝ → Measure ℝ} {f g T : ℝ → ℝ}
    {c C a q D α : ℝ}
    (hfin : ∀ r : ℝ, 1 ≤ r →
      IsFiniteMeasure ((μ r).withDensity fun x => ENNReal.ofReal (x / ∫ x, x ∂μ r)))
    (hc : 0 < c) (hcC : c ≤ C) (ha : 0 < a) (hq : 0 < q) (hα : 0 < α)
    (hmean : ∀ r : ℝ, 1 ≤ r → a * r ^ α ≤ ∫ x, x ∂μ r)
    (hband : ∀ r : ℝ, 1 ≤ r → q ≤
      ((μ r).withDensity fun x => ENNReal.ofReal (x / ∫ x, x ∂μ r)).real
        (Icc (c * f r) (C * f r)))
    (hT : ∀ r n : ℝ, (μ r).real (Ici n) ≤ T n)
    (hgmono : Monotone g) (hgpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hD : 0 < D) (hdouble : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x)
    (hgAtTop : Tendsto g atTop atTop) (hgf : ∀ x : ℝ, 0 < x → f (g x) = x) :
    ∃ N κ : ℝ, 0 < κ ∧ ∀ n : ℝ, N ≤ n → κ * g n ^ α / n ≤ T n := by
  have hC : 0 < C := hc.trans_le hcC
  obtain ⟨N, K, hK, hscale⟩ := exists_le_mul_div_of_doubling hgmono hD hc hdouble
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((hgAtTop.comp (tendsto_id.atTop_div_const hc)).eventually (eventually_ge_atTop 1))
  have hA : 0 < a * q * c / C := by positivity
  refine ⟨max N (max M 1), a * q * c / C * K ^ (-α), mul_pos hA (Real.rpow_pos_of_pos hK _),
    fun n hn => ?_⟩
  simp only [max_le_iff] at hn
  obtain ⟨hnN, hnM, hn1⟩ := hn
  have hnpos : 0 < n := one_pos.trans_le hn1
  set r := g (n / c) with hrdef
  have hr : 1 ≤ r := hM n hnM
  have hrpos : 0 < r := one_pos.trans_le hr
  have hfr : f r = n / c := hgf _ (div_pos hnpos hc)
  have := hfin r hr
  have hmeanpos : 0 < ∫ x, x ∂μ r :=
    (mul_pos ha (Real.rpow_pos_of_pos hrpos α)).trans_le (hmean r hr)
  have hper : (∫ x, x ∂μ r) * (q / (C * f r)) ≤ T n := by
    refine (mul_div_le_measureReal_Ici_of_le hmeanpos (hband r hr) hnpos ?_ ?_).trans (hT r n)
    · rw [hfr, mul_div_cancel₀ _ hc.ne']
    · rw [hfr]
      exact mul_le_mul_of_nonneg_right hcC (div_nonneg hnpos.le hc.le)
  have hpow : K ^ (-α) * g n ^ α ≤ r ^ α := by
    rw [Real.rpow_neg hK.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK α), ← Real.mul_rpow hK.le
      hrpos.le]
    exact Real.rpow_le_rpow (hgpos n hnpos).le (hscale n hnN) hα.le
  calc a * q * c / C * K ^ (-α) * g n ^ α / n = a * q * c / C * (K ^ (-α) * g n ^ α / n) := by
        ring
    _ ≤ a * q * c / C * (r ^ α / n) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hnpos.le) hA.le
    _ = a * r ^ α * (q / (C * f r)) := by
        rw [hfr]
        field_simp
    _ ≤ (∫ x, x ∂μ r) * (q / (C * f r)) := by
        refine mul_le_mul_of_nonneg_right (hmean r hr) ?_
        rw [hfr]
        positivity
    _ ≤ T n := hper

end PercLib.Analysis
