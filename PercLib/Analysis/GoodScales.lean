/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: higher moments under a uniform exponential tail, the interval
bound between good scales and the persistence of good scales (wiki cutoff-hydrodynamics, tags BZDZ,
DISO and YEVN). No upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import PercLib.Meta.Tag

/-! # Good scales

* `integral_rpow_add_le_of_tail` (BZDZ): a uniform exponential tail
  `P(X ≥ tM) ≤ A e^{-bt} P(X ≥ M)`, `t ≥ 1`, gives `E X^{p+q} ≤ D_{p,q} M^q E X^p` with
  `D_{p,q} = 1 + A e^{-b} + A (p+q) ∫_1^∞ t^{p+q-1} e^{-bt} dt`. The layer-cake formula splits at
  `M`: below `M` it is the moment of `min(X, M)`, above `M` the tail bound and Markov apply.
* `div_le_of_logDeriv_ge` (DISO): if `f > 0` is absolutely continuous on `[s, R/C]`,
  `f(s) ≥ b s^k`, `f(R/C) ≤ B (R/C)^k` and `(log f)' ≥ λ/t` almost everywhere with `λ > k`,
  then `R/s ≤ C (B/b)^{1/(λ-k)}`.
* `good_scale_persists` (YEVN): once `M(r_*) ≥ δ r_*^h`, the scales stay good up to the
  factor `L^{-h}`, `L = C (B/(c δ³))^{1/(λ-k)}`: the last good scale `s ≤ R` satisfies
  `R ≤ L s` by DISO.

The logarithm of `f` is absolutely continuous, so its increment is the integral of its
derivative, which is at least `λ log(R/(Cs))`; the endpoint bounds give at most
`log(B/b) + k log(R/(Cs))`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace PercLib.Analysis

/-- The logarithm is `1/m`-Lipschitz on `[m, ∞)`. -/
theorem lipschitzOnWith_log_Ici {m : ℝ} (hm : 0 < m) :
    LipschitzOnWith (Real.toNNReal (1 / m)) Real.log (Ici m) := by
  refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  rw [Real.dist_eq, Real.dist_eq]
  have key : ∀ u v : ℝ, m ≤ u → m ≤ v → v ≤ u → Real.log u - Real.log v ≤ 1 / m * (u - v) := by
    intro u v hu hv hvu
    have hv0 : 0 < v := hm.trans_le hv
    have hu0 : 0 < u := hm.trans_le hu
    rw [← Real.log_div hu0.ne' hv0.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    have h2 : u / v - 1 = (u - v) / v := by field_simp
    have h3 : (u - v) / v ≤ (u - v) / m :=
      div_le_div_of_nonneg_left (sub_nonneg.2 hvu) hm hv
    rw [h2] at h1
    rw [one_div_mul_eq_div]
    linarith
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hy0 hyx)), abs_of_nonneg (sub_nonneg.2 hyx)]
    exact key x y hx hy hyx
  · rw [abs_of_nonpos (sub_nonpos.2 (Real.log_le_log hx0 hxy)),
      abs_of_nonpos (sub_nonpos.2 hxy), neg_sub, neg_sub]
    exact key y x hy hx hxy

/-- The logarithm of a positive absolutely continuous function is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_log {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hpos : ∀ t ∈ uIcc a b, 0 < f t) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (f t)) a b := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_uIcc.exists_isMinOn (nonempty_uIcc) hf.continuousOn
  have hm : 0 < f t₀ := hpos t₀ ht₀
  exact (lipschitzOnWith_log_Ici hm).comp_absolutelyContinuousOnInterval
    (fun t ht => (hmin ht : f t₀ ≤ f t)) hf

/-- **DISO.** Let `C ≥ 1`, `s > 0`, `R ≥ C s`, `B ≥ b > 0` and `λ > k`. If `f > 0` is
absolutely continuous on `[s, R/C]` with `f(s) ≥ b s^k`, `f(R/C) ≤ B (R/C)^k` and
`(log f)'(t) ≥ λ/t` for almost every `t ∈ [s, R/C]`, then `R/s ≤ C (B/b)^{1/(λ-k)}`. -/
@[tag "DISO"]
theorem div_le_of_logDeriv_ge {f : ℝ → ℝ} {C s R b B lam k : ℝ} (hC : 1 ≤ C) (hs : 0 < s)
    (hR : C * s ≤ R) (hb : 0 < b) (hbB : b ≤ B) (hlk : k < lam)
    (hpos : ∀ t ∈ Icc s (R / C), 0 < f t) (hac : AbsolutelyContinuousOnInterval f s (R / C))
    (hfs : b * s ^ k ≤ f s) (hfR : f (R / C) ≤ B * (R / C) ^ k)
    (hderiv : ∀ᵐ t, t ∈ Icc s (R / C) → lam / t ≤ deriv (fun t => Real.log (f t)) t) :
    R / s ≤ C * (B / b) ^ (1 / (lam - k)) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  set t₁ := R / C
  have hst : s ≤ t₁ := by
    rw [le_div_iff₀ hC0]
    linarith
  have ht₁ : 0 < t₁ := hs.trans_le hst
  have huIcc : uIcc s t₁ = Icc s t₁ := uIcc_of_le hst
  have hlog := absolutelyContinuousOnInterval_log hac (fun t ht => hpos t (huIcc ▸ ht))
  have hftc := hlog.integral_deriv_eq_sub
  -- The integral of `λ/t` is `λ log(t₁/s)`.
  have hint : ∫ t in s..t₁, lam / t = lam * Real.log (t₁ / s) := by
    simp_rw [div_eq_mul_inv lam]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hs ht₁]
  have hcont : ContinuousOn (fun t : ℝ => lam / t) (uIcc s t₁) := by
    refine ContinuousOn.div continuousOn_const continuousOn_id fun t ht => ?_
    rw [huIcc] at ht
    exact (hs.trans_le ht.1).ne'
  have hmono : ∫ t in s..t₁, lam / t ≤ ∫ t in s..t₁, deriv (fun t => Real.log (f t)) t := by
    refine intervalIntegral.integral_mono_ae_restrict hst (hcont.intervalIntegrable)
      hlog.intervalIntegrable_deriv ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact hderiv
  rw [hint, hftc] at hmono
  have hfs0 : 0 < b * s ^ k := mul_pos hb (rpow_pos_of_pos hs k)
  have hlogs : Real.log (b * s ^ k) ≤ Real.log (f s) := Real.log_le_log hfs0 hfs
  have hlogt : Real.log (f t₁) ≤ Real.log (B * t₁ ^ k) :=
    Real.log_le_log (hpos t₁ ⟨hst, le_rfl⟩) hfR
  have hB0 : 0 < B := hb.trans_le hbB
  rw [Real.log_mul hb.ne' (rpow_pos_of_pos hs k).ne', Real.log_rpow hs] at hlogs
  rw [Real.log_mul hB0.ne' (rpow_pos_of_pos ht₁ k).ne', Real.log_rpow ht₁] at hlogt
  rw [Real.log_div ht₁.ne' hs.ne'] at hmono
  have hkey : (lam - k) * Real.log (t₁ / s) ≤ Real.log (B / b) := by
    rw [Real.log_div ht₁.ne' hs.ne', Real.log_div hB0.ne' hb.ne']
    nlinarith
  have hratio : t₁ / s ≤ (B / b) ^ (1 / (lam - k)) := by
    have hlk' : 0 < lam - k := sub_pos.2 hlk
    rw [← Real.exp_log (div_pos ht₁ hs), Real.rpow_def_of_pos (div_pos hB0 hb)]
    refine Real.exp_le_exp.2 ?_
    rw [mul_one_div, le_div_iff₀ hlk', mul_comm]
    exact hkey
  have : R / s = C * (t₁ / s) := by
    simp only [t₁]
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hratio hC0.le

/-- At a good scale `M(r) ≥ δ r^h`, the lower bound `f(r) ≥ c M(r)³ / r^d` gives
`f(r) ≥ c δ³ r^{3h-d}`. -/
theorem le_of_good_scale {M f : ℝ → ℝ} {d h c δ r : ℝ} (hr : 0 < r) (hc : 0 < c) (hδ : 0 < δ)
    (hlow : c * M r ^ 3 / r ^ d ≤ f r) (hgood : δ * r ^ h ≤ M r) :
    c * δ ^ 3 * r ^ (3 * h - d) ≤ f r := by
  refine le_trans ?_ hlow
  have hrh : 0 < δ * r ^ h := mul_pos hδ (rpow_pos_of_pos hr h)
  have hcube : (δ * r ^ h) ^ 3 ≤ M r ^ 3 := pow_le_pow_left₀ hrh.le hgood 3
  have heq : c * δ ^ 3 * r ^ (3 * h - d) = c * (δ * r ^ h) ^ 3 / r ^ d := by
    rw [Real.rpow_sub hr, mul_pow, ← Real.rpow_natCast (r ^ h) 3, ← Real.rpow_mul hr.le]
    push_cast
    ring_nf
  rw [heq]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcube hc.le)
    (rpow_pos_of_pos hr d).le

/-- **YEVN.** Let `h, r₀, c, δ > 0`, `C ≥ 1`, `k = 3h - d` and `λ > k` (the hypotheses
`d > 0`, `B > 0` and `M > 0` of the wiki statement are not needed). Let `M` be
nondecreasing on `[r₀, ∞)` and `f > 0` locally absolutely continuous on
`[r₀, ∞)` with `c M(r)³ / r^d ≤ f(r) ≤ B r^k` for `r ≥ r₀`, and suppose that for almost
every `r ≥ r₀`, `M(Cr) ≤ δ (Cr)^h` implies `(log f)'(r) ≥ λ/r`. If `M(r_*) ≥ δ r_*^h` for some
`r_* ≥ r₀`, then `L = C (B/(c δ³))^{1/(λ-k)}` satisfies `L ≥ C` and
`M(R) ≥ δ L^{-h} R^h` for every `R ≥ r_*`. -/
@[tag "YEVN"]
theorem good_scale_persists {M f : ℝ → ℝ} {d h r₀ c B δ C lam k : ℝ}
    (hh : 0 < h) (hr₀ : 0 < r₀) (hc : 0 < c) (hδ : 0 < δ) (hC : 1 ≤ C)
    (hk : k = 3 * h - d) (hlk : k < lam) (hMmono : MonotoneOn M (Ici r₀))
    (hfpos : ∀ r, r₀ ≤ r → 0 < f r)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hlow : ∀ r, r₀ ≤ r → c * M r ^ 3 / r ^ d ≤ f r) (hup : ∀ r, r₀ ≤ r → f r ≤ B * r ^ k)
    (hderiv : ∀ᵐ r, r₀ ≤ r → M (C * r) ≤ δ * (C * r) ^ h →
      lam / r ≤ deriv (fun t => Real.log (f t)) r)
    {r_star : ℝ} (hrs : r₀ ≤ r_star) (hMrs : δ * r_star ^ h ≤ M r_star) :
    C ≤ C * (B / (c * δ ^ 3)) ^ (1 / (lam - k)) ∧
      ∀ R, r_star ≤ R →
        δ * (C * (B / (c * δ ^ 3)) ^ (1 / (lam - k))) ^ (-h) * R ^ h ≤ M R := by
  subst hk
  set k := 3 * h - d
  set b := c * δ ^ 3
  have hb : 0 < b := mul_pos hc (pow_pos hδ 3)
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hrs0 : 0 < r_star := hr₀.trans_le hrs
  -- `b ≤ B`, read off at `r_*`.
  have hbB : b ≤ B := by
    have h1 := le_of_good_scale hrs0 hc hδ (hlow r_star hrs) hMrs
    have h2 := (h1.trans (hup r_star hrs))
    exact le_of_mul_le_mul_right h2 (rpow_pos_of_pos hrs0 k)
  set L := C * (B / b) ^ (1 / (lam - k))
  have hlk' : 0 < lam - k := sub_pos.2 hlk
  have hone : 1 ≤ (B / b) ^ (1 / (lam - k)) :=
    Real.one_le_rpow ((one_le_div hb).2 hbB) (by positivity)
  have hCL : C ≤ L := le_mul_of_one_le_right hC0.le hone
  refine ⟨hCL, fun R hR => ?_⟩
  have hL0 : 0 < L := hC0.trans_le hCL
  have hR0 : 0 < R := hrs0.trans_le hR
  -- The last good scale below `R`.
  set G := {r | r_star ≤ r ∧ r ≤ R ∧ δ * r ^ h ≤ M r}
  have hGne : G.Nonempty := ⟨r_star, le_rfl, hR, hMrs⟩
  have hGbdd : BddAbove G := ⟨R, fun r hr => hr.2.1⟩
  set s := sSup G
  have hs₁ : r_star ≤ s := le_csSup hGbdd ⟨le_rfl, hR, hMrs⟩
  have hs₂ : s ≤ R := csSup_le hGne fun r hr => hr.2.1
  have hs0 : 0 < s := hrs0.trans_le hs₁
  have hsr₀ : r₀ ≤ s := hrs.trans hs₁
  have hsgood : δ * s ^ h ≤ M s := by
    have hclosed : IsClosed {r : ℝ | δ * r ^ h ≤ M s} :=
      isClosed_le (continuous_const.mul (Real.continuous_rpow_const hh.le)) continuous_const
    refine closure_minimal (fun r hr => ?_) hclosed (csSup_mem_closure hGne hGbdd)
    exact hr.2.2.trans (hMmono (hrs.trans hr.1) hsr₀ (le_csSup hGbdd hr))
  have hbad : ∀ t, s < t → t ≤ R → M t < δ * t ^ h := by
    intro t hst htR
    by_contra hcon
    exact (not_le.2 hst) (le_csSup hGbdd ⟨hs₁.trans hst.le, htR, not_lt.1 hcon⟩)
  -- `R ≤ L s`.
  have hRs : R / s ≤ L := by
    rcases le_or_gt (C * s) R with hCs | hCs
    · have hRC : s ≤ R / C := by
        rw [le_div_iff₀ hC0]
        linarith
      refine div_le_of_logDeriv_ge hC hs0 hCs hb hbB hlk
        (fun t ht => hfpos t (hsr₀.trans ht.1))
        ((hac (R / C) (hsr₀.trans hRC)).mono (by
          rw [uIcc_of_le hRC, uIcc_of_le (hsr₀.trans hRC)]
          exact Icc_subset_Icc hsr₀ le_rfl))
        (le_of_good_scale hs0 hc hδ (hlow s hsr₀) hsgood)
        (hup (R / C) (hsr₀.trans hRC)) ?_
      have hne : ∀ᵐ t : ℝ, t ≠ s := by
        rw [ae_iff]
        simp
      filter_upwards [hderiv, hne] with t ht hts htI
      have hst : s < t := lt_of_le_of_ne htI.1 (Ne.symm hts)
      have hCt : C * t ≤ R := by
        have := htI.2
        rw [le_div_iff₀ hC0] at this
        linarith
      exact ht (hsr₀.trans htI.1)
        (hbad (C * t) (hst.trans_le (le_mul_of_one_le_left (hs0.trans hst).le hC)) hCt).le
    · rw [div_le_iff₀ hs0]
      exact hCs.le.trans (mul_le_mul_of_nonneg_right hCL hs0.le)
  -- `M(R) ≥ M(s) ≥ δ s^h ≥ δ (R/L)^h`.
  have hsL : R / L ≤ s := by
    rw [div_le_iff₀ hL0]
    rw [div_le_iff₀ hs0] at hRs
    linarith
  have hpow : (R / L) ^ h ≤ s ^ h :=
    Real.rpow_le_rpow (div_pos hR0 hL0).le hsL hh.le
  have hMR : M s ≤ M R := hMmono hsr₀ (hsr₀.trans hs₂) hs₂
  calc δ * L ^ (-h) * R ^ h = δ * (R / L) ^ h := by
        rw [Real.div_rpow hR0.le hL0.le, Real.rpow_neg hL0.le]
        ring
    _ ≤ δ * s ^ h := mul_le_mul_of_nonneg_left hpow hδ.le
    _ ≤ M s := hsgood
    _ ≤ M R := hMR

/-! ### BZDZ: a uniform exponential tail controls higher moments -/

/-- The kernel `t^{r-1} e^{-bt}` is integrable on `(1, ∞)`. -/
theorem integrableOn_rpow_mul_exp_neg_Ioi_one {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-b * t)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := r - 1) (p := 1) (by linarith)
    one_pos hb
  simp only [Real.rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi zero_le_one)

/-- `∫_{t > M} k(t/M) dt = M ∫_{s > 1} k(s) ds` for the kernel `k(s) = s^{r-1} e^{-bs}`, with
integrability. -/
theorem integral_kernel_scale {r b M : ℝ} (hr : 0 < r) (hb : 0 < b) (hM : 0 < M) :
    IntegrableOn (fun t : ℝ => (M⁻¹ * t) ^ (r - 1) * Real.exp (-b * (M⁻¹ * t))) (Ioi M) ∧
      ∫ t in Ioi M, (M⁻¹ * t) ^ (r - 1) * Real.exp (-b * (M⁻¹ * t)) =
        M * ∫ t in Ioi 1, t ^ (r - 1) * Real.exp (-b * t) := by
  set k : ℝ → ℝ := fun t => t ^ (r - 1) * Real.exp (-b * t)
  have hk := integrableOn_rpow_mul_exp_neg_Ioi_one hr hb
  have hF : Integrable ((Ioi (1 : ℝ)).indicator k) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hk
  have hFc := hF.comp_mul_left' (inv_ne_zero hM.ne')
  have heq : EqOn (fun t => (Ioi (1 : ℝ)).indicator k (M⁻¹ * t)) (fun t => k (M⁻¹ * t))
      (Ioi M) := by
    intro t ht
    have : (1 : ℝ) < M⁻¹ * t := by
      rw [← div_eq_inv_mul, one_lt_div hM]
      exact ht
    simp [indicator_of_mem (show M⁻¹ * t ∈ Ioi (1 : ℝ) from this)]
  refine ⟨(hFc.integrableOn).congr_fun heq measurableSet_Ioi, ?_⟩
  have := integral_comp_mul_left_Ioi k M (inv_pos.2 hM)
  rw [inv_inv, inv_mul_cancel₀ hM.ne', smul_eq_mul] at this
  exact this

/-- **BZDZ.** Let `X ≥ 0` be a random variable on a finite measure space, `M, A, b > 0`, and
`P(X ≥ tM) ≤ A e^{-bt} P(X ≥ M)` for `t ≥ 1`. For `p, q > 0` with `E X^p < ∞`,
`E X^{p+q} ≤ D_{p,q} M^q E X^p` where
`D_{p,q} = 1 + A e^{-b} + A (p+q) ∫_1^∞ t^{p+q-1} e^{-bt} dt`; the integral converges and
`X^{p+q}` is integrable. -/
@[tag "BZDZ"]
theorem integral_rpow_add_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {M A b p q : ℝ} (hM : 0 < M) (hA : 0 < A) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (htail : ∀ t, 1 ≤ t → μ.real {ω | t * M ≤ X ω} ≤ A * Real.exp (-b * t) * μ.real {ω | M ≤ X ω})
    (hint : Integrable (fun ω => X ω ^ p) μ) :
    IntegrableOn (fun t : ℝ => t ^ (p + q - 1) * Real.exp (-b * t)) (Ioi 1) ∧
      Integrable (fun ω => X ω ^ (p + q)) μ ∧
      ∫ ω, X ω ^ (p + q) ∂μ ≤ (1 + A * Real.exp (-b) + A * (p + q) *
        ∫ t in Ioi 1, t ^ (p + q - 1) * Real.exp (-b * t)) * M ^ q * ∫ ω, X ω ^ p ∂μ := by
  set r := p + q
  have hr : 0 < r := add_pos hp hq
  set I := ∫ t in Ioi 1, t ^ (r - 1) * Real.exp (-b * t)
  have hkI := integrableOn_rpow_mul_exp_neg_Ioi_one hr hb
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _) (Real.exp_pos _).le
  set E := ∫ ω, X ω ^ p ∂μ
  have hE : ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂μ = ENNReal.ofReal E :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hX0 ω) p)).symm
  have hE0 : 0 ≤ E := integral_nonneg fun ω => Real.rpow_nonneg (hX0 ω) p
  set P := μ.real {ω | M ≤ X ω}
  -- Markov: `M^p P ≤ E`.
  have hMarkov : M ^ p * P ≤ E := by
    have h := mul_meas_ge_le_lintegral₀ (μ := μ)
      (f := fun ω => ENNReal.ofReal (X ω ^ p)) (by fun_prop) (ENNReal.ofReal (M ^ p))
    have hsub : {ω | M ≤ X ω} ⊆ {ω | ENNReal.ofReal (M ^ p) ≤ ENNReal.ofReal (X ω ^ p)} :=
      fun ω hω => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hM.le hω hp.le)
    have h2 := (mul_le_mul_right (measure_mono hsub) _).trans h
    rw [hE, ← ofReal_measureReal (measure_ne_top _ _) , ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff hE0] at h2
    exact h2
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (r - 1))
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hX0) hXm.aemeasurable hr
  -- Part I: the layer below `M` is the `r`-th moment of `min X M`.
  set Y : Ω → ℝ := fun ω => min (X ω) M
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_min (hX0 ω) hM.le
  have hlayerY := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hY0) (hXm.min measurable_const).aemeasurable hr
  have hI1 : ENNReal.ofReal r * ∫⁻ t in Ioc 0 M, μ {ω | t ≤ X ω} * w t ≤
      ENNReal.ofReal (M ^ q * E) := by
    have h1 : ∫⁻ t in Ioc 0 M, μ {ω | t ≤ X ω} * w t =
        ∫⁻ t in Ioc 0 M, μ {ω | t ≤ Y ω} * w t := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      congr 2
      ext ω
      simp only [mem_ofPred_eq, Y, le_min_iff, ht.2, and_true]
    rw [h1]
    refine (mul_le_mul_right (lintegral_mono_set Ioc_subset_Ioi_self) _).trans ?_
    rw [← hlayerY, ENNReal.ofReal_mul (by positivity), ← hE,
      ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_mono fun ω => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_add' (hY0 ω) hr.ne', mul_comm]
    exact mul_le_mul (Real.rpow_le_rpow (hY0 ω) (min_le_right _ _) hq.le)
      (Real.rpow_le_rpow (hY0 ω) (min_le_left _ _) hp.le) (Real.rpow_nonneg (hY0 ω) _)
      (Real.rpow_nonneg hM.le _)
  -- Part II: the layer above `M`, by the tail hypothesis.
  obtain ⟨hkM, hkMI⟩ := integral_kernel_scale (r := r) hr hb hM
  set c := A * P * M ^ (r - 1)
  have hP0 : 0 ≤ P := measureReal_nonneg
  have hc0 : 0 ≤ c := by positivity
  have hI2 : ENNReal.ofReal r * ∫⁻ t in Ioi M, μ {ω | t ≤ X ω} * w t ≤
      ENNReal.ofReal (r * A * I * M ^ q * E) := by
    have hpt : ∀ t ∈ Ioi M, μ {ω | t ≤ X ω} * w t ≤
        ENNReal.ofReal (c * ((M⁻¹ * t) ^ (r - 1) * Real.exp (-b * (M⁻¹ * t)))) := by
      intro t ht
      have ht1 : 1 ≤ M⁻¹ * t := by
        rw [← div_eq_inv_mul, one_le_div hM]
        exact le_of_lt ht
      have h := htail (M⁻¹ * t) ht1
      rw [show M⁻¹ * t * M = t by field_simp] at h
      rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_mul measureReal_nonneg]
      refine ENNReal.ofReal_le_ofReal ?_
      have hpow : t ^ (r - 1) = M ^ (r - 1) * (M⁻¹ * t) ^ (r - 1) := by
        rw [← Real.mul_rpow hM.le (by positivity), mul_inv_cancel_left₀ hM.ne']
      rw [hpow]
      have ht0 : 0 ≤ (M⁻¹ * t) ^ (r - 1) := by positivity
      calc μ.real {ω | t ≤ X ω} * (M ^ (r - 1) * (M⁻¹ * t) ^ (r - 1))
          ≤ A * Real.exp (-b * (M⁻¹ * t)) * P * (M ^ (r - 1) * (M⁻¹ * t) ^ (r - 1)) :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ = c * ((M⁻¹ * t) ^ (r - 1) * Real.exp (-b * (M⁻¹ * t))) := by
            simp only [c]
            ring
    have hk0 : ∀ t ∈ Ioi M, 0 ≤ c * ((M⁻¹ * t) ^ (r - 1) * Real.exp (-b * (M⁻¹ * t))) :=
      fun t ht => mul_nonneg hc0 (mul_nonneg (Real.rpow_nonneg (by
        have : 0 < t := hM.trans ht
        positivity) _) (Real.exp_pos _).le)
    calc ENNReal.ofReal r * ∫⁻ t in Ioi M, μ {ω | t ≤ X ω} * w t
        ≤ ENNReal.ofReal r * ∫⁻ t in Ioi M,
            ENNReal.ofReal (c * ((M⁻¹ * t) ^ (r - 1) * Real.exp (-b * (M⁻¹ * t)))) :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hpt) _
      _ = ENNReal.ofReal (r * (c * (M * I))) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hkM.const_mul c)
            (ae_restrict_of_forall_mem measurableSet_Ioi hk0), integral_const_mul, hkMI,
            ← ENNReal.ofReal_mul hr.le]
      _ ≤ ENNReal.ofReal (r * A * I * M ^ q * E) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hMr : M ^ (r - 1) * M = M ^ q * M ^ p := by
            rw [← Real.rpow_add_one hM.ne', ← Real.rpow_add hM]
            congr 1
            simp only [r]
            ring
          have : r * (c * (M * I)) = r * A * I * M ^ q * (M ^ p * P) := by
            simp only [c]
            rw [show r * (A * P * M ^ (r - 1) * (M * I)) = r * A * I * P * (M ^ (r - 1) * M) by
              ring, hMr]
            ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hMarkov (by positivity)
  -- Assemble.
  have hsplit : Ioi (0 : ℝ) = Ioc 0 M ∪ Ioi M := (Ioc_union_Ioi_eq_Ioi hM.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) M) (Ioi M) :=
    Set.disjoint_left.2 fun t h1 h2 => (not_lt.2 h1.2) h2
  have hbound : ∫⁻ ω, ENNReal.ofReal (X ω ^ r) ∂μ ≤
      ENNReal.ofReal ((1 + A * Real.exp (-b) + A * r * I) * M ^ q * E) := by
    rw [hlayer, hsplit, lintegral_union measurableSet_Ioi hdisj, mul_add]
    refine (add_le_add hI1 hI2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ A * Real.exp (-b) * M ^ q * E := by positivity
    nlinarith
  have hr0 : 0 ≤ᵐ[μ] fun ω => X ω ^ r :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hX0 ω) r
  have hmeas : AEStronglyMeasurable (fun ω => X ω ^ r) μ :=
    (hXm.pow_const r).aestronglyMeasurable
  have hInt : Integrable (fun ω => X ω ^ r) μ :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hr0).2 (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hkI, hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hr0 hmeas]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

/-! ### Non-vacuity -/

/-- `div_le_of_logDeriv_ge` with `f(t) = t`, `s = C = b = 1`, `k = 0`, `λ = 1`, `R = B = 2`, where
`(log f)' = 1/t` and the conclusion `2 ≤ 2` is an equality. -/
example : (2 : ℝ) / 1 ≤ 1 * (2 / 1) ^ (1 / ((1 : ℝ) - 0)) := by
  refine div_le_of_logDeriv_ge (f := id) le_rfl one_pos (by norm_num) one_pos (by norm_num)
    zero_lt_one (fun t ht => by simp only [id]; linarith [ht.1])
    (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval) (by simp) (by simp) ?_
  refine Filter.Eventually.of_forall fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
  simp only [id, Real.deriv_log, one_div, le_refl]

/-- `good_scale_persists` with `h = d = δ = c = C = r₀ = r_* = 1`, `k = 2`, `λ = 3`, `B = 8`,
`M(r) = 2r` and `f(r) = 8 r²`. Every scale is good, so the derivative hypothesis is vacuous. -/
example : (1 : ℝ) ≤ 1 * (8 / (1 * 1 ^ 3)) ^ (1 / ((3 : ℝ) - 2)) ∧
    ∀ R, (1 : ℝ) ≤ R →
      1 * (1 * (8 / (1 * 1 ^ 3)) ^ (1 / ((3 : ℝ) - 2))) ^ (-(1 : ℝ)) * R ^ (1 : ℝ) ≤ 2 * R := by
  refine good_scale_persists (M := fun r => 2 * r) (f := fun r => 8 * r ^ 2) (d := 1) (B := 8)
    one_pos one_pos one_pos one_pos le_rfl (by norm_num) (by norm_num)
    (fun x _ y _ hxy => by linarith) (fun r hr => by positivity)
    (fun R _ => ?_) (fun r hr => ?_) (fun r hr => ?_) ?_ le_rfl (by norm_num)
  · exact ((contDiff_const.mul (contDiff_id.pow 2)).contDiffOn).absolutelyContinuousOnInterval
  · have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    rw [Real.rpow_one, div_le_iff₀ hr0]
    ring_nf
    rfl
  · norm_num
  · refine Filter.Eventually.of_forall fun r hr hM => ?_
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    rw [Real.rpow_one] at hM
    linarith

/-- `integral_rpow_add_le_of_tail` with `X ≡ 1` under a point mass, `M = p = q = b = 1`, `A = e`:
the tail hypothesis holds (with equality at `t = 1`). -/
example := integral_rpow_add_le_of_tail (μ := Measure.dirac ()) (X := fun _ : Unit => (1 : ℝ))
    measurable_const (fun _ => zero_le_one) one_pos (Real.exp_pos 1) one_pos one_pos one_pos
    (fun t ht => by
      have h1 : {ω : Unit | (1 : ℝ) ≤ (fun _ : Unit => (1 : ℝ)) ω} = univ := by
        ext ω
        simp
      rw [h1, probReal_univ, mul_one, ← Real.exp_add]
      by_cases h : t ≤ 1
      · have h2 : {ω : Unit | t ≤ 1} = univ := by
          ext ω
          simp only [mem_ofPred_eq, mem_univ, iff_true]
          exact h
        rw [h2, probReal_univ, show t = 1 by linarith]
        simp
      · have h2 : {ω : Unit | t ≤ 1} = ∅ := by
          ext ω
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact h
        rw [h2, measureReal_empty]
        positivity)
    (integrable_const _)

end PercLib.Analysis
