/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Source motivation: T. Hutchcroft, arXiv:2008.11197v2,
§2 (consequences of universal tightness), and the wiki statements MJEP, 7VCS and DEZI. No source
text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Percolation.Bond.WindowPartition
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Window tails with damping, fractional moments, and exponent relations

* MJEP, `law_le_clusterIntersection_le_damped` and `lintegral_rpow_clusterIntersection_le`:
  by universal tightness, under a window tail `P(n ≤ X) ≤ A n^(-θ)` (`0 ≤ θ < 1`),
  `P(n ≤ X) ≤ e A (18/n)^θ e^(-n/(18M))` for `n ≥ 1`, and for real `p > θ`
  `E X^p ≤ e A 18^p p Γ(p-θ) M^(p-θ)`.
* 7VCS, `dimension_bounds_of_hyperscaling`: exponent inequalities from the WRHL bounds,
  for real functions of `R → ∞`.
* DEZI, `exponent_relations`: `α = 2 d_f + κ - d` and `d_f/δ = d - d_f - κ > 0` from
  two-sided power bounds, for real functions of `r → ∞`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### MJEP: damped window tails -/

/-- `x^θ ≤ e^x` for `x ≥ 0` and `0 ≤ θ ≤ 1`. -/
theorem rpow_le_exp_self {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ^ θ ≤ Real.exp x := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_one hx h hθ0).trans (Real.one_le_exp hx)
  · calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hθ1
      _ = x := Real.rpow_one x
      _ ≤ x + 1 := by linarith
      _ ≤ Real.exp x := Real.add_one_le_exp x

/-- **Tail.** By universal tightness, if `P(n ≤ X_u) ≤ A n^(-θ)` for all
`n ≥ 1`, with `A ≥ 0` and `0 ≤ θ < 1`, then for `n ≥ 1`
`P(n ≤ X_u) ≤ e A (18/n)^θ e^(-n/(18M))`, `M = tightnessScale q Λ`. -/
theorem law_le_clusterIntersection_le_damped [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ n : ℕ, 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ)))
    (n : ℕ) (hn : 1 ≤ n) :
    law q {ω | n ≤ clusterIntersection Λ ω u} ≤
      ENNReal.ofReal (Real.exp 1 * A * (18 / (n : ℝ)) ^ θ *
        Real.exp (-(n : ℝ) / (18 * tightnessScale q Λ))) := by
  set M := tightnessScale q Λ with hMdef
  have hM2 : 2 ≤ M := two_le_tightnessScale q hΛ
  have hM0 : (0 : ℝ) < M := by have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
                               linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set y : ℝ := (n : ℝ) / (18 * M) with hy
  have hy0 : 0 ≤ y := by positivity
  have h18 : (18 / (n : ℝ)) ^ θ = 18 ^ θ / (n : ℝ) ^ θ :=
    Real.div_rpow (by norm_num) hn0.le θ
  have hnθ : 0 < (n : ℝ) ^ θ := Real.rpow_pos_of_pos hn0 θ
  have hexpy : Real.exp (-(n : ℝ) / (18 * M)) = Real.exp (-y) := by rw [hy, neg_div]
  rw [hexpy]
  rcases Nat.lt_or_ge n M with hlt | hge
  · -- below the scale: the given tail suffices
    refine (htail n hn).trans (ENNReal.ofReal_le_ofReal ?_)
    have hy1 : y ≤ 1 := by
      rw [hy, div_le_one (by positivity)]
      have : (n : ℝ) < M := by exact_mod_cast hlt
      linarith
    have h1 : 1 ≤ Real.exp 1 * Real.exp (-y) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h18' : 1 ≤ (18 : ℝ) ^ θ := Real.one_le_rpow (by norm_num) hθ0
    rw [Real.rpow_neg hn0.le, h18]
    calc A * ((n : ℝ) ^ θ)⁻¹ = A * 1 * 1 / (n : ℝ) ^ θ := by ring
      _ ≤ A * (Real.exp 1 * Real.exp (-y)) * (18 : ℝ) ^ θ / (n : ℝ) ^ θ := by gcongr
      _ = _ := by ring
  · -- above the scale: rooted damping at `a = n / M`
    set a : ℝ := (n : ℝ) / M with ha
    have ha1 : 1 ≤ a := by
      rw [ha, le_div_iff₀ hM0, one_mul]; exact_mod_cast hge
    have hev : {ω : Config V | n ≤ clusterIntersection Λ ω u} =
        {ω | a * (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, ha, div_mul_cancel₀ _ hM0.ne']
      constructor
      · intro h; exact_mod_cast h
      · intro h; exact_mod_cast h
    rw [hev]
    refine (law_mul_tightnessScale_le_clusterIntersection_le q hΛ u ha1).trans ?_
    have hMt := htail M (by omega)
    calc ENNReal.ofReal (Real.exp 1) * law q {ω | M ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9))
        ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (A * (M : ℝ) ^ (-θ)) *
          ENNReal.ofReal (Real.exp (-a / 9)) := by gcongr
      _ = ENNReal.ofReal (Real.exp 1 * (A * (M : ℝ) ^ (-θ)) * Real.exp (-a / 9)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg he.le (by positivity)), ENNReal.ofReal_mul he.le]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          -- `(n/(18M))^θ ≤ e^(n/(18M))`
          have hkey := rpow_le_exp_self hy0 hθ0 hθ1.le
          have hsplit : y ^ θ = (n : ℝ) ^ θ / (18 ^ θ * (M : ℝ) ^ θ) := by
            rw [hy, Real.div_rpow hn0.le (by positivity), Real.mul_rpow (by norm_num) hM0.le]
          have hMθ : 0 < (M : ℝ) ^ θ := Real.rpow_pos_of_pos hM0 θ
          have h18θ : 0 < (18 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
          rw [hsplit, div_le_iff₀ (by positivity)] at hkey
          have ha9 : Real.exp (-a / 9) = Real.exp (-y) * Real.exp (-y) := by
            rw [← Real.exp_add, ha, hy]; congr 1; field_simp; ring
          rw [ha9, Real.rpow_neg hM0.le, h18]
          have hey : 0 < Real.exp (-y) := Real.exp_pos _
          have hyy : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
          -- multiply out
          rw [show Real.exp 1 * (A * ((M : ℝ) ^ θ)⁻¹) * (Real.exp (-y) * Real.exp (-y)) =
              Real.exp 1 * A * Real.exp (-y) * (Real.exp (-y) / (M : ℝ) ^ θ) by
                field_simp,
            show Real.exp 1 * A * (18 ^ θ / (n : ℝ) ^ θ) * Real.exp (-y) =
              Real.exp 1 * A * Real.exp (-y) * (18 ^ θ / (n : ℝ) ^ θ) by ring]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ hMθ hnθ]
          calc Real.exp (-y) * (n : ℝ) ^ θ ≤ Real.exp (-y) * (Real.exp y * (18 ^ θ * M ^ θ)) :=
                mul_le_mul_of_nonneg_left hkey hey.le
            _ = 18 ^ θ * (M : ℝ) ^ θ := by rw [← mul_assoc, mul_comm (Real.exp (-y)), hyy,
                one_mul]

/-- **Fractional moments.** Under the hypotheses of
`law_le_clusterIntersection_le_damped`, for every real `p > θ`,
`E X_u^p ≤ e A 18^p p Γ(p-θ) M^(p-θ)`. -/
theorem lintegral_rpow_clusterIntersection_le [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ n : ℕ, 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ)))
    {p : ℝ} (hp : θ < p) :
    ∫⁻ ω, ENNReal.ofReal ((clusterIntersection Λ ω u : ℝ) ^ p) ∂(law q) ≤
      ENNReal.ofReal (Real.exp 1 * A * 18 ^ p * p * Real.Gamma (p - θ) *
        (tightnessScale q Λ : ℝ) ^ (p - θ)) := by
  set M := tightnessScale q Λ with hMdef
  have hM2 : 2 ≤ M := two_le_tightnessScale q hΛ
  have hM0 : (0 : ℝ) < M := by have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
                               linarith
  have hp0 : 0 < p := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set a : ℝ := p - θ with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set r : ℝ := 1 / (18 * M) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hmeas : Measurable fun ω : Config V => (clusterIntersection Λ ω u : ℝ) :=
    measurable_from_nat.comp (measurable_clusterIntersection Λ u)
  rw [lintegral_rpow_eq_lintegral_meas_le_mul (law q)
    (Filter.Eventually.of_forall fun ω => by simp) hmeas.aemeasurable hp0]
  set c : ℝ := Real.exp 1 * A * 18 ^ θ with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set g : ℝ → ℝ := fun t => t ^ (a - 1) * Real.exp (-(r * t)) with hg
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      law q {ω | t ≤ (clusterIntersection Λ ω u : ℝ)} * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal c * ENNReal.ofReal (g t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    set n := ⌈t⌉₊ with hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 ht0))
    have htn : t ≤ n := Nat.le_ceil t
    have hev : {ω : Config V | t ≤ (clusterIntersection Λ ω u : ℝ)} =
        {ω | n ≤ clusterIntersection Λ ω u} := by
      ext ω; simp only [Set.mem_ofPred_eq, hn, Nat.ceil_le]
    rw [hev]
    have h1 := law_le_clusterIntersection_le_damped q hΛ u hA hθ0 hθ1 htail n hn1
    refine (mul_le_mul' h1 le_rfl).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn0 : (0 : ℝ) < n := by linarith
    have h18 : (18 / (n : ℝ)) ^ θ ≤ 18 ^ θ * t ^ (-θ) := by
      rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv, ← Real.div_rpow (by norm_num) ht0.le]
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left (by norm_num) ht0 htn)
        hθ0
    have hexp : Real.exp (-(n : ℝ) / (18 * M)) ≤ Real.exp (-(r * t)) := by
      rw [Real.exp_le_exp, hr, neg_div, neg_le_neg_iff]
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right htn (by positivity)
    have hpow : t ^ (-θ) * t ^ (p - 1) = t ^ (a - 1) := by
      rw [← Real.rpow_add ht0, ha]; ring_nf
    calc Real.exp 1 * A * (18 / (n : ℝ)) ^ θ * Real.exp (-(n : ℝ) / (18 * M)) * t ^ (p - 1)
        ≤ Real.exp 1 * A * (18 ^ θ * t ^ (-θ)) * Real.exp (-(r * t)) * t ^ (p - 1) := by
          gcongr
      _ = c * g t := by rw [hc, hg]; simp only; rw [← hpow]; ring
  refine (mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioi hbound)).trans_eq ?_
  have hint : IntegrableOn g (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := a - 1) (p := 1) (b := r)
      (by linarith) zero_lt_one hr0).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hg, Real.rpow_one, neg_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : (0 : ℝ) < t) =>
        mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le),
    hg, Real.integral_rpow_mul_exp_neg_mul_Ioi ha0 hr0,
    ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hp0.le]
  congr 1
  have h1r : 1 / r = 18 * M := by rw [hr, one_div_one_div]
  rw [h1r, Real.mul_rpow (by norm_num) hM0.le, hc]
  have h18 : (18 : ℝ) ^ θ * 18 ^ a = 18 ^ p := by
    rw [← Real.rpow_add (by norm_num), ha]; ring_nf
  calc p * (Real.exp 1 * A * 18 ^ θ * (18 ^ a * (M : ℝ) ^ a * Real.Gamma a))
      = Real.exp 1 * A * ((18 : ℝ) ^ θ * 18 ^ a) * p * Real.Gamma a * (M : ℝ) ^ a := by ring
    _ = _ := by rw [h18]

/-! ### 7VCS: exponents from the WRHL inequalities -/

/-- If `0 < x ≤ C y^k` eventually, `log x / log R → a` and `log y / log R → b`, then
`a ≤ k b`. -/
theorem exponent_le_of_le_rpow {x y : ℝ → ℝ} {a b k C : ℝ}
    (hpos : ∀ᶠ R in atTop, 0 < x R ∧ 0 < y R) (hle : ∀ᶠ R in atTop, x R ≤ C * y R ^ k)
    (hx : Tendsto (fun R => Real.log (x R) / Real.log R) atTop (𝓝 a))
    (hy : Tendsto (fun R => Real.log (y R) / Real.log R) atTop (𝓝 b)) :
    a ≤ k * b := by
  obtain ⟨R₀, hR₀⟩ := (hpos.and hle).exists
  have hC : 0 < C := by
    by_contra hC
    have : C * y R₀ ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hC) (Real.rpow_nonneg hR₀.1.2.le _)
    linarith [hR₀.1.1, hR₀.2]
  have hlim : Tendsto (fun R => Real.log C / Real.log R + k * (Real.log (y R) / Real.log R))
      atTop (𝓝 (0 + k * b)) :=
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add (hy.const_mul k)
  rw [zero_add] at hlim
  refine le_of_tendsto_of_tendsto hx hlim ?_
  filter_upwards [hpos, hle, eventually_gt_atTop 1] with R hp hl hR
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hlog : Real.log (x R) ≤ Real.log C + k * Real.log (y R) := by
    calc Real.log (x R) ≤ Real.log (C * y R ^ k) := Real.log_le_log hp.1 hl
      _ = Real.log C + k * Real.log (y R) := by
          rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hp.2 k).ne', Real.log_rpow hp.2]
  rw [← mul_div_assoc, ← add_div, div_le_div_iff_of_pos_right hlogR]
  exact hlog

/-- **Hyperscaling exponent inequalities.** Let `N_R, M_R, s_R > 0` with `log N_R / log R → d > 0`,
`log M_R / log R → d_f` and `log s_R / log R → s`. If for some `δ > 1` and constants
`C₁, C₂`, eventually `M_R ≤ C₁ N_R^(δ/(δ+1))` and `s_R / N_R ≤ C₂ N_R^(-2/(δ+1))`, then
`d_f / d ≤ δ/(δ+1)` and `s ≤ d (δ-1)/(δ+1)`. -/
theorem dimension_bounds_of_hyperscaling {N Mr s : ℝ → ℝ} {d df σ δ C₁ C₂ : ℝ}
    (hd : 0 < d) (hδ : 1 < δ)
    (hpos : ∀ᶠ R in atTop, 0 < N R ∧ 0 < Mr R ∧ 0 < s R)
    (hN : Tendsto (fun R => Real.log (N R) / Real.log R) atTop (𝓝 d))
    (hM : Tendsto (fun R => Real.log (Mr R) / Real.log R) atTop (𝓝 df))
    (hs : Tendsto (fun R => Real.log (s R) / Real.log R) atTop (𝓝 σ))
    (h1 : ∀ᶠ R in atTop, Mr R ≤ C₁ * N R ^ (δ / (δ + 1)))
    (h2 : ∀ᶠ R in atTop, s R / N R ≤ C₂ * N R ^ (-2 / (δ + 1))) :
    df / d ≤ δ / (δ + 1) ∧ σ ≤ d * (δ - 1) / (δ + 1) := by
  constructor
  · have h := exponent_le_of_le_rpow (hpos.mono fun R h => ⟨h.2.1, h.1⟩) h1 hM hN
    rw [div_le_iff₀ hd]; linarith
  · have h2' : ∀ᶠ R in atTop, s R ≤ C₂ * N R ^ ((δ - 1) / (δ + 1)) := by
      filter_upwards [hpos, h2] with R hp hl
      rw [div_le_iff₀ hp.1] at hl
      have he : (δ - 1) / (δ + 1) = -2 / (δ + 1) + 1 := by field_simp; ring
      rw [he, Real.rpow_add_one hp.1.ne']
      linarith
    have h := exponent_le_of_le_rpow (hpos.mono fun R h => ⟨h.2.2, h.1⟩) h2' hs hN
    calc σ ≤ (δ - 1) / (δ + 1) * d := h
      _ = d * (δ - 1) / (δ + 1) := by ring

/-! ### DEZI: exponent relations from two-sided power bounds -/

/-- Two-sided power bounds give a bounded logarithmic error. -/
theorem abs_log_sub_le_of_sandwich {K : ℝ → ℝ} {a c C : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r in atTop, c * r ^ a ≤ K r ∧ K r ≤ C * r ^ a) :
    ∃ B, ∀ᶠ r in atTop, 0 < K r ∧ |Real.log (K r) - a * Real.log r| ≤ B := by
  obtain ⟨r₀, hr₀⟩ := (h.and (eventually_gt_atTop 0)).exists
  have hcC : c ≤ C := by
    have hp := Real.rpow_pos_of_pos hr₀.2 a
    nlinarith [hr₀.1.1, hr₀.1.2]
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  refine ⟨|Real.log c| + |Real.log C|, ?_⟩
  filter_upwards [h, eventually_gt_atTop 0] with r hr hr0
  have hp := Real.rpow_pos_of_pos hr0 a
  have hK : 0 < K r := lt_of_lt_of_le (by positivity) hr.1
  refine ⟨hK, ?_⟩
  have hlo : Real.log c + a * Real.log r ≤ Real.log (K r) := by
    calc Real.log c + a * Real.log r = Real.log (c * r ^ a) := by
          rw [Real.log_mul hc.ne' hp.ne', Real.log_rpow hr0]
      _ ≤ Real.log (K r) := Real.log_le_log (by positivity) hr.1
  have hhi : Real.log (K r) ≤ Real.log C + a * Real.log r := by
    calc Real.log (K r) ≤ Real.log (C * r ^ a) := Real.log_le_log hK hr.2
      _ = Real.log C + a * Real.log r := by
          rw [Real.log_mul hC.ne' hp.ne', Real.log_rpow hr0]
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log C),
    abs_nonneg (Real.log c), abs_nonneg (Real.log C), le_abs_self (Real.log c),
    neg_abs_le (Real.log C)]

/-- Two logarithmic sandwiches of one function have the same exponent. -/
theorem exponent_eq_of_abs_log_le {f : ℝ → ℝ} {a b B B' : ℝ}
    (ha : ∀ᶠ r in atTop, |f r - a * Real.log r| ≤ B)
    (hb : ∀ᶠ r in atTop, |f r - b * Real.log r| ≤ B') : a = b := by
  by_contra hab
  have hpos : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
  have hlog := Real.tendsto_log_atTop.eventually_gt_atTop ((B + B' + 1) / |a - b|)
  obtain ⟨r, h1, h2, h3⟩ := (ha.and (hb.and hlog)).exists
  have hdiff : |(a - b) * Real.log r| ≤ B + B' := by
    calc |(a - b) * Real.log r| = |(f r - b * Real.log r) - (f r - a * Real.log r)| := by
          congr 1; ring
      _ ≤ |f r - b * Real.log r| + |f r - a * Real.log r| := abs_sub _ _
      _ ≤ B + B' := by linarith
  rw [div_lt_iff₀ hpos] at h3
  have hlogpos : 0 < Real.log r := by
    have : 0 ≤ B + B' := le_trans (abs_nonneg _) hdiff
    nlinarith
  rw [abs_mul, abs_of_pos hlogpos] at hdiff
  nlinarith

/-- **Exponent relations.** Real functions of `r → ∞` (all relations eventually in `r`, with
positive lower constants): `|Λ_r| ≍ r^d`, `v_r ≍ r^(d_f)`, `E N_r ≍ r^κ`, `E ∑ S² ≍ v_r² E N_r`,
`E X_r ≍ r^α`, the sampled-root identity `E X_r = E ∑ S² / |Λ_r|`, `P(Z ≥ n) ≍ n^(-1/δ)` for
`n ≥ 1`, and `P(Z ≥ ⌈v_r⌉) ≍ v_r E N_r / |Λ_r|`. If `d_f > 0` and `δ > 0`, then `α = 2 d_f + κ - d`
and `d_f / δ = d - d_f - κ > 0`. -/
theorem exponent_relations {Λ v EN ES EX : ℝ → ℝ} {F : ℕ → ℝ} {d df κ α δ : ℝ}
    (hdf : 0 < df) (hδ : 0 < δ)
    (hΛ : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ d ≤ Λ r ∧ Λ r ≤ C * r ^ d)
    (hv : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ df ≤ v r ∧ v r ≤ C * r ^ df)
    (hEN : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ κ ≤ EN r ∧ EN r ≤ C * r ^ κ)
    (hES : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c * (v r ^ 2 * EN r) ≤ ES r ∧ ES r ≤ C * (v r ^ 2 * EN r))
    (hEX : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ α ≤ EX r ∧ EX r ≤ C * r ^ α)
    (hOB : ∀ᶠ r in atTop, EX r = ES r / Λ r)
    (hF : ∃ c C : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (n : ℝ) ^ (-1 / δ) ≤ F n ∧ F n ≤ C * (n : ℝ) ^ (-1 / δ))
    (hFv : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c * (v r * EN r / Λ r) ≤ F ⌈v r⌉₊ ∧ F ⌈v r⌉₊ ≤ C * (v r * EN r / Λ r)) :
    α = 2 * df + κ - d ∧ df / δ = d - df - κ ∧ 0 < d - df - κ := by
  obtain ⟨c₁, C₁, hc₁, h₁⟩ := hΛ
  obtain ⟨c₂, C₂, hc₂, h₂⟩ := hv
  obtain ⟨c₃, C₃, hc₃, h₃⟩ := hEN
  obtain ⟨c₄, C₄, hc₄, h₄⟩ := hES
  obtain ⟨c₅, C₅, hc₅, h₅⟩ := hEX
  obtain ⟨c₇, C₇, hc₇, h₇⟩ := hF
  obtain ⟨c₈, C₈, hc₈, h₈⟩ := hFv
  obtain ⟨B₁, hB₁⟩ := abs_log_sub_le_of_sandwich hc₁ h₁
  obtain ⟨B₂, hB₂⟩ := abs_log_sub_le_of_sandwich hc₂ h₂
  obtain ⟨B₃, hB₃⟩ := abs_log_sub_le_of_sandwich hc₃ h₃
  obtain ⟨B₅, hB₅⟩ := abs_log_sub_le_of_sandwich hc₅ h₅
  -- the sandwich of `E ∑ S²` in logarithmic form
  have hC₇ : 0 < C₇ := by
    have h := h₇ 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    linarith
  have hlogS : ∀ {K : ℝ → ℝ} {G : ℝ → ℝ} {c C : ℝ}, 0 < c →
      (∀ᶠ r in atTop, c * G r ≤ K r ∧ K r ≤ C * G r) → (∀ᶠ r in atTop, 0 < G r) →
      ∀ᶠ r in atTop, 0 < K r ∧ |Real.log (K r) - Real.log (G r)| ≤ |Real.log c| + |Real.log C| := by
    intro K G c C hc h hG
    obtain ⟨r₀, hr₀⟩ := (h.and hG).exists
    have hC : 0 < C := by
      by_contra hC
      have h0 : C * G r₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hC) hr₀.2.le
      linarith [hr₀.1.1, hr₀.1.2, mul_pos hc hr₀.2]
    filter_upwards [h, hG] with r hr hGr
    have hK : 0 < K r := lt_of_lt_of_le (mul_pos hc hGr) hr.1
    refine ⟨hK, ?_⟩
    have hlo : Real.log c + Real.log (G r) ≤ Real.log (K r) := by
      rw [← Real.log_mul hc.ne' hGr.ne']; exact Real.log_le_log (mul_pos hc hGr) hr.1
    have hhi : Real.log (K r) ≤ Real.log C + Real.log (G r) := by
      rw [← Real.log_mul hC.ne' hGr.ne']; exact Real.log_le_log hK hr.2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log C),
      abs_nonneg (Real.log c), abs_nonneg (Real.log C)]
  have hvEN : ∀ᶠ r in atTop, 0 < v r ^ 2 * EN r := by
    filter_upwards [hB₂, hB₃] with r h2 h3
    exact mul_pos (pow_pos h2.1 2) h3.1
  have hB₄ := hlogS hc₄ h₄ hvEN
  have hratio : ∀ᶠ r in atTop, 0 < v r * EN r / Λ r := by
    filter_upwards [hB₁, hB₂, hB₃] with r h1 h2 h3
    exact div_pos (mul_pos h2.1 h3.1) h1.1
  have hB₈ := hlogS hc₈ h₈ hratio
  -- `α`
  have hα : α = 2 * df + κ - d := by
    refine exponent_eq_of_abs_log_le (f := fun r => Real.log (EX r)) (hB₅.mono fun r h => h.2)
      (B' := (|Real.log c₄| + |Real.log C₄|) + 2 * B₂ + B₃ + B₁) ?_
    filter_upwards [hB₁, hB₂, hB₃, hB₄, hOB] with r h1 h2 h3 h4 hob
    show |Real.log (EX r) - (2 * df + κ - d) * Real.log r| ≤ _
    rw [hob, Real.log_div h4.1.ne' h1.1.ne',
      show (2 * df + κ - d) * Real.log r =
        2 * (df * Real.log r) + κ * Real.log r - d * Real.log r by ring]
    rw [Real.log_mul (pow_pos h2.1 2).ne' h3.1.ne', Real.log_pow] at h4
    obtain ⟨-, g1⟩ := h1
    obtain ⟨-, g2⟩ := h2
    obtain ⟨-, g3⟩ := h3
    obtain ⟨-, g4⟩ := h4
    rw [abs_le] at g1 g2 g3 g4 ⊢
    push_cast at g4
    constructor <;> linarith
  -- `d_f / δ`
  have hv1 : ∀ᶠ r in atTop, 1 ≤ v r := by
    have hlim : Tendsto (fun r : ℝ => c₂ * r ^ df) atTop atTop :=
      (tendsto_rpow_atTop hdf).const_mul_atTop hc₂
    filter_upwards [hlim.eventually_ge_atTop 1, h₂] with r h1 h2
    linarith [h2.1]
  have hceil : ∀ᶠ r in atTop, 1 ≤ ⌈v r⌉₊ ∧
      |Real.log (⌈v r⌉₊ : ℝ) - Real.log (v r)| ≤ Real.log 2 := by
    filter_upwards [hv1] with r hv
    have hv0 : 0 < v r := by linarith
    have hc1 : (v r) ≤ ⌈v r⌉₊ := Nat.le_ceil _
    have hc2 : (⌈v r⌉₊ : ℝ) ≤ 2 * v r := by
      have := Nat.ceil_lt_add_one hv0.le; linarith
    refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hv0)), ?_⟩
    rw [abs_le]
    constructor
    · linarith [Real.log_le_log hv0 hc1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    · have := Real.log_le_log (by linarith) hc2
      rw [Real.log_mul (by norm_num) hv0.ne'] at this
      linarith
  have hF7 : ∀ n : ℕ, 1 ≤ n →
      |Real.log (F n) - (-1 / δ) * Real.log n| ≤ |Real.log c₇| + |Real.log C₇| := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hp := Real.rpow_pos_of_pos hn0 (-1 / δ)
    have hFn : 0 < F n := lt_of_lt_of_le (mul_pos hc₇ hp) (h₇ n hn).1
    have hlo : Real.log c₇ + (-1 / δ) * Real.log n ≤ Real.log (F n) := by
      rw [← Real.log_rpow hn0, ← Real.log_mul hc₇.ne' hp.ne']
      exact Real.log_le_log (mul_pos hc₇ hp) (h₇ n hn).1
    have hhi : Real.log (F n) ≤ Real.log C₇ + (-1 / δ) * Real.log n := by
      rw [← Real.log_rpow hn0, ← Real.log_mul hC₇.ne' hp.ne']
      exact Real.log_le_log hFn (h₇ n hn).2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log c₇), le_abs_self (Real.log C₇),
      abs_nonneg (Real.log c₇), abs_nonneg (Real.log C₇)]
  have hδ' : -df / δ = df + κ - d := by
    refine exponent_eq_of_abs_log_le (f := fun r => Real.log (F ⌈v r⌉₊))
      (B := |Real.log c₇| + |Real.log C₇| + |1 / δ| * Real.log 2 + |1 / δ| * B₂)
      (B' := (|Real.log c₈| + |Real.log C₈|) + B₂ + B₃ + B₁) ?_ ?_
    · filter_upwards [hceil, hB₂] with r hc h2
      have h7 := hF7 _ hc.1
      have hδinv : 0 ≤ 1 / δ := by positivity
      have e1 : |(-1 / δ) * (Real.log (⌈v r⌉₊ : ℝ) - Real.log (v r))| ≤ |1 / δ| * Real.log 2 := by
        rw [abs_mul, show |(-1 / δ)| = |1 / δ| by rw [neg_div, abs_neg]]
        exact mul_le_mul_of_nonneg_left hc.2 (abs_nonneg _)
      have e2 : |(-1 / δ) * (Real.log (v r) - df * Real.log r)| ≤ |1 / δ| * B₂ := by
        rw [abs_mul, show |(-1 / δ)| = |1 / δ| by rw [neg_div, abs_neg]]
        exact mul_le_mul_of_nonneg_left h2.2 (abs_nonneg _)
      calc |Real.log (F ⌈v r⌉₊) - -df / δ * Real.log r|
          = |(Real.log (F ⌈v r⌉₊) - (-1 / δ) * Real.log (⌈v r⌉₊ : ℝ)) +
              (-1 / δ) * (Real.log (⌈v r⌉₊ : ℝ) - Real.log (v r)) +
              (-1 / δ) * (Real.log (v r) - df * Real.log r)| := by congr 1; ring
        _ ≤ |Real.log (F ⌈v r⌉₊) - (-1 / δ) * Real.log (⌈v r⌉₊ : ℝ)| +
              |(-1 / δ) * (Real.log (⌈v r⌉₊ : ℝ) - Real.log (v r))| +
              |(-1 / δ) * (Real.log (v r) - df * Real.log r)| := abs_add_three _ _ _
        _ ≤ _ := by linarith
    · filter_upwards [hB₁, hB₂, hB₃, hB₈] with r h1 h2 h3 h8
      rw [Real.log_div (mul_pos h2.1 h3.1).ne' h1.1.ne', Real.log_mul h2.1.ne' h3.1.ne'] at h8
      rw [show (df + κ - d) * Real.log r =
        df * Real.log r + κ * Real.log r - d * Real.log r by ring]
      obtain ⟨-, g1⟩ := h1
      obtain ⟨-, g2⟩ := h2
      obtain ⟨-, g3⟩ := h3
      obtain ⟨-, g8⟩ := h8
      rw [abs_le] at g1 g2 g3 g8 ⊢
      constructor <;> linarith
  refine ⟨hα, ?_, ?_⟩
  · have : df / δ = -(-df / δ) := by ring
    rw [this, hδ']; ring
  · have : 0 < df / δ := div_pos hdf hδ
    have h' : df / δ = -(-df / δ) := by ring
    rw [h', hδ'] at this
    linarith

/-! ### Non-vacuity -/

/-- The window tail with `A = 1`, `θ = 0` holds for every window and root. -/
theorem window_tail_one [Countable V] (q : Sym2 V → unitInterval) (Λ : Finset V) (u : V)
    (n : ℕ) (_hn : 1 ≤ n) :
    law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (1 * (n : ℝ) ^ (-(0 : ℝ))) := by
  simp only [neg_zero, Real.rpow_zero, mul_one, ENNReal.ofReal_one]
  exact prob_le_one

/-- The window-tail damping on `Unit` with `Λ = {()}`, `A = 1`, `θ = 0`: every hypothesis holds. -/
example (q : Sym2 Unit → unitInterval) (n : ℕ) (hn : 1 ≤ n) :
    law q {ω | n ≤ clusterIntersection {()} ω ()} ≤
      ENNReal.ofReal (Real.exp 1 * 1 * (18 / (n : ℝ)) ^ (0 : ℝ) *
        Real.exp (-(n : ℝ) / (18 * tightnessScale q {()}))) :=
  law_le_clusterIntersection_le_damped q (Finset.singleton_nonempty _)
    () zero_le_one le_rfl zero_lt_one (window_tail_one q _ ()) n hn

example (q : Sym2 Unit → unitInterval) :
    ∫⁻ ω, ENNReal.ofReal ((clusterIntersection {()} ω () : ℝ) ^ (2 : ℝ)) ∂(law q) ≤
      ENNReal.ofReal (Real.exp 1 * 1 * 18 ^ (2 : ℝ) * 2 * Real.Gamma (2 - 0) *
        (tightnessScale q {()} : ℝ) ^ ((2 : ℝ) - 0)) :=
  lintegral_rpow_clusterIntersection_le q
    (Finset.singleton_nonempty _) () zero_le_one le_rfl zero_lt_one (window_tail_one q _ ())
    (by norm_num)

/-- `log (R^a) / log R → a`. -/
theorem tendsto_log_rpow_div_log (a : ℝ) :
    Tendsto (fun R : ℝ => Real.log (R ^ a) / Real.log R) atTop (𝓝 a) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  rw [Real.log_rpow (by linarith), mul_div_assoc, div_self (Real.log_pos hR).ne', mul_one]

/-- `dimension_bounds_of_hyperscaling` with equality: `N_R = R`, `M_R = R^(2/3)`, `s_R = R^(1/3)`,
`δ = 2`. -/
example : (2 / 3 : ℝ) / 1 ≤ 2 / (2 + 1) ∧ (1 / 3 : ℝ) ≤ 1 * (2 - 1) / (2 + 1) :=
  dimension_bounds_of_hyperscaling (N := fun R => R ^ (1 : ℝ)) (Mr := fun R => R ^ (2 / 3 : ℝ))
    (s := fun R => R ^ (1 / 3 : ℝ)) (C₁ := 1) (C₂ := 1) one_pos one_lt_two
    (by filter_upwards [eventually_gt_atTop 0] with R hR
        exact ⟨Real.rpow_pos_of_pos hR _, Real.rpow_pos_of_pos hR _,
          Real.rpow_pos_of_pos hR _⟩)
    (tendsto_log_rpow_div_log 1) (tendsto_log_rpow_div_log _) (tendsto_log_rpow_div_log _)
    (Eventually.of_forall fun R => by
      rw [Real.rpow_one, one_mul]; norm_num)
    (by filter_upwards [eventually_gt_atTop 0] with R hR
        rw [Real.rpow_one, one_mul, div_eq_mul_inv, ← Real.rpow_neg_one,
          ← Real.rpow_add hR]
        norm_num)

/-- `exponent_relations` with pure powers: `|Λ_r| = r^3`, `v_r = r^2`, `E N_r = 1`, `E ∑ S² = r^4`,
`E X_r = r^4 / r^3`, `P(Z ≥ n) = n^(-1/2)`; then `α = 1`, `d_f/δ = 1 = d - d_f - κ`. -/
example : (1 : ℝ) = 2 * 2 + 0 - 3 ∧ (2 : ℝ) / 2 = 3 - 2 - 0 ∧ (0 : ℝ) < 3 - 2 - 0 := by
  refine exponent_relations (Λ := fun r => r ^ (3 : ℝ)) (v := fun r => r ^ (2 : ℝ))
    (EN := fun _ => 1) (ES := fun r => (r ^ (2 : ℝ)) ^ 2 * 1)
    (EX := fun r => (r ^ (2 : ℝ)) ^ 2 * 1 / r ^ (3 : ℝ)) (F := fun n => (n : ℝ) ^ (-1 / 2 : ℝ))
    two_pos two_pos ⟨1, 1, one_pos, Eventually.of_forall fun r => by simp⟩
    ⟨1, 1, one_pos, Eventually.of_forall fun r => by simp⟩
    ⟨1, 1, one_pos, Eventually.of_forall fun r => by simp⟩
    ⟨1, 1, one_pos, Eventually.of_forall fun r => by simp⟩
    ⟨1, 1, one_pos, ?_⟩ (Eventually.of_forall fun r => rfl)
    ⟨1, 1, one_pos, fun n _ => by simp⟩ ⟨1 / 2, 1, by norm_num, ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have h : (r ^ (2 : ℝ)) ^ 2 * 1 / r ^ (3 : ℝ) = r ^ (1 : ℝ) := by
      rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_sub hr]
      norm_num
    simp only [h, one_mul, le_refl, and_self]
  · filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : 0 < r := by linarith
    have hv : r ^ (2 : ℝ) * 1 / r ^ (3 : ℝ) = (r ^ (2 : ℝ)) ^ (-1 / 2 : ℝ) := by
      rw [mul_one, ← Real.rpow_sub hr0, ← Real.rpow_mul hr0.le]; norm_num
    have hv1 : 1 ≤ r ^ (2 : ℝ) := Real.one_le_rpow hr (by norm_num)
    have hc1 : r ^ (2 : ℝ) ≤ (⌈r ^ (2 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have hc2 : (⌈r ^ (2 : ℝ)⌉₊ : ℝ) ≤ 2 * r ^ (2 : ℝ) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ r ^ (2 : ℝ) by linarith); linarith
    change 1 / 2 * (r ^ (2 : ℝ) * 1 / r ^ (3 : ℝ)) ≤ (⌈r ^ (2 : ℝ)⌉₊ : ℝ) ^ (-1 / 2 : ℝ) ∧
      (⌈r ^ (2 : ℝ)⌉₊ : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 * (r ^ (2 : ℝ) * 1 / r ^ (3 : ℝ))
    rw [hv]
    constructor
    · calc 1 / 2 * (r ^ (2 : ℝ)) ^ (-1 / 2 : ℝ)
          ≤ (2 : ℝ) ^ (-1 / 2 : ℝ) * (r ^ (2 : ℝ)) ^ (-1 / 2 : ℝ) := by
            gcongr
            rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
              ← one_div, one_div_le_one_div (by norm_num) (by positivity)]
            calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
        _ = (2 * r ^ (2 : ℝ)) ^ (-1 / 2 : ℝ) := (Real.mul_rpow (by norm_num) (by positivity)).symm
        _ ≤ (⌈r ^ (2 : ℝ)⌉₊ : ℝ) ^ (-1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hc2 (by norm_num)
    · rw [one_mul]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hc1 (by norm_num)

end PercLib.Percolation.Bond
