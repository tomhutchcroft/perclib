/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied and no definition is added.
Mathematical reference: the Fourier proof of the Green, bubble and triangle thresholds for
lazy nearest-neighbour walk on `ℤ^d` (standard; see e.g. G. F. Lawler and V. Limic, *Random
Walk: A Modern Introduction*, Chapter 2).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import PercLib.Analysis.HomogeneousBallIntegrals
public import PercLib.Analysis.DiscreteConvolution

/-!
# Green, bubble and triangle thresholds for lazy nearest-neighbour walk

For lazy nearest-neighbour walk on `ℤ^d` (stay put with probability `1/2`, each of the `2d`
unit steps with probability `1/(4d)`), with Green function `G(u) = ∑ₙ Pⁿ(0,u)` in `ℝ≥0∞`,
`G(0) < ∞ ↔ 2 < d`, `∑ᵤ G(u)² < ∞ ↔ 4 < d` and `∑ᵤ,ᵥ G(u) G(v-u) G(v) < ∞ ↔ 6 < d`.

The proof is Fourier analytic. The `n`-step return probability is a finite sum over step
sequences, and the orthogonality of the characters `k ↦ exp(i k·x)` on the box `(-π, π)^d`
writes it as `(2π)^{-d} ∫ φ(k)^n dk`, with `φ(k) = 1/2 + (2d)⁻¹ ∑ⱼ cos kⱼ ∈ [0,1]`. Summing
the geometric series under the integral (Tonelli in `ℝ≥0∞`) gives
`(2π)^{-d} ∫ (1 - φ)^{-j}` for the three quantities (`j = 1, 2, 3`), and
`‖k‖²/(dπ²) ≤ 1 - φ(k) ≤ ‖k‖²/4` on the box reduces finiteness to that of
`∫_{‖k‖<1} ‖k‖^{-2j} dk`, which holds exactly when `2j < d`.

## Main results

* `lintegral_ball_rpow_neg_lt_top`, `lintegral_ball_rpow_neg_eq_top`: `∫_{‖k‖<R} ‖k‖^{-s}` is
  finite for `0 < s < d` and infinite for `s ≥ d` (sup norm on `Fin d → ℝ`).
* `lintegral_lazySymbol_lt_top_iff`: `∫_{(-π,π)^d} (1 - φ)^{-j} < ∞ ↔ 2j < d` for `j ≥ 1`.
* `integral_ball_exp_inner`: orthogonality of characters on `(-π, π)^d`.
* `integral_ball_pow_sum_exp`: the `N`-th power of the transform of a finite step
  distribution integrates to `(2π)^d` times the weight of the closed step sequences.
* `convPow_eq_sum_prod`, `convPow_add_of_rec`, `convPow_neg_of_rec`: additive convolution
  powers as sums over step sequences, and their semigroup and symmetry identities.
* `tsum_convPow_zero_eq_lintegral`, `tsum_sq_tsum_convPow_eq_lintegral`,
  `tsum_triangle_tsum_convPow_eq_lintegral`: Green, bubble and triangle sums as integrals.
* `lazyWalk_return_eq_lintegral`, `lazyWalk_green_lt_top_iff`, `lazyWalk_bubble_lt_top_iff`,
  `lazyWalk_triangle_lt_top_iff`: the lazy nearest-neighbour walk.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Module
open scoped ENNReal

namespace PercLib.Analysis

variable {d : ℕ}

/-! ### Radial integrals of `‖k‖^{-s}` -/

/-- `∫_{‖k‖<R} ‖k‖^{-s} dk < ∞` on `Fin d → ℝ` (sup norm) for `0 < s < d`. -/
theorem lintegral_ball_rpow_neg_lt_top (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    {R : ℝ} (hR : 0 < R) :
    ∫⁻ k in ball (0 : Fin d → ℝ) R, ENNReal.ofReal (‖k‖ ^ (-s)) < ∞ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfin : finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  have h := lintegral_ball_hom_rpow (volume : Measure (Fin d → ℝ)) (P := fun _ => 1)
    (fun _ => zero_le_one) measurable_const (k := 0) (fun c _ x => by simp) hs
    (by rw [hfin]; simpa using hsd) hR
  simp only [one_mul] at h
  rw [h]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  simp

/-- `∫_{‖k‖<1} ‖k‖^{-s} dk = ∞` on `Fin d → ℝ` (sup norm) for `s ≥ d ≥ 1`. -/
theorem lintegral_ball_rpow_neg_eq_top (hd : 0 < d) {s : ℝ} (hds : (d : ℝ) ≤ s) :
    ∫⁻ k in ball (0 : Fin d → ℝ) 1, ENNReal.ofReal (‖k‖ ^ (-s)) = ∞ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfin : finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set V := ∫⁻ k in ball (0 : Fin d → ℝ) 1, ENNReal.ofReal 1 with hV
  have hVeq : V = volume (ball (0 : Fin d → ℝ) 1) := by simp [hV]
  have hV0 : V ≠ 0 := by rw [hVeq]; exact (measure_ball_pos volume 0 one_pos).ne'
  have hVt : V ≠ ∞ := by rw [hVeq]; exact measure_ball_lt_top.ne
  have hge : ∀ n : ℕ, 2 ≤ n →
      (n : ℝ≥0∞) * V ≤ ∫⁻ k in ball (0 : Fin d → ℝ) 1, ENNReal.ofReal (‖k‖ ^ (-s)) := by
    intro n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hnpos : (0 : ℝ) < n := by linarith
    set t : ℝ := d - d / n with ht
    have hdn : d / n < (d : ℝ) := div_lt_self hdpos hn1
    have ht0 : 0 < t := by rw [ht]; linarith
    have htd : t < d := by rw [ht]; have : 0 < (d : ℝ) / n := by positivity
                           linarith
    have h := lintegral_ball_hom_rpow (volume : Measure (Fin d → ℝ)) (P := fun _ => 1)
      (fun _ => zero_le_one) measurable_const (k := 0) (fun c _ x => by simp) ht0
      (by rw [hfin]; simpa using htd) one_pos
    have hval : (0 + (finrank ℝ (Fin d → ℝ) : ℝ)) / (0 + (finrank ℝ (Fin d → ℝ) : ℝ) - t) *
        1 ^ (0 + (finrank ℝ (Fin d → ℝ) : ℝ) - t) = n := by
      rw [hfin, one_rpow, mul_one, zero_add, ht]
      field_simp
      ring
    simp only [one_mul] at h
    rw [hval, ENNReal.ofReal_natCast] at h
    rw [← hV] at h
    rw [← h]
    refine setLIntegral_mono' measurableSet_ball fun k hk => ENNReal.ofReal_le_ofReal ?_
    rcases (norm_nonneg k).eq_or_lt with h0 | h0
    · rw [← h0, zero_rpow (by linarith), zero_rpow (by linarith)]
    · have hk1 : ‖k‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hk).le
      exact rpow_le_rpow_of_exponent_ge h0 hk1 (by linarith)
  by_contra hI
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hI hV0)
  have h2 := hge (n + 2) (by omega)
  rw [← ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)] at h2
  have := h2.trans_lt hn
  norm_cast at this
  omega

/-! ### The lazy nearest-neighbour symbol -/

/-- `‖k‖² ≤ ∑ⱼ kⱼ²` for the sup norm on `Fin d → ℝ`. -/
theorem sq_norm_le_sum_sq (k : Fin d → ℝ) : ‖k‖ ^ 2 ≤ ∑ j, k j ^ 2 := by
  have h : ‖k‖ ≤ √(∑ j, k j ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (sqrt_nonneg _)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (fun i _ => sq_nonneg (k i))
      (Finset.mem_univ j))
  calc ‖k‖ ^ 2 ≤ √(∑ j, k j ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (k i))

/-- `∑ⱼ kⱼ² ≤ d ‖k‖²` for the sup norm on `Fin d → ℝ`. -/
theorem sum_sq_le_card_mul_sq_norm (k : Fin d → ℝ) : ∑ j, k j ^ 2 ≤ d * ‖k‖ ^ 2 := by
  have h : ∀ j, k j ^ 2 ≤ ‖k‖ ^ 2 := fun j => by
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm k j) 2
  calc ∑ j, k j ^ 2 ≤ ∑ _j : Fin d, ‖k‖ ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

/-- `1 - φ(k) = (2d)⁻¹ ∑ⱼ (1 - cos kⱼ)` for `φ(k) = 1/2 + (2d)⁻¹ ∑ⱼ cos kⱼ`. -/
theorem one_sub_lazySymbol_eq (hd : 0 < d) (k : Fin d → ℝ) :
    1 - (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ j, cos (k j)) = (2 * d : ℝ)⁻¹ * ∑ j, (1 - cos (k j)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  ring

/-- `1 - φ(k) ≤ ‖k‖²/4`. -/
theorem one_sub_lazySymbol_le (hd : 0 < d) (k : Fin d → ℝ) :
    1 - (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ j, cos (k j)) ≤ ‖k‖ ^ 2 / 4 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [one_sub_lazySymbol_eq hd]
  have h1 : ∑ j, (1 - cos (k j)) ≤ ∑ j, k j ^ 2 / 2 :=
    Finset.sum_le_sum fun j _ => by linarith [one_sub_sq_div_two_le_cos (x := k j)]
  have h2 := sum_sq_le_card_mul_sq_norm k
  rw [← Finset.sum_div] at h1
  calc (2 * d : ℝ)⁻¹ * ∑ j, (1 - cos (k j)) ≤ (2 * d : ℝ)⁻¹ * ((d * ‖k‖ ^ 2) / 2) := by
        gcongr
        linarith
    _ = ‖k‖ ^ 2 / 4 := by field_simp; ring

/-- `‖k‖²/(dπ²) ≤ 1 - φ(k)` on the box `(-π, π)^d = ball 0 π`. -/
theorem le_one_sub_lazySymbol (hd : 0 < d) {k : Fin d → ℝ} (hk : k ∈ ball (0 : Fin d → ℝ) π) :
    ‖k‖ ^ 2 / (d * π ^ 2) ≤ 1 - (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ j, cos (k j)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [one_sub_lazySymbol_eq hd]
  have hkπ : ‖k‖ < π := mem_ball_zero_iff.1 hk
  have h1 : ∑ j, 2 / π ^ 2 * k j ^ 2 ≤ ∑ j, (1 - cos (k j)) :=
    Finset.sum_le_sum fun j _ => by
      have : |k j| ≤ π := by
        rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm k j).trans hkπ.le
      linarith [cos_le_one_sub_mul_cos_sq this]
  rw [← Finset.mul_sum] at h1
  have h2 := sq_norm_le_sum_sq k
  calc ‖k‖ ^ 2 / (d * π ^ 2) = (2 * d : ℝ)⁻¹ * (2 / π ^ 2 * ‖k‖ ^ 2) := by
        field_simp
    _ ≤ (2 * d : ℝ)⁻¹ * (2 / π ^ 2 * ∑ j, k j ^ 2) := by gcongr
    _ ≤ _ := by gcongr

/-- `0 ≤ φ(k)` for `φ(k) = 1/2 + (2d)⁻¹ ∑ⱼ cos kⱼ`. -/
theorem lazySymbol_nonneg (hd : 0 < d) (k : Fin d → ℝ) :
    0 ≤ 1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => neg_one_le_cos (k i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_neg, mul_one] at h
  have : (2 * d : ℝ)⁻¹ * (-d) ≤ (2 * d : ℝ)⁻¹ * ∑ i, cos (k i) := by gcongr
  have he : (2 * d : ℝ)⁻¹ * (-d) = -1 / 2 := by field_simp
  linarith

/-- **Integrability threshold.** For `j ≥ 1`,
`∫_{(-π,π)^d} (1 - φ(k))^{-j} dk < ∞ ↔ 2j < d`, in `ℝ≥0∞`. -/
theorem lintegral_lazySymbol_lt_top_iff (hd : 0 < d) {j : ℕ} (hj : 0 < j) :
    ∫⁻ k in ball (0 : Fin d → ℝ) π,
        ((1 - ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)))⁻¹) ^ j < ∞ ↔
      2 * j < d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set s : ℝ := ((2 * j : ℕ) : ℝ) with hs
  have hspos : 0 < s := by rw [hs]; exact_mod_cast (by omega : 0 < 2 * j)
  -- `1 - ofReal φ = ofReal (1 - φ)`
  have hsub : ∀ k : Fin d → ℝ, 1 - ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) =
      ENNReal.ofReal (1 - (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i))) := fun k => by
    rw [ENNReal.ofReal_sub _ (lazySymbol_nonneg hd k), ENNReal.ofReal_one]
  -- the power of the norm as an inverse power
  have hrpow : ∀ k : Fin d → ℝ, ‖k‖ ^ (-s) = ((‖k‖ ^ 2) ^ j)⁻¹ := fun k => by
    rw [hs, rpow_neg (norm_nonneg _), rpow_natCast, pow_mul]
  constructor
  · intro hfin
    by_contra hdj
    push Not at hdj
    have hds : (d : ℝ) ≤ s := by rw [hs]; exact_mod_cast hdj
    have htop := lintegral_ball_rpow_neg_eq_top hd hds
    refine absurd hfin (not_lt.2 ?_)
    rw [← htop]
    calc ∫⁻ k in ball (0 : Fin d → ℝ) 1, ENNReal.ofReal (‖k‖ ^ (-s))
        ≤ ∫⁻ k in ball (0 : Fin d → ℝ) 1,
            ((1 - ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)))⁻¹) ^ j := by
          refine lintegral_mono fun k => ?_
          rw [hsub]
          have hup := ENNReal.ofReal_le_ofReal (one_sub_lazySymbol_le hd k)
          refine le_trans ?_ (pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.2 hup) j)
          rcases (norm_nonneg k).eq_or_lt with h0 | h0
          · rw [← h0, zero_rpow (by linarith)]; simp
          · rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow
              (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hrpow]
            have hk2 : 0 < ‖k‖ ^ 2 := by positivity
            have he : ((‖k‖ ^ 2 / 4)⁻¹) ^ j = 4 ^ j * ((‖k‖ ^ 2) ^ j)⁻¹ := by
              rw [inv_div, div_pow, div_eq_mul_inv]
            rw [he]
            exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      _ ≤ _ := lintegral_mono_set (ball_subset_ball (by linarith [pi_gt_three]))
  · intro hdj
    have hsd : s < d := by rw [hs]; exact_mod_cast hdj
    set c : ℝ := d * π ^ 2 with hc
    have hcpos : 0 < c := by positivity
    have hae : ∀ᵐ k ∂(volume.restrict (ball (0 : Fin d → ℝ) π)), k ≠ 0 :=
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton 0))
    calc ∫⁻ k in ball (0 : Fin d → ℝ) π,
          ((1 - ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)))⁻¹) ^ j
        ≤ ∫⁻ k in ball (0 : Fin d → ℝ) π, ENNReal.ofReal (c ^ j) * ENNReal.ofReal (‖k‖ ^ (-s)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, ae_restrict_mem measurableSet_ball] with k hk0 hk
          rw [hsub]
          have hk2 : 0 < ‖k‖ ^ 2 := by have := norm_pos_iff.2 hk0; positivity
          have hlow := ENNReal.ofReal_le_ofReal (le_one_sub_lazySymbol hd hk)
          refine le_trans (pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.2 hlow) j) ?_
          rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow
            (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          rw [hrpow, ← hc, inv_div, div_pow, div_eq_mul_inv]
      _ = ENNReal.ofReal (c ^ j) * ∫⁻ k in ball (0 : Fin d → ℝ) π, ENNReal.ofReal (‖k‖ ^ (-s)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_ball_rpow_neg_lt_top hd hspos hsd pi_pos)

/-! ### Orthogonality of characters on the box -/

/-- `∫_{-π}^{π} exp(i n t) dt = 2π [n = 0]` for `n ∈ ℤ`. -/
theorem integral_Ioo_exp_int_mul_I (n : ℤ) :
    ∫ t in Ioo (-π) π, Complex.exp (↑(t * (n : ℝ)) * Complex.I) =
      if n = 0 then (2 * π : ℂ) else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_neg_eq_add, Complex.real_smul, mul_one]
    push_cast
    ring
  · have hc : (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.2 hn) Complex.I_ne_zero
    have hfun : (fun t : ℝ => Complex.exp (↑(t * (n : ℝ)) * Complex.I)) =
        fun t : ℝ => Complex.exp ((n : ℂ) * Complex.I * t) := by
      funext t; push_cast; ring_nf
    rw [hfun, integral_exp_mul_complex hc]
    have he : Complex.exp ((n : ℂ) * Complex.I * (π : ℝ)) =
        Complex.exp ((n : ℂ) * Complex.I * ((-π : ℝ))) := by
      have : (n : ℂ) * Complex.I * (π : ℝ) =
          (n : ℂ) * Complex.I * ((-π : ℝ)) + n * (2 * π * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [he, sub_self, zero_div]

/-- **Orthogonality of characters.** For `x ∈ ℤ^d`,
`∫_{(-π,π)^d} exp(i k·x) dk = (2π)^d [x = 0]`. -/
theorem integral_ball_exp_inner (x : Fin d → ℤ) :
    ∫ k in ball (0 : Fin d → ℝ) π, Complex.exp (↑(∑ j, k j * (x j : ℝ)) * Complex.I) =
      if x = 0 then ((2 * π : ℂ) ^ d) else 0 := by
  have hball : ball (0 : Fin d → ℝ) π = Set.univ.pi fun _ => Ioo (-π) π := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · ext k; simp [Subsingleton.elim k 0, pi_pos]
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      rw [ball_pi _ pi_pos]
      simp [Real.ball_eq_Ioo]
  rw [hball, volume_pi, Measure.restrict_pi_pi]
  simp_rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun j t => Complex.exp (↑(t * (x j : ℝ)) * Complex.I))]
  simp_rw [integral_Ioo_exp_int_mul_I]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]


/-- **Fourier formula for closed step sequences.** For a finite family of steps `v a ∈ ℤ^d`
with real weights `w a`, the `N`-th power of `ŵ(k) = ∑ₐ w a exp(i k·v a)` integrates over
`(-π, π)^d` to `(2π)^d` times the total weight of the step sequences of length `N` that
return to `0`. -/
theorem integral_ball_pow_sum_exp {α : Type*} [Fintype α] (w : α → ℝ) (v : α → Fin d → ℤ)
    (N : ℕ) :
    ∫ k in ball (0 : Fin d → ℝ) π,
        (∑ a, (w a : ℂ) * Complex.exp (↑(∑ j, k j * (v a j : ℝ)) * Complex.I)) ^ N =
      (2 * π : ℂ) ^ d *
        ((∑ s ∈ Finset.univ.filter fun s : Fin N → α => ∑ i, v (s i) = 0, ∏ i, w (s i) : ℝ) :
          ℂ) := by
  rw [Complex.ofReal_sum, Finset.sum_filter]
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hint : ∀ s : Fin N → α, Integrable (fun k : Fin d → ℝ => (∏ i, (w (s i) : ℂ)) *
      Complex.exp (∑ i, ↑(∑ j, k j * (v (s i) j : ℝ)) * Complex.I))
      (volume.restrict (ball (0 : Fin d → ℝ) π)) := fun s => by
    refine (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 π) ?_).mono_set
      ball_subset_closedBall
    exact (continuous_const.mul (Complex.continuous_exp.comp (continuous_finsetSum _
      fun i _ => (Complex.continuous_ofReal.comp (continuous_finsetSum _
        fun j _ => (continuous_apply j).mul continuous_const)).mul
          continuous_const))).continuousOn
  rw [integral_finsetSum _ fun s _ => hint s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]
  have hsum : ∀ k : Fin d → ℝ, ∑ i, (↑(∑ j, k j * (v (s i) j : ℝ)) : ℂ) * Complex.I =
      ↑(∑ j, k j * ((∑ i, v (s i)) j : ℝ)) * Complex.I := fun k => by
    rw [← Finset.sum_mul]
    congr 1
    push_cast [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hsum, integral_ball_exp_inner]
  split_ifs <;> push_cast <;> ring

/-! ### Convolution powers as sums over step sequences -/

/-- **Step-sequence expansion.** If `p = ∑ₐ w a δ_{v a}` is a finite combination of point
masses on an abelian group and `Pⁿ` are its convolution powers, then `Pⁿ(z)` is the total
weight `∏ᵢ w(sᵢ)` of the step sequences `s` of length `n` with `∑ᵢ v(sᵢ) = z`. -/
theorem convPow_eq_sum_prod {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] {α : Type*}
    [Fintype α] (w : α → ℝ≥0∞) (v : α → Γ) (p : Γ → ℝ≥0∞)
    (hp : ∀ x, p x = ∑ a, w a * if v a = x then 1 else 0) (P : ℕ → Γ → ℝ≥0∞)
    (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) (n : ℕ) (z : Γ) :
    P n z = ∑ s : Fin n → α, (∏ i, w (s i)) * if ∑ i, v (s i) = z then 1 else 0 := by
  induction n generalizing z with
  | zero => simp [h0, eq_comm]
  | succ n ih =>
    rw [hs]
    simp_rw [ih, hp, Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    conv_rhs => rw [← (Fin.snocEquiv fun _ => α).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
    rw [tsum_eq_single (∑ i, v (s i)) fun y hy => by simp [Ne.symm hy]]
    simp only [ite_true, mul_one, Finset.mul_sum, eq_neg_add_iff_add_eq, mul_assoc]

/-! ### Green, bubble and triangle sums as integrals -/

section Diagrams

variable {Γ : Type*} [AddCommGroup Γ] (P : ℕ → Γ → ℝ≥0∞)
  {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ≥0∞}

private theorem tsum_mul_tsum' (a b : ℕ → ℝ≥0∞) :
    (∑' n, a n) * (∑' m, b m) = ∑' n, ∑' m, a n * b m := by
  rw [← ENNReal.tsum_mul_right]
  congr 1
  funext n
  rw [← ENNReal.tsum_mul_left]

/-- **Green function at the origin.** If `Pⁿ(0) = ∫ fⁿ dμ` for all `n`, then
`∑ₙ Pⁿ(0) = ∫ (1 - f)⁻¹ dμ`. -/
theorem tsum_convPow_zero_eq_lintegral (hf : Measurable f)
    (hret : ∀ n, P n 0 = ∫⁻ x, f x ^ n ∂μ) :
    ∑' n, P n 0 = ∫⁻ x, (1 - f x)⁻¹ ∂μ := by
  simp_rw [hret, ← ENNReal.tsum_geometric]
  rw [lintegral_tsum fun n => (hf.pow_const n).aemeasurable]

/-- **Bubble.** For symmetric convolution powers (`P^{a+b}(x) = ∑_y Pᵃ(y) Pᵇ(x - y)`,
`Pⁿ(-x) = Pⁿ(x)`) with `Pⁿ(0) = ∫ fⁿ dμ`, `∑ᵤ G(u)² = ∫ (1 - f)⁻² dμ`, `G = ∑ₙ Pⁿ`. -/
theorem tsum_sq_tsum_convPow_eq_lintegral
    (hadd : ∀ a b x, P (a + b) x = ∑' y, P a y * P b (-y + x))
    (hsym : ∀ n x, P n (-x) = P n x) (hf : Measurable f)
    (hret : ∀ n, P n 0 = ∫⁻ x, f x ^ n ∂μ) :
    ∑' u, (∑' n, P n u) ^ 2 = ∫⁻ x, ((1 - f x)⁻¹) ^ 2 ∂μ := by
  have hpair : ∀ n m, ∑' u, P n u * P m u = P (n + m) 0 := fun n m => by
    rw [hadd]; simp [hsym]
  calc ∑' u, (∑' n, P n u) ^ 2 = ∑' u, ∑' n, ∑' m, P n u * P m u := by
        simp_rw [sq, tsum_mul_tsum']
    _ = ∑' n, ∑' m, ∑' u, P n u * P m u := by
        rw [ENNReal.tsum_comm]; congr 1; funext n; rw [ENNReal.tsum_comm]
    _ = ∑' n, ∑' m, ∫⁻ x, f x ^ n * f x ^ m ∂μ := by simp_rw [hpair, hret, pow_add]
    _ = ∫⁻ x, ∑' n, ∑' m, f x ^ n * f x ^ m ∂μ := by
        have hm : ∀ n m, Measurable fun x => f x ^ n * f x ^ m := fun n m =>
          (hf.pow_const n).mul (hf.pow_const m)
        rw [lintegral_tsum fun n => (Measurable.tsum fun m => hm n m).aemeasurable]
        congr 1; funext n
        rw [lintegral_tsum fun m => (hm n m).aemeasurable]
    _ = _ := by simp_rw [← tsum_mul_tsum', ENNReal.tsum_geometric, sq]

/-- **Triangle.** Under the hypotheses of `tsum_sq_tsum_convPow_eq_lintegral`,
`∑ᵤ,ᵥ G(u) G(v - u) G(v) = ∫ (1 - f)⁻³ dμ`. -/
theorem tsum_triangle_tsum_convPow_eq_lintegral
    (hadd : ∀ a b x, P (a + b) x = ∑' y, P a y * P b (-y + x))
    (hsym : ∀ n x, P n (-x) = P n x) (hf : Measurable f)
    (hret : ∀ n, P n 0 = ∫⁻ x, f x ^ n ∂μ) :
    ∑' u, ∑' v, (∑' n, P n u) * (∑' n, P n (v - u)) * (∑' n, P n v) =
      ∫⁻ x, ((1 - f x)⁻¹) ^ 3 ∂μ := by
  have hpair : ∀ n m, ∑' u, P n u * P m u = P (n + m) 0 := fun n m => by
    rw [hadd]; simp [hsym]
  have htwo : ∀ v, ∑' u, (∑' n, P n u) * (∑' n, P n (v - u)) =
      ∑' n, ∑' m, P (n + m) v := fun v => by
    simp_rw [tsum_mul_tsum']
    rw [ENNReal.tsum_comm]; congr 1; funext n; rw [ENNReal.tsum_comm]; congr 1; funext m
    rw [hadd]; simp_rw [sub_eq_neg_add]
  have hm : ∀ n m l, Measurable fun x => f x ^ n * f x ^ m * f x ^ l := fun n m l =>
    ((hf.pow_const n).mul (hf.pow_const m)).mul (hf.pow_const l)
  calc ∑' u, ∑' v, (∑' n, P n u) * (∑' n, P n (v - u)) * (∑' n, P n v)
      = ∑' v, (∑' n, ∑' m, P (n + m) v) * ∑' l, P l v := by
        rw [ENNReal.tsum_comm]; congr 1; funext v; rw [ENNReal.tsum_mul_right, htwo]
    _ = ∑' v, ∑' n, ∑' m, ∑' l, P (n + m) v * P l v := by
        congr 1; funext v; rw [← ENNReal.tsum_mul_right]; congr 1; funext n
        rw [← ENNReal.tsum_mul_right]; congr 1; funext m; rw [← ENNReal.tsum_mul_left]
    _ = ∑' n, ∑' m, ∑' l, ∑' v, P (n + m) v * P l v := by
        rw [ENNReal.tsum_comm]; congr 1; funext n
        rw [ENNReal.tsum_comm]; congr 1; funext m
        rw [ENNReal.tsum_comm]
    _ = ∑' n, ∑' m, ∑' l, ∫⁻ x, f x ^ n * f x ^ m * f x ^ l ∂μ := by
        simp_rw [hpair, hret, pow_add]
    _ = ∫⁻ x, ∑' n, ∑' m, ∑' l, f x ^ n * f x ^ m * f x ^ l ∂μ := by
        rw [lintegral_tsum fun n => (Measurable.tsum fun m =>
          Measurable.tsum fun l => hm n m l).aemeasurable]
        congr 1; funext n
        rw [lintegral_tsum fun m => (Measurable.tsum fun l => hm n m l).aemeasurable]
        congr 1; funext m
        rw [lintegral_tsum fun l => (hm n m l).aemeasurable]
    _ = _ := by
        congr 1; funext x
        rw [pow_succ, sq, ← ENNReal.tsum_geometric, tsum_mul_tsum', ← ENNReal.tsum_mul_right]
        congr 1; funext n; rw [← ENNReal.tsum_mul_right]; congr 1; funext m
        rw [← ENNReal.tsum_mul_left]

end Diagrams


/-! ### Additive convolution powers -/

section Additive

variable {Γ : Type*} [AddCommGroup Γ] (p : Γ → ℝ≥0∞) (P : ℕ → Γ → ℝ≥0∞)

open Classical in
/-- The additive recursion `P⁰ = δ₀`, `Pⁿ⁺¹(z) = ∑_y Pⁿ(y) p(z - y)` gives the convolution powers
of `DiscreteConvolution`, written there on `Multiplicative Γ`. -/
theorem eq_convPow_ofAdd (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) (n : ℕ) (z : Γ) :
    P n z = (Nat.rec (fun z => if z = 1 then 1 else 0)
      (fun _ ν z => ∑' y, ν y * (fun y : Multiplicative Γ => p y.toAdd) (y⁻¹ * z)) n :
        Multiplicative Γ → ℝ≥0∞) (Multiplicative.ofAdd z) := by
  induction n generalizing z with
  | zero =>
    rw [h0, Nat.rec_zero]
    by_cases hz : z = 0 <;> simp [hz]
  | succ n ih =>
    rw [hs]
    change _ = ∑' y : Multiplicative Γ, _
    rw [← Multiplicative.ofAdd.tsum_eq]
    refine tsum_congr fun y => ?_
    rw [ih]
    rfl

open Classical in
/-- `P^{a+b}(x) = ∑_y Pᵃ(y) Pᵇ(x - y)` for the additive convolution powers. -/
theorem convPow_add_of_rec (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) (a b : ℕ) (x : Γ) :
    P (a + b) x = ∑' y, P a y * P b (-y + x) := by
  simp_rw [eq_convPow_ofAdd p P h0 hs]
  refine (convPow_add (fun y : Multiplicative Γ => p y.toAdd) a b
    (Multiplicative.ofAdd x)).trans ?_
  rw [← Multiplicative.ofAdd.tsum_eq]
  rfl

open Classical in
/-- The additive convolution powers of a symmetric `p` are symmetric. -/
theorem convPow_neg_of_rec (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) (hp : ∀ x, p (-x) = p x) (n : ℕ)
    (x : Γ) : P n (-x) = P n x := by
  rw [eq_convPow_ofAdd p P h0 hs, eq_convPow_ofAdd p P h0 hs]
  exact convPow_inv (fun y : Multiplicative Γ => p y.toAdd) (fun y => hp y.toAdd) n
    (Multiplicative.ofAdd x)

end Additive

/-! ### Lazy nearest-neighbour walk -/

private theorem lazy_sum_exp (hd : 0 < d) (k : Fin d → ℝ) :
    ∑ a : Option (Fin d × Bool),
        ((a.elim (1 / 2) fun _ => (4 * d : ℝ)⁻¹ : ℝ) : ℂ) * Complex.exp
          (↑(∑ j, k j * (((a.elim 0 fun jb => if jb.2 then Pi.single jb.1 1 else
            -Pi.single jb.1 1 : Fin d → ℤ) j : ℤ) : ℝ)) * Complex.I) =
      ((1 / 2 + (2 * d : ℝ)⁻¹ * ∑ j, cos (k j) : ℝ) : ℂ) := by
  have hdpos : (0 : ℂ) ≠ d := by exact_mod_cast hd.ne
  have hsg : ∀ j, ∑ i, k i * (((Pi.single j (1 : ℤ) : Fin d → ℤ) i : ℤ) : ℝ) = k j := fun j => by
    simp [Pi.single_apply]
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, Option.elim_none,
    Option.elim_some, ite_true, Bool.false_eq_true, ite_false, Pi.zero_apply, Int.cast_zero,
    mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, hsg]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (2 * d : ℂ)⁻¹ * Complex.cos (k j) = (4 * d : ℂ)⁻¹ * (2 * Complex.cos (k j)) by
    field_simp; ring, Complex.two_cos]
  ring_nf

open Classical in
private theorem lazy_kernel_eq (hd : 0 < d) (x : Fin d → ℤ) :
    (if x = 0 then 2⁻¹ else if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then
        (4 * d : ℝ≥0∞)⁻¹ else 0) =
      ∑ a : Option (Fin d × Bool), ENNReal.ofReal (a.elim (1 / 2) fun _ => (4 * d : ℝ)⁻¹) *
        if (a.elim 0 fun jb => if jb.2 then Pi.single jb.1 1 else -Pi.single jb.1 1 :
          Fin d → ℤ) = x then 1 else 0 := by
  have hc : ENNReal.ofReal (4 * d : ℝ)⁻¹ = (4 * d : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  have hh : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hne : ∀ j, (Pi.single j (1 : ℤ) : Fin d → ℤ) ≠ 0 := fun j h => by
    simpa using congr_fun h j
  have hne' : ∀ j j', (Pi.single j (1 : ℤ) : Fin d → ℤ) ≠ -Pi.single j' 1 := fun j j' h => by
    have := congr_fun h j
    simp only [Pi.single_eq_same, Pi.neg_apply, Pi.single_apply] at this
    split_ifs at this
    omega
  have hinj : ∀ j j', (Pi.single j (1 : ℤ) : Fin d → ℤ) = Pi.single j' 1 ↔ j = j' :=
    fun j j' => ⟨fun h => by
      have := congr_fun h j
      simp only [Pi.single_eq_same, Pi.single_apply] at this
      split_ifs at this with hj
      · exact hj
      · omega, fun h => h ▸ rfl⟩
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, Option.elim_none,
    Option.elim_some, ite_true, Bool.false_eq_true, ite_false, hh, hc]
  by_cases hx : x = 0
  · subst hx
    simp [hne]
  · have h0x : ¬(0 = x) := Ne.symm hx
    simp only [hx, h0x, ↓reduceIte, mul_zero, zero_add]
    split_ifs with hex
    · obtain ⟨j0, rfl | rfl⟩ := hex
      · simp [hinj, fun j => (hne' j0 j).symm]
      · simp [hinj, neg_inj, hne']
    · push Not at hex
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [(hex j).1.symm, (hex j).2.symm, ↓reduceIte, mul_zero, add_zero]

open Classical in
/-- **Return probabilities of lazy nearest-neighbour walk.** For the walk on `ℤ^d` that stays
put with probability `1/2` and takes each unit step with probability `1/(4d)`,
`Pⁿ(0,0) = (2π)^{-d} ∫_{(-π,π)^d} φ(k)ⁿ dk` with `φ(k) = 1/2 + (2d)⁻¹ ∑ⱼ cos kⱼ`. -/
theorem lazyWalk_return_eq_lintegral (hd : 0 < d) (p : (Fin d → ℤ) → ℝ≥0∞)
    (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (P : ℕ → (Fin d → ℤ) → ℝ≥0∞) (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) (n : ℕ) :
    P n 0 = ENNReal.ofReal ((2 * π) ^ d)⁻¹ * ∫⁻ k in ball (0 : Fin d → ℝ) π,
      ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) ^ n := by
  set W : Option (Fin d × Bool) → ℝ := fun a => a.elim (1 / 2) fun _ => (4 * d : ℝ)⁻¹ with hW
  set V : Option (Fin d × Bool) → Fin d → ℤ := fun a =>
    a.elim 0 fun jb => if jb.2 then Pi.single jb.1 1 else -Pi.single jb.1 1 with hV
  have hW0 : ∀ a, 0 ≤ W a := fun a => by cases a <;> simp [hW]
  have hpw : ∀ x, p x = ∑ a, ENNReal.ofReal (W a) * if V a = x then 1 else 0 := fun x => by
    rw [hp, lazy_kernel_eq hd]
  rw [convPow_eq_sum_prod (fun a => ENNReal.ofReal (W a)) V p hpw P h0 hs n 0]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp_rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => hW0 _]
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => Finset.prod_nonneg fun i _ => hW0 _]
  have hcont : Continuous fun k : Fin d → ℝ => 1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i) := by
    fun_prop
  have hint : Integrable (fun k : Fin d → ℝ => (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) ^ n)
      (volume.restrict (ball (0 : Fin d → ℝ) π)) :=
    ((hcont.pow n).continuousOn.integrableOn_compact (isCompact_closedBall 0 π)).mono_set
      ball_subset_closedBall
  have hR := integral_ball_pow_sum_exp W V n
  have hsum : ∀ k : Fin d → ℝ, ∑ a, (W a : ℂ) *
      Complex.exp (↑(∑ j, k j * (V a j : ℝ)) * Complex.I) =
        ((1 / 2 + (2 * d : ℝ)⁻¹ * ∑ j, cos (k j) : ℝ) : ℂ) := fun k => lazy_sum_exp hd k
  simp_rw [hsum, ← Complex.ofReal_pow, integral_complex_ofReal] at hR
  have hR' : ∫ k in ball (0 : Fin d → ℝ) π, (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) ^ n =
      (2 * π) ^ d * ∑ s ∈ Finset.univ.filter fun s : Fin n → Option (Fin d × Bool) =>
        ∑ i, V (s i) = 0, ∏ i, W (s i) := by
    exact_mod_cast hR
  have h2π : (0 : ℝ) < (2 * π) ^ d := by positivity
  have hR'' : ∑ s ∈ Finset.univ.filter fun s : Fin n → Option (Fin d × Bool) =>
      ∑ i, V (s i) = 0, ∏ i, W (s i) = ((2 * π) ^ d)⁻¹ *
        ∫ k in ball (0 : Fin d → ℝ) π, (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) ^ n := by
    rw [hR', ← mul_assoc, inv_mul_cancel₀ h2π.ne', one_mul]
  rw [hR'', ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun k => pow_nonneg (lazySymbol_nonneg hd k) n)]
  simp_rw [ENNReal.ofReal_pow (lazySymbol_nonneg hd _)]

section Thresholds

variable {p : (Fin d → ℤ) → ℝ≥0∞} {P : ℕ → (Fin d → ℤ) → ℝ≥0∞}

private theorem ofReal_inv_two_pi_pow_mul_lt_top_iff {I : ℝ≥0∞} :
    ENNReal.ofReal ((2 * π) ^ d)⁻¹ * I < ∞ ↔ I < ∞ :=
  ⟨fun h => ENNReal.lt_top_of_mul_ne_top_right h.ne
    (ENNReal.ofReal_pos.2 (by positivity)).ne', fun h => ENNReal.mul_lt_top ENNReal.ofReal_lt_top h⟩

private theorem measurable_ofReal_lazySymbol :
    Measurable fun k : Fin d → ℝ => ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) := by
  fun_prop

open Classical in
private theorem lazyWalk_return_eq_lintegral_smul (hd : 0 < d)
    (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) (n : ℕ) :
    P n 0 = ∫⁻ k, ENNReal.ofReal (1 / 2 + (2 * d : ℝ)⁻¹ * ∑ i, cos (k i)) ^ n
      ∂(ENNReal.ofReal ((2 * π) ^ d)⁻¹ • volume.restrict (ball (0 : Fin d → ℝ) π)) := by
  rw [lintegral_smul_measure, smul_eq_mul, lazyWalk_return_eq_lintegral hd p hp P h0 hs n]

open Classical in
private theorem lazyWalk_add_neg (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) :
    (∀ a b x, P (a + b) x = ∑' y, P a y * P b (-y + x)) ∧ ∀ n x, P n (-x) = P n x := by
  have h0' : ∀ z, P 0 z = @ite _ (z = 0) (Classical.propDecidable _) 1 0 := fun z => by
    rw [h0 z]; congr
  have hpsym : ∀ x, p (-x) = p x := fun x => by
    have hex : (∃ j, -x = Pi.single j 1 ∨ -x = -Pi.single j 1) ↔
        ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 := exists_congr fun j => by
      rw [neg_eq_iff_eq_neg, neg_eq_iff_eq_neg, neg_neg, or_comm]
    rw [hp, hp]
    simp only [neg_eq_zero, hex]
  exact ⟨convPow_add_of_rec p P h0' hs, convPow_neg_of_rec p P h0' hs hpsym⟩

open Classical in
/-- **Green threshold.** For lazy nearest-neighbour walk on `ℤ^d`, `G(0) < ∞ ↔ 2 < d`. -/
theorem lazyWalk_green_lt_top_iff (hd : 0 < d)
    (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) :
    ∑' n, P n 0 < ∞ ↔ 2 < d := by
  rw [tsum_convPow_zero_eq_lintegral P _ measurable_ofReal_lazySymbol
    (lazyWalk_return_eq_lintegral_smul hd hp h0 hs), lintegral_smul_measure, smul_eq_mul,
    ofReal_inv_two_pi_pow_mul_lt_top_iff]
  simpa using lintegral_lazySymbol_lt_top_iff hd (j := 1) one_pos

open Classical in
/-- **Bubble threshold.** For lazy nearest-neighbour walk on `ℤ^d`,
`∑ᵤ G(u)² < ∞ ↔ 4 < d`. -/
theorem lazyWalk_bubble_lt_top_iff (hd : 0 < d)
    (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) :
    ∑' u, (∑' n, P n u) ^ 2 < ∞ ↔ 4 < d := by
  obtain ⟨hadd, hsym⟩ := lazyWalk_add_neg hp h0 hs
  rw [tsum_sq_tsum_convPow_eq_lintegral P _ hadd hsym measurable_ofReal_lazySymbol
    (lazyWalk_return_eq_lintegral_smul hd hp h0 hs), lintegral_smul_measure, smul_eq_mul,
    ofReal_inv_two_pi_pow_mul_lt_top_iff, lintegral_lazySymbol_lt_top_iff hd two_pos]
  norm_num

open Classical in
/-- **Triangle threshold.** For lazy nearest-neighbour walk on `ℤ^d`,
`∑ᵤ,ᵥ G(u) G(v - u) G(v) < ∞ ↔ 6 < d`. -/
theorem lazyWalk_triangle_lt_top_iff (hd : 0 < d)
    (hp : ∀ x, p x = if x = 0 then 2⁻¹ else
      if ∃ j, x = Pi.single j 1 ∨ x = -Pi.single j 1 then (4 * d : ℝ≥0∞)⁻¹ else 0)
    (h0 : ∀ z, P 0 z = if z = 0 then 1 else 0)
    (hs : ∀ n z, P (n + 1) z = ∑' y, P n y * p (-y + z)) :
    ∑' u, ∑' v, (∑' n, P n u) * (∑' n, P n (v - u)) * (∑' n, P n v) < ∞ ↔ 6 < d := by
  obtain ⟨hadd, hsym⟩ := lazyWalk_add_neg hp h0 hs
  rw [tsum_triangle_tsum_convPow_eq_lintegral P _ hadd hsym measurable_ofReal_lazySymbol
    (lazyWalk_return_eq_lintegral_smul hd hp h0 hs), lintegral_smul_measure, smul_eq_mul,
    ofReal_inv_two_pi_pow_mul_lt_top_iff, lintegral_lazySymbol_lt_top_iff hd (by norm_num)]

end Thresholds

end PercLib.Analysis
