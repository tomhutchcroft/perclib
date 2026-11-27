/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.CosineReciprocal
public import PercLib.Percolation.Bond.Lace.Expansion.BootstrapAlgebra
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Effective-denominator algebra for the second Fourier difference

Writing the canonical quotient as the reciprocal of
`1 - (j D + P / (1 + P))` avoids constructing an inverse convolution kernel.
The signed cosine-kernel estimates control the three values of `P`, while the
normalization keeps the dependence on the susceptibility parameter.

## Main results

* `effective_denominator_difference_bounds`: the two estimates needed by the reciprocal rule.
* `abs_effective_reciprocal_second_difference_le`: the three-resolvent bound.
* `effective_difference_coefficients_le`: explicit small-error constants after the first
  Fourier ratio has improved to `5/4`.

These are conditional scalar algebra lemmas. Their independent sign, denominator,
and difference hypotheses are kept explicit, even when there are more than ten,
so an application must supply each from its actual kernels. They do not assert
that any percolation model satisfies the weighted error estimates.
-/

@[expose] public section

open PercLib.Analysis

namespace PercLib.Percolation.Bond.Lace

private theorem fraction_difference {a b : ℝ} (ha : 1 + a ≠ 0) (hb : 1 + b ≠ 0) :
    a / (1 + a) - b / (1 + b) = (a - b) / ((1 + a) * (1 + b)) := by
  field_simp
  ring

/-- Passing from the signed numerator to the effective denominator preserves
its frequency deficit, with the quadratic correction displayed explicitly. -/
theorem abs_fraction_second_difference_le
    {a b c η ζ gl gk : ℝ} (hη : η < 1) (hζ : 0 ≤ ζ)
    (ha : |a| ≤ η) (hb : |b| ≤ η) (hc : |c| ≤ η)
    (hgl : 0 ≤ gl) (hgl2 : gl ≤ 2) (hgk : 0 ≤ gk)
    (hsecond : |a + c - 2 * b| ≤ 2 * ζ * gk)
    (hfirst : (c - a) ^ 2 ≤ 16 * ζ ^ 2 * gl * gk) :
    |a / (1 + a) + c / (1 + c) - 2 * (b / (1 + b))| ≤
      2 * (ζ / (1 - η) ^ 2 + 8 * ζ ^ 2 / (1 - η) ^ 3) * gk := by
  have he : 0 < 1 - η := sub_pos.mpr hη
  have hpa : 0 < 1 + a := by linarith [(abs_le.mp ha).1]
  have hpb : 0 < 1 + b := by linarith [(abs_le.mp hb).1]
  have hpc : 0 < 1 + c := by linarith [(abs_le.mp hc).1]
  have hia : (1 + a)⁻¹ ≤ (1 - η)⁻¹ := by
    apply inv_anti₀ he
    linarith [(abs_le.mp ha).1]
  have hib : (1 + b)⁻¹ ≤ (1 - η)⁻¹ := by
    apply inv_anti₀ he
    linarith [(abs_le.mp hb).1]
  have hic : (1 + c)⁻¹ ≤ (1 - η)⁻¹ := by
    apply inv_anti₀ he
    linarith [(abs_le.mp hc).1]
  have hs : |-a + -c - 2 * -b| ≤ 2 * (ζ * gk) := by
    calc
      _ = |-(a + c - 2 * b)| := by congr 1; ring
      _ = |a + c - 2 * b| := abs_neg _
      _ ≤ 2 * ζ * gk := hsecond
      _ = _ := by ring
  have hf : (-c - -a) ^ 2 ≤ 16 * (ζ * gl) * (ζ * gk) := by
    convert hfirst using 1 <;> ring
  have hraw := abs_reciprocal_second_difference_le
    (a := -a) (b := -b) (c := -c) (u := ζ * gk) (v := ζ * gl)
    (by simpa using hpa.ne') (by simpa using hpb.ne') (by simpa using hpc.ne') hs hf
  simp only [sub_neg_eq_add, abs_of_pos (inv_pos.mpr hpa),
    abs_of_pos (inv_pos.mpr hpb), abs_of_pos (inv_pos.mpr hpc), abs_mul] at hraw
  have heq : a / (1 + a) + c / (1 + c) - 2 * (b / (1 + b)) =
      -((1 + a)⁻¹ + (1 + c)⁻¹ - 2 * (1 + b)⁻¹) := by
    field_simp
    ring
  rw [heq, abs_neg]
  apply hraw.trans
  have hleft := mul_le_mul_of_nonneg_right
    (mul_le_mul (add_le_add hia hic) hib (inv_nonneg.mpr hpb.le)
      (by positivity : 0 ≤ (1 - η)⁻¹ + (1 - η)⁻¹))
    (mul_nonneg hζ hgk)
  have hprod := mul_le_mul
    (mul_le_mul hia hib (inv_nonneg.mpr hpb.le) (inv_nonneg.mpr he.le)) hic
    (inv_nonneg.mpr hpc.le) (by positivity : 0 ≤ (1 - η)⁻¹ * (1 - η)⁻¹)
  have hright := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 8))
      (mul_nonneg hζ hgl)) (mul_nonneg hζ hgk)
  have hgl' := mul_le_mul_of_nonneg_left hgl2
    (show 0 ≤ 8 * (1 - η)⁻¹ ^ 3 * ζ ^ 2 * gk by positivity)
  calc
    _ ≤ ((1 - η)⁻¹ + (1 - η)⁻¹) * (1 - η)⁻¹ * (ζ * gk) +
        8 * ((1 - η)⁻¹ * (1 - η)⁻¹ * (1 - η)⁻¹) * (ζ * gl) * (ζ * gk) :=
      add_le_add hleft hright
    _ = 2 * ζ / (1 - η) ^ 2 * gk +
        (8 * (1 - η)⁻¹ ^ 3 * ζ ^ 2 * gk) * gl := by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
    _ ≤ 2 * ζ / (1 - η) ^ 2 * gk +
        (8 * (1 - η)⁻¹ ^ 3 * ζ ^ 2 * gk) * 2 := add_le_add le_rfl hgl'
    _ = _ := by simp only [div_eq_mul_inv, ← inv_pow]; ring

/-- The antisymmetric difference of the fractional numerator has only two
positive numerator denominators. -/
theorem fraction_difference_sq_le
    {a c η ζ gl gk : ℝ} (hη : η < 1)
    (ha : |a| ≤ η) (hc : |c| ≤ η) (hgl : 0 ≤ gl) (hgk : 0 ≤ gk)
    (hfirst : (c - a) ^ 2 ≤ 16 * ζ ^ 2 * gl * gk) :
    (c / (1 + c) - a / (1 + a)) ^ 2 ≤
      16 * (ζ / (1 - η) ^ 2) ^ 2 * gl * gk := by
  have he : 0 < 1 - η := sub_pos.mpr hη
  have hpa : 0 < 1 + a := by linarith [(abs_le.mp ha).1]
  have hpc : 0 < 1 + c := by linarith [(abs_le.mp hc).1]
  have hprod : (1 - η) ^ 2 ≤ (1 + c) * (1 + a) := by
    simpa only [pow_two] using mul_le_mul
      (show 1 - η ≤ 1 + c by linarith [(abs_le.mp hc).1])
      (show 1 - η ≤ 1 + a by linarith [(abs_le.mp ha).1]) he.le hpc.le
  rw [fraction_difference hpc.ne' hpa.ne', div_pow]
  have hden := pow_le_pow_left₀ (sq_nonneg (1 - η)) hprod 2
  calc
    _ ≤ (16 * ζ ^ 2 * gl * gk) / ((1 - η) ^ 2) ^ 2 :=
      div_le_div₀ (by positivity) hfirst (by positivity) hden
    _ = _ := by simp only [div_eq_mul_inv, ← inv_pow]; ring

private theorem sq_add_le_common_factor {x y a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hx : x ^ 2 ≤ a ^ 2 * t) (hy : y ^ 2 ≤ b ^ 2 * t) :
    (x + y) ^ 2 ≤ (a + b) ^ 2 * t := by
  have hx' : |x| ≤ a * Real.sqrt t := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt ht] using hx
  have hy' : |y| ≤ b * Real.sqrt t := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt ht] using hy
  have h := pow_le_pow_left₀ (abs_nonneg (x + y))
    ((abs_add_le x y).trans ((add_le_add hx' hy').trans_eq
      (show a * Real.sqrt t + b * Real.sqrt t = (a + b) * Real.sqrt t by ring))) 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt ht] using h

/-- The effective denominator inherits both signed cosine difference estimates.
The arguments are the three transforms at `l-k`, `l`, and `l+k`; the displayed
premises are supplied by the existing cosine-kernel lemmas in applications. -/
theorem effective_denominator_difference_bounds
    {a b c Dm D0 Dp j η ζ gl gk : ℝ}
    (hη : η < 1) (hζ : 0 ≤ ζ) (hj : 0 ≤ j)
    (ha : |a| ≤ η) (hb : |b| ≤ η) (hc : |c| ≤ η)
    (hgl : 0 ≤ gl) (hgl2 : gl ≤ 2) (hgk : 0 ≤ gk)
    (hDsecond : |Dm + Dp - 2 * D0| ≤ 2 * gk)
    (hDfirst : (Dp - Dm) ^ 2 ≤ 16 * gl * gk)
    (hPsecond : |a + c - 2 * b| ≤ 2 * ζ * gk)
    (hPfirst : (c - a) ^ 2 ≤ 16 * ζ ^ 2 * gl * gk) :
    let Em := j * Dm + a / (1 + a)
    let E0 := j * D0 + b / (1 + b)
    let Ep := j * Dp + c / (1 + c)
    |Em + Ep - 2 * E0| ≤
        2 * (j + ζ / (1 - η) ^ 2 + 8 * ζ ^ 2 / (1 - η) ^ 3) * gk ∧
      (Ep - Em) ^ 2 ≤ 16 * (j + ζ / (1 - η) ^ 2) ^ 2 * gl * gk := by
  dsimp only
  constructor
  · have hP := abs_fraction_second_difference_le hη hζ ha hb hc hgl hgl2 hgk
      hPsecond hPfirst
    calc
      _ = |j * (Dm + Dp - 2 * D0) +
          (a / (1 + a) + c / (1 + c) - 2 * (b / (1 + b)))| := by congr 1; ring
      _ ≤ |j * (Dm + Dp - 2 * D0)| +
          |a / (1 + a) + c / (1 + c) - 2 * (b / (1 + b))| := abs_add_le _ _
      _ ≤ j * (2 * gk) +
          2 * (ζ / (1 - η) ^ 2 + 8 * ζ ^ 2 / (1 - η) ^ 3) * gk := by
        rw [abs_mul, abs_of_nonneg hj]
        exact add_le_add (mul_le_mul_of_nonneg_left hDsecond hj) hP
      _ = _ := by ring
  · have hP := fraction_difference_sq_le hη ha hc hgl hgk hPfirst
    have hD : (j * (Dp - Dm)) ^ 2 ≤ j ^ 2 * (16 * gl * gk) := by
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hDfirst (sq_nonneg j)]
    have hP' : (c / (1 + c) - a / (1 + a)) ^ 2 ≤
        (ζ / (1 - η) ^ 2) ^ 2 * (16 * gl * gk) := by nlinarith [hP]
    have h := sq_add_le_common_factor hj (by positivity : 0 ≤ ζ / (1 - η) ^ 2)
      (by positivity : 0 ≤ 16 * gl * gk) hD hP'
    convert h using 1 <;> ring

/-- The canonical Fourier equation gives the effective reciprocal directly;
no convolution inverse or additional expansion equation is introduced. -/
theorem eq_effective_reciprocal {T P j D : ℝ} (hP : 1 + P ≠ 0)
    (heq : T = 1 + P + (1 + P) * j * D * T) :
    1 - (j * D + P / (1 + P)) ≠ 0 ∧
      T = (1 - (j * D + P / (1 + P)))⁻¹ := by
  have hm : T * (1 - (j * D + P / (1 + P))) = 1 := by
    field_simp
    nlinarith [heq]
  have hd : 1 - (j * D + P / (1 + P)) ≠ 0 := by
    intro hz
    simp [hz] at hm
  exact ⟨hd, (mul_eq_one_iff_eq_inv₀ hd).mp hm⟩

/-- The second-difference estimate retains the two endpoint products and the
middle cancellation separately. This is the exact bound before taking their maximum. -/
theorem abs_effective_reciprocal_second_difference_le
    {a b c Cm C0 Cp K L1 L2 gl gk lam : ℝ}
    (ha : 0 < 1 - a) (hb : 0 < 1 - b) (hc : 0 < 1 - c)
    (hCm : 0 ≤ Cm) (hC0 : 0 ≤ C0) (hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (hgk : 0 ≤ gk)
    (hweakm : (1 - a)⁻¹ ≤ K * Cm) (hweak0 : (1 - b)⁻¹ ≤ K * C0)
    (hweakp : (1 - c)⁻¹ ≤ K * Cp) (hcancel : C0 * gl ≤ 2 / (1 + lam))
    (hsecond : |a + c - 2 * b| ≤ 2 * L2 * gk)
    (hfirst : (c - a) ^ 2 ≤ 16 * L1 ^ 2 * gl * gk) :
    |(1 - a)⁻¹ + (1 - c)⁻¹ - 2 * (1 - b)⁻¹| ≤
      gk * (K ^ 2 * L2 * (Cm * C0 + C0 * Cp) +
        16 * K ^ 3 * L1 ^ 2 / (1 + lam) * (Cm * Cp)) := by
  rw [reciprocal_second_difference ha.ne' hb.ne' hc.ne']
  have hIm : 0 ≤ (1 - a)⁻¹ := (inv_pos.mpr ha).le
  have hI0 : 0 ≤ (1 - b)⁻¹ := (inv_pos.mpr hb).le
  have hIp : 0 ≤ (1 - c)⁻¹ := (inv_pos.mpr hc).le
  have hprod := mul_le_mul (mul_le_mul hweak0 hweakm hIm (by positivity))
    hweakp hIp (by positivity)
  have hsum := mul_le_mul hweak0 (add_le_add hweakm hweakp)
    (add_nonneg hIm hIp) (by positivity)
  calc
    _ ≤ |(1 - b)⁻¹ * ((1 - a)⁻¹ + (1 - c)⁻¹) / 2 * (a + c - 2 * b)| +
        |(1 - b)⁻¹ * (1 - a)⁻¹ * (1 - c)⁻¹ / 2 * (c - a) ^ 2| := abs_add_le _ _
    _ = (1 - b)⁻¹ * ((1 - a)⁻¹ + (1 - c)⁻¹) / 2 * |a + c - 2 * b| +
        (1 - b)⁻¹ * (1 - a)⁻¹ * (1 - c)⁻¹ / 2 * (c - a) ^ 2 := by
      simp only [abs_mul, abs_div, abs_of_nonneg hIm, abs_of_nonneg hI0,
        abs_of_nonneg hIp, abs_of_nonneg (add_nonneg hIm hIp), abs_pow, sq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (K * C0) * (K * Cm + K * Cp) / 2 * (2 * L2 * gk) +
        ((K * C0) * (K * Cm) * (K * Cp)) / 2 * (16 * L1 ^ 2 * gl * gk) := by
      apply add_le_add
      · exact mul_le_mul (div_le_div_of_nonneg_right hsum (by norm_num))
          hsecond (abs_nonneg _) (by positivity)
      · exact mul_le_mul (div_le_div_of_nonneg_right hprod (by norm_num))
          hfirst (sq_nonneg _) (by positivity)
    _ = gk * (K ^ 2 * L2 * (Cm * C0 + C0 * Cp) +
        8 * K ^ 3 * L1 ^ 2 * (Cm * Cp) * (C0 * gl)) := by ring
    _ ≤ gk * (K ^ 2 * L2 * (Cm * C0 + C0 * Cp) +
        8 * K ^ 3 * L1 ^ 2 * (Cm * Cp) * (2 / (1 + lam))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcancel (by positivity))) hgk
    _ = _ := by ring

/-- The normalization halves the worst squared effective step factor.
The factorization keeps the susceptibility parameter until the final comparison. -/
theorem sq_normalized_step_le {lam u : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (lam + u) ^ 2 / (1 + lam) ≤ (1 + u) ^ 2 / 2 := by
  apply (div_le_div_iff₀ (by linarith) (by norm_num)).mpr
  have hu : 0 ≤ 1 + 2 * lam + 2 * u - u ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hlam1) hu]

/-- At small mass and frequency errors, the already improved ratio `5/4`
gives a strict `1/10` bound after division by the conventional factor `200`.
The exact three-product estimate above remains available for sharper substitutions. -/
theorem effective_difference_coefficients_le
    {eta zeta j lam : ℝ} (heta0 : 0 ≤ eta) (heta : eta ≤ 1 / 1000)
    (hzeta0 : 0 ≤ zeta) (hzeta : zeta ≤ 1 / 10)
    (hj0 : 0 ≤ j) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hj : j ≤ lam + eta / (1 - eta)) :
    (5 / 4 : ℝ) ^ 2 * (j + zeta / (1 - eta) ^ 2 +
        8 * zeta ^ 2 / (1 - eta) ^ 3) ≤ 10125 / 512 ∧
      16 * (5 / 4 : ℝ) ^ 3 * (j + zeta / (1 - eta) ^ 2) ^ 2 / (1 + lam) ≤
        10125 / 512 := by
  have he : 0 < 1 - eta := by linarith
  have he' : (999 / 1000 : ℝ) ≤ 1 - eta := by linarith
  have hc : eta / (1 - eta) ≤ 1 / 999 := by
    apply (div_le_iff₀ he).mpr
    linarith
  have hz : zeta / (1 - eta) ^ 2 ≤ 100000 / 998001 := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 999 / 1000) he' 2
    nlinarith
  have hz2 : 8 * zeta ^ 2 / (1 - eta) ^ 3 ≤ 80000000 / 997002999 := by
    apply (div_le_iff₀ (pow_pos he 3)).mpr
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 999 / 1000) he' 3
    have hzs := pow_le_pow_left₀ hzeta0 hzeta 2
    nlinarith
  have hu : eta / (1 - eta) + zeta / (1 - eta) ^ 2 ≤ 1 / 8 := by
    linarith
  constructor
  · have hj' : j ≤ 1 + 1 / 999 := by linarith
    nlinarith
  · have hsq := sq_normalized_step_le hlam0 hlam1
      (by positivity : 0 ≤ eta / (1 - eta) + zeta / (1 - eta) ^ 2)
      (hu.trans (by norm_num))
    have hj' : j + zeta / (1 - eta) ^ 2 ≤
        lam + (eta / (1 - eta) + zeta / (1 - eta) ^ 2) := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ j + zeta / (1 - eta) ^ 2) hj' 2
    have hden : 0 < 1 + lam := by linarith
    have hsmall := pow_le_pow_left₀
      (by positivity : 0 ≤ 1 + (eta / (1 - eta) + zeta / (1 - eta) ^ 2))
      (show 1 + (eta / (1 - eta) + zeta / (1 - eta) ^ 2) ≤ 9 / 8 by linarith) 2
    have hfinal : (j + zeta / (1 - eta) ^ 2) ^ 2 / (1 + lam) ≤ 81 / 128 := by
      apply (div_le_div_of_nonneg_right hpow hden.le).trans
      apply hsq.trans
      linarith
    calc
      _ = 16 * (5 / 4 : ℝ) ^ 3 *
          ((j + zeta / (1 - eta) ^ 2) ^ 2 / (1 + lam)) := by ring
      _ ≤ 16 * (5 / 4 : ℝ) ^ 3 * (81 / 128) :=
        mul_le_mul_of_nonneg_left hfinal (by norm_num)
      _ = _ := by norm_num

end PercLib.Percolation.Bond.Lace
