/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Normalisation of a polynomially compounded lattice law (wiki article
`branching-random-walk`). New proofs; nothing is copied, no definition is added.
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Normalisation of a polynomially compounded lattice law

For `U : A → ℝ≥0∞` on an additive group, the convolution powers are written inline as
`Nat.rec (fun z => if z = 0 then 1 else 0) (fun _ ν z => ∑' y, ν y * U (z - y)) n`, the
additive form of the convention of `PercLib.Analysis.DiscreteConvolution`. Their total mass is
`(∑ U)^n`, so a mixture `∑_t T(t) U^{*t}` has mass `∑_t T(t) (∑ U)^t` (Tonelli).

On `ℤ^d`, let `w ≥ 0` be summable with `H = ∑_{x ≠ 0} w(x) > 0`, and
`T(t) = t^{-1-α/2} / ζ(1+α/2)`, `α > 0`, where `ζ(s) = ∑_{n ≥ 1} n^{-s}`. If `w(0) > 0`, the
compounded law of `U = w / H` has infinite mass, since `U` has mass `1 + w(0)/H > 1`; the law of
`U^* = 1_{x ≠ 0} w / H` and its compound `D^*` are probability mass functions.

## Main results

* `tsum_convPow_add`: `∑ U^{*n} = (∑ U)^n`.
* `tsum_tsum_mul_convPow_add`: the total mass of `∑_t T(t) U^{*t}`.
* `tsum_ofReal_rpow_div_mul_pow_eq_top`: `∑_t t^{-a} r^t / Z = ∞` for `r > 1`.
* `compoundedLattice_mass_eq_top_of_pos`, `tsum_ofReal_ite_div_eq_one`,
  `compoundedLattice_mass_eq_one`: the normalisation statements on `ℤ^d`.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal

namespace PercLib

section General

variable {A : Type*} [AddGroup A] [DecidableEq A]

/-- **Total mass of convolution powers.** `∑ U^{*n} = (∑ U)^n` on an additive group. -/
theorem tsum_convPow_add (U : A → ℝ≥0∞) (n : ℕ) :
    ∑' x, (Nat.rec (fun z => if z = 0 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * U (z - y)) n : A → ℝ≥0∞) x = (∑' x, U x) ^ n := by
  induction n with
  | zero =>
    change ∑' x, (if x = 0 then (1 : ℝ≥0∞) else 0) = _
    simp
  | succ n ih =>
    change ∑' x, ∑' y, (Nat.rec (fun z => if z = 0 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * U (z - y)) n : A → ℝ≥0∞) y * U (x - y) = _
    rw [ENNReal.tsum_comm, pow_succ, ← ih, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun y => ?_
    rw [ENNReal.tsum_mul_left]
    congr 1
    exact (Equiv.subRight y).tsum_eq U

/-- **Total mass of a compounded law.** `∑_x ∑_i T(i) U^{*n(i)}(x) = ∑_i T(i) (∑ U)^{n(i)}`. -/
theorem tsum_tsum_mul_convPow_add {ι : Type*} (T : ι → ℝ≥0∞) (n : ι → ℕ) (U : A → ℝ≥0∞) :
    ∑' x, ∑' i, T i * (Nat.rec (fun z => if z = 0 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * U (z - y)) (n i) : A → ℝ≥0∞) x =
      ∑' i, T i * (∑' x, U x) ^ n i := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun i => ?_
  rw [ENNReal.tsum_mul_left, tsum_convPow_add]

end General

/-- For `Z > 0` and `r > 1`, `∑_{t ≥ 1} (t^{-a} / Z) r^t = ∞`: the summands are eventually at
least `1 / Z`. -/
theorem tsum_ofReal_rpow_div_mul_pow_eq_top {a Z r : ℝ} (hZ : 0 < Z) (hr : 1 < r) :
    ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) + 1) ^ (-a) / Z) * ENNReal.ofReal r ^ (t + 1) = ∞ := by
  by_contra h
  have h0 := ENNReal.tendsto_cofinite_zero_of_tsum_ne_top h
  rw [Nat.cofinite_eq_atTop] at h0
  have hsmall := h0.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (one_div_pos.2 hZ)))
  -- `n ^ K (1/r) ^ n → 0` with `K = ⌈a⌉₊`, so eventually `n ^ K ≤ r ^ n`.
  have hr0 : 0 < r := by linarith
  have habs : |r⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.2 hr0)]; exact inv_lt_one_of_one_lt₀ hr
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one ⌈a⌉₊ habs).comp
    (tendsto_add_atTop_nat 1)
  have hle := hlim.eventually (ge_mem_nhds zero_lt_one)
  obtain ⟨t, hts, htl⟩ := (hsmall.and hle).exists
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at htl
  have h1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [t.cast_nonneg (α := ℝ)]
  have hpow : ((t : ℝ) + 1) ^ a ≤ r ^ (t + 1) := by
    calc ((t : ℝ) + 1) ^ a ≤ ((t : ℝ) + 1) ^ (⌈a⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil a)
      _ = ((t : ℝ) + 1) ^ ⌈a⌉₊ := Real.rpow_natCast _ _
      _ ≤ r ^ (t + 1) := by
          rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hr0 _)] at htl
          exact htl
  have hpos : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  have hge : ENNReal.ofReal (1 / Z) ≤
      ENNReal.ofReal (((t : ℝ) + 1) ^ (-a) / Z) * ENNReal.ofReal r ^ (t + 1) := by
    rw [← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, Real.rpow_neg hpos.le]
    refine div_le_div_of_nonneg_right ?_ hZ.le
    rw [inv_mul_eq_div, le_div_iff₀ (Real.rpow_pos_of_pos hpos a), one_mul]
    exact hpow
  exact absurd hts (not_lt.2 hge)

/-- The series `∑_{n ≥ 1} n^{-(1+α/2)}` converges for `α > 0`. -/
theorem summable_add_one_rpow_neg {α : ℝ} (hα : 0 < α) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 + α / 2)) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -(1 + α / 2) < -1))
  simpa only [Nat.cast_add, Nat.cast_one] using this

variable {d : ℕ}

/-- `∑_x w(x) / H = 1 + w(0) / H` for `H = ∑_{x ≠ 0} w(x)`, as an extended real. -/
theorem tsum_ofReal_div_eq (w : (Fin d → ℤ) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw : Summable w)
    (hH : 0 < ∑' x, if x = 0 then 0 else w x) :
    ∑' x, ENNReal.ofReal (w x / ∑' x, if x = 0 then 0 else w x) =
      ENNReal.ofReal ((w 0 + ∑' x, if x = 0 then 0 else w x) /
        ∑' x, if x = 0 then 0 else w x) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => div_nonneg (hw0 x) hH.le) (hw.div_const _),
    tsum_div_const, hw.tsum_eq_add_tsum_ite 0]

/-- **The compounded law of `U = w / H` has infinite mass when `w(0) > 0`.** Here
`H = ∑_{x ≠ 0} w(x) > 0`, `T(t) = t^{-1-α/2} / ζ(1+α/2)` with `ζ(s) = ∑_{n ≥ 1} n^{-s}`, and
the law is `∑_{t ≥ 1} T(t) U^{*t}`. -/
theorem compoundedLattice_mass_eq_top_of_pos (w : (Fin d → ℤ) → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : Summable w) (hH : 0 < ∑' x, if x = 0 then 0 else w x) (h0 : 0 < w 0)
    {α : ℝ} (hα : 0 < α) :
    ∑' x, ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) + 1) ^ (-(1 + α / 2)) /
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + α / 2))) *
      (Nat.rec (fun z => if z = 0 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * ENNReal.ofReal (w (z - y) /
          ∑' x, if x = 0 then 0 else w x)) (t + 1) :
        (Fin d → ℤ) → ℝ≥0∞) x = ∞ := by
  have hZ : 0 < ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + α / 2)) :=
    (summable_add_one_rpow_neg hα).tsum_pos (fun n => by positivity) 0 (by positivity)
  refine (tsum_tsum_mul_convPow_add (A := Fin d → ℤ) _ (fun t : ℕ => t + 1)
    (fun x => ENNReal.ofReal (w x / ∑' x, if x = 0 then 0 else w x))).trans ?_
  rw [tsum_ofReal_div_eq w hw0 hw hH]
  exact tsum_ofReal_rpow_div_mul_pow_eq_top hZ ((one_lt_div hH).2 (by linarith))

/-- **The repaired step law is a probability mass function.** `U^*(x) = 1_{x ≠ 0} w(x) / H`
with `H = ∑_{x ≠ 0} w(x) > 0` has total mass one. -/
theorem tsum_ofReal_ite_div_eq_one (w : (Fin d → ℤ) → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : Summable w) (hH : 0 < ∑' x, if x = 0 then 0 else w x) :
    ∑' x, ENNReal.ofReal ((if x = 0 then 0 else w x) / ∑' x, if x = 0 then 0 else w x) = 1 := by
  have hite : ∀ x : Fin d → ℤ, 0 ≤ (if x = 0 then 0 else w x) := fun x => by
    split_ifs
    · exact le_rfl
    · exact hw0 x
  have hsum : Summable fun x : Fin d → ℤ => if x = 0 then 0 else w x :=
    hw.of_nonneg_of_le hite fun x => by
      split_ifs
      · exact hw0 x
      · exact le_rfl
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => div_nonneg (hite x) hH.le)
    (hsum.div_const _), tsum_div_const, div_self hH.ne', ENNReal.ofReal_one]

/-- **The repaired compounded law is a probability mass function.** With
`U^*(x) = 1_{x ≠ 0} w(x) / H` and `T(t) = t^{-1-α/2} / ζ(1+α/2)`,
`D^* = ∑_{t ≥ 1} T(t) (U^*)^{*t}` has total mass one. -/
theorem compoundedLattice_mass_eq_one (w : (Fin d → ℤ) → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : Summable w) (hH : 0 < ∑' x, if x = 0 then 0 else w x) {α : ℝ} (hα : 0 < α) :
    ∑' x, ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) + 1) ^ (-(1 + α / 2)) /
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + α / 2))) *
      (Nat.rec (fun z => if z = 0 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * ENNReal.ofReal ((if z - y = 0 then 0 else w (z - y)) /
          ∑' x, if x = 0 then 0 else w x)) (t + 1) :
        (Fin d → ℤ) → ℝ≥0∞) x = 1 := by
  have hZ : 0 < ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + α / 2)) :=
    (summable_add_one_rpow_neg hα).tsum_pos (fun n => by positivity) 0 (by positivity)
  refine (tsum_tsum_mul_convPow_add (A := Fin d → ℤ) _ (fun t : ℕ => t + 1) (fun x =>
    ENNReal.ofReal ((if x = 0 then 0 else w x) / ∑' x, if x = 0 then 0 else w x))).trans ?_
  rw [tsum_ofReal_ite_div_eq_one w hw0 hw hH]
  simp only [one_pow, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_add_one_rpow_neg hα).div_const _), tsum_div_const, div_self hZ.ne',
    ENNReal.ofReal_one]

end PercLib
