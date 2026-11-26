/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs of the targets PVA8, MQNP, LF50 and 6YYS of the wiki article `cutoff-families` (Definitions
I.1.3 and I.1.5 of T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1), stated
in `PercLib/Models/LongRange/Defs.lean`. New proofs from pinned mathlib's `integral_rpow`,
`Real.hasDerivAt_rpow_const` and `tendsto_rpow_neg_atTop`. No upstream code is copied.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Percolation.Bond.IntensityScaling
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The cut-off power law

For a general profile `K`, decreasing on `(0, ∞)`:

* `tendsto_cutoffKernel`: if `K → 0` (decreasing or not), then `J_r(e) → J(e)` as `r → ∞`;
* `hasDerivAt_cutoffKernel`: if `K` has derivative `-k` at `r` and `r ≠ N(x - y)`, then
  `d/dr J_r(x, y) = 1{N(x - y) < r} k`;
* `hasDerivAt_intensityProfile_of_hasDerivAt`: the chain rule for `1 - e^{-β J}`.

For the power law `K(s) = s^{-a}/a` with `a = d + α`, the four targets
`cutoffPowerLawFormula` (PVA8), `cutoffPowerLawMonotone` (MQNP),
`cutoffPowerLawDeficit` (LF50) and `cutoffPowerLawDerivative` (6YYS) follow.
-/

@[expose] public section
noncomputable section

open Filter Set
open scoped NNReal Topology
open PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K : ℝ → ℝ}

/-! ### General profiles -/

/-- Inside the cut-off, for a decreasing profile, `J_r(x, y) = K (N(x - y)) - K r`. -/
theorem coe_cutoffKernel_of_le {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    {r : ℝ} {x y : Fin d → ℤ}
    (hxy : x ≠ y) (h : N (Int.cast ∘ (x - y)) ≤ r) :
    (cutoffKernel N K r s(x, y) : ℝ) = K (N (Int.cast ∘ (x - y))) - K r := by
  have hs := N.intCast_comp_sub_pos hxy
  rw [cutoffKernel_def, radialKernel_of_ne hxy, ModelNorm.coe_toSeminorm, cutoffProfile_of_le h,
    Real.coe_toNNReal _ (sub_nonneg.2 (hKa hs (hs.trans_le h) h))]

/-- Outside the cut-off, `J_r(x, y) = 0`. -/
theorem cutoffKernel_of_lt {r : ℝ} {x y : Fin d → ℤ} (hxy : x ≠ y)
    (h : r < N (Int.cast ∘ (x - y))) :
    cutoffKernel N K r s(x, y) = 0 := by
  rw [cutoffKernel_def, radialKernel_of_ne hxy, cutoffProfile_of_lt h, Real.toNNReal_zero]

/-- **Limit in the scale.** If `K → 0` at infinity, then `J_r(e) → J(e)`. -/
theorem tendsto_cutoffKernel (hK : Tendsto K atTop (𝓝 0))
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r => cutoffKernel N K r e) atTop (𝓝 (radialKernel N K e)) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [cutoffKernel_def, radialKernel_diag]
      exact tendsto_const_nhds
    have hlim : Tendsto (fun r => (K (N (Int.cast ∘ (x - y))) - K r).toNNReal) atTop
        (𝓝 (K (N (Int.cast ∘ (x - y)))).toNNReal) := by
      have := (continuous_real_toNNReal.tendsto _).comp
        ((tendsto_const_nhds (x := K (N (Int.cast ∘ (x - y))))).sub hK)
      rw [sub_zero] at this
      exact this
    rw [radialKernel_of_ne hxy]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (N (Int.cast ∘ (x - y)))] with r hr
    rw [cutoffKernel_def, radialKernel_of_ne hxy, cutoffProfile_of_le hr]

/-- **The derivative in the scale off the corner.** If `K` is decreasing on `(0, ∞)` and has
derivative `-k` at `r ≠ N(x - y)`, then `d/dr J_r(x, y) = 1{N(x - y) < r} k`. -/
theorem hasDerivAt_cutoffKernel {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    {k r : ℝ}
    (hK : 0 < r → HasDerivAt K (-k) r) {x y : Fin d → ℤ} (hxy : x ≠ y)
    (hr : r ≠ N (Int.cast ∘ (x - y))) :
    HasDerivAt (fun r => (cutoffKernel N K r s(x, y) : ℝ))
      (if N (Int.cast ∘ (x - y)) < r then k else 0) r := by
  have hs := N.intCast_comp_sub_pos hxy
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · simp only [not_lt.2 hlt.le, ite_false]
    refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hlt] with r' hr'
    rw [cutoffKernel_of_lt hxy hr', NNReal.coe_zero]
  · simp only [hgt, ite_true]
    have hK' : HasDerivAt K (-k) r := hK (hs.trans hgt)
    have h := hK'.const_sub (K (N (Int.cast ∘ (x - y))))
    rw [neg_neg] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hgt] with r' hr'
    exact coe_cutoffKernel_of_le hKa hxy hr'.le

/-- **Chain rule for edge probabilities.** If `r ↦ J_r(e)` has derivative `D` at `r`, then
`r ↦ 1 - e^{-β J_r(e)}` has derivative `β e^{-β J_r(e)} D`. -/
theorem hasDerivAt_intensityProfile_of_hasDerivAt {V : Type*} (J : ℝ → Sym2 V → ℝ≥0)
    (β : ℝ≥0) (e : Sym2 V) {D r : ℝ} (h : HasDerivAt (fun r => (J r e : ℝ)) D r) :
    HasDerivAt (fun r => (intensityProfile (J r) β e : ℝ))
      (β * Real.exp (-(β : ℝ) * (J r e : ℝ)) * D) r := by
  have h2 := ((h.const_mul (-(β : ℝ))).exp).const_sub 1
  change HasDerivAt (fun r => 1 - Real.exp (-(β : ℝ) * (J r e : ℝ))) _ r
  convert h2 using 1
  ring

/-! ### The power law -/

/-- The derivative of the power law `s^{-a}/a` is `-s^{-a-1}` on `(0, ∞)`. -/
theorem hasDerivAt_powerLawProfile_inv {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (powerLawProfile (1 / a) a) (-(t ^ (-a - 1))) t := by
  have h := (Real.hasDerivAt_rpow_const (p := -a) (Or.inl ht.ne')).const_mul (1 / a)
  have h' : -(t ^ (-a - 1)) = 1 / a * (-a * t ^ (-a - 1)) := by field_simp
  rw [h']
  exact h

/-- **PVA8.** -/
@[tag "PVA8"]
theorem cutoffPowerLawFormula : CutoffPowerLawFormula := by
  intro d α N r x y hα hr hxy
  set a : ℝ := d + α
  have ha : 0 < a := by positivity
  have hs := N.intCast_comp_sub_pos hxy
  have hKa := antitoneOn_powerLawProfile (c := 1 / a) (by positivity) ha.le
  have hval : (cutoffKernel N (powerLawProfile (1 / a) a) r s(x, y) : ℝ) =
      max (N (Int.cast ∘ (x - y)) ^ (-a) - r ^ (-a)) 0 / a := by
    by_cases h : N (Int.cast ∘ (x - y)) ≤ r
    · rw [coe_cutoffKernel_of_le hKa hxy h, max_eq_left (sub_nonneg.2
        (Real.rpow_le_rpow_of_nonpos hs h (by linarith)))]
      simp only [powerLawProfile]
      ring
    · rw [cutoffKernel_of_lt hxy (not_le.1 h), NNReal.coe_zero, max_eq_right, zero_div]
      exact sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos hr (not_le.1 h).le (by linarith))
  refine ⟨?_, hval⟩
  rw [hval]
  split_ifs with h
  · rw [integral_rpow (Or.inr ⟨by linarith, fun h0 => ?_⟩), max_eq_left (sub_nonneg.2
      (Real.rpow_le_rpow_of_nonpos hs h (by linarith)))]
    · rw [show -a - 1 + 1 = -a by ring]
      field_simp
      ring
    · rw [uIcc_of_le h] at h0
      linarith [h0.1]
  · rw [max_eq_right (sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos hr (not_le.1 h).le
      (by linarith))), zero_div]

/-- **MQNP.** -/
@[tag "MQNP"]
theorem cutoffPowerLawMonotone : CutoffPowerLawMonotone := by
  intro d α N β e hα
  have ha : (0 : ℝ) < d + α := by positivity
  have hKa := antitoneOn_powerLawProfile (c := 1 / (d + α)) (by positivity) ha.le
  refine ⟨monotone_cutoffKernel hKa e, tendsto_cutoffKernel ?_ e, fun r r' h => ?_⟩
  · have := (tendsto_rpow_neg_atTop ha).const_mul (1 / ((d : ℝ) + α))
    rw [mul_zero] at this
    exact this
  · exact intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKa e h) β e

/-- **LF50.** -/
@[tag "LF50"]
theorem cutoffPowerLawDeficit : CutoffPowerLawDeficit := by
  intro d α N r x y hα hxy h
  have ha : (0 : ℝ) < d + α := by positivity
  have hs := N.intCast_comp_sub_pos hxy
  have hKa := antitoneOn_powerLawProfile (c := 1 / (d + α)) (by positivity) ha.le
  rw [coe_cutoffKernel_of_le hKa hxy h, coe_radialKernel_of_ne hxy
    (powerLawProfile_pos (by positivity) hs).le]
  simp only [powerLawProfile, ModelNorm.coe_toSeminorm]
  ring

/-- **6YYS.** -/
@[tag "6YYS"]
theorem cutoffPowerLawDerivative : CutoffPowerLawDerivative := by
  intro d α N β r x y hα hxy hr
  have ha : (0 : ℝ) < d + α := by positivity
  have hKa := antitoneOn_powerLawProfile (c := 1 / (d + α)) (by positivity) ha.le
  have hJ := hasDerivAt_cutoffKernel hKa (k := r ^ (-((d : ℝ) + α) - 1))
    (fun h0 => hasDerivAt_powerLawProfile_inv ha h0) hxy hr
  exact ⟨hJ, hasDerivAt_intensityProfile_of_hasDerivAt _ β _ hJ⟩

/-! ### Witnesses -/

/-- The cut-off power-law formula at `d = 1`, `α = 1`, the sup norm, `r = 2` and `N(x - y) = 1`: the
value is `(1 - 2^{-2})/2`. -/
example : (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile (1 / ((1 : ℕ) + 1))
    ((1 : ℕ) + 1)) 2 s(fun _ => 1, 0) : ℝ) = (1 - 2 ^ (-(2 : ℝ))) / 2 := by
  have h := (cutoffPowerLawFormula 1 1 (ModelNorm.ofNorm (Fin 1 → ℝ)) 2 (fun _ => 1) 0
    one_pos two_pos (fun h => by simpa using congrFun h 0)).2
  rw [ModelNorm.toSeminorm_ofNorm, ModelNorm.coe_ofNorm] at h
  rw [h, norm_intCast_comp, sub_zero]
  have hn : ‖(fun _ => (1 : ℤ) : Fin 1 → ℤ)‖ = 1 := by
    simp [Pi.norm_def]
  rw [hn, Real.one_rpow, max_eq_left (by
    have : (2 : ℝ) ^ (-(((1 : ℕ) : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    linarith)]
  norm_num

/-- The other three targets at the same parameters. -/
example (β : ℝ≥0) (e : Sym2 (Fin 1 → ℤ)) :
    Monotone (fun r => cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (powerLawProfile (1 / ((1 : ℕ) + 1)) ((1 : ℕ) + 1)) r e) :=
  (cutoffPowerLawMonotone 1 1 (ModelNorm.ofNorm (Fin 1 → ℝ)) β e one_pos).1

example : (radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (powerLawProfile (1 / ((1 : ℕ) + 1)) ((1 : ℕ) + 1)) s(fun _ => 1, 0) : ℝ) -
    cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (powerLawProfile (1 / ((1 : ℕ) + 1)) ((1 : ℕ) + 1)) 2 s(fun _ => 1, 0) =
    2 ^ (-(((1 : ℕ) : ℝ) + 1)) / (((1 : ℕ) : ℝ) + 1) :=
  cutoffPowerLawDeficit 1 1 (ModelNorm.ofNorm (Fin 1 → ℝ)) 2 (fun _ => 1) 0 one_pos
      (fun h => by simpa using congrFun h 0)
    (by simp [Pi.norm_def])

example (β : ℝ≥0) := cutoffPowerLawDerivative 1 1 (ModelNorm.ofNorm (Fin 1 → ℝ)) β 2
  (fun _ => 1) 0 one_pos (fun h => by simpa using congrFun h 0)
  (by simp [Pi.norm_def])

end PercLib.Models.LongRange
