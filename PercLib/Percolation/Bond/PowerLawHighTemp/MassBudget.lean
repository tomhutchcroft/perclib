/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New material, no old-source migration: the quantitative mass budget `M` of the summable
power-law profile on `ℤ^d`, its exactness as a row mass, its behaviour in the exponent, and the
resulting explicit high-temperature parameter interval.

Reused without restatement (all Apache-2.0):

* `PercLib.Models.LongRange.tsum_ofReal_powerLaw_bounds` and
  `PercLib.Models.LongRange.tsum_ite_rpow_le`, in `PercLib/Models/LongRange/PowerLaw.lean`,
  adapted there from repository `yujinhkim/lrp` at source revision
  `6953cfc748205d5589dd0ed17f79afff0d44b2d7`;
* `PercLib.Percolation.Bond.Exploration.BFS.summable_norm_pow`, `...power_rowSum_le`,
  `...power_lintegral_encard_cluster_pow_ne_top`, in
  `PercLib/Percolation/Bond/Exploration/BFS/IntensityMoments.lean` and
  `PercLib/Percolation/Bond/PowerLawHighTemp/Tail.lean`.

This is a proof-only module: it introduces no definition, no configuration model and no
namespace. Nothing is asserted at `β M = 1`, at `β_c`, about sharpness or about a limit.

Source comparison.  The source-level facts `powerMass_nonneg` and `ofReal_powerMass_eq_coe` are
already landed in `PowerLawHighTemp/Tail.lean` and are only used, not restated.  The source's
`powerProfile_antitone` (the radial profile `t ↦ t^{-s}` is antitone on `t > 0`) and
`tsum_toNNReal_powerProfile_eq` (the profile-level mass identity, `PowerLawHighTemp.lean`,
revision `6953cfc748205d5589dd0ed17f79afff0d44b2d7`) are **not** migrated in production and are
neither restated nor claimed here.  The statements below about the mass as a function of the
exponent, the row-level equality with the mass, the explicit budget and the interval structure
have no source counterpart.
-/
module

public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail

/-!
# The mass budget of the summable power-law profile

The high-temperature statements for the power-law model are all of the form "if `β M < 1`",
where `M = ∑_z ‖z‖^{-d-α}` is the mass of the profile.  This file supplies the properties of
`M` that make that hypothesis usable:

* `powerMass_le_explicit`: an explicit budget, `M ≤ 2·d·3^(d-1)·(1 + 1/α)`, so the parameter
  interval can be written with a computable endpoint instead of the infinite sum;
* `one_le_powerMass`: `1 ≤ M`, hence the admitted intensities never exceed `1`;
* `powerMass_antitone`: `M` decreases as the exponent grows, so the admitted interval grows;
* `mul_coe_lt_one_iff_lt_inv`: for `M ≠ 0` the hypothesis `β M < 1` is exactly `β < M⁻¹`, and
  `highTempRegion_downward`: the admitted set is a down-set;
* `power_lintegral_encard_cluster_pow_ne_top_of_mass_le` and
  `exists_beta_interval_powerLaw_explicit`: the moment theorem at an explicit endpoint.

Nothing here is a critical, cutoff or sharpness statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Probability
open scoped ENNReal NNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

/-! ## The mass in the guarded and unguarded presentations -/

/-- The `ℝ≥0∞`-sum of the guarded power-law profile is the `ofReal` of the unguarded real mass:
at the origin both are zero. -/
theorem ofReal_tsum_pow_eq_tsum_if {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) =
      ∑' z : Fin d → ℤ,
        ENNReal.ofReal (if z = 0 then (0 : ℝ) else (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _)
    (summable_norm_pow hd hα)]
  refine tsum_congr fun z => ?_
  by_cases h : z = 0
  · subst h
    rw [ite_eq_left rfl, norm_zero, Real.zero_rpow (neg_add_ne_zero hα)]
  · rw [ite_eq_right h]

/-- **Explicit mass budget.**  The total mass of the summable power-law profile on `ℤ^d` is at
most the explicit number `2·d·3^(d-1)·(1 + 1/α)` for every `α > 0` and `d ≥ 1`.  It is a
consequence of the two-sided comparison `tsum_ofReal_powerLaw_bounds` with the `p`-series and of
the explicit `p`-series bound `tsum_ite_rpow_le`. -/
theorem powerMass_le_explicit {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) ≤
      ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) := by
  have hps : (∑' n : ℕ, ENNReal.ofReal (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α)))) ≤
      ENNReal.ofReal (1 + 1 / α) := by
    have h := PercLib.Models.LongRange.tsum_ite_rpow_le α hα (r := 1) le_rfl
    rw [Real.one_rpow, mul_one] at h
    have heq : (∑' n : ℕ, ENNReal.ofReal (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α)))) =
        ∑' n : ℕ,
          ENNReal.ofReal (if (1 : ℝ) ≤ (n : ℝ) then (n : ℝ) ^ (-(1 + α)) else 0) := by
      refine tsum_congr fun n => ?_
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        rw [ite_eq_left rfl, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ ((0 : ℕ) : ℝ))]
      · rw [ite_eq_right hn, ite_eq_left (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)]
    rw [heq]
    exact h
  have hmain : (∑' z : Fin d → ℤ,
        ENNReal.ofReal (if z = 0 then (0 : ℝ) else (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) ≤
      ENNReal.ofReal (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) := by
    refine ((PercLib.Models.LongRange.tsum_ofReal_powerLaw_bounds hd α).2).trans ?_
    calc ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) *
          (∑' n : ℕ, ENNReal.ofReal (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + α))))
        ≤ ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 1 / α) := by
          gcongr
      _ = ENNReal.ofReal (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [← ofReal_tsum_pow_eq_tsum_if hd hα] at hmain
  rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain

/-- The explicit budget is positive. -/
theorem powerMassBudget_pos {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    0 < ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) := by
  have h2 : (0 : ℝ) < ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) := by
    have : 0 < 2 * d * 3 ^ (d - 1) := by positivity
    exact_mod_cast this
  have h1 : (0 : ℝ) < 1 + 1 / α := by positivity
  exact mul_pos h2 h1

/-! ## The mass is at least one -/

/-- **The mass is at least one.**  A unit vector contributes `1^(-d-α) = 1` to the profile, so
`M ≥ 1` in every dimension.  Consequently the admitted intensities `β < M⁻¹` are `≤ 1`. -/
theorem one_le_powerMass {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    1 ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) := by
  classical
  set i : Fin d := ⟨0, hd⟩ with hi
  set z₀ : Fin d → ℤ := Pi.single i (1 : ℤ) with hz₀
  have hne : z₀ ≠ 0 := by
    intro h
    have h1 : z₀ i = (1 : ℤ) := by rw [hz₀]; exact Pi.single_eq_same i 1
    rw [h] at h1
    simp at h1
  have hnat : ∀ j : Fin d, (z₀ j).natAbs ≤ 1 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [hz₀, Pi.single_eq_same]
      simp
    · rw [hz₀, Pi.single_eq_of_ne hj]
      simp
  have hupper : ‖z₀‖ ≤ (1 : ℝ) := by
    simpa using (PercLib.Models.LongRange.norm_le_natCast_iff z₀ 1).2 hnat
  have hnorm : ‖z₀‖ = 1 := le_antisymm hupper (PercLib.Models.LongRange.one_le_norm_of_ne_zero hne)
  have hsum := summable_norm_pow hd hα
  have h := hsum.sum_le_tsum ({z₀} : Finset (Fin d → ℤ))
    (fun z _ => Real.rpow_nonneg (norm_nonneg z) _)
  rw [Finset.sum_singleton, hnorm, Real.one_rpow] at h
  exact h

/-- The mass of the summable power-law profile is positive. -/
theorem powerMass_pos {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    0 < ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) :=
  lt_of_lt_of_le zero_lt_one (one_le_powerMass hd hα)

/-! ## Behaviour of the mass in the exponent -/

/-- **The mass decreases as the exponent grows.**  Every lattice point other than the origin has
`‖z‖ ≥ 1`, so raising the exponent can only decrease the profile pointwise; both sides are
summable by `summable_norm_pow`. -/
theorem powerMass_antitone {d : ℕ} (hd : 1 ≤ d) {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα : α₁ ≤ α₂) :
    (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂))) ≤
      ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₁)) := by
  have hα₂ : 0 < α₂ := lt_of_lt_of_le hα₁ hα
  refine Summable.tsum_le_tsum (fun z => ?_) (summable_norm_pow hd hα₂) (summable_norm_pow hd hα₁)
  by_cases hz : z = 0
  · subst hz
    rw [norm_zero, Real.zero_rpow (x := -((d : ℝ) + α₂)) (neg_add_ne_zero hα₂),
      Real.zero_rpow (x := -((d : ℝ) + α₁)) (neg_add_ne_zero hα₁)]
  · exact Real.rpow_le_rpow_of_exponent_le
      (PercLib.Models.LongRange.one_le_norm_of_ne_zero hz) (by linarith)

/-- **The high-temperature hypothesis transfers to every larger exponent.**  If `β M < 1` holds
at the exponent `d + α₁` then it holds at `d + α₂` for every `α₂ ≥ α₁`, because the mass can only
decrease.  This is what makes "the admitted intensity interval grows with the exponent" precise;
the percolation statements themselves are not restated here. -/
theorem mul_powerMass_lt_one_of_le_exponent {d : ℕ} (hd : 1 ≤ d) {α₁ α₂ : ℝ}
    (hα₁ : 0 < α₁) (hα : α₁ ≤ α₂) {β : ℝ≥0}
    (hβ : (β : ℝ) * (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₁))) < 1) :
    (β : ℝ) * (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂))) < 1 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left (powerMass_antitone hd hα₁ hα) β.coe_nonneg) hβ

/-! ## The admitted intensity set is the interval `[0, M⁻¹)` -/

/-- For a nonzero mass, the high-temperature hypothesis is exactly the interval condition
`β < M⁻¹`, in the `ℝ≥0∞` form in which it is consumed by the moment and tail theorems. -/
theorem mul_coe_lt_one_iff_lt_inv {M β : ℝ≥0} (hM : M ≠ 0) :
    (β : ℝ≥0∞) * (M : ℝ≥0∞) < 1 ↔ β < M⁻¹ := by
  rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff, NNReal.lt_inv_iff_mul_lt hM]

/-- The admitted intensity set of a nonzero mass is the down-set `{β | β < M⁻¹}`; in particular
it is an interval of intensities, not an arbitrary set. -/
theorem highTempRegion_eq_Iio {M : ℝ≥0} (hM : M ≠ 0) :
    {β : ℝ≥0 | (β : ℝ≥0∞) * (M : ℝ≥0∞) < 1} = Set.Iio M⁻¹ := by
  ext β
  exact mul_coe_lt_one_iff_lt_inv hM

/-- The admitted intensity set is downward closed. -/
theorem highTempRegion_downward {M : ℝ≥0} {β β' : ℝ≥0} (h : β' ≤ β)
    (hβ : (β : ℝ≥0∞) * (M : ℝ≥0∞) < 1) : (β' : ℝ≥0∞) * (M : ℝ≥0∞) < 1 := by
  refine lt_of_le_of_lt ?_ hβ
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.2 (mul_le_mul_of_nonneg_right h M.coe_nonneg)

/-- A mass of at least one forces every admitted intensity to be below one.  This bounds the
hypothesis, not the model: nothing is asserted about percolation at `β ≥ 1`. -/
theorem coe_lt_one_of_one_le_mass {M β : ℝ≥0} (hM : 1 ≤ M)
    (hβ : (β : ℝ≥0∞) * (M : ℝ≥0∞) < 1) : β < 1 := by
  have hle : (β : ℝ≥0∞) ≤ (β : ℝ≥0∞) * (M : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
    calc β = β * 1 := (mul_one β).symm
      _ ≤ β * M := mul_le_mul_of_nonneg_left hM β.coe_nonneg
  exact ENNReal.coe_lt_one_iff.1 (lt_of_le_of_lt hle hβ)

/-- **The power law's admitted intensities are all below one**: `1 ≤ M` for every `α > 0`, so
`β M < 1` already forces `β < 1`. -/
theorem power_coe_lt_one_of_highTemp {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) : β < 1 := by
  refine coe_lt_one_of_one_le_mass ?_ hβ
  have h := one_le_powerMass hd hα
  calc (1 : ℝ≥0) = Real.toNNReal 1 := (Real.toNNReal_one).symm
    _ ≤ Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) :=
        Real.toNNReal_le_toNNReal h

/-! ## The mass is exactly the row mass -/

/-- Shifting the power-law profile by a vertex does not change its total mass. -/
theorem tsum_norm_pow_sub_eq {d : ℕ} (v : Fin d → ℤ) {s : ℝ} :
    (∑' w : Fin d → ℤ, (‖w - v‖ : ℝ) ^ (-s)) = ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s) := by
  rw [← (Equiv.addRight v).tsum_eq (fun w : Fin d → ℤ => (‖w - v‖ : ℝ) ^ (-s))]
  exact tsum_congr fun z => by
    simp only [Equiv.coe_addRight]
    rw [add_sub_cancel_right]

/-- **The row mass of the power-law profile equals its total mass** — the inequality
`power_rowSum_le` is an equality.  The full row sum, diagonal included, is exactly
`M = ∑_z ‖z‖^{-s}`, since the diagonal term vanishes.  Consequently the hypothesis `β M < 1`
is a condition on the actual row mass and not on a convenient upper bound. -/
theorem power_rowSum_eq_powerMass {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    (v : Fin d → ℤ) :
    (∑' w : Fin d → ℤ, (J s(v, w) : ℝ≥0∞)) =
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
  have hs0 : (0 : ℝ) < s := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hsum : Summable fun z : Fin d → ℤ => (‖z‖ : ℝ) ^ (-s) := by
    have h := (PercLib.Models.LongRange.summable_powerLaw_iff hd (s - d)).2 (by linarith)
    refine h.congr fun z => ?_
    rw [show -((d : ℝ) + (s - d)) = -s by ring]
    by_cases hz : z = 0
    · subst hz
      rw [ite_eq_left rfl, norm_zero, Real.zero_rpow (x := -s) (by linarith)]
    · rw [ite_eq_right hz]
  have hnonneg : 0 ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s) :=
    tsum_nonneg fun z => Real.rpow_nonneg (norm_nonneg z) _
  have hterm : ∀ w : Fin d → ℤ, (J s(v, w) : ℝ≥0∞) = ENNReal.ofReal ((‖w - v‖ : ℝ) ^ (-s)) := by
    intro w
    have hx0 : 0 ≤ (‖w - v‖ : ℝ) ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    rw [hJ v w]
    exact (ENNReal.ofReal_coe_nnreal
      (p := Real.toNNReal ((‖w - v‖ : ℝ) ^ (-s)))).symm.trans (by rw [Real.coe_toNNReal _ hx0])
  calc (∑' w : Fin d → ℤ, (J s(v, w) : ℝ≥0∞))
      = ∑' w : Fin d → ℤ, ENNReal.ofReal ((‖w - v‖ : ℝ) ^ (-s)) := tsum_congr hterm
    _ = ∑' z : Fin d → ℤ, ENNReal.ofReal ((‖z‖ : ℝ) ^ (-s)) := by
        rw [← (Equiv.addRight v).tsum_eq
          (fun w : Fin d → ℤ => ENNReal.ofReal ((‖w - v‖ : ℝ) ^ (-s)))]
        exact tsum_congr fun z => by
          simp only [Equiv.coe_addRight]
          rw [add_sub_cancel_right]
    _ = ENNReal.ofReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _) hsum).symm
    _ = ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal
            (p := Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s))),
          Real.coe_toNNReal _ hnonneg]

/-- **The `rowSum` of the power-law intensity is exactly the mass.**  The library's guarded row sum
drops the diagonal, which vanishes for the power law, so the value is again `M` rather than only
bounded by it. -/
theorem rowSum_power_eq_powerMass {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    (v : Fin d → ℤ) :
    rowSum (fun e => (J e : ℝ≥0∞)) v =
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
  have hs0 : (0 : ℝ) < s := by linarith [Nat.cast_nonneg (α := ℝ) d]
  rw [rowSum_def]
  refine (tsum_congr fun w => ?_).trans (power_rowSum_eq_powerMass hd hs hJ v)
  by_cases h : w = v
  · rw [ite_eq_left h, h, hJ v v, sub_self, norm_zero,
      Real.zero_rpow (x := -s) (by linarith), Real.toNNReal_zero]
    rfl
  · rw [ite_eq_right h]
/-! ## The explicit-endpoint consequences -/

/-- The explicit mass budget converts into the `ℝ≥0∞`-form high-temperature hypothesis that the
moment and tail theorems consume. -/
theorem power_mul_mass_lt_one_of_mass_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) < 1) :
    (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hMnn : (0 : ℝ) ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) :=
    tsum_nonneg fun z => Real.rpow_nonneg (norm_nonneg z) _
  have hmul : (β : ℝ) * (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (powerMass_le_explicit hd hα) β.coe_nonneg) hβ
  have hcoele : (β * Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_one, Real.coe_toNNReal _ hMnn]
    exact hmul
  rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
  exact hcoele

/-- For a positive intensity the real mass parameter `(β M).toReal` is positive.  The landed tail
theorem `exists_lam_law_cluster_encard_ge_le_powerLaw` assumes this separately; here it follows
from `β > 0` and `M > 0`. -/
theorem power_mass_mul_toReal_pos {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβpos : 0 < β) :
    0 < ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal := by
  have hMpos : 0 < Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) :=
    Real.toNNReal_pos.2 (powerMass_pos hd hα)
  have hne0 : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.coe_mul]
    exact ENNReal.coe_ne_zero.2 (mul_ne_zero hβpos.ne' hMpos.ne')
  have htop : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.coe_mul]
    exact ENNReal.coe_ne_top
  exact ENNReal.toReal_pos hne0 htop

/-- **Every natural cluster moment is finite under the explicit mass budget.**  The hypothesis is
the computable condition `β · 2·d·3^(d-1)·(1 + 1/α) < 1` instead of the infinite sum: the same
conclusion as `power_lintegral_encard_cluster_pow_ne_top`, from a sufficient explicit condition. -/
theorem power_lintegral_encard_cluster_pow_ne_top_of_mass_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ :=
  power_lintegral_encard_cluster_pow_ne_top hd hα
    (power_mul_mass_lt_one_of_mass_le hd hα hβ) x k

/-- **Every natural cluster moment is finite throughout the interval `[0, M⁻¹)` of the exact
mass.**  The endpoint is the exact one, not a sufficient bound: the whole set of intensities on
which the landed hypothesis `β M < 1` holds is `Set.Iio M⁻¹`. -/
theorem power_lintegral_encard_cluster_pow_ne_top_of_lt_inv {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : β < (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))))⁻¹)
    (x : Fin d → ℤ) (k : ℕ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  have hM0 : Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) ≠ 0 :=
    (Real.toNNReal_pos.2 (powerMass_pos hd hα)).ne'
  exact power_lintegral_encard_cluster_pow_ne_top hd hα
    ((mul_coe_lt_one_iff_lt_inv hM0).2 hβ) x k

/-- **A positive interval of parameters with an explicit endpoint.**  Every natural cluster moment
is finite for every `β < (2·d·3^(d-1)·(1 + 1/α) + 1)⁻¹`; this is the explicit-endpoint form of
`exists_beta_interval_powerLaw_encard_cluster_pow_ne_top`, whose endpoint is the infinite sum. -/
theorem exists_beta_interval_powerLaw_explicit {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (x : Fin d → ℤ) (k : ℕ),
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  have hB0 : (0 : ℝ) ≤ ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) :=
    (powerMassBudget_pos hd hα).le
  refine ⟨(Real.toNNReal (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) + 1)⁻¹,
    inv_pos.mpr (by positivity), ?_⟩
  intro β hβ x k
  have h := mul_lt_one_of_lt_inv_add_one hβ
  rw [Real.coe_toNNReal _ hB0] at h
  exact power_lintegral_encard_cluster_pow_ne_top_of_mass_le hd hα h x k

/-- **The exponential cluster tail under the explicit mass budget.**  The landed tail theorem
`exists_lam_law_cluster_encard_ge_le_powerLaw` with its hypothesis replaced by the computable
condition and its positivity assumption on `(β M).toReal` derived from `β > 0`. -/
theorem exists_lam_law_cluster_encard_ge_le_powerLaw_of_mass_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0} (hβpos : 0 < β)
    (hβ : (β : ℝ) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) < 1)
    (x : Fin d → ℤ) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤
        ENNReal.ofReal (1 / ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ :=
  exists_lam_law_cluster_encard_ge_le_powerLaw hd hα
    (power_mul_mass_lt_one_of_mass_le hd hα hβ)
    (power_mass_mul_toReal_pos hd hα hβpos) x

/-- **A positive interval of parameters with an explicit endpoint for the cluster tail.**  For
every `0 < β < (2·d·3^(d-1)·(1 + 1/α) + 1)⁻¹` there is `lam > 1` with the exponential tail bound
at every natural index and every root.  Nothing is asserted at or beyond the endpoint. -/
theorem exists_beta_interval_powerLaw_tail_explicit {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℤ) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, 0 < β → β < β₀ → ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤
        ENNReal.ofReal (1 / ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  have hB0 : (0 : ℝ) ≤ ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) :=
    (powerMassBudget_pos hd hα).le
  refine ⟨(Real.toNNReal (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α)) + 1)⁻¹,
    inv_pos.mpr (by positivity), ?_⟩
  intro β hβpos hβ
  have h := mul_lt_one_of_lt_inv_add_one hβ
  rw [Real.coe_toNNReal _ hB0] at h
  exact exists_lam_law_cluster_encard_ge_le_powerLaw_of_mass_le hd hα hβpos h x

/-! ## A numeric instance -/

/-- **A fully explicit non-vacuity witness.**  In one dimension with exponent `d + α = 2` the
budget is `2·1·3⁰·(1 + 1) = 4`, so every `β < 1/5` is admitted; at `β = 1/8` every natural
cluster moment is finite.  This is a compiled witness that the explicit interval is nonempty and
computable. -/
example (x : Fin 1 → ℤ) (k : ℕ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 (((1 : ℕ) : ℝ) + 1)))
        (1 / 8 : ℝ≥0))) ≠ ⊤ := by
  refine power_lintegral_encard_cluster_pow_ne_top_of_mass_le (d := 1) le_rfl
    (α := 1) one_pos ?_ x k
  norm_num
/-! ## Strict growth of the admitted interval -/

/-- The vector with a single `2` has sup norm strictly larger than one; this is the point at which
raising the exponent strictly decreases the profile. -/
theorem one_lt_norm_single_two {d : ℕ} (hd : 1 ≤ d) :
    1 < ‖(Pi.single (⟨0, hd⟩ : Fin d) (2 : ℤ) : Fin d → ℤ)‖ := by
  by_cases h : ‖(Pi.single (⟨0, hd⟩ : Fin d) (2 : ℤ) : Fin d → ℤ)‖ ≤ (1 : ℝ)
  · exfalso
    have hu : ‖(Pi.single (⟨0, hd⟩ : Fin d) (2 : ℤ) : Fin d → ℤ)‖ ≤ ((1 : ℕ) : ℝ) := by
      simpa using h
    have h2 := (PercLib.Models.LongRange.norm_le_natCast_iff
      (Pi.single (⟨0, hd⟩ : Fin d) (2 : ℤ)) 1).1 hu ⟨0, hd⟩
    rw [Pi.single_eq_same] at h2
    simp at h2
  · exact not_le.1 h

/-- **The mass strictly decreases as the exponent grows.**  At the vector with a single `2` the
profile strictly decreases, and it weakly decreases everywhere else, so the sums are strictly
ordered by `Summable.tsum_lt_tsum`.  Consequently the admitted interval strictly grows with the
exponent. -/
theorem powerMass_strictAnti {d : ℕ} (hd : 1 ≤ d) {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα : α₁ < α₂) :
    (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂))) <
      ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₁)) := by
  have hα₂ : 0 < α₂ := lt_trans hα₁ hα
  have hgt := one_lt_norm_single_two hd
  have hle : ∀ z : Fin d → ℤ,
      (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂)) ≤ (‖z‖ : ℝ) ^ (-((d : ℝ) + α₁)) := by
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [norm_zero, Real.zero_rpow (x := -((d : ℝ) + α₂)) (neg_add_ne_zero hα₂),
        Real.zero_rpow (x := -((d : ℝ) + α₁)) (neg_add_ne_zero hα₁)]
    · exact Real.rpow_le_rpow_of_exponent_le
        (PercLib.Models.LongRange.one_le_norm_of_ne_zero hz) (by linarith)
  have hstrict : (‖(Pi.single (⟨0, hd⟩ : Fin d) (2 : ℤ) : Fin d → ℤ)‖ : ℝ) ^ (-((d : ℝ) + α₂)) <
      (‖(Pi.single (⟨0, hd⟩ : Fin d) (2 : ℤ) : Fin d → ℤ)‖ : ℝ) ^ (-((d : ℝ) + α₁)) := by
    rw [Real.rpow_lt_rpow_left_iff hgt]
    linarith
  exact Summable.tsum_lt_tsum hle hstrict (summable_norm_pow hd hα₂) (summable_norm_pow hd hα₁)

/-- **The high-temperature threshold strictly grows with the exponent.**  Since the mass is
positive and strictly decreasing in the exponent, its reciprocal `M⁻¹` is strictly increasing:
for larger `d + α` strictly more intensities satisfy `β M < 1`. -/
theorem powerMass_inv_strictMono {d : ℕ} (hd : 1 ≤ d) {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα : α₁ < α₂) :
    (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₁)))⁻¹ <
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂)))⁻¹ := by
  have h₂ : (0 : ℝ) < ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂)) :=
    powerMass_pos hd (lt_trans hα₁ hα)
  have h := one_div_lt_one_div_of_lt h₂ (powerMass_strictAnti hd hα₁ hα)
  simpa only [one_div] using h

/-- **The admitted intensity set strictly grows with the exponent**: as a set of real intensities
the high-temperature region at the larger exponent strictly contains the region at the smaller
one.  This is the interval form of `powerMass_inv_strictMono`. -/
theorem highTempRegion_powerMass_ssubset {d : ℕ} (hd : 1 ≤ d) {α₁ α₂ : ℝ} (hα₁ : 0 < α₁)
    (hα : α₁ < α₂) :
    Set.Iio (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₁)))⁻¹ ⊂
      Set.Iio (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α₂)))⁻¹ :=
  Set.Iio_ssubset_Iio (powerMass_inv_strictMono hd hα₁ hα)

end PercLib.Percolation.Bond.Exploration.BFS
