/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, supplied under its Apache-2.0 header:
* `PercLib/CriticalLRP/PowerLawHighTemp/Tail.lean`, source revision
  `4a8819bfb7779ac3ff9bf079a8f8edc0a6b19536`;
* `PercLib/CriticalLRP/PowerLawHighTemp/Moments.lean`, source revision
  `7802b33d22f7516ab155005e8526d0b4264ad855`;
* the row-sum and scalar-profile section of `PercLib/CriticalLRP/PowerLawHighTemp.lean`,
  source revision `6953cfc748205d5589dd0ed17f79afff0d44b2d7`.

The canonical namespace is `PercLib.Percolation.Bond.Exploration.BFS`. The paper's `lrKernel`
is presented by `Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
(powerLawProfile 1 (d + α))`; its `linfNorm` is the corresponding sup norm on `Fin d → ℤ`.
The source abbreviation `clusterVol` is written as `((cluster ω x).encard : ℝ≥0∞)`.
The ordinary full-row bound already proved in `IntensityMoments` is reused rather than copied.
Forbidden source options are omitted; `Classical.propDecidable` remains local for the source's
explicit guarded row sums.

The legacy `longRangeMeasure`/`latticeLongRangeMeasure`, `kernelJ`, and cutoff declarations are
not migrated here. No statement is made at `β_c`, at `β M ≥ 1`, about sharpness, or about a
limit `n → ∞`. This is a proof-only module.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.IntensityMoments
public import PercLib.Percolation.Bond.HighTemperatureTail
public import PercLib.Models.LongRange.Defs
public import PercLib.Models.LongRange.PowerLaw

/-!
# High-temperature tails and moments for the power-law model

Specialise the generic high-temperature estimates to the power-law kernel on `Fin d → ℤ`. Its
row sums are bounded by the finite mass `M = ∑' z, ‖z‖ ^ (-(d + α))`. Consequently, when
`β M < 1`, all natural moments of the genuine infinite-lattice cluster are finite at every root;
when its real value is positive, the cluster-volume tail is bounded by an exponential in `n : ℕ`.
A positive parameter interval guarantees that these hypotheses are non-vacuous.

## Main results

* `power_lintegral_encard_cluster_pow_ne_top` and its simultaneous and interval forms;
* `exists_lam_law_cluster_encard_ge_le_powerLaw`, the exponential tail bound;
* `intensityProfile_powerLaw_coe`, identifying the open-edge probability with the source model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

namespace PercLib.Percolation.Bond.Exploration.BFS

/-! ## The power-law kernel in the production presentation -/

/-- Value of the production power-law radial kernel off the diagonal: the source's
`PowerLawHighTemp.lrKernel_mk_eq_linfNorm` in production notation. -/
theorem radialKernel_powerLaw_coe {d : ℕ} {α : ℝ} {x y : Fin d → ℤ} (h : x ≠ y) :
    (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(x, y) : ℝ)
      = (‖y - x‖ : ℝ) ^ (-((d : ℝ) + α)) := by
  have hK : (0 : ℝ) ≤ PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)
      (normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y))) := by
    rw [PercLib.Models.LongRange.powerLawProfile, one_mul,
      PercLib.Models.LongRange.normSeminorm_intCast]
    positivity
  rw [PercLib.Models.LongRange.coe_radialKernel_of_ne (N := normSeminorm ℝ (Fin d → ℝ))
    (K := PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) h hK]
  simp only [PercLib.Models.LongRange.powerLawProfile, one_mul,
    PercLib.Models.LongRange.normSeminorm_intCast, norm_sub_rev]

/-- The production power-law radial kernel has the displacement profile of the source's
`lrKernel d α`, on every pair including the diagonal. -/
theorem radialKernel_powerLaw_mk {d : ℕ} {α : ℝ} (hα : 0 < α) (x y : Fin d → ℤ) :
    PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(x, y)
      = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))) := by
  by_cases h : x = y
  · subst h
    rw [PercLib.Models.LongRange.radialKernel_diag, sub_self, norm_zero,
      Real.zero_rpow (by linarith : -((d : ℝ) + α) ≠ 0), Real.toNNReal_zero]
  · rw [PercLib.Models.LongRange.radialKernel_of_ne
      (N := normSeminorm ℝ (Fin d → ℝ)) (K :=
        PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) h]
    congr 1
    simp only [PercLib.Models.LongRange.powerLawProfile, one_mul,
      PercLib.Models.LongRange.normSeminorm_intCast, norm_sub_rev]

/-! ## The row-sum bound for the summable power-law kernel -/

/-- The paper's exponent is nonzero, so `0 ^ (-d-α) = 0`. -/
theorem neg_add_ne_zero {d : ℕ} {α : ℝ} (hα : 0 < α) : -((d : ℝ) + α) ≠ 0 := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

/-- `ENNReal.ofReal` of a nonnegative real is the coercion of its `ℝ≥0` truncation. -/
theorem ofReal_eq_coe_toNNReal {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x = (Real.toNNReal x : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_coe_nnreal (p := Real.toNNReal x), Real.coe_toNNReal x hx]

/-- The profile `z ↦ ‖z‖_∞^{-d-α}` has the same sum with and without the `if z = 0` guard of
the production summability statement: at `0` the value is `0^{-d-α} = 0`. -/
theorem tsum_if_zero_norm_pow_eq {d : ℕ} {α : ℝ} (hα : 0 < α) :
    (∑' z : Fin d → ℤ, (if z = 0 then (0 : ℝ) else (‖z‖ : ℝ) ^ (-((d : ℝ) + α))))
      = ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) := by
  refine tsum_congr fun z => ?_
  by_cases hz : z = 0
  · subst hz
    simp only [↓reduceIte, norm_zero]
    exact (Real.zero_rpow (neg_add_ne_zero hα)).symm
  · simp [hz]

/-- **Summability of the power-law profile on `ℤ^d` for `α > 0`**, in the unguarded form used
by the source; `PercLib.Models.LongRange.summable_powerLaw_iff` is the guarded form. -/
theorem summable_norm_pow {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    Summable (fun z : Fin d → ℤ => (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) := by
  refine ((PercLib.Models.LongRange.summable_powerLaw_iff hd α).2 hα).congr fun z => ?_
  by_cases hz : z = 0
  · subst hz
    simp only [↓reduceIte, norm_zero]
    exact (Real.zero_rpow (neg_add_ne_zero hα)).symm
  · simp [hz]

/-! ## The power-law profile, restated over the production sup norm -/

/-- The power-law profile `‖z‖_∞^{-s}` is nonnegative (source `powerProfile_nonneg`). -/
theorem powerProfile_nonneg {d : ℕ} {s : ℝ} (z : Fin d → ℤ) :
    0 ≤ (‖z‖ : ℝ) ^ (-s) :=
  Real.rpow_nonneg (norm_nonneg z) _

/-- The power-law profile is even, so it defines a symmetric pair intensity (source
`powerProfile_even`). -/
theorem powerProfile_even {d : ℕ} (s : ℝ) :
    ∀ x : Fin d → ℤ,
      (fun y : Fin d → ℤ => (‖y‖ : ℝ) ^ (-s)) (-x)
        = (fun y : Fin d → ℤ => (‖y‖ : ℝ) ^ (-s)) x := by
  intro x
  change (‖-x‖ : ℝ) ^ (-s) = (‖x‖ : ℝ) ^ (-s)
  rw [norm_neg]

/-- The total mass of the power-law profile is nonnegative (source
`powerMass_nonneg`). -/
theorem powerMass_nonneg {d : ℕ} {s : ℝ} :
    0 ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s) :=
  tsum_nonneg fun z => powerProfile_nonneg z

/-- The mass of the power-law profile as an `ℝ≥0∞`, in the row-sum form
(source `ofReal_powerMass_eq_coe`). -/
theorem ofReal_powerMass_eq_coe {d : ℕ} {s : ℝ} :
    ENNReal.ofReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s))
      = ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) :=
  ofReal_eq_coe_toNNReal (powerMass_nonneg (d := d) (s := s))

/-! ## The scalar interval comparison -/

/-- Elementary scalar comparison: `β < (M + 1)⁻¹` forces `β M < 1`, in `ℝ` (source
`mul_lt_one_of_lt_inv_add_one`). -/
theorem mul_lt_one_of_lt_inv_add_one {M β : ℝ≥0} (hβ : β < (M + 1)⁻¹) :
    (β : ℝ) * (M : ℝ) < 1 := by
  rcases eq_or_lt_of_le M.coe_nonneg with h0 | hpos
  · rw [← h0, mul_zero]
    norm_num
  · have hβr : (β : ℝ) < ((M : ℝ) + 1)⁻¹ := by
      have h' : (β : ℝ) < (((M + 1)⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.mpr hβ
      rwa [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one] at h'
    have hstep : (β : ℝ) * (M : ℝ) < ((M : ℝ) + 1)⁻¹ * (M : ℝ) :=
      mul_lt_mul_of_pos_right hβr hpos
    have hlt : ((M : ℝ) + 1)⁻¹ * (M : ℝ) < 1 := by
      rw [inv_mul_eq_div, div_lt_one (by linarith)]
      linarith
    linarith

/-- The same comparison in the `ℝ≥0∞` form used by the moment theorem (source
`mul_coe_lt_one_of_lt_inv_add_one`). -/
theorem mul_coe_lt_one_of_lt_inv_add_one {M β : ℝ≥0} (hβ : β < (M + 1)⁻¹) :
    (β : ℝ≥0∞) * (M : ℝ≥0∞) < 1 := by
  rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, NNReal.coe_one]
  exact mul_lt_one_of_lt_inv_add_one hβ

/-! ## The generic intensity tail bound -/

/-- A positive nonzero high-temperature interval always admits an exponential cluster-tail
bound.  Exact source statement of `PowerLawHighTemp/Tail.lean`
(`exists_lam_measure_cluster_encard_ge_le_intensityProfile`). -/
theorem exists_lam_measure_cluster_encard_ge_le_intensityProfile {V : Type*} [Countable V]
    (J : Sym2 V → ℝ≥0)
    (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (hm : 0 < ((β : ℝ≥0∞) * M).toReal) (o : V) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (law (intensityProfile J β)) {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
        ENNReal.ofReal (1 / (((β : ℝ≥0∞) * M).toReal)) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  let m := ((β : ℝ≥0∞) * M).toReal
  have hJcanon : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M := by
    intro v
    rw [rowSum_def]
    exact hJ v
  have hrow : UniformRowBound (intensityProfile J β) m :=
    uniformRowBound_intensityProfile J M hJcanon β hβ
  have hm1 : m < 1 := intensity_toReal_mul_lt_one M hβ
  obtain ⟨lam, hlam, hcond⟩ :=
    PercLib.Probability.ExplorationEnvelope.exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, fun n =>
    measure_cluster_encard_ge_le_inv_mul_rpow hrow o hlam hm hm1.le hcond n⟩

/-! ## The power-law instance -/

/-- **For the power-law intensity, a positive high-temperature budget gives an explicit
exponential cluster-volume tail bound.**  Source statement
`exists_lam_measure_cluster_encard_ge_le_lrKernel`, with the source's `lrKernel d α` and law
`longRangeMeasure (lrKernel d α) (lrKernel_nonneg d α) β` written in their production
presentation (`radialKernel … (powerLawProfile 1 (d + α))` and
`law (intensityProfile … β)`); see the file header.  Every hypothesis and the conclusion form
are those of the source theorem. -/
theorem exists_lam_law_cluster_encard_ge_le_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hm : 0 < ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal)
    (x : Fin d → ℤ) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤
        ENNReal.ofReal (1 / ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  classical
  have hrows : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, if w = v then 0 else
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(v, w) : ℝ≥0∞)) ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (power_rowSum_le hd (by linarith) (radialKernel_powerLaw_mk hα) v)
  have hrows' : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, @ite ℝ≥0∞ (w = v) (Classical.propDecidable _) 0
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(v, w) : ℝ≥0∞)) ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    refine le_of_eq_of_le ?_ (hrows v)
    exact tsum_congr fun w => by by_cases h : w = v <;> simp [h]
  exact exists_lam_measure_cluster_encard_ge_le_intensityProfile
    (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)))
    (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hrows' β hβ hm x

/-! ## Every natural cluster moment at high temperature -/

/-- **Every natural cluster moment of the power-law model is finite** at every lattice vertex,
in the explicit high-temperature region `β M < 1` with `M = ∑_z ‖z‖_∞^{-d-α}`.  This is the
`k`-th-moment companion of the first-moment statement, in the production presentation of the
kernel (source `PowerLawHighTemp/Moments.lean`,
`lrKernel_lintegral_clusterVol_pow_ne_top`).  No statement is made at or above `β M = 1`, and
in particular none at `β_c`. -/
theorem power_lintegral_encard_cluster_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  classical
  have hrows : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, if w = v then 0 else
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(v, w) : ℝ≥0∞)) ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (power_rowSum_le hd (by linarith) (radialKernel_powerLaw_mk hα) v)
  have hrows' : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, @ite ℝ≥0∞ (w = v) (Classical.propDecidable _) 0
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(v, w) : ℝ≥0∞)) ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    refine le_of_eq_of_le ?_ (hrows v)
    exact tsum_congr fun w => by by_cases h : w = v <;> simp [h]
  exact lintegral_clusterVol_intensity_pow_ne_top
    (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)))
    (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))))
    (fun v => by
      rw [rowSum_def]
      refine le_of_eq_of_le ?_ (hrows v)
      exact tsum_congr fun w => by by_cases h : w = v <;> simp [h]) β hβ x k

/-- **The edge probabilities of the production power-law kernel are the paper's
`1 - exp(-β ‖x - y‖^{-d-α})`.**  This is the checked content of the source's
`law_intensityProfile_eq_longRangeMeasure`: production has no `longRangeMeasure` or
`bernoulliEdgeProb`, so the identification of the laws is recorded at the level of the edge
probabilities of `intensityProfile`, where both sides are defined. -/
theorem intensityProfile_powerLaw_coe {d : ℕ} {α : ℝ} (hα : 0 < α) (β : ℝ≥0)
    (x y : Fin d → ℤ) :
    (((intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β) s(x, y) :
        unitInterval) : ℝ)
      = 1 - Real.exp (-((β : ℝ) * (‖y - x‖ : ℝ) ^ (-((d : ℝ) + α)))) := by
  have hk : ((PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(x, y) : ℝ≥0) : ℝ)
      = (‖y - x‖ : ℝ) ^ (-((d : ℝ) + α)) := by
    rw [radialKernel_powerLaw_mk hα]
    exact Real.coe_toNNReal _ (Real.rpow_nonneg (norm_nonneg _) _)
  simp only [intensityProfile]
  rw [hk]
  ring_nf

/-- Non-vacuity of the moment theorem: at `β = 0` its high-temperature hypothesis holds. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) (k : ℕ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) 0)) ≠ ⊤ :=
  power_lintegral_encard_cluster_pow_ne_top hd hα (β := 0)
    (by rw [ENNReal.coe_zero, zero_mul]; exact zero_lt_one) x k

/-- Simultaneous form: all natural moments at a vertex are finite at once (source
`lrKernel_forall_lintegral_clusterVol_pow_ne_top`). -/
theorem power_forall_lintegral_encard_cluster_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∀ k : ℕ,
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ :=
  fun k => power_lintegral_encard_cluster_pow_ne_top hd hα hβ x k

/-- **A positive interval of parameters on which every natural cluster moment of the
power-law model is finite.**  The endpoint is `β₀ = (M + 1)⁻¹` with
`M = ∑_z ‖z‖_∞^{-d-α}`; the theorem produces it, so the high-temperature region is not a
single point (source `exists_beta_interval_lrKernel_clusterVol_pow_ne_top`, with the source's
`lrKernel`/`longRangeMeasure` written in their production presentation).  No statement is made
at `β₀` or beyond. -/
theorem exists_beta_interval_powerLaw_encard_cluster_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (x : Fin d → ℤ) (k : ℕ),
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  refine ⟨((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) + 1)⁻¹,
    inv_pos.mpr (by positivity), fun β hβ x k => ?_⟩
  exact power_lintegral_encard_cluster_pow_ne_top hd hα
    (mul_coe_lt_one_of_lt_inv_add_one hβ) x k


/-- The `k = 1` instance of the moment theorem (source `Moments.lean` example "agreement with
the committed first-moment statement"), at the candidate's own law.  The source's comparison
against `PowerLawHighTemp.lrKernel_lintegral_clusterVol_ne_top` is omitted because that lemma
is stated over the legacy `longRangeMeasure`. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  simpa only [pow_one] using power_lintegral_encard_cluster_pow_ne_top hd hα hβ x 1

/-! ## Non-vacuity: a positive high-temperature parameter exists -/

/-- **The high-temperature hypotheses of the tail and moment theorems are satisfiable at a
positive parameter.**  For `d ≥ 1`, `α > 0` the parameter `β = ((M + 1)⁻¹)/2`, with
`M = ∑_z ‖z‖_∞^{-d-α}`, satisfies `β > 0`, `β M < 1` and `0 < (β M).toReal`.  Nothing is
claimed at `β M = 1`. -/
theorem exists_beta_positive_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β : ℝ≥0, 0 < β ∧
      (β : ℝ≥0∞) * ((Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1 ∧
      0 < ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal := by
  classical
  set S : ℝ := ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) with hSdef
  set M : ℝ≥0 := Real.toNNReal S with hMdef
  have hSnonneg : ∀ z : Fin d → ℤ, 0 ≤ (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) :=
    fun z => Real.rpow_nonneg (norm_nonneg z) _
  have hSsum : Summable fun z : Fin d → ℤ => (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) :=
    summable_norm_pow hd hα
  set i : Fin d := ⟨0, hd⟩ with hidef
  set z₀ : Fin d → ℤ := Pi.single i 1 with hz₀def
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    have h1 : z₀ i = (1 : ℤ) := Pi.single_eq_same i 1
    rw [h] at h1
    exact one_ne_zero h1.symm
  have hz₀pos : 0 < (‖z₀‖ : ℝ) := by
    have h1 := PercLib.Models.LongRange.one_le_norm_of_ne_zero hz₀ne
    linarith
  have hterm : 0 < (‖z₀‖ : ℝ) ^ (-((d : ℝ) + α)) := Real.rpow_pos_of_pos hz₀pos _
  have hSpos : 0 < S := by
    rw [hSdef]
    have h := hSsum.sum_le_tsum ({z₀} : Finset (Fin d → ℤ)) (fun z _ => hSnonneg z)
    have hle : (‖z₀‖ : ℝ) ^ (-((d : ℝ) + α))
        ≤ ∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)) := by
      simpa using h
    linarith
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Real.toNNReal_pos.mpr hSpos
  have hβpos : 0 < (M + 1)⁻¹ / 2 := by positivity
  have hlt : (M + 1)⁻¹ / 2 * M < 1 := by
    have hβle : (M + 1)⁻¹ / 2 ≤ (M + 1)⁻¹ := by
      rw [div_eq_mul_inv]
      calc (M + 1)⁻¹ * 2⁻¹ ≤ (M + 1)⁻¹ * 1 := by gcongr; norm_num
        _ = (M + 1)⁻¹ := mul_one _
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hβle hMpos.le) ?_
    rw [← NNReal.coe_lt_coe]
    push_cast
    rw [inv_mul_eq_div, div_lt_one (by positivity)]
    linarith [M.coe_nonneg]
  refine ⟨(M + 1)⁻¹ / 2, hβpos, ?_, ?_⟩
  · rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    exact hlt
  · have hE : (↑((M + 1)⁻¹ / 2) : ℝ≥0∞) * (M : ℝ≥0∞) < 1 := by
      rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
      exact hlt
    have hne0 : (↑((M + 1)⁻¹ / 2) : ℝ≥0∞) * (M : ℝ≥0∞) ≠ 0 := by
      rw [← ENNReal.coe_mul]
      exact ENNReal.coe_ne_zero.mpr (mul_ne_zero (ne_of_gt hβpos) (ne_of_gt hMpos))
    exact ENNReal.toReal_pos hne0 (ne_top_of_lt (hE.trans_le le_top))

/-- Non-vacuity of the power-law tail theorem at a **positive** parameter: the two
high-temperature hypotheses `β M < 1` and `0 < (β M).toReal` are simultaneously satisfiable,
and the tail bound is then available at every natural index. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧ ∃ lam : ℝ, 1 < lam ∧ ∀ n : ℕ,
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤
        ENNReal.ofReal (1 / ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal) *
          ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  obtain ⟨β, hβ, hβM, hm⟩ := exists_beta_positive_powerLaw hd hα
  obtain ⟨lam, hlam, htail⟩ := exists_lam_law_cluster_encard_ge_le_powerLaw hd hα hβM hm x
  exact ⟨β, hβ, lam, hlam, htail⟩

end PercLib.Percolation.Bond.Exploration.BFS
