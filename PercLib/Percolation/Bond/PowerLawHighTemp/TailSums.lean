/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
No counterpart in the source repository `yujinhkim/lrp`: every declaration below is a derived
consequence, not a migrated statement.  The two ported inputs are

* the geometric cluster tail bound `measure_cluster_encard_ge_le_inv_mul_rpow`, adapted into
  `PercLib/Percolation/Bond/HighTemperatureTail.lean` from
  `PercLib/CriticalLRP/HighTemperatureTail.lean`, source revision
  `7802b33d22f7516ab155005e8526d0b4264ad855`;
* its power-law instance `exists_lam_law_cluster_encard_ge_le_powerLaw`, adapted into
  `PercLib/Percolation/Bond/PowerLawHighTemp/Tail.lean` from
  `PercLib/CriticalLRP/PowerLawHighTemp/Tail.lean`, source revision
  `4a8819bfb7779ac3ff9bf079a8f8edc0a6b19536`.

Both source files are supplied under the Apache-2.0 header of that repository.  The source states
the tail bound at a fixed `n : ℕ` only and asserts nothing as `n → ∞`; the summability over natural
thresholds, the vanishing limit and the real-valued series bound are therefore new derived
statements.  Nothing here is claimed at `β M = 1`, at a critical parameter, or as sharpness, and no
finite substitute for the cluster is introduced.  This is a proof-only module: no definitions.
-/
module

public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summability of the high-temperature cluster-volume tail at natural thresholds

The landed fixed-`n` bound says that under a uniform row-sum budget `m` with `0 < m ≤ 1`, a
high-temperature region `m = β M` with `β M < 1`, and an admissible `lam > 1` there is
`μ{ω | n ≤ encard (cluster ω o)} ≤ m⁻¹ lam⁻ⁿ` for every `n : ℕ`.  On its own that is
a statement about each threshold separately.  This file reads the geometric right-hand side as a
sequence in `n` and draws the consequences of its ratio `lam⁻¹ < 1`:

* the tails are dominated termwise by `ENNReal.ofReal (m⁻¹ (lam⁻¹)ⁿ)`, so their sum is at most
  `ENNReal.ofReal (m⁻¹ (1 - lam⁻¹)⁻¹)` and in particular finite;
* the real sequence of tail probabilities is summable, with the same explicit bound;
* the tail probability tends to `0` as `n → ∞`;
* the same statements for the concrete power-law intensity of `PowerLawHighTemp/Tail.lean`, at
  every lattice vertex, whenever `β M < 1` and `0 < (β M).toReal`, together with a
  positive-parameter instance showing the hypotheses can hold at once.

The threshold is the natural number `n`; the cluster is the genuine, possibly infinite, open
cluster of the root, and the measure is `law (intensityProfile J β) = prodBernoulli _`.

## Main results

* `ofReal_mul_inv_rpow_natCast`: `c * (ofReal lam ^ (n : ℝ))⁻¹ = ofReal (c * lam⁻¹ ^ n)`.
* `tsum_le_of_geometric_bound`: a termwise geometric bound sums to `ofReal (C (1 - lam⁻¹)⁻¹)`.
* `tsum_measure_cluster_encard_ge_le`, `tsum_measure_cluster_encard_ge_ne_top`,
  `tendsto_measure_cluster_encard_ge_atTop_zero`,
  `summable_toReal_measure_cluster_encard_ge`: the generic bond statements, and
  `measure_cluster_encard_ge_le_ofReal_pow` for the same bound as a geometric sequence, with
  `exists_lam_forall_tsum_measure_cluster_encard_ge_le` giving one ratio for all roots.
* `exists_lam_tsum_measure_cluster_encard_ge_le_powerLaw`,
  `tendsto_measure_cluster_encard_ge_powerLaw`,
  `summable_toReal_measure_cluster_encard_ge_powerLaw`: the power-law statements.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open PercLib.Probability
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

/-! ## Reading a threshold bound as a geometric sequence -/

/-- The landed tail bound is written with the real exponent `n : ℝ`; at a natural index the factor
is the `n`-th power of the ratio `lam⁻¹`, multiplied by the constant `c ≥ 0`. -/
theorem ofReal_mul_inv_rpow_natCast {c lam : ℝ} (hc : 0 ≤ c) (hlam : 0 < lam) (n : ℕ) :
    ENNReal.ofReal c * ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹
      = ENNReal.ofReal (c * lam⁻¹ ^ n) := by
  have h0 : 0 ≤ lam⁻¹ := (inv_pos.mpr hlam).le
  have h1 : ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ = (ENNReal.ofReal lam⁻¹) ^ n := by
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_inv_of_pos hlam]
    exact ENNReal.inv_pow
  rw [h1, ← ENNReal.ofReal_pow h0, ← ENNReal.ofReal_mul hc]

/-- **A termwise geometric bound sums.**  If `t n ≤ C lam⁻ⁿ` at every natural threshold with
`C ≥ 0` and `lam > 1`, the `ℝ≥0∞`-series of the `t n` is at most `C (1 - lam⁻¹)⁻¹`. -/
theorem tsum_le_of_geometric_bound {t : ℕ → ℝ≥0∞} {C lam : ℝ} (hC : 0 ≤ C) (hlam : 1 < lam)
    (h : ∀ n : ℕ, t n ≤ ENNReal.ofReal C * ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹) :
    ∑' n : ℕ, t n ≤ ENNReal.ofReal (C * (1 - lam⁻¹)⁻¹) := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hr0 : 0 ≤ lam⁻¹ := (inv_pos.mpr hlam0).le
  have hr1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam
  have hsumm : Summable fun n : ℕ => C * lam⁻¹ ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hgeom : (∑' n : ℕ, ENNReal.ofReal (C * lam⁻¹ ^ n))
      = ENNReal.ofReal (C * (1 - lam⁻¹)⁻¹) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hC (pow_nonneg hr0 n)) hsumm,
      tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  refine (ENNReal.tsum_le_tsum fun n => (h n).trans_eq ?_).trans_eq hgeom
  exact ofReal_mul_inv_rpow_natCast hC hlam0 n

/-- The geometric bound makes the series finite. -/
theorem ne_top_tsum_of_geometric_bound {t : ℕ → ℝ≥0∞} {C lam : ℝ} (hC : 0 ≤ C) (hlam : 1 < lam)
    (h : ∀ n : ℕ, t n ≤ ENNReal.ofReal C * ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹) :
    (∑' n : ℕ, t n) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_le_of_geometric_bound hC hlam h)

/-- **The real series of a geometrically dominated tail is summable**, with the explicit bound
`C (1 - lam⁻¹)⁻¹`. -/
theorem summable_toReal_of_geometric_bound {t : ℕ → ℝ≥0∞} {C lam : ℝ} (hC : 0 ≤ C)
    (hlam : 1 < lam) (h : ∀ n : ℕ, t n ≤ ENNReal.ofReal C * ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹) :
    Summable (fun n : ℕ => (t n).toReal) ∧ (∑' n : ℕ, (t n).toReal) ≤ C * (1 - lam⁻¹)⁻¹ := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hr1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam
  have hterm : ∀ n : ℕ, t n ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((h n).trans_eq (ofReal_mul_inv_rpow_natCast hC hlam0 n))
  have htop := ne_top_tsum_of_geometric_bound hC hlam h
  have hbound : (∑' n : ℕ, t n) ≤ ENNReal.ofReal (C * (1 - lam⁻¹)⁻¹) :=
    tsum_le_of_geometric_bound hC hlam h
  have hnn : 0 ≤ C * (1 - lam⁻¹)⁻¹ :=
    mul_nonneg hC (inv_nonneg.mpr (by linarith))
  refine ⟨ENNReal.summable_toReal htop, ?_⟩
  rw [← ENNReal.tsum_toReal_eq hterm]
  calc (∑' n : ℕ, t n).toReal
      ≤ (ENNReal.ofReal (C * (1 - lam⁻¹)⁻¹)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = C * (1 - lam⁻¹)⁻¹ := ENNReal.toReal_ofReal hnn

variable {V : Type*} [Countable V]

/-! ## The landed tail bound as a geometric sequence -/

/-- **The landed exponential tail bound, as a geometric sequence at natural thresholds.**  This is
`measure_cluster_encard_ge_le_inv_mul_rpow` with the real exponent `n : ℝ` rewritten as the natural
power of the ratio `lam⁻¹`; it is the form in which the summability arguments below read the bound.
The threshold is a natural number and no limit is taken here. -/
theorem measure_cluster_encard_ge_le_ofReal_pow {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) (n : ℕ) :
    (prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard}
      ≤ ENNReal.ofReal (1 / m * lam⁻¹ ^ n) :=
  (measure_cluster_encard_ge_le_inv_mul_rpow hrow o hlam hm hm1 hcond n).trans_eq
    (ofReal_mul_inv_rpow_natCast (div_nonneg zero_le_one hm.le) (by linarith) n)

/-! ## The generic bond percolation statements -/

/-- **Natural-threshold summability of the high-temperature cluster tail.**  Under a uniform
row-sum budget `m = (β M).toReal` with `0 < m ≤ 1` and an admissible `lam > 1`, the series over
`n : ℕ` of the probabilities that the cluster of `o` has at least `n` vertices is bounded by the
explicit geometric constant `m⁻¹ (1 - lam⁻¹)⁻¹`.  The threshold inequality is the landed bound
`measure_cluster_encard_ge_le_inv_mul_rpow`, read as a geometric sequence in `n`. -/
theorem tsum_measure_cluster_encard_ge_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    (∑' n : ℕ, (prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard})
      ≤ ENNReal.ofReal (1 / m * (1 - lam⁻¹)⁻¹) :=
  tsum_le_of_geometric_bound (div_nonneg zero_le_one hm.le) hlam
    (fun n => measure_cluster_encard_ge_le_inv_mul_rpow hrow o hlam hm hm1 hcond n)

/-- The geometric bound is finite, so the tail series is not `⊤`. -/
theorem tsum_measure_cluster_encard_ge_ne_top {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    (∑' n : ℕ, (prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard}) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (tsum_measure_cluster_encard_ge_le hrow o hlam hm hm1 hcond)

/-- **The high-temperature cluster tail vanishes as the threshold grows.**  The tail probabilities
at natural thresholds form a sequence in `ℝ≥0∞` with finite sum, hence tend to `0`. -/
theorem tendsto_measure_cluster_encard_ge_atTop_zero {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    Tendsto (fun n : ℕ => (prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard})
      atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    (tsum_measure_cluster_encard_ge_ne_top hrow o hlam hm hm1 hcond)

/-- **The real tail series is summable with the same explicit bound.** -/
theorem summable_toReal_measure_cluster_encard_ge {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    Summable (fun n : ℕ =>
        ((prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard}).toReal) ∧
      (∑' n : ℕ,
        ((prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard}).toReal)
        ≤ 1 / m * (1 - lam⁻¹)⁻¹ :=
  summable_toReal_of_geometric_bound (div_nonneg zero_le_one hm.le) hlam
    (fun n => measure_cluster_encard_ge_le_inv_mul_rpow hrow o hlam hm hm1 hcond n)

/-- **One admissible ratio serves every root at once.**  The exponential envelope `lam` produced by
`exists_admissible_lambda` depends only on the row budget `m`, never on the root, so the summability
bound with that single ratio holds simultaneously at every vertex `o : V`. -/
theorem exists_lam_forall_tsum_measure_cluster_encard_ge_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ o : V,
      (∑' n : ℕ, (prodBernoulli p) {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard})
        ≤ ENNReal.ofReal (1 / m * (1 - lam⁻¹)⁻¹) := by
  obtain ⟨lam, hlam, hcond⟩ :=
    PercLib.Probability.ExplorationEnvelope.exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, fun o =>
    tsum_measure_cluster_encard_ge_le hrow o hlam hm hm1.le hcond⟩

/-! ## The concrete power-law intensity -/

/-- **Natural-threshold summability for the power-law intensity.**  For every `d ≥ 1` and
`α > 0`, at every lattice vertex `x`, when `β M < 1` and `0 < (β M).toReal` with
`M = ∑_z ‖z‖_∞^{-d-α}`, there is `lam > 1` such that the whole series of cluster-volume tail
probabilities is bounded by `(β M)⁻¹ (1 - lam⁻¹)⁻¹`. -/
theorem exists_lam_tsum_measure_cluster_encard_ge_le_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hm : 0 < ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal)
    (x : Fin d → ℤ) :
    ∃ lam : ℝ, 1 < lam ∧
      (∑' n : ℕ, (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω : Config (Fin d → ℤ) | (n : ℕ∞) ≤ (cluster ω x).encard})
      ≤ ENNReal.ofReal (1 / ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal
            * (1 - lam⁻¹)⁻¹) := by
  obtain ⟨lam, hlam, htail⟩ := exists_lam_law_cluster_encard_ge_le_powerLaw hd hα hβ hm x
  exact ⟨lam, hlam, tsum_le_of_geometric_bound (div_nonneg zero_le_one hm.le) hlam htail⟩

/-- **The power-law cluster tail vanishes as the threshold grows.** -/
theorem tendsto_measure_cluster_encard_ge_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hm : 0 < ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal)
    (x : Fin d → ℤ) :
    Tendsto (fun n : ℕ => (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω : Config (Fin d → ℤ) | (n : ℕ∞) ≤ (cluster ω x).encard}) atTop (𝓝 0) := by
  obtain ⟨lam, hlam, htail⟩ := exists_lam_law_cluster_encard_ge_le_powerLaw hd hα hβ hm x
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (tsum_le_of_geometric_bound (div_nonneg zero_le_one hm.le) hlam htail))

/-- **The real power-law tail series is summable with an explicit bound.** -/
theorem summable_toReal_measure_cluster_encard_ge_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hm : 0 < ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal)
    (x : Fin d → ℤ) :
    Summable (fun n : ℕ => ((law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω : Config (Fin d → ℤ) | (n : ℕ∞) ≤ (cluster ω x).encard}).toReal) ∧
      ∃ lam : ℝ, 1 < lam ∧
        (∑' n : ℕ, ((law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
          {ω : Config (Fin d → ℤ) | (n : ℕ∞) ≤ (cluster ω x).encard}).toReal)
        ≤ 1 / ((β : ℝ≥0∞) * (Real.toNNReal
            (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal
              * (1 - lam⁻¹)⁻¹ := by
  obtain ⟨lam, hlam, htail⟩ := exists_lam_law_cluster_encard_ge_le_powerLaw hd hα hβ hm x
  obtain ⟨hsum, hbound⟩ :=
    summable_toReal_of_geometric_bound (div_nonneg zero_le_one hm.le) hlam htail
  exact ⟨hsum, lam, hlam, hbound⟩

/-! ## Non-vacuity: the hypotheses hold at a positive parameter -/

/-- The generic summability layer is non-vacuous at explicit numbers: the zero profile has uniform
row bound `0`, so with `m = 1/2` the existential ratio and the bound apply. -/
example {V : Type*} [Countable V] :
    ∃ lam : ℝ, 1 < lam ∧ ∀ o : V,
      (∑' n : ℕ, (prodBernoulli (0 : Sym2 V → unitInterval))
          {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard})
        ≤ ENNReal.ofReal (2 * (1 - lam⁻¹)⁻¹) := by
  have hrow : UniformRowBound (0 : Sym2 V → unitInterval) (1 / 2) := by
    intro x t _
    simp
  have h := exists_lam_forall_tsum_measure_cluster_encard_ge_le hrow
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  simpa only [div_eq_mul_inv, one_mul, inv_inv] using h

/-- At a positive high-temperature parameter the power-law cluster tail vanishes. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧
      Tendsto (fun n : ℕ => (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
          {ω : Config (Fin d → ℤ) | (n : ℕ∞) ≤ (cluster ω x).encard}) atTop (𝓝 0) := by
  obtain ⟨β, hβ, hβM, hm⟩ := exists_beta_positive_powerLaw hd hα
  exact ⟨β, hβ, tendsto_measure_cluster_encard_ge_powerLaw hd hα hβM hm x⟩

/-- At a positive high-temperature parameter the explicit geometric constant exists. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧ ∃ lam : ℝ, 1 < lam ∧
      (∑' n : ℕ, (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        {ω : Config (Fin d → ℤ) | (n : ℕ∞) ≤ (cluster ω x).encard})
      ≤ ENNReal.ofReal (1 / ((β : ℝ≥0∞) * (Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal
            * (1 - lam⁻¹)⁻¹) := by
  obtain ⟨β, hβ, hβM, hm⟩ := exists_beta_positive_powerLaw hd hα
  obtain ⟨lam, hlam, hb⟩ := exists_lam_tsum_measure_cluster_encard_ge_le_powerLaw hd hα hβM hm x
  exact ⟨β, hβ, lam, hlam, hb⟩

end PercLib.Percolation.Bond.Exploration.BFS
