/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Truncated first moments and size-biased laws of nonnegative random variables, with the
cluster-volume instance. New proofs against pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream proof is copied. Random variables
are `ℝ≥0∞`-valued and expectations are lower Lebesgue integrals; the size-biased law is
`sizeBiased` of `SizeBias/Defs.lean` (mathlib's `Measure.withDensity`).
-/
module

public import PercLib.Percolation.Bond.ClusterMoments
public import PercLib.Percolation.Bond.RowSum
public import PercLib.Probability.SizeBias.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Truncated first moments and size-biased laws

Truncated means of a nonnegative random variable from its first two moments, the size-biased law
`sizeBiased` (a `withDensity` measure), and its instance for the cluster volume.

## Main results

* `le_setLIntegral_le_of_le`
* `le_lintegral_min`
* `isProbabilityMeasure_withDensity_div`
* `lintegral_withDensity_div`
* `isProbabilityMeasure_sizeBiased_cluster`
* `lintegral_sizeBiased_cluster`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Truncated first moments (LLGA) -/

/-- The upper tail of the first moment above `t`: `t · E[X 1{X > t}] ≤ E X²`. -/
theorem setLIntegral_gt_mul_le (P : Measure Ω) {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (t : ℝ≥0∞) :
    (∫⁻ ω in {ω | t < X ω}, X ω ∂P) * t ≤ ∫⁻ ω, X ω ^ 2 ∂P := by
  rw [← lintegral_mul_const t hX]
  calc ∫⁻ ω in {ω | t < X ω}, X ω * t ∂P
      ≤ ∫⁻ ω in {ω | t < X ω}, X ω ^ 2 ∂P :=
        setLIntegral_mono' (measurableSet_lt measurable_const hX) fun ω hω => by
          rw [pow_two]; gcongr; exact le_of_lt hω
    _ ≤ ∫⁻ ω, X ω ^ 2 ∂P := setLIntegral_le_lintegral _ _

/-- A vanishing second moment forces a vanishing first moment. -/
theorem lintegral_eq_zero_of_lintegral_sq_eq_zero (P : Measure Ω) {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (h : ∫⁻ ω, X ω ^ 2 ∂P = 0) : ∫⁻ ω, X ω ∂P = 0 := by
  rw [lintegral_eq_zero_iff (hX.pow_const 2)] at h
  rw [lintegral_eq_zero_iff hX]
  filter_upwards [h] with ω hω
  simpa using hω

/-- **Truncated mean.** If `μ = E X < ∞`, `ν = E X²` and `λ > 1`, then for every
threshold `t ≥ λν/μ`, `E[X 1{X ≤ t}] ≥ (1 − λ⁻¹) μ`. -/
theorem le_setLIntegral_le_of_le (P : Measure Ω) {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hμ : ∫⁻ ω, X ω ∂P ≠ ∞) {l t : ℝ≥0∞} (hl : 1 < l)
    (ht : l * (∫⁻ ω, X ω ^ 2 ∂P) / (∫⁻ ω, X ω ∂P) ≤ t) :
    (1 - l⁻¹) * ∫⁻ ω, X ω ∂P ≤ ∫⁻ ω in {ω | X ω ≤ t}, X ω ∂P := by
  set μ := ∫⁻ ω, X ω ∂P
  set ν := ∫⁻ ω, X ω ^ 2 ∂P
  set A := ∫⁻ ω in {ω | X ω ≤ t}, X ω ∂P
  set B := ∫⁻ ω in {ω | t < X ω}, X ω ∂P
  have hl0 : l ≠ 0 := (zero_lt_one.trans hl).ne'
  rcases eq_or_ne μ 0 with hμ0 | hμ0
  · rw [hμ0, mul_zero]; exact zero_le
  have hν0 : ν ≠ 0 := fun h => hμ0 (lintegral_eq_zero_of_lintegral_sq_eq_zero P hX h)
  have hAB : A + B = μ := by
    have hc : {ω | X ω ≤ t}ᶜ = {ω | t < X ω} := by ext ω; simp
    change _ = ∫⁻ ω, X ω ∂P
    rw [← lintegral_add_compl (fun ω => X ω) (measurableSet_le hX measurable_const), hc]
  -- `B λ ≤ μ`.
  have hBl : B * l ≤ μ := by
    rcases eq_or_ne t ∞ with htop | htop
    · have : B = 0 := by simp [B, htop]
      simp [this]
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, nonpos_iff_eq_zero, ENNReal.div_eq_zero_iff] at ht
      rcases ht with h | h
      · exact (mul_ne_zero hl0 hν0) h
      · exact hμ h
    have key : l * ν ≤ μ * t := by
      calc l * ν = μ * (l * ν / μ) := (ENNReal.mul_div_cancel hμ0 hμ).symm
        _ ≤ μ * t := by gcongr
    rw [← ENNReal.mul_le_mul_iff_left ht0 htop]
    calc B * l * t = l * (B * t) := by ring
      _ ≤ l * ν := by gcongr; exact setLIntegral_gt_mul_le P hX t
      _ ≤ μ * t := key
  have hB : B ≤ μ * l⁻¹ := by
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hl0) (Or.inr hμ)]
    exact hBl
  calc (1 - l⁻¹) * μ = μ - μ * l⁻¹ := by
        rw [mul_comm, ENNReal.mul_sub (fun _ _ => hμ), mul_one]
    _ ≤ μ - B := tsub_le_tsub_left hB _
    _ ≤ A := by rw [← hAB]; exact le_of_eq (ENNReal.add_sub_cancel_right
        (ne_top_of_le_ne_top hμ (hAB ▸ le_add_self)))

/-- **Truncated mean at the threshold `λν/μ`.** -/
theorem le_setLIntegral_le (P : Measure Ω) {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hμ : ∫⁻ ω, X ω ∂P ≠ ∞) {l : ℝ≥0∞} (hl : 1 < l) :
    (1 - l⁻¹) * ∫⁻ ω, X ω ∂P ≤
      ∫⁻ ω in {ω | X ω ≤ l * (∫⁻ ω, X ω ^ 2 ∂P) / (∫⁻ ω, X ω ∂P)}, X ω ∂P :=
  le_setLIntegral_le_of_le P hX hμ hl le_rfl

/-- **Truncation by a minimum.** If `N ≥ λν/μ` then `E[min X N] ≥ (1 − λ⁻¹) μ`. -/
theorem le_lintegral_min (P : Measure Ω) {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hμ : ∫⁻ ω, X ω ∂P ≠ ∞) {l N : ℝ≥0∞} (hl : 1 < l)
    (hN : l * (∫⁻ ω, X ω ^ 2 ∂P) / (∫⁻ ω, X ω ∂P) ≤ N) :
    (1 - l⁻¹) * ∫⁻ ω, X ω ∂P ≤ ∫⁻ ω, min (X ω) N ∂P := by
  refine (le_setLIntegral_le_of_le P hX hμ hl hN).trans ?_
  calc ∫⁻ ω in {ω | X ω ≤ N}, X ω ∂P = ∫⁻ ω in {ω | X ω ≤ N}, min (X ω) N ∂P :=
        setLIntegral_congr_fun (measurableSet_le hX measurable_const)
          fun ω hω => (min_eq_left hω).symm
    _ ≤ ∫⁻ ω, min (X ω) N ∂P := setLIntegral_le_lintegral _ _

/-! ### Size-biased laws (6L9Z) -/

/-- The size-biased law of `X ≥ 0` with `0 < E X < ∞` is a probability measure. -/
theorem isProbabilityMeasure_withDensity_div (P : Measure Ω) {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (h0 : ∫⁻ ω, X ω ∂P ≠ 0) (htop : ∫⁻ ω, X ω ∂P ≠ ∞) :
    IsProbabilityMeasure (P.withDensity fun ω => X ω / ∫⁻ ω, X ω ∂P) :=
  isProbabilityMeasure_sizeBiased P hX h0 htop

/-- Expectations under the size-biased law: `Ê F = E[X F] / E X` for measurable `F ≥ 0`. -/
theorem lintegral_withDensity_div (P : Measure Ω) {X F : Ω → ℝ≥0∞} (hX : Measurable X)
    (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(P.withDensity fun ω => X ω / ∫⁻ ω, X ω ∂P) =
      (∫⁻ ω, X ω * F ω ∂P) / ∫⁻ ω, X ω ∂P :=
  lintegral_sizeBiased P hX hF

/-- The size-biased mean: `Ê X = E X² / E X`, with `E X²` allowed to be infinite. -/
theorem lintegral_self_withDensity_div (P : Measure Ω) {X : Ω → ℝ≥0∞}
    (hX : Measurable X) :
    ∫⁻ ω, X ω ∂(P.withDensity fun ω => X ω / ∫⁻ ω, X ω ∂P) =
      (∫⁻ ω, X ω ^ 2 ∂P) / ∫⁻ ω, X ω ∂P :=
  lintegral_self_sizeBiased P hX

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*} [Countable V]

/-- **Cluster instance.** With `T = |K_o|` and `χ(o) < ∞`, the size-biased law of
`T` is a probability measure and its mean is `E T² / χ(o)`. -/
theorem isProbabilityMeasure_sizeBiased_cluster (q : Sym2 V → unitInterval) (o : V)
    (hχ : chi q o < ∞) :
    IsProbabilityMeasure ((law q).withDensity fun ω =>
      ((cluster ω o).encard : ℝ≥0∞) / chi q o) :=
  isProbabilityMeasure_withDensity_div (law q)
    ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster o))
    (zero_lt_one.trans_le (one_le_chi q o)).ne' hχ.ne

/-- **Cluster instance.** `Ê T = E T² / χ(o)` for `T = |K_o|`. -/
theorem lintegral_sizeBiased_cluster (q : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂((law q).withDensity fun ω =>
        ((cluster ω o).encard : ℝ≥0∞) / chi q o) =
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ 2 ∂law q) / chi q o :=
  lintegral_self_withDensity_div (law q) ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard_cluster o))

/-! ### Non-vacuity witnesses -/

/-- The singleton cluster: on `Unit`, `T = 1`, so `χ = 1 < ∞` and `Ê T = E T² / χ = 1`. -/
example (q : Sym2 Unit → unitInterval) :
    chi q () < ∞ ∧
      ∫⁻ ω, ((cluster ω ()).encard : ℝ≥0∞) ∂((law q).withDensity fun ω =>
        ((cluster ω ()).encard : ℝ≥0∞) / chi q ()) = 1 := by
  have hT : ∀ ω : Config Unit, (cluster ω ()).encard = 1 := fun ω => by
    rw [Set.encard_eq_one]
    exact ⟨(), Set.eq_singleton_iff_unique_mem.2 ⟨mem_cluster_self ω (), fun _ _ => rfl⟩⟩
  have hχ : chi q () = 1 := by simp [chi, hT]
  refine ⟨by simp [hχ], ?_⟩
  rw [lintegral_sizeBiased_cluster, hχ]
  simp [hT]

end PercLib.Percolation.Bond

namespace PercLib.Probability

/-- `X` uniform on `{1, 2}`: `E X = 3/2`, the truncated-mean bound applies with `λ = 2`, the
size-biased law is a probability measure, and it gives mass `2/3` to `X = 2`. -/
example :
    let P : Measure Bool := (2⁻¹ : ℝ≥0∞) • Measure.count
    let X : Bool → ℝ≥0∞ := fun b => if b then 2 else 1
    ∫⁻ b, X b ∂P = 3 / 2 ∧
      (1 - 2⁻¹) * ∫⁻ b, X b ∂P ≤
        ∫⁻ b in {b | X b ≤ 2 * (∫⁻ b, X b ^ 2 ∂P) / (∫⁻ b, X b ∂P)}, X b ∂P ∧
      IsProbabilityMeasure (P.withDensity fun b => X b / ∫⁻ b, X b ∂P) ∧
      (P.withDensity fun b => X b / ∫⁻ b, X b ∂P) {true} = 2 / 3 := by
  intro P X
  have hX : Measurable X := measurable_of_countable _
  have hμ : ∫⁻ b, X b ∂P = 3 / 2 := by
    simp only [P, X, lintegral_fintype, Fintype.sum_bool, Measure.smul_apply,
      Measure.count_singleton, smul_eq_mul, mul_one, ite_true]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp [ENNReal.toReal_div]
    norm_num
  refine ⟨hμ, le_setLIntegral_le P hX (by rw [hμ]; finiteness) (by norm_num),
    isProbabilityMeasure_withDensity_div P hX (by rw [hμ]; simp) (by rw [hμ]; finiteness), ?_⟩
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton, hμ]
  simp only [P, X, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one, ite_true]
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by simp)) (by simp)) (by finiteness)]
  simp [ENNReal.toReal_div]
  norm_num

end PercLib.Probability
