/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the Paley–Zygmund inequality and the second-moment method, from
pinned mathlib's Hölder inequality for lower Lebesgue integrals, and the cluster-volume corollary.
No upstream code is copied, no definition is added and no Input is introduced.
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Distributions.Bernoulli
public import PercLib.Percolation.Bond.TreeGraph.Moments
public import PercLib.Percolation.Bond.RowSum
public import PercLib.Percolation.Bond.Intensity

/-! # Paley–Zygmund and the second-moment method

* `paleyZygmund` (`ℝ≥0∞` form): for a probability measure, measurable `X : Ω → ℝ≥0∞` with
  `E X < ⊤` and `0 ≤ θ < 1`, `(1 - θ)² (E X)² ≤ P(X > θ E X) E X²`.
* `paleyZygmund_real` (real form): for `X ≥ 0` in `L²` with `E X² > 0`,
  `(1 - θ)² (E X)² / E X² ≤ P(X > θ E X)`.
* `sq_lintegral_le_measure_pos_mul` (second-moment method): `(E X)² ≤ P(X > 0) E X²`.
* `paleyZygmund_cluster`, `paleyZygmund_cluster_of_chi_le` (cluster volumes):
  `(1 - θ)² χ(o)² ≤ P(|K_o| > θ χ(o)) E|K_o|²`, and `(1 - θ)² χ(o) ≤ P(|K_o| > θ χ(o)) M²`
  when `χ ≤ M` everywhere (with `E|K_o|² ≤ χ(o) M²`, `lintegral_encard_pow_le` at `m = 2`).

The proof: `E X ≤ θ E X + E[X 1_A]` for `A = {X > θ E X}`, and Cauchy–Schwarz
`E[X 1_A]² ≤ E X² · P(A)` (`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `(√x √y)² = x y` in `ℝ≥0∞`. -/
theorem sq_rpow_half_mul_rpow_half (x y : ℝ≥0∞) :
    (x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) ^ 2 = x * y := by
  have h : ∀ z : ℝ≥0∞, (z ^ (1 / 2 : ℝ)) ^ 2 = z := fun z => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [mul_pow, h, h]

/-- **Cauchy–Schwarz on an event.** `(∫_A X)² ≤ (∫ X²) μ(A)`. -/
theorem sq_setLIntegral_le {X : Ω → ℝ≥0∞} (hX : Measurable X) {A : Set Ω}
    (hA : MeasurableSet A) :
    (∫⁻ ω in A, X ω ∂μ) ^ 2 ≤ (∫⁻ ω, X ω ^ 2 ∂μ) * μ A := by
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hX.aemeasurable
    ((measurable_one (α := ℝ≥0∞)).indicator hA).aemeasurable (f := X) (g := A.indicator 1)
  have e1 : ∫⁻ a, (X * A.indicator (1 : Ω → ℝ≥0∞)) a ∂μ = ∫⁻ ω in A, X ω ∂μ := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun ω => ?_
    by_cases h : ω ∈ A <;> simp [h]
  have e2 : ∫⁻ a, X a ^ (2 : ℝ) ∂μ = ∫⁻ ω, X ω ^ 2 ∂μ := by
    simp_rw [ENNReal.rpow_two]
  have e3 : ∫⁻ a, (A.indicator (1 : Ω → ℝ≥0∞) a) ^ (2 : ℝ) ∂μ = μ A := by
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr fun ω => ?_
    by_cases h : ω ∈ A <;> simp [h]
  rw [e1, e2, e3] at hcs
  calc (∫⁻ ω in A, X ω ∂μ) ^ 2
      ≤ ((∫⁻ ω, X ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ A) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := sq_rpow_half_mul_rpow_half _ _

/-- **Paley–Zygmund, `ℝ≥0∞` form.** For a probability measure, measurable `X : Ω → ℝ≥0∞` with
`E X < ⊤` and `0 ≤ θ < 1`: `(1 - θ)² (E X)² ≤ P(X > θ E X) · E X²`. -/
theorem paleyZygmund [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hfin : ∫⁻ ω, X ω ∂μ ≠ ⊤) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ENNReal.ofReal ((1 - θ) ^ 2) * (∫⁻ ω, X ω ∂μ) ^ 2 ≤
      μ {ω | ENNReal.ofReal θ * ∫⁻ ω, X ω ∂μ < X ω} * ∫⁻ ω, X ω ^ 2 ∂μ := by
  set a := ∫⁻ ω, X ω ∂μ with ha
  set A := {ω | ENNReal.ofReal θ * a < X ω} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hX
  -- `E X ≤ θ E X + E[X 1_A]`.
  have hsplit : a ≤ ∫⁻ ω in A, X ω ∂μ + ENNReal.ofReal θ * a := by
    calc a = ∫⁻ ω in A, X ω ∂μ + ∫⁻ ω in Aᶜ, X ω ∂μ := (lintegral_add_compl X hAm).symm
      _ ≤ _ := by
        refine add_le_add le_rfl ?_
        calc ∫⁻ ω in Aᶜ, X ω ∂μ ≤ ∫⁻ ω in Aᶜ, ENNReal.ofReal θ * a ∂μ :=
              setLIntegral_mono measurable_const fun ω hω => not_lt.1 hω
          _ ≤ ∫⁻ _, ENNReal.ofReal θ * a ∂μ := setLIntegral_le_lintegral _ _
          _ = ENNReal.ofReal θ * a := by simp
  have hθa : ENNReal.ofReal θ * a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hkey : ENNReal.ofReal (1 - θ) * a ≤ ∫⁻ ω in A, X ω ∂μ := by
    refine ENNReal.le_of_add_le_add_right hθa ?_
    calc ENNReal.ofReal (1 - θ) * a + ENNReal.ofReal θ * a
        = ENNReal.ofReal (1 - θ + θ) * a := by
          rw [← add_mul, ENNReal.ofReal_add (by linarith) hθ0]
      _ = a := by simp
      _ ≤ _ := hsplit
  calc ENNReal.ofReal ((1 - θ) ^ 2) * a ^ 2 = (ENNReal.ofReal (1 - θ) * a) ^ 2 := by
        rw [mul_pow, ENNReal.ofReal_pow (by linarith)]
    _ ≤ (∫⁻ ω in A, X ω ∂μ) ^ 2 := by gcongr
    _ ≤ (∫⁻ ω, X ω ^ 2 ∂μ) * μ A := sq_setLIntegral_le hX hAm
    _ = μ A * ∫⁻ ω, X ω ^ 2 ∂μ := mul_comm _ _

/-- **The second-moment method.** `(E X)² ≤ P(X > 0) · E X²`. -/
theorem sq_lintegral_le_measure_pos_mul [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hfin : ∫⁻ ω, X ω ∂μ ≠ ⊤) :
    (∫⁻ ω, X ω ∂μ) ^ 2 ≤ μ {ω | 0 < X ω} * ∫⁻ ω, X ω ^ 2 ∂μ := by
  have h := paleyZygmund (μ := μ) hX hfin le_rfl zero_lt_one
  simpa using h

/-- **Paley–Zygmund, real form.** For `X ≥ 0` in `L²` with `E X² > 0` and `0 ≤ θ < 1`:
`(1 - θ)² (E X)² / E X² ≤ P(X > θ E X)`. -/
theorem paleyZygmund_real [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hL2 : MemLp X 2 μ) (hpos : 0 < ∫ ω, X ω ^ 2 ∂μ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 / ∫ ω, X ω ^ 2 ∂μ ≤
      μ.real {ω | θ * ∫ ω, X ω ∂μ < X ω} := by
  have hint : Integrable X μ := hL2.integrable one_le_two
  have hint2 : Integrable (fun ω => X ω ^ 2) μ := hL2.integrable_sq
  have hE : ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ENNReal.ofReal (∫ ω, X ω ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hX0)).symm
  have hE2 : ∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂μ = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall fun ω =>
        sq_nonneg _)]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_pow (hX0 ω)]
  have hEX0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg hX0
  have h := paleyZygmund (μ := μ) (X := fun ω => ENNReal.ofReal (X ω)) hX.ennreal_ofReal
    (by rw [hE]; exact ENNReal.ofReal_ne_top) hθ0 hθ1
  rw [hE, hE2] at h
  have hset : {ω | ENNReal.ofReal θ * ENNReal.ofReal (∫ ω, X ω ∂μ) < ENNReal.ofReal (X ω)} =
      {ω | θ * ∫ ω, X ω ∂μ < X ω} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [← ENNReal.ofReal_mul hθ0, ENNReal.ofReal_lt_ofReal_iff']
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, (mul_nonneg hθ0 hEX0).trans_lt h⟩
  rw [hset, ← ENNReal.ofReal_pow hEX0, ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ofReal_measureReal (measure_ne_top _ _),
    ← ENNReal.ofReal_mul measureReal_nonneg] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg measureReal_nonneg hpos.le)).1 h
  rw [div_le_iff₀ hpos]
  exact h'

/-! ### Cluster volumes -/

open PercLib.Percolation.Bond

/-- **Paley–Zygmund for the cluster volume.** For a countable `V`, any profile, `o`, finite
`χ(o)` and `0 ≤ θ < 1`: `(1 - θ)² χ(o)² ≤ P(|K_o| > θ χ(o)) E|K_o|²`. -/
theorem paleyZygmund_cluster {V : Type*} [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (hχ : chi q o ≠ ⊤) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ENNReal.ofReal ((1 - θ) ^ 2) * chi q o ^ 2 ≤
      law q {ω | ENNReal.ofReal θ * chi q o < ((cluster ω o).encard : ℝ≥0∞)} *
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ 2 ∂law q :=
  paleyZygmund ((Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp
    (measurable_encard_cluster o)) hχ hθ0 hθ1

/-- **Paley–Zygmund for the cluster volume, uniform form.** If `χ ≤ M` at every vertex with
`M < ⊤`, then `(1 - θ)² χ(o) ≤ P(|K_o| > θ χ(o)) M²`. -/
theorem paleyZygmund_cluster_of_chi_le {V : Type*} [Countable V] (q : Sym2 V → unitInterval)
    {M : ℝ≥0∞} (hM : ∀ x, chi q x ≤ M) (hMt : M ≠ ⊤) (o : V) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    ENNReal.ofReal ((1 - θ) ^ 2) * chi q o ≤
      law q {ω | ENNReal.ofReal θ * chi q o < ((cluster ω o).encard : ℝ≥0∞)} * M ^ 2 := by
  have hχ : chi q o ≠ ⊤ := ne_top_of_le_ne_top hMt (hM o)
  have hχ0 : chi q o ≠ 0 := (zero_lt_one.trans_le (one_le_chi q o)).ne'
  have h := paleyZygmund_cluster q o hχ hθ0 hθ1
  have h2 := lintegral_encard_pow_le q hM 2 one_le_two o
  norm_num at h2
  have h3 : ENNReal.ofReal ((1 - θ) ^ 2) * chi q o * chi q o ≤
      law q {ω | ENNReal.ofReal θ * chi q o < ((cluster ω o).encard : ℝ≥0∞)} * M ^ 2 *
        chi q o := by
    calc ENNReal.ofReal ((1 - θ) ^ 2) * chi q o * chi q o
        = ENNReal.ofReal ((1 - θ) ^ 2) * chi q o ^ 2 := by ring
      _ ≤ _ := h
      _ ≤ law q {ω | ENNReal.ofReal θ * chi q o < ((cluster ω o).encard : ℝ≥0∞)} *
            (chi q o * M ^ 2) := mul_le_mul' le_rfl h2
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_left hχ0 hχ).1 h3

/-! ### Non-vacuity -/

/-- A Bernoulli(1/2) variable (`X = 1` on `true` under `Ber(true, false, 1/2)`): every hypothesis of
the second-moment method holds (here it is an equality, `1/4 = 1/2 · 1/2`). -/
example : (∫⁻ ω, (if ω = true then 1 else 0 : ℝ≥0∞)
    ∂(ProbabilityTheory.bernoulliMeasure true false
    (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))) ^ 2 ≤
    (ProbabilityTheory.bernoulliMeasure true false
        (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
        {ω | 0 < (if ω = true then 1 else 0 : ℝ≥0∞)} *
      ∫⁻ ω, (if ω = true then 1 else 0 : ℝ≥0∞) ^ 2
          ∂(ProbabilityTheory.bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) :=
  sq_lintegral_le_measure_pos_mul (Measurable.of_discrete) (ne_top_of_le_ne_top ENNReal.one_ne_top
    (by
      calc ∫⁻ ω, (if ω = true then 1 else 0 : ℝ≥0∞)
          ∂(ProbabilityTheory.bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
          ≤ ∫⁻ _, 1 ∂(ProbabilityTheory.bernoulliMeasure true false
              (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) :=
            lintegral_mono fun ω => by split_ifs <;> simp
        _ = 1 := by simp))

/-- The zero kernel on `ℕ`: `χ ≡ 1 ≤ 1 = M`, so the uniform cluster form applies. -/
example (o : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ENNReal.ofReal ((1 - θ) ^ 2) * chi (intensityProfile (fun _ : Sym2 ℕ => 0) 1) o ≤
      law (intensityProfile (fun _ : Sym2 ℕ => 0) 1)
        {ω | ENNReal.ofReal θ * chi (intensityProfile (fun _ : Sym2 ℕ => 0) 1) o <
          ((cluster ω o).encard : ℝ≥0∞)} * 1 ^ 2 :=
  paleyZygmund_cluster_of_chi_le _ (fun x => (chi_intensity_eq_one_of_rowSum_zero _
    (fun _ => by simp) 1 x).le) ENNReal.one_ne_top o hθ0 hθ1

end PercLib.Probability
