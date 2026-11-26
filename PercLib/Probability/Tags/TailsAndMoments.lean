/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for truncated first moments, size-biased limits, mixed spatial
moments and tail comparison for random sets. Every statement is assembled from lemmas
proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.SizeBias
public import PercLib.Probability.SizeBiasLimits
public import PercLib.Probability.MixedSpatialMoments
public import PercLib.Probability.TailComparison

/-!
# Truncated moments, size-biased limits and random-set tails: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `truncated_mean_lower_bounds`
* `sizeBias_limit_tail_and_laplace`
* `mixed_spatial_moment_bounds`
* `random_set_tail_comparison`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology RealInnerProductSpace Nat

universe u

namespace PercLib.Probability

/-- For a nonnegative random variable with finite mean `μ` and second moment `ν`, a
proportion at least `1 - λ⁻¹` of the mean comes from values at most `λν/μ`, and the same
holds for the mean of `X` truncated at any level `N ≥ λν/μ`. -/
@[tag "LLGA"]
theorem truncated_mean_lower_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) (_hX0 : ∀ ω, 0 ≤ X ω) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂P ≠ ∞ → ∀ l : ℝ≥0∞, 1 < l →
      ((1 - l⁻¹) * ∫⁻ ω, ENNReal.ofReal (X ω) ∂P ≤
        ∫⁻ ω in {ω | ENNReal.ofReal (X ω) ≤ l * (∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂P) /
          (∫⁻ ω, ENNReal.ofReal (X ω) ∂P)}, ENNReal.ofReal (X ω) ∂P) ∧
      ∀ N : ℝ≥0∞, l * (∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂P) / (∫⁻ ω, ENNReal.ofReal (X ω) ∂P) ≤ N →
        (1 - l⁻¹) * ∫⁻ ω, ENNReal.ofReal (X ω) ∂P ≤
          ∫⁻ ω, min (ENNReal.ofReal (X ω)) N ∂P :=
  fun hμ _ hl => ⟨le_setLIntegral_le P hX.ennreal_ofReal hμ hl,
    fun _ hN => le_lintegral_min P hX.ennreal_ofReal hμ hl hN⟩

/-- If the rescaled size-biased laws converge weakly to a law `Q₀` on `[0, ∞)`, then the
rescaled tails converge to `∫_{[t,∞)} y⁻¹ dQ₀` at continuity points `t > 0`, and the
rescaled Laplace transforms converge to `∫ (1 - e^{-λy})/y dQ₀` (value `λ` at `y = 0`). -/
@[tag "7W00"]
theorem sizeBias_limit_tail_and_laplace {ι : Type*} {l : Filter ι} {Ω : Type*}
    [MeasurableSpace Ω] (P : ι → Measure Ω) (X : ι → Ω → ℝ) (hXm : ∀ r, Measurable (X r))
    (hX0 : ∀ r ω, 0 ≤ X r ω) (a : ι → ℝ) (ha : ∀ r, 0 < a r) (Q : ι → ProbabilityMeasure ℝ)
    (hQ : ∀ r, (Q r : Measure ℝ) =
      ((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / a r)
    (Q₀ : ProbabilityMeasure ℝ) (hconv : Tendsto Q l (𝓝 Q₀))
    (hQ₀ : (Q₀ : Measure ℝ) (Iio 0) = 0) :
    (∀ t : ℝ, 0 < t → (Q₀ : Measure ℝ) {t} = 0 →
      Tendsto (fun r => a r / (∫ ω, X r ω ∂P r) * (P r).real {ω | t * a r ≤ X r ω}) l
        (𝓝 (∫ y in Ici t, y⁻¹ ∂(Q₀ : Measure ℝ)))) ∧
    (∀ h : ι → ℝ, (∀ r, 0 < h r) → ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r => h r * a r) l (𝓝 lam) →
      Tendsto (fun r => a r / (∫ ω, X r ω ∂P r) *
          ∫ ω, (1 - Real.exp (-(h r * X r ω))) ∂P r) l
        (𝓝 (∫ y, (if y = 0 then lam else (1 - Real.exp (-(lam * y))) / y)
          ∂(Q₀ : Measure ℝ)))) :=
  ⟨fun _ ht hQt => tendsto_tail_of_sizeBias_tendsto P X hXm hX0 a ha Q hQ Q₀ hconv ht hQt,
    fun h hh _ hlam hlim => tendsto_laplace_of_sizeBias_tendsto P X hXm hX0 a ha Q hQ Q₀ hQ₀
      hconv h hh hlam hlim⟩

section Mixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]

/-- Mixed spatial moments of a random finite point set: the Hölder bound in terms of the
size-biased cluster moment and directional moments, and its consequence along a filter
under asymptotic moment hypotheses, with constant `max 4 (2 C₀)` independent of `n, p`. -/
@[tag "VMEJ"]
theorem mixed_spatial_moment_bounds :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → Finset E),
      (∀ ω, (K ω).Nonempty) →
      (∀ g : E → ℝ≥0∞, Measurable g → Measurable fun ω => ∑ x ∈ K ω, g x) →
      ∫⁻ ω, (#(K ω) : ℝ≥0∞) ∂P ≠ ⊤ → ∀ {n p : ℕ} (deg : Fin n → ℕ)
      (u : (i : Fin n) → Fin (deg i) → E), ∑ i, deg i = p → 1 ≤ p →
      ∫⁻ ω, ∑ x ∈ Fintype.piFinset (fun _ : Fin n => K ω), ∏ i, ‖∏ j, ⟪x i, u i j⟫‖ₑ ∂P ≤
        (∫⁻ ω, (#(K ω) : ℝ≥0∞) ∂P) *
          ((∫⁻ ω, (#(K ω) : ℝ≥0∞) * (#(K ω) : ℝ≥0∞) ^ (2 * n - 2) ∂P) /
            ∫⁻ ω, (#(K ω) : ℝ≥0∞) ∂P) ^ (1 / 2 : ℝ) *
          ⨆ f : (Σ i, Fin (deg i)),
            ((∫⁻ ω, (#(K ω) : ℝ≥0∞) *
                ((#(K ω) : ℝ≥0∞)⁻¹ * ∑ x ∈ K ω, ‖⟪x, u f.1 f.2⟫‖ₑ ^ (2 * p)) ∂P) /
              ∫⁻ ω, (#(K ω) : ℝ≥0∞) ∂P) ^ (1 / 2 : ℝ)) ∧
    (∀ {ι : Type u} {l : Filter ι} (P : ι → Measure Ω) [∀ r, IsProbabilityMeasure (P r)]
      (K : ι → Ω → Finset E), (∀ r ω, (K r ω).Nonempty) →
      (∀ r, ∀ g : E → ℝ≥0∞, Measurable g → Measurable fun ω => ∑ x ∈ K r ω, g x) →
      (∀ r, ∫⁻ ω, (#(K r ω) : ℝ≥0∞) ∂P r ≠ ⊤) → ∀ {n p : ℕ} (deg : Fin n → ℕ)
      (u : (i : Fin n) → Fin (deg i) → E), ∑ i, deg i = p → 1 ≤ p →
      ∀ {m σ ε₁ ε₂ : ι → ℝ≥0∞} {C₀ : ℝ≥0},
      Filter.Tendsto ε₁ l (nhds 0) → Filter.Tendsto ε₂ l (nhds 0) →
      (∀ r, (∫⁻ ω, (#(K r ω) : ℝ≥0∞) * (#(K r ω) : ℝ≥0∞) ^ (2 * n - 2) ∂P r) /
          ∫⁻ ω, (#(K r ω) : ℝ≥0∞) ∂P r ≤
        (1 + ε₁ r) * ((4 * n - 5)‼ : ℝ≥0∞) * m r ^ (2 * n - 2)) →
      (∀ r, ∀ f : (Σ i, Fin (deg i)),
        (∫⁻ ω, (#(K r ω) : ℝ≥0∞) *
            ((#(K r ω) : ℝ≥0∞)⁻¹ * ∑ x ∈ K r ω, ‖⟪x, u f.1 f.2⟫‖ₑ ^ (2 * p)) ∂P r) /
          ∫⁻ ω, (#(K r ω) : ℝ≥0∞) ∂P r ≤
        (1 + ε₂ r) * (C₀ : ℝ≥0∞) ^ (2 * p) * ((2 * p)! : ℝ≥0∞) * σ r ^ (2 * p)) →
      ∃ ε : ι → ℝ≥0∞, Filter.Tendsto ε l (nhds 0) ∧ ∀ r,
        ∫⁻ ω, ∑ x ∈ Fintype.piFinset (fun _ : Fin n => K r ω), ∏ i, ‖∏ j, ⟪x i, u i j⟫‖ₑ ∂P r ≤
          (1 + ε r) * ((max 4 (2 * C₀) : ℝ≥0) : ℝ≥0∞) ^ (n + p) * (n ! : ℝ≥0∞) *
            (p ! : ℝ≥0∞) * (∫⁻ ω, (#(K r ω) : ℝ≥0∞) ∂P r) * m r ^ (n - 1) * σ r ^ p) :=
  ⟨fun P _ K hne hK hχ _ _ deg u hp hp1 => lintegral_mixedMoment_le P K hne hK hχ deg u hp hp1,
    fun P _ K hne hK hχ _ _ deg u hp hp1 _ _ _ _ _ hε₁ hε₂ hA hB =>
      mixedMoment_le_one_add_error P K hne hK hχ deg u hp hp1 hε₁ hε₂ hA hB⟩

end Mixed

section RandomSet
variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {K : Ω → Set V}

/-- A random set that escapes the boxes `Λ r` with probability `O(r^{-a})` and meets them
in expected size `O(r^b)` is almost surely finite, has size tail `O(n^{-a/(a+b)})`, and any
log-tail exponent `1/δ` satisfies `δ ≤ (a+b)/a`. -/
@[tag "HPE6"]
theorem random_set_tail_comparison (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (Λ : ℕ → Finset V)
    {a b C₁ C₂ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ¬ K ω ⊆ Λ r} ≤ ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a)))
    (h2 : ∀ r : ℕ, 1 ≤ r →
      ∫⁻ ω, ((K ω ∩ Λ r).encard : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (C₂ * (r : ℝ) ^ b)) :
    (∀ᵐ ω ∂μ, (K ω).Finite) ∧
    (∀ n : ℕ, 1 ≤ n → μ {ω | (n : ℕ∞) ≤ (K ω).encard} ≤
      ENNReal.ofReal ((2 ^ a * C₁ + C₂) * (n : ℝ) ^ (-a / (a + b)))) ∧
    (∀ [IsProbabilityMeasure μ], ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => Real.log (μ {ω | (n : ℕ∞) ≤ (K ω).encard}).toReal /
        Real.log n) atTop (𝓝 (-1 / δ)) → δ ≤ (a + b) / a) :=
  ⟨ae_finite_of_escape Λ ha h1,
    fun _ hn => measure_le_encard_le hK Λ ha hb hC₁ hC₂ h1 h2 hn,
    fun _ hδ hlim => le_of_log_tail_exponent hK Λ ha hb hC₁ hC₂ h1 h2 hδ hlim⟩

end RandomSet

end PercLib.Probability
