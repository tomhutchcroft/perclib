/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the mixed moments of rescaled cluster measures under volume size
bias. Every statement is assembled from lemmas proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.SizeBias.ClusterMeasure
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Rescaled cluster measures under volume size bias: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Probability.SizeBias.ClusterMeasure`.

## Main results

* `rescaledCount_moments_sizeBiased`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

/-- Rescaled cluster measures under volume size bias. Let `K` be a random subset of a
countable `V ⊆ ℝ^d`, `ζ > 0`, `s` a scale, `μ = ζ⁻¹ ∑_{x ∈ K} δ_{x/s}` and
`Q = sizeBiased P |K|` (density `|K| / E|K|`). For measurable `f_1, …, f_k ≥ 0`, with
extended nonnegative expectations,
`E ∏_j ⟨μ, f_j⟩ = ζ^{-k} ∑_{x_1, …, x_k ∈ V} ∏_j f_j(x_j/s) P(x_1, …, x_k ∈ K)` and
`E_Q ∏_j ⟨μ, f_j⟩ = ζ^{-k} ∑_{y, x_1, …, x_k ∈ V} ∏_j f_j(x_j/s) P(y, x_1, …, x_k ∈ K) / E|K|`;
and if `0 < E|K| < ∞`, `E|K|² < ∞`, the choice `ζ = E|K|² / E|K|` gives `E_Q μ(ℝ^d) = 1`. -/
@[tag "XA7C"]
theorem rescaledCount_moments_sizeBiased {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d))) [Countable V] (K : Ω → Set V)
    (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) {ζ : ℝ} (hζ : 0 < ζ) (s : ℝ) {k : ℕ}
    (f : Fin k → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    (∫⁻ ω, ∏ j, ∫⁻ y, f j y ∂(rescaledCount Subtype.val ζ s (K ω)) ∂P =
      (ENNReal.ofReal ζ)⁻¹ ^ k *
        ∑' x : Fin k → V, (∏ j, f j (s⁻¹ • (x j : EuclideanSpace ℝ (Fin d)))) *
          P {ω | ∀ j, x j ∈ K ω}) ∧
    (∫⁻ ω, ∏ j, ∫⁻ y, f j y ∂(rescaledCount Subtype.val ζ s (K ω))
        ∂(sizeBiased P fun ω => ((K ω).encard : ℝ≥0∞)) =
      (ENNReal.ofReal ζ)⁻¹ ^ k * (∑' (y : V) (x : Fin k → V),
        (∏ j, f j (s⁻¹ • (x j : EuclideanSpace ℝ (Fin d)))) *
          P {ω | y ∈ K ω ∧ ∀ j, x j ∈ K ω}) /
        ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P) ∧
    (∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P ≠ 0 → ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P ≠ ∞ →
      ∫⁻ ω, ((K ω).encard : ℝ≥0∞) ^ 2 ∂P ≠ ∞ →
      ∫⁻ ω, rescaledCount Subtype.val ((∫⁻ ω, ((K ω).encard : ℝ≥0∞) ^ 2 ∂P).toReal /
          (∫⁻ ω, ((K ω).encard : ℝ≥0∞) ∂P).toReal) s (K ω) univ
          ∂(sizeBiased P fun ω => ((K ω).encard : ℝ≥0∞)) = 1) :=
  ⟨lintegral_prod_lintegral_rescaledCount P K hK _ ζ s f hf,
    lintegral_prod_lintegral_rescaledCount_sizeBiased P K hK _ hζ s f hf,
    fun h0 htop h2 => lintegral_rescaledCount_univ_sizeBiased P K hK _ s h0 htop h2⟩

end PercLib.Probability
