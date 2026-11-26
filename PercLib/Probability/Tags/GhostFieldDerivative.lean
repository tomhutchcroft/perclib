/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the positive-field derivatives of the ghost-field transform
`M(h) = E[1 - e^{-hT}]` of an `ℕ∞`-valued random variable. Every statement is assembled
from lemmas proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GhostFieldDerivative

/-!
# Ghost-field derivatives: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Probability.GhostFieldDerivative`.

## Main results

* `ghost_smooth_and_iteratedDeriv`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- The ghost transform `M(h) = E[1 - e^{-hT}]` is smooth on `(0, ∞)`, its `k`-th
derivative for `k ≥ 1` is `(-1)^{k+1} E[T^k e^{-hT}; T < ∞]`, and it is nondecreasing and
concave on `(0, ∞)`. -/
@[tag "J2TE"]
theorem ghost_smooth_and_iteratedDeriv [IsProbabilityMeasure μ] (hT : Measurable T) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      (Ioi 0) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ h : ℝ, 0 < h →
      iteratedDeriv k
        (fun h : ℝ =>
          (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal) h =
        (-1) ^ (k + 1) *
          ∫ ω in {ω | T ω ≠ ⊤}, ((T ω).toNat : ℝ) ^ k * Real.exp (-(h * (T ω).toNat)) ∂μ) ∧
    MonotoneOn
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal)
      (Ioi 0) ∧
    ConcaveOn ℝ (Ioi 0)
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal) :=
  ⟨contDiffOn_ghost_toReal hT, fun _ hk _ hh => iteratedDeriv_ghost_toReal hT hk hh,
    monotoneOn_ghost_toReal hT, concaveOn_ghost_toReal hT⟩

end PercLib.Probability
