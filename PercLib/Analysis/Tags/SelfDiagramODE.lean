/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.SelfDiagramODE

/-!
# Diagram bounds expressed in the susceptibility: correspondence

Wiki correspondence for `PercLib/Analysis/SelfDiagramODE.lean`. No new definitions.

## Main results

* `eventual_bounds_of_deriv_ge_of_self_diagram`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PercLib.Analysis

/-- **GQJY.** Let `a < b < ∞`, `y : (a, b) → [1, ∞)` locally absolutely continuous with
`y(t) → ∞` as `t ↑ b`, `D : (a, b) → [1, ∞)` measurable, and `k > 0` with
`y' ≥ k (y - D)₊²/D²` a.e. on some `(t₀, b)`. If `D(t) ≤ C log(e y(t))` near `b`, then
eventually as `ε ↓ 0`, `y(b - ε) ≤ C₁ ε⁻¹ log²(1/ε)` and `D(b - ε) ≤ C₂ log(1/ε)`. If instead
`D(t) ≤ C y(t)^q` near `b` with `0 ≤ q < 1/2`, then eventually `y(b - ε) ≤ C₃ ε^{-1/(1-2q)}`. -/
@[tag "GQJY"]
theorem eventual_bounds_of_deriv_ge_of_self_diagram {a b k : ℝ} {y D : ℝ → ℝ}
    (hab : a < b) (hy1 : ∀ t ∈ Ioo a b, 1 ≤ y t)
    (hac : ∀ p q, a < p → p ≤ q → q < b → AbsolutelyContinuousOnInterval y p q)
    (htend : Tendsto y (𝓝[<] b) atTop) (_hD : Measurable D) (hD1 : ∀ t ∈ Ioo a b, 1 ≤ D t)
    (hk : 0 < k)
    (hder : ∃ t₀ < b, ∀ᵐ t, t ∈ Ioo t₀ b → k * max (y t - D t) 0 ^ 2 / D t ^ 2 ≤ deriv y t) :
    (∀ {C : ℝ}, (∀ᶠ t in 𝓝[<] b, D t ≤ C * Real.log (Real.exp 1 * y t)) →
      (∃ C₁, ∀ᶠ ε in 𝓝[>] 0, y (b - ε) ≤ C₁ * (ε⁻¹ * Real.log (1 / ε) ^ 2)) ∧
      ∃ C₂, ∀ᶠ ε in 𝓝[>] 0, D (b - ε) ≤ C₂ * Real.log (1 / ε)) ∧
    (∀ {C q : ℝ}, 0 ≤ q → q < 1 / 2 → (∀ᶠ t in 𝓝[<] b, D t ≤ C * y t ^ q) →
      ∃ C₃, ∀ᶠ ε in 𝓝[>] 0, y (b - ε) ≤ C₃ * ε ^ (-(1 / (1 - 2 * q)))) :=
  ⟨fun h => ⟨eventually_le_inv_mul_log_sq_of_deriv_ge_of_le_log hab hy1 hac htend hD1 hk hder h,
      eventually_le_log_of_deriv_ge_of_le_log hab hy1 hac htend hD1 hk hder h⟩,
    fun _ hq h => eventually_le_rpow_of_deriv_ge_of_le_rpow hab hy1 hac htend hD1 hk hder hq h⟩

end PercLib.Analysis
