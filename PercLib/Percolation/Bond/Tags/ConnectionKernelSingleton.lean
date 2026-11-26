/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for uniform positivity of the connection kernel from singleton-cluster
probabilities (wiki article `connection-kernels`). All mathematical inputs are proved in the
imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ConnectionKernelSingleton

/-!
# Uniform kernel positivity from singleton probabilities: correspondence

Restates `sum_finset_mul_connProb_ge_sum_isolated`, `sum_finset_mul_connProb_ge_mul_sum_sq`
and `exp_neg_mul_le_law_cluster_eq_singleton`.

## Main results

* `connProb_quadratic_form_ge_singleton`
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- With `T(x, y) = μ(x ↔ y)` and `p_x = μ(C(x) = {x})`: every finitely supported real `f`
satisfies `∑_{x,y} f(x) T(x,y) f(y) ≥ ∑_x p_x f(x)²`; if `p_x ≥ δ` for every `x`, then
`T ⪰ δ I` as a quadratic form; and for independent bonds with probabilities
`1 - e^{-β J(x,y)}`, `β ≥ 0` finite, `J ≥ 0` and `∑_{y ≠ x} J(x, y) ≤ L` for every `x`, one
may take `δ = e^{-β L}`. -/
@[tag "R1HO"]
theorem connProb_quadratic_form_ge_singleton [Countable V] :
    (∀ (μ : Measure (Config V)) [IsProbabilityMeasure μ] (f : V →₀ ℝ),
      ∑ x ∈ f.support, (μ {ω | cluster ω x = {x}}).toReal * f x ^ 2 ≤
        ∑ x ∈ f.support, ∑ y ∈ f.support, f x * f y * (connProb μ x y).toReal) ∧
    (∀ (μ : Measure (Config V)) [IsProbabilityMeasure μ] (δ : ℝ),
      (∀ x, δ ≤ (μ {ω | cluster ω x = {x}}).toReal) → ∀ f : V →₀ ℝ,
        δ * ∑ x ∈ f.support, f x ^ 2 ≤
          ∑ x ∈ f.support, ∑ y ∈ f.support, f x * f y * (connProb μ x y).toReal) ∧
    ∀ (q : Sym2 V → unitInterval) (β L : ℝ) (J : Sym2 V → ℝ), 0 ≤ β → (∀ e, 0 ≤ J e) →
      (∀ x y : V, x ≠ y → (q s(x, y) : ℝ) = 1 - Real.exp (-(β * J s(x, y)))) →
      (∀ x, Summable fun y : {y // y ≠ x} => J s(x, y.1)) →
      (∀ x, ∑' y : {y // y ≠ x}, J s(x, y.1) ≤ L) →
      ∀ x, Real.exp (-(β * L)) ≤ (law q {ω : Config V | cluster ω x = {x}}).toReal :=
  ⟨fun μ _ f => sum_finset_mul_connProb_ge_sum_isolated μ f.support f,
    fun μ _ _ hδ f => sum_finset_mul_connProb_ge_mul_sum_sq μ hδ f.support f,
    fun q _ _ J hβ hJ hq hJs hL x =>
      exp_neg_mul_le_law_cluster_eq_singleton q hβ J hJ hq x (hJs x) (hL x)⟩

end PercLib.Percolation.Bond
