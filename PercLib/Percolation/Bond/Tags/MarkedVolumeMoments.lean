/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project, written on 2026-11-22. A restatement of library lemmas; no upstream
code is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.MarkedVolumeMoments

/-!
# Correspondence wrapper for marked-volume and damped-cluster moments

Tagged restatement of the moment bounds for the marked volume and the damped cluster size on a
finite vertex type with a transitive bond law. All mathematical inputs are proved in
`PercLib.Percolation.Bond.MarkedVolumeMoments`.

## Main results

* `markedVolume_secondMoment_bounds_and_dampedCluster_moments_le`: with marks of probability
  `γ ∈ (0,1)`, `r = 1 - γ`, `S = |C_o|`, `M = P(o ↔ marks)`, `Z = ∑_x 1{x ↔ marks}`,
  `Q = E Z²`, `χ₀ = E[S r^S]`, `χ₁ = E[S (1 - r^S)]` and `B = E[S² r^S]`:
  `N χ₁ ≤ Q ≤ N² M² + N χ₁`, `χ₁ ≤ γ χ³`, `χ₀ ≤ (r/γ) M` and `B ≤ (r/γ) χ₁`.
-/

@[expose] public section

noncomputable section

open MeasureTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-- On a finite vertex type with `N` vertices and a transitive bond law, mark each vertex
independently with probability `γ ∈ (0,1)` (the marks are a random set with law
`prodBernoulli (fun _ => γ)`, independent of the bonds) and write `r = 1 - γ`. With
`S = |C_o|`, `χ = E S`, `M = P(o ↔ marks)`, `Z = ∑_x 1{x ↔ marks}`, `Q = E Z²`,
`χ₀ = E[S r^S]`, `χ₁ = E[S (1 - r^S)]` and `B = E[S² r^S]`:
`N χ₁ ≤ Q ≤ N² M² + N χ₁`, `χ₁ ≤ γ χ³`, `χ₀ ≤ (r/γ) M` and `B ≤ (r/γ) χ₁`. -/
@[tag "6AEH"]
theorem markedVolume_secondMoment_bounds_and_dampedCluster_moments_le {V : Type*}
    [Fintype V] :
    ∀ q : Sym2 V → unitInterval,
      (∀ x y : V, ∃ e : V ≃ V, e x = y ∧ (law q).map (fun ω => Sym2.map e '' ω) = law q) →
      ∀ γ : unitInterval, 0 < (γ : ℝ) → (γ : ℝ) < 1 → ∀ o : V,
        (Fintype.card V : ℝ≥0∞) * ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
            (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q ≤
          ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
            (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) ∧
        ∫⁻ z, (∑ x, {z : Config V × Set V | (cluster z.1 x ∩ z.2).Nonempty}.indicator
            (fun _ => (1 : ℝ≥0∞)) z) ^ 2 ∂((law q).prod (prodBernoulli fun _ : V => γ)) ≤
          (Fintype.card V : ℝ≥0∞) ^ 2 * ((law q).prod (prodBernoulli fun _ : V => γ))
              {z | (cluster z.1 o ∩ z.2).Nonempty} ^ 2 +
            (Fintype.card V : ℝ≥0∞) * ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
              (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q ∧
        ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
            (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q ≤
          ENNReal.ofReal γ * chi q o ^ 3 ∧
        ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) * ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard
            ∂law q ≤
          ENNReal.ofReal (1 - γ) / ENNReal.ofReal γ *
            ((law q).prod (prodBernoulli fun _ : V => γ)) {z | (cluster z.1 o ∩ z.2).Nonempty} ∧
        ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard
            ∂law q ≤
          ENNReal.ofReal (1 - γ) / ENNReal.ofReal γ *
            ∫⁻ ω, ((cluster ω o).ncard : ℝ≥0∞) *
              (1 - ENNReal.ofReal (1 - γ) ^ (cluster ω o).ncard) ∂law q :=
  fun q hT _γ hγ0 hγ1 o =>
    ⟨card_mul_lintegral_ncard_mul_one_sub_pow_le_lintegral_sq q hT hγ0 hγ1 o,
      lintegral_sq_le_card_sq_mul_add_card_mul q hT hγ0 hγ1 o,
      lintegral_ncard_mul_one_sub_pow_le q hT o,
      lintegral_ncard_mul_pow_le q hγ0 hγ1 o,
      lintegral_ncard_sq_mul_pow_le q hγ0 o⟩

end PercLib.Percolation.Bond
