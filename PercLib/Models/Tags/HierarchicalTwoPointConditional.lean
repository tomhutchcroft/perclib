/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's conditional two-point theorems. No upstream code is copied
and no definition is added. Mathematical reference: T. Hutchcroft, *The critical two-point
function for long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1,
Propositions 2.7, 2.10 and 2.12, and Corollary 1.5.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalTwoPointConditional
public import PercLib.Models.HierarchicalVolumeExponent

/-!
# Conditional hierarchical two-point bounds (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.
The rooted damping estimate in the block-restricted form holds for every profile
(`rooted_upper_tail`), so it is not a hypothesis here.

## Main results

* `restricted_mean_recursion_and_le_of_chi_lt_top`: the quadratic recursion and the upper
  bound for the block-restricted means at an endpoint.
* `law_localConn_bounds_of_chi_lt_top_of_boundaryFlux`: the two-sided pointwise two-point
  bounds at an endpoint, given the boundary flux.
* `add_div_sub_le_of_law_le_encard_cluster_eq_rpow`: a logarithmic critical volume-tail exponent `δ`
  satisfies `δ ≥ (d+α)/(d-α)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

open Classical in
/-- On `ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `c > 0`, `0 < α < d`, a translation-invariant
kernel `J` with `J(u, v) ≥ c L^{-(d+α)j}` at first common level `j`, and `a < b` with
`χ(β) < ∞` for every `β ∈ (a, b)`: with `a_n = E_b |K_0 ∩ Λ_n|` under the profile restricted to
the pairs inside `Λ_n`, there are `k, C' > 0` with `a_{n+1} ≥ k L^{-αn} a_n²` and
`a_n ≤ C' L^{αn}` for every `n`. -/
@[tag "655W"]
theorem restricted_mean_recursion_and_le_of_chi_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) :
    (∃ k : ℝ, 0 < k ∧ ∀ n : ℕ,
      ENNReal.ofReal (k * (L : ℝ) ^ (-(α * n))) *
          (∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
            ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
              z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0)) ^ 2 ≤
        ∫⁻ ω, (clusterIntersection (finite_level_ball (n + 1)).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n + 1}.sym2 then intensityProfile J b e else 0)) ∧
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ,
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0) ≤
        ENNReal.ofReal (C' * (L : ℝ) ^ (α * n)) :=
  ⟨exists_restricted_mean_sq_le_succ_of_chi_lt_top hL hc hα hαd J hJt hJ hab hχ,
    exists_restricted_mean_le_of_chi_lt_top hL hc hα hαd J hJt hJ hab hχ⟩

open Classical in
/-- In the setting of `restricted_mean_recursion_and_le_of_chi_lt_top`, suppose also
`J(u, v) ≤ C₀ L^{-(d+α)j}` at first common level `j`, and the boundary flux
`b ∑_{u ∈ Λ_n} τ_n(0, u) ∑_{v ∉ Λ_n} J(u, v) ≥ 1` for every `n`, where
`τ_n(0, u) = P_b(0 ↔ u using only edges in Λ_n)`. Then there are `c₁, C₁ > 0` with
`c₁ L^{-(d-α)n} ≤ τ_n(0, x) ≤ τ(0, x) ≤ C₁ L^{-(d-α)n}` whenever `x ∈ Λ_n \ Λ_{n-1}`,
`n ≥ 1`. -/
theorem law_localConn_bounds_of_chi_lt_top_of_boundaryFlux [NeZero L] (hL : 2 ≤ L)
    {α c C₀ : ℝ} (hc : 0 < c) (hα : 0 < α) (hαd : α < d)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤)
    (hflux : ∀ n : ℕ, 1 ≤ (b : ℝ≥0∞) * ∑ u ∈ (finite_level_ball n).toFinset,
      law (intensityProfile J b)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 u) *
        ∑' v, if n < v.support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ →₀ (Fin d → ZMod L),
      x.support.sup Nat.succ = n →
      ENNReal.ofReal (c₁ * (L : ℝ) ^ (-(((d : ℝ) - α) * n))) ≤
          law (intensityProfile J b)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) ∧
        law (intensityProfile J b)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) ≤
          tau (intensityProfile J b) 0 x ∧
        tau (intensityProfile J b) 0 x ≤
          ENNReal.ofReal (C₁ * (L : ℝ) ^ (-(((d : ℝ) - α) * n))) :=
  exists_law_localConn_bounds_of_boundaryFlux hL hc hα hαd J hJt hJ hJu hab hχ hflux

open Classical in
/-- On `ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `c > 0`, `0 < α < d`, a translation-invariant
kernel `J` with `c L^{-(d+α)j} ≤ J(u, v) ≤ C₀ L^{-(d+α)j}` at first common level `j`, and
`β_c = rootCriticalIntensity J 0`: if the critical full-cluster tail has a finite positive
logarithmic exponent `δ`, `P_{β_c}(|K_0| ≥ n) = n^{-1/δ + ε(n)}` for `n ≥ 1` with `ε(n) → 0`,
then `δ ≥ (d+α)/(d-α)`. The bound holds for every `0 < α < d`; `α > d/3` is not needed. -/
@[tag "7GDE"]
theorem add_div_sub_le_of_law_le_encard_cluster_eq_rpow [NeZero L] (hL : 2 ≤ L) {α c C₀ δ : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (hδ : 0 < δ) {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (htail : ∀ n : ℕ, 1 ≤ n →
      law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
          {ω | (n : ℕ∞) ≤ (cluster ω 0).encard} = ENNReal.ofReal ((n : ℝ) ^ (-1 / δ + ε n))) :
    ((d : ℝ) + α) / (d - α) ≤ δ :=
  div_le_of_law_le_encard_cluster_eq_rpow hL hc hα hαd J hJt hJ hJu hδ hε htail

end PercLib.Models
