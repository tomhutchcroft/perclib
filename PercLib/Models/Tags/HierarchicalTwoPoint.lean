/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper assembled from lemmas proved in the imported modules; no new definition
is introduced. Mathematical reference: T. Hutchcroft, *The critical two-point function for
long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1, Section 2.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalPointwiseCritical

/-!
# Hierarchical two-point bounds from block means and boundary flux: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Models.HierarchicalPointwiseCritical` and `law_localConn_le_tau`.

## Main results

* `hierarchical_two_point_of_boundaryFlux`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

variable {d L : ℕ}

open Classical in
/-- On `V = ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `d ≥ 1`, `c > 0`, `0 < α < d`, write
`h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}` and let `J` be a translation-invariant kernel
with `J(u,v) ≥ c L^{-(d+α) h(v-u)}` off the diagonal (the model of 7AER). Let `0 ≤ a < b` with
`χ_β(0) < ∞` for every `β ∈ (a, b)`, and suppose rooted damping holds at `b` in every block:
with `q_n` the profile `intensityProfile J b` restricted to the pairs inside `Λ_n` and
`R_n = tightnessScale q_n Λ_n`,
`P_{q_n}(|K_x ∩ Λ_n| ≥ t R_n) ≤ e^{1-t/9} P_{q_n}(|K_x ∩ Λ_n| ≥ R_n)` for `x ∈ Λ_n`,
`t ≥ 1` (the hypotheses of 655W). Suppose also
`J(u,v) ≤ C₀ L^{-(d+α) h(v-u)}` off the diagonal and the boundary-flux inequalities
`b ∑_{u ∈ Λ_n} τ_n(0,u) ∑_{v ∉ Λ_n} J(u,v) ≥ 1` for all `n ≥ 0`, where
`τ_n(0,u) = P_b(0 ↔ u inside Λ_n)`. Then there are `c₁, C₁ > 0` such that for `n ≥ 1` and
`h x = n`, `c₁ L^{-(d-α)n} ≤ τ_n(0,x) ≤ τ_b(0,x) ≤ C₁ L^{-(d-α)n}`. The rooted-damping
hypothesis is not used: the library proves it for independent bonds (12NL). `[NeZero L]`
makes the balls `Λ_n` finite (it follows from `L ≥ 2`). -/
@[tag "7YNX"]
theorem hierarchical_two_point_of_boundaryFlux [NeZero L] (hL : 2 ≤ L) (hd : 1 ≤ d)
    {α c C₀ : ℝ} (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤)
    (_hdamp : ∀ n : ℕ, ∀ x : ℕ →₀ (Fin d → ZMod L), x.support.sup Nat.succ ≤ n →
      ∀ t : ℝ, 1 ≤ t →
        law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2
            then intensityProfile J b e else 0)
          {ω | t * (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
              z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0)
              (finite_level_ball n).toFinset : ℝ) ≤
            (clusterIntersection (finite_level_ball n).toFinset ω x : ℝ)} ≤
        ENNReal.ofReal (Real.exp (1 - t / 9)) *
          law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2
              then intensityProfile J b e else 0)
            {ω | (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
                z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0)
                (finite_level_ball n).toFinset : ℝ) ≤
              (clusterIntersection (finite_level_ball n).toFinset ω x : ℝ)})
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (hflux : ∀ n : ℕ, 1 ≤ (b : ℝ≥0∞) * ∑ u ∈ (finite_level_ball n).toFinset,
      law (intensityProfile J b)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 u) *
      ∑' v, (if v ∈ (finite_level_ball n).toFinset then 0 else (J s(u, v) : ℝ≥0∞))) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ →₀ (Fin d → ZMod L),
      x.support.sup Nat.succ = n →
      ENNReal.ofReal (c₁ * (L : ℝ) ^ (-((d : ℝ) - α) * n)) ≤
          law (intensityProfile J b)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) ∧
        law (intensityProfile J b)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) ≤
          tau (intensityProfile J b) 0 x ∧
        tau (intensityProfile J b) 0 x ≤ ENNReal.ofReal (C₁ * (L : ℝ) ^ (-((d : ℝ) - α) * n)) := by
  obtain ⟨c₁, hc₁, hlow⟩ := exists_ofReal_le_law_localConn_of_boundaryFlux hL hd hc hα hαd J hJt
    hJ hJu hab hχ hflux
  obtain ⟨C₁, hC₁, hup⟩ := exists_tau_le_of_chi_lt_top hL hd hc hα hαd J hJt hJ hJu hab hχ
  exact ⟨c₁, C₁, hc₁, hC₁, fun n hn x hx =>
    ⟨hlow n hn x hx, law_localConn_le_tau _ _ 0 x, hup n hn x hx⟩⟩

end PercLib.Models
