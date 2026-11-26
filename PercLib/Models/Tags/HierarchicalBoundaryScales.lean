/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's boundary-scale theorems for hierarchical balls. No upstream
code is copied and no definition is added. Mathematical reference: T. Hutchcroft, *The critical
two-point function for long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1
(off-critical estimates from finite-ball boundary scales).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalBoundaryScales

/-!
# Boundary scales of hierarchical balls (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `boundaryFlux_ball_eq_and_boundaryThreshold_spec`: the flux identity `Φ_β(Λ_n) = r_n(β)χ_n(β)`,
  strict monotonicity of the flux, and `β_n ∈ (0, b)` as the unique solution of
  `Φ_β(Λ_n) = 1/2`.
* `chi_le_two_mul_and_ballSusceptibility_bounds`: finite-ball control at the boundary
  thresholds.
-/

@[expose] public section
noncomputable section

open Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-- **Hierarchical boundary thresholds.** On `V = ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`,
`0 < α < d`, let `J` be translation invariant with
`c L^{-(d+α) h(v-u)} ≤ J(u,v) ≤ C L^{-(d+α) h(v-u)}` for `u ≠ v` (`c > 0`), and let `b` satisfy
`Φ_b(Λ_n) ≥ 1` for every `n`, where `Φ_β(Λ_n) = boundaryFlux q_β Λ_n 0` and
`q_β = intensityProfile J β`. Then for every `n`:
`Φ_β(Λ_n) = r_n(β) χ_n(β)` for every `β`, with `r_n = ballExitRate J n` and
`χ_n(β) = ∑_z P_β(0 ↔ z inside Λ_n)`; `β ↦ Φ_β(Λ_n)` is strictly increasing; and
`β_n = boundaryThreshold J n` lies in `(0, b)`, satisfies `Φ_{β_n}(Λ_n) = 1/2` and is the only
solution of that equation. The further quantities of the definition are
`b_n = maxBoundaryThreshold J n`, `m(β) = boundaryScaleIndex J β` and
`ξ(β) = boundaryLength J β`. -/
@[tag "GPDF"]
theorem boundaryFlux_ball_eq_and_boundaryThreshold_spec (hL : 2 ≤ L) {α c C : ℝ}
    (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (b : ℝ≥0)
    (hb : ∀ n, 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0) :
    ∀ n : ℕ,
      (∀ β : ℝ≥0, boundaryFlux (intensityProfile J β)
          (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 =
        ballExitRate J n β * ∑' z, law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z)) ∧
      StrictMono (fun β : ℝ≥0 => boundaryFlux (intensityProfile J β)
          (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0) ∧
      boundaryThreshold J n ∈ Ioo 0 b ∧
      boundaryFlux (intensityProfile J (boundaryThreshold J n))
          (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 = 2⁻¹ ∧
      ∀ β : ℝ≥0, boundaryFlux (intensityProfile J β)
          (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 = 2⁻¹ →
        β = boundaryThreshold J n := fun n =>
  ⟨fun β => boundaryFlux_ball_eq_ballExitRate_mul J hJt β n,
    strictMono_boundaryFlux_ball J hL hα hαd hc hJt hlow hup n,
    boundaryThreshold_mem_Ioo J hL hα hαd hc hJt hlow hup (hb n),
    boundaryFlux_boundaryThreshold J hL hα hαd hc hJt hlow hup (hb n),
    fun _ hβ => eq_boundaryThreshold_of_boundaryFlux_eq J hL hα hαd hc hJt hlow hup (hb n) hβ⟩

/-- **Finite-ball control at the hierarchical boundary thresholds.** In the setting of
`boundaryFlux_ball_eq_and_boundaryThreshold_spec`, assume also
`τ_b(0, x) ≤ A ⟨x⟩^{-(d-α)}` for every `x`, with `⟨x⟩ = L^{h x}`. Then
`χ(β) ≤ 2 χ_n(β)` whenever `β ≤ β_n`, and there are `c₀, C₀ > 0`, independent of `n` and `β`,
with `c₀ L^{αn} ≤ χ_n(β) ≤ χ_n(b) ≤ C₀ L^{αn}` for `b_n ≤ β ≤ b`, and
`χ(β) ≤ 2 C₀ L^α L^{αn}` whenever `β ≤ b_{n+1}` (in particular for `b_n ≤ β ≤ b_{n+1}`).
Here `χ(β) = chi q_β 0`, `χ_n(β) = ∑_z P_β(0 ↔ z inside Λ_n)`, `β_n = boundaryThreshold J n`
and `b_n = maxBoundaryThreshold J n`. -/
@[tag "6F2J"]
theorem chi_le_two_mul_and_ballSusceptibility_bounds (hL : 2 ≤ L) {α c C : ℝ}
    (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (b : ℝ≥0) {A : ℝ}
    (hτ : ∀ x, tau (intensityProfile J b) 0 x ≤
      ENNReal.ofReal (A * (L : ℝ) ^ (-((d : ℝ) - α) * (x.support.sup Nat.succ : ℕ))))
    (hb : ∀ n, 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0) :
    (∀ n : ℕ, ∀ β : ℝ≥0, β ≤ boundaryThreshold J n →
      chi (intensityProfile J β) 0 ≤ 2 * ∑' z, law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z)) ∧
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      (∀ n : ℕ, ∀ β : ℝ≥0, maxBoundaryThreshold J n ≤ β → β ≤ b →
        ENNReal.ofReal (c₀ * (L : ℝ) ^ (α * n)) ≤ ∑' z, law (intensityProfile J β)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ∧
          ∑' z, law (intensityProfile J β)
              (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ≤
            ∑' z, law (intensityProfile J b)
              (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ∧
          ∑' z, law (intensityProfile J b)
              (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ≤
            ENNReal.ofReal (C₀ * (L : ℝ) ^ (α * n))) ∧
      (∀ n : ℕ, ∀ β : ℝ≥0, β ≤ maxBoundaryThreshold J (n + 1) →
        chi (intensityProfile J β) 0 ≤
          ENNReal.ofReal (2 * C₀ * (L : ℝ) ^ α * (L : ℝ) ^ (α * n))) :=
  ⟨fun n _ hβ => chi_le_two_mul_of_le_boundaryThreshold J hL hα hαd hc hJt hlow hup (hb n) hβ,
    exists_ballSusceptibility_bounds_of_maxBoundaryThreshold_le J hL hα hαd hc hJt hlow hup b hτ
      hb⟩

end PercLib.Models
