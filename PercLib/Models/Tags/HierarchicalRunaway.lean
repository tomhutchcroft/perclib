/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's runaway theorems. No upstream code is copied and no
definition is added. Mathematical reference: T. Hutchcroft, *The critical two-point function for
long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1, Proposition 2.2 and
Corollary 2.3.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalRunawayInterval

/-!
# Hierarchical runaway bound (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `sq_tightnessScale_lt_and_le_of_chi_lt_top`: the block-quantile bound from finite
  susceptibility, strict at a parameter and non-strict up to the end of an interval.
* `rootCriticalIntensity_bounds_and_sq_tightnessScale_le`: `0 < 1/B ≤ β_c ≤ A/4` for the common
  row sum `B`, and the quantile bound at `β_c`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

open Classical in
/-- On `ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `c, α > 0`, a translation-invariant kernel `J`
with `J(u,v) ≥ c L^{-(d+α)j}` at first common level `j`: with `R_n(β)` the quantile
`tightnessScale` of the origin's level-`n` block under the profile restricted to that block,
`N = L^{dℓ}`, `e^{-N/(8e)} ≤ 1/4`, `L^{(d-α)ℓ} ≥ 16e²` and `A = (4/c) L^{(d+α)ℓ} log(2N²)`:
if `β > 0` and `χ(β) < ∞` then `R_n(β)² < (A/β) L^{(d+α)n}` for every `n`; and if `a < b` and
`χ(β) < ∞` for every `β ∈ (a, b)` then `R_n(β)² ≤ (A/b) L^{(d+α)n}` for every `n` and every
`β ≤ b`. -/
@[tag "2XJX"]
theorem sq_tightnessScale_lt_and_le_of_chi_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) :
    (∀ β : ℝ≥0, 0 < β → chi (intensityProfile J β) 0 < ⊤ → ∀ n : ℕ,
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
          (finite_level_ball n).toFinset : ℝ) ^ 2 <
        (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
          (L : ℝ) ^ (((d : ℝ) + α) * n)) ∧
    (∀ a b : ℝ≥0, a < b → (∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) →
      ∀ (n : ℕ) (β : ℝ≥0), β ≤ b →
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
          (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
        (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / b *
          (L : ℝ) ^ (((d : ℝ) + α) * n)) :=
  ⟨fun _ hβ hχ n => sq_tightnessScale_lt_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ hβ hχ n,
    fun _ _ hab hχ n _ hβb =>
      sq_tightnessScale_le_of_chi_lt_top_on_Ioo hL hc hα J hJt hJ hexp hℓ hab hχ n hβb⟩

open Classical in
/-- In the setting of `sq_tightnessScale_lt_and_le_of_chi_lt_top`, with `0 < α < d` and a
finite common off-diagonal row sum `B = ∑_{v ≠ u} J(u, v)`: `B > 0`,
`1/B ≤ β_c ≤ A/4 < ∞` with `A = (4/c) L^{(d+α)ℓ} log(2N²)`, and
`R_n(β_c)² ≤ (A/β_c) L^{(d+α)n}` for every `n`, and for every finite `S ∋ 0` the boundary flux
bound `β_c ∑_{u ∈ S} τ_{S,β_c}(0,u) ∑_{v ∉ S} J(u,v) ≥ 1`. -/
@[tag "FF30"]
theorem rootCriticalIntensity_bounds_and_sq_tightnessScale_le [NeZero L] (hL : 2 ≤ L)
    {α c : ℝ} (hc : 0 < c) (hα : 0 < α) (hαd : α < d)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {B : ℝ≥0} (hB : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u = B)
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) :
    0 < B ∧ (B : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J 0 ∧
      rootCriticalIntensity J 0 ≤ ENNReal.ofReal
        ((4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / 4) ∧
      (∀ n : ℕ,
        (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then
              intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0)
            (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
          (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) /
            (rootCriticalIntensity J 0).toNNReal * (L : ℝ) ^ (((d : ℝ) + α) * n)) ∧
      ∀ S : Finset (ℕ →₀ (Fin d → ZMod L)), 0 ∈ S →
        1 ≤ rootCriticalIntensity J 0 * ∑ u ∈ S,
          law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
            (localConn (S : Set (ℕ →₀ (Fin d → ZMod L))) 0 u) *
          ∑' v, (if v ∈ S then 0 else (J s(u, v) : ℝ≥0∞)) := by
  have hd : 1 ≤ d := by
    have : 0 < d := by exact_mod_cast hα.trans hαd
    omega
  have hJs : ∀ u, Summable fun v => (J s(u, v) : ℝ) := fun u =>
    summable_of_rowSum_ne_top J (by rw [hB u]; exact ENNReal.coe_ne_top)
  have hB0 : 0 < B := by
    have := rowSum_pos_hierarchical hd hL hc J hJ 0
    rw [hB 0] at this
    exact_mod_cast this
  have hlow : (B : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J 0 :=
    inv_le_rootCriticalIntensity J B (fun v => (hB v).le) 0
  have hup := rootCriticalIntensity_hierarchical_le hL hc hα J hJt hJ hJs hexp hℓ
  have hT : ∀ x y : ℕ →₀ (Fin d → ZMod L),
      ∃ σ : (ℕ →₀ (Fin d → ZMod L)) ≃ (ℕ →₀ (Fin d → ZMod L)),
        σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := fun x y =>
    ⟨Equiv.addRight (y - x), by simp, fun e => by
      induction e using Sym2.ind with
      | h u v => simpa using hJt (y - x) u v⟩
  have hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ⊤ := fun u => by
    rw [hB u]; exact ENNReal.coe_lt_top
  have hfin : rootCriticalIntensity J 0 < ⊤ := hup.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hB0, hlow, hup,
    sq_tightnessScale_le_at_rootCriticalIntensity hL hc hα J hJt hJ hJs hexp hℓ ?_,
    fun S hS => by
      convert (one_le_boundaryFlux_at_rootCriticalIntensity J hT hrow hfin S hS).1.trans
        (one_le_boundaryFlux_at_rootCriticalIntensity J hT hrow hfin S hS).2⟩
  exact ENNReal.toNNReal_pos ((ENNReal.inv_pos.2 ENNReal.coe_ne_top).trans_le hlow).ne'
    (hup.trans_lt ENNReal.ofReal_lt_top).ne

end PercLib.Models
