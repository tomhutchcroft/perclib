/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's boundary-contraction, finite-set-criterion and hierarchical
ball-sum theorems, and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code
is copied and no definition is added. Mathematical reference: T. Hutchcroft, *The critical
two-point function for long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1
(off-critical estimates from finite-ball boundary scales).
-/
module

public import PercLib.Models.HierarchicalBoundaryScales.Defs
public import PercLib.Models.HierarchicalBallSusceptibility
public import PercLib.Models.HierarchicalPowerKernel
public import PercLib.Models.HierarchicalTranslation
public import PercLib.Models.HierarchicalRunawayInterval
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.IntensityScaling

/-!
# Boundary scales of hierarchical balls below an endpoint

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ` and `Λ_n = {h ≤ n}`. For a
translation-invariant kernel `J` and the profile `q_β = 1 - e^{-βJ}`, let
`χ_n(β) = ∑_z P_β(0 ↔ z inside Λ_n)` be the internal-ball susceptibility and
`Φ_β(Λ_n) = boundaryFlux q_β Λ_n 0` the boundary flux of the ball. With the exit rate
`r_n(β) = ∑_{h y > n} q_β(0, y)` one has `Φ_β(Λ_n) = r_n(β) χ_n(β)`.

If `J` has two-sided power-law bounds and `Φ_b(Λ_n) ≥ 1`, the flux is continuous and strictly
increasing in `β`, vanishes at `0`, and so crosses `1/2` at a unique `β_n ∈ (0, b)`. We put
`b_n = max_{k ≤ n} β_k`, `m(β) = min {n : β ≤ b_n}` (`⊤` if there is none) and
`ξ(β) = L^{m(β)}` (`⊤` if there is none).

Finite-ball control: `χ(β) ≤ 2 χ_n(β)` for `β ≤ β_n` (boundary contraction), and if moreover
`τ_b(0, x) ≤ A L^{-(d-α) h x}`, then `c₀ L^{αn} ≤ χ_n(β) ≤ χ_n(b) ≤ C₀ L^{αn}` for
`b_n ≤ β ≤ b` and `χ(β) ≤ 2 C₀ L^α L^{αn}` for `β ≤ b_{n+1}`.

The quantities `r_n`, `β_n`, `b_n`, `m` and `ξ` are defined in
`PercLib.Models.HierarchicalBoundaryScales.Defs`.

## Main results

* `boundaryFlux_ball_eq_ballExitRate_mul`: `Φ_β(Λ_n) = r_n(β) χ_n(β)`.
* `strictMono_ballExitRate`, `strictMono_boundaryFlux_ball`: strict monotonicity in `β`.
* `boundaryThreshold_mem_Ioo`, `boundaryFlux_boundaryThreshold`,
  `eq_boundaryThreshold_of_boundaryFlux_eq`: `β_n ∈ (0, b)` is the unique solution of
  `Φ_β(Λ_n) = 1/2`.
* `chi_le_two_mul_of_le_boundaryThreshold`: `χ(β) ≤ 2 χ_n(β)` for `β ≤ β_n`.
* `exists_ballSusceptibility_bounds_of_maxBoundaryThreshold_le`: `c₀ L^{αn} ≤ χ_n(β)` and
  `χ_n(b) ≤ C₀ L^{αn}` for `b_n ≤ β ≤ b`, with the bound on `χ(β)` for `β ≤ b_{n+1}`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-! ### The exit rate and the flux identity -/

section Flux

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)

/-- The internal-ball susceptibility is the finite sum over the ball. -/
theorem tsum_law_localConn_ball_eq_sum (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval)
    (n : ℕ) :
    ∑' z, law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) =
      ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
        law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) :=
  tsum_eq_sum fun z hz => by
    have hz' : z ∉ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} := fun h =>
      hz (mem_toFinset_level_ball_finset.2 h)
    rw [localConn_of_notMem_right hz', measure_empty]

omit [NeZero L] in
/-- `1 ≤ χ_n(β)`: the origin is joined to itself. -/
theorem one_le_tsum_law_localConn_ball (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval)
    (n : ℕ) :
    1 ≤ ∑' z, law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) := by
  calc (1 : ℝ≥0∞) = law q (localConn {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n} 0 0) := by
        rw [localConn_self (by simp), measure_univ]
    _ ≤ _ := ENNReal.le_tsum (f := fun z => law q (localConn {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n} 0 z)) 0

/-- `χ_n(β) < ∞`: it is at most the volume of the ball. -/
theorem tsum_law_localConn_ball_ne_top (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval)
    (n : ℕ) :
    ∑' z, law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ≠ ⊤ := by
  have h := tsum_law_induce_conn_le_card (q := q)
    (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0
  rw [coe_toFinset_level_ball] at h
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) h

/-- `β ↦ χ_n(β)` is monotone. -/
theorem monotone_tsum_law_localConn_ball (n : ℕ) :
    Monotone fun β : ℝ≥0 => ∑' z, law (intensityProfile J β)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) :=
  fun _ _ h => ENNReal.tsum_le_tsum fun z =>
    law_intensityProfile_mono (isUpperSet_localConn _ 0 z) (measurableSet_localConn _ 0 z) J h

omit [NeZero L] in
/-- `r_n(β) ≤ β ∑_{h y > n} J(0, y)`. -/
theorem ballExitRate_le_mul (n : ℕ) (β : ℝ≥0) :
    ballExitRate J n β ≤ β * ∑' y : ℕ →₀ (Fin d → ZMod L),
      if n < y.support.sup Nat.succ then (J s(0, y) : ℝ≥0∞) else 0 := by
  rw [ballExitRate, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs
  · exact_mod_cast intensityProfile_toNNReal_le J β _
  · simp

/-- Power-law form of the exit-rate bound:
`r_n(β) ≤ β C (1 - L^{-d}) L^{-αn} / (L^α - 1)`. -/
theorem ballExitRate_le_of_powerLaw (hL : 2 ≤ L) {α C : ℝ} (hα : 0 < α)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (n : ℕ) (β : ℝ≥0) :
    ballExitRate J n β ≤ β * ENNReal.ofReal (C * (1 - (L : ℝ) ^ (-(d : ℝ))) *
      (L : ℝ) ^ (-(α * n)) / ((L : ℝ) ^ α - 1)) :=
  (ballExitRate_le_mul J n β).trans (mul_le_mul_right
    (tsum_level_gt_le_of_powerLaw hL hα J hJ n (u := 0) (by simp)) _)

/-- **The flux identity.** For a translation-invariant kernel,
`Φ_β(Λ_n) = r_n(β) χ_n(β)`: translating by a point of the ball permutes its complement. -/
theorem boundaryFlux_ball_eq_ballExitRate_mul
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)) (β : ℝ≥0) (n : ℕ) :
    boundaryFlux (intensityProfile J β) (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 =
      ballExitRate J n β * ∑' z, law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) := by
  classical
  set S := (finite_level_ball (A := Fin d → ZMod L) n).toFinset with hS
  rw [boundaryFlux_eq, coe_toFinset_level_ball, tsum_law_localConn_ball_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u.support.sup Nat.succ ≤ n := mem_toFinset_level_ball_finset.1 hu
  rw [mul_comm, ballExitRate, ← ENNReal.tsum_mul_left, ← (Equiv.addRight u).tsum_eq]
  refine tsum_congr fun w => ?_
  simp only [Equiv.coe_addRight]
  have hw : w + u ∈ S ↔ w.support.sup Nat.succ ≤ n := by
    rw [mem_toFinset_level_ball_finset, level_le_iff_level_sub_le hu', add_sub_cancel_right]
  by_cases hwn : w.support.sup Nat.succ ≤ n
  · simp [hw, hwn, not_lt.2 hwn]
  · have hJ : J s(u, w + u) = J s(0, w) := by simpa using hJt u 0 w
    have hqe : intensityProfile J β s(u, w + u) = intensityProfile J β s(0, w) :=
      Subtype.ext (by simp only [intensityProfile, hJ])
    simp only [hw, hwn, not_le.1 hwn, ↓reduceIte, hqe]

omit [NeZero L] in
/-- A point at level `n + 1` exists when `d ≥ 1` and `L ≥ 2`. -/
theorem exists_level_eq_succ (hd : 1 ≤ d) (hL : 2 ≤ L) (n : ℕ) :
    ∃ y : ℕ →₀ (Fin d → ZMod L), y.support.sup Nat.succ = n + 1 := by
  have : Fact (1 < L) := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a, ha⟩ := exists_ne (0 : Fin d → ZMod L)
  exact ⟨Finsupp.single n a, by rw [Finsupp.support_single n ha, Finset.sup_singleton]⟩

/-- **Strict monotonicity of the exit rate.** Under two-sided power-law bounds,
`β ↦ r_n(β)` is strictly increasing. -/
theorem strictMono_ballExitRate (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c)
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (n : ℕ) : StrictMono (ballExitRate J n) := by
  intro β β' hββ'
  have hd : 1 ≤ d := by
    have : (0 : ℝ) < d := hα.trans hαd
    exact_mod_cast this
  have hfin : ballExitRate J n β ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (ballExitRate_le_of_powerLaw J hL hα hup n β)
  obtain ⟨y, hy⟩ := exists_level_eq_succ hd hL n
  have hy0 : (0 : ℕ →₀ (Fin d → ZMod L)) ≠ y := by
    rintro rfl
    simp at hy
  have hJ0 : 0 < J s(0, y) := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have := (mul_pos hc (Real.rpow_pos_of_pos hL0 _)).trans_le (hlow 0 y hy0)
    exact_mod_cast this
  refine ENNReal.tsum_lt_tsum hfin (fun v => ?_) (i := y) ?_
  · split_ifs
    · exact ENNReal.coe_le_coe.2 (intensityProfile_mono J hββ'.le _)
    · exact le_rfl
  · simp only [show n < y.support.sup Nat.succ by omega, ↓reduceIte]
    refine ENNReal.coe_lt_coe.2 ?_
    rw [← NNReal.coe_lt_coe]
    exact strictMono_intensityProfile J hJ0 hββ'

/-- **Strict monotonicity of the flux.** Under the same hypotheses and translation invariance,
`β ↦ Φ_β(Λ_n)` is strictly increasing. -/
theorem strictMono_boundaryFlux_ball (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (n : ℕ) : StrictMono fun β : ℝ≥0 => boundaryFlux (intensityProfile J β)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 := by
  intro β β' h
  simp only [boundaryFlux_ball_eq_ballExitRate_mul J hJt]
  have hχ0 : ∑' z, law (intensityProfile J β')
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_tsum_law_localConn_ball _ n)).ne'
  calc _ ≤ ballExitRate J n β * ∑' z, law (intensityProfile J β')
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) :=
        mul_le_mul_right (monotone_tsum_law_localConn_ball J n h.le) _
    _ < _ := ENNReal.mul_lt_mul_left hχ0 (tsum_law_localConn_ball_ne_top _ n)
        (strictMono_ballExitRate J hL hα hαd hc hlow hup n h)

end Flux

/-! ### The boundary thresholds -/

section Threshold

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)

/-- **Existence and uniqueness of the boundary threshold.** If `Φ_b(Λ_n) ≥ 1`, then
`β_n ∈ (0, b)`, `Φ_{β_n}(Λ_n) = 1/2`, and `β_n` is the only solution of `Φ_β(Λ_n) = 1/2`. -/
theorem boundaryThreshold_spec (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {n : ℕ} {b : ℝ≥0}
    (hb : 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0) :
    boundaryThreshold J n ∈ Ioo 0 b ∧
      boundaryFlux (intensityProfile J (boundaryThreshold J n))
        (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 = 2⁻¹ ∧
      ∀ β : ℝ≥0, boundaryFlux (intensityProfile J β)
        (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 = 2⁻¹ →
          β = boundaryThreshold J n := by
  set Φ : ℝ≥0 → ℝ≥0∞ := fun β => boundaryFlux (intensityProfile J β)
    (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 with hΦ
  have hstrict : StrictMono Φ := strictMono_boundaryFlux_ball J hL hα hαd hc hJt hlow hup n
  have hcont : Continuous Φ := continuous_boundaryFlux_intensity J
    (fun u => (rowSum_le_of_powerLaw hL hα J hup u).trans_lt ENNReal.ofReal_lt_top) _ 0
  have hΦ0 : Φ 0 = 0 := by
    refine le_antisymm ?_ bot_le
    simp only [hΦ, boundaryFlux_ball_eq_ballExitRate_mul J hJt]
    calc _ ≤ ((0 : ℝ≥0) : ℝ≥0∞) * (∑' y : ℕ →₀ (Fin d → ZMod L),
          if n < y.support.sup Nat.succ then (J s(0, y) : ℝ≥0∞) else 0) *
          ∑' z, law (intensityProfile J 0)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) :=
          mul_le_mul_left (ballExitRate_le_mul J n 0) _
      _ = 0 := by simp
  have hhalf : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  obtain ⟨β₀, ⟨-, hβ₀b⟩, hβ₀⟩ : (2⁻¹ : ℝ≥0∞) ∈ Φ '' Icc 0 b :=
    intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ b) hcont.continuousOn
      ⟨hΦ0 ▸ bot_le, hhalf.le.trans hb⟩
  have hleast : IsLeast {β : ℝ≥0 | 2⁻¹ ≤ Φ β} β₀ := by
    refine ⟨hβ₀.ge, fun β hβ => ?_⟩
    by_contra hlt
    exact (hstrict (not_le.1 hlt)).not_ge (hβ₀ ▸ hβ)
  have heq : boundaryThreshold J n = β₀ := hleast.csInf_eq
  refine ⟨⟨?_, ?_⟩, heq ▸ hβ₀, fun β hβ => heq ▸ hstrict.injective (hβ.trans hβ₀.symm)⟩
  · rw [heq, pos_iff_ne_zero]
    rintro rfl
    rw [hΦ0] at hβ₀
    exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top hβ₀.symm
  · rw [heq]
    refine lt_of_le_of_ne hβ₀b ?_
    rintro rfl
    exact hhalf.not_ge (hβ₀ ▸ hb)

/-- `β_n ∈ (0, b)` when `Φ_b(Λ_n) ≥ 1`. -/
theorem boundaryThreshold_mem_Ioo (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {n : ℕ} {b : ℝ≥0}
    (hb : 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0) :
    boundaryThreshold J n ∈ Ioo 0 b :=
  (boundaryThreshold_spec J hL hα hαd hc hJt hlow hup hb).1

/-- `Φ_{β_n}(Λ_n) = 1/2` when `Φ_b(Λ_n) ≥ 1`. -/
theorem boundaryFlux_boundaryThreshold (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {n : ℕ} {b : ℝ≥0}
    (hb : 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0) :
    boundaryFlux (intensityProfile J (boundaryThreshold J n))
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 = 2⁻¹ :=
  (boundaryThreshold_spec J hL hα hαd hc hJt hlow hup hb).2.1

/-- `β_n` is the only solution of `Φ_β(Λ_n) = 1/2` when `Φ_b(Λ_n) ≥ 1`. -/
theorem eq_boundaryThreshold_of_boundaryFlux_eq (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {n : ℕ} {b : ℝ≥0}
    (hb : 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0)
    {β : ℝ≥0} (hβ : boundaryFlux (intensityProfile J β)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0 = 2⁻¹) :
    β = boundaryThreshold J n :=
  (boundaryThreshold_spec J hL hα hαd hc hJt hlow hup hb).2.2 β hβ

end Threshold

/-! ### Finite-ball control -/

section Control

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)

/-- **Boundary contraction below the threshold.** If `Φ_b(Λ_n) ≥ 1` and `β ≤ β_n`, then
`χ(β) ≤ 2 χ_n(β)`. -/
theorem chi_le_two_mul_of_le_boundaryThreshold (hL : 2 ≤ L) {α c C : ℝ} (hα : 0 < α)
    (hαd : α < d) (hc : 0 < c) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hlow : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        (J s(u, v) : ℝ))
    (hup : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {n : ℕ} {b : ℝ≥0}
    (hb : 1 ≤ boundaryFlux (intensityProfile J b)
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0)
    {β : ℝ≥0} (hβ : β ≤ boundaryThreshold J n) :
    chi (intensityProfile J β) 0 ≤ 2 * ∑' z, law (intensityProfile J β)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) := by
  classical
  set S := (finite_level_ball (A := Fin d → ZMod L) n).toFinset with hS
  set σ : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) ≃ (ℕ →₀ (Fin d → ZMod L)) :=
    fun x => Equiv.addRight x with hσ
  have hσ0 : ∀ x, σ x 0 = x := fun x => zero_add x
  have hσJ : ∀ x e, J (Sym2.map (σ x) e) = J e := fun x =>
    map_addRight_eq_of_translationInvariant J hJt x
  set Sx : (ℕ →₀ (Fin d → ZMod L)) → Finset (ℕ →₀ (Fin d → ZMod L)) :=
    fun x => S.map (σ x).toEmbedding with hSx
  have hmemSx : ∀ x, x ∈ Sx x := fun x => by
    simp only [hSx, Finset.mem_map_equiv]
    rw [mem_toFinset_level_ball_finset]
    simp [hσ]
  have hB : ∀ x, ∑ u ∈ Sx x, law (intensityProfile J β) (localConn (Sx x : Set _) x u) ≤
      ∑' z, law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) := by
    intro x
    rw [tsum_law_localConn_ball_eq_sum, hSx, Finset.sum_map]
    refine le_of_eq (Finset.sum_congr rfl fun u _ => ?_)
    have h := law_localConn_eq_of_image J (σ x) (hσJ x) β
      (S := (S : Set (ℕ →₀ (Fin d → ZMod L)))) (T := ((S.map (σ x).toEmbedding : Finset _) : Set _))
      (fun v => by simp) 0 u
    rw [hσ0 x, coe_toFinset_level_ball] at h
    exact h
  have hΦ : ∀ x, boundaryFlux (intensityProfile J β) (Sx x) x ≤ 2⁻¹ := by
    intro x
    have h := boundaryFlux_map_le J (σ x) (hσJ x) β S 0
    rw [hσ0 x] at h
    refine h.trans ((monotone_boundaryFlux_intensity J S 0 hβ).trans_eq ?_)
    exact (boundaryThreshold_spec J hL hα hαd hc hJt hlow hup hb).2.1
  have h := chi_le_of_boundary_contraction (intensityProfile J β) Sx hmemSx
    (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) hB hΦ 0
  rwa [ENNReal.one_sub_inv_two, inv_inv, mul_comm] at h

/-- **Ball susceptibility bounds between consecutive scales.** If moreover
`τ_b(0, x) ≤ A L^{-(d-α) h x}` for every `x` and `Φ_b(Λ_n) ≥ 1` for every `n`, there are
`c₀, C₀ > 0`, independent of `n` and `β`, with `c₀ L^{αn} ≤ χ_n(β) ≤ χ_n(b) ≤ C₀ L^{αn}` for
`b_n ≤ β ≤ b`, and `χ(β) ≤ 2 C₀ L^α L^{αn}` for `β ≤ b_{n+1}`. -/
theorem exists_ballSusceptibility_bounds_of_maxBoundaryThreshold_le (hL : 2 ≤ L)
    {α c C : ℝ} (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
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
          ENNReal.ofReal (2 * C₀ * (L : ℝ) ^ α * (L : ℝ) ^ (α * n))) := by
  classical
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hρ1 : 1 < (L : ℝ) ^ α := Real.one_lt_rpow hL1 hα
  -- `A ≥ 1` from the bound at the origin.
  have hA : 0 ≤ A := by
    have h0 := hτ 0
    rw [show tau (intensityProfile J b) 0 0 = 1 by
      rw [tau, conn_self, measure_univ]] at h0
    simp only [Finsupp.support_zero, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero, mul_zero,
      Real.rpow_zero, mul_one] at h0
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (not_le.1 hneg).le] at h0
    exact one_ne_zero (le_antisymm h0 bot_le)
  -- `b > 0`, since the flux vanishes at `0`.
  have hb0 : 0 < b := by
    obtain ⟨⟨h0, -⟩, -⟩ := boundaryThreshold_spec J hL hα hαd hc hJt hlow hup (hb 0)
    exact h0.trans (boundaryThreshold_spec J hL hα hαd hc hJt hlow hup (hb 0)).1.2
  set C₀ : ℝ := 1 + A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1) with hC₀
  have hC₀0 : 0 < C₀ := by
    have : 0 ≤ A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1) :=
      div_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos hL0 α).le) (by linarith)
    linarith
  set K : ℝ := max (C * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1)) 0 + 1 with hK
  have hK0 : 0 < K := by positivity
  set c₀ : ℝ := 1 / (2 * b * K) with hc₀
  have hc₀0 : 0 < c₀ := by
    have : (0 : ℝ) < b := by exact_mod_cast hb0
    positivity
  -- The upper bound on `χ_n(b)`.
  have hupper : ∀ n : ℕ, ∑' z, law (intensityProfile J b)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) ≤
        ENNReal.ofReal (C₀ * (L : ℝ) ^ (α * n)) := by
    intro n
    refine (tsum_law_localConn_le_tsum_tau _ _ 0).trans ?_
    set f : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ :=
      fun x y => tau (intensityProfile J b) 0 (y - x) with hf
    have hdiag : ∀ x, f x x ≤ 1 := fun x => prob_le_one
    have hupf : ∀ x y, x ≠ y → f x y ≤ ENNReal.ofReal
        (A * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) := by
      intro x y _
      refine (hτ (y - x)).trans_eq ?_
      congr 3
      ring
    refine le_of_eq_of_le (tsum_congr fun y => ?_) (tsum_levelBall_le hL hα hA f hdiag hupf 0 n)
    simp only [hf, sub_zero, Set.mem_ofPred_eq]
  -- The upper bound on `r_n(b)`.
  have hrate : ∀ n : ℕ, ballExitRate J n b ≤ ENNReal.ofReal (b * K * (L : ℝ) ^ (-(α * n))) := by
    intro n
    refine (ballExitRate_le_of_powerLaw J hL hα hup n b).trans ?_
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul b.coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc (b : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ b.coe_nonneg
    have hpow : 0 < (L : ℝ) ^ (-(α * n)) := Real.rpow_pos_of_pos hL0 _
    rw [mul_div_right_comm]
    refine mul_le_mul_of_nonneg_right ?_ hpow.le
    rw [hK]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨c₀, C₀, hc₀0, hC₀0, fun n β hnβ hβb => ⟨?_, monotone_tsum_law_localConn_ball J n hβb,
    hupper n⟩, fun n β hβ => ?_⟩
  · -- Lower bound: `1/2 ≤ Φ_β(Λ_n) ≤ r_n(b) χ_n(β)`.
    obtain ⟨-, hhalf, -⟩ := boundaryThreshold_spec J hL hα hαd hc hJt hlow hup (hb n)
    have h1 : (2⁻¹ : ℝ≥0∞) ≤ ENNReal.ofReal (b * K * (L : ℝ) ^ (-(α * n))) *
        ∑' z, law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) := by
      rw [← hhalf]
      refine (monotone_boundaryFlux_intensity J _ 0
        ((boundaryThreshold_le_maxBoundaryThreshold J le_rfl).trans hnβ)).trans ?_
      dsimp only
      rw [boundaryFlux_ball_eq_ballExitRate_mul J hJt]
      exact mul_le_mul_left (((strictMono_ballExitRate J hL hα hαd hc hlow hup n).monotone
        hβb).trans (hrate n)) _
    refine le_trans (le_of_eq ?_) (ENNReal.div_le_of_le_mul' h1)
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb0
    have hpos : 0 < (b : ℝ) * K * (L : ℝ) ^ (-(α * n)) := by positivity
    rw [show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_div_of_pos hpos]
    congr 1
    rw [Real.rpow_neg hL0.le, hc₀]
    have : (0 : ℝ) < (L : ℝ) ^ (α * n) := Real.rpow_pos_of_pos hL0 _
    field_simp
  · -- `χ(β) ≤ 2 χ_k(b) ≤ 2 C₀ L^{α(n+1)}` with `b_{n+1} = β_k`.
    obtain ⟨k, hk, hke⟩ := exists_maxBoundaryThreshold_eq J (n + 1)
    rw [hke] at hβ
    have hkb := (boundaryThreshold_spec J hL hα hαd hc hJt hlow hup (hb k)).1.2
    refine (chi_le_two_mul_of_le_boundaryThreshold J hL hα hαd hc hJt hlow hup (hb k) hβ).trans ?_
    calc 2 * ∑' z, law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ k} 0 z)
        ≤ 2 * ENNReal.ofReal (C₀ * (L : ℝ) ^ (α * k)) :=
          mul_le_mul_right ((monotone_tsum_law_localConn_ball J k (hβ.trans hkb.le)).trans
            (hupper k)) _
      _ ≤ 2 * ENNReal.ofReal (C₀ * (L : ℝ) ^ (α * (n + 1 : ℕ))) := by
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left ?_ hC₀0.le)) _
          exact Real.rpow_le_rpow_of_exponent_le hL1.le
            (mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hα.le)
      _ = ENNReal.ofReal (2 * C₀ * (L : ℝ) ^ α * (L : ℝ) ^ (α * n)) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          rw [show α * ((n + 1 : ℕ) : ℝ) = α + α * n by push_cast; ring,
            Real.rpow_add hL0]
          ring

end Control

end PercLib.Models
