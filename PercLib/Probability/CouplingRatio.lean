/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21: elementary measure theory on an arbitrary probability space.
Mathematical reference: the ratio step in W. Conijn, arXiv:1502.04387v3, Proposition 10,
(3.12)–(3.17). No upstream code is copied, no definition is added and no Input is introduced.
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Coupling ratios

Two sets `X`, `Y` that agree almost everywhere on a set `S` (a successful coupling) differ in
measure by at most the larger of their masses on `Sᶜ`. If moreover both failure masses are at
most `C a μ(Sᶜ)`, the success mass of `X` is at least `c a μ(S)` and `μ(Sᶜ) ≤ ε < 1`, then the
ratio `μ(X) / μ(Y)` is within `C ε / (c (1 - ε))` of `1`, uniformly in the scale `a`.

Only `S` needs to be (null-)measurable; `X` and `Y` are arbitrary sets.

## Main results

* `abs_measureReal_sub_le_of_inter_ae_eq`: `|μ(X) - μ(Y)| ≤ max (μ(X ∩ Sᶜ)) (μ(Y ∩ Sᶜ))`.
* `mul_one_sub_le_measureReal_of_inter_ae_eq`: `c a (1 - ε) ≤ μ(Y)`.
* `measureReal_pos_of_inter_ae_eq`: `0 < μ(Y)`.
* `abs_measureReal_div_sub_one_le_of_inter_ae_eq`: `|μ(X) / μ(Y) - 1| ≤ C ε / (c (1 - ε))`.
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y S : Set Ω}

/-- Sets that agree almost everywhere on `S` differ in measure by at most the larger of their
masses on `Sᶜ`. -/
theorem abs_measureReal_sub_le_of_inter_ae_eq [IsFiniteMeasure μ] (hS : NullMeasurableSet S μ)
    (hXY : (X ∩ S : Set Ω) =ᵐ[μ] (Y ∩ S : Set Ω)) :
    |μ.real X - μ.real Y| ≤ max (μ.real (X ∩ Sᶜ)) (μ.real (Y ∩ Sᶜ)) := by
  rw [← measureReal_inter_add_sdiff₀ (s := X) hS, ← measureReal_inter_add_sdiff₀ (s := Y) hS,
    measureReal_congr hXY, add_sub_add_left_eq_sub, sdiff_eq, sdiff_eq]
  have hX0 : 0 ≤ μ.real (X ∩ Sᶜ) := measureReal_nonneg
  have hY0 : 0 ≤ μ.real (Y ∩ Sᶜ) := measureReal_nonneg
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_max_left (μ.real (X ∩ Sᶜ)) (μ.real (Y ∩ Sᶜ)),
    le_max_right (μ.real (X ∩ Sᶜ)) (μ.real (Y ∩ Sᶜ))]

/-- If `X` and `Y` agree almost everywhere on `S`, `μ(Sᶜ) ≤ ε` and the success mass of `X` is
at least `c a μ(S)` with `c a ≥ 0`, then `μ(Y) ≥ c a (1 - ε)`. -/
theorem mul_one_sub_le_measureReal_of_inter_ae_eq [IsProbabilityMeasure μ]
    (hS : NullMeasurableSet S μ) (hXY : (X ∩ S : Set Ω) =ᵐ[μ] (Y ∩ S : Set Ω)) {ε a c : ℝ}
    (hε : μ.real Sᶜ ≤ ε) (hca : 0 ≤ c * a) (hlow : c * a * μ.real S ≤ μ.real (X ∩ S)) :
    c * a * (1 - ε) ≤ μ.real Y := by
  have hSc : μ.real Sᶜ = 1 - μ.real S := probReal_compl_eq_one_sub₀ hS
  have hYS : μ.real (Y ∩ S) ≤ μ.real Y := measureReal_mono inter_subset_left
  have hS1 : 1 - ε ≤ μ.real S := by linarith
  calc c * a * (1 - ε) ≤ c * a * μ.real S := mul_le_mul_of_nonneg_left hS1 hca
    _ ≤ μ.real (X ∩ S) := hlow
    _ = μ.real (Y ∩ S) := measureReal_congr hXY
    _ ≤ μ.real Y := hYS

/-- Under a successful coupling on `S` with `μ(Sᶜ) ≤ ε < 1` and a success mass of `X` at least
`c a μ(S)` with `a, c > 0`, the set `Y` has positive measure. -/
theorem measureReal_pos_of_inter_ae_eq [IsProbabilityMeasure μ]
    (hS : NullMeasurableSet S μ) (hXY : (X ∩ S : Set Ω) =ᵐ[μ] (Y ∩ S : Set Ω)) {ε a c : ℝ}
    (hε : μ.real Sᶜ ≤ ε) (hε1 : ε < 1) (ha : 0 < a) (hc : 0 < c)
    (hlow : c * a * μ.real S ≤ μ.real (X ∩ S)) :
    0 < μ.real Y :=
  lt_of_lt_of_le (mul_pos (mul_pos hc ha) (sub_pos.2 hε1))
    (mul_one_sub_le_measureReal_of_inter_ae_eq hS hXY hε (mul_pos hc ha).le hlow)

/-- **Coupling ratio bound.** If `X` and `Y` agree almost everywhere on `S`, `μ(Sᶜ) ≤ ε < 1`,
the success mass of `X` is at least `c a μ(S)` and both failure masses are at most
`C a μ(Sᶜ)`, then `|μ(X) / μ(Y) - 1| ≤ C ε / (c (1 - ε))`. -/
theorem abs_measureReal_div_sub_one_le_of_inter_ae_eq [IsProbabilityMeasure μ]
    (hS : NullMeasurableSet S μ) (hXY : (X ∩ S : Set Ω) =ᵐ[μ] (Y ∩ S : Set Ω)) {ε a c C : ℝ}
    (hε : μ.real Sᶜ ≤ ε) (hε1 : ε < 1) (ha : 0 < a) (hc : 0 < c) (hC : 0 ≤ C)
    (hlow : c * a * μ.real S ≤ μ.real (X ∩ S))
    (hXc : μ.real (X ∩ Sᶜ) ≤ C * a * μ.real Sᶜ) (hYc : μ.real (Y ∩ Sᶜ) ≤ C * a * μ.real Sᶜ) :
    |μ.real X / μ.real Y - 1| ≤ C * ε / (c * (1 - ε)) := by
  have hden : 0 < c * a * (1 - ε) := mul_pos (mul_pos hc ha) (sub_pos.2 hε1)
  have hY : c * a * (1 - ε) ≤ μ.real Y :=
    mul_one_sub_le_measureReal_of_inter_ae_eq hS hXY hε (mul_pos hc ha).le hlow
  have hYpos : 0 < μ.real Y := hden.trans_le hY
  have hnum : |μ.real X - μ.real Y| ≤ C * a * ε :=
    (abs_measureReal_sub_le_of_inter_ae_eq hS hXY).trans
      ((max_le hXc hYc).trans (mul_le_mul_of_nonneg_left hε (mul_nonneg hC ha.le)))
  have hrw : C * ε / (c * (1 - ε)) = C * a * ε / (c * a * (1 - ε)) := by
    field_simp
  rw [div_sub_one hYpos.ne', abs_div, abs_of_pos hYpos, hrw]
  exact div_le_div₀ ((abs_nonneg _).trans hnum) hnum hden hY

/-- The hypotheses of `abs_measureReal_div_sub_one_le_of_inter_ae_eq` are satisfiable on every
probability space: `X = Y = S = univ`, `ε = 0` and `a = c = C = 1`. -/
example (μ : Measure Ω) [IsProbabilityMeasure μ] :
    |μ.real (univ : Set Ω) / μ.real univ - 1| ≤ 1 * 0 / (1 * (1 - 0)) :=
  abs_measureReal_div_sub_one_le_of_inter_ae_eq (X := univ) (Y := univ)
    MeasurableSet.univ.nullMeasurableSet (by rfl) (by simp) zero_lt_one one_pos one_pos
    zero_le_one (by simp) (by simp) (by simp)

end PercLib.Probability
