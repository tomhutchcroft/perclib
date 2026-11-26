/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Homogeneous and exponential bond profiles side by side. New for this project; no upstream code
is copied. Mathematical reference: G. Grimmett, *Percolation* (2nd ed., 1999), §1.1.
-/
module

public import PercLib.Percolation.Bond.Homogeneous.Defs
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.Degree
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Homogeneous and exponential families of bond profiles

## Main results

* `law_adj_homogeneousProfile_top`: on the complete graph each pair of distinct vertices is
  adjacent in the open graph with probability `p` (the Erdős–Rényi graph).
* `hasDerivAt_one_sub_exp_neg_mul`: the parameter derivative `J e^{-βJ}` of the exponential
  family.
* `not_exists_intensityProfile_eq_mul`: a family `p ↦ p D(e)` need not be an exponential family
  `1 - exp(-φ(p) J(e))` for any fixed `J` and any reparametrisation `φ`, even for `0 < p < 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Erdős–Rényi edges.** Under the homogeneous profile on the complete graph, two distinct
vertices are adjacent in the open graph with probability `p`. -/
theorem law_adj_homogeneousProfile_top (p : unitInterval) {x y : V} (h : x ≠ y) :
    law (homogeneousProfile ⊤ p) {ω : Config V | (openGraph ω).Adj x y} =
      (unitInterval.toNNReal p : ℝ≥0∞) := by
  simp [law_adj, Ne.symm h, homogeneousProfile_top_mk p h]

/-- The parameter derivative of `β ↦ 1 - exp(-β c)` is `c exp(-β c)`. -/
theorem hasDerivAt_one_sub_exp_neg_mul (c β : ℝ) :
    HasDerivAt (fun b : ℝ => 1 - Real.exp (-b * c)) (c * Real.exp (-β * c)) β := by
  have h : HasDerivAt (fun b : ℝ => -b * c) (-c) β := by
    simpa using ((hasDerivAt_id β).neg).mul_const c
  simpa [mul_comm] using (h.exp).const_sub 1

/-- **A linear family is not a reparametrised exponential family.** On `Fin 3`, the family
`p ↦ p D(e)` with `D(s(0,1)) = 1` and `D = 1/2` elsewhere is not of the form
`p ↦ 1 - exp(-φ(p) J(e))` for any fixed intensity `J` and any reparametrisation `φ`, already on
`0 < p < 1`. -/
theorem not_exists_intensityProfile_eq_mul :
    ∃ D : Sym2 (Fin 3) → unitInterval, ¬ ∃ (J : Sym2 (Fin 3) → ℝ≥0) (φ : unitInterval → ℝ≥0),
      ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ e,
        (intensityProfile J (φ p) e : ℝ) = p * D e := by
  classical
  let h2 : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let p1 : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let p2 : unitInterval := ⟨3 / 4, by constructor <;> norm_num⟩
  set D : Sym2 (Fin 3) → unitInterval := fun e => if e = s(0, 1) then 1 else h2 with hD
  refine ⟨D, ?_⟩
  rintro ⟨J, φ, h⟩
  have hne : (s(0, 2) : Sym2 (Fin 3)) ≠ s(0, 1) := by decide
  have hD1 : D s(0, 1) = 1 := by simp [hD]
  have hD2 : D s(0, 2) = h2 := by simp [hD, hne]
  have e11 := h p1 (by norm_num [p1]) (by norm_num [p1]) s(0, 1)
  have e21 := h p2 (by norm_num [p2]) (by norm_num [p2]) s(0, 1)
  have e12 := h p1 (by norm_num [p1]) (by norm_num [p1]) s(0, 2)
  have e22 := h p2 (by norm_num [p2]) (by norm_num [p2]) s(0, 2)
  rw [hD1] at e11 e21
  rw [hD2] at e12 e22
  change 1 - Real.exp (-((φ p1 : ℝ)) * (J s(0, 1) : ℝ)) = 1 / 2 * 1 at e11
  change 1 - Real.exp (-((φ p2 : ℝ)) * (J s(0, 1) : ℝ)) = 3 / 4 * 1 at e21
  change 1 - Real.exp (-((φ p1 : ℝ)) * (J s(0, 2) : ℝ)) = 1 / 2 * (1 / 2) at e12
  change 1 - Real.exp (-((φ p2 : ℝ)) * (J s(0, 2) : ℝ)) = 3 / 4 * (1 / 2) at e22
  set a : ℝ := ((φ p1 : ℝ≥0) : ℝ)
  set b : ℝ := ((φ p2 : ℝ≥0) : ℝ)
  set j : ℝ := ((J s(0, 1) : ℝ≥0) : ℝ)
  set k : ℝ := ((J s(0, 2) : ℝ≥0) : ℝ)
  have ha : Real.exp (-a * j) = 1 / 2 := by linarith
  have hb : Real.exp (-b * j) = 1 / 4 := by linarith
  have hak : Real.exp (-a * k) = 3 / 4 := by linarith
  have hbk : Real.exp (-b * k) = 5 / 8 := by linarith
  have hj : j ≠ 0 := by
    rintro hj
    rw [hj, mul_zero, Real.exp_zero] at ha
    norm_num at ha
  have hbj : -b * j = 2 * (-a * j) := by
    apply Real.exp_injective
    rw [hb, show (2 : ℝ) * (-a * j) = -a * j + -a * j by ring, Real.exp_add, ha]
    norm_num
  have hba : b = 2 * a := by
    have : (b - 2 * a) * j = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hj
  have : Real.exp (-b * k) = Real.exp (-a * k) ^ 2 := by
    rw [← Real.exp_nat_mul, hba]
    congr 1
    push_cast
    ring
  rw [hbk, hak] at this
  norm_num at this

end PercLib.Percolation.Bond
