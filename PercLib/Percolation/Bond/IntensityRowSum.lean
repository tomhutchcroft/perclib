/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of the actual open-edge row mass

The off-diagonal intensity row controls the Lipschitz constant of the actual
open-edge row mass. Only the row at the specified vertex needs to be finite;
neither transitivity nor a finite susceptibility is required.

## Main results

* `rowSum_intensityProfile_le`: the rooted mass bound, including infinite values.
* `abs_intensityProfile_sub_le`: the exact edgewise Lipschitz constant.
* `abs_toReal_rowSum_intensityProfile_sub_le`: the corresponding row estimate.
* `lipschitzWith_toReal_rowSum_intensityProfile`: global intensity continuity.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A rooted intensity row bounds the corresponding open-edge row, with no finiteness
or assumptions on the other rows. -/
theorem rowSum_intensityProfile_le (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (o : V) :
    rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o ≤
      (β : ℝ≥0∞) * rowSum (fun e => (J e : ℝ≥0∞)) o := by
  calc
    _ ≤ rowSum (fun e => (β : ℝ≥0∞) * (J e : ℝ≥0∞)) o := by
      apply rowSum_mono
      intro e
      change (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) ≤
        (β : ℝ≥0∞) * (J e : ℝ≥0∞)
      rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
      exact intensityProfile_toNNReal_le J β e
    _ = _ := rowSum_const_mul _ _ _

/-- The open probability at an edge is Lipschitz in intensity with constant equal
to that edge's intensity weight. -/
theorem abs_intensityProfile_sub_le (J : Sym2 V → ℝ≥0) (β γ : ℝ≥0) (e : Sym2 V) :
    |(intensityProfile J β e : ℝ) - (intensityProfile J γ e : ℝ)| ≤
      |(β : ℝ) - γ| * (J e : ℝ) := by
  have hordered (a b : ℝ≥0) (hab : a ≤ b) :
      |(intensityProfile J b e : ℝ) - (intensityProfile J a e : ℝ)| ≤
        |(b : ℝ) - a| * (J e : ℝ) := by
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hprob : (intensityProfile J a e : ℝ) ≤ intensityProfile J b e :=
      intensityProfile_mono J hab e
    rw [abs_of_nonneg (sub_nonneg.mpr hprob), abs_of_nonneg (sub_nonneg.mpr habR)]
    have hE : Real.exp (-(a : ℝ) * (J e : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr a.coe_nonneg) (J e).coe_nonneg)
    have hsmall : 1 - Real.exp (-((b : ℝ) - a) * (J e : ℝ)) ≤
        ((b : ℝ) - a) * (J e : ℝ) := by
      have h := Real.add_one_le_exp (-((b : ℝ) - a) * (J e : ℝ))
      linarith
    have hexp : Real.exp (-(b : ℝ) * (J e : ℝ)) =
        Real.exp (-(a : ℝ) * (J e : ℝ)) *
          Real.exp (-((b : ℝ) - a) * (J e : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = Real.exp (-(a : ℝ) * (J e : ℝ)) *
          (1 - Real.exp (-((b : ℝ) - a) * (J e : ℝ))) := by
        change (1 - Real.exp (-(b : ℝ) * (J e : ℝ))) -
          (1 - Real.exp (-(a : ℝ) * (J e : ℝ))) = _
        rw [hexp]
        ring
      _ ≤ Real.exp (-(a : ℝ) * (J e : ℝ)) * (((b : ℝ) - a) * (J e : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
      _ ≤ ((b : ℝ) - a) * (J e : ℝ) :=
        mul_le_of_le_one_left (mul_nonneg (sub_nonneg.mpr habR) (J e).coe_nonneg) hE
  rcases le_total β γ with h | h
  · simpa only [abs_sub_comm] using hordered β γ h
  · exact hordered γ β h

/-- The actual open-edge row is finite whenever its intensity row is finite. -/
theorem rowSum_intensityProfile_ne_top (J : Sym2 V → ℝ≥0) (o : V)
    (hJ : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) (β : ℝ≥0) :
    rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hJ)
    (rowSum_intensityProfile_le J β o)

/-- The actual row mass has Lipschitz constant equal to the finite rooted intensity row. -/
theorem abs_toReal_rowSum_intensityProfile_sub_le (J : Sym2 V → ℝ≥0) (o : V)
    (hJ : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) (β γ : ℝ≥0) :
    |(rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o).toReal -
        (rowSum (fun e => unitInterval.toENNReal (intensityProfile J γ e)) o).toReal| ≤
      |(β : ℝ) - γ| * (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal := by
  have hJL : Summable fun x : {x : V // x ≠ o} => (J s(o, x.1) : ℝ) := by
    rw [rowSum_eq_tsum_ne] at hJ
    simpa only [ENNReal.coe_toReal] using ENNReal.summable_toReal hJ
  have hmass : (∑' x : {x : V // x ≠ o}, (J s(o, x.1) : ℝ)) =
      (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal := by
    rw [rowSum_eq_tsum_ne, ENNReal.tsum_toReal_eq (fun _ => ENNReal.coe_ne_top)]
    simp
  have hrow (a : ℝ≥0) : Summable fun x : {x : V // x ≠ o} =>
      (intensityProfile J a s(o, x.1) : ℝ) := by
    have h := rowSum_intensityProfile_ne_top J o hJ a
    rw [rowSum_eq_tsum_ne] at h
    simpa only [unitInterval.toENNReal_toReal] using ENNReal.summable_toReal h
  have hreal (a : ℝ≥0) :
      (rowSum (fun e => unitInterval.toENNReal (intensityProfile J a e)) o).toReal =
        ∑' x : {x : V // x ≠ o}, (intensityProfile J a s(o, x.1) : ℝ) := by
    rw [rowSum_eq_tsum_ne,
      ENNReal.tsum_toReal_eq (fun _ => unitInterval.toENNReal_ne_top _)]
    simp
  rw [hreal β, hreal γ, ← (hrow β).tsum_sub (hrow γ), ← hmass]
  have h := ((hrow β).sub (hrow γ)).hasSum.norm_le_of_bounded
    ((hJL.mul_left |(β : ℝ) - γ|).hasSum) (fun x => by
      simpa only [Real.norm_eq_abs] using abs_intensityProfile_sub_le J β γ s(o, x.1))
  simpa only [Real.norm_eq_abs, tsum_mul_left] using h

/-- The real actual row mass is globally Lipschitz on nonnegative intensities. -/
theorem lipschitzWith_toReal_rowSum_intensityProfile (J : Sym2 V → ℝ≥0) (o : V)
    (hJ : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) :
    LipschitzWith (rowSum (fun e => (J e : ℝ≥0∞)) o).toNNReal
      (fun β : ℝ≥0 =>
        (rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o).toReal) := by
  apply LipschitzWith.of_dist_le_mul
  intro β γ
  simpa only [Real.dist_eq, NNReal.dist_eq, ENNReal.toReal, mul_comm] using
    abs_toReal_rowSum_intensityProfile_sub_le J o hJ β γ

/-- A finite rooted intensity row gives continuity of the actual row mass. -/
theorem continuous_toReal_rowSum_intensityProfile (J : Sym2 V → ℝ≥0) (o : V)
    (hJ : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) :
    Continuous (fun β : ℝ≥0 =>
      (rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o).toReal) :=
  (lipschitzWith_toReal_rowSum_intensityProfile J o hJ).continuous

end PercLib.Percolation.Bond
