/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.ReciprocalDifference

/-!
# Normalization algebra for the Fourier bootstrap

## Main results

The zero-frequency equation gives an exact mass normalization and a rational
upper bound retaining the coefficient error. The normalized denominator defect
is an identity, and positivity of the reciprocal follows from the Fourier
equation and the positive numerator. These scalar lemmas do not assume that
the canonical coefficients satisfy any unproved analytic estimate.
-/

@[expose] public section

namespace PercLib.Percolation.Bond.Lace

/-- Normalization extracted from the zero-frequency equation. -/
theorem mass_normalization_of_lace_equation {chi m j : ℝ}
    (hchi : chi ≠ 0) (hm : 1 + m ≠ 0)
    (heq : chi = 1 + m + (1 + m) * j * chi) :
    1 - chi⁻¹ = j + m / (1 + m) := by
  field_simp
  nlinarith [heq]

/-- The mass bound retains the exact rational dependence on the error. -/
theorem mass_le_of_normalization {j lam m eps : ℝ}
    (heps : eps < 1) (hm : |m| ≤ eps)
    (heq : lam = j + m / (1 + m)) :
    j ≤ lam + eps / (1 - eps) := by
  have hlow : -eps ≤ m := (abs_le.mp hm).1
  have hden : 0 < 1 + m := by linarith
  have he : 0 < 1 - eps := by linarith
  have hfrac : -m / (1 + m) ≤ eps / (1 - eps) := by
    apply (div_le_div_iff₀ hden he).2
    nlinarith
  rw [neg_div] at hfrac
  linarith

/-- The rational mass correction is attained at the negative error endpoint. -/
theorem mass_correction_sharp (eps : ℝ) :
    -(-eps) / (1 + -eps) = eps / (1 - eps) := by ring

/-- Numerator normalization with its exact error dependence. -/
theorem normalized_numerator_le {m P eps : ℝ}
    (heps : eps < 1) (hm : |m| ≤ eps) (hP : P ≤ eps) :
    (1 + P) / (1 + m) ≤ 1 + 2 * eps / (1 - eps) := by
  have hlow := (abs_le.mp hm).1
  have heps0 : 0 ≤ eps := (abs_nonneg m).trans hm
  have hden : 0 < 1 + m := by linarith
  have he : 0 < 1 - eps := by linarith
  have hr : 1 + 2 * eps / (1 - eps) = (1 + eps) / (1 - eps) := by
    field_simp
    ring
  rw [hr]
  apply (div_le_div_iff₀ hden he).2
  nlinarith [mul_nonneg (show 0 ≤ eps - P by linarith) he.le,
    mul_nonneg (show 0 ≤ m + eps by linarith) (show 0 ≤ 1 + eps by linarith)]

/-- The exact normalized denominator defect used in Fourier improvement. -/
theorem normalized_denominator_defect {j lam m P D : ℝ}
    (hm : 1 + m ≠ 0) (heq : lam = j + m / (1 + m)) :
    (1 - lam * D) - (1 - j * D * (1 + P)) / (1 + m) =
      ((1 - D) * m + j * D * (P - m)) / (1 + m) := by
  rw [heq]
  field_simp
  ring

/-- Separate mass and frequency errors are retained in the denominator bound.
This avoids replacing both by the larger weighted error. -/
theorem abs_normalized_defect_le {j m P D eta zeta : ℝ}
    (heta : eta < 1) (hzeta : 0 ≤ zeta) (hm : |m| ≤ eta)
    (hD : |D| ≤ 1) (hj : 0 ≤ j) (hP : |P - m| ≤ zeta * (1 - D)) :
    |((1 - D) * m + j * D * (P - m)) / (1 + m)| ≤
      (eta + j * zeta) / (1 - eta) * (1 - D) := by
  have heta0 : 0 ≤ eta := (abs_nonneg m).trans hm
  have hg : 0 ≤ 1 - D := sub_nonneg.mpr ((le_abs_self D).trans hD)
  have hden : 0 < 1 + m := by have := (abs_le.mp hm).1; linarith
  have he : 0 < 1 - eta := by linarith
  have hdenle : 1 - eta ≤ 1 + m := by have := (abs_le.mp hm).1; linarith
  have hnum : |(1 - D) * m + j * D * (P - m)| ≤
      (eta + j * zeta) * (1 - D) := by
    calc
      _ ≤ |(1 - D) * m| + |j * D * (P - m)| := abs_add_le _ _
      _ = (1 - D) * |m| + j * |D| * |P - m| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg hj]
      _ ≤ (1 - D) * eta + j * (zeta * (1 - D)) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hm hg)
        exact (mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hj hD) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hP hj)
      _ = _ := by ring
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ ((eta + j * zeta) * (1 - D)) / (1 - eta) :=
      div_le_div₀ (by positivity) hnum he hdenle
    _ = _ := by ring

/-- An exact ratio identity derived from the two scalar lace equations. -/
theorem normalized_fourier_ratio_identity {T P m j lam D : ℝ}
    (hm : 1 + m ≠ 0) (hnorm : lam = j + m / (1 + m))
    (heq : T = 1 + P + (1 + P) * j * D * T) :
    T * (1 - lam * D) = (1 + P) / (1 + m) +
      T * (((1 - D) * m + j * D * (P - m)) / (1 + m)) := by
  rw [hnorm]
  field_simp
  nlinarith [heq]

/-- The first Fourier bootstrap improvement retains separate mass and frequency
errors and the parameter-dependent walk comparison. The scalar hypotheses are
kept explicit to expose every sign and normalization used when this lemma is
applied to actual transforms; no bundle conceals an analytic estimate. -/
theorem fourier_ratio_le_of_two_errors {T P m j lam D eta zeta K : ℝ}
    (heta : eta < 1) (hzeta : 0 ≤ zeta) (hm : |m| ≤ eta) (hP : |P| ≤ eta)
    (hvariation : |P - m| ≤ zeta * (1 - D)) (hD : |D| ≤ 1)
    (hj : 0 ≤ j) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hT : 0 ≤ T)
    (hweak : T * (1 - lam * D) ≤ K)
    (hnorm : lam = j + m / (1 + m))
    (heq : T = 1 + P + (1 + P) * j * D * T) :
    T * (1 - lam * D) ≤
      1 + (2 * eta + 2 * K * (eta + j * zeta) / (1 + lam)) / (1 - eta) := by
  have heta0 : 0 ≤ eta := (abs_nonneg m).trans hm
  have hden : 0 < 1 + m := by have := (abs_le.mp hm).1; linarith
  have he : 0 < 1 - eta := by linarith
  have hl : 0 < 1 + lam := by linarith
  have hwalk := PercLib.Analysis.walk_denominator_comparison hlam1 (abs_le.mp hD).1
  have hTg : T * (1 - D) ≤ 2 * K / (1 + lam) := by
    apply (le_div_iff₀ hl).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwalk hT]
  have hdef := abs_normalized_defect_le heta hzeta hm hD hj hvariation
  have hnum := normalized_numerator_le heta hm ((le_abs_self P).trans hP)
  have hA : 0 ≤ (eta + j * zeta) / (1 - eta) := by positivity
  have herror : T * (((1 - D) * m + j * D * (P - m)) / (1 + m)) ≤
      (eta + j * zeta) / (1 - eta) * (2 * K / (1 + lam)) := by
    calc
      _ ≤ T * |((1 - D) * m + j * D * (P - m)) / (1 + m)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hT
      _ ≤ T * ((eta + j * zeta) / (1 - eta) * (1 - D)) :=
        mul_le_mul_of_nonneg_left hdef hT
      _ = (eta + j * zeta) / (1 - eta) * (T * (1 - D)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hTg hA
  rw [normalized_fourier_ratio_identity hden.ne' hnorm heq]
  calc
    _ ≤ (1 + 2 * eta / (1 - eta)) +
        (eta + j * zeta) / (1 - eta) * (2 * K / (1 + lam)) := add_le_add hnum herror
    _ = _ := by ring

/-- Positivity of the Fourier reciprocal is a consequence of the equation;
evenness of a signed kernel would not be sufficient. -/
theorem fourier_denominator_pos {T P j D : ℝ}
    (hT : 0 ≤ T) (hP : 0 < 1 + P)
    (heq : T = 1 + P + (1 + P) * j * D * T) :
    0 < T ∧ 0 < 1 - j * D * (1 + P) := by
  have hmul : T * (1 - j * D * (1 + P)) = 1 + P := by
    nlinarith [heq]
  have hTpos : 0 < T := by
    by_contra h
    have : T = 0 := le_antisymm (le_of_not_gt h) hT
    simp [this] at hmul
    linarith
  refine ⟨hTpos, ?_⟩
  apply (mul_pos_iff_of_pos_left hTpos).mp
  rw [hmul]
  exact hP

end PercLib.Percolation.Bond.Lace
