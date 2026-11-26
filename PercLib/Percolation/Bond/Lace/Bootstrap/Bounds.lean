/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.SpatialMoments.FourierBootstrapContinuity

/-!
# Pointwise bounds from the actual Fourier bootstrap suprema

Finite susceptibility bounds the Fourier-ratio family. A finite second spatial
moment bounds the normalized second-difference family, uniformly over its positive
deficit domain. These derived bounds justify evaluating the real suprema at each
frequency; no boundedness premise or Fourier-positivity premise is needed.

## Main results

* `abs_tauFourier_le_fourierRatioSup_mul_resolvent`: the actual ratio bound.
* `abs_fwdDiff_two_tauFourier_le_fourierDifferenceSup_mul_majorant`: the difference bound.
* `abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le`: the weak-bootstrap consequence.
* `abs_fwdDiff_two_tauFourier_le_mul_majorant_of_fourierDifferenceSup_le`: its difference analogue.
* `bddAbove_fourierDifference_of_finiteRange_of_transitive`: boundedness from the actual law.
-/

@[expose] public section

noncomputable section

open Set PercLib.Analysis
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The absolute actual Fourier transform is bounded by susceptibility. -/
theorem abs_tauFourier_le_chi (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hchi : chi q 0 ≠ ⊤) (k : Fin d → ℝ) :
    |tauFourier q k| ≤ (chi q 0).toReal :=
  abs_tau_cosine_tsum_le_chi q hchi k

/-- The Fourier-ratio family is uniformly bounded, retaining the actual walk parameter. -/
theorem abs_tauFourier_mul_den_le (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (k : Fin d → ℝ) :
    |tauFourier q k * (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k)| ≤
      (chi q 0).toReal * (1 + susceptibilityWalkParameter q) := by
  have hlam := susceptibilityWalkParameter_mem_Ico q hchi
  have hden := nearestNeighborResolvent_den_pos hd hlam k
  have hD := (abs_le.mp (nearestNeighborSymbol_abs_le_one hd k)).1
  have hupper : 1 - susceptibilityWalkParameter q * nearestNeighborSymbol k ≤
      1 + susceptibilityWalkParameter q := by
    nlinarith [mul_nonneg hlam.1 (show 0 ≤ nearestNeighborSymbol k + 1 by linarith)]
  rw [abs_mul, abs_of_pos hden]
  exact mul_le_mul (abs_tauFourier_le_chi q hchi k) hupper hden.le ENNReal.toReal_nonneg

/-- Finite susceptibility makes the actual ratio family bounded above. -/
theorem bddAbove_fourierRatio (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤) :
    BddAbove (range fun k : Fin d → ℝ =>
      |tauFourier q k * (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k)|) := by
  refine ⟨(chi q 0).toReal * (1 + susceptibilityWalkParameter q), ?_⟩
  rintro _ ⟨k, rfl⟩
  exact abs_tauFourier_mul_den_le hd q hchi k

/-- A quantitative upper bound for the canonical ratio supremum. -/
theorem fourierRatioSup_le_chi_mul_one_add (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤) :
    fourierRatioSup q ≤ (chi q 0).toReal * (1 + susceptibilityWalkParameter q) := by
  exact ciSup_le (abs_tauFourier_mul_den_le hd q hchi)

/-- Evaluating the actual ratio supremum gives the resolvent comparison. -/
theorem abs_tauFourier_le_fourierRatioSup_mul_resolvent (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (k : Fin d → ℝ) :
    |tauFourier q k| ≤ fourierRatioSup q *
      nearestNeighborResolvent (susceptibilityWalkParameter q) k := by
  have hlam := susceptibilityWalkParameter_mem_Ico q hchi
  have hden := nearestNeighborResolvent_den_pos hd hlam k
  have h := le_ciSup (bddAbove_fourierRatio hd q hchi) k
  rw [abs_mul, abs_of_pos hden] at h
  have hm := mul_le_mul_of_nonneg_right h
    (nearestNeighborResolvent_pos hd hlam k).le
  simpa only [fourierRatioSup, nearestNeighborResolvent, mul_assoc,
    mul_inv_cancel₀ hden.ne', mul_one] using hm

/-- A weak bound on the actual ratio supremum gives the pointwise bootstrap estimate. -/
theorem abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    {K : ℝ} (hK : fourierRatioSup q ≤ K) (k : Fin d → ℝ) :
    |tauFourier q k| ≤ K * nearestNeighborResolvent (susceptibilityWalkParameter q) k := by
  exact (abs_tauFourier_le_fourierRatioSup_mul_resolvent hd q hchi k).trans
    (mul_le_mul_of_nonneg_right hK (nearestNeighborResolvent_pos hd
      (susceptibilityWalkParameter_mem_Ico q hchi) k).le)

/-- The actual second spatial moment bounds every symmetric Fourier second difference. -/
theorem abs_fwdDiff_two_tauFourier_le_spatialMoment
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤)
    (k l : Fin d → ℝ) :
    |(fwdDiff k)^[2] (tauFourier q) (l - k)| ≤
      2 * (d : ℝ) * (spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2))).toReal *
        ∑ i, (1 - Real.cos (k i)) := by
  have hrow : Summable fun x => (tau q 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi)
  have hsum : (∑' x, |(tau q 0 x).toReal| * ‖x‖ ^ 2) =
      (spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2))).toReal := by
    rw [spatialMoment_eq_tsum, ENNReal.tsum_toReal_eq]
    · simp only [sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
        abs_of_nonneg ENNReal.toReal_nonneg, mul_comm]
    · intro x
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((tau_le_one q 0 x).trans_lt ENNReal.one_lt_top).ne
  have hw : Summable fun x => |(tau q 0 x).toReal| * ‖x‖ ^ 2 := by
    rw [spatialMoment_eq_tsum] at hsecond
    simpa only [sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      abs_of_nonneg ENNReal.toReal_nonneg, mul_comm] using ENNReal.summable_toReal hsecond
  have h := abs_tsum_lattice_cos_second_difference_le_norm_sq hrow hw l k
  rw [hsum] at h
  simpa only [fwdDiff_two_at_sub, tauFourier_def, Pi.sub_apply, Pi.add_apply] using h

/-- The normalized second-difference family has the explicit bound `d² S₂ / 75`. -/
theorem abs_fwdDiff_two_tauFourier_div_majorant_le (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤)
    {k l : Fin d → ℝ} (hk : 0 < 1 - nearestNeighborSymbol k) :
    |(fwdDiff k)^[2] (tauFourier q) (l - k)| /
        bootstrapMajorant (susceptibilityWalkParameter q) k l ≤
      (d : ℝ) ^ 2 * (spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2))).toReal / 75 := by
  have hlam := susceptibilityWalkParameter_mem_Ico q hchi
  apply (div_le_iff₀ (bootstrapMajorant_pos hd hlam hk)).2
  have h := abs_fwdDiff_two_tauFourier_le_spatialMoment q hchi hsecond k l
  rw [sum_one_sub_cos_eq_mul_deficit hd] at h
  refine h.trans ?_
  have hU : 150 * (1 - nearestNeighborSymbol k) ≤
      bootstrapMajorant (susceptibilityWalkParameter q) k l := by
    have hV := mul_le_mul_of_nonneg_left
      (three_quarters_le_bootstrapTripleProduct hd hlam k l)
      (show 0 ≤ 200 * (1 - nearestNeighborSymbol k) by positivity)
    simpa only [bootstrapMajorant] using (show
      150 * (1 - nearestNeighborSymbol k) ≤
        200 * (1 - nearestNeighborSymbol k) *
          bootstrapTripleProduct (susceptibilityWalkParameter q) k l by nlinarith)
  calc
    _ = ((d : ℝ) ^ 2 *
        (spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2))).toReal / 75) *
          (150 * (1 - nearestNeighborSymbol k)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hU (by positivity)

/-- A finite actual second spatial moment makes the canonical difference family bounded above. -/
theorem bddAbove_fourierDifference (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤) :
    BddAbove (range fun p :
      {p : (Fin d → ℝ) × (Fin d → ℝ) // 0 < 1 - nearestNeighborSymbol p.1} =>
        |(fwdDiff p.1.1)^[2] (tauFourier q) (p.1.2 - p.1.1)| /
          bootstrapMajorant (susceptibilityWalkParameter q) p.1.1 p.1.2) := by
  refine ⟨(d : ℝ) ^ 2 *
    (spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2))).toReal / 75, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact abs_fwdDiff_two_tauFourier_div_majorant_le hd q hchi hsecond p.2

/-- Evaluating the actual difference supremum gives the bootstrap majorant comparison. -/
theorem abs_fwdDiff_two_tauFourier_le_fourierDifferenceSup_mul_majorant (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤)
    {k l : Fin d → ℝ} (hk : 0 < 1 - nearestNeighborSymbol k) :
    |(fwdDiff k)^[2] (tauFourier q) (l - k)| ≤ fourierDifferenceSup q *
      bootstrapMajorant (susceptibilityWalkParameter q) k l := by
  have h := le_ciSup (bddAbove_fourierDifference hd q hchi hsecond) ⟨(k, l), hk⟩
  exact (div_le_iff₀ (bootstrapMajorant_pos hd
    (susceptibilityWalkParameter_mem_Ico q hchi) hk)).1 h

/-- A weak bound on the actual difference supremum gives its pointwise bootstrap estimate. -/
theorem abs_fwdDiff_two_tauFourier_le_mul_majorant_of_fourierDifferenceSup_le (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤)
    {K : ℝ} (hK : fourierDifferenceSup q ≤ K)
    {k l : Fin d → ℝ} (hk : 0 < 1 - nearestNeighborSymbol k) :
    |(fwdDiff k)^[2] (tauFourier q) (l - k)| ≤ K *
      bootstrapMajorant (susceptibilityWalkParameter q) k l := by
  exact (abs_fwdDiff_two_tauFourier_le_fourierDifferenceSup_mul_majorant
    hd q hchi hsecond hk).trans (mul_le_mul_of_nonneg_right hK
      (bootstrapMajorant_pos hd (susceptibilityWalkParameter_mem_Ico q hchi) hk).le)

/-- For transitive finite-range profiles, finite susceptibility already implies
the boundedness needed to evaluate the actual difference supremum. -/
theorem bddAbove_fourierDifference_of_finiteRange_of_transitive (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤) {R : ℝ}
    (hR : 0 ≤ R) (hq : ∀ x y : Fin d → ℤ, R < ‖x - y‖ → q s(x, y) = 0)
    (htrans : ∀ x y : Fin d → ℤ, ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ),
      σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) :
    BddAbove (range fun p :
      {p : (Fin d → ℝ) × (Fin d → ℝ) // 0 < 1 - nearestNeighborSymbol p.1} =>
        |(fwdDiff p.1.1)^[2] (tauFourier q) (p.1.2 - p.1.1)| /
          bootstrapMajorant (susceptibilityWalkParameter q) p.1.1 p.1.2) :=
  bddAbove_fourierDifference hd q hchi
    (spatialMoment_sq_lt_top_of_finiteRange_of_transitive q 0 hR hq htrans hchi).ne

/-- For a transitive finite-range law, a weak difference-supremum bound gives the
pointwise bootstrap estimate using finite susceptibility alone. -/
theorem abs_fwdDiff_two_tauFourier_le_mul_majorant_of_finiteRange_of_transitive
    (hd : 0 < d) (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤) {R : ℝ}
    (hR : 0 ≤ R) (hq : ∀ x y : Fin d → ℤ, R < ‖x - y‖ → q s(x, y) = 0)
    (htrans : ∀ x y : Fin d → ℤ, ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ),
      σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e)
    {K : ℝ} (hK : fourierDifferenceSup q ≤ K)
    {k l : Fin d → ℝ} (hk : 0 < 1 - nearestNeighborSymbol k) :
    |(fwdDiff k)^[2] (tauFourier q) (l - k)| ≤ K *
      bootstrapMajorant (susceptibilityWalkParameter q) k l :=
  abs_fwdDiff_two_tauFourier_le_mul_majorant_of_fourierDifferenceSup_le hd q hchi
    (spatialMoment_sq_lt_top_of_finiteRange_of_transitive q 0 hR hq htrans hchi).ne hK hk

end PercLib.Percolation.Bond.Lace
