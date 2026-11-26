/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions and proofs for this project; no upstream Lean code is copied.
Mathematical reference: Heydenreich and van der Hofstad (2017), Chapter 8.
-/
module

public import PercLib.Analysis.LatticeFourier.Bounds
public import PercLib.Percolation.Bond.RowSum
public import PercLib.Probability.BKEndpoints

/-!
# Canonical percolation Fourier bootstrap quantities

The walk comparison uses the ordinary nearest-neighbour symbol. The ratio supremum
includes an absolute value, so its definition does not rely on a Fourier-positivity
theorem. The second-difference supremum excludes every real frequency with zero
symbol deficit, which is the zero frequency modulo periods on the torus.

## Main results

* `tauFourier`, `susceptibilityWalkParameter`: the actual model transform and normalization.
* `bootstrapTripleProduct`, `bootstrapMajorant`: the three-resolvent factor and `200 g V`.
* `fourierRatioSup`, `fourierDifferenceSup`: the canonical absolute bootstrap suprema.
* `three_quarters_le_bootstrapTripleProduct`: the derived uniform positive denominator factor.

The zero profile has transform one, parameter zero, ratio supremum one and difference
supremum zero. The analytic quantities retain their total real-valued definitions outside
the finite-susceptibility regime; their positivity statements have explicit hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Analysis
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The rooted real Fourier transform of the actual two-point function. -/
def tauFourier (q : Sym2 (Fin d → ℤ) → unitInterval) (k : Fin d → ℝ) : ℝ :=
  latticeCosineTransform (fun x => (tau q 0 x).toReal) k

theorem tauFourier_def (q : Sym2 (Fin d → ℤ) → unitInterval) (k : Fin d → ℝ) :
    tauFourier q k = ∑' x, (tau q 0 x).toReal * Real.cos (∑ i, k i * (x i : ℝ)) := rfl

@[simp] theorem tauFourier_at_zero (q : Sym2 (Fin d → ℤ) → unitInterval) :
    tauFourier q 0 = (chi q 0).toReal := by
  rw [tauFourier, latticeCosineTransform_at_zero, chi_eq_tsum_tau]
  exact (ENNReal.tsum_toReal_eq fun x =>
    ((tau_le_one q 0 x).trans_lt ENNReal.one_lt_top).ne).symm

@[simp] theorem tauFourier_neg_frequency (q : Sym2 (Fin d → ℤ) → unitInterval)
    (k : Fin d → ℝ) : tauFourier q (-k) = tauFourier q k :=
  latticeCosineTransform_neg_frequency _ _

/-- The actual walk parameter extracted from susceptibility. -/
def susceptibilityWalkParameter (q : Sym2 (Fin d → ℤ) → unitInterval) : ℝ :=
  1 - (chi q 0).toReal⁻¹

theorem susceptibilityWalkParameter_def (q : Sym2 (Fin d → ℤ) → unitInterval) :
    susceptibilityWalkParameter q = 1 - (chi q 0).toReal⁻¹ := rfl

/-- The three positive resolvent products in the bootstrap denominator. -/
def bootstrapTripleProduct (lam : ℝ) (k l : Fin d → ℝ) : ℝ :=
  nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam l +
    nearestNeighborResolvent lam l * nearestNeighborResolvent lam (l + k) +
    nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam (l + k)

theorem bootstrapTripleProduct_def (lam : ℝ) (k l : Fin d → ℝ) :
    bootstrapTripleProduct lam k l =
      nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam l +
      nearestNeighborResolvent lam l * nearestNeighborResolvent lam (l + k) +
      nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam (l + k) := rfl

/-- The conventional nearest-neighbour bootstrap majorant `U = 200 (1 - D) V`. -/
def bootstrapMajorant (lam : ℝ) (k l : Fin d → ℝ) : ℝ :=
  200 * (1 - nearestNeighborSymbol k) * bootstrapTripleProduct lam k l

theorem bootstrapMajorant_def (lam : ℝ) (k l : Fin d → ℝ) :
    bootstrapMajorant lam k l =
      200 * (1 - nearestNeighborSymbol k) * bootstrapTripleProduct lam k l := rfl

/-- The absolute Fourier-ratio bootstrap supremum. -/
def fourierRatioSup (q : Sym2 (Fin d → ℤ) → unitInterval) : ℝ :=
  ⨆ k : Fin d → ℝ, |tauFourier q k *
    (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k)|

theorem fourierRatioSup_def (q : Sym2 (Fin d → ℤ) → unitInterval) :
    fourierRatioSup q = ⨆ k : Fin d → ℝ, |tauFourier q k *
      (1 - susceptibilityWalkParameter q * nearestNeighborSymbol k)| := rfl

/-- The second-difference bootstrap supremum on positive-deficit frequencies.
The pair is ordered as `(k,l)`, matching the denominator convention. -/
def fourierDifferenceSup (q : Sym2 (Fin d → ℤ) → unitInterval) : ℝ :=
  ⨆ p : {p : (Fin d → ℝ) × (Fin d → ℝ) // 0 < 1 - nearestNeighborSymbol p.1},
    |(fwdDiff p.1.1)^[2] (tauFourier q) (p.1.2 - p.1.1)| /
      bootstrapMajorant (susceptibilityWalkParameter q) p.1.1 p.1.2

/-- The expanded numerator agrees with the existing symmetric-difference formulas. -/
theorem fourierDifferenceSup_def (q : Sym2 (Fin d → ℤ) → unitInterval) :
    fourierDifferenceSup q =
      ⨆ p : {p : (Fin d → ℝ) × (Fin d → ℝ) // 0 < 1 - nearestNeighborSymbol p.1},
        |tauFourier q (p.1.2 - p.1.1) + tauFourier q (p.1.2 + p.1.1) -
          2 * tauFourier q p.1.2| /
          bootstrapMajorant (susceptibilityWalkParameter q) p.1.1 p.1.2 := by
  simp only [fourierDifferenceSup, fwdDiff_two_at_sub]

@[simp] theorem bootstrapTripleProduct_zero_parameter (k l : Fin d → ℝ) :
    bootstrapTripleProduct 0 k l = 3 := by norm_num [bootstrapTripleProduct]

@[simp] theorem bootstrapMajorant_zero_parameter (k l : Fin d → ℝ) :
    bootstrapMajorant 0 k l = 600 * (1 - nearestNeighborSymbol k) := by
  simp only [bootstrapMajorant, bootstrapTripleProduct_zero_parameter]
  ring

/-- The three-resolvent factor is uniformly bounded below by three quarters. -/
theorem three_quarters_le_bootstrapTripleProduct (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) (k l : Fin d → ℝ) :
    (3 / 4 : ℝ) ≤ bootstrapTripleProduct lam k l := by
  have hp (a b : Fin d → ℝ) : (1 / 4 : ℝ) ≤
      nearestNeighborResolvent lam a * nearestNeighborResolvent lam b := by
    have h := mul_le_mul (half_le_nearestNeighborResolvent hd hlam a)
      (half_le_nearestNeighborResolvent hd hlam b) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (nearestNeighborResolvent_pos hd hlam a).le
    norm_num at h ⊢
    exact h
  unfold bootstrapTripleProduct
  linarith [hp (l - k) l, hp l (l + k), hp (l - k) (l + k)]

/-- The bootstrap majorant is positive on precisely the frequency region used in its quotient. -/
theorem bootstrapMajorant_pos (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) {k l : Fin d → ℝ}
    (hk : 0 < 1 - nearestNeighborSymbol k) : 0 < bootstrapMajorant lam k l := by
  have hV := three_quarters_le_bootstrapTripleProduct hd hlam k l
  unfold bootstrapMajorant
  exact mul_pos (mul_pos (by norm_num) hk) (by linarith)

@[simp] theorem tauFourier_zero_profile (k : Fin d → ℝ) :
    tauFourier (fun _ => 0) k = 1 := by
  classical
  have hlaw : law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) = Measure.dirac ∅ := by
    rw [law, ← PercLib.Probability.prodBernoulli_deterministic (∅ : Config (Fin d → ℤ))]
    simp
  rw [tauFourier_def, tsum_eq_single 0]
  · simp [tau_self]
  · intro x hx
    have ht : tau (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) 0 x = 0 := by
      rw [tau, hlaw, Measure.dirac_apply' _ (measurableSet_conn 0 x)]
      exact indicator_of_notMem (fun h => hx ((empty_mem_conn_iff 0 x).1 h).symm) _
    simp [ht]

@[simp] theorem susceptibilityWalkParameter_zero_profile :
    susceptibilityWalkParameter (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) = 0 := by
  rw [susceptibilityWalkParameter, chi_eq_one_of_offDiagonal_zero _ (fun _ _ _ => rfl)]
  norm_num

@[simp] theorem fourierRatioSup_zero_profile :
    fourierRatioSup (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) = 1 := by
  simp [fourierRatioSup]

@[simp] theorem fourierDifferenceSup_zero_profile :
    fourierDifferenceSup (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) = 0 := by
  norm_num [fourierDifferenceSup_def]

end PercLib.Percolation.Bond.Lace
