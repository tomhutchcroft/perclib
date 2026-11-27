/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.BoundaryRusso.Exhaustion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Differentiating the actual boundary susceptibility identity

## Main results

The integrated Russo identity gives the derivative of susceptibility almost everywhere
as the actual finite-cluster expectation of boundary susceptibility. A countable interval
cover gives the same identity throughout an open interval of finite susceptibility;
finiteness at the excluded upper endpoint is not required.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- On a positive compact interval with finite uniform susceptibility at its upper
endpoint, the actual boundary expectation is the derivative of susceptibility almost
everywhere in the interior. This is a consequence of integrated Russo and the Lebesgue
fundamental theorem of calculus. -/
theorem ae_hasDerivAt_chi_boundarySusceptibility_of_upper_finite
    (J : Sym2 V → ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hchi : (⨆ v, chi (intensityProfile J b.toNNReal) v) ≠ ⊤) :
    ∀ᵐ t, t ∈ Ioo a b →
      HasDerivAt (fun s : ℝ => (chi (intensityProfile J s.toNNReal) o).toReal)
        (∑' C : Finset V, (law (intensityProfile J t.toNNReal)).real
          {ω | cluster ω o = (C : Set V)} * boundarySusceptibility J t.toNNReal C) t := by
  have hint := intervalIntegrable_tsum_law_cluster_eq_mul_boundarySusceptibility
    J o R hrow hab hchi
  filter_upwards [hint.ae_hasDerivAt_integral] with t ht htab
  have hta : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨htab.1.le, htab.2.le⟩
  have hder := (ht hta a left_mem_uIcc).const_add
    (chi (intensityProfile J a.toNNReal) o).toReal
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htab.1 htab.2] with s hs
  have hchis : (⨆ v, chi (intensityProfile J s.toNNReal) v) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hchi (iSup_le fun v => ?_)
    exact (chi_mono (fun e => intensityProfile_mono J
      (Real.toNNReal_le_toNNReal hs.2.le) e) v).trans (le_iSup _ v)
  have h := chi_sub_eq_integral_boundarySusceptibility J o R hrow ha hs.1.le hchis
  linarith

/-- The actual derivative identity on an open interval. Only susceptibility inside
the interval must be finite; no assertion at either excluded endpoint is assumed. -/
theorem ae_hasDerivAt_chi_boundarySusceptibility
    (J : Sym2 V → ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ t ∈ Ioo a b, (⨆ v, chi (intensityProfile J t.toNNReal) v) ≠ ⊤) :
    ∀ᵐ t, t ∈ Ioo a b →
      HasDerivAt (fun s : ℝ => (chi (intensityProfile J s.toNNReal) o).toReal)
        (∑' C : Finset V, (law (intensityProfile J t.toNNReal)).real
          {ω | cluster ω o = (C : Set V)} * boundarySusceptibility J t.toNNReal C) t := by
  have hrat (s r : ℚ) : ∀ᵐ t,
      a < (s : ℝ) → (r : ℝ) < b → (s : ℝ) < r → t ∈ Ioo (s : ℝ) r →
      HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal)
        (∑' C : Finset V, (law (intensityProfile J t.toNNReal)).real
          {ω | cluster ω o = (C : Set V)} * boundarySusceptibility J t.toNNReal C) t := by
    by_cases hs : a < (s : ℝ)
    · by_cases hr : (r : ℝ) < b
      · by_cases hsr : (s : ℝ) < r
        · exact (ae_hasDerivAt_chi_boundarySusceptibility_of_upper_finite J o R hrow
            (ha.trans_lt hs) hsr.le (hfin r ⟨hs.trans hsr, hr⟩)).mono
            fun t ht _ _ _ htab => ht htab
        · exact Eventually.of_forall fun _ _ _ h => (hsr h).elim
      · exact Eventually.of_forall fun _ _ h => (hr h).elim
    · exact Eventually.of_forall fun _ h => (hs h).elim
  filter_upwards [ae_all_iff.mpr fun s => ae_all_iff.mpr (hrat s)] with t ht htab
  obtain ⟨s, has, hst⟩ := exists_rat_btwn htab.1
  obtain ⟨r, htr, hrb⟩ := exists_rat_btwn htab.2
  exact ht s r has hrb (hst.trans htr) ⟨hst, htr⟩

end PercLib.Percolation.Bond
