/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.SpatialMoments.FiniteRange
public import PercLib.Percolation.Bond.SusceptibilityKernelContinuity

/-!
# Weighted two-point continuity for finite-range profiles

## Main results

A transitive finite-range upper profile with finite susceptibility supplies a
summable second-moment envelope. Susceptibility convergence along comparable
profiles then gives weighted absolute convergence of the two-point functions.
The spatial-moment bound is proved from the actual percolation law.
-/

@[expose] public section
noncomputable section

open Filter PercLib.Models.Site
open scoped Topology ENNReal

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-- Finite susceptibility and second spatial moment give a summable real weighted row. -/
theorem summable_one_add_norm_sq_mul_tau_toReal
    (q : Sym2 (LatticeSite d) → unitInterval) (o : LatticeSite d)
    (hchi : chi q o ≠ ⊤)
    (hsecond : spatialMoment q o (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤) :
    Summable fun x => (1 + ‖x - o‖ ^ 2) * (tau q o x).toReal := by
  have h0 : Summable fun x => (tau q o x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi)
  rw [spatialMoment_eq_tsum] at hsecond
  have h2 : Summable fun x => ‖x - o‖ ^ 2 * (tau q o x).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.summable_toReal hsecond
  simpa only [add_mul, one_mul] using h0.add h2

/-- Weighted convergence below a finite-range envelope, with no assumed
spatial-moment or weighted-continuity input. -/
theorem tendsto_norm_sq_weighted_tau_of_finiteRange {ι : Type*} {l : Filter ι}
    (q : ι → Sym2 (LatticeSite d) → unitInterval)
    (r s : Sym2 (LatticeSite d) → unitInterval) (o : LatticeSite d) {R : ℝ}
    (hR : 0 ≤ R) (hsrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → s s(x, y) = 0)
    (htrans : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, s (Sym2.map σ e) = s e)
    (hs : chi s o ≠ ⊤) (hrs : r ≤ s)
    (hnear : ∀ᶠ i in l, (q i ≤ r ∨ r ≤ q i) ∧ q i ≤ s)
    (hchi : Tendsto (fun i => (chi (q i) o).toReal) l (𝓝 (chi r o).toReal)) :
    Tendsto (fun i => ∑' x, (1 + ‖x - o‖ ^ 2) *
      |(tau (q i) o x).toReal - (tau r o x).toReal|) l (𝓝 0) := by
  refine tendsto_weighted_tau_toReal_sub_of_tendsto_chi q r s o
    (fun x => 1 + ‖x - o‖ ^ 2) (fun _ => by positivity)
    (ne_top_of_le_ne_top hs (chi_mono hrs o)) hrs ?_ hchi ?_
  · filter_upwards [hnear] with i hi
    exact ⟨hi.1, ne_top_of_le_ne_top hs (chi_mono hi.2 o), hi.2⟩
  · exact summable_one_add_norm_sq_mul_tau_toReal s o hs
      (spatialMoment_sq_lt_top_of_finiteRange_of_transitive s o hR hsrange htrans hs).ne

end PercLib.Percolation.Bond
