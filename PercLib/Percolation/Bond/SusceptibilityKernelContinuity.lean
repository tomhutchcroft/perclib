/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.SusceptibilityContinuity

/-!
# Two-point continuity controlled by susceptibility

## Main results

For comparable profiles of finite susceptibility, every two-point increment is
bounded by the susceptibility increment. Consequently, continuity of susceptibility
along an ordered family supplies two-point continuity without a separate event-limit
argument.
-/

@[expose] public section
noncomputable section

open Filter
open scoped Topology ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- Under monotone coupling, a two-point increment is one nonnegative summand
of the susceptibility increment. -/
theorem tau_toReal_sub_le_chi_toReal_sub {q r : Sym2 V → unitInterval}
    (hqr : q ≤ r) (o x : V) (hr : chi r o ≠ ⊤) :
    (tau r o x).toReal - (tau q o x).toReal ≤ (chi r o).toReal - (chi q o).toReal := by
  have hq : chi q o ≠ ⊤ := ne_top_of_le_ne_top hr (chi_mono hqr o)
  have hs (p : Sym2 V → unitInterval) (hp : chi p o ≠ ⊤) :
      Summable fun y => (tau p o y).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hp)
  have ht (p : Sym2 V → unitInterval) (y : V) : tau p o y ≠ ⊤ :=
    ((tau_le_one p o y).trans_lt ENNReal.one_lt_top).ne
  have hnonneg (y : V) : 0 ≤ (tau r o y).toReal - (tau q o y).toReal :=
    sub_nonneg.mpr (ENNReal.toReal_mono (ht r y) (tau_mono hqr o y))
  have h := (hs r hr |>.sub (hs q hq)).le_tsum x (fun y _ => hnonneg y)
  rw [(hs r hr).tsum_sub (hs q hq)] at h
  simpa only [chi_eq_tsum_tau, ENNReal.tsum_toReal_eq (ht r),
    ENNReal.tsum_toReal_eq (ht q)] using h

/-- Comparable profiles give an absolute increment bound, uniformly in the endpoint. -/
theorem abs_tau_toReal_sub_le_abs_chi_toReal_sub {q r : Sym2 V → unitInterval}
    (hcomp : q ≤ r ∨ r ≤ q) (o x : V) (hq : chi q o ≠ ⊤) (hr : chi r o ≠ ⊤) :
    |(tau r o x).toReal - (tau q o x).toReal| ≤
      |(chi r o).toReal - (chi q o).toReal| := by
  have hforward {p s : Sym2 V → unitInterval} (hps : p ≤ s) (hs : chi s o ≠ ⊤) :
      |(tau s o x).toReal - (tau p o x).toReal| ≤
        |(chi s o).toReal - (chi p o).toReal| := by
    have ht := ENNReal.toReal_mono
      (((tau_le_one s o x).trans_lt ENNReal.one_lt_top).ne) (tau_mono hps o x)
    rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    exact (tau_toReal_sub_le_chi_toReal_sub hps o x hs).trans (le_abs_self _)
  rcases hcomp with h | h
  · exact hforward h hr
  · simpa only [abs_sub_comm] using hforward h hq

/-- Susceptibility convergence implies two-point convergence when the nearby
profiles are comparable and have finite susceptibility. -/
theorem tendsto_tau_toReal_of_tendsto_chi_toReal {ι : Type*} {l : Filter ι}
    (q : ι → Sym2 V → unitInterval) (r : Sym2 V → unitInterval) (o x : V)
    (hr : chi r o ≠ ⊤)
    (hnear : ∀ᶠ i in l, (q i ≤ r ∨ r ≤ q i) ∧ chi (q i) o ≠ ⊤)
    (hchi : Tendsto (fun i => (chi (q i) o).toReal) l (𝓝 (chi r o).toReal)) :
    Tendsto (fun i => (tau (q i) o x).toReal) l (𝓝 (tau r o x).toReal) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ᶠ i in l, ‖(tau (q i) o x).toReal - (tau r o x).toReal‖ ≤
      |(chi (q i) o).toReal - (chi r o).toReal| := by
    filter_upwards [hnear] with i hi
    simpa only [Real.norm_eq_abs] using
      abs_tau_toReal_sub_le_abs_chi_toReal_sub hi.1.symm o x hr hi.2
  have hzero : Tendsto (fun i => |(chi (q i) o).toReal - (chi r o).toReal|) l (𝓝 0) := by
    simpa using (hchi.sub_const (chi r o).toReal).abs
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hzero

/-- A nearby finite weighted envelope upgrades susceptibility convergence to
weighted absolute convergence of the actual two-point functions. Nonnegativity
allows a single envelope, rather than twice the envelope. -/
theorem tendsto_weighted_tau_toReal_sub_of_tendsto_chi {ι : Type*} {l : Filter ι}
    (q : ι → Sym2 V → unitInterval) (r s : Sym2 V → unitInterval) (o : V) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : chi r o ≠ ⊤) (hrs : r ≤ s)
    (hnear : ∀ᶠ i in l, (q i ≤ r ∨ r ≤ q i) ∧ chi (q i) o ≠ ⊤ ∧ q i ≤ s)
    (hchi : Tendsto (fun i => (chi (q i) o).toReal) l (𝓝 (chi r o).toReal))
    (hweight : Summable fun x => w x * (tau s o x).toReal) :
    Tendsto (fun i => ∑' x, w x * |(tau (q i) o x).toReal - (tau r o x).toReal|)
      l (𝓝 0) := by
  have hpoint (x : V) := tendsto_tau_toReal_of_tendsto_chi_toReal q r o x hr
    (hnear.mono fun _ h => ⟨h.1, h.2.1⟩) hchi
  have ht (x : V) : tau s o x ≠ ⊤ :=
    ((tau_le_one s o x).trans_lt ENNReal.one_lt_top).ne
  have hlim (x : V) : Tendsto
      (fun i => w x * |(tau (q i) o x).toReal - (tau r o x).toReal|) l (𝓝 0) := by
    simpa using ((hpoint x).sub_const (tau r o x).toReal).abs.const_mul (w x)
  have hb : ∀ᶠ i in l, ∀ x,
      ‖w x * |(tau (q i) o x).toReal - (tau r o x).toReal|‖ ≤ w x * (tau s o x).toReal := by
    filter_upwards [hnear] with i hi x
    rw [Real.norm_of_nonneg (mul_nonneg (hw x) (abs_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (hw x)
    have hqle := ENNReal.toReal_mono (ht x) (tau_mono hi.2.2 o x)
    have hrle := ENNReal.toReal_mono (ht x) (tau_mono hrs o x)
    exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := tau (q i) o x)],
      by linarith [ENNReal.toReal_nonneg (a := tau r o x)]⟩
  simpa using tendsto_tsum_of_dominated_convergence hweight hlim hb

end PercLib.Percolation.Bond
