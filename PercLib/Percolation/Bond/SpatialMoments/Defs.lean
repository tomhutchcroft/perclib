/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The spatial moment of the cluster, `E[∑_{x ∈ K_o} w(x - o)]`, used in §I.4.1 and §I.5.1 of T.
Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, and in the wiki article
`spatial-cutoff-moments` (as `S = ∑_x ℓ(x)² τ(0, x)`), on the bond interface.

The notion corresponds to `spatialMoment` in the source formalisation (repository `yujinhkim/lrp`,
branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/VolumeMoments/SpatialMoments.lean`; licence Apache-2.0 as declared in that
file's header; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`), which is stated on a finite model with real values;
here it is a lower integral under `law q` with an `ℝ≥0∞`-valued weight. No code is copied; the API
and witness are new.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.BKEndpoints
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Spatial moments of the cluster

For a vertex set with subtraction, a root `o` and a weight `w : V → ℝ≥0∞`, the spatial moment
is `E[∑_{x ∈ K_o} w(x - o)]`. With `w x = ⟨x, u⟩²` it is the second spatial moment `S` of the
paper; the radius of gyration is a ratio of it and `chi`, and is written out where used.
By Tonelli it equals `∑_x w(x - o) τ(o, x)` (`spatialMoment_eq_tsum`), which is the form in the
wiki article `spatial-cutoff-moments` (0CUF, 7F5O, 5OBO, Z11O).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [AddGroup V]

/-- The **spatial moment** of the cluster of `o` with weight `w`:
`E_q[∑_{x ∈ K_o} w(x - o)]`. -/
def spatialMoment (q : Sym2 V → unitInterval) (o : V) (w : V → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => w (x - o)) x ∂law q

theorem spatialMoment_def (q : Sym2 V → unitInterval) (o : V) (w : V → ℝ≥0∞) :
    spatialMoment q o w = ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => w (x - o)) x ∂law q :=
  rfl

/-- Monotonicity in the weight. -/
theorem spatialMoment_mono (q : Sym2 V → unitInterval) (o : V) {w w' : V → ℝ≥0∞}
    (h : w ≤ w') : spatialMoment q o w ≤ spatialMoment q o w' :=
  lintegral_mono fun _ => ENNReal.tsum_le_tsum fun x =>
    indicator_le_indicator (h (x - o))

/-- Tonelli form: `E[∑_{x ∈ K_o} w(x - o)] = ∑_x w(x - o) τ(o, x)`. -/
theorem spatialMoment_eq_tsum [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (w : V → ℝ≥0∞) : spatialMoment q o w = ∑' x, w (x - o) * tau q o x := by
  have hind : ∀ x ω, (cluster ω o).indicator (fun x => w (x - o)) x =
      (conn o x).indicator (fun _ => w (x - o)) ω := by
    intro x ω
    by_cases h : x ∈ cluster ω o
    · rw [indicator_of_mem h, indicator_of_mem (show ω ∈ conn o x from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show ω ∉ conn o x from h)]
  rw [spatialMoment_def, lintegral_tsum fun x => ?_]
  · refine tsum_congr fun x => ?_
    simp_rw [hind x]
    rw [lintegral_indicator_const (measurableSet_conn o x), tau]
  · simp_rw [hind x]
    exact (measurable_const.indicator (measurableSet_conn o x)).aemeasurable

/-! ### Witness -/

/-- With every pair closed (`q = 0`) the cluster is `{o}`, and the spatial moment is `w 0`. -/
theorem spatialMoment_zero [Countable V] (o : V) (w : V → ℝ≥0∞) :
    spatialMoment (fun _ => 0) o w = w 0 := by
  have hlaw : law (fun _ : Sym2 V => (0 : unitInterval)) = Measure.dirac ∅ := by
    rw [law, ← PercLib.Probability.prodBernoulli_deterministic (∅ : Set (Sym2 V))]
    simp
  rw [spatialMoment_eq_tsum, tsum_eq_single o]
  · rw [sub_self, tau, hlaw, Measure.dirac_apply' _ (measurableSet_conn o o)]
    simp [conn_self]
  · intro x hx
    rw [tau, hlaw, Measure.dirac_apply' _ (measurableSet_conn o x),
      indicator_of_notMem (fun h => hx ((empty_mem_conn_iff o x).1 h).symm),
      mul_zero]

end PercLib.Percolation.Bond
