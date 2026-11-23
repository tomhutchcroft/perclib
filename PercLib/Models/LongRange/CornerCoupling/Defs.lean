/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module
public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Models.LongRange.CutoffCorner
public import PercLib.Models.LongRange.UncappedMomentContinuity
public import PercLib.Probability.Superposition
public import PercLib.Probability.ClosedProduct
public import PercLib.Probability.CapMoment
public import PercLib.Percolation.Bond.ClosedCertificates

/-!
# Definitions for the softened-edge coupling between integer cutoff radii

For `n ∈ ℕ` and `r ∈ [n,n+1)`, the kernel profile at radius `r` is equal in law to the
independent union of the radius-`n` configuration and an independent reopening configuration.
The definitions retain existing short edges with a uniform retention probability and reopen
closed short edges independently. They concern the full infinite lattice, not a finite proxy.
-/

@[expose] public section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open scoped ENNReal NNReal unitInterval Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-- The supremum-norm model norm on `ℤ^d`. -/
noncomputable abbrev supModelNorm (d : ℕ) : PercLib.Analysis.ModelNorm (Fin d → ℝ) :=
  PercLib.Analysis.ModelNorm.ofNorm (Fin d → ℝ)

/-- The length of a pair of lattice points under the supremum norm. -/
noncomputable def edgeLen (e : Sym2 (Fin d → ℤ)) : ℝ :=
  Sym2.lift ⟨fun x y => ‖x - y‖, fun x y => norm_sub_rev x y⟩ e

/-- The edge set of the cut-off at integer scale `n`: pairs of distinct points of length at
most `n`. At every scale `r ∈ [n, n+1)` the kernel is supported exactly on this set. -/
def scaleSupport (n : ℕ) : Set (Sym2 (Fin d → ℤ)) :=
  {e | 0 < edgeLen e ∧ edgeLen e ≤ (n : ℝ)}

open Classical in
/-- The **softening factor** of the cut-off at integer scale `n`: `1` off the scale-`n` support
and the retention probability `exp (-(β (K n - K r)))` of a closed edge on it. -/
noncomputable def softenFactor (K : ℝ → ℝ) (β : ℝ≥0) (n : ℕ) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) : ℝ :=
  if e ∈ scaleSupport n then Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)) else 1

open Classical in
/-- The **reopening profile**: a closed edge of the scale-`n` support is reopened
independently with probability `ρ`. -/
noncomputable def reopenProfile (n : ℕ) (ρ : unitInterval) :
    Sym2 (Fin d → ℤ) → unitInterval :=
  fun e => if e ∈ scaleSupport n then ρ else 0

end PercLib.Models.LongRange
