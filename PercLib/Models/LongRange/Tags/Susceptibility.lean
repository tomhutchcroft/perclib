/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for root independence of the susceptibility.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.RootIndependence

/-!
# Root independence of the susceptibility: correspondence

Wiki correspondence for the equality of susceptibilities under a transitive law.

## Main results

* `chi_eq_of_transitive_law`
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- Under a transitive law (a vertex bijection carrying `x` to `y` and preserving every edge
probability, for each `x, y`) the susceptibility does not depend on the root. -/
@[tag "QXWF"]
theorem chi_eq_of_transitive_law {V : Type*} (q : Sym2 V → unitInterval)
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, q (Sym2.map φ e) = q e) (x y : V) :
    chi q x = chi q y :=
  lintegral_encard_cluster_eq_of_transitive q hT (fun n => (n : ℝ≥0∞)) x y

end PercLib.Models.LongRange
