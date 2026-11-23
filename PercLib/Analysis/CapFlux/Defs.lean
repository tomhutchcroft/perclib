/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived definitions for capped pivotal increments and the concrete power-law derivative
weight. These are abbreviations for existing cluster-function and kernel expressions; no new
probabilistic model or hypothesis structure is introduced.
-/
module

public import PercLib.Models.LongRange.Defs

/-!
# Definitions for cap-flux monotonicity and convergence

`capInc` expresses a capped inserted-pivotal increment using an extended-nonnegative minimum,
before real conversion. `capIncLim` is the corresponding real uncapped increment. These forms are
used to invoke dominated convergence without pretending that an infinite extended cluster has real
size zero everywhere. `plWeight` is the usual radial derivative weight of the sup-norm power law
at one pair.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond


namespace PercLib.Analysis.CapFlux

variable {d : ℕ}

/-- The capped inserted-pivotal increment at a root, pair, moment and cap. -/
def capInc (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p B : ℕ)
    (ω : Config (Fin d → ℤ)) : ℝ :=
  ((min ((cluster (insert e ω) o).encard : ℝ≥0∞) (B : ℝ≥0∞)).toReal) ^ p -
    ((min ((cluster (ω \ {e}) o).encard : ℝ≥0∞) (B : ℝ≥0∞)).toReal) ^ p

/-- The real inserted-pivotal increment without a cap. -/
def capIncLim (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p : ℕ)
    (ω : Config (Fin d → ℤ)) : ℝ :=
  (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
    ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal

/-- The cutoff derivative weight of one pair at scale `r` for the sup-norm power law. -/
def plWeight {d : ℕ} (α : ℝ) (β : ℝ≥0) (r : ℝ) (e : Sym2 (Fin d → ℤ)) : ℝ :=
  (PercLib.Models.LongRange.radialKernel (_root_.normSeminorm ℝ (Fin d → ℝ))
      (fun s => if s < r then 1 else 0) e : ℝ) *
    ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
      Real.exp (-(β : ℝ) * (PercLib.Models.LongRange.cutoffKernel
        (_root_.normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))

end PercLib.Analysis.CapFlux
