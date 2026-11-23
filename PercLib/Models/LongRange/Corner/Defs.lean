/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Models.LongRange.RestorationDerivativeGeneral

/-!
# Definitions for the radius-one corner computation

These abbreviations and the real-valued moment retain the canonical sup-norm power-law cut-off
percolation law on the entire infinite lattice. They do not introduce a finite-graph proxy or a
new intensity assumption. The proof statements that constrain this model are in `MomentCorner`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange.Corner

variable {d : ℕ}

/-- The power-law cut-off profile used throughout production. -/
noncomputable abbrev prof (d : ℕ) (α : ℝ) : ℝ → ℝ :=
  PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)

/-- The sup norm on `ℤ^d` as a seminorm on `ℝ^d`. -/
noncomputable abbrev snorm (d : ℕ) : Seminorm ℝ (Fin d → ℝ) := normSeminorm ℝ (Fin d → ℝ)

/-- The cut-off law `μ_r` of the paper. -/
noncomputable abbrev mu (d : ℕ) (α : ℝ) (β : ℝ≥0) (r : ℝ) : Measure (Config (Fin d → ℤ)) :=
  law (intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) (snorm d) (prof d α) r) β)

/-- The paper's `p`-th root moment, in production's carrier. -/
noncomputable def moment (d : ℕ) (α : ℝ) (β : ℝ≥0) (p : ℕ) (r : ℝ) : ℝ :=
  ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal ∂(mu d α β r)


end PercLib.Models.LongRange.Corner
