/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Poisson/Scalar.lean`; added at source revision
`a1dd3fd7178264bb1dfc2c71abc2cdca25da9d48`,
supplied under its Apache-2.0 header. Canonical definitions and their stated API are moved into
this interface module; declarations are unchanged except for the coordinated namespace prefix.
The forbidden `set_option autoImplicit false` was removed, since the build enforces it.
-/
module

public import PercLib.Probability.Exploration.AdaptedReveal.PGF

/-!
# The one-coordinate Bernoulli generating-function factor

The factor `t * p + (1 - p)` in `ℝ≥0∞`. Truncated subtraction needs its stated hypotheses;
no positivity or finite-product statement is made unconditionally by this interface file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace PercLib.Probability.ExplorationPoisson

/-- The `ℝ≥0∞`-valued one-coordinate Bernoulli pgf factor `t * p + (1 - p)`. It is intended for
`p ≤ 1`; for `p > 1` truncated subtraction makes it `t * p`. -/
def pgfFactor (t p : ℝ≥0∞) : ℝ≥0∞ := t * p + (1 - p)

theorem pgfFactor_def (t p : ℝ≥0∞) : pgfFactor t p = t * p + (1 - p) := rfl

end PercLib.Probability.ExplorationPoisson
