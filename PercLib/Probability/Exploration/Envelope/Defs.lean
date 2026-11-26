/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Definitions adapted from repository `yujinhkim/lrp`, branch
`work/yujinhkim-critical-lrp-orchestration`, file
`PercLib/Probability/Exploration/Envelope/Defs.lean`; added at source revision
`d5e0763c9187ea85e4877ae4f6a19ab0b58c1c4d`, supplied under its Apache-2.0 header.
Changes: the forbidden `set_option autoImplicit false` was removed (the build enforces it), and
audit-only commands and scratch comments were removed. Mathematical reference: the accompanying
uniform-row-sum frontier-exploration proof outline, §1 (R_m) and (5.1). These are scalar and
finite-configuration ingredients, not an infinite-cluster moment theorem.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset

/-!
# Definitions for the scalar exploration envelope

The recursion `u₀ = 1`, `uₙ₊₁ = exp (m (λ uₙ - 1))`, a uniform bound on all finite partial row
sums, and finite Bernoulli configuration weights.

## Main definitions

* `PercLib.Probability.ExplorationEnvelope.envelope`
* `PercLib.Probability.ExplorationEnvelope.configWeight`
* `PercLib.Probability.ExplorationEnvelope.tiltedWeight`
-/

@[expose] public section

namespace PercLib.Probability.ExplorationEnvelope

/-- One step of the envelope recursion: `u ↦ exp (m * (λ * u - 1))`. -/
noncomputable def envelopeStep (m lam u : ℝ) : ℝ := Real.exp (m * (lam * u - 1))

/-- The envelope sequence `u_0 = 1`, `u_{n+1} = exp (m * (λ * u_n - 1))` of the exploration outline (5.1).
It is the number of "units of λ-weight" carried by one vertex of the frontier after `n`
generations of the exploration. -/
noncomputable def envelope (m lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | (n + 1) => envelopeStep m lam (envelope m lam n)

@[simp]
theorem envelope_zero (m lam : ℝ) : envelope m lam 0 = 1 := rfl

theorem envelope_succ (m lam : ℝ) (n : ℕ) :
    envelope m lam (n + 1) = envelopeStep m lam (envelope m lam n) := rfl

/-- Weight of a finite open-edge configuration under independent Bernoulli edge probabilities. -/
noncomputable def configWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (s : Finset ι) : ℝ :=
  (∏ e ∈ s, p e) * ∏ e ∈ sᶜ, (1 - p e)

/-- Exact probability of the configuration `s ⊆ ι` times `t^{#(open edges of s inside S)}`:
the `S`-tilted configuration weight, used for the per-vertex Poisson domination
(the exploration outline, Lemma 4.4, with the edge set `S` and `t ≥ 1`). -/
noncomputable def tiltedWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (t : ℝ) (S s : Finset ι) : ℝ :=
  (∏ e ∈ s, p e * (if e ∈ S then t else 1)) * ∏ e ∈ sᶜ, (1 - p e)

end PercLib.Probability.ExplorationEnvelope
