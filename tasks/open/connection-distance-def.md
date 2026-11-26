---
id: connection-distance-def
title: The extended connection distance -log tau (definition tag)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# The extended connection distance -log tau (definition tag)

## Goal
Tag the definition assertion **NZMZ** (article `directional-correlation-length`): the extended
connection distance of a bond profile, `D_q(x,y) = -log τ_q(x,y)` with `-log 0 = +∞`. The later
assertions of the article (the directional limit and its seminorm property) are stated in terms
of this function, so it needs one library spelling with its basic API.

## Target
For a profile `q : Sym2 V → unitInterval` and vertices `x y`, define
`D_q(x,y) = -log τ_q(x,y) ∈ [0, +∞]`, where `τ_q = tau q` (`PercLib/Percolation/Bond/Basic.lean`)
and `log` is mathlib's `ENNReal.log : ℝ≥0∞ → EReal` (so `log 0 = ⊥` and `-⊥ = ⊤`).

Sketch (spelling free):
```lean
/-- The extended connection distance `D_q(x, y) = -log τ_q(x, y)`. -/
@[tag "NZMZ"]
def connDist (q : Sym2 V → unitInterval) (x y : V) : EReal :=
  -(tau q x y).log
```
The spelling `-ENNReal.log (tau q x y)` is already used inline, with its pseudo-distance lemmas,
in `PercLib/Percolation/Bond/CorrelationLength.lean` (`neg_log_tau_self`, `neg_log_tau_comm`,
`neg_log_tau_le_add` (Harris), `neg_log_tau_nonneg`). The definition must unfold to exactly that
spelling, so that those lemmas transfer by `rfl`/`unfold`; do not reprove them and do not edit
`CorrelationLength.lean` (switching its statements to the new name is a later clean-up).

Basic API (D-35), in the same file, each a one-line restatement where an inline lemma exists:
1. `connDist_def` (unfolding lemma);
2. `connDist_nonneg` (from `neg_log_tau_nonneg`);
3. `connDist_eq_top_iff : connDist q x y = ⊤ ↔ tau q x y = 0` (new);
4. `connDist_self` (from `neg_log_tau_self`), `connDist_comm` (from `neg_log_tau_comm`);
5. `connDist_le_add` for countable `V` (from `neg_log_tau_le_add`);
6. `connDist_eq_neg_log_toReal`: `connDist q x y = -Real.log (tau q x y).toReal` when
   `0 < tau q x y` (new; compare `tau_toReal_pos`).

## Owned files
- New `PercLib/Percolation/Bond/ConnectionDistance/Defs.lean` (the definition and its API).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/Basic.lean` (`tau`, `tau_self`, `tau_le_one`, `tau_comm`),
`PercLib/Percolation/Bond/CorrelationLength.lean`, mathlib
(`ENNReal.log`, module `Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog`); wiki assertion NZMZ.

## Stop condition
NZMZ tagged on the definition, API lemmas proved, module built with `--wfail`.

## Hand-off
Pull request description: the definition, the list of API lemmas, build result.
