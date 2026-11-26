/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the ghost field on the rooted binary tree. Every statement is
assembled from lemmas proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GhostBinaryTree

/-!
# Ghost field on the rooted binary tree: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `binaryTree_ghost_recursion_and_critical`
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Asymptotics PercLib.Percolation.Bond
open scoped ENNReal Topology

namespace PercLib.Models

/-- On the rooted binary tree with open probability `p ∈ [0, 1]`, the ghost transform
`M_p(h) = E[1 - e^{-h|K|}]` of the root cluster satisfies
`M_p(h) = 1 - e^{-h} (1 - p M_p(h))^2` for every `h > 0`; at `p = 1/2`,
`M_{1/2}(h) = 2√(1-e^{-h}) / (1 + √(1-e^{-h}))` for `h > 0` and `M_{1/2}(h) ~ 2√h` as
`h ↓ 0`. -/
@[tag "4QV6"]
theorem binaryTree_ghost_recursion_and_critical (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    (∀ h : ℝ, 0 < h →
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
          ∂law q).toReal =
        1 - Real.exp (-h) * (1 - (p : ℝ) *
          (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
            ∂law q).toReal) ^ 2) ∧
    ((p : ℝ) = 1 / 2 →
      (∀ h : ℝ, 0 < h →
        (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
            ∂law q).toReal =
          2 * √(1 - Real.exp (-h)) / (1 + √(1 - Real.exp (-h)))) ∧
      (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
          (((cluster ω []).encard : ℝ≥0∞) : EReal)))) ∂law q).toReal)
        ~[𝓝[>] 0] fun h => 2 * √h) :=
  ⟨fun _ hh => binaryTree_ghost_recursion p q hq hh, fun hp =>
    ⟨fun _ hh => binaryTree_ghost_critical_eq p q hq hp hh,
      binaryTree_ghost_critical_isEquivalent p q hq hp⟩⟩

end PercLib.Models
