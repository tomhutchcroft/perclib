/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for a displacement-kernel assertion: cuts on both sides of every
vertex for a one-dimensional distance profile with finite first moment. All mathematical
inputs are proved in the imported module; no definition is added and no Input is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.OneDimensional

/-! # Cuts on the line for off-diagonal distance profiles: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Models.LongRange.OneDimensional`.

## Main results

* `ae_cuts_unbounded_and_cluster_finite`: for a profile `q` on `ℤ` with
  `q s(a,b) = p |b - a|` off the diagonal (diagonal arbitrary), `p n < 1` for `n ≥ 1` and
  `∑ n p n < ∞`, almost surely closed gaps occur arbitrarily far to the right and to the
  left, and every open cluster is finite.
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- On `ℤ`, let the pair probabilities be a distance profile `p` off the diagonal (any
values on the diagonal), with `p n < 1` for every `n ≥ 1` and `∑ n p n` finite. Then
almost surely the closed gaps are unbounded above and below, and every open cluster is
finite. -/
@[tag "ZH13"]
theorem ae_cuts_unbounded_and_cluster_finite (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, (∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k) ∧
      (∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k) ∧
      ∀ x, (cluster ω x).Finite :=
  (ae_cuts_atTop_of_offDiagonal p q hq hlt hsum).and
    ((ae_cuts_atBot_of_offDiagonal p q hq hlt hsum).and
      (ae_cluster_finite_of_offDiagonal p q hq hlt hsum))

end PercLib.Models.LongRange
