/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Mathematical reference: R. Ahlswede and D. E. Daykin, "An inequality for the weights of two
families of sets, their unions and intersections", Z. Wahrscheinlichkeitstheorie verw. Gebiete
43 (1978), 183–185. The proof is mathlib's `four_functions_theorem_univ`
(`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`).
-/
module

public import PercLib.Meta.Tag
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Basic.Real.Basic

/-!
# Four-functions inequality: statement form

The Ahlswede–Daykin four-functions inequality on the Boolean lattice `Finset E` of a finite
type `E`, restated from mathlib's `four_functions_theorem_univ`. On `Finset E` the lattice
operations `⊓` and `⊔` are `∩` and `∪` by definition, so the mathlib statement applies as is.

## Main results

* `four_functions_inequality`: the statement over all subsets of a finite type.
-/

@[expose] public section

open Finset

namespace PercLib.Probability

/-- The four-functions inequality: if nonnegative real functions `a b c d` on the subsets of a
finite type satisfy `a S * b T ≤ c (S ∩ T) * d (S ∪ T)` for all `S T`, then
`(∑ a) (∑ b) ≤ (∑ c) (∑ d)`. -/
@[tag "EZJ7"]
theorem four_functions_inequality {E : Type*} [Fintype E] [DecidableEq E]
    (a b c d : Finset E → ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : ∀ S T, a S * b T ≤ c (S ∩ T) * d (S ∪ T)) :
    (∑ S, a S) * (∑ S, b S) ≤ (∑ S, c S) * (∑ S, d S) :=
  four_functions_theorem_univ a b c d ha hb hc hd h

end PercLib.Probability
