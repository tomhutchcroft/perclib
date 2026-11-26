/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the closure properties of the cone of functions with nonnegative
Boolean coefficients, proved from `BooleanCoefficients.lean` and
`BooleanCoefficients/Defs.lean`. Mathematical reference: Möbius inversion on the Boolean
lattice, R. P. Stanley, *Enumerative Combinatorics*, Vol. 1, Section 3.7. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.BooleanCoefficients
public import Mathlib.Basic.Real.Basic

/-!
# Nonnegative Boolean coefficients under products and coordinate differences

Restates the uniqueness and inversion formula of the Boolean coefficients and the closure
properties of the cone `HasNonnegMobiusCoeffs E` in the form of the wiki assertion.

## Main results

* `PercLib.hasNonnegMobiusCoeffs_closure`: uniqueness of the coefficients with the inversion
  formula; closure under nonnegative linear combinations and pointwise products; for `e ∈ E`,
  the restrictions `f⁻ S = f S`, `f⁺ S = f (S ∪ {e})` and the difference `f⁺ - f⁻` lie in the
  cone over `E \ {e}`.
-/

@[expose] public section

namespace PercLib

universe u

variable {α : Type*} [DecidableEq α]

/-- **Nonnegative Boolean coefficients are preserved by products and coordinate differences.**
Let `E` be a finite set and `𝒞_E` the functions `f S = ∑_{T ⊆ S} a T` (`S ⊆ E`) with all
`a T ≥ 0` (`HasNonnegMobiusCoeffs E f`). Coefficients representing a function on the subsets
of `E` are unique, given by `a T = ∑_{U ⊆ T} (-1)^{|T \ U|} f U`. The cone `𝒞_E` is closed
under nonnegative linear combinations and pointwise products. For `e ∈ E` and `f ∈ 𝒞_E`, the
restrictions `f⁻ S = f S` and `f⁺ S = f (S ∪ {e})` and the difference `f⁺ - f⁻` belong to
`𝒞_{E \ {e}}`.

The uniqueness clause is stated for every representation, without assuming nonnegative
coefficients. -/
@[tag "CUE4"]
theorem hasNonnegMobiusCoeffs_closure (E : Finset α) :
    (∀ f a : Finset α → ℝ, (∀ S ⊆ E, f S = ∑ T ∈ S.powerset, a T) →
      ∀ T ⊆ E, a T = ∑ U ∈ T.powerset, (-1 : ℝ) ^ (T \ U).card * f U) ∧
    (∀ (ι : Type u) (s : Finset ι) (c : ι → ℝ) (F : ι → Finset α → ℝ),
      (∀ i ∈ s, 0 ≤ c i) → (∀ i ∈ s, HasNonnegMobiusCoeffs E (F i)) →
      HasNonnegMobiusCoeffs E (fun S ↦ ∑ i ∈ s, c i * F i S)) ∧
    (∀ f g : Finset α → ℝ, HasNonnegMobiusCoeffs E f → HasNonnegMobiusCoeffs E g →
      HasNonnegMobiusCoeffs E (fun S ↦ f S * g S)) ∧
    (∀ e ∈ E, ∀ f : Finset α → ℝ, HasNonnegMobiusCoeffs E f →
      HasNonnegMobiusCoeffs (E.erase e) f ∧
      HasNonnegMobiusCoeffs (E.erase e) (fun S ↦ f (insert e S)) ∧
      HasNonnegMobiusCoeffs (E.erase e) (fun S ↦ f (insert e S) - f S)) :=
  ⟨fun _ _ h _ hT ↦ (mobiusCoeff_eq_of_forall_eq_sum h hT).symm,
    fun _ s _ _ hc hF ↦ hasNonnegMobiusCoeffs_sum s hc hF,
    fun _ _ hf hg ↦ hf.mul hg,
    fun e he _ hf ↦ ⟨hf.erase e, hf.comp_insert he, hf.comp_insert_sub he⟩⟩

end PercLib
