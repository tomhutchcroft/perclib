/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the zero-one law under law-preserving separating relabellings.
Every statement is assembled from lemmas proved in the imported modules; no new definition
is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.Mixing

/-!
# Zero-one law under separating relabellings: statement form

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `prodBernoulli_ergodic`
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set

namespace PercLib.Probability
variable {ι : Type*}

/-- Ergodicity: under relabellings that preserve the Bernoulli law and separate finite
sets, invariant measurable events have probability `0` or `1`, and invariant measurable
`ℕ∞`-valued observables take some value with probability one. -/
@[tag "DRQ2"]
theorem prodBernoulli_ergodic (p : ι → unitInterval) (e : ℕ → ι ≃ ι)
    (hpres : ∀ n, MeasurePreserving (fun ω : Set ι => e n '' ω)
      (prodBernoulli p) (prodBernoulli p))
    (hsep : ∀ F G : Finset ι, ∀ᶠ n in atTop, ∀ i ∈ F, e n i ∉ G) :
    (∀ A : Set (Set ι), MeasurableSet A → (∀ n, (fun ω : Set ι => e n '' ω) ⁻¹' A = A) →
      prodBernoulli p A = 0 ∨ prodBernoulli p A = 1) ∧
    (∀ f : Set ι → ℕ∞, Measurable f → (∀ n ω, f (e n '' ω) = f ω) →
      ∃ c : ℕ∞, prodBernoulli p {ω | f ω = c} = 1) :=
  ⟨fun _ hA hinv => prodBernoulli_eq_zero_or_one_of_invariant p e hpres hsep hA hinv,
    fun _ hf hinv => prodBernoulli_exists_measure_eq_one_of_invariant p e hpres hsep hf hinv⟩

end PercLib.Probability
