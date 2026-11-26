/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the insertion recursion of higher correlations and the correlation
of nested events, and the conditioning identity for the three-function correlation, proved in
`PercLib.Probability.HigherCorrelation` and `PercLib.Probability.ConditionalCorrelation`.
Mathematical references: D. St. P. Richards, *Algebraic methods toward higher-order probability
inequalities, II*, Ann. Probab. 32 (2004); E. H. Lieb and S. Sahi, *On the extension of the FKG
inequality to n functions*, J. Math. Phys. 63 (2022), Section 2. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.HigherCorrelation
public import PercLib.Probability.ConditionalCorrelation

/-!
# Higher correlations: insertion recursion, nested events and conditioning

## Main results

* `PercLib.higherCorrelation_insert_and_indicator_nested`: the recursion obtained by inserting
  one argument, and the product formula with its nonnegativity for nested events.
* `PercLib.higherCorrelation_fin_three_condExp_and_exists_covariance_sum_neg`: the conditioning
  identity for `E_3` and a negative covariance sum on two fair bits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace PercLib

universe u

/-- **Insertion of one argument gives a correlation recursion and a nested-event product
formula.** The higher correlation `E_s(f) = higherCorrelation μ s f` of a finite family is
indexed by a finset, so `E_n(f_1, …, f_{n-1}, f)` is `E_{insert a s}` of a family `f` with
`f a = f` and `s` indexing `f_1, …, f_{n-1}` (`n ≥ 2` is `s` nonempty). Then
`E_n(f_1, …, f_{n-1}, f) = ∑_{i=1}^{n-1} E_{n-1}(f_1, …, f_i f, …, f_{n-1}) - (∫ f) E_{n-1}(f_1, …,
f_{n-1})`; the identity needs no boundedness. Under a probability measure, if
`A 0 ⊆ ⋯ ⊆ A (n-1)` are measurable events with probabilities `a_j`, then
`E_n(1_{A 0}, …, 1_{A (n-1)}) = a_0 ∏_{j=1}^{n-1} (j - a_j) ≥ 0`, which is
`a_1 ∏_{j=2}^n (j - 1 - a_j) ≥ 0` in one-based indexing. -/
@[tag "AFJX"]
theorem higherCorrelation_insert_and_indicator_nested {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) :
    (∀ (ι : Type u) [DecidableEq ι] (a : ι) (s : Finset ι), a ∉ s → s.Nonempty →
      ∀ f : ι → Ω → ℝ, higherCorrelation μ (insert a s) f =
        ∑ i ∈ s, higherCorrelation μ s (Function.update f i (f i * f a)) -
          (∫ ω, f a ω ∂μ) * higherCorrelation μ s f) ∧
    (IsProbabilityMeasure μ → ∀ (n : ℕ) (hn : 0 < n) (A : Fin n → Set Ω),
      (∀ i, MeasurableSet (A i)) → Monotone A →
      higherCorrelation μ univ (fun i ↦ (A i).indicator 1) =
          μ.real (A ⟨0, hn⟩) *
            ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j)) ∧
        0 ≤ μ.real (A ⟨0, hn⟩) *
            ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j))) :=
  ⟨fun _ _ _ _ ha hs f ↦ higherCorrelation_insert μ ha hs f,
    fun _ _ hn A hA hmono ↦ higherCorrelation_indicator_fin_of_monotone μ hn A hA hmono⟩

/-- **Conditional three-function correlations have an additional covariance term.** Let
`f 0, f 1, f 2` be bounded real random variables on a probability space and `m` a
sub-σ-algebra. With `M i = μ[f i | m]`, `c i j = μ[f i * f j | m] - M i * M j` and `L` the
expression defining `E_3` with every expectation replaced by the conditional expectation given
`m`, `E_3(f) = ∫ L + E_3(M) + cov(c 0 1, M 2) + cov(c 0 2, M 1) + cov(c 1 2, M 0)`, where
`E_3 = higherCorrelation μ univ` on `Fin 3`. The covariance sum can be negative even for
nonnegative increasing functions of independent fair bits: under the uniform law on
`Bool × Bool` (two independent fair bits), conditioning on the second bit. -/
@[tag "ICQP"]
theorem higherCorrelation_fin_three_condExp_and_exists_covariance_sum_neg :
    (∀ (Ω : Type u) (m mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ],
      m ≤ mΩ → ∀ f : Fin 3 → Ω → ℝ, (∀ i, Measurable (f i)) →
      (∀ i, ∃ C, ∀ ω, |f i ω| ≤ C) →
      higherCorrelation μ univ f =
        ∫ ω, (2 * (μ[f 0 * f 1 * f 2 | m]) ω -
            ((μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω + (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω +
              (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω) +
            (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω) ∂μ +
          higherCorrelation μ univ (fun i ↦ μ[f i | m]) +
          (cov[μ[f 0 * f 1 | m] - μ[f 0 | m] * μ[f 1 | m], μ[f 2 | m]; μ] +
            cov[μ[f 0 * f 2 | m] - μ[f 0 | m] * μ[f 2 | m], μ[f 1 | m]; μ] +
            cov[μ[f 1 * f 2 | m] - μ[f 1 | m] * μ[f 2 | m], μ[f 0 | m]; μ])) ∧
    (∃ f : Fin 3 → Bool × Bool → ℝ, (∀ i, 0 ≤ f i) ∧ (∀ i, Monotone (f i)) ∧
      cov[condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0 * f 1) -
            condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0) *
              condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1),
          condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 2);
          Measure.uniformOfFinset univ] +
        cov[condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0 * f 2) -
            condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0) *
              condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 2),
          condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1);
          Measure.uniformOfFinset univ] +
        cov[condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1 * f 2) -
            condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1) *
              condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 2),
          condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0);
          Measure.uniformOfFinset univ] < 0) :=
  ⟨fun _ _ _ _ _ hm f hf hb ↦ higherCorrelation_fin_three_eq_condExp hm f hf hb,
    exists_covariance_sum_neg_fairBits⟩

end PercLib
