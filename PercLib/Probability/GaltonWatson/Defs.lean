/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions, written on 2026-11-22. Reference: K. B. Athreya and P. E. Ney, *Branching
Processes*, Springer, 1972, Chapter I. No upstream code is copied.
-/
module

public import PercLib.Meta.Tag
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # The Galton–Watson process

Fix an offspring law `p : PMF ℕ`. The offspring variables `ξ_{n,j}` (the number of children of
the `j`-th individual of generation `n`) are the coordinates `ω n j` of a point
`ω : ℕ → ℕ → ℕ`, and `galtonWatsonMeasure p` is the product law making them independent with
law `p`. The generation sizes are

`Z₀ = 1`, `Z_{n+1} = ∑_{j < Z_n} ξ_{n,j}`,

so the empty sum makes zero absorbing, and the total progeny is `T = ∑ₙ Zₙ ∈ ℕ ∪ {∞}`
(valued in `ℝ≥0∞`). Each generation is a natural number, so it is finite for every `ω`.

## Main definitions

* `galtonWatsonMeasure p`: the product law of the offspring variables.
* `generationSize n ω`: the generation size `Zₙ`.
* `totalProgeny ω`: the total progeny `T`.

## Main results

* `measurable_generationSize`, `measurable_totalProgeny`.
* `generationSize_eq_zero_of_le`: zero is absorbing.
* `generationSize_congr`: `Zₙ` depends only on the offspring variables of generations `< n`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Probability

/-- The **Galton–Watson product law**: under `galtonWatsonMeasure p` the offspring variables
`ξ_{n,j} = ω n j` are independent with law `p`. -/
def galtonWatsonMeasure (p : PMF ℕ) : Measure (ℕ → ℕ → ℕ) :=
  Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => p.toMeasure

instance (p : PMF ℕ) : IsProbabilityMeasure (galtonWatsonMeasure p) := by
  unfold galtonWatsonMeasure; infer_instance

/-- The **Galton–Watson process** (generation sizes): `Z₀ = 1` and
`Z_{n+1} = ∑_{j < Zₙ} ξ_{n,j}`, where `ξ_{n,j} = ω n j`. -/
@[tag "NCWZ"]
def generationSize : ℕ → (ℕ → ℕ → ℕ) → ℕ
  | 0, _ => 1
  | n + 1, ω => ∑ j ∈ Finset.range (generationSize n ω), ω n j

/-- The **total progeny** `T = ∑ₙ Zₙ ∈ ℕ ∪ {∞}`. -/
def totalProgeny (ω : ℕ → ℕ → ℕ) : ℝ≥0∞ :=
  ∑' n, (generationSize n ω : ℝ≥0∞)

theorem galtonWatsonMeasure_def (p : PMF ℕ) : galtonWatsonMeasure p =
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => p.toMeasure :=
  rfl

@[simp]
theorem generationSize_zero (ω : ℕ → ℕ → ℕ) : generationSize 0 ω = 1 :=
  rfl

@[simp]
theorem generationSize_succ (n : ℕ) (ω : ℕ → ℕ → ℕ) :
    generationSize (n + 1) ω = ∑ j ∈ Finset.range (generationSize n ω), ω n j :=
  rfl

theorem totalProgeny_def (ω : ℕ → ℕ → ℕ) :
    totalProgeny ω = ∑' n, (generationSize n ω : ℝ≥0∞) :=
  rfl

/-- Each generation is at most the total progeny. -/
theorem generationSize_le_totalProgeny (n : ℕ) (ω : ℕ → ℕ → ℕ) :
    (generationSize n ω : ℝ≥0∞) ≤ totalProgeny ω :=
  ENNReal.le_tsum (f := fun n => (generationSize n ω : ℝ≥0∞)) n

/-- The root is counted in the total progeny. -/
theorem one_le_totalProgeny (ω : ℕ → ℕ → ℕ) : 1 ≤ totalProgeny ω := by
  simpa using generationSize_le_totalProgeny 0 ω

/-- **Zero is absorbing.** -/
theorem generationSize_succ_eq_zero {n : ℕ} {ω : ℕ → ℕ → ℕ} (h : generationSize n ω = 0) :
    generationSize (n + 1) ω = 0 := by
  simp [h]

/-- **Zero is absorbing**, at every later generation. -/
theorem generationSize_eq_zero_of_le {m n : ℕ} (hmn : m ≤ n) {ω : ℕ → ℕ → ℕ}
    (h : generationSize m ω = 0) : generationSize n ω = 0 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact generationSize_succ_eq_zero ih

/-- The extinction events `{Zₙ = 0}` increase in `n`. -/
theorem monotone_setOf_generationSize_eq_zero :
    Monotone fun n => {ω : ℕ → ℕ → ℕ | generationSize n ω = 0} :=
  fun _ _ hmn _ h => generationSize_eq_zero_of_le hmn h

/-- `Zₙ` depends only on the offspring variables of the generations before `n`. -/
theorem generationSize_congr {n : ℕ} {ω ω' : ℕ → ℕ → ℕ} (h : ∀ i < n, ω i = ω' i) :
    generationSize n ω = generationSize n ω' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [generationSize_succ, generationSize_succ, ih fun i hi => h i (by omega),
      h n (by omega)]

@[fun_prop]
theorem measurable_generationSize (n : ℕ) : Measurable (generationSize n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    refine measurable_to_countable' fun m => ?_
    have : generationSize (n + 1) ⁻¹' {m} =
        ⋃ k : ℕ, (generationSize n ⁻¹' {k} ∩
          {ω : ℕ → ℕ → ℕ | ∑ j ∈ Finset.range k, ω n j = m}) := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.iUnion fun k => (ih (measurableSet_singleton k)).inter ?_
    exact measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => by fun_prop)
      measurable_const

@[fun_prop]
theorem measurable_totalProgeny : Measurable totalProgeny := by
  unfold totalProgeny
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s => s.measurable_fun_sum fun n _ =>
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp (measurable_generationSize n)

end PercLib.Probability
