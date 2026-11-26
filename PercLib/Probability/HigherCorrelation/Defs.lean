/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Higher-order correlations of finitely many real functions. New for this project against
pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied.
Mathematical reference: D. St. P. Richards, *Algebraic methods toward higher-order probability
inequalities, II*, Ann. Probab. 32 (2004); E. H. Lieb and S. Sahi, *On the extension of the
FKG inequality to n functions*, J. Math. Phys. 63 (2022).
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Grade

/-!
# Higher-order correlations

For real functions `f i` (`i ∈ s`) on a measure space, the higher correlation is the sum over
the partitions `π` of `s`
`E_s(f) = ∑_π (-1)^{|π| - 1} ∏_{B ∈ π} (|B| - 1)! ∫ ∏_{i ∈ B} f i dμ`.
For `s = {1, …, n}` this is the correlation `E_n(f_1, …, f_n)`: the expectation for `n = 1`,
the covariance for `n = 2`. It is symmetric in the functions because it is indexed by a finset.
No integrability is built in: the integral is mathlib's Bochner integral.

## Main definitions

* `PercLib.higherCorrelation μ s f`: the higher correlation of the functions `f i`, `i ∈ s`.

## Main results

* `PercLib.higherCorrelation_singleton`: for one function it is the integral.
* `PercLib.higherCorrelation_congr`: it depends only on the functions indexed by `s`.
-/

@[expose] public section

open MeasureTheory Finset

namespace PercLib

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

/-- The higher correlation of the real functions `f i`, `i ∈ s`, under `μ`:
`∑_π (-1)^{|π| - 1} ∏_{B ∈ π} (|B| - 1)! ∫ ∏_{i ∈ B} f i dμ`, summed over the partitions `π` of
`s`. With `s = univ` in `Fin n` this is `E_n(f_0, …, f_{n-1})`. -/
noncomputable def higherCorrelation (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ) : ℝ :=
  ∑ P : Finpartition s, (-1 : ℝ) ^ (#P.parts - 1) *
    ∏ B ∈ P.parts, (((#B - 1).factorial : ℝ) * ∫ ω, ∏ i ∈ B, f i ω ∂μ)

theorem higherCorrelation_def (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    higherCorrelation μ s f = ∑ P : Finpartition s, (-1 : ℝ) ^ (#P.parts - 1) *
      ∏ B ∈ P.parts, (((#B - 1).factorial : ℝ) * ∫ ω, ∏ i ∈ B, f i ω ∂μ) := rfl

/-- The higher correlation depends only on the functions indexed by `s`. -/
theorem higherCorrelation_congr (μ : Measure Ω) {s : Finset ι} {f g : ι → Ω → ℝ}
    (h : ∀ i ∈ s, f i = g i) : higherCorrelation μ s f = higherCorrelation μ s g := by
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  refine congrArg _ (Finset.prod_congr rfl fun B hB ↦ ?_)
  refine congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_))
  exact Finset.prod_congr rfl fun i hi ↦ by rw [h i (P.le hB hi)]

/-- The higher correlation of a single function is its integral. -/
@[simp]
theorem higherCorrelation_singleton (μ : Measure Ω) (i : ι) (f : ι → Ω → ℝ) :
    higherCorrelation μ {i} f = ∫ ω, f i ω ∂μ := by
  let _ : Unique (Finpartition ({i} : Finset ι)) := (isAtom_singleton i).uniqueFinpartition
    (P := .indiscrete (singleton_ne_empty i))
  rw [higherCorrelation, Fintype.sum_unique]
  change (-1 : ℝ) ^ (#({{i}} : Finset (Finset ι)) - 1) *
    ∏ B ∈ ({{i}} : Finset (Finset ι)), (((#B - 1).factorial : ℝ) * ∫ ω, ∏ i ∈ B, f i ω ∂μ) = _
  simp

end PercLib
