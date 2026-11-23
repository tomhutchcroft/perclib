/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived definitions for restoration-based window bounds.
These are abbreviations for existing root-monomial expectations and finite range sums, not new
model inputs or alternate probability spaces.
-/
module

public import PercLib.Percolation.Bond.RestorationFibreMajorant

/-!
# Definitions for uniform restoration windows

`rootWeight` is the expected root-monomial mass at one vertex, and `rootMoment` is the root volume
moment. `dilatedRootWeight` sums it over a finite translate. The frozen weights collect the binomial
coefficients and support factors from restoration coupling; `Mt` is intended to bound the root
`p`-th moment. The final definition is the radially truncated unit pair weight.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond


variable {d : ℕ}

open Classical in
/-- The vertex mass of the root `l`-th monomial at the vertex `x`. -/
noncomputable def rootWeight (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (l : ℕ)
    (x : Fin d → ℤ) : ℝ≥0∞ :=
  ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ

open Classical in
/-- The *dilated* vertex mass of the root `l`-th monomial: the sum of `rootWeight` over the finite
range `y + S` of the pair weight.  This is the `y`-orientation weight of the restoration chain, and
it carries no factor at `y` itself. -/
noncomputable def dilatedRootWeight (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (l : ℕ) (y : Fin d → ℤ) : ℝ≥0∞ :=
  ∑ z ∈ S, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
    ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ

/-- The root `m`-th volume moment. -/
noncomputable def rootMoment (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂μ

open Classical in
theorem rootWeight_eq (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (l : ℕ)
    (x : Fin d → ℤ) :
    rootWeight μ o l x = ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ := rfl

theorem rootMoment_eq (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (m : ℕ) :
    rootMoment μ o m = ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂μ := rfl


open Classical in
/-- The `x`-orientation fibre weight of the restoration chain at the top scale `v`, with the range
set `S` and the root moment `Mt` read at `v`, and the pair weight bounded by `1`. -/
noncomputable def topWeightLeft (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (Mt : ℝ≥0∞) (x : Fin d → ℤ) : ℝ≥0∞ :=
  ∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
    ((S.card : ℝ≥0∞) * (1 * (rootWeight μ o l x * Mt)))

open Classical in
/-- The `y`-orientation (dilated) fibre weight of the restoration chain at the top scale `v`. -/
noncomputable def topWeightRight (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (Mt : ℝ≥0∞) (y : Fin d → ℤ) : ℝ≥0∞ :=
  ∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
    ((1 * dilatedRootWeight μ o S l y) * Mt)


/-- The radially truncated unit pair weight `e ↦ 1{N (e) < r}` as a function of the edge.  Giving
it a name keeps the `ℝ≥0∞` coercion and the indicator profile out of the statements that only
need the weight as an abstract pair weight. -/
noncomputable def indicatorPairWeight {N : Seminorm ℝ (Fin d → ℝ)} (r : ℝ) :
    Sym2 (Fin d → ℤ) → ℝ≥0∞ :=
  fun e => (PercLib.Models.LongRange.radialKernel N
    (fun s => if s < r then 1 else 0) e : ℝ≥0∞)


end PercLib.Percolation.Bond
