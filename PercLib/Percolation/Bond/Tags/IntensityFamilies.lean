/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the homogeneous and exponential families of bond profiles.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.IntensityFamilies

/-!
# Homogeneous and exponential intensity families: correspondence

## Main results

* `homogeneousProfile_and_intensityProfile_families`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-- Homogeneous bond percolation on a host `G` takes `q(e) = p` on the host edges (and `0` off
the host); on the complete graph on `Fin n` each pair of distinct vertices is open with
probability `p` (the Erdős–Rényi graph). For a finite nonnegative intensity `J` the exponential
family is `q_β(e) = 1 - exp(-β J(e))`, `β ≥ 0`, with parameter derivative `J(e) e^{-β J(e)}`.
A family `p D(e)` is not in general a fixed-`J` exponential family with a renamed parameter. -/
@[tag "A65C"]
theorem homogeneousProfile_and_intensityProfile_families {V : Type*} :
    (∀ (G : SimpleGraph V) (p : unitInterval) (e : Sym2 V),
      e ∈ G.edgeSet → homogeneousProfile G p e = p) ∧
    (∀ (G : SimpleGraph V) (p : unitInterval) (e : Sym2 V),
      e ∉ G.edgeSet → homogeneousProfile G p e = 0) ∧
    (∀ (n : ℕ) (p : unitInterval) (x y : Fin n), x ≠ y →
      law (homogeneousProfile ⊤ p) {ω : Config (Fin n) | (openGraph ω).Adj x y} =
        (unitInterval.toNNReal p : ℝ≥0∞)) ∧
    (∀ (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V),
      (intensityProfile J β e : ℝ) = 1 - Real.exp (-(β : ℝ) * (J e : ℝ))) ∧
    (∀ (J : Sym2 V → ℝ≥0) (e : Sym2 V) (β : ℝ),
      HasDerivAt (fun b : ℝ => 1 - Real.exp (-b * (J e : ℝ)))
        ((J e : ℝ) * Real.exp (-β * (J e : ℝ))) β) ∧
    (∃ D : Sym2 (Fin 3) → unitInterval, ¬ ∃ (J : Sym2 (Fin 3) → ℝ≥0) (φ : unitInterval → ℝ≥0),
      ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ e,
        (intensityProfile J (φ p) e : ℝ) = p * D e) :=
  ⟨fun _ p _ h => homogeneousProfile_of_mem p h,
    fun _ p _ h => homogeneousProfile_of_notMem p h,
    fun _ p _ _ h => law_adj_homogeneousProfile_top p h,
    fun _ _ _ => rfl,
    fun J e β => hasDerivAt_one_sub_exp_neg_mul (J e) β,
    not_exists_intensityProfile_eq_mul⟩

end PercLib.Percolation.Bond
