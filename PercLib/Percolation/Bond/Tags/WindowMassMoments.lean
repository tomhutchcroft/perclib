/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the moments of the total squared cluster mass. All mathematical
inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.WindowMassMoments

/-!
# Moments of the total squared cluster mass: correspondence

Wiki correspondence for the polynomial moments of `∑_C |C|²` under a uniform susceptibility
bound.

## Main results

* `sum_component_sq_moments_le`
-/

@[expose] public section
noncomputable section
open MeasureTheory Finset
open scoped ENNReal Nat

namespace PercLib.Percolation.Bond

universe u

/-- A uniform susceptibility bound controls every polynomial moment of the total squared
cluster mass. For independent bond percolation on a finite vertex set with `N` vertices and
`M = ⨆ v, E|C_v|`, and every integer `m ≥ 1`,
`E (∑_C |C|²)^m ≤ ∑_{π ∈ 𝒫_m} N^{|π|} M^{4m-3|π|} ∏_{B ∈ π} (4|B|-5)‼`
(with `(4·1-5)‼ = 0‼ = 1` in `ℕ`). Consequently, for every `K` and every real `r > 0` there
is a finite `C` with `E (N^{-4/3} ∑_C |C|²)^r ≤ C` whenever the vertex set is nonempty and
`M ≤ K N^{1/3}`. -/
@[tag "YN7V"]
theorem sum_component_sq_moments_le :
    (∀ (V : Type u) [Fintype V] (q : Sym2 V → unitInterval) (m : ℕ), 1 ≤ m →
      ∫⁻ ω, ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) ^ m
          ∂law q ≤
        ∑ π : Finpartition (univ : Finset (Fin m)),
          (Fintype.card V : ℝ≥0∞) ^ #π.parts * (⨆ x, chi q x) ^ (4 * m - 3 * #π.parts) *
            ∏ B ∈ π.parts, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞)) ∧
    (∀ (K : NNReal) (r : ℝ), 0 < r →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (V : Type u) [Fintype V] [Nonempty V]
        (q : Sym2 V → unitInterval),
        (⨆ x, chi q x) ≤ K * (Fintype.card V : ℝ≥0∞) ^ (1 / 3 : ℝ) →
        ∫⁻ ω, ((Fintype.card V : ℝ≥0∞) ^ (-(4 / 3 : ℝ)) *
          ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞)) ^ r
            ∂law q ≤ C) :=
  ⟨fun _ _ q m _ => lintegral_sum_component_sq_pow_le q m,
    fun K _ hr => exists_lintegral_normalized_sum_component_sq_rpow_le K hr⟩

end PercLib.Percolation.Bond
