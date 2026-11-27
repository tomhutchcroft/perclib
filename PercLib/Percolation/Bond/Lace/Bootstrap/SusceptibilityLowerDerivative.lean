/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.BoundaryRusso.Differentiation
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.Lace.Bootstrap.BoundaryExpectation

/-!
# The actual susceptibility derivative under a triangle cap

## Main results

A constant upper bound `D` on the actual triangle gives the almost-everywhere lower
bound `chi' >= (chi - D)₊² / (3 * beta² * D²)` throughout an open interval of finite
susceptibility. The boundary expectation and its derivative identity are proved results;
there is no assumed differential inequality or finiteness at the excluded endpoint.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- Replacing the actual triangle by a larger constant weakens the boundary-expectation
lower bound in the required direction. Intensity zero remains included. -/
theorem tsum_law_cluster_eq_mul_boundarySusceptibility_ge_triangle_cap
    (J : Sym2 (Fin d → ℤ) → ℝ≥0) (β : ℝ≥0)
    (hJ : ∀ x y g : Fin d → ℤ, J s(x + g, y + g) = J s(x, y))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (hchi : chi (intensityProfile J β) 0 ≠ ⊤)
    (D : ℝ) (hD : 1 ≤ D)
    (htriangle : (∑' u, ∑' v, tau (intensityProfile J β) 0 u *
      tau (intensityProfile J β) u v * tau (intensityProfile J β) v 0) ≤ ENNReal.ofReal D) :
    (max ((chi (intensityProfile J β) 0).toReal - D) 0) ^ 2 /
        (3 * (β : ℝ) ^ 2 * D ^ 2) ≤
      ∑' C : Finset (Fin d → ℤ), (law (intensityProfile J β)).real
        {ω | cluster ω 0 = (C : Set (Fin d → ℤ))} * boundarySusceptibility J β C := by
  let q := intensityProfile J β
  let χ := (chi q 0).toReal
  let T := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
  let δ := T.toReal
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hTf : T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top htriangle
  have hδD : δ ≤ D := ENNReal.toReal_le_of_le_ofReal hD0.le htriangle
  have hT1 : (1 : ℝ≥0∞) ≤ T := by
    calc
      1 = tau q 0 0 * tau q 0 0 * tau q 0 0 := by rw [tau_self]; norm_num
      _ ≤ ∑' v, tau q 0 0 * tau q 0 v * tau q v 0 :=
        ENNReal.le_tsum (f := fun v => tau q 0 0 * tau q 0 v * tau q v 0) 0
      _ ≤ T := ENNReal.le_tsum (f := fun u =>
        ∑' v, tau q 0 u * tau q u v * tau q v 0) 0
  have hδ : 0 < δ := zero_lt_one.trans_le (by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hTf hT1)
  refine le_trans ?_ (tsum_law_cluster_eq_mul_boundarySusceptibility_ge_triangle
    J β hJ hrow hchi)
  change max (χ - D) 0 ^ 2 / (3 * (β : ℝ) ^ 2 * D ^ 2) ≤
    max (χ - δ) 0 ^ 2 / (3 * (β : ℝ) ^ 2 * δ ^ 2)
  by_cases hβ : (β : ℝ) = 0
  · simp [hβ]
  have hβ0 : 0 < (β : ℝ) := lt_of_le_of_ne β.coe_nonneg (Ne.symm hβ)
  calc
    _ ≤ max (χ - δ) 0 ^ 2 / (3 * (β : ℝ) ^ 2 * D ^ 2) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (le_max_right _ _)
          (max_le_max (sub_le_sub_left hδD χ) le_rfl) 2) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδD 2) (by positivity))

/-- The actual susceptibility satisfies the triangle-cap lower differential inequality
almost everywhere on every open positive-intensity interval of finite susceptibility.
The upper endpoint need not have finite susceptibility. -/
theorem ae_deriv_chi_ge_triangle_cap
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y g : Fin d → ℤ, J s(x + g, y + g) = J s(x, y))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ t ∈ Ioo a b, chi (intensityProfile J t.toNNReal) 0 ≠ ⊤)
    (D : ℝ) (hD : 1 ≤ D)
    (htriangle : ∀ t ∈ Ioo a b,
      (∑' u, ∑' v, tau (intensityProfile J t.toNNReal) 0 u *
        tau (intensityProfile J t.toNNReal) u v *
        tau (intensityProfile J t.toNNReal) v 0) ≤ ENNReal.ofReal D) :
    ∀ᵐ t, t ∈ Ioo a b →
      (max ((chi (intensityProfile J t.toNNReal) 0).toReal - D) 0) ^ 2 /
          (3 * t ^ 2 * D ^ 2) ≤
        deriv (fun s : ℝ => (chi (intensityProfile J s.toNNReal) 0).toReal) t := by
  have htrans (x y : Fin d → ℤ) : ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ),
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := by
    refine ⟨Equiv.addRight (y - x), by simp, ?_⟩
    intro e
    induction e using Sym2.inductionOn with
    | _ u v => exact hJ u v (y - x)
  have hfinite (t : ℝ) (ht : t ∈ Ioo a b) :
      (⨆ v, chi (intensityProfile J t.toNNReal) v) ≠ ⊤ := by
    have hc (v : Fin d → ℤ) : chi (intensityProfile J t.toNNReal) v =
        chi (intensityProfile J t.toNNReal) 0 := chi_eq_of_transitive J htrans t.toNNReal v 0
    simpa only [hc, iSup_const] using hfin t ht
  filter_upwards [ae_hasDerivAt_chi_boundarySusceptibility J 0 1 hrow ha hfinite]
    with t ht htab
  rw [(ht htab).deriv]
  have h := tsum_law_cluster_eq_mul_boundarySusceptibility_ge_triangle_cap
    J t.toNNReal hJ hrow (hfin t htab) D hD (htriangle t htab)
  simpa only [Real.coe_toNNReal t (ha.trans htab.1.le)] using h

end PercLib.Percolation.Bond.Lace
