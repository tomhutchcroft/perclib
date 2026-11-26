/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the three-vertex counterexample of the boundary-susceptibility
article. All mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.BoundaryCounterexample

/-!
# The three-vertex boundary counterexample: statement form

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `boundary_counterexample_three_path`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-- On the path `0, 1, 2` at `β = 1` with `J(0,1) = 99/100`, `J(1,2) = 1/100`,
`J(0,2) = 0` (diagonal arbitrary) and `S = {0,1}`: `χ_min = 1 + t + pt`, `χ_max = 1 + p + t`,
the two-point sums over `S` give `Q(S) = 2(1+p)^2`, `Φ_1(S) = 1/100`, the unsigned-square
bound exceeds `841/10050`, and so the unsigned boundary bound fails. -/
@[tag "JTBG"]
theorem boundary_counterexample_three_path (J : Sym2 (Fin 3) → ℝ≥0)
    (h01 : J s(0, 1) = 99 / 100) (h12 : J s(1, 2) = 1 / 100) (h02 : J s(0, 2) = 0) :
    ((⨅ u, chi (intensityProfile J 1) u).toReal = 1 + (1 - Real.exp (-(1 / 100))) +
        (1 - Real.exp (-(99 / 100))) * (1 - Real.exp (-(1 / 100))) ∧
      (⨆ u, chi (intensityProfile J 1) u).toReal = 1 + (1 - Real.exp (-(99 / 100))) +
        (1 - Real.exp (-(1 / 100)))) ∧
    (∑ u ∈ ({0, 1} : Finset (Fin 3)), ∑ v ∈ ({0, 1} : Finset (Fin 3)),
        (tau (intensityProfile J 1) u v).toReal = 2 * (1 + (1 - Real.exp (-(99 / 100)))) ∧
      ∑ u ∈ ({0, 1} : Finset (Fin 3)),
          (∑ v ∈ ({0, 1} : Finset (Fin 3)), (tau (intensityProfile J 1) u v).toReal) ^ 2 =
        2 * (1 + (1 - Real.exp (-(99 / 100)))) ^ 2) ∧
    ∑ v ∈ ({0, 1} : Finset (Fin 3)), ∑' z,
        (if z ∈ ({0, 1} : Finset (Fin 3)) then 0 else (J s(v, z) : ℝ)) *
          ∑' w, (law (intensityProfile J 1)).real
            (localConn ((({0, 1} : Finset (Fin 3)) : Set (Fin 3))ᶜ) z w) = 1 / 100 ∧
    (841 / 10050 : ℝ) <
      ((⨅ u, chi (intensityProfile J 1) u).toReal * (({0, 1} : Finset (Fin 3)).card : ℝ) -
          ∑ u ∈ ({0, 1} : Finset (Fin 3)), ∑ v ∈ ({0, 1} : Finset (Fin 3)),
            (tau (intensityProfile J 1) u v).toReal) ^ 2 /
        ((1 : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J 1) u).toReal *
          ∑ u ∈ ({0, 1} : Finset (Fin 3)),
            (∑ v ∈ ({0, 1} : Finset (Fin 3)), (tau (intensityProfile J 1) u v).toReal) ^ 2) ∧
    ¬ (((⨅ u, chi (intensityProfile J 1) u).toReal * (({0, 1} : Finset (Fin 3)).card : ℝ) -
          ∑ u ∈ ({0, 1} : Finset (Fin 3)), ∑ v ∈ ({0, 1} : Finset (Fin 3)),
            (tau (intensityProfile J 1) u v).toReal) ^ 2 /
        ((1 : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J 1) u).toReal *
          ∑ u ∈ ({0, 1} : Finset (Fin 3)),
            (∑ v ∈ ({0, 1} : Finset (Fin 3)), (tau (intensityProfile J 1) u v).toReal) ^ 2) ≤
      ∑ v ∈ ({0, 1} : Finset (Fin 3)), ∑' z,
        (if z ∈ ({0, 1} : Finset (Fin 3)) then 0 else (J s(v, z) : ℝ)) *
          ∑' w, (law (intensityProfile J 1)).real
            (localConn ((({0, 1} : Finset (Fin 3)) : Set (Fin 3))ᶜ) z w)) :=
  ⟨iInf_iSup_chi_three_path h01 h12 h02, sum_tau_pair_three_path h01 h12 h02,
    boundary_functional_three_path h12 h02, unsigned_square_three_path_gt h01 h12 h02,
    not_boundary_bound_unsigned h01 h12 h02⟩

end PercLib.Percolation.Bond
