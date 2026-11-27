/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper, proved from `PercLib/Percolation/Bond/ArmContraction.lean`.
No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ArmContraction

/-!
# Arm contraction on `ℤ^d`: correspondence

Wiki correspondence for the finite-set contraction of the arm probabilities of homogeneous
nearest-neighbour bond percolation on `ℤ^d`, from
`PercLib/Percolation/Bond/ArmContraction.lean`.

## Main results

* `arm_le_boundaryFlux_pow_and_exp`
-/

@[expose] public section
noncomputable section

open PercLib.Models.Site

namespace PercLib.Percolation.Bond

open Classical in
/-- Homogeneous nearest-neighbour bond percolation on `ℤ^d` with `0 < p < 1`; write
`Λ_N = {x : ‖x‖_∞ ≤ N}`, `∂Λ_N = {x : ‖x‖_∞ = N}`, `a_N(p) = P_p(0 ↔ ∂Λ_N)` (so `a_0 = 1`)
and `φ = φ_p(S) = p ∑_{x ∈ S, y ∉ S, |x - y|_1 = 1} P_p(0 ↔_S x)` (the boundary flux of `S`
at `0`). If `S ⊆ Λ_{L-1}` and `0 < φ < 1`, then `a_N(p) ≤ φ^⌊N/L⌋` for every `N ≥ 0`, the
constant `c = (2L)⁻¹ min(-log φ, -log(1 - (1-p)^{2d}))` is positive, and
`a_N(p) ≤ e^{-cN}` for every `N ≥ 1`. -/
@[tag "TVM9"]
theorem arm_le_boundaryFlux_pow_and_exp (d : ℕ) (p : unitInterval) (hp0 : 0 < p)
    (hp1 : p < 1) (L : ℕ) (S : Finset (Fin d → ℤ)) (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1)
    (hφ0 : 0 < (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal)
    (hφ1 : (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal < 1) :
    (∀ N : ℕ, (law (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
        {ω | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b}).toReal ≤
      (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal ^
        (N / L)) ∧
    0 < 1 / (2 * (L : ℝ)) *
      min (-Real.log (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal)
        (-Real.log (1 - (1 - (p : ℝ)) ^ (2 * d))) ∧
    (∀ N : ℕ, 1 ≤ N → (law (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
        {ω | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b}).toReal ≤
      Real.exp (-(1 / (2 * (L : ℝ)) *
        min
          (-Real.log (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal)
          (-Real.log (1 - (1 - (p : ℝ)) ^ (2 * d))) * N))) := by
  obtain ⟨-, hL, hd⟩ := mem_and_one_le_of_boundaryFlux_pos p hS hφ0
  exact ⟨fun N => toReal_law_arm_le_pow p hS hφ0 N, arm_exponent_pos p hp0 hp1 hL hd hφ0 hφ1,
    fun N hN => toReal_law_arm_le_exp p hp0 hp1 hS hφ0 hφ1 hN⟩

end PercLib.Percolation.Bond
