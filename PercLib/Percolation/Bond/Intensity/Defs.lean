/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
PercLib intensity interface on the bond interface of `PercLib.Percolation.Bond.Basic`. New
definitions using mathlib's real exponential and complete-lattice infimum; no upstream probability
foundation is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Finite intensities and extended-valued thresholds

The parameter and pair intensities are finite nonnegative numbers. Only the
thresholds are extended-valued. Loops are discarded by the existing open graph;
no diagonal restriction is imposed on the intensity. A threshold is an infimum
of parameters giving positive probability of an infinite cluster, not a
susceptibility threshold. The infimum of the empty set is infinity.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The canonical bond profile at finite intensity beta. -/
def intensityProfile (J : Sym2 V → ℝ≥0) (β : ℝ≥0) : Sym2 V → unitInterval :=
  fun e => ⟨1 - Real.exp (-(β : ℝ) * (J e : ℝ)), by
    constructor
    · apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr β.coe_nonneg) (J e).coe_nonneg
    · exact sub_le_self _ (Real.exp_pos _).le⟩

/-- Infimum of finite parameters giving a positive probability of an infinite
cluster at the specified root. No percolation assertion at the infimum is implied. -/
@[tag "8DAH"]
def rootCriticalIntensity (J : Sym2 V → ℝ≥0) (x : V) : ℝ≥0∞ :=
  sInf {b | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧
    0 < law (intensityProfile J β) {ω | (cluster ω x).Infinite}}

/-- Infimum of finite parameters giving a positive probability that some infinite
cluster exists. This need not equal the threshold at an arbitrary root. -/
def globalCriticalIntensity (J : Sym2 V → ℝ≥0) : ℝ≥0∞ :=
  sInf {b | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧
    0 < law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite}}

open Classical in
/-- The boundary susceptibility of a finite set `S` at intensity `β`:
`Φ_β(S) = ∑_{v ∈ S} ∑_{z ∉ S} J(v, z) χ_{Sᶜ}(z)`, where
`χ_{Sᶜ}(z) = ∑_w P_β(z ↔ w inside Sᶜ)` is the expected size of the cluster of `z` inside the
complement of `S`. It is real-valued; every series is a real `tsum`, so a series that does
not converge contributes `0`. -/
def boundarySusceptibility (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (S : Finset V) : ℝ :=
  ∑ v ∈ S, ∑' z, (if z ∈ S then 0 else (J s(v, z) : ℝ)) *
    ∑' w, (law (intensityProfile J β)).real (localConn (↑S)ᶜ z w)

open Classical in
theorem boundarySusceptibility_def (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (S : Finset V) :
    boundarySusceptibility J β S = ∑ v ∈ S, ∑' z, (if z ∈ S then 0 else (J s(v, z) : ℝ)) *
      ∑' w, (law (intensityProfile J β)).real (localConn (↑S)ᶜ z w) :=
  rfl

/-- Unfolding `boundarySusceptibility`, for any decidability instance on `V`. -/
theorem boundarySusceptibility_eq [DecidableEq V] (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (S : Finset V) :
    boundarySusceptibility J β S = ∑ v ∈ S, ∑' z, (if z ∈ S then 0 else (J s(v, z) : ℝ)) *
      ∑' w, (law (intensityProfile J β)).real (localConn (↑S)ᶜ z w) := by
  simp only [boundarySusceptibility]
  exact Finset.sum_congr rfl fun v _ => tsum_congr fun z => by congr

theorem boundarySusceptibility_nonneg (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (S : Finset V) :
    0 ≤ boundarySusceptibility J β S := by
  classical
  rw [boundarySusceptibility_eq]
  refine Finset.sum_nonneg fun v _ => tsum_nonneg fun z => mul_nonneg ?_
    (tsum_nonneg fun w => measureReal_nonneg)
  split_ifs
  · exact le_rfl
  · exact (J s(v, z)).coe_nonneg

@[simp]
theorem boundarySusceptibility_empty (J : Sym2 V → ℝ≥0) (β : ℝ≥0) :
    boundarySusceptibility J β ∅ = 0 :=
  Finset.sum_empty


/-- On two vertices with unit weight, the boundary susceptibility of one vertex is `1`: the
definition is not identically zero. -/
example (β : ℝ≥0) : boundarySusceptibility (fun _ : Sym2 Bool => 1) β {false} = 1 := by
  have hS : ((({false} : Finset Bool) : Set Bool)ᶜ) = {true} := by ext b; cases b <;> simp
  rw [boundarySusceptibility_eq, Finset.sum_singleton, tsum_fintype, Fintype.sum_bool]
  simp only [Finset.mem_singleton, Bool.true_eq_false, ite_false, ite_true, zero_mul, add_zero,
    NNReal.coe_one, one_mul, hS, tsum_fintype, Fintype.sum_bool]
  rw [localConn_self (Set.mem_singleton true),
    localConn_of_notMem_right (by simp : (false : Bool) ∉ ({true} : Set Bool)),
    probReal_univ, measureReal_empty, add_zero]

-- Finite parameters, including beta = 0, inhabit the interface with nonzero J.
example : Sym2 Unit → unitInterval := intensityProfile (fun _ => 1) 0
example : ℝ≥0∞ := rootCriticalIntensity (fun _ : Sym2 Unit => 1) ()
example : ℝ≥0∞ := globalCriticalIntensity (fun _ : Sym2 Empty => 1)

end PercLib.Percolation.Bond
