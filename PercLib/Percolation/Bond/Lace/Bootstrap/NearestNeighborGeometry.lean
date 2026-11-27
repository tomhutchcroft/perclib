/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighbor
public import PercLib.Models.DirectionalDecay
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Percolation.Bond.Transport

/-!
# Geometry of the homogeneous lattice profile

## Main results

The actual homogeneous nearest-neighbour bond profile is translation invariant,
has range one in the sup norm, and is transitive. These properties discharge
the geometric hypotheses of the canonical Fourier bootstrap estimates.
-/

@[expose] public section
noncomputable section

open PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

/-- The homogeneous lattice profile is invariant under translations. -/
theorem homogeneous_zdGraph_add {d : ℕ} (p : unitInterval)
    (x y g : Fin d → ℤ) :
    homogeneousProfile (zdGraph d) p s(x + g, y + g) =
      homogeneousProfile (zdGraph d) p s(x, y) := by
  classical
  have h : (zdGraph d).Adj (x + g) (y + g) ↔ (zdGraph d).Adj x y :=
    zdGraph_adj_iff_of_sub fun i => by simp
  simp only [homogeneousProfile, SimpleGraph.mem_edgeSet, h]

/-- An actual nearest-neighbour edge has sup-norm length at most one. -/
theorem norm_sub_le_one_of_zdGraph_adj {d : ℕ} {x y : Fin d → ℤ}
    (h : (zdGraph d).Adj x y) : ‖x - y‖ ≤ 1 := by
  classical
  obtain ⟨⟨i, b⟩, rfl⟩ := (zdGraph_adj_iff_eq_update x y).mp h
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  by_cases hj : j = i
  · subst j
    cases b <;> simp
  · simp [Function.update_of_ne hj]

/-- The actual bond profile vanishes beyond range one. -/
theorem homogeneous_zdGraph_eq_zero_of_one_lt_norm {d : ℕ} (p : unitInterval)
    (x y : Fin d → ℤ) (h : 1 < ‖x - y‖) :
    homogeneousProfile (zdGraph d) p s(x, y) = 0 := by
  apply homogeneousProfile_of_notMem
  intro he
  exact (not_le_of_gt h) (norm_sub_le_one_of_zdGraph_adj
    (by simpa only [SimpleGraph.mem_edgeSet] using he))

/-- Translations supply the actual profile-preserving maps between roots. -/
theorem homogeneous_zdGraph_transitive {d : ℕ} (p : unitInterval)
    (x y : Fin d → ℤ) : ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ),
      σ x = y ∧ ∀ e, homogeneousProfile (zdGraph d) p (Sym2.map σ e) =
        homogeneousProfile (zdGraph d) p e := by
  refine ⟨Equiv.addRight (y - x), by simp, ?_⟩
  intro e
  induction e using Sym2.inductionOn with
  | _ a b => exact homogeneous_zdGraph_add p a b (y - x)

/-- Reflection preserves the actual rooted two-point function. -/
theorem tau_homogeneous_zdGraph_neg {d : ℕ} (p : unitInterval) (z : Fin d → ℤ) :
    tau (homogeneousProfile (zdGraph d) p) 0 (-z) =
      tau (homogeneousProfile (zdGraph d) p) 0 z := by
  classical
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_neg (d := d) (fun _ => true)
  have hzero : φ 0 = 0 := by ext i; simp [hφ]
  have hz : φ z = -z := by ext i; simp [hφ]
  change tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) 0 (-z) =
    tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) 0 z
  simpa only [hzero, hz] using
    tau_map_iso_hostProfile (zdGraph d) p φ 0 z

private theorem tau_homogeneous_zdGraph_update_one {d : ℕ} (p : unitInterval)
    (i j : Fin d) :
    tau (homogeneousProfile (zdGraph d) p) 0 (Function.update (0 : Fin d → ℤ) i 1) =
      tau (homogeneousProfile (zdGraph d) p) 0 (Function.update (0 : Fin d → ℤ) j 1) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_perm (Equiv.swap i j)
  have hzero : φ 0 = 0 := by simp [hφ]
  have hz : φ (Function.update (0 : Fin d → ℤ) i 1) = Function.update (0 : Fin d → ℤ) j 1 := by
    rw [hφ]
    simpa using Function.update_comp_eq_of_injective (0 : Fin d → ℤ)
      (Equiv.swap i j).injective j (1 : ℤ)
  exact (show tau (homogeneousProfile (zdGraph d) p) 0 (Function.update (0 : Fin d → ℤ) j 1) =
      tau (homogeneousProfile (zdGraph d) p) 0 (Function.update (0 : Fin d → ℤ) i 1) by
    change tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) 0
      (Function.update (0 : Fin d → ℤ) j 1) =
      tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) 0
        (Function.update (0 : Fin d → ℤ) i 1)
    simpa only [hzero, hz] using
      tau_map_iso_hostProfile (zdGraph d) p φ 0 (Function.update (0 : Fin d → ℤ) i 1)).symm

/-- All actual nearest-neighbour two-point values agree by lattice symmetries. -/
theorem tau_homogeneous_zdGraph_eq_of_neighbors {d : ℕ} (p : unitInterval)
    {e z : Fin d → ℤ} (he : (zdGraph d).Adj 0 e) (hz : (zdGraph d).Adj 0 z) :
    tau (homogeneousProfile (zdGraph d) p) 0 e =
      tau (homogeneousProfile (zdGraph d) p) 0 z := by
  classical
  obtain ⟨⟨i, b⟩, rfl⟩ := (zdGraph_adj_iff_eq_update 0 e).mp he
  obtain ⟨⟨j, c⟩, rfl⟩ := (zdGraph_adj_iff_eq_update 0 z).mp hz
  have hn (a : Fin d) :
      tau (homogeneousProfile (zdGraph d) p) 0 (Function.update (0 : Fin d → ℤ) a (-1)) =
        tau (homogeneousProfile (zdGraph d) p) 0 (Function.update (0 : Fin d → ℤ) a 1) := by
    have hu : Function.update (0 : Fin d → ℤ) a (-1) =
        -(Function.update (0 : Fin d → ℤ) a 1) := by
      ext k
      by_cases h : k = a <;> simp [h]
    rw [hu]
    exact tau_homogeneous_zdGraph_neg p _
  cases b <;> cases c <;>
    simpa only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Pi.zero_apply, zero_add, hn]
      using tau_homogeneous_zdGraph_update_one p i j

/-- The actual homogeneous nearest-neighbour step kernel is summable. -/
theorem summable_homogeneous_zdGraph {d : ℕ} (p : unitInterval) :
    Summable (fun z : Fin d → ℤ =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)) := by
  classical
  apply summable_of_ne_finset_zero (s := (zdGraph_finite_neighborSet (0 : Fin d → ℤ)).toFinset)
  intro z hz
  have hn : s((0 : Fin d → ℤ), z) ∉ (zdGraph d).edgeSet := by
    simpa only [Set.Finite.mem_toFinset, SimpleGraph.mem_neighborSet,
      SimpleGraph.mem_edgeSet] using hz
  simp [homogeneousProfile_of_notMem p hn]

/-- The actual off-diagonal row mass is exactly `2 d p`, including dimension zero. -/
theorem rowSum_homogeneous_zdGraph {d : ℕ} (p : unitInterval) :
    rowSum (fun e => unitInterval.toENNReal (homogeneousProfile (zdGraph d) p e)) 0 =
      ENNReal.ofReal (2 * d * (p : ℝ)) := by
  classical
  have hsum : (∑' z : Fin d → ℤ,
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)) = 2 * d * (p : ℝ) := by
    have h := tsum_homogeneous_zdGraph_mul (d := d) p (fun _ => 1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [rowSum_def]
  have hpoint (z : Fin d → ℤ) :
      (if z = 0 then 0 else unitInterval.toENNReal
        (homogeneousProfile (zdGraph d) p s(0, z))) =
      ENNReal.ofReal (homogeneousProfile (zdGraph d) p s(0, z) : ℝ) := by
    by_cases hz : z = 0
    · subst z
      simp [homogeneousProfile]
    · simp only [hz, ↓reduceIte, unitInterval.toENNReal_apply,
        ← unitInterval.coe_toNNReal, ENNReal.ofReal_coe_nnreal]
  simp_rw [hpoint]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z =>
    (homogeneousProfile (zdGraph d) p s(0, z)).2.1) (summable_homogeneous_zdGraph p), hsum]

/-- The finite neighbour set makes the actual step row finite at every probability. -/
theorem rowSum_homogeneous_zdGraph_ne_top {d : ℕ} (p : unitInterval) :
    rowSum (fun e => unitInterval.toENNReal (homogeneousProfile (zdGraph d) p e)) 0 ≠ ⊤ := by
  rw [rowSum_homogeneous_zdGraph]
  exact ENNReal.ofReal_ne_top

/-- The actual nearest-neighbour off-diagonal step is its nonnegative real embedding. -/
theorem nn_offDiagonal_eq {d : ℕ} (p : unitInterval) (z : Fin d → ℤ) :
    offDiagonal (fun x y : Fin d → ℤ =>
      (unitInterval.toNNReal (homogeneousProfile (zdGraph d) p s(x, y)) : ℝ≥0∞)) 0 z =
      ENNReal.ofReal (homogeneousProfile (zdGraph d) p s(0, z) : ℝ) := by
  classical
  by_cases hz : z = 0
  · subst z
    simp [homogeneousProfile]
  · simp only [offDiagonal_apply, hz, ↓reduceIte,
      ← unitInterval.coe_toNNReal, ENNReal.ofReal_coe_nnreal]

/-- The nearest-neighbour off-diagonal step has finite total mass. -/
theorem nn_step_mass_ne_top {d : ℕ} (p : unitInterval) :
    (∑' z : Fin d → ℤ, offDiagonal (fun x y : Fin d → ℤ =>
      (unitInterval.toNNReal (homogeneousProfile (zdGraph d) p s(x, y)) : ℝ≥0∞)) 0 z) ≠ ⊤ := by
  simp_rw [nn_offDiagonal_eq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z =>
    (homogeneousProfile (zdGraph d) p s(0, z)).2.1) (summable_homogeneous_zdGraph p)]
  exact ENNReal.ofReal_ne_top

/-- Real projection of the actual off-diagonal step recovers the homogeneous profile. -/
theorem nn_offDiagonal_toReal {d : ℕ} (p : unitInterval) (z : Fin d → ℤ) :
    (offDiagonal (fun x y : Fin d → ℤ =>
      (unitInterval.toNNReal (homogeneousProfile (zdGraph d) p s(x, y)) : ℝ≥0∞)) 0 z).toReal =
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ) := by
  rw [nn_offDiagonal_eq, ENNReal.toReal_ofReal (homogeneousProfile (zdGraph d) p s(0, z)).2.1]

end PercLib.Percolation.Bond.Lace
