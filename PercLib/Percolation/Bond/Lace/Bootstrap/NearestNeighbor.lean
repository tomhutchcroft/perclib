/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.Defs
public import PercLib.Models.Lattice
public import PercLib.Percolation.Bond.Homogeneous.Defs

/-!
# The actual nearest-neighbour bond kernel

## Main results

The homogeneous profile on the existing integer lattice has a finite directional
sum. Its physical cosine transform is its edge mass times the normalized
nearest-neighbour symbol; no auxiliary percolation profile is introduced.
-/

@[expose] public section
noncomputable section

open PercLib.Analysis PercLib.Models.Site

namespace PercLib.Percolation.Bond.Lace

/-- A weighted row of the actual homogeneous lattice profile is a finite sum
of its two coordinate directions. -/
theorem tsum_homogeneous_zdGraph_mul {d : ℕ} (p : unitInterval)
    (f : (Fin d → ℤ) → ℝ) :
    (∑' z, (homogeneousProfile (zdGraph d) p s(0, z) : ℝ) * f z) =
      (p : ℝ) * ∑ a : Fin d × Bool,
        f (Function.update 0 a.1 (if a.2 then 1 else -1)) := by
  classical
  have hs : Function.support (fun z : Fin d → ℤ =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ) * f z) ⊆
      Set.range (fun a : Fin d × Bool =>
        Function.update (0 : Fin d → ℤ) a.1 ((0 : Fin d → ℤ) a.1 + if a.2 then 1 else -1)) := by
    intro z hz
    rw [← zdGraph_neighborSet_eq]
    by_contra hn
    have he : s((0 : Fin d → ℤ), z) ∉ (zdGraph d).edgeSet := by
      simpa only [SimpleGraph.mem_edgeSet, SimpleGraph.mem_neighborSet] using hn
    simp [Function.mem_support, homogeneousProfile_of_notMem p he] at hz
  have h := (injective_update_step (0 : Fin d → ℤ)).tsum_eq hs
  rw [← h, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have ha : s((0 : Fin d → ℤ),
      Function.update 0 a.1 ((0 : Fin d → ℤ) a.1 + if a.2 then 1 else -1)) ∈
        (zdGraph d).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, zdGraph_adj_iff_eq_update]
    exact ⟨a, rfl⟩
  rw [homogeneousProfile_of_mem p ha]
  simp

/-- The actual homogeneous nearest-neighbour bond kernel has Fourier multiplier
`2 d p` times the canonical normalized walk symbol. -/
theorem latticeCosineTransform_homogeneous_zdGraph {d : ℕ} (hd : 0 < d)
    (p : unitInterval) (k : Fin d → ℝ) :
    latticeCosineTransform (fun z => (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)) k =
      (2 * d * (p : ℝ)) * nearestNeighborSymbol k := by
  rw [latticeCosineTransform, tsum_homogeneous_zdGraph_mul]
  simp only [Fintype.sum_prod_type]
  have hdir (i : Fin d) :
      (∑ b : Bool, Real.cos (∑ j, k j *
        ((Function.update (0 : Fin d → ℤ) i (if b then 1 else -1)) j : ℝ))) =
      2 * Real.cos (k i) := by
    simp [Finset.sum_ite_eq', Function.update_apply]
    ring
  simp_rw [hdir]
  rw [← Finset.mul_sum, nearestNeighborSymbol]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

end PercLib.Percolation.Bond.Lace
