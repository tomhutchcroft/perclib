/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions and proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborGeometry

/-!
# The normalized nearest-neighbour intensity family

## Main results

`nearestNeighborIntensity d` assigns rate `1/(2d)` to every lattice edge and
zero elsewhere. `nearestNeighborProbability d beta` is the resulting edge
probability. Their canonical intensity profile equals the existing homogeneous
lattice profile, providing the parameter conversion for the critical bootstrap.
In dimension zero both the rate and the edge probability vanish.
-/

@[expose] public section
noncomputable section

open PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

open Classical in
/-- The nearest-neighbour rate normalized to total incident rate one in
positive dimension; the zero-dimensional graph has no edges. -/
def nearestNeighborIntensity (d : ℕ) : Sym2 (Fin d → ℤ) → ℝ≥0 :=
  fun e => if e ∈ (zdGraph d).edgeSet then (2 * (d : ℝ≥0))⁻¹ else 0

/-- The open-edge probability at normalized lattice intensity `beta`, obtained
from the canonical intensity-to-probability conversion. -/
def nearestNeighborProbability (d : ℕ) (β : ℝ≥0) : unitInterval :=
  intensityProfile (fun _ : Sym2 Unit => (2 * (d : ℝ≥0))⁻¹) β s((), ())

open Classical in
theorem nearestNeighborIntensity_apply (d : ℕ) (e : Sym2 (Fin d → ℤ)) :
    nearestNeighborIntensity d e =
      if e ∈ (zdGraph d).edgeSet then (2 * (d : ℝ≥0))⁻¹ else 0 := rfl

@[simp] theorem nearestNeighborIntensity_of_mem {d : ℕ} {e : Sym2 (Fin d → ℤ)}
    (he : e ∈ (zdGraph d).edgeSet) :
    nearestNeighborIntensity d e = (2 * (d : ℝ≥0))⁻¹ := by
  simp [nearestNeighborIntensity, he]

@[simp] theorem nearestNeighborIntensity_of_notMem {d : ℕ} {e : Sym2 (Fin d → ℤ)}
    (he : e ∉ (zdGraph d).edgeSet) : nearestNeighborIntensity d e = 0 := by
  simp [nearestNeighborIntensity, he]

@[simp] theorem nearestNeighborIntensity_self (d : ℕ) (x : Fin d → ℤ) :
    nearestNeighborIntensity d s(x, x) = 0 := by
  simp [nearestNeighborIntensity]

@[simp] theorem nearestNeighborIntensity_zero : nearestNeighborIntensity 0 = fun _ => 0 := by
  funext e
  simp [nearestNeighborIntensity]

/-- The exact probability conversion uses normalized intensity, not edge probability. -/
theorem nearestNeighborProbability_coe (d : ℕ) (β : ℝ≥0) :
    (nearestNeighborProbability d β : ℝ) = 1 - Real.exp (-(β : ℝ) / (2 * d)) := by
  simp [nearestNeighborProbability, intensityProfile, div_eq_mul_inv]

@[simp] theorem nearestNeighborProbability_zero (d : ℕ) :
    nearestNeighborProbability d 0 = 0 := by
  apply Subtype.ext
  simp [nearestNeighborProbability_coe]

@[simp] theorem nearestNeighborProbability_dimension_zero (β : ℝ≥0) :
    nearestNeighborProbability 0 β = 0 := by
  apply Subtype.ext
  simp [nearestNeighborProbability_coe]

/-- Every finite normalized intensity has edge probability strictly less than one. -/
theorem nearestNeighborProbability_lt_one (d : ℕ) (β : ℝ≥0) :
    nearestNeighborProbability d β < 1 := by
  change (nearestNeighborProbability d β : ℝ) < 1
  rw [nearestNeighborProbability_coe]
  linarith [Real.exp_pos (-(β : ℝ) / (2 * d))]

/-- The lattice edge probability is monotone in intensity. -/
theorem nearestNeighborProbability_mono (d : ℕ) : Monotone (nearestNeighborProbability d) := by
  intro a b hab
  exact intensityProfile_mono _ hab _

/-- The normalized canonical intensity family is exactly homogeneous lattice percolation. -/
theorem intensityProfile_nearestNeighborIntensity (d : ℕ) (β : ℝ≥0) :
    intensityProfile (nearestNeighborIntensity d) β =
      homogeneousProfile (zdGraph d) (nearestNeighborProbability d β) := by
  classical
  funext e
  apply Subtype.ext
  by_cases he : e ∈ (zdGraph d).edgeSet
  · simp [intensityProfile, nearestNeighborIntensity, homogeneousProfile,
      nearestNeighborProbability, he]
  · simp [intensityProfile, nearestNeighborIntensity, homogeneousProfile, he]

/-- Translation preserves the normalized rate. -/
theorem nearestNeighborIntensity_add (d : ℕ) (x y g : Fin d → ℤ) :
    nearestNeighborIntensity d s(x + g, y + g) = nearestNeighborIntensity d s(x, y) := by
  classical
  have h : (zdGraph d).Adj (x + g) (y + g) ↔ (zdGraph d).Adj x y :=
    zdGraph_adj_iff_of_sub fun i => by simp
  simp only [nearestNeighborIntensity, SimpleGraph.mem_edgeSet, h]

/-- Translations act transitively and preserve the actual normalized rate. -/
theorem nearestNeighborIntensity_transitive (d : ℕ) (x y : Fin d → ℤ) :
    ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ), σ x = y ∧
      ∀ e, nearestNeighborIntensity d (Sym2.map σ e) = nearestNeighborIntensity d e := by
  refine ⟨Equiv.addRight (y - x), by simp, ?_⟩
  intro e
  induction e using Sym2.inductionOn with
  | _ a b => exact nearestNeighborIntensity_add d a b (y - x)

/-- The normalized rate is supported on edges of sup-norm length one. -/
theorem nearestNeighborIntensity_eq_zero_of_one_lt_norm (d : ℕ) (x y : Fin d → ℤ)
    (h : 1 < ‖x - y‖) : nearestNeighborIntensity d s(x, y) = 0 := by
  apply nearestNeighborIntensity_of_notMem
  intro he
  exact (not_le_of_gt h) (norm_sub_le_one_of_zdGraph_adj
    (by simpa only [SimpleGraph.mem_edgeSet] using he))

end PercLib.Percolation.Bond.Lace
