/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.ThetaDiagram
public import PercLib.Percolation.Bond.TriangleComparison
public import PercLib.Percolation.Bond.TripleClusterContractions

/-!
# Triangle control of the actual third cluster moment

## Main results

For a translation-invariant lattice profile with finite susceptibility, the
connection-weighted third cluster moment is at most three times susceptibility
times the square of the actual triangle diagram. The coefficient three counts
the three proved four-point tree pairings; the theta comparison has coefficient one.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The actual third weighted cluster moment is at most `3 * chi * Delta²`.
Only subcritical finite susceptibility and profile translation invariance are used. -/
theorem lintegral_cluster_triple_tau_le_three_chi_triangle_sq
    (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ x y g : Fin d → ℤ, q s(x + g, y + g) = q s(x, y))
    (hchi : chi q 0 ≠ ⊤) :
    (∫⁻ ω, ∑' a, ∑' b, ∑' c,
      (conn 0 a ∩ (conn 0 b ∩ conn 0 c)).indicator
        (fun _ => tau q a b * tau q a c) ω ∂law q) ≤
      3 * chi q 0 * (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ^ 2 := by
  have ht (x y g : Fin d → ℤ) : tau q (x + g) (y + g) = tau q x y := by
    rw [tau_eq_rooted_of_add_right q hq, tau_eq_rooted_of_add_right q hq x y]
    simp only [add_sub_add_right_eq_sub]
  have htrans : ∀ x y : Fin d → ℤ, ∃ σ : (Fin d → ℤ) ≃ (Fin d → ℤ),
      σ x = y ∧ ∀ a b, connProb (law q) (σ a) (σ b) = connProb (law q) a b := by
    intro x y
    refine ⟨Equiv.addRight (y - x), by simp, ?_⟩
    intro a b
    simpa only [connProb_law, Equiv.coe_addRight] using ht a b (y - x)
  have hA := triangle_weighted_le_sq_of_transitive (law q) htrans 0
  simp only [connProb_law] at hA
  have hB := tsum_tau_pair_cube_le_triangle_sq q hq hchi
  refine (lintegral_cluster_triple_tau_le_chi_diagrams q ht).trans ?_
  calc
    _ ≤ chi q 0 *
        ((∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ^ 2 +
          2 * (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ^ 2) :=
      mul_le_mul' le_rfl (add_le_add hB (mul_le_mul' le_rfl hA))
    _ = _ := by ring

end PercLib.Percolation.Bond.Lace
