/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original sharpness witnesses for the zeroth lace coefficient.
-/
module

public import PercLib.Percolation.Bond.Lace.DiagramBounds
public import PercLib.Percolation.Bond.CorrelationLength

/-!
# Sharpness on the complete three-vertex graph

## Main results

The all-open triangle has zeroth-coefficient mass two and triangle diagram nine.
It is an equality case for the universal coefficient four.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Three distinct vertices with probability-one bonds are doubly connected. -/
theorem law_doubleConn_one_of_third [Countable V] {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    law (fun _ : Sym2 V => (1 : unitInterval)) (doubleConn x y) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_doubleConn x y)).mp
  have hedge (a b : V) : ∀ᵐ ω ∂law (fun _ : Sym2 V => (1 : unitInterval)),
      s(a, b) ∈ ω := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_mem s(a, b))).mpr
    change prodBernoulli _ _ = 1
    rw [prodBernoulli_setOf_mem]
    rfl
  filter_upwards [hedge x y, hedge x z, hedge z y] with ω hxyω hxzω hzyω
  exact mem_doubleConn_of_triangle hxy hxz hyz hxyω hxzω hzyω

/-- The total zeroth coefficient on the fully open three-vertex graph is two. -/
theorem tsum_piZero_complete_three :
    ∑' y : Fin 3, piZero (fun _ => (1 : unitInterval)) (0 : Fin 3) y = 2 := by
  have h01 : piZero (fun _ => (1 : unitInterval)) (0 : Fin 3) 1 = 1 := by
    rw [piZero_of_ne _ (by decide)]
    exact law_doubleConn_one_of_third (z := (2 : Fin 3))
      (by decide) (by decide) (by decide)
  have h02 : piZero (fun _ => (1 : unitInterval)) (0 : Fin 3) 2 = 1 := by
    rw [piZero_of_ne _ (by decide)]
    exact law_doubleConn_one_of_third (z := (1 : Fin 3))
      (by decide) (by decide) (by decide)
  norm_num [tsum_fintype, Fin.sum_univ_succ, h01, h02]

/-- The rooted triangle on the fully open three-vertex graph is nine. -/
theorem triangle_complete_three :
    ∑' u : Fin 3, ∑' v : Fin 3,
      tau (fun _ => (1 : unitInterval)) 0 u *
        tau (fun _ => (1 : unitInterval)) u v *
        tau (fun _ => (1 : unitInterval)) v 0 = 9 := by
  simp [tau_one_eq_one, tsum_fintype]
  norm_num

/-- The coefficient four is attained with positive zeroth-coefficient mass. -/
theorem complete_three_attains_four :
    1 + 4 * (∑' y : Fin 3, piZero (fun _ => (1 : unitInterval)) 0 y) =
      ∑' u : Fin 3, ∑' v : Fin 3,
        tau (fun _ => (1 : unitInterval)) 0 u *
          tau (fun _ => (1 : unitInterval)) u v *
          tau (fun _ => (1 : unitInterval)) v 0 := by
  rw [tsum_piZero_complete_three, triangle_complete_three]
  norm_num

/-- Any universal real constant in this coefficient-mass bound is at most four.
It suffices to test the bound on profiles on three vertices. -/
theorem coefficient_le_four_of_universal_bound (c : ℝ)
    (h : ∀ q : Sym2 (Fin 3) → unitInterval,
      1 + c * (∑' y, piZero q 0 y).toReal ≤
        (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0).toReal) : c ≤ 4 := by
  have hc := h (fun _ => 1)
  rw [tsum_piZero_complete_three, triangle_complete_three] at hc
  norm_num at hc
  linarith

end PercLib.Percolation.Bond.Lace
