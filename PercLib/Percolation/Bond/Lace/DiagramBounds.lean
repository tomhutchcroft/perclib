/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original proofs on the D-2 bond interface. The three diagonal contributions are
retained exactly; no estimate from the literature is assumed.
-/
module

public import PercLib.Percolation.Bond.Lace.DoubleConnection
public import PercLib.Percolation.Bond.Lace.DistinctTriangle
public import PercLib.Percolation.Bond.ConnectionKernel

/-!
# Zeroth lace coefficient: diagram bounds with the diagonal retained

The triangle has three copies of the off-diagonal bubble, not just one.
The remaining contribution is the sum over three distinct vertices. Consequently
`1 + 3 * ∑' y, piZero q x y` is bounded by the diagonal part. A triple BK
estimate bounds one more copy by the distinct-vertex part, giving coefficient four.
The complete three-vertex graph attains this bound; see `Sharpness.lean`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Removing the root term from the bubble loses exactly one. -/
theorem tsum_tau_sq_eq_one_add_offDiagonal (q : Sym2 V → unitInterval) (x : V) :
    ∑' y, tau q x y ^ 2 = 1 + ∑' y, if y = x then 0 else tau q x y ^ 2 := by
  rw [ENNReal.tsum_eq_add_tsum_ite x, tau_self, one_pow]

/-- Exact decomposition into the root, three off-diagonal bubbles, and triangles
whose vertices are all distinct. No finiteness assumption or subtraction is used. -/
theorem triangle_eq_one_add_three_mul_offDiagonal_add
    (q : Sym2 V → unitInterval) (x : V) :
    ∑' u, ∑' v, tau q x u * tau q u v * tau q v x =
      1 + 3 * (∑' y, if y = x then 0 else tau q x y ^ 2) +
        ∑' u, ∑' v, if u = x ∨ v = x ∨ u = v then 0
          else tau q x u * tau q u v * tau q v x := by
  have hrow (u : V) (hu : u ≠ x) :
      ∑' v, tau q x u * tau q u v * tau q v x =
        2 * tau q x u ^ 2 + ∑' v, if v = x ∨ u = v then 0
          else tau q x u * tau q u v * tau q v x := by
    rw [ENNReal.tsum_eq_add_tsum_ite x]
    rw [ENNReal.tsum_eq_add_tsum_ite u]
    simp only [tau_self, mul_one, hu, ite_false]
    rw [tau_comm q u x]
    have htail : (∑' v, if v = u then 0 else
        if v = x then 0 else tau q x u * tau q u v * tau q v x) =
        ∑' v, if v = x ∨ u = v then 0 else
          tau q x u * tau q u v * tau q v x := by
      apply tsum_congr
      intro v
      by_cases hvx : v = x <;> by_cases huv : u = v <;>
        simp [hvx, huv, eq_comm]
    rw [htail]
    ring
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  have hroot : (∑' v, tau q x x * tau q x v * tau q v x) =
      1 + ∑' v, if v = x then 0 else tau q x v ^ 2 := by
    simp only [tau_self, one_mul]
    simp_rw [tau_comm q _ x, ← sq]
    exact tsum_tau_sq_eq_one_add_offDiagonal q x
  rw [hroot]
  have hrest : (∑' u, if u = x then 0 else
        ∑' v, tau q x u * tau q u v * tau q v x) =
      2 * (∑' u, if u = x then 0 else tau q x u ^ 2) +
        ∑' u, ∑' v, if u = x ∨ v = x ∨ u = v then 0 else
          tau q x u * tau q u v * tau q v x := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro u
    by_cases hu : u = x
    · simp [hu]
    · simpa only [hu, ite_false, false_or] using hrow u hu
  rw [hrest]
  ring

/-- The triangle controls three copies of the off-diagonal bubble. -/
theorem one_add_three_mul_offDiagonal_le_triangle
    (q : Sym2 V → unitInterval) (x : V) :
    1 + 3 * (∑' y, if y = x then 0 else tau q x y ^ 2) ≤
      ∑' u, ∑' v, tau q x u * tau q u v * tau q v x := by
  rw [triangle_eq_one_add_three_mul_offDiagonal_add]
  exact le_self_add

/-- The zeroth coefficient has no diagonal contribution to its bubble bound. -/
theorem tsum_piZero_le_offDiagonal [Countable V]
    (q : Sym2 V → unitInterval) (x : V) :
    ∑' y, piZero q x y ≤ ∑' y, if y = x then 0 else tau q x y ^ 2 := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y = x
  · simp [hy, piZero_self]
  · simpa only [hy, ite_false] using piZero_le_tau_sq q x y

/-- The unit mass and the zeroth coefficient are bounded by the full bubble. -/
theorem one_add_tsum_piZero_le_bubble [Countable V]
    (q : Sym2 V → unitInterval) (x : V) :
    1 + ∑' y, piZero q x y ≤ ∑' y, tau q x y ^ 2 := by
  rw [tsum_tau_sq_eq_one_add_offDiagonal]
  exact add_le_add le_rfl (tsum_piZero_le_offDiagonal q x)

/-- Retaining all three diagonal parts improves the coefficient mass bound by a
factor of three compared with simply bounding the bubble by the triangle. -/
theorem one_add_three_mul_tsum_piZero_le_triangle [Countable V]
    (q : Sym2 V → unitInterval) (x : V) :
    1 + 3 * (∑' y, piZero q x y) ≤
      ∑' u, ∑' v, tau q x u * tau q u v * tau q v x := by
  exact (add_le_add le_rfl
    (mul_le_mul' le_rfl (tsum_piZero_le_offDiagonal q x))).trans
      (one_add_three_mul_offDiagonal_le_triangle q x)

/-- Optimal universal coefficient: the three diagonal bubble contributions and
the distinct-vertex triangle contribution each control the zeroth coefficient.
The fully open three-vertex graph attains equality, as proved in `Sharpness.lean`. -/
@[tag "RCHH"]
theorem one_add_four_mul_tsum_piZero_le_triangle [Countable V]
    (q : Sym2 V → unitInterval) (x : V) :
    1 + 4 * (∑' y, piZero q x y) ≤
      ∑' u, ∑' v, tau q x u * tau q u v * tau q v x := by
  rw [triangle_eq_one_add_three_mul_offDiagonal_add]
  calc
    1 + 4 * (∑' y, piZero q x y) =
        (1 + 3 * (∑' y, piZero q x y)) + ∑' y, piZero q x y := by ring
    _ ≤ (1 + 3 * (∑' y, if y = x then 0 else tau q x y ^ 2)) +
        ∑' u, ∑' v, if u = x ∨ v = x ∨ u = v then 0 else
          tau q x u * tau q u v * tau q v x :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul' le_rfl (tsum_piZero_le_offDiagonal q x)))
        (tsum_piZero_le_distinct_triangle q x)

/-- A finite rooted triangle gives a finite total zeroth coefficient. -/
theorem tsum_piZero_lt_top_of_triangle_lt_top [Countable V]
    (q : Sym2 V → unitInterval) (x : V)
    (h : ∑' u, ∑' v, tau q x u * tau q u v * tau q v x < ⊤) :
    ∑' y, piZero q x y < ⊤ := by
  have hb := (one_add_tsum_piZero_le_bubble q x).trans
    (tsum_tau_sq_le_triangle q x)
  exact (le_add_self.trans hb).trans_lt h

/-- The real zeroth coefficient is absolutely summable under a finite triangle. -/
theorem summable_piZero_toReal_of_triangle_lt_top [Countable V]
    (q : Sym2 V → unitInterval) (x : V)
    (h : ∑' u, ∑' v, tau q x u * tau q u v * tau q v x < ⊤) :
    Summable (fun y => (piZero q x y).toReal) :=
  ENNReal.summable_toReal (tsum_piZero_lt_top_of_triangle_lt_top q x h).ne

end PercLib.Percolation.Bond.Lace
