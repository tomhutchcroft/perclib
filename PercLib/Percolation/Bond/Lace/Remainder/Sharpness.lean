/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original sharpness witnesses for the nonnegative lace remainder; no upstream
proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Bounds
public import PercLib.Percolation.Bond.Lace.FirstDiagramRefined

/-!
# Sharpness of the remainder bound on two vertices

If the only nonloop pair has probability `p`, then the first positive
coefficient on the diagonal is `p²`, its off-diagonal entry is zero, and the
first remainder on the diagonal is `p⁴`. The convolution bound is also `p⁴`.
The repeated oriented pair `(false,true)` supplies the lower bound; repeated
pairs in successive independent layers are permitted by the definitions.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

/-- A two-vertex graph cannot doubly connect its distinct vertices. -/
theorem doubleConn_bool_cross_eq_empty :
    (doubleConn false true : Set (Config Bool)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ω h
  exact Bool.false_ne_true ((bool_deleted_conn ω false true).mp
    (conn_sdiff_singleton_of_mem_doubleConn h s(false, true)))

/-- The first coefficient has no off-diagonal entry on two vertices. -/
theorem laceCoefficient_one_bool_cross (q : Sym2 Bool → unitInterval) :
    laceCoefficient q 1 false true = 0 := by
  unfold laceCoefficient
  apply ENNReal.tsum_eq_zero.mpr
  intro b
  change (∏ i : Fin 1, offDiagonal
    (fun a c : Bool => (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞)) (b i).1 (b i).2) * _ = 0
  rw [Fin.prod_univ_one]
  cases hu : (b 0).1
  · cases hv : (b 0).2
    · simp [offDiagonal]
    · have hevent : coefficientEvent false true b = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro ω h
        have h' := (mem_coefficientEvent_one_iff false true b ω).mp h
        simpa [hu, hv, bool_deleted_cluster] using h'.2
      simp [hevent]
  · have hevent : coefficientEvent false true b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω h
      have hd := ((mem_coefficientEvent_one_iff false true b ω).mp h).1
      simp only [hu, doubleConn_bool_cross_eq_empty, mem_empty_iff_false] at hd
    simp [hevent]

/-- Deleting the sole nonloop pair leaves either root isolated. -/
theorem bool_deleted_cluster_eq_singleton (ω : Config Bool) (x : Bool) :
    cluster (ω \ {s(false, true)}) x = {x} := by
  ext y
  rw [mem_cluster_iff, bool_deleted_conn]
  simp only [mem_singleton_iff, eq_comm]

/-- The repeated directed pair uses one cross connection in each of the last
two layers; its initial double connection is diagonal. -/
theorem repeated_remainderEvent_bool_eq_rect :
    remainderEvent false false (fun _ : Fin 2 => (false, true)) =
      Set.pi univ ![(univ : Set (Config Bool)), conn true false, conn true false] := by
  ext ω
  have hlast (i : Fin 3) : Fin.lastCases false (fun _ : Fin 2 => false) i = false := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.lastCases_last
    · exact Fin.lastCases_castSucc j
  simp [remainderEvent, bool_deleted_cluster_eq_singleton, hlast,
    laceEPrime_singleton_bool, Set.mem_pi, Fin.forall_fin_succ,
    throughSet_eq_conn_of_left_mem (mem_singleton true)]

/-- The repeated-pair remainder event has probability `p²`. -/
theorem repeated_remainderEvent_bool_probability (q : Sym2 Bool → unitInterval) :
    (Measure.pi (fun _ : Fin 3 => law q))
      (remainderEvent false false (fun _ : Fin 2 => (false, true))) =
        (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)^2 := by
  rw [repeated_remainderEvent_bool_eq_rect, Measure.pi_pi, Fin.prod_univ_three]
  change law q univ * tau q true false * tau q true false = _
  rw [measure_univ, one_mul, tau_comm q true false, tau_bool_cross]
  exact (pow_two _).symm

/-- The convolution in the remainder upper bound evaluates exactly to `p⁴`. -/
theorem first_remainder_convolution_bool (q : Sym2 Bool → unitInterval) :
    (∑' u, ∑' v, laceCoefficient q 1 false u *
      offDiagonal (fun a b : Bool => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
      tau q v false) = (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)^4 := by
  have ht : tau q true false = (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) := by
    rw [tau_comm]
    exact tau_bool_cross q
  simp [tsum_fintype, offDiagonal, laceCoefficient_one_bool,
    laceCoefficient_one_bool_cross, ht, pow_succ, mul_assoc]

/-- The constant-one remainder bound is attained for every two-vertex profile.
In particular, it is attained with positive remainder whenever `p > 0`. -/
theorem laceRemainder_one_bool (q : Sym2 Bool → unitInterval) :
    laceRemainder q 1 false false =
      (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)^4 := by
  apply le_antisymm
  · exact (laceRemainder_succ_le_tsum_laceCoefficient_mul_tau q 0 false false).trans_eq
      (first_remainder_convolution_bool q)
  · have hle := ENNReal.le_tsum (f := fun b : Fin 2 → Bool × Bool =>
      (∏ i, offDiagonal (fun a c : Bool =>
        (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞)) (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin 3 => law q)) (remainderEvent false false b))
        (fun _ => (false, true))
    have hw : (∏ i : Fin 2, offDiagonal (fun a c : Bool =>
        (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞)) false true) =
        (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)^2 := by
      simp [offDiagonal, pow_two]
    rw [hw, repeated_remainderEvent_bool_probability] at hle
    simpa only [laceRemainder, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hle

/-- A nonzero, normalized equality witness for the remainder bound. -/
theorem remainder_one_bool_attains_one :
    laceRemainder (fun _ : Sym2 Bool => 1) 1 false false = 1 ∧
      (∑' u, ∑' v, laceCoefficient (fun _ : Sym2 Bool => 1) 1 false u *
        offDiagonal (fun _ _ : Bool =>
          (unitInterval.toNNReal ((1 : unitInterval)) : ℝ≥0∞)) u v *
        tau (fun _ : Sym2 Bool => 1) v false) = 1 := by
  constructor
  · simp [laceRemainder_one_bool]
  · simpa using first_remainder_convolution_bool (fun _ : Sym2 Bool => 1)

/-- Every universal multiplier in the remainder convolution bound is at least
one. Testing only two-vertex profiles already forces this value. -/
theorem one_le_of_universal_remainder_bound (C : ℝ≥0∞)
    (h : ∀ q : Sym2 Bool → unitInterval,
      laceRemainder q 1 false false ≤ C *
        ∑' u, ∑' v, laceCoefficient q 1 false u *
          offDiagonal (fun a b : Bool => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v false) : 1 ≤ C := by
  have hc := h (fun _ => 1)
  rw [first_remainder_convolution_bool, laceRemainder_one_bool] at hc
  simpa only [unitInterval.toNNReal_one, ENNReal.coe_one, one_pow, mul_one] using hc

end PercLib.Percolation.Bond.Lace
