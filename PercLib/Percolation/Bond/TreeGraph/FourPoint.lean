/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.TreeGraph.BranchPoint

/-!
# The three pairings in the four-point tree-graph bound

## Main results

Four terminals joined in the actual configuration are bounded by the three
possible tree pairings, with two summed branch vertices. The proof specializes
the existing branch-point inequality and then applies the proved three-point
bound. Repeated terminals and infinite sums are allowed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- The actual four-point connection probability is bounded by its three
pairings; the coefficient of each pairing is exactly one. -/
theorem law_three_conn_le_three_pairings (q : Sym2 V → unitInterval) (o a b c : V) :
    law q (conn o a ∩ (conn o b ∩ conn o c)) ≤
      ∑' u, ∑' v, tau q o u *
        (tau q u a * tau q u v * tau q v b * tau q v c +
          tau q u b * tau q u v * tau q v a * tau q v c +
          tau q u c * tau q u v * tau q v a * tau q v b) := by
  classical
  have hsets : (Finset.univ : Finset (Fin 3)).powerset.filter
      (fun A => (0 : Fin 3) ∈ A ∧ (Finset.univ \ A).Nonempty) =
        {({0} : Finset (Fin 3)), {0, 1}, {0, 2}} := by decide
  have h := law_forall_conn_le q ![a, b, c] Finset.univ (by decide)
    (i₀ := 0) (by simp) o
  rw [hsets] at h
  have hbranch : law q (conn o a ∩ (conn o b ∩ conn o c)) ≤
      ∑' u, tau q o u *
        (tau q u a * law q (conn u b ∩ conn u c) +
          tau q u b * law q (conn u a ∩ conn u c) +
          tau q u c * law q (conn u a ∩ conn u b)) := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.mem_univ, forall_const,
      Fin.forall_fin_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, sep_and, sep_mem_eq, tau, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true, ofPred_and, Finset.mem_sdiff,
      true_and, Finset.mem_insert, Finset.ext_iff, Finset.mem_singleton, iff_self_or,
      forall_eq, one_ne_zero, Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_insert,
      ofPred_mem_eq, ofPred_true, inter_self, inter_univ, not_true_eq_false, univ_inter,
      zero_ne_one, or_false, Fin.succ_ne_zero, false_or, iff_false, iff_true, and_self,
      and_false, or_true, Finset.sum_singleton] at h
    convert h using 1
    · congr 1
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    · apply tsum_congr
      intro u
      simp only [tau]
      ring
  refine hbranch.trans (ENNReal.tsum_le_tsum fun u => ?_)
  calc
    _ ≤ tau q o u *
        (tau q u a * (∑' v, tau q u v * tau q v b * tau q v c) +
          tau q u b * (∑' v, tau q u v * tau q v a * tau q v c) +
          tau q u c * (∑' v, tau q u v * tau q v a * tau q v b)) :=
      mul_le_mul' le_rfl (add_le_add (add_le_add
        (mul_le_mul' le_rfl (treeGraphInequality V q u b c))
        (mul_le_mul' le_rfl (treeGraphInequality V q u a c)))
        (mul_le_mul' le_rfl (treeGraphInequality V q u a b)))
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      ring

end PercLib.Percolation.Bond
