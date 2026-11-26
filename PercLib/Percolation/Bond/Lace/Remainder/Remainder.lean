/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Basic
public import PercLib.Percolation.Bond.Lace.Coefficients.Coefficients

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Removing the no-earlier-pivotal restriction in the final layer enlarges
the positive coefficient event to the remainder event. -/
theorem coefficientEvent_subset_remainderEvent {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V) :
    coefficientEvent x y b ⊆ remainderEvent x y b := by
  intro ω h
  refine ⟨h.1, fun i => ?_⟩
  split_ifs
  · exact (h.2 i).1
  · exact h.2 i

set_option maxHeartbeats 800000 in
/-- Remainder events are measurable even though the last domain is random. -/
theorem measurableSet_remainderEvent [Countable V] {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V) : MeasurableSet (remainderEvent x y b) := by
  unfold remainderEvent
  simp only [ofPred_and, ofPred_forall]
  refine ((measurableSet_doubleConn x (b 0).1).preimage (measurable_pi_apply 0)).inter
    (MeasurableSet.iInter fun i => ?_)
  generalize (Fin.cases x (fun j => (b j).2) i.castSucc : V) = a
  generalize (Fin.lastCases y (fun j => (b j).1) i.succ : V) = z
  have hC : Measurable (fun ω : Fin (n + 2) → Config V =>
      cluster (ω i.castSucc \ {s((b i).1, (b i).2)}) a) :=
    (measurable_deleted_cluster s((b i).1, (b i).2) a).comp
      (measurable_pi_apply i.castSucc)
  split_ifs
  · exact measurableSet_throughSet_of_measurable hC (measurable_pi_apply i.succ) _ _
  · exact measurableSet_laceEPrime_of_measurable hC (measurable_pi_apply i.succ) _ _

/-- The next positive coefficient is bounded by the current nonnegative
remainder, with exact constant one. -/
theorem laceCoefficient_succ_le_remainder (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) : laceCoefficient q (n + 1) x y ≤ laceRemainder q n x y := by
  apply ENNReal.tsum_le_tsum
  intro b
  exact mul_le_mul_right (measure_mono (coefficientEvent_subset_remainderEvent x y b)) _

/-- At order zero the only through-set test occurs in the second layer. -/
theorem mem_remainderEvent_zero_iff (x y : V) (b : Fin 1 → V × V)
    (ω : Fin 2 → Config V) :
    ω ∈ remainderEvent x y b ↔
      ω 0 ∈ doubleConn x (b 0).1 ∧
      ω 1 ∈ throughSet (cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y := by
  have hlast : Fin.lastCases y (fun j => (b j).1) (1 : Fin 2) = y := by
    change Fin.lastCases y (fun j => (b j).1) (Fin.last 1) = y
    exact Fin.lastCases_last
  simp [remainderEvent, Fin.forall_fin_one, hlast]

@[simp] theorem laceRemainder_zero_profile (n : ℕ) (x y : V) :
    laceRemainder (fun _ : Sym2 V => 0) n x y = 0 := by
  simp [laceRemainder, offDiagonal]

end PercLib.Percolation.Bond.Lace
