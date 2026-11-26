/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Coefficients.Basic
public import PercLib.Percolation.Bond.Lace.JointMeasurability
public import PercLib.Percolation.Bond.Lace.DoubleConnection

/-!
# Measurability and endpoint checks for positive lace coefficients

The event depends on earlier configurations through their deleted clusters.
Its measurability uses the joint measurable-set theorem, rather than an
incorrect fixed-domain measurability argument. Individual event probabilities
are at most one. The sum over oriented bond sequences may be infinite.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

@[simp] theorem laceCoefficient_zero (q : Sym2 V → unitInterval) (x y : V) :
    laceCoefficient q 0 x y = piZero q x y := rfl

set_option maxHeartbeats 800000 in
/-- Positive-order event probabilities are genuine measurable events on the
finite product of configuration spaces. -/
theorem measurableSet_coefficientEvent [Countable V] {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V) : MeasurableSet (coefficientEvent x y b) := by
  have hi : ∀ i : Fin (n + 1), MeasurableSet {ω : Fin (n + 2) → Config V |
      ω i.succ ∈ laceEPrime
        (cluster (ω i.castSucc \ {s((b i).1, (b i).2)})
          (Fin.cases x (fun j => (b j).2) i.castSucc))
        (b i).2 (Fin.lastCases y (fun j => (b j).1) i.succ)} := by
    intro i
    generalize (Fin.cases x (fun j => (b j).2) i.castSucc : V) = a
    generalize (Fin.lastCases y (fun j => (b j).1) i.succ : V) = z
    have hprev : Measurable (fun ω : Fin (n + 2) → Config V => ω i.castSucc) :=
      measurable_pi_apply i.castSucc
    have hnext : Measurable (fun ω : Fin (n + 2) → Config V => ω i.succ) :=
      measurable_pi_apply i.succ
    exact measurableSet_laceEPrime_of_measurable
      ((measurable_deleted_cluster s((b i).1, (b i).2) a).comp hprev)
      hnext (b i).2 z
  change MeasurableSet ({ω : Fin (n + 2) → Config V | ω 0 ∈ doubleConn x (b 0).1} ∩
    {ω | ∀ i : Fin (n + 1), ω i.succ ∈ laceEPrime
      (cluster (ω i.castSucc \ {s((b i).1, (b i).2)})
        (Fin.cases x (fun j => (b j).2) i.castSucc))
      (b i).2 (Fin.lastCases y (fun j => (b j).1) i.succ)})
  refine ((measurableSet_doubleConn x (b 0).1).preimage (measurable_pi_apply 0)).inter ?_
  simp only [ofPred_forall]
  exact MeasurableSet.iInter hi

/-- No extra normalization factor is introduced by the finite independent layers. -/
theorem coefficientEvent_probability_le_one (q : Sym2 V → unitInterval) {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b) ≤ 1 :=
  prob_le_one

/-- First positive order has exactly two independent layers and one deleted cluster. -/
theorem mem_coefficientEvent_one_iff (x y : V) (b : Fin 1 → V × V)
    (ω : Fin 2 → Config V) :
    ω ∈ coefficientEvent x y b ↔
      ω 0 ∈ doubleConn x (b 0).1 ∧
      ω 1 ∈ laceEPrime (cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y := by
  have hlast : Fin.lastCases y (fun j => (b j).1) (1 : Fin 2) = y := by
    change Fin.lastCases y (fun j => (b j).1) (Fin.last 1) = y
    exact Fin.lastCases_last
  simp [coefficientEvent, Fin.forall_fin_one, hlast]

/-- All orders vanish at the zero edge profile. -/
@[simp] theorem laceCoefficient_zero_profile [Countable V] (n : ℕ) (x y : V) :
    laceCoefficient (fun _ : Sym2 V => 0) n x y = 0 := by
  cases n with
  | zero => simp
  | succ n => simp [laceCoefficient, offDiagonal]

/-- An oriented sequence containing a diagonal pair has zero bond weight,
regardless of the profile's arbitrary diagonal values. -/
theorem coefficient_weight_eq_zero_of_diag (q : Sym2 V → unitInterval) {n : ℕ}
    (b : Fin (n + 1) → V × V) (i : Fin (n + 1)) (hi : (b i).1 = (b i).2) :
    (∏ j, offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
      (b j).1 (b j).2) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [offDiagonal, hi]

/-- A through-set connection with no pivotal pair is in `E'`. -/
theorem mem_laceEPrime_of_mem_doubleConn {A : Set V} {ω : Config V} {x y : V}
    (hd : ω ∈ doubleConn x y) (ht : ω ∈ throughSet A x y) : ω ∈ laceEPrime A x y := by
  refine ⟨ht, ?_⟩
  rintro ⟨_, ⟨u, rfl⟩, h⟩
  rcases mem_iUnion.mp h with ⟨v, hp, _⟩
  exact not_pivotal_of_mem_doubleConn hd s(u, v) ⟨hp.1, hp.2.1⟩

/-- A concrete nonempty positive-order event on three vertices. The initial
double connection is diagonal and must therefore be retained in this event. -/
example : (fun _ : Fin 2 => (univ : Config (Fin 3))) ∈
    coefficientEvent 0 2 (fun _ : Fin 1 => ((0 : Fin 3), 1)) := by
  rw [mem_coefficientEvent_one_iff]
  refine ⟨by simp, mem_laceEPrime_of_mem_doubleConn ?_ ?_⟩
  · exact mem_doubleConn_of_triangle (z := 0) (by decide) (by decide) (by decide)
      (mem_univ _) (mem_univ _) (mem_univ _)
  · have hA : (2 : Fin 3) ∈ cluster (univ \ {s((0 : Fin 3), 1)}) 0 := by
      exact mem_conn_of_mem (by decide) ⟨mem_univ _, by decide⟩
    rw [throughSet_eq_conn_of_right_mem hA]
    exact mem_conn_of_mem (by decide) (mem_univ _)

end PercLib.Percolation.Bond.Lace
