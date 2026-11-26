/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original finite-layer interface proofs; no upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Defs
public import PercLib.Percolation.Bond.Lace.Coefficients.Recursion

/-!
# Prefix events and their last independent layer

## Main results

Proves measurability and exact decomposition of canonical coefficient prefixes
into the previous layers and their last independent configuration.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

@[simp] theorem coefficientPrefixEvent_zero (x u : V) (b : Fin 0 → V × V) :
    coefficientPrefixEvent x u 0 b = {ω : Fin 1 → Config V | ω 0 ∈ doubleConn x u} := rfl

@[simp] theorem coefficientPrefixEvent_succ (x u : V) {n : ℕ} (b : Fin (n + 1) → V × V) :
    coefficientPrefixEvent x u (n + 1) b = coefficientEvent x u b := rfl

theorem measurableSet_coefficientPrefixEvent [Countable V] (x u : V)
    (n : ℕ) (b : Fin n → V × V) : MeasurableSet (coefficientPrefixEvent x u n b) := by
  classical
  cases n with
  | zero => exact (measurableSet_doubleConn x u).preimage (measurable_pi_apply 0)
  | succ n => exact measurableSet_coefficientEvent x u b

theorem measurableSet_markedPrefix [Countable V] (x : V) (n : ℕ)
    (b : Fin n → V × V) (c : V × V) (a : V) :
    MeasurableSet (coefficientPrefixEvent x c.1 n b ∩
      {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
        conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) a}) :=
  (measurableSet_coefficientPrefixEvent x c.1 n b).inter
    ((measurableSet_conn _ a).preimage (by fun_prop))

theorem prefixIncoming_snoc_last (x : V) {n : ℕ} (b : Fin n → V × V) (c : V × V) :
    Fin.cases x (fun j => ((Fin.snoc b c : Fin (n + 1) → V × V) j).2)
      (Fin.last (n + 1)) = c.2 := by
  classical
  rw [← Fin.succ_last, Fin.cases_succ, Fin.snoc_last]

/-- Appending the final bond gives a prefix and one independent `E'` section,
including the case of a prefix with no earlier bond. -/
theorem mem_coefficientEvent_snoc_prefix_iff {n : ℕ} (x y : V)
    (b : Fin n → V × V) (c : V × V)
    (ω : Fin (n + 1) → Config V) (η : Config V) :
    Fin.snoc ω η ∈ coefficientEvent x y (Fin.snoc b c) ↔
      ω ∈ coefficientPrefixEvent x c.1 n b ∧
      η ∈ laceEPrime
        (cluster (ω (Fin.last n) \ {s(c.1, c.2)})
          (Fin.cases x (fun j => (b j).2) (Fin.last n))) c.2 y := by
  classical
  cases n with
  | zero =>
    rw [mem_coefficientEvent_one_iff]
    simp [coefficientPrefixEvent, Fin.snoc]
  | succ n =>
    simpa only [coefficientPrefixEvent, ← Fin.succ_last, Fin.cases_succ] using
      mem_coefficientEvent_snoc_iff x y b c ω η

/-- A marked prefix splits into the preceding prefix and an interior layer
with its outgoing deleted-cluster marker. -/
theorem mem_markedPrefix_snoc_iff {n : ℕ} (x : V)
    (b : Fin n → V × V) (d c : V × V) (a : V)
    (ω : Fin (n + 1) → Config V) (η : Config V) :
    Fin.snoc ω η ∈ coefficientPrefixEvent x c.1 (n + 1) (Fin.snoc b d) ∩
      {ξ | ξ (Fin.last (n + 1)) \ {s(c.1, c.2)} ∈ conn
        (Fin.cases x (fun j => ((Fin.snoc b d : Fin (n + 1) → V × V) j).2)
          (Fin.last (n + 1))) a} ↔
      ω ∈ coefficientPrefixEvent x d.1 n b ∧
        η ∈ laceEPrime
          (cluster (ω (Fin.last n) \ {s(d.1, d.2)})
            (Fin.cases x (fun j => (b j).2) (Fin.last n))) d.2 c.1 ∩
          {ξ : Config V | ξ \ {s(c.1, c.2)} ∈ conn d.2 a} := by
  classical
  simp only [mem_inter_iff, coefficientPrefixEvent_succ,
    mem_coefficientEvent_snoc_prefix_iff, mem_ofPred_eq, Fin.snoc_last,
    prefixIncoming_snoc_last]
  tauto

end PercLib.Percolation.Bond.Lace
