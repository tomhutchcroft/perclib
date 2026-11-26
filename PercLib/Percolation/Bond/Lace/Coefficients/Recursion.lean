/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Remainder
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Exact integration of the last independent lace layer

## Main results

Finite product measures split using mathlib's measure-preserving coordinate
equivalence. This gives exact nonnegative integral formulas, with no absolute
summability or finiteness assumption on the sum of coefficients.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Split off the last configuration in a finite independent family. -/
theorem measure_layers_eq_lintegral_snoc (q : Sym2 V → unitInterval) {n : ℕ}
    {S : Set (Fin (n + 1) → Config V)} (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin (n + 1) => law q)) S =
      ∫⁻ ω : Fin n → Config V, law q {η | Fin.snoc ω η ∈ S}
        ∂(Measure.pi (fun _ : Fin n => law q)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Config V) (Fin.last n)
  have he : (fun p : Config V × (Fin n → Config V) => e.symm p) =
      fun p => Fin.snoc p.2 p.1 := by
    funext p
    exact Fin.insertNth_last' p.1 p.2
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => law q) (Fin.last n)).symm
  have hm : Measurable (fun p : Config V × (Fin n → Config V) =>
      (Fin.snoc p.2 p.1 : Fin (n + 1) → Config V)) := by
    rw [← he]
    exact e.symm.measurable
  have hmeasure : ((law q).prod (Measure.pi (fun _ : Fin n => law q)))
      {p : Config V × (Fin n → Config V) | Fin.snoc p.2 p.1 ∈ S} =
        (Measure.pi (fun _ : Fin (n + 1) => law q)) S := by
    change ((law q).prod (Measure.pi (fun _ : Fin n => law q)))
      ((fun p => Fin.snoc p.2 p.1) ⁻¹' S) = _
    rw [← he]
    exact hp.measure_preimage hS.nullMeasurableSet
  rw [← hmeasure]
  exact Measure.prod_apply_symm (hS.preimage hm)

/-- The last layer can always be integrated conditionally on all earlier ones. -/
theorem coefficientEvent_probability_eq_lintegral_last [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b) =
      ∫⁻ ω : Fin (n + 1) → Config V,
        law q {η | Fin.snoc ω η ∈ coefficientEvent x y b}
        ∂(Measure.pi (fun _ : Fin (n + 1) => law q)) :=
  measure_layers_eq_lintegral_snoc q (measurableSet_coefficientEvent x y b)

private theorem incoming_snoc_castSucc {n : ℕ} (x : V)
    (b : Fin (n + 1) → V × V) (c : V × V) (i : Fin (n + 1)) :
    (Fin.cases x (fun j => ((Fin.snoc b c : Fin (n + 2) → V × V) j).2) i.castSucc.castSucc : V) =
      Fin.cases x (fun j => (b j).2) i.castSucc := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.castSucc_succ]

private theorem outgoing_snoc_castSucc {n : ℕ} (y : V)
    (b : Fin (n + 1) → V × V) (c : V × V) (i : Fin (n + 1)) :
    (Fin.lastCases y (fun j => ((Fin.snoc b c : Fin (n + 2) → V × V) j).1) i.castSucc.succ : V) =
      Fin.lastCases c.1 (fun j => (b j).1) i.succ := by
  classical
  rw [← Fin.castSucc_succ, Fin.lastCases_castSucc]
  generalize i.succ = j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp

/-- Appending a bond and a configuration appends exactly one `E'` factor.
The cluster in that factor is computed in the preceding configuration. -/
theorem mem_coefficientEvent_snoc_iff {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (c : V × V)
    (ω : Fin (n + 2) → Config V) (η : Config V) :
    Fin.snoc ω η ∈ coefficientEvent x y (Fin.snoc b c) ↔
      ω ∈ coefficientEvent x c.1 b ∧
      η ∈ laceEPrime
        (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y := by
  classical
  have hω (i : Fin (n + 1)) :
      (Fin.snoc ω η : Fin (n + 3) → Config V) i.castSucc.succ = ω i.succ := by
    rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
  have hlast : (Fin.cases x (fun j => ((Fin.snoc b c : Fin (n + 2) → V × V) j).2)
      (Fin.last (n + 1)).castSucc : V) = (b (Fin.last n)).2 := by
    rw [show (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ by ext; simp]
    simp
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [Fin.snoc_apply_zero] using h0
    · intro i
      simpa only [hω, Fin.snoc_castSucc, incoming_snoc_castSucc,
        outgoing_snoc_castSucc] using h i.castSucc
    · simpa only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc,
        Fin.lastCases_last, hlast] using h (Fin.last (n + 1))
  · rintro ⟨⟨h0, h⟩, hη⟩
    refine ⟨?_, ?_⟩
    · simpa only [Fin.snoc_apply_zero] using h0
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc,
          Fin.lastCases_last, hlast] using hη
      · simpa only [hω, Fin.snoc_castSucc, incoming_snoc_castSucc,
          outgoing_snoc_castSucc] using h j

/-- Exact recursion for a fixed oriented bond sequence, integrating its final
`E'` event under a fresh independent configuration. -/
theorem coefficientEvent_snoc_probability_eq_lintegral [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (c : V × V) :
    (Measure.pi (fun _ : Fin (n + 3) => law q)) (coefficientEvent x y (Fin.snoc b c)) =
      ∫⁻ ω : Fin (n + 2) → Config V,
        (coefficientEvent x c.1 b).indicator (fun ω =>
          law q (laceEPrime
            (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y)) ω
        ∂(Measure.pi (fun _ : Fin (n + 2) => law q)) := by
  classical
  rw [coefficientEvent_probability_eq_lintegral_last]
  apply lintegral_congr
  intro ω
  have hset : {η | Fin.snoc ω η ∈ coefficientEvent x y (Fin.snoc b c)} =
      if ω ∈ coefficientEvent x c.1 b then
        laceEPrime (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y
      else ∅ := by
    ext η
    rw [mem_ofPred_eq, mem_coefficientEvent_snoc_iff]
    split_ifs <;> simp_all
  rw [hset]
  split_ifs <;> simp_all [Set.indicator]

/-- The same last-coordinate integration applies to the nonnegative remainder. -/
theorem remainderEvent_probability_eq_lintegral_last [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q)) (remainderEvent x y b) =
      ∫⁻ ω : Fin (n + 1) → Config V,
        law q {η | Fin.snoc ω η ∈ remainderEvent x y b}
        ∂(Measure.pi (fun _ : Fin (n + 1) => law q)) :=
  measure_layers_eq_lintegral_snoc q (measurableSet_remainderEvent x y b)

/-- A remainder with one appended bond retains all the preceding `E'` tests
and ends with one through-set test in a fresh configuration. -/
theorem mem_remainderEvent_snoc_iff {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (c : V × V)
    (ω : Fin (n + 2) → Config V) (η : Config V) :
    Fin.snoc ω η ∈ remainderEvent x y (Fin.snoc b c) ↔
      ω ∈ coefficientEvent x c.1 b ∧
      η ∈ throughSet
        (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y := by
  classical
  have hω (i : Fin (n + 1)) :
      (Fin.snoc ω η : Fin (n + 3) → Config V) i.castSucc.succ = ω i.succ := by
    rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
  have hlast : (Fin.cases x (fun j => ((Fin.snoc b c : Fin (n + 2) → V × V) j).2)
      (Fin.last (n + 1)).castSucc : V) = (b (Fin.last n)).2 := by
    rw [show (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ by ext; simp]
    simp
  have hn (i : Fin (n + 1)) : (i.castSucc : Fin (n + 2)).val ≠ n + 1 :=
    Nat.ne_of_lt i.isLt
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [Fin.snoc_apply_zero] using h0
    · intro i
      simpa only [hn, ite_false, hω, Fin.snoc_castSucc, incoming_snoc_castSucc,
        outgoing_snoc_castSucc] using h i.castSucc
    · simpa only [Fin.val_last, ite_eq_left, Fin.succ_last, Fin.snoc_last,
        Fin.snoc_castSucc, Fin.lastCases_last, hlast] using h (Fin.last (n + 1))
  · rintro ⟨⟨h0, h⟩, hη⟩
    refine ⟨?_, ?_⟩
    · simpa only [Fin.snoc_apply_zero] using h0
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.val_last, ite_eq_left, Fin.succ_last, Fin.snoc_last,
          Fin.snoc_castSucc, Fin.lastCases_last, hlast] using hη
      · simpa only [hn, ite_false, hω, Fin.snoc_castSucc, incoming_snoc_castSucc,
          outgoing_snoc_castSucc] using h j

/-- Exact last-layer recursion for a fixed remainder bond sequence. The
initial layers form the coefficient event, and the last factor is through-set
connection under an independent configuration. -/
theorem remainderEvent_snoc_probability_eq_lintegral [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (c : V × V) :
    (Measure.pi (fun _ : Fin (n + 3) => law q)) (remainderEvent x y (Fin.snoc b c)) =
      ∫⁻ ω : Fin (n + 2) → Config V,
        (coefficientEvent x c.1 b).indicator (fun ω =>
          law q (throughSet
            (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y)) ω
        ∂(Measure.pi (fun _ : Fin (n + 2) => law q)) := by
  classical
  rw [remainderEvent_probability_eq_lintegral_last]
  apply lintegral_congr
  intro ω
  have hset : {η | Fin.snoc ω η ∈ remainderEvent x y (Fin.snoc b c)} =
      if ω ∈ coefficientEvent x c.1 b then
        throughSet (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y
      else ∅ := by
    ext η
    rw [mem_ofPred_eq, mem_remainderEvent_snoc_iff]
    split_ifs <;> simp_all
  rw [hset]
  split_ifs <;> simp_all [Set.indicator]

end PercLib.Percolation.Bond.Lace
