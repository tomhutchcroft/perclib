/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original cylinder and conditional-law proofs for the canonical stopped priority
exploration, using the existing independent-coordinate Bernoulli law.
-/
module

public import PercLib.Probability.Exploration.PriorityStopped
public import PercLib.Probability.Exploration.Transcript

/-!
# Finite prefixes of the stopped priority exploration

## Main results

The actual answer prefix agrees with a reference run exactly when the statuses
of its previously queried bonds agree. This gives measurable finite prefixes
and the exact next-answer factorization, including the cemetery answer. These
statements use deterministic adaptedness and no repeated queries; they do not
assume independence of the adaptively chosen queried set.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory ProbabilityTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}
variable [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)]

omit [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)] in
/-- A reference answer prefix fixes precisely the statuses of its queried bonds. -/
theorem priorityAnswer_prefix_eq_iff (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ)
    (o : V) (n m : ℕ) (ω ω₀ : Config V) :
    (fun s : Fin m => priorityAnswer G ι o n ω s) =
      (fun s : Fin m => priorityAnswer G ι o n ω₀ s) ↔
    ∀ s < m, ∀ e, priorityQuery G ι o n ω₀ s = some e →
      ((e : Sym2 V) ∈ ω ↔ (e : Sym2 V) ∈ ω₀) := by
  classical
  constructor
  · intro h s hs e he
    have hp : ∀ t < s, priorityAnswer G ι o n ω t = priorityAnswer G ι o n ω₀ t :=
      fun t ht => congrFun h ⟨t, ht.trans hs⟩
    have hq := priorityQuery_eq_of_priorityAnswer_eq hp
    have ha := congrFun h ⟨s, hs⟩
    simpa [priorityAnswer, hq, he] using ha
  · intro h
    have hp : ∀ s, s < m → priorityAnswer G ι o n ω s = priorityAnswer G ι o n ω₀ s := by
      intro s
      induction s using Nat.strong_induction_on with
      | h s ih =>
        intro hs
        have hq := priorityQuery_eq_of_priorityAnswer_eq
          (fun t ht => ih t ht (ht.trans hs))
        cases he : priorityQuery G ι o n ω₀ s with
        | none => simp [priorityAnswer, hq, he]
        | some e => simp [priorityAnswer, hq, he, h s hs e he]
    funext s
    exact hp s s.isLt

omit [MeasurableSingletonClass (Option Bool)] in
/-- Finite answer prefixes are measurable for arbitrary vertex types. -/
theorem measurable_priorityAnswer_prefix (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ)
    (o : V) (n m : ℕ) :
    Measurable (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s) := by
  classical
  let : Countable G.edgeSet := ι.injective.countable
  apply measurable_to_countable
  intro ω₀
  change MeasurableSet {ω : Config V |
    (fun s : Fin m => priorityAnswer G ι o n ω s) =
      (fun s : Fin m => priorityAnswer G ι o n ω₀ s)}
  simp_rw [priorityAnswer_prefix_eq_iff]
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun (s : ℕ) => MeasurableSet.iInter fun (hs : s < m) =>
    MeasurableSet.iInter fun (e : G.edgeSet) =>
      MeasurableSet.iInter fun (he : priorityQuery G ι o n ω₀ s = some e) => ?_
  by_cases h : (e : Sym2 V) ∈ ω₀
  · simpa [h] using measurableSet_mem (e : Sym2 V)
  · convert (measurableSet_mem (e : Sym2 V)).compl using 1
    ext ω
    simp [h]

omit [MeasurableSingletonClass (Option Bool)] in
/-- A single answer in the actual stopped exploration is measurable. -/
theorem measurable_priorityAnswer (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ)
    (o : V) (n m : ℕ) : Measurable (fun ω : Config V => priorityAnswer G ι o n ω m) := by
  have h := measurable_priorityAnswer_prefix G ι o n (m + 1)
  exact (measurable_pi_iff.mp h) (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))

open Classical in
/-- The marginal law of a fixed bond's recorded answer. -/
theorem law_some_decide_mem (q : Sym2 V → unitInterval) (e : Sym2 V) (b : Option Bool) :
    law q {ω : Config V | some (decide (e ∈ ω)) = b} =
      bernoulliMeasure (some true : Option Bool) (some false) (q e) {b} := by
  classical
  cases b with
  | none => simp [bernoulliMeasure_def]
  | some b =>
    have h := prodBernoulli_transcript q (fun _ : Fin 1 => e)
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ => b)
    cases b <;> simpa [law, bernoulliMeasure_def] using h

/-- The next-answer law factors from a reference prefix. This unnormalized
identity also holds for null prefixes and for a halted exploration. -/
theorem law_priorityAnswer_prefix_inter_next (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ)
    (o : V) (n m : ℕ) (q : Sym2 V → unitInterval) (ω₀ : Config V) (b : Option Bool) :
    law q {ω : Config V |
      (fun s : Fin m => priorityAnswer G ι o n ω s) =
        (fun s : Fin m => priorityAnswer G ι o n ω₀ s) ∧
      priorityAnswer G ι o n ω m = b} =
    law q {ω : Config V |
      (fun s : Fin m => priorityAnswer G ι o n ω s) =
        (fun s : Fin m => priorityAnswer G ι o n ω₀ s)} *
      (priorityQuery G ι o n ω₀ m).elim (Measure.dirac none {b})
        (fun e => bernoulliMeasure (some true : Option Bool) (some false)
          (q (e : Sym2 V)) {b}) := by
  classical
  let A (ω : Config V) : Prop :=
    (fun s : Fin m => priorityAnswer G ι o n ω s) =
      (fun s : Fin m => priorityAnswer G ι o n ω₀ s)
  have hq (ω : Config V) (hω : A ω) :
      priorityQuery G ι o n ω m = priorityQuery G ι o n ω₀ m :=
    priorityQuery_eq_of_priorityAnswer_eq fun s hs => congrFun hω ⟨s, hs⟩
  cases he : priorityQuery G ι o n ω₀ m with
  | none =>
    have hset : {ω : Config V | A ω ∧ priorityAnswer G ι o n ω m = b} =
        if b = none then {ω | A ω} else ∅ := by
      ext ω
      by_cases hω : A ω
      · simp [hω, priorityAnswer, hq ω hω, he, eq_comm]
      · simp [hω]
    change law q {ω | A ω ∧ priorityAnswer G ι o n ω m = b} =
      law q {ω | A ω} * _
    rw [hset]
    cases b <;> simp
  | some e =>
    let : Countable G.edgeSet := ι.injective.countable
    let S : Set (Sym2 V) := Subtype.val '' {f : G.edgeSet |
      ∃ s < m, priorityQuery G ι o n ω₀ s = some f}
    have hS : S.Countable := (Set.to_countable {f : G.edgeSet |
      ∃ s < m, priorityQuery G ι o n ω₀ s = some f}).image Subtype.val
    let : Countable S := hS.to_subtype
    have heS : (e : Sym2 V) ∉ S := by
      rintro ⟨f, ⟨s, hs, hf⟩, hfe⟩
      have hfe' : f = e := Subtype.ext hfe
      subst f
      exact (Nat.ne_of_lt hs) (priorityQuery_injective hf he)
    let C : Set (Set S) := {η | ∀ f : S, f ∈ η ↔ (f : Sym2 V) ∈ ω₀}
    let B : Set (Set (Sᶜ : Set (Sym2 V))) :=
      {η | some (decide ((⟨(e : Sym2 V), heS⟩ : (Sᶜ : Set (Sym2 V))) ∈ η)) = b}
    have hC : MeasurableSet C := by
      dsimp only [C]
      simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun f => ?_
      by_cases hf : (f : Sym2 V) ∈ ω₀
      · simpa [hf] using measurableSet_mem f
      · convert (measurableSet_mem f).compl using 1
        ext η
        simp [hf]
    have hB : MeasurableSet B := by
      cases b with
      | none => simp [B]
      | some b =>
        cases b
        · convert (measurableSet_mem
            (⟨(e : Sym2 V), heS⟩ : (Sᶜ : Set (Sym2 V)))).compl using 1
          ext η
          simp [B]
        · simpa [B] using measurableSet_mem
            (⟨(e : Sym2 V), heS⟩ : (Sᶜ : Set (Sym2 V)))
    have hA (ω : Config V) : A ω ↔ {f : S | (f : Sym2 V) ∈ ω} ∈ C := by
      rw [show A ω ↔ _ from priorityAnswer_prefix_eq_iff G ι o n m ω ω₀]
      constructor
      · intro h f
        obtain ⟨f', ⟨s, hs, hf'⟩, hff⟩ := f.property
        change (f : Sym2 V) ∈ ω ↔ (f : Sym2 V) ∈ ω₀
        rw [← hff]
        exact h s hs f' hf'
      · intro h s hs f hf
        exact h ⟨(f : Sym2 V), ⟨f, ⟨s, hs, hf⟩, rfl⟩⟩
    have hfactor := prodBernoulli_block_inter q S Sᶜ disjoint_compl_right C B hC hB
    have hjoint : {ω : Config V | A ω ∧ priorityAnswer G ι o n ω m = b} =
        {ω | {f : S | (f : Sym2 V) ∈ ω} ∈ C ∧
          {f : (Sᶜ : Set (Sym2 V)) | (f : Sym2 V) ∈ ω} ∈ B} := by
      ext ω
      simp only [mem_ofPred_eq]
      by_cases hω : A ω
      · simp only [hω, (hA ω).mp hω, true_and]
        simp [B, priorityAnswer, hq ω hω, he]
      · simp only [hω, false_and, ← hA ω]
    change law q {ω | A ω ∧ priorityAnswer G ι o n ω m = b} = _
    rw [hjoint]
    change prodBernoulli q _ = _
    rw [hfactor]
    change law q {ω | {f : S | (f : Sym2 V) ∈ ω} ∈ C} *
      law q {ω | some (decide ((e : Sym2 V) ∈ ω)) = b} = _
    simp only [← hA, law_some_decide_mem, Option.elim_some]
    rfl

omit [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)] in
/-- The actual next query is a deterministic function of its finite answer
prefix. The function is independent of the Bernoulli profile. -/
theorem exists_priorityQuery_eq_prefix (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ)
    (o : V) (n m : ℕ) :
    ∃ next : (Fin m → Option Bool) → Option G.edgeSet, ∀ ω : Config V,
      priorityQuery G ι o n ω m = next (fun s => priorityAnswer G ι o n ω s) := by
  have hf : Function.FactorsThrough (fun ω : Config V => priorityQuery G ι o n ω m)
      (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s) := by
    intro ω ω' h
    exact priorityQuery_eq_of_priorityAnswer_eq fun s hs => congrFun h ⟨s, hs⟩
  obtain ⟨next, hnext⟩ := (Function.factorsThrough_iff _).mp hf
  exact ⟨next, fun ω => congrFun hnext ω⟩

/-- Any function of the next query is measurable, because the query factors
through a finite answer space. No measurable structure on the vertex type is needed. -/
theorem measurable_priorityQuery_elim {X : Type*} [MeasurableSpace X]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ)
    (a : X) (f : G.edgeSet → X) :
    Measurable (fun ω : Config V => (priorityQuery G ι o n ω m).elim a f) := by
  obtain ⟨next, hnext⟩ := exists_priorityQuery_eq_prefix G ι o n m
  simpa only [hnext, Function.comp_def] using
    (measurable_of_finite (fun b : Fin m → Option Bool => (next b).elim a f)).comp
      (measurable_priorityAnswer_prefix G ι o n m)

end PercLib.Percolation.Bond
