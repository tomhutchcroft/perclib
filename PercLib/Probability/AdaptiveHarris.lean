/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the canonical finite Bernoulli law. Mathematical reference: the adaptive Harris
inequality for predictable sharing in decision trees, N. Gladkov, "Percolation Inequalities and
Decision Trees", arXiv:2408.08457 (2024). The decision tree is encoded as in
`PercLib.Probability.PredictableSwap`; no new definition is introduced.
-/
module

public import PercLib.Probability.Coordinate
public import PercLib.Probability.PredictableSwap
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Adaptive Harris and BK inequalities

Let `X, Y` be independent with law `μ = prodBernoulli p` on a finite set `E`, read by a
decision tree of depth `n` which, before revealing the pair `(X e, Y e)` of a freshly queried
coordinate, decides whether `e` is shared. With `S` the shared set, the hybrid configuration is
`H = X ∩ S ∪ Y \ S`. If `A, B` are both increasing or both decreasing, then
`μ(A) μ(B) ≤ P(X ∈ A, H ∈ B)`.

The proof removes the sharing decisions from the deepest step upwards. On a fixed history of
the steps before step `k`, the coordinate queried at step `k` is fresh whenever it is shared,
so the fibre does not depend on it, and unsharing it can only lower the probability: this is
a two-point covariance inequality in that coordinate.

The same induction gives the adaptive BK inequality: the probability that there are witnesses
for `A` in `X` and for `B` in `H` whose overlap avoids `S` is at most `μ(A) μ(B)`. Unsharing one
coordinate can only raise that probability, by a four-case comparison of which witnesses may use
the coordinate.

## Main results

* `measure_inter_add_measure_inter_le`: for `P₀ ⊆ P₁` and `Q₀ ⊆ Q₁`,
  `μ(P₀ ∩ Q₁) + μ(P₁ ∩ Q₀) ≤ μ(P₀ ∩ Q₀) + μ(P₁ ∩ Q₁)`.
* `prodBernoulli_prod_hybrid_le_insert`: sharing one more coordinate `e`, on an event that
  does not depend on `e`, does not decrease `P(X ∈ A, H ∈ B)`.
* `answers_eq_of_agree`: the event that the first `k` revealed pairs equal a given history
  depends only on the coordinates that history queries.
* `prodBernoulli_prod_apply_eq_sum_bool`: the pair law split at the two bits of one
  coordinate.
* `prodBernoulli_prod_sharedWitness_insert_le`: unsharing one coordinate `e`, on an event that
  does not depend on `e`, does not decrease the probability of witnesses for `A` in `X` and for
  `B` in `H` overlapping only off `S`.
* `prodBernoulli_prod_le_of_step`, `prodBernoulli_prod_le_of_sharingTree`: for any family of
  events with the one-coordinate monotonicity, sharing along a predictable sharing tree does
  not decrease the probability.
* `prodBernoulli_mul_le_prod_hybrid`: the adaptive Harris inequality.
* `prodBernoulli_prod_sharedWitness_le_mul`: the adaptive BK inequality.
-/

@[expose] public section

open MeasureTheory Set unitInterval
open scoped ENNReal NNReal

/-- **Two-by-two lattice inequality.** For `P₀ ⊆ P₁` and `Q₀ ⊆ Q₁`,
`μ(P₀ ∩ Q₁) + μ(P₁ ∩ Q₀) ≤ μ(P₀ ∩ Q₀) + μ(P₁ ∩ Q₁)`. -/
theorem MeasureTheory.measure_inter_add_measure_inter_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {P₀ P₁ Q₀ Q₁ : Set α} (hP : P₀ ⊆ P₁) (hQ : Q₀ ⊆ Q₁)
    (hQ₀ : MeasurableSet Q₀) :
    μ (P₀ ∩ Q₁) + μ (P₁ ∩ Q₀) ≤ μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₁) := by
  have key : ∀ P, μ (P ∩ Q₁) = μ (P ∩ Q₀) + μ ((P ∩ Q₁) \ Q₀) := fun P => by
    rw [← measure_inter_add_sdiff (P ∩ Q₁) hQ₀, inter_assoc, inter_eq_right.2 hQ]
  have hle : μ ((P₀ ∩ Q₁) \ Q₀) ≤ μ ((P₁ ∩ Q₁) \ Q₀) :=
    measure_mono fun x hx => ⟨⟨hP hx.1.1, hx.1.2⟩, hx.2⟩
  calc μ (P₀ ∩ Q₁) + μ (P₁ ∩ Q₀) = μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₀) + μ ((P₀ ∩ Q₁) \ Q₀) := by
        rw [key P₀]; ring
    _ ≤ μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₀) + μ ((P₁ ∩ Q₁) \ Q₀) := by gcongr
    _ = μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₁) := by rw [key P₁]; ring

namespace PercLib.Probability

variable {E : Type*}

/-- **Splitting the pair law at one coordinate.** For `ν = μ ⊗ μ` with `μ = prodBernoulli p`,
`ν(T)` is the sum over the four values of the two bits at `e` of their weights times the
probability of `T` after setting those two bits. -/
theorem prodBernoulli_prod_apply_eq_sum_bool [Fintype E] (p : E → unitInterval) (e : E)
    (T : Set (Set E × Set E)) :
    (prodBernoulli p).prod (prodBernoulli p) T = ∑ i : Bool, ∑ j : Bool,
      ((if i then unitInterval.toNNReal (p e) else unitInterval.toNNReal (σ (p e)) : ℝ≥0) :
          ℝ≥0∞) *
        ((if j then unitInterval.toNNReal (p e) else unitInterval.toNNReal (σ (p e)) : ℝ≥0) :
          ℝ≥0∞) *
        (prodBernoulli p).prod (prodBernoulli p)
          (Prod.map (fun x => if i then insert e x else x \ {e})
            (fun y => if j then insert e y else y \ {e}) ⁻¹' T) := by
  classical
  set μ := prodBernoulli p with hμdef
  set f : Bool → Set E → Set E := fun b x => if b then insert e x else x \ {e} with hfdef
  set w : Bool → ℝ≥0 := fun b =>
    if b then unitInterval.toNNReal (p e) else unitInterval.toNNReal (σ (p e)) with hwdef
  have hfm : ∀ b, Measurable (f b) := fun b => measurable_of_countable _
  have hμ : μ = w true • μ.map (f true) + w false • μ.map (f false) := by
    have h := prodBernoulli_eq_smul_add_smul p e
    rw [← prodBernoulli_map_insert, ← prodBernoulli_map_diff_singleton] at h
    exact h
  have hmeas : MeasurableSet T := (Set.to_countable T).measurableSet
  change μ.prod μ T = ∑ i : Bool, ∑ j : Bool, (w i : ℝ≥0∞) * w j *
    μ.prod μ (Prod.map (f i) (f j) ⁻¹' T)
  conv_lhs => rw [hμ]
  simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.map_prod_map _ _ (hfm _) (hfm _), Measure.add_apply,
    Measure.smul_apply, Measure.map_apply (measurable_of_countable _) hmeas, Fintype.sum_bool,
    ENNReal.smul_def, smul_eq_mul]
  ring

/-- **Sharing one more coordinate.** Let `C` be an event of the pair `(X, Y)` that does not
depend on the two bits at `e`, and let `e ∉ S₀`. If `A, B` are both increasing or both
decreasing, adding `e` to the shared set does not decrease `P(C, X ∈ A, X ∩ S ∪ Y \ S ∈ B)`. -/
theorem prodBernoulli_prod_hybrid_le_insert [Fintype E] (p : E → unitInterval) (e : E)
    {C : Set (Set E × Set E)}
    (hC : ∀ x y x' y' : Set E, (∀ a, a ≠ e → (a ∈ x ↔ a ∈ x') ∧ (a ∈ y ↔ a ∈ y')) →
      (x, y) ∈ C → (x', y') ∈ C)
    {S₀ : Set E} (he : e ∉ S₀) {A B : Set (Set E)}
    (hAB : (IsUpperSet A ∧ IsUpperSet B) ∨ (IsLowerSet A ∧ IsLowerSet B)) :
    (prodBernoulli p).prod (prodBernoulli p)
        (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∈ B}) ≤
      (prodBernoulli p).prod (prodBernoulli p)
        (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ insert e S₀ ∪ ω.2 \ insert e S₀ ∈ B}) := by
  classical
  set μ := prodBernoulli p with hμdef
  set ν := μ.prod μ with hνdef
  set f : Bool → Set E → Set E := fun b x => if b then insert e x else x \ {e} with hfdef
  set w : Bool → ℝ≥0 := fun b =>
    if b then unitInterval.toNNReal (p e) else unitInterval.toNNReal (σ (p e)) with hwdef
  have hdec : ∀ T : Set (Set E × Set E), ν T = ∑ i : Bool, ∑ j : Bool,
      (w i : ℝ≥0∞) * w j * ν (Prod.map (f i) (f j) ⁻¹' T) := fun T =>
    prodBernoulli_prod_apply_eq_sum_bool p e T
  have hagree : ∀ i j (ω : Set E × Set E) a, a ≠ e →
      (a ∈ ω.1 ↔ a ∈ f i ω.1) ∧ (a ∈ ω.2 ↔ a ∈ f j ω.2) := by
    intro i j ω a ha
    cases i <;> cases j <;> simp [f, ha]
  have hc : ∀ i j (ω : Set E × Set E), Prod.map (f i) (f j) ω ∈ C ↔ ω ∈ C := by
    intro i j ω
    constructor
    · exact hC _ _ ω.1 ω.2 fun a ha =>
        ⟨(hagree i j ω a ha).1.symm, (hagree i j ω a ha).2.symm⟩
    · exact hC ω.1 ω.2 _ _ (hagree i j ω)
  have hH0 : ∀ i j (x y : Set E), f i x ∩ S₀ ∪ f j y \ S₀ = f j (x ∩ S₀ ∪ y \ S₀) := by
    intro i j x y
    ext a
    by_cases ha : a = e
    · subst ha
      cases i <;> cases j <;> simp [f, he]
    · cases i <;> cases j <;> simp [f, ha]
  have hH1 : ∀ i j (x y : Set E),
      f i x ∩ insert e S₀ ∪ f j y \ insert e S₀ = f i (x ∩ S₀ ∪ y \ S₀) := by
    intro i j x y
    ext a
    by_cases ha : a = e
    · subst ha
      cases i <;> cases j <;> simp [f, he]
    · cases i <;> cases j <;> simp [f, ha]
  set P : Bool → Set (Set E × Set E) := fun i => C ∩ {ω | f i ω.1 ∈ A} with hPdef
  set Q : Bool → Set (Set E × Set E) := fun j => {ω | f j (ω.1 ∩ S₀ ∪ ω.2 \ S₀) ∈ B}
    with hQdef
  have hpre0 : ∀ i j, Prod.map (f i) (f j) ⁻¹' (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∈ B}) =
      P i ∩ Q j := by
    intro i j
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hc, Prod.map_fst, Prod.map_snd, hH0,
      P, Q]
    tauto
  have hpre1 : ∀ i j, Prod.map (f i) (f j) ⁻¹'
      (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ insert e S₀ ∪ ω.2 \ insert e S₀ ∈ B}) = P i ∩ Q i := by
    intro i j
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hc, Prod.map_fst, Prod.map_snd, hH1,
      P, Q]
    tauto
  have hfsub : ∀ x, f false x ⊆ f true x := fun x => by
    simp only [f]
    exact sdiff_subset.trans (subset_insert _ _)
  have hmeasQ : ∀ j, MeasurableSet (Q j) := fun j => (Set.to_countable _).measurableSet
  have key : ν (P true ∩ Q false) + ν (P false ∩ Q true) ≤
      ν (P true ∩ Q true) + ν (P false ∩ Q false) := by
    rcases hAB with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have h := measure_inter_add_measure_inter_le ν (P₀ := P false) (P₁ := P true)
        (Q₀ := Q false) (Q₁ := Q true) (fun ω hω => ⟨hω.1, hA (hfsub _) hω.2⟩)
        (fun ω hω => hB (hfsub _) hω) (hmeasQ _)
      rw [add_comm, add_comm (ν (P true ∩ Q true))]
      exact h
    · exact measure_inter_add_measure_inter_le ν (fun ω hω => ⟨hω.1, hA (hfsub _) hω.2⟩)
        (fun ω hω => hB (hfsub _) hω) (hmeasQ _)
  rw [hdec, hdec]
  simp only [hpre0, hpre1, Fintype.sum_bool]
  calc (w true : ℝ≥0∞) * w true * ν (P true ∩ Q true) + w true * w false * ν (P true ∩ Q false) +
        (w false * w true * ν (P false ∩ Q true) + w false * w false * ν (P false ∩ Q false))
      = w true * w true * ν (P true ∩ Q true) + w false * w false * ν (P false ∩ Q false) +
          w true * w false * (ν (P true ∩ Q false) + ν (P false ∩ Q true)) := by ring
    _ ≤ w true * w true * ν (P true ∩ Q true) + w false * w false * ν (P false ∩ Q false) +
          w true * w false * (ν (P true ∩ Q true) + ν (P false ∩ Q false)) := by gcongr
    _ = _ := by ring

/-- **Unsharing one more coordinate, for witnesses.** Let `C` be an event of the pair `(X, Y)`
that does not depend on the two bits at `e`, and let `e ∉ S₀`. Consider the event that there are
witnesses `I ⊆ X` for `A` and `J ⊆ X ∩ S ∪ Y \ S` for `B` (every configuration containing the
witness lies in the event) with `I ∩ J` disjoint from `S`. Removing `e` from the shared set
`insert e S₀` does not decrease its probability on `C`. -/
theorem prodBernoulli_prod_sharedWitness_insert_le [Fintype E] (p : E → unitInterval) (e : E)
    {C : Set (Set E × Set E)}
    (hC : ∀ x y x' y' : Set E, (∀ a, a ≠ e → (a ∈ x ↔ a ∈ x') ∧ (a ∈ y ↔ a ∈ y')) →
      (x, y) ∈ C → (x', y') ∈ C)
    {S₀ : Set E} (he : e ∉ S₀) (A B : Set (Set E)) :
    (prodBernoulli p).prod (prodBernoulli p)
        (C ∩ {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧ (∀ z, I₁ ⊆ z → z ∈ A) ∧
          J ⊆ ω.1 ∩ insert e S₀ ∪ ω.2 \ insert e S₀ ∧ (∀ z, J ⊆ z → z ∈ B) ∧
          I₁ ∩ J ⊆ (insert e S₀)ᶜ}) ≤
      (prodBernoulli p).prod (prodBernoulli p)
        (C ∩ {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧ (∀ z, I₁ ⊆ z → z ∈ A) ∧
          J ⊆ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∧ (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ S₀ᶜ}) := by
  classical
  set ν := (prodBernoulli p).prod (prodBernoulli p) with hνdef
  set f : Bool → Set E → Set E := fun b x => if b then insert e x else x \ {e} with hfdef
  set w : Bool → ℝ≥0 := fun b =>
    if b then unitInterval.toNNReal (p e) else unitInterval.toNNReal (σ (p e)) with hwdef
  have hdec : ∀ T : Set (Set E × Set E), ν T = ∑ i : Bool, ∑ j : Bool,
      (w i : ℝ≥0∞) * w j * ν (Prod.map (f i) (f j) ⁻¹' T) := fun T =>
    prodBernoulli_prod_apply_eq_sum_bool p e T
  have hagree : ∀ i j (ω : Set E × Set E) a, a ≠ e →
      (a ∈ ω.1 ↔ a ∈ f i ω.1) ∧ (a ∈ ω.2 ↔ a ∈ f j ω.2) := by
    intro i j ω a ha
    cases i <;> cases j <;> simp [f, ha]
  have hc : ∀ i j (ω : Set E × Set E), Prod.map (f i) (f j) ω ∈ C ↔ ω ∈ C := by
    intro i j ω
    constructor
    · exact hC _ _ ω.1 ω.2 fun a ha =>
        ⟨(hagree i j ω a ha).1.symm, (hagree i j ω a ha).2.symm⟩
    · exact hC ω.1 ω.2 _ _ (hagree i j ω)
  have hH0 : ∀ i j (x y : Set E), f i x ∩ S₀ ∪ f j y \ S₀ = f j (x ∩ S₀ ∪ y \ S₀) := by
    intro i j x y
    ext a
    by_cases ha : a = e
    · subst ha
      cases i <;> cases j <;> simp [f, he]
    · cases i <;> cases j <;> simp [f, ha]
  have hH1 : ∀ i j (x y : Set E),
      f i x ∩ insert e S₀ ∪ f j y \ insert e S₀ = f i (x ∩ S₀ ∪ y \ S₀) := by
    intro i j x y
    ext a
    by_cases ha : a = e
    · subst ha
      cases i <;> cases j <;> simp [f, he]
    · cases i <;> cases j <;> simp [f, ha]
  set K : Bool → Bool → Set (Set E × Set E) := fun a b => C ∩ {ω | ∃ I₁ J : Set E,
    I₁ ⊆ f a ω.1 ∧ (∀ z, I₁ ⊆ z → z ∈ A) ∧ J ⊆ f b (ω.1 ∩ S₀ ∪ ω.2 \ S₀) ∧
      (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ S₀ᶜ} with hKdef
  set L : Bool → Set (Set E × Set E) := fun a => C ∩ {ω | ∃ I₁ J : Set E,
    I₁ ⊆ f a ω.1 ∧ (∀ z, I₁ ⊆ z → z ∈ A) ∧ J ⊆ f a (ω.1 ∩ S₀ ∪ ω.2 \ S₀) ∧
      (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ (insert e S₀)ᶜ} with hLdef
  have hpre0 : ∀ i j, Prod.map (f i) (f j) ⁻¹' (C ∩ {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧
      (∀ z, I₁ ⊆ z → z ∈ A) ∧ J ⊆ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∧ (∀ z, J ⊆ z → z ∈ B) ∧
        I₁ ∩ J ⊆ S₀ᶜ}) = K i j := by
    intro i j
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hc, Prod.map_fst, Prod.map_snd, hH0,
      K]
  have hpre1 : ∀ i j, Prod.map (f i) (f j) ⁻¹' (C ∩ {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧
      (∀ z, I₁ ⊆ z → z ∈ A) ∧ J ⊆ ω.1 ∩ insert e S₀ ∪ ω.2 \ insert e S₀ ∧
        (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ (insert e S₀)ᶜ}) = L i := by
    intro i j
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hc, Prod.map_fst, Prod.map_snd, hH1,
      L]
  have hft : ∀ x : Set E, f false x = x \ {e} := fun x => rfl
  have htt : ∀ x : Set E, f true x = insert e x := fun x => rfl
  have hL0 : L false = K false false := by
    ext ω
    simp only [L, K, mem_inter_iff, mem_ofPred_eq, hft]
    refine and_congr_right fun _ => exists_congr fun I₁ => exists_congr fun J => ?_
    refine and_congr_right fun hI => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ?_
    have heI : e ∉ I₁ := fun h => (hI h).2 rfl
    constructor
    · exact fun h a ha => fun hs => h ha (mem_insert_of_mem _ hs)
    · intro h a ha hs
      rcases hs with rfl | hs
      · exact heI ha.1
      · exact h ha hs
  have hL1 : L true = K true false ∪ K false true := by
    ext ω
    simp only [L, K, mem_inter_iff, mem_union, mem_ofPred_eq, hft, htt]
    constructor
    · rintro ⟨hω, I₁, J, hI, hA, hJ, hB, hIJ⟩
      have hS₀ : I₁ ∩ J ⊆ S₀ᶜ := fun a ha hs => hIJ ha (mem_insert_of_mem _ hs)
      by_cases heJ : e ∈ J
      · have heI : e ∉ I₁ := fun h => hIJ ⟨h, heJ⟩ (mem_insert _ _)
        refine Or.inr ⟨hω, I₁, J, fun a ha => ⟨?_, ?_⟩, hA, hJ, hB, hS₀⟩
        · rcases hI ha with rfl | h
          · exact absurd ha heI
          · exact h
        · rintro rfl
          exact heI ha
      · refine Or.inl ⟨hω, I₁, J, hI, hA, fun a ha => ⟨?_, ?_⟩, hB, hS₀⟩
        · rcases hJ ha with rfl | h
          · exact absurd ha heJ
          · exact h
        · rintro rfl
          exact heJ ha
    · rintro (⟨hω, I₁, J, hI, hA, hJ, hB, hIJ⟩ | ⟨hω, I₁, J, hI, hA, hJ, hB, hIJ⟩)
      · refine ⟨hω, I₁, J, hI, hA, fun a ha => mem_insert_of_mem _ (hJ ha).1, hB, ?_⟩
        intro a ha hs
        rcases hs with rfl | hs
        · exact (hJ ha.2).2 rfl
        · exact hIJ ha hs
      · refine ⟨hω, I₁, J, fun a ha => mem_insert_of_mem _ (hI ha).1, hA, hJ, hB, ?_⟩
        intro a ha hs
        rcases hs with rfl | hs
        · exact (hI ha.1).2 rfl
        · exact hIJ ha hs
  have hfsub : ∀ x, f false x ⊆ f true x := fun x => by
    simp only [f]
    exact sdiff_subset.trans (subset_insert _ _)
  have hKmono : ∀ a b a' b', (a = true ∨ a = a') → (b = true ∨ b = b') →
      K a' b' ⊆ K a b := by
    rintro a b a' b' ha hb ω ⟨hω, I₁, J, hI, hA, hJ, hB, hIJ⟩
    refine ⟨hω, I₁, J, ?_, hA, ?_, hB, hIJ⟩
    · rcases ha with rfl | rfl
      · cases a' <;> [exact hI.trans (hfsub _); exact hI]
      · exact hI
    · rcases hb with rfl | rfl
      · cases b' <;> [exact hJ.trans (hfsub _); exact hJ]
      · exact hJ
  have hmeasK : MeasurableSet (K false true) := (Set.to_countable _).measurableSet
  have key : ν (K true false ∪ K false true) + ν (K false false) ≤
      ν (K true false) + ν (K false true) := by
    rw [← measure_union_add_inter _ hmeasK]
    gcongr
    exact subset_inter (hKmono _ _ _ _ (Or.inl rfl) (Or.inr rfl))
      (hKmono _ _ _ _ (Or.inr rfl) (Or.inl rfl))
  have hU : K true false ∪ K false true ⊆ K true true :=
    union_subset (hKmono _ _ _ _ (Or.inl rfl) (Or.inl rfl))
      (hKmono _ _ _ _ (Or.inl rfl) (Or.inl rfl))
  rw [hdec, hdec]
  simp only [hpre0, hpre1, hL0, hL1, Fintype.sum_bool]
  calc (w true : ℝ≥0∞) * w true * ν (K true false ∪ K false true) +
        w true * w false * ν (K true false ∪ K false true) +
        (w false * w true * ν (K false false) + w false * w false * ν (K false false))
      = w true * w true * ν (K true false ∪ K false true) +
          w false * w false * ν (K false false) +
          w true * w false * (ν (K true false ∪ K false true) + ν (K false false)) := by ring
    _ ≤ w true * w true * ν (K true true) + w false * w false * ν (K false false) +
          w true * w false * (ν (K true false) + ν (K false true)) := by
        gcongr _ * ?_ + _ + _ * ?_
        exact measure_mono hU
    _ = _ := by ring

section Tree

variable {n : ℕ} (next : (k : Fin n) → (Fin k.val → Bool × Bool) → E)
  (share : (k : Fin n) → (Fin k.val → Bool × Bool) → Bool)
  (answers : Set E × Set E → Fin n → Bool × Bool)

/-- **Histories depend only on their queried coordinates.** If the first `k` revealed pairs on
`ω` form the history `h`, and `ω'` agrees with `ω` on every coordinate that `h` queries, then the
first `k` revealed pairs on `ω'` also form `h`. -/
theorem answers_eq_of_agree
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (k : Fin n) (h : Fin k.val → Bool × Bool) {ω ω' : Set E × Set E}
    (hω : (fun i : Fin k.val => answers ω ⟨i.val, i.isLt.trans k.isLt⟩) = h)
    (hagree : ∀ (j : Fin n) (hj : j < k),
      (next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω.1 ↔
        next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω'.1) ∧
      (next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω.2 ↔
        next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω'.2)) :
    (fun i : Fin k.val => answers ω' ⟨i.val, i.isLt.trans k.isLt⟩) = h := by
  suffices H : ∀ m (hm : m < k.val), answers ω' ⟨m, hm.trans k.isLt⟩ = h ⟨m, hm⟩ by
    funext i
    exact H i.val i.isLt
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  set j : Fin n := ⟨m, hm.trans k.isLt⟩ with hjdef
  have hj : j < k := hm
  have hω' : (fun i : Fin j.val => answers ω' ⟨i.val, i.isLt.trans j.isLt⟩) =
      fun i => h ⟨i.val, i.isLt.trans hj⟩ := funext fun i => ih i.val i.isLt _
  have hωj : (fun i : Fin j.val => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) =
      fun i => h ⟨i.val, i.isLt.trans hj⟩ :=
    funext fun i => congrFun hω ⟨i.val, i.isLt.trans hj⟩
  have hhm : answers ω j = h ⟨m, hm⟩ := congrFun hω ⟨m, hm⟩
  rw [← hhm]
  obtain ⟨ha1, ha2⟩ := hagree j hj
  refine Prod.ext (Bool.eq_iff_iff.2 ?_) (Bool.eq_iff_iff.2 ?_)
  · rw [(hrun ω' j).1, (hrun ω j).1, hω', hωj]
    exact ha1.symm
  · rw [(hrun ω' j).2, (hrun ω j).2, hω', hωj]
    exact ha2.symm

/-- **Unsharing one step, for any event family.** Let `F S` be events of the pair `(X, Y)`
indexed by a shared set `S`, such that on every event `C` not depending on the two bits at a
coordinate `e ∉ S₀`, adding `e` to `S₀` does not decrease `P(C ∩ F S₀)`. Let `S₀` and `S₁` be
the sets shared by a predictable sharing tree strictly before step `k` and up to step `k`. Then
`P(F S₀) ≤ P(F S₁)`. -/
theorem prodBernoulli_prod_le_of_step [Fintype E] (p : E → unitInterval)
    (F : Set E → Set (Set E × Set E))
    (hF : ∀ (e : E) (S₀ : Set E) (C : Set (Set E × Set E)),
      (∀ x y x' y' : Set E, (∀ a, a ≠ e → (a ∈ x ↔ a ∈ x') ∧ (a ∈ y ↔ a ∈ y')) →
        (x, y) ∈ C → (x', y') ∈ C) → e ∉ S₀ →
      (prodBernoulli p).prod (prodBernoulli p) (C ∩ F S₀) ≤
        (prodBernoulli p).prod (prodBernoulli p) (C ∩ F (insert e S₀)))
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (k : Fin n) (S₀ S₁ : Set E × Set E → Set E)
    (hS₀ : ∀ ω e, e ∈ S₀ ω ↔ ∃ j : Fin n, j < k ∧
      share j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = true ∧
        next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e)
    (hS₁ : ∀ ω e, e ∈ S₁ ω ↔ ∃ j : Fin n, j ≤ k ∧
      share j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = true ∧
        next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e) :
    (prodBernoulli p).prod (prodBernoulli p) {ω | ω ∈ F (S₀ ω)} ≤
      (prodBernoulli p).prod (prodBernoulli p) {ω | ω ∈ F (S₁ ω)} := by
  classical
  set ν := (prodBernoulli p).prod (prodBernoulli p) with hν
  set g : Set E × Set E → (Fin k.val → Bool × Bool) :=
    fun ω i => answers ω ⟨i.val, i.isLt.trans k.isLt⟩ with hgdef
  have hsplit : ∀ T : Set (Set E × Set E), ν T = ∑ h, ν (T ∩ g ⁻¹' {h}) := by
    intro T
    have := sum_measure_preimage_singleton (μ := ν.restrict T) Finset.univ (f := g)
      (fun _ _ => (Set.to_countable _).measurableSet)
    simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at this
    rw [← this]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Measure.restrict_apply (Set.to_countable _).measurableSet, inter_comm]
  rw [hsplit, hsplit]
  refine Finset.sum_le_sum fun h _ => ?_
  have hhist : ∀ ω ∈ g ⁻¹' {h}, ∀ (j : Fin n) (hj : j < k),
      (fun i : Fin j.val => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) =
        fun i => h ⟨i.val, i.isLt.trans hj⟩ := by
    intro ω hω j hj
    funext i
    exact congrFun hω ⟨i.val, i.isLt.trans hj⟩
  set S₀' : Set E := {e | ∃ (j : Fin n) (hj : j < k),
    share j (fun i => h ⟨i.val, i.isLt.trans hj⟩) = true ∧
      next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) = e} with hS₀'
  have h₀ : ∀ ω ∈ g ⁻¹' {h}, S₀ ω = S₀' := by
    intro ω hω
    ext e
    rw [hS₀]
    constructor
    · rintro ⟨j, hj, hs⟩
      rw [hhist ω hω j hj] at hs
      exact ⟨j, hj, hs⟩
    · rintro ⟨j, hj, hs⟩
      refine ⟨j, hj, ?_⟩
      rw [hhist ω hω j hj]
      exact hs
  have h₁ : ∀ ω ∈ g ⁻¹' {h}, S₁ ω = S₀' ∪ {e | share k h = true ∧ next k h = e} := by
    intro ω hω
    have hk : (fun i : Fin k.val => answers ω ⟨i.val, i.isLt.trans k.isLt⟩) = h := hω
    ext e
    rw [hS₁, mem_union, ← h₀ ω hω, hS₀, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hs⟩
      rcases hj.lt_or_eq with hj | rfl
      · exact Or.inl ⟨j, hj, hs⟩
      · rw [hk] at hs
        exact Or.inr hs
    · rintro (⟨j, hj, hs⟩ | hs)
      · exact ⟨j, hj.le, hs⟩
      · exact ⟨k, le_rfl, by rw [hk]; exact hs⟩
  have hT : ∀ (S : Set E × Set E → Set E) (S' : Set E), (∀ ω ∈ g ⁻¹' {h}, S ω = S') →
      {ω | ω ∈ F (S ω)} ∩ g ⁻¹' {h} = g ⁻¹' {h} ∩ F S' := by
    intro S S' hS
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [← hS ω h2]
      exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      change ω ∈ F (S ω)
      rw [hS ω h2]
      exact h1
  rw [hT S₀ S₀' h₀, hT S₁ _ h₁]
  cases hsk : share k h
  · simp
  · simp only [true_and, ofPred_eq_eq_singleton', union_singleton]
    rcases (g ⁻¹' {h}).eq_empty_or_nonempty with hempty | ⟨ω₀, hω₀⟩
    · simp [hempty]
    have hk0 : (fun i : Fin k.val => answers ω₀ ⟨i.val, i.isLt.trans k.isLt⟩) = h := hω₀
    refine hF (next k h) S₀' _ ?_ ?_
    · intro x y x' y' hxy hmem
      refine answers_eq_of_agree next answers hrun k h hmem fun j hj => ?_
      have hne : next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ≠ next k h := by
        have := hfresh (answers ω₀) k (by rw [hk0]; exact hsk) j hj
        rwa [hk0, hhist ω₀ hω₀ j hj] at this
      exact hxy _ hne
    · rintro ⟨j, hj, -, hn⟩
      have := hfresh (answers ω₀) k (by rw [hk0]; exact hsk) j hj
      rw [hk0, hhist ω₀ hω₀ j hj] at this
      exact this hn

/-- **Removing all sharing, for any event family.** Let `F S` be events of the pair `(X, Y)`
indexed by a shared set `S` such that, on every event not depending on the two bits at a
coordinate `e ∉ S₀`, adding `e` to `S₀` does not decrease the probability. For a predictable
sharing tree with shared set `S`, `P(F ∅) ≤ P(F S)`. -/
theorem prodBernoulli_prod_le_of_sharingTree [Fintype E] (p : E → unitInterval)
    (F : Set E → Set (Set E × Set E))
    (hF : ∀ (e : E) (S₀ : Set E) (C : Set (Set E × Set E)),
      (∀ x y x' y' : Set E, (∀ a, a ≠ e → (a ∈ x ↔ a ∈ x') ∧ (a ∈ y ↔ a ∈ y')) →
        (x, y) ∈ C → (x', y') ∈ C) → e ∉ S₀ →
      (prodBernoulli p).prod (prodBernoulli p) (C ∩ F S₀) ≤
        (prodBernoulli p).prod (prodBernoulli p) (C ∩ F (insert e S₀)))
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e) :
    (prodBernoulli p).prod (prodBernoulli p) (F ∅) ≤
      (prodBernoulli p).prod (prodBernoulli p) {ω | ω ∈ F (S ω)} := by
  classical
  set T : ℕ → Set E × Set E → Set E := fun m ω => {e | ∃ j : Fin n, j.val < m ∧
      share j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = true ∧
        next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e} with hTdef
  have hT0 : ∀ ω, T 0 ω = ∅ := fun ω => by
    ext e
    simp [T]
  have hTn : ∀ ω, T n ω = S ω := fun ω => by
    ext e
    rw [hS]
    simp only [T, mem_ofPred_eq]
    exact exists_congr fun j => by simp [j.isLt]
  have hmono : ∀ m ≤ n, (prodBernoulli p).prod (prodBernoulli p) {ω | ω ∈ F (T 0 ω)} ≤
        (prodBernoulli p).prod (prodBernoulli p) {ω | ω ∈ F (T m ω)} := by
    intro m
    induction m with
    | zero => exact fun _ => le_rfl
    | succ m ih =>
      intro hm
      refine (ih (by omega)).trans ?_
      exact prodBernoulli_prod_le_of_step next share answers p F hF hrun hfresh ⟨m, hm⟩
        (T m) (T (m + 1)) (fun ω e => Iff.rfl)
        (fun ω e => exists_congr fun j => and_congr_left'
          (by rw [Fin.le_iff_val_le_val]; exact Nat.lt_succ_iff))
  have h := hmono n le_rfl
  simp only [hT0, hTn] at h
  exact h

/-- **Adaptive Harris inequality.** Let `E` be finite, `μ = prodBernoulli p`, and let
`ω = (X, Y)` have law `μ ⊗ μ`, read by a predictable sharing tree (`next`, `share`, `answers`)
with shared set `S` as in `prodBernoulli_prod_map_predictableSwap`. If `A, B` are both
increasing or both decreasing, then `μ(A) μ(B) ≤ P(X ∈ A, X ∩ S ∪ Y \ S ∈ B)`. -/
theorem prodBernoulli_mul_le_prod_hybrid [Fintype E] (p : E → unitInterval)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e)
    {A B : Set (Set E)}
    (hAB : (IsUpperSet A ∧ IsUpperSet B) ∨ (IsLowerSet A ∧ IsLowerSet B)) :
    prodBernoulli p A * prodBernoulli p B ≤
      (prodBernoulli p).prod (prodBernoulli p) {ω | ω.1 ∈ A ∧ ω.1 ∩ S ω ∪ ω.2 \ S ω ∈ B} := by
  have h := prodBernoulli_prod_le_of_sharingTree next share answers p
    (fun S₀ => {ω | ω.1 ∈ A ∧ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∈ B})
    (fun e S₀ C hC he => prodBernoulli_prod_hybrid_le_insert p e hC he hAB) hrun hfresh S hS
  simp only [inter_empty, empty_union, sdiff_empty] at h
  refine le_of_eq_of_le ?_ h
  rw [← Measure.prod_prod]
  rfl

/-- **Adaptive BK inequality.** Let `E` be finite, `μ = prodBernoulli p`, and let `ω = (X, Y)`
have law `μ ⊗ μ`, read by a predictable sharing tree (`next`, `share`, `answers`) with shared set
`S` as in `prodBernoulli_prod_map_predictableSwap`. Let `H = X ∩ S ∪ Y \ S`. The probability
that there are witnesses `I ⊆ X` for `A` and `J ⊆ H` for `B` (every configuration containing
the witness lies in the event) with `I ∩ J` disjoint from `S` is at most `μ(A) μ(B)`. -/
theorem prodBernoulli_prod_sharedWitness_le_mul [Fintype E] (p : E → unitInterval)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e)
    (A B : Set (Set E)) :
    (prodBernoulli p).prod (prodBernoulli p)
        {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧ (∀ z, I₁ ⊆ z → z ∈ A) ∧
          J ⊆ ω.1 ∩ S ω ∪ ω.2 \ S ω ∧ (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ (S ω)ᶜ} ≤
      prodBernoulli p A * prodBernoulli p B := by
  classical
  set ν := (prodBernoulli p).prod (prodBernoulli p) with hνdef
  set K : Set E → Set (Set E × Set E) := fun S₀ => {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧
    (∀ z, I₁ ⊆ z → z ∈ A) ∧ J ⊆ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∧ (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ S₀ᶜ}
    with hKdef
  have hmeas : ∀ T : Set (Set E × Set E), MeasurableSet T := fun T =>
    (Set.to_countable T).measurableSet
  have hF : ∀ (e : E) (S₀ : Set E) (C : Set (Set E × Set E)),
      (∀ x y x' y' : Set E, (∀ a, a ≠ e → (a ∈ x ↔ a ∈ x') ∧ (a ∈ y ↔ a ∈ y')) →
        (x, y) ∈ C → (x', y') ∈ C) → e ∉ S₀ →
      ν (C ∩ (K S₀)ᶜ) ≤ ν (C ∩ (K (insert e S₀))ᶜ) := by
    intro e S₀ C hC he
    have h := prodBernoulli_prod_sharedWitness_insert_le p e hC he A B
    have h₀ := measure_inter_add_sdiff (μ := ν) C (hmeas (K S₀))
    have h₁ := measure_inter_add_sdiff (μ := ν) C (hmeas (K (insert e S₀)))
    rw [← sdiff_eq, ← sdiff_eq,
      ENNReal.eq_sub_of_add_eq (measure_ne_top ν _) ((add_comm _ _).trans h₀),
      ENNReal.eq_sub_of_add_eq (measure_ne_top ν _) ((add_comm _ _).trans h₁)]
    exact tsub_le_tsub_left h _
  have h := prodBernoulli_prod_le_of_sharingTree next share answers p (fun S₀ => (K S₀)ᶜ) hF
    hrun hfresh S hS
  change ν (K ∅)ᶜ ≤ ν {ω | ω ∈ K (S ω)}ᶜ at h
  rw [prob_compl_eq_one_sub (hmeas _), prob_compl_eq_one_sub (hmeas _),
    ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top] at h
  refine h.trans ?_
  rw [← Measure.prod_prod]
  refine measure_mono ?_
  rintro ω ⟨I₁, J, hI, hA, hJ, hB, -⟩
  simp only [inter_empty, empty_union, sdiff_empty] at hJ
  exact ⟨hA _ hI, hB _ hJ⟩

end Tree

end PercLib.Probability
