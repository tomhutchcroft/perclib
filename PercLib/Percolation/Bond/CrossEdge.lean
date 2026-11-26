/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs (the cross-edge estimate), written on 2026-11-20. No upstream proof is copied and no
definition is added.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.Cylinder
public import PercLib.Probability.HarrisDecreasing
public import Mathlib.Probability.Independence.Integration

/-!
# The cross-edge estimate

Let `S, T` be disjoint finite vertex sets and `W` a finite set of pairs containing no pair
between `S` and `T` (for instance `W = S.sym2 ∪ T.sym2`). Let `C, D ⊆ S, T` be random finite
sets and `H ≥ 0` a weight, all three depending only on `ω ∩ W`. Then, by independence of the
pairs inside `W` from the pairs between `S` and `T`, and a sum over the values of `(C, D)`,

`E[H 1{some pair between C and D is open}] = E[H (1 - ∏_{u ∈ C, v ∈ D} (1 - q s(u,v)))]`

(`lintegral_crossEdge_eq`). If every pair between `S` and `T` is open with probability at
least `1 - e^{-r}`, this gives `E[H (1 - e^{-r |C| |D|})] ≤ E[H 1{…}]`
(`lintegral_crossEdge_ge_exp`). The case `H = F(ω ∩ S.sym2) G(ω ∩ T.sym2)` is the
three-block form.

Auxiliary statements: a function of `ω ∩ W` with `W` finite is measurable
(`measurable_of_determined_finite`), and the expectation of a product of functions
determined by disjoint sets of pairs factors (`lintegral_mul_of_determined`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A function of the configuration determined by a finite set of pairs is measurable. -/
theorem measurable_of_determined_finite {W : Set (Sym2 V)} (hW : W.Finite) {β : Type*}
    [MeasurableSpace β] {f : Config V → β} (hf : ∀ ω, f ω = f (ω ∩ W)) : Measurable f := by
  intro s _
  have : Finite W := hW.to_subtype
  have hpre : f ⁻¹' s = (fun ω : Config V => fun k : W => (k : Sym2 V) ∈ ω) ⁻¹'
      {g | f {x | ∃ hx : x ∈ W, g ⟨x, hx⟩} ∈ s} := by
    ext ω
    have hset : {x | ∃ hx : x ∈ W, x ∈ ω} = ω ∩ W := by
      ext x
      simp [and_comm]
    simp only [mem_preimage, mem_ofPred_eq, hset]
    rw [← hf ω]
  rw [hpre]
  exact (measurable_pi_iff.2 fun k => measurable_set_mem _) (Set.to_countable _).measurableSet

/-- An event determined by a finite set of pairs is measurable. -/
theorem measurableSet_of_determined_finite {W : Set (Sym2 V)} (hW : W.Finite)
    {A : Set (Config V)} (hA : ∀ ω, ω ∈ A ↔ ω ∩ W ∈ A) : MeasurableSet A :=
  measurableSet_setOfPred.2 (measurable_of_determined_finite hW fun ω => propext (hA ω))

/-- **Product of determined functions.** Measurable `ℝ≥0∞`-valued functions determined by
disjoint sets of pairs are independent: the expectation of their product factors. -/
theorem lintegral_mul_of_determined (q : Sym2 V → unitInterval) {P Q : Set (Sym2 V)}
    (hPQ : Disjoint P Q) {f g : Config V → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfP : ∀ ω, f ω = f (ω ∩ P)) (hgQ : ∀ ω, g ω = g (ω ∩ Q)) :
    ∫⁻ ω, f ω * g ω ∂law q = (∫⁻ ω, f ω ∂law q) * ∫⁻ ω, g ω ∂law q := by
  have hind := PercLib.Probability.prodBernoulli_indepFun_block_observables q P Q hPQ
    (fun η : Set P => f (Subtype.val '' η)) (fun η : Set Q => g (Subtype.val '' η))
    (hf.comp (PercLib.Probability.measurable_image_val P))
    (hg.comp (PercLib.Probability.measurable_image_val Q))
  have himg : ∀ (R : Set (Sym2 V)) (ω : Config V),
      (Subtype.val '' {i : R | (i : Sym2 V) ∈ ω} : Set (Sym2 V)) = ω ∩ R := by
    intro R ω
    ext e
    simp [and_comm]
  have hf' : (fun ω : Config V => f (Subtype.val '' {i : P | (i : Sym2 V) ∈ ω})) = f := by
    funext ω
    rw [himg, ← hfP]
  have hg' : (fun ω : Config V => g (Subtype.val '' {i : Q | (i : Sym2 V) ∈ ω})) = g := by
    funext ω
    rw [himg, ← hgQ]
  rw [hf', hg'] at hind
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hf.aemeasurable hg.aemeasurable
    hind

/-- The probability that every pair of a finite set is closed is the product of the closing
probabilities. -/
theorem law_all_closed_eq (q : Sym2 V → unitInterval) (F : Finset (Sym2 V)) :
    law q {ω | ∀ e ∈ F, e ∉ ω} =
      ∏ e ∈ F, (unitInterval.toNNReal (unitInterval.symm (q e)) : ℝ≥0∞) := by
  have hset : {ω : Config V | ∀ e ∈ F, e ∉ ω} =
      {ω | ωᶜ ∈ {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'}} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe, Set.mem_compl_iff]
  have hmeas : MeasurableSet {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'} := by
    have : {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'} = ⋂ e ∈ F, {ω' | e ∈ ω'} := by
      ext ω; simp [Set.subset_def]
    rw [this]
    exact Finset.measurableSet_biInter F fun e _ => measurableSet_mem e
  rw [hset, law, PercLib.Probability.prodBernoulli_preimage_compl _ hmeas,
    PercLib.Probability.prodBernoulli_subset]

/-- **Cross-edge identity.** Let `S, T` be disjoint finite vertex sets and `W` a finite set of
pairs with no pair between `S` and `T`. Let `H ≥ 0` and the random sets `C ⊆ S`, `D ⊆ T`
depend only on `ω ∩ W`. Then
`E[H; some pair between C and D is open] = E[H (1 - ∏_{u ∈ C} ∏_{v ∈ D} (1 - q s(u,v)))]`. -/
theorem lintegral_crossEdge_eq (q : Sym2 V → unitInterval) {S T : Finset V}
    (hST : Disjoint S T) {W : Set (Sym2 V)} (hW : W.Finite)
    (hWST : ∀ u ∈ S, ∀ v ∈ T, s(u, v) ∉ W)
    {H : Config V → ℝ≥0∞} {C D : Config V → Finset V}
    (hH : ∀ ω, H ω = H (ω ∩ W)) (hC : ∀ ω, C ω = C (ω ∩ W)) (hD : ∀ ω, D ω = D (ω ∩ W))
    (hCS : ∀ ω, C ω ⊆ S) (hDT : ∀ ω, D ω ⊆ T) :
    ∫⁻ ω in {ω | ∃ u ∈ C ω, ∃ v ∈ D ω, s(u, v) ∈ ω}, H ω ∂law q =
      ∫⁻ ω, H ω * (1 - ∏ u ∈ C ω, ∏ v ∈ D ω,
        (unitInterval.toNNReal (unitInterval.symm (q s(u, v))) : ℝ≥0∞)) ∂law q := by
  classical
  set E : Set (Config V) := {ω | ∃ u ∈ C ω, ∃ v ∈ D ω, s(u, v) ∈ ω} with hE
  let F : Finset V × Finset V → Finset (Sym2 V) := fun p =>
    (p.1 ×ˢ p.2).image fun x => s(x.1, x.2)
  let P : Finset (Finset V × Finset V) := S.powerset ×ˢ T.powerset
  let A : Finset V × Finset V → Set (Config V) := fun p => {ω | C ω = p.1 ∧ D ω = p.2}
  let Ep : Finset V × Finset V → Set (Config V) := fun p =>
    {ω | ∃ u ∈ p.1, ∃ v ∈ p.2, s(u, v) ∈ ω}
  let π : Finset V × Finset V → ℝ≥0∞ := fun p => ∏ u ∈ p.1, ∏ v ∈ p.2,
    (unitInterval.toNNReal (unitInterval.symm (q s(u, v))) : ℝ≥0∞)
  have hWW : ∀ ω : Config V, ω ∩ W ∩ W = ω ∩ W := fun ω => by rw [inter_assoc, inter_self]
  -- measurability
  have hHm : Measurable H := measurable_of_determined_finite hW hH
  have hAdet : ∀ p ω, ω ∈ A p ↔ ω ∩ W ∈ A p := by
    intro p ω
    simp only [A, mem_ofPred_eq]
    rw [← hC ω, ← hD ω]
  have hAm : ∀ p, MeasurableSet (A p) := fun p =>
    measurableSet_of_determined_finite hW (hAdet p)
  have hFfin : ∀ p, ((F p : Finset (Sym2 V)) : Set (Sym2 V)).Finite := fun p =>
    Finset.finite_toSet _
  have hEpdet : ∀ p ω, ω ∈ Ep p ↔ ω ∩ (F p : Set (Sym2 V)) ∈ Ep p := by
    intro p ω
    simp only [Ep, mem_ofPred_eq, mem_inter_iff, Finset.mem_coe]
    constructor
    · rintro ⟨u, hu, v, hv, h⟩
      exact ⟨u, hu, v, hv, h, Finset.mem_image.2 ⟨(u, v), Finset.mem_product.2 ⟨hu, hv⟩, rfl⟩⟩
    · rintro ⟨u, hu, v, hv, h, -⟩
      exact ⟨u, hu, v, hv, h⟩
  have hEpm : ∀ p, MeasurableSet (Ep p) := fun p =>
    measurableSet_of_determined_finite (hFfin p) (hEpdet p)
  -- the pairs between `S` and `T` are not in `W`
  have hdisj : ∀ p ∈ P, Disjoint W (F p : Set (Sym2 V)) := by
    intro p hp
    simp only [P, Finset.mem_product, Finset.mem_powerset] at hp
    refine Set.disjoint_left.2 fun e he heF => ?_
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 heF)
    rw [Finset.mem_product] at huv
    exact hWST u (hp.1 huv.1) v (hp.2 huv.2) he
  -- the probability of a direct open pair
  have hlawEp : ∀ p ∈ P, law q (Ep p) = 1 - π p := by
    intro p hp
    simp only [P, Finset.mem_product, Finset.mem_powerset] at hp
    have hcompl : Ep p = {ω | ∀ e ∈ F p, e ∉ ω}ᶜ := by
      ext ω
      simp only [Ep, F, mem_ofPred_eq, mem_compl_iff, Finset.mem_image, Finset.mem_product]
      constructor
      · rintro ⟨u, hu, v, hv, h⟩ hall
        exact hall _ ⟨(u, v), ⟨hu, hv⟩, rfl⟩ h
      · intro h
        by_contra hne
        push Not at hne
        refine h ?_
        rintro e ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
        exact hne u hu v hv
    have hmeas : MeasurableSet {ω : Config V | ∀ e ∈ F p, e ∉ ω} := by
      have : {ω : Config V | ∀ e ∈ F p, e ∉ ω} = ⋂ e ∈ F p, {ω | e ∈ ω}ᶜ := by
        ext ω; simp
      rw [this]
      exact Finset.measurableSet_biInter _ fun e _ => (measurableSet_mem e).compl
    rw [hcompl, prob_compl_eq_one_sub hmeas, law_all_closed_eq]
    congr 1
    simp only [π, F]
    rw [Finset.prod_image, Finset.prod_product]
    rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
    simp only [Finset.coe_product, mem_prod, Finset.mem_coe] at huv huv'
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext h1 h2
    · have h1' : u = v' := h1
      exact (Finset.disjoint_left.1 hST (hp.1 huv.1) (by rw [h1']; exact hp.2 huv'.2)).elim
  -- the partition according to the values of `(C, D)`
  have hpart : ∀ (g : Config V → ℝ≥0∞) ω, ∑ p ∈ P, (A p).indicator g ω = g ω := by
    intro g ω
    rw [Finset.sum_eq_single (C ω, D ω)]
    · exact indicator_of_mem (show ω ∈ A (C ω, D ω) from ⟨rfl, rfl⟩) g
    · intro p _ hp
      exact indicator_of_notMem (fun h => hp (Prod.ext h.1.symm h.2.symm)) g
    · intro h
      exact absurd (Finset.mem_product.2 ⟨Finset.mem_powerset.2 (hCS ω),
        Finset.mem_powerset.2 (hDT ω)⟩) h
  have hsplit : ∀ g : Config V → ℝ≥0∞, Measurable g →
      ∫⁻ ω, g ω ∂law q = ∑ p ∈ P, ∫⁻ ω, (A p).indicator g ω ∂law q := by
    intro g hg
    rw [← lintegral_finsetSum _ (fun p _ => hg.indicator (hAm p))]
    exact lintegral_congr fun ω => (hpart g ω).symm
  -- measurability of the two integrands
  set FST : Set (Sym2 V) := (F (S, T) : Set (Sym2 V)) with hFST
  have hEdet : ∀ ω, ω ∈ E ↔ ω ∩ (W ∪ FST) ∈ E := by
    intro ω
    have h1 : ω ∩ (W ∪ FST) ∩ W = ω ∩ W := by
      rw [inter_assoc, inter_eq_right.2 subset_union_left]
    simp only [hE, mem_ofPred_eq]
    rw [hC (ω ∩ (W ∪ FST)), hD (ω ∩ (W ∪ FST)), h1, ← hC, ← hD]
    constructor
    · rintro ⟨u, hu, v, hv, h⟩
      refine ⟨u, hu, v, hv, h, Or.inr ?_⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(u, v), Finset.mem_product.2
        ⟨hCS ω hu, hDT ω hv⟩, rfl⟩)
    · rintro ⟨u, hu, v, hv, h, -⟩
      exact ⟨u, hu, v, hv, h⟩
  have hEm : MeasurableSet E :=
    measurableSet_of_determined_finite (hW.union (Finset.finite_toSet _)) hEdet
  have hRm : Measurable fun ω => H ω * (1 - π (C ω, D ω)) := by
    refine measurable_of_determined_finite hW fun ω => ?_
    rw [← hH, ← hC, ← hD]
  -- assembly
  rw [← lintegral_indicator hEm, hsplit _ (hHm.indicator hEm), hsplit _ hRm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hl : ∀ ω, (A p).indicator (E.indicator H) ω =
      (A p).indicator H ω * (Ep p).indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ A p
    · obtain ⟨h1, h2⟩ := hω
      have hEE : ω ∈ E ↔ ω ∈ Ep p := by
        simp only [hE, Ep, mem_ofPred_eq, h1, h2]
      rw [indicator_of_mem (show ω ∈ A p from ⟨h1, h2⟩),
        indicator_of_mem (show ω ∈ A p from ⟨h1, h2⟩)]
      by_cases hω' : ω ∈ Ep p
      · rw [indicator_of_mem (hEE.2 hω'), indicator_of_mem hω', Pi.one_apply, mul_one]
      · rw [indicator_of_notMem (fun h => hω' (hEE.1 h)), indicator_of_notMem hω', mul_zero]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
  have hr : ∀ ω, (A p).indicator (fun ω => H ω * (1 - π (C ω, D ω))) ω =
      (A p).indicator H ω * (1 - π p) := by
    intro ω
    by_cases hω : ω ∈ A p
    · obtain ⟨h1, h2⟩ := hω
      rw [indicator_of_mem (show ω ∈ A p from ⟨h1, h2⟩),
        indicator_of_mem (show ω ∈ A p from ⟨h1, h2⟩), h1, h2]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
  have hAHm : Measurable ((A p).indicator H) := hHm.indicator (hAm p)
  rw [lintegral_congr hl, lintegral_congr hr, lintegral_mul_const _ hAHm,
    lintegral_mul_of_determined q (hdisj p hp) hAHm (measurable_one.indicator (hEpm p)),
    lintegral_indicator_one (hEpm p), hlawEp p hp]
  · intro ω
    by_cases hω : ω ∈ A p
    · rw [indicator_of_mem hω, indicator_of_mem ((hAdet p ω).1 hω), ← hH]
    · rw [indicator_of_notMem hω, indicator_of_notMem fun h => hω ((hAdet p ω).2 h)]
  · intro ω
    by_cases hω : ω ∈ Ep p
    · rw [indicator_of_mem hω, indicator_of_mem ((hEpdet p ω).1 hω)]
      rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem fun h => hω ((hEpdet p ω).2 h)]

/-- One closing probability bounded by `e^{-r}` in `ℝ≥0∞`. -/
theorem coe_toNNReal_symm_le_ofReal_exp {x : unitInterval} {r : ℝ}
    (hx : 1 - Real.exp (-r) ≤ (x : ℝ)) :
    (unitInterval.toNNReal (unitInterval.symm x) : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-r)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  change 1 - (x : ℝ) ≤ Real.exp (-r)
  linarith

/-- **Cross-edge estimate, exponential form.** Under the hypotheses of
`lintegral_crossEdge_eq`, if every pair between `S` and `T` is open with probability at least
`1 - e^{-r}`, then `E[H (1 - e^{-r |C| |D|})] ≤ E[H; some pair between C and D is open]`. -/
theorem lintegral_crossEdge_ge_exp (q : Sym2 V → unitInterval) {S T : Finset V}
    (hST : Disjoint S T) {W : Set (Sym2 V)} (hW : W.Finite)
    (hWST : ∀ u ∈ S, ∀ v ∈ T, s(u, v) ∉ W)
    {H : Config V → ℝ≥0∞} {C D : Config V → Finset V}
    (hH : ∀ ω, H ω = H (ω ∩ W)) (hC : ∀ ω, C ω = C (ω ∩ W)) (hD : ∀ ω, D ω = D (ω ∩ W))
    (hCS : ∀ ω, C ω ⊆ S) (hDT : ∀ ω, D ω ⊆ T) {r : ℝ}
    (hq : ∀ u ∈ S, ∀ v ∈ T, 1 - Real.exp (-r) ≤ (q s(u, v) : ℝ)) :
    ∫⁻ ω, H ω * ENNReal.ofReal (1 - Real.exp (-(r * (C ω).card * (D ω).card))) ∂law q ≤
      ∫⁻ ω in {ω | ∃ u ∈ C ω, ∃ v ∈ D ω, s(u, v) ∈ ω}, H ω ∂law q := by
  rw [lintegral_crossEdge_eq q hST hW hWST hH hC hD hCS hDT]
  refine lintegral_mono fun ω => mul_le_mul' le_rfl ?_
  have hprod : ∏ u ∈ C ω, ∏ v ∈ D ω,
      (unitInterval.toNNReal (unitInterval.symm (q s(u, v))) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (-(r * (C ω).card * (D ω).card))) := by
    calc ∏ u ∈ C ω, ∏ v ∈ D ω,
          (unitInterval.toNNReal (unitInterval.symm (q s(u, v))) : ℝ≥0∞)
        ≤ ∏ _u ∈ C ω, ∏ _v ∈ D ω, ENNReal.ofReal (Real.exp (-r)) :=
          Finset.prod_le_prod fun u hu => Finset.prod_le_prod fun v hv =>
            coe_toNNReal_symm_le_ofReal_exp (hq u (hCS ω hu) v (hDT ω hv))
      _ = ENNReal.ofReal (Real.exp (-(r * (C ω).card * (D ω).card))) := by
          rw [Finset.prod_const, Finset.prod_const, ← pow_mul,
            ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hprod 1

end PercLib.Percolation.Bond
