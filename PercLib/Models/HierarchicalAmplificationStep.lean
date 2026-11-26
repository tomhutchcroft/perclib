/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Models.HierarchicalAmplification
public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.Tightness.FiniteQuantile
public import PercLib.Percolation.Bond.Tightness.FromBK
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Probability.DeterministicModification
public import PercLib.Probability.OpenEventHarris
public import PercLib.Models.HierarchicalCutoff

/-!
# Hierarchical block-quantile amplification: the assembly

Part 1 (`HierarchicalAmplification.lean`) proved the scale, the no-direct-edge bound, the
connection threshold, the amplification arithmetic and the Hoeffding count. This file
assembles them.

* `measurableSet_of_determined`: an event determined by a finite set of pairs is measurable,
  so the independence lemmas of `DeterminedIndependence.lean` apply to it.
* `law_restrict_apply`: the law of the profile restricted to a set `W` of pairs is the law
  of `ω ∩ W`.
* `lt_tightnessScale_of_blocks` (**the amplification step on any vertex set**): if a finite
  set is split into `N` disjoint blocks whose restricted quantiles are at least `R ≥ 2`, and
  two sets of size `R - 1` in different blocks fail to be joined by a direct open pair with
  probability at most `1/(2N²)`, and `e^{-N/(8e)} ≤ 1/4`, then the restricted quantile of
  the union exceeds `⌈N/(2e)⌉ (R - 1)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models

open PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Events determined by finite blocks -/

/-- An event determined by a finite set `S` of pairs is measurable. -/
theorem measurableSet_of_determined {S : Set (Sym2 V)} (hS : S.Finite) {E : Set (Config V)}
    (hE : ∀ ω, ω ∈ E ↔ ω ∩ S ∈ E) : MeasurableSet E := by
  have : Finite S := hS.to_subtype
  have hpre : E = (fun ω : Config V => fun k : S => (k : Sym2 V) ∈ ω) ⁻¹'
      {f | {x | ∃ hx : x ∈ S, f ⟨x, hx⟩} ∈ E} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, exists_prop]
    rw [hE ω]
    constructor <;> intro h <;> convert h using 2 <;> ext x <;> simp [and_comm]
  rw [hpre]
  exact (measurable_pi_iff.2 fun k => measurable_set_mem _) (Set.to_countable _).measurableSet

/-- The law of the profile restricted to a set `W` of pairs is the law of `ω ∩ W`. -/
theorem law_restrict_apply (q : Sym2 V → unitInterval) (W : Set (Sym2 V))
    [DecidablePred (· ∈ W)] {A : Set (Config V)} (hA : MeasurableSet A) :
    law (fun e => if e ∈ W then q e else 0) A = law q {ω | ω ∩ W ∈ A} := by
  rw [law, ← PercLib.Probability.prodBernoulli_map_inter q W, Measure.map_apply (by fun_prop) hA]
  rfl

/-! ### One pair of blocks -/

/-- **One pair of blocks.** Let `Λᵢ, Λⱼ` be disjoint finite vertex sets, `Gᵢ, Gⱼ` events and
`Cᵢ, Cⱼ` random subsets of `Λᵢ, Λⱼ`, each determined by the pairs inside its block, with
`|Cᵢ| ≥ r` on `Gᵢ` and `|Cⱼ| ≥ r` on `Gⱼ`. If any two sets of size at least `r` in the two
blocks fail to be joined by a direct open pair with probability at most `ε`, then so do
`Cᵢ` and `Cⱼ` on `Gᵢ ∩ Gⱼ`. -/
theorem law_bad_pair_le [DecidableEq V] (q : Sym2 V → unitInterval) {Λi Λj : Finset V}
    (hij : Disjoint Λi Λj) {Gi Gj : Set (Config V)} {Ci Cj : Config V → Finset V} {r : ℕ}
    {ε : ℝ≥0∞}
    (hGi : ∀ ω, ω ∈ Gi ↔ ω ∩ (Λi : Set V).sym2 ∈ Gi)
    (hGj : ∀ ω, ω ∈ Gj ↔ ω ∩ (Λj : Set V).sym2 ∈ Gj)
    (hCi : ∀ ω, Ci ω = Ci (ω ∩ (Λi : Set V).sym2)) (hCj : ∀ ω, Cj ω = Cj (ω ∩ (Λj : Set V).sym2))
    (hCiΛ : ∀ ω, Ci ω ⊆ Λi) (hCjΛ : ∀ ω, Cj ω ⊆ Λj)
    (hci : ∀ ω ∈ Gi, r ≤ (Ci ω).card) (hcj : ∀ ω ∈ Gj, r ≤ (Cj ω).card)
    (hedge : ∀ X Y : Finset V, X ⊆ Λi → Y ⊆ Λj → r ≤ X.card → r ≤ Y.card →
      law q {ω | ∀ u ∈ X, ∀ v ∈ Y, s(u, v) ∉ ω} ≤ ε) :
    law q {ω | ω ∈ Gi ∧ ω ∈ Gj ∧ ∀ u ∈ Ci ω, ∀ v ∈ Cj ω, s(u, v) ∉ ω} ≤ ε := by
  set Si : Set (Sym2 V) := (Λi : Set V).sym2
  set Sj : Set (Sym2 V) := (Λj : Set V).sym2
  set SS : Set (Sym2 V) := Si ∪ Sj with hSS
  have hSSfin : SS.Finite := by
    refine Set.Finite.union ?_ ?_
    · change ((Λi : Set V).sym2).Finite
      rw [← Finset.coe_sym2]; exact Finset.finite_toSet _
    · change ((Λj : Set V).sym2).Finite
      rw [← Finset.coe_sym2]; exact Finset.finite_toSet _
  have hi_eq : ∀ ω : Config V, ω ∩ SS ∩ Si = ω ∩ Si := fun ω => by
    rw [inter_assoc, inter_eq_right.2 subset_union_left]
  have hj_eq : ∀ ω : Config V, ω ∩ SS ∩ Sj = ω ∩ Sj := fun ω => by
    rw [inter_assoc, inter_eq_right.2 subset_union_right]
  set P := (Λi.powerset.filter fun X => r ≤ X.card) ×ˢ (Λj.powerset.filter fun Y => r ≤ Y.card)
  let D : Finset V × Finset V → Set (Config V) := fun p =>
    {ω | ω ∈ Gi ∧ ω ∈ Gj ∧ Ci ω = p.1 ∧ Cj ω = p.2}
  let NE : Finset V × Finset V → Set (Config V) := fun p =>
    {ω | ∀ u ∈ p.1, ∀ v ∈ p.2, s(u, v) ∉ ω}
  let T : Finset V × Finset V → Set (Sym2 V) := fun p =>
    ((p.1 ×ˢ p.2).image fun x => s(x.1, x.2) : Finset (Sym2 V))
  have hDdet : ∀ p ω, ω ∈ D p ↔ ω ∩ SS ∈ D p := by
    intro p ω
    simp only [D, mem_ofPred_eq]
    rw [hGi (ω ∩ SS), hGj (ω ∩ SS), hi_eq, hj_eq, hCi (ω ∩ SS), hCj (ω ∩ SS), hi_eq, hj_eq,
      ← hGi, ← hGj, ← hCi, ← hCj]
  have hNEdet : ∀ p ω, ω ∈ NE p ↔ ω ∩ T p ∈ NE p := by
    intro p ω
    simp only [NE, T, mem_ofPred_eq, mem_inter_iff, Finset.coe_image, Finset.coe_product,
      mem_image, mem_prod, Finset.mem_coe, not_and]
    constructor
    · intro h u hu v hv hω _
      exact h u hu v hv hω
    · intro h u hu v hv hω
      exact h u hu v hv hω ⟨(u, v), ⟨hu, hv⟩, rfl⟩
  have hdisjT : ∀ p ∈ P, Disjoint SS (T p) := by
    intro p hp
    simp only [P, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    refine Set.disjoint_left.2 fun e he heT => ?_
    simp only [T, Finset.coe_image, Finset.coe_product, mem_image, mem_prod,
      Finset.mem_coe] at heT
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := heT
    have hu' : u ∈ Λi := hp.1.1 hu
    have hv' : v ∈ Λj := hp.2.1 hv
    rcases he with he | he
    · exact Finset.disjoint_left.1 hij ((Set.mk_mem_sym2_iff.1 he).2) hv'
    · exact Finset.disjoint_left.1 hij hu' ((Set.mk_mem_sym2_iff.1 he).1)
  have hsub : {ω | ω ∈ Gi ∧ ω ∈ Gj ∧ ∀ u ∈ Ci ω, ∀ v ∈ Cj ω, s(u, v) ∉ ω} ⊆
      ⋃ p ∈ P, D p ∩ NE p := by
    rintro ω ⟨hωi, hωj, hω⟩
    refine mem_iUnion₂.2 ⟨(Ci ω, Cj ω), ?_, ⟨hωi, hωj, rfl, rfl⟩, hω⟩
    simp only [P, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨hCiΛ ω, hci ω hωi⟩, ⟨hCjΛ ω, hcj ω hωj⟩⟩
  have hDmeas : ∀ p, MeasurableSet (D p) := fun p => measurableSet_of_determined hSSfin (hDdet p)
  have hDdisj : PairwiseDisjoint (↑P : Set (Finset V × Finset V)) D := by
    intro p _ p' _ hpp'
    refine Set.disjoint_left.2 fun ω h h' => hpp' ?_
    obtain ⟨_, _, h1, h2⟩ := h
    obtain ⟨_, _, h1', h2'⟩ := h'
    exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')
  calc law q {ω | ω ∈ Gi ∧ ω ∈ Gj ∧ ∀ u ∈ Ci ω, ∀ v ∈ Cj ω, s(u, v) ∉ ω}
      ≤ ∑ p ∈ P, law q (D p ∩ NE p) := (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ p ∈ P, law q (D p) * law q (NE p) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        exact PercLib.Probability.prodBernoulli_inter_of_determined q (hdisjT p hp) (hDmeas p)
          (measurableSet_of_determined (Finset.finite_toSet _) (hNEdet p))
          (fun ω ω' h => by rw [hDdet p ω, hDdet p ω', h])
          (fun ω ω' h => by rw [hNEdet p ω, hNEdet p ω', h])
    _ ≤ ∑ p ∈ P, law q (D p) * ε := by
        refine Finset.sum_le_sum fun p hp => ?_
        gcongr
        simp only [P, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
        exact hedge p.1 p.2 hp.1.1 hp.2.1 hp.1.2 hp.2.2
    _ = law q (⋃ p ∈ P, D p) * ε := by
        rw [← Finset.sum_mul, measure_biUnion_finset hDdisj fun p _ => hDmeas p]
    _ ≤ 1 * ε := by gcongr; exact prob_le_one
    _ = ε := one_mul ε

/-! ### The amplification step on any vertex set -/

open Classical in
/-- **Amplification step.** Let a finite vertex set `U = ⋃ᵢ Λᵢ` be split into `N ≥ 1` pairwise
disjoint blocks, and write `q_W` for the profile `q` restricted to the pairs inside `W`. If
the quantile of every block is at least `R ≥ 2`, if two sets of size at least `R - 1` in two
different blocks have no open pair between them with probability at most `1/(2N²)`, and if
`e^{-N/(8e)} ≤ 1/4`, then `⌈N/(2e)⌉ (R - 1) < tightnessScale q_U U`.

With probability at least `3/4` more than `N/(2e)` blocks are good (Hoeffding), and with
probability at least `3/4` the chosen large clusters of any two good blocks are joined by a
direct open pair; so the largest cluster of `U` has size at least `⌈N/(2e)⌉ (R - 1)` with
probability at least `1/2 > e^{-1}`. -/
theorem lt_tightnessScale_of_blocks [Countable V] [DecidableEq V] (q : Sym2 V → unitInterval)
    {N : ℕ} (hN : 0 < N) (Λ : Fin N → Finset V) (hdisj : Pairwise (Function.onFun Disjoint Λ))
    {R : ℕ} (hR2 : 2 ≤ R)
    (hR : ∀ i, R ≤ tightnessScale (fun e => if e ∈ (Λ i : Set V).sym2 then q e else 0) (Λ i))
    (hedge : ∀ i j, i ≠ j → ∀ X Y : Finset V, X ⊆ Λ i → Y ⊆ Λ j → R - 1 ≤ X.card →
      R - 1 ≤ Y.card → law q {ω | ∀ u ∈ X, ∀ v ∈ Y, s(u, v) ∉ ω} ≤
        ENNReal.ofReal (1 / (2 * (N : ℝ) ^ 2)))
    (hexp : Real.exp (-((N : ℝ) / (8 * Real.exp 1))) ≤ 1 / 4) :
    ⌈(N : ℝ) / (2 * Real.exp 1)⌉₊ * (R - 1) <
      tightnessScale (fun e => if e ∈ ((Finset.univ.biUnion Λ : Finset V) : Set V).sym2
        then q e else 0) (Finset.univ.biUnion Λ) := by
  set U := Finset.univ.biUnion Λ with hU
  set Si : Fin N → Set (Sym2 V) := fun i => (Λ i : Set V).sym2 with hSi
  set SU : Set (Sym2 V) := (U : Set V).sym2 with hSU
  set m := ⌈(N : ℝ) / (2 * Real.exp 1)⌉₊ * (R - 1) with hm
  have hΛU : ∀ i, Λ i ⊆ U := fun i => Finset.subset_biUnion_of_mem Λ (Finset.mem_univ i)
  have hSiU : ∀ i, Si i ⊆ SU := fun i e he => Set.mem_sym2_iff_subset.2
    ((Set.mem_sym2_iff_subset.1 he).trans (Finset.coe_subset.2 (hΛU i)))
  have hfinS : ∀ i, (Si i).Finite := fun i => by
    simp only [hSi]; rw [← Finset.coe_sym2]; exact Finset.finite_toSet _
  have hSdisj : Pairwise (Function.onFun Disjoint Si) := by
    intro i j hij
    refine Set.disjoint_left.2 fun e hi hj => ?_
    induction e using Sym2.ind with
    | _ a b =>
      exact Finset.disjoint_left.1 (hdisj hij) (Set.mk_mem_sym2_iff.1 hi).1
        (Set.mk_mem_sym2_iff.1 hj).1
  -- good blocks
  set G : Fin N → Set (Config V) :=
    fun i => {ω | R - 1 ≤ maxClusterIntersection (Λ i) (ω ∩ Si i)} with hG
  have hGdet : ∀ i ω, ω ∈ G i ↔ ω ∩ Si i ∈ G i := by
    intro i ω
    simp only [hG, mem_ofPred_eq, inter_assoc, inter_self]
  have hGmeas : ∀ i, MeasurableSet (G i) := fun i =>
    measurableSet_of_determined (hfinS i) (hGdet i)
  have hGprob : ∀ i, ENNReal.ofReal (Real.exp (-1)) < law q (G i) := by
    intro i
    have h := lt_law_max_tail_of_lt_tightnessScale
      (fun e => if e ∈ (Λ i : Set V).sym2 then q e else 0) (Λ i) (n := R - 1)
      (lt_of_lt_of_le (by omega) (hR i))
    rwa [law_restrict_apply q (Si i) (measurableSet_le_maxClusterIntersection _ _)] at h
  have hind : iIndepSet G (law q) := by
    rw [iIndepSet_iff_meas_biInter hGmeas]
    intro s
    exact PercLib.Probability.prodBernoulli_biInter_of_determined q s
      (fun i _ j _ hij => hSdisj hij) (fun i _ => hGmeas i)
      (fun i ω ω' h => by rw [hGdet i ω, hGdet i ω', h])
  -- many good blocks
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have he1 : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  set t : ℝ := N * Real.exp (-1) - N / (2 * Real.exp 1) with ht_def
  have ht_eq : t = N / (2 * Real.exp 1) := by
    rw [ht_def, he1]; field_simp; ring
  have ht : 0 ≤ t := by rw [ht_eq]; positivity
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin N)), Real.exp (-1) ≤ (law q).real (G i) := by
    intro i _
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (hGprob i).le
  have hH := measure_count_le_le hGmeas hind Finset.univ hp ht
  simp only [Finset.card_univ, Fintype.card_fin] at hH
  have hH' := hH.trans ((exp_neg_two_mul_sq_le hNpos).trans hexp)
  set B1 : Set (Config V) :=
    {ω | ∑ i, (G i).indicator (fun _ => (1 : ℝ)) ω ≤ N * Real.exp (-1) - t} with hB1_def
  have hB1 : law q B1 ≤ ENNReal.ofReal (1 / 4) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hH'
  -- the chosen cluster of a block
  let C : Fin N → Config V → Finset V := fun i ω =>
    if h : ∃ v ∈ Λ i, R - 1 ≤ ((Λ i).filter fun w => w ∈ cluster (ω ∩ Si i) v).card
    then (Λ i).filter fun w => w ∈ cluster (ω ∩ Si i) h.choose else ∅
  have hCdet : ∀ i ω, C i ω = C i (ω ∩ Si i) := by
    intro i ω
    simp only [C, inter_assoc, inter_self]
  have hCsub : ∀ i ω, C i ω ⊆ Λ i := by
    intro i ω
    simp only [C]
    split_ifs
    · exact Finset.filter_subset _ _
    · exact Finset.empty_subset _
  have hCgood : ∀ i, ∀ ω ∈ G i, R - 1 ≤ (C i ω).card ∧
      ∀ w ∈ C i ω, ∀ w' ∈ C i ω, ω ∩ Si i ∈ conn w w' := by
    intro i ω hω
    have hex : ∃ v ∈ Λ i, R - 1 ≤ ((Λ i).filter fun w => w ∈ cluster (ω ∩ Si i) v).card := by
      have h1 : R - 1 ≤ maxClusterIntersection (Λ i) (ω ∩ Si i) := hω
      rw [maxClusterIntersection, Finset.le_sup_iff (by simp only [bot_eq_zero']; omega)] at h1
      obtain ⟨v, hv, hle⟩ := h1
      refine ⟨v, hv, hle.trans (le_of_eq ?_)⟩
      rw [← Set.ncard_coe_finset, Finset.coe_filter]
      congr 1
      ext w
      simp [and_comm]
    simp only [C, hex, ↓reduceDIte]
    refine ⟨hex.choose_spec.2, fun w hw w' hw' => ?_⟩
    simp only [Finset.mem_filter] at hw hw'
    exact conn_trans (by rw [conn_symm]; exact hw.2) hw'.2
  -- no two good blocks fail to be joined
  set Bp : Fin N → Fin N → Set (Config V) := fun i j =>
    {ω | ω ∈ G i ∧ ω ∈ G j ∧ ∀ u ∈ C i ω, ∀ v ∈ C j ω, s(u, v) ∉ ω} with hBp_def
  have hBp : ∀ i j, i ≠ j → law q (Bp i j) ≤ ENNReal.ofReal (1 / (2 * (N : ℝ) ^ 2)) :=
    fun i j hij => law_bad_pair_le q (hdisj hij) (hGdet i) (hGdet j) (hCdet i) (hCdet j)
      (hCsub i) (hCsub j) (fun ω h => (hCgood i ω h).1) (fun ω h => (hCgood j ω h).1)
      (hedge i j hij)
  set B2 : Set (Config V) := ⋃ i, ⋃ j, ⋃ (_ : i < j), Bp i j with hB2_def
  have hcount : 2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => p.1 < p.2)).card ≤ N ^ 2 := by
    have hswap : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)).card =
        ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)).card := by
      refine Finset.card_bij (fun p _ => p.swap) (by simp) (by simp) ?_
      intro p hp
      exact ⟨p.swap, by simpa using hp, by simp⟩
    have hdis : Disjoint ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2))
        ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)) :=
      Finset.disjoint_filter.2 fun p _ h1 h2 => lt_asymm h1 h2
    have h := Finset.card_le_univ (((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => p.1 < p.2)) ∪ ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => p.2 < p.1)))
    rw [Finset.card_union_of_disjoint hdis, hswap, Fintype.card_prod, Fintype.card_fin] at h
    nlinarith
  have hB2 : law q B2 ≤ ENNReal.ofReal (1 / 4) := by
    calc law q B2 ≤ ∑ i, ∑ j, law q (⋃ (_ : i < j), Bp i j) :=
          (measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _)
      _ ≤ ∑ i, ∑ j, (if i < j then ENNReal.ofReal (1 / (2 * (N : ℝ) ^ 2)) else 0) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          split_ifs with hij
          · exact (measure_mono (iUnion_subset fun _ => subset_rfl)).trans (hBp i j hij.ne)
          · simp [hij]
      _ = ∑ p : Fin N × Fin N, (if p.1 < p.2 then ENNReal.ofReal (1 / (2 * (N : ℝ) ^ 2))
            else 0) := (Fintype.sum_prod_type' _).symm
      _ = ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)).card *
            ENNReal.ofReal (1 / (2 * (N : ℝ) ^ 2)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hc : (2 : ℝ) * ((Finset.univ : Finset (Fin N × Fin N)).filter
              (fun p => p.1 < p.2)).card ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcount
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith
  -- outside `B1 ∪ B2` the union of the chosen clusters lies in one cluster
  have hgood : (B1 ∪ B2)ᶜ ⊆ {ω | m ≤ maxClusterIntersection U (ω ∩ SU)} := by
    intro ω hω
    simp only [mem_compl_iff, mem_union, not_or] at hω
    obtain ⟨h1, h2⟩ := hω
    set g := (Finset.univ : Finset (Fin N)).filter fun i => ω ∈ G i with hg_def
    have hsum : ∑ i, (G i).indicator (fun _ => (1 : ℝ)) ω = g.card := by
      simp only [Set.indicator_apply, hg_def]
      rw [Finset.sum_boole]
    have hg : (N : ℝ) / (2 * Real.exp 1) < g.card := by
      have h1' : ¬ (∑ i, (G i).indicator (fun _ => (1 : ℝ)) ω ≤ N * Real.exp (-1) - t) := h1
      rw [hsum, not_le] at h1'
      have hval : (N : ℝ) * Real.exp (-1) - t = N / (2 * Real.exp 1) := by
        rw [ht_eq, he1]; field_simp; ring
      rwa [hval] at h1'
    have hK : ⌈(N : ℝ) / (2 * Real.exp 1)⌉₊ ≤ g.card := Nat.ceil_le.2 hg.le
    have hgne : g.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < g.card := lt_of_le_of_lt (by positivity) hg
      exact_mod_cast this
    obtain ⟨i₀, hi₀⟩ := hgne
    have hi₀G : ω ∈ G i₀ := (Finset.mem_filter.1 hi₀).2
    have hC₀ := hCgood i₀ ω hi₀G
    have hC₀ne : (C i₀ ω).Nonempty := by
      rw [← Finset.card_pos]; have := hC₀.1; omega
    obtain ⟨v₀, hv₀⟩ := hC₀ne
    have hmono : ∀ k, ω ∩ Si k ⊆ ω ∩ SU := fun k => inter_subset_inter_right _ (hSiU k)
    have hconn : ∀ i ∈ g, ∀ w ∈ C i ω, ω ∩ SU ∈ conn v₀ w := by
      intro i hi w hw
      have hiG : ω ∈ G i := (Finset.mem_filter.1 hi).2
      by_cases hii : i = i₀
      · subst hii
        exact conn_mono (hmono i) (hC₀.2 v₀ hv₀ w hw)
      · obtain ⟨u, hu, u', hu', hedge'⟩ : ∃ u ∈ C i ω, ∃ u' ∈ C i₀ ω, s(u, u') ∈ ω := by
          rcases lt_or_gt_of_ne hii with hlt | hlt
          · have hnot : ω ∉ Bp i i₀ := fun hb =>
              h2 (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨i₀, mem_iUnion.2 ⟨hlt, hb⟩⟩⟩)
            simp only [hBp_def, mem_ofPred_eq, not_and, not_forall, not_not] at hnot
            obtain ⟨u, hu, u', hu', h⟩ := hnot hiG hi₀G
            exact ⟨u, hu, u', hu', h⟩
          · have hnot : ω ∉ Bp i₀ i := fun hb =>
              h2 (mem_iUnion.2 ⟨i₀, mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hlt, hb⟩⟩⟩)
            simp only [hBp_def, mem_ofPred_eq, not_and, not_forall, not_not] at hnot
            obtain ⟨u', hu', u, hu, h⟩ := hnot hi₀G hiG
            exact ⟨u, hu, u', hu', by rw [Sym2.eq_swap]; exact h⟩
        have hne : u ≠ u' := fun h =>
          Finset.disjoint_left.1 (hdisj hii) (hCsub i ω hu) (h ▸ hCsub i₀ ω hu')
        have hU' : s(u, u') ∈ SU :=
          Set.mk_mem_sym2_iff.2 ⟨Finset.mem_coe.2 (hΛU i (hCsub i ω hu)),
            Finset.mem_coe.2 (hΛU i₀ (hCsub i₀ ω hu'))⟩
        have c1 : ω ∩ SU ∈ conn v₀ u' := conn_mono (hmono i₀) (hC₀.2 v₀ hv₀ u' hu')
        have c2 : ω ∩ SU ∈ conn u' u :=
          mem_conn_of_mem hne.symm (by rw [Sym2.eq_swap]; exact ⟨hedge', hU'⟩)
        have c3 : ω ∩ SU ∈ conn u w := conn_mono (hmono i) ((hCgood i ω hiG).2 u hu w hw)
        exact conn_trans (conn_trans c1 c2) c3
    have hv₀U : v₀ ∈ U := hΛU i₀ (hCsub i₀ ω hv₀)
    have hsub : g.biUnion (fun i => C i ω) ⊆ U.filter (fun w => w ∈ cluster (ω ∩ SU) v₀) := by
      intro w hw
      obtain ⟨i, hi, hw⟩ := Finset.mem_biUnion.1 hw
      exact Finset.mem_filter.2 ⟨hΛU i (hCsub i ω hw), hconn i hi w hw⟩
    have hcardU : (g.biUnion fun i => C i ω).card = ∑ i ∈ g, (C i ω).card :=
      Finset.card_biUnion fun i _ j _ hij => (hdisj hij).mono (hCsub i ω) (hCsub j ω)
    have hlow : g.card * (R - 1) ≤ ∑ i ∈ g, (C i ω).card := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun i hi => (hCgood i ω (Finset.mem_filter.1 hi).2).1
    have hZ : (U.filter (fun w => w ∈ cluster (ω ∩ SU) v₀)).card ≤
        maxClusterIntersection U (ω ∩ SU) := by
      unfold maxClusterIntersection
      refine le_trans (le_of_eq ?_)
        (Finset.le_sup (f := fun v => (cluster (ω ∩ SU) v ∩ (U : Set V)).ncard) hv₀U)
      rw [← Set.ncard_coe_finset, Finset.coe_filter]
      congr 1
      ext w
      simp [and_comm]
    change m ≤ _
    calc m ≤ g.card * (R - 1) := Nat.mul_le_mul_right _ hK
      _ ≤ ∑ i ∈ g, (C i ω).card := hlow
      _ = (g.biUnion fun i => C i ω).card := hcardU.symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := hZ
  -- the probability of a large cluster is at least `1/2 > e^{-1}`
  have hprob : ENNReal.ofReal (Real.exp (-1)) <
      law q {ω | m ≤ maxClusterIntersection U (ω ∩ SU)} := by
    have hc : law q (B1 ∪ B2) ≤ ENNReal.ofReal (1 / 2) := by
      refine (measure_union_le _ _).trans ?_
      calc law q B1 + law q B2 ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) :=
            add_le_add hB1 hB2
        _ = ENNReal.ofReal (1 / 2) := by
            rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    have h1 : (1 : ℝ≥0∞) ≤ law q {ω | m ≤ maxClusterIntersection U (ω ∩ SU)} +
        ENNReal.ofReal (1 / 2) := by
      calc (1 : ℝ≥0∞) = law q ((B1 ∪ B2)ᶜ ∪ (B1 ∪ B2)) := by
            rw [compl_union_self, measure_univ]
        _ ≤ law q (B1 ∪ B2)ᶜ + law q (B1 ∪ B2) := measure_union_le _ _
        _ ≤ _ := add_le_add (measure_mono hgood) hc
    have h2 : ENNReal.ofReal (1 / 2) ≤ law q {ω | m ≤ maxClusterIntersection U (ω ∩ SU)} := by
      have hhalf : ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
      rw [hhalf]
      exact tsub_le_iff_right.2 h1
    have h3 : ENNReal.ofReal (Real.exp (-1)) < ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
      have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      rw [Real.exp_neg]
      calc (Real.exp 1)⁻¹ < (2 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) he
        _ = 1 / 2 := by norm_num
    exact h3.trans_le h2
  by_contra hcon
  push Not at hcon
  have h := law_max_tail_le_of_tightnessScale_le _ U hcon
  rw [law_restrict_apply q SU (measurableSet_le_maxClusterIntersection _ _)] at h
  exact absurd h (not_le.2 hprob)

/-! ### Transport of the quantile -/

/-- **Transport of the quantile.** If `q' (σ e) = q e` for a bijection `σ`, the quantile of
`σ(Λ)` under `q'` equals the quantile of `Λ` under `q`. -/
theorem tightnessScale_map_equiv {W : Type*} (σ : V ≃ W) (q : Sym2 V → unitInterval)
    (q' : Sym2 W → unitInterval) (hq : ∀ e, q' (Sym2.map σ e) = q e) (Λ : Finset V) :
    tightnessScale q' (Λ.map σ.toEmbedding) = tightnessScale q Λ := by
  have hlaw : (law q).map (fun ω => Sym2.map σ '' ω) = law q' := by
    have himg : (fun ω : Config V => Sym2.map σ '' ω) =
        fun ω => (Sym2.map σ.symm.toEmbedding ⁻¹' ω : Config W) := by
      funext ω
      ext e
      exact mem_image_sym2Map_iff σ ω e
    rw [himg, law_map_preimage_sym2Map]
    congr 1
    funext e
    have h := hq (Sym2.map σ.symm e)
    rw [Sym2.map_map, σ.self_comp_symm, Sym2.map_id, id] at h
    exact h.symm
  have hZ : ∀ ω : Config V, maxClusterIntersection (Λ.map σ.toEmbedding) (Sym2.map σ '' ω) =
      maxClusterIntersection Λ ω := by
    intro ω
    unfold maxClusterIntersection
    rw [Finset.sup_map]
    congr 1
    funext v
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, Finset.coe_map]
    rw [cluster_image, ← Set.image_inter σ.injective, Set.ncard_image_of_injective _ σ.injective]
  unfold tightnessScale
  congr 1
  ext k
  simp only [mem_ofPred_eq]
  rw [← hlaw, map_image_sym2Map_apply]
  have hpre : (fun ω : Config V => Sym2.map σ '' ω) ⁻¹'
      {ω | k ≤ maxClusterIntersection (Λ.map σ.toEmbedding) ω} =
      {ω | k ≤ maxClusterIntersection Λ ω} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, hZ]
  rw [hpre]

/-! ### The hierarchical lattice -/

section Hierarchical

variable {d L : ℕ}

/-- The level-`n` block of `x`, as the translate of the level-`n` block of the origin. -/
theorem coe_map_addLeft_level_ball [NeZero L] (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ) :
    (((finite_level_ball n).toFinset.map (Equiv.addLeft x).toEmbedding :
      Finset (ℕ →₀ (Fin d → ZMod L))) : Set (ℕ →₀ (Fin d → ZMod L))) =
      {y | (y - x).support.sup Nat.succ ≤ n} := by
  rw [Finset.coe_map, Set.Finite.coe_toFinset, level_ball_eq_translate]
  rfl

/-- The level-`n` block of the origin has `L^{dn}` vertices. -/
theorem card_toFinset_level_ball [NeZero L] (n : ℕ) :
    (finite_level_ball (A := Fin d → ZMod L) n).toFinset.card = (L ^ d) ^ n := by
  rw [← Nat.card_eq_finsetCard, ← card_ball (d := d) (L := L) n]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun z => by simp)

/-- Within a level-`m` block, two vertices first share a block of level at most `m`. -/
theorem level_sub_le_of_mem_level_ball {u v : ℕ →₀ (Fin d → ZMod L)} {m : ℕ}
    (hu : u.support.sup Nat.succ ≤ m) (hv : v.support.sup Nat.succ ≤ m) :
    (v - u).support.sup Nat.succ ≤ m := by
  have h := level_sub_le_max u 0 v
  rw [zero_sub, sub_zero, Finsupp.support_neg] at h
  exact h.trans (max_le hu hv)

open Classical in
/-- **Hierarchical block-quantile amplification.** On the hierarchical
lattice `ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, let `c, α > 0` and let `J` be a
translation-invariant kernel with `J(u, v) ≥ c L^{-(d+α)j}` when `u ≠ v` first share a
level-`j` block. Write `R_n(β)` for the quantile `tightnessScale` of the level-`n` block of the
origin under `q_β = intensityProfile J β` restricted to the pairs inside that block, and let
`N = L^{dℓ}` with `e^{-N/(8e)} ≤ 1/4` and `L^{(d-α)ℓ} ≥ 16e²`, and
`A = (4/c) L^{(d+α)ℓ} log(2N²)`. Then for every `β > 0` and `n ≥ 0`,
`R_n(β)² ≥ (A/β) L^{(d+α)n}` implies `R_{n+ℓ}(β)² ≥ (A/β) L^{(d+α)(n+ℓ)}`.

The hypotheses `ℓ ≥ 1` and `α < d` are not needed here: they serve only to produce
such an `ℓ` (`exists_amplification_scale`). The kernel bound is assumed for `u ≠ v` only. -/
theorem tightnessScale_hierarchical_amplification [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {β : ℝ≥0} (hβ : 0 < β) (n : ℕ)
    (hn : (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) /
        β * (L : ℝ) ^ (((d : ℝ) + α) * n) ≤
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2) :
    (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
        (L : ℝ) ^ (((d : ℝ) + α) * ((n : ℝ) + ℓ)) ≤
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n + ℓ}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball (n + ℓ)).toFinset : ℝ) ^ 2 := by
  set q := intensityProfile J β with hq_def
  let ball : ℕ → Finset (ℕ →₀ (Fin d → ZMod L)) := fun m => (finite_level_ball m).toFinset
  have hball : ∀ m, (ball m : Set (ℕ →₀ (Fin d → ZMod L))) =
      {z | z.support.sup Nat.succ ≤ m} := fun m => Set.Finite.coe_toFinset _
  have hmem : ∀ m z, z ∈ ball m ↔ z.support.sup Nat.succ ≤ m := fun m z => by
    rw [← Finset.mem_coe, hball]; rfl
  let sub : (ℕ →₀ (Fin d → ZMod L)) → Finset (ℕ →₀ (Fin d → ZMod L)) :=
    fun x => (ball n).map (Equiv.addLeft x).toEmbedding
  have hsub_mem : ∀ x y, y ∈ sub x ↔ (y - x).support.sup Nat.succ ≤ n := fun x y => by
    rw [← Finset.mem_coe, coe_map_addLeft_level_ball]; rfl
  set B := (ball (n + ℓ)).image sub with hB_def
  have hBsub : ∀ b ∈ B, b ⊆ ball (n + ℓ) := by
    intro b hb y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
    rw [hsub_mem] at hy
    rw [hmem] at hx ⊢
    have h := level_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le (hy.trans (Nat.le_add_right _ _)) hx)
  have hself : ∀ y, y ∈ sub y := fun y => by
    rw [hsub_mem, sub_self, Finsupp.support_zero, Finset.sup_empty]
    exact Nat.zero_le _
  have hBdisj : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b' := by
    intro b hb b' hb' hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨x', _, rfl⟩ := Finset.mem_image.1 hb'
    rcases level_balls_eq_or_disjoint x x' n with h | h
    · exact absurd (Finset.coe_inj.1 (by
        rw [coe_map_addLeft_level_ball, coe_map_addLeft_level_ball]; exact h)) hne
    · rw [← Finset.disjoint_coe, coe_map_addLeft_level_ball, coe_map_addLeft_level_ball]
      exact h
  have hUB : B.biUnion id = ball (n + ℓ) := by
    ext y
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨b, hb, hy⟩
      exact hBsub b hb hy
    · intro hy
      exact ⟨sub y, Finset.mem_image_of_mem _ hy, hself y⟩
  have hBcard : B.card = (L ^ d) ^ ℓ := by
    have h := Finset.card_biUnion (s := B) (t := id) fun b hb b' hb' hne => hBdisj b hb b' hb' hne
    rw [hUB] at h
    have hcb : ∀ b ∈ B, (id b).card = (L ^ d) ^ n := by
      intro b hb
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hb
      simp only [id, sub, Finset.card_map]
      exact card_toFinset_level_ball n
    rw [Finset.sum_congr rfl hcb, Finset.sum_const, smul_eq_mul] at h
    have h' : (finite_level_ball (A := Fin d → ZMod L) (n + ℓ)).toFinset.card =
        (L ^ d) ^ (n + ℓ) := card_toFinset_level_ball (n + ℓ)
    have hpos : 0 < (L ^ d) ^ n := pow_pos (pow_pos (by omega) _) _
    rw [h', pow_add] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h, mul_comm])).symm
  -- the blocks as a family indexed by `Fin N`
  set N := B.card with hN_def
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hNreal : (N : ℝ) = (L : ℝ) ^ (d * ℓ) := by
    rw [hBcard, ← pow_mul]; push_cast; ring
  have hNpos : 0 < N := by
    rw [hBcard]; exact pow_pos (pow_pos (by omega) _) _
  let Λ : Fin N → Finset (ℕ →₀ (Fin d → ZMod L)) := fun k => (B.equivFin.symm k).1
  have hΛB : ∀ k, Λ k ∈ B := fun k => (B.equivFin.symm k).2
  have hΛdisj : Pairwise (Function.onFun Disjoint Λ) := by
    intro k k' hkk'
    refine hBdisj _ (hΛB k) _ (hΛB k') fun h => hkk' ?_
    exact B.equivFin.symm.injective (Subtype.ext h)
  have hΛU : Finset.univ.biUnion Λ = ball (n + ℓ) := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hy⟩
      exact hBsub _ (hΛB k) hy
    · intro hy
      refine ⟨B.equivFin ⟨sub y, Finset.mem_image_of_mem _ hy⟩, ?_⟩
      simp only [Λ, Equiv.symm_apply_apply]
      exact hself y
  -- translation invariance of the quantile
  have hJσ : ∀ x e, J (Sym2.map (Equiv.addLeft x) e) = J e := by
    intro x e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Equiv.coe_addLeft]
      rw [add_comm x a, add_comm x b]
      exact hJt x a b
  have hqσ : ∀ x e, q (Sym2.map (Equiv.addLeft x) e) = q e := by
    intro x e
    apply Subtype.ext
    change 1 - Real.exp (-(β : ℝ) * (J (Sym2.map (Equiv.addLeft x) e) : ℝ)) =
      1 - Real.exp (-(β : ℝ) * (J e : ℝ))
    rw [hJσ]
  set R := tightnessScale (fun e => if e ∈ ((ball n : Finset _) : Set _).sym2 then q e else 0)
    (ball n) with hR_def
  have hRstmt : tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
      (finite_level_ball n).toFinset = R := by
    rw [hR_def, hball]
  rw [hRstmt] at hn
  have hR : ∀ k, R ≤ tightnessScale (fun e => if e ∈ (Λ k : Set _).sym2 then q e else 0)
      (Λ k) := by
    intro k
    obtain ⟨x, _, hx⟩ := Finset.mem_image.1 (hΛB k)
    rw [← hx]
    refine le_of_eq (tightnessScale_map_equiv (Equiv.addLeft x) _ _ ?_ (ball n)).symm
    intro e
    have hmemσ : Sym2.map (Equiv.addLeft x) e ∈ ((sub x : Finset _) : Set _).sym2 ↔
        e ∈ ((ball n : Finset _) : Set _).sym2 := by
      simp only [sub, Finset.coe_map, Equiv.coe_toEmbedding, Set.sym2_image]
      exact (Sym2.map.injective (Equiv.addLeft x).injective).mem_set_image
    by_cases he : e ∈ ((ball n : Finset _) : Set _).sym2
    · simp only [hmemσ, he, ↓reduceIte, hqσ]
    · simp only [hmemσ, he, ↓reduceIte]
  have hR2 : 2 ≤ R := two_le_tightnessScale _ ⟨0, (hmem n 0).2 (by simp)⟩
  -- the direct-edge bound between two blocks
  set a : ℝ := (d : ℝ) + α with ha_def
  have ha : 0 ≤ a := by positivity
  set j₀ : ℝ := c * (L : ℝ) ^ (-(a * ((n : ℝ) + ℓ))) with hj₀_def
  have hj₀ : 0 ≤ j₀ := by positivity
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR2
  have hRsub : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hN1 : (1 : ℝ) ≤ (L : ℝ) ^ (d * ℓ) := one_le_pow₀ hL1
  have hedge : ∀ k k', k ≠ k' → ∀ X Y : Finset (ℕ →₀ (Fin d → ZMod L)), X ⊆ Λ k →
      Y ⊆ Λ k' → R - 1 ≤ X.card → R - 1 ≤ Y.card →
      law q {ω | ∀ u ∈ X, ∀ v ∈ Y, s(u, v) ∉ ω} ≤ ENNReal.ofReal (1 / (2 * (N : ℝ) ^ 2)) := by
    intro k k' hkk' X Y hX hY hXc hYc
    set F := (X ×ˢ Y).image fun p => s(p.1, p.2) with hF_def
    have hset : {ω : Config (ℕ →₀ (Fin d → ZMod L)) | ∀ u ∈ X, ∀ v ∈ Y, s(u, v) ∉ ω} =
        {ω | ∀ e ∈ F, e ∉ ω} := by
      ext ω
      simp only [mem_ofPred_eq, hF_def, Finset.mem_image, Finset.mem_product]
      constructor
      · rintro h e ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
        exact h u hu v hv
      · intro h u hu v hv
        exact h _ ⟨(u, v), ⟨hu, hv⟩, rfl⟩
    have hdXY : ∀ u ∈ X, ∀ v ∈ Y, u ≠ v := fun u hu v hv huv =>
      Finset.disjoint_left.1 (hΛdisj hkk') (hX hu) (huv ▸ hY hv)
    have hFcard : F.card = X.card * Y.card := by
      rw [hF_def, Finset.card_image_of_injOn, Finset.card_product]
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
      simp only [Finset.mem_coe, Finset.mem_product] at huv huv'
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact Prod.ext h1 h2
      · exact absurd h1 (hdXY u huv.1 v' huv'.2)
    have hJF : ∀ e ∈ F, j₀ ≤ J e := by
      intro e he
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 he
      rw [Finset.mem_product] at huv
      obtain ⟨hu, hv⟩ := huv
      refine le_trans ?_ (hJ u v (hdXY u hu v hv))
      rw [hj₀_def]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have hlev : (((v - u).support.sup Nat.succ : ℕ) : ℝ) ≤ (n : ℝ) + ℓ := by
        have := level_sub_le_of_mem_level_ball ((hmem _ _).1 (hBsub _ (hΛB k) (hX hu)))
          ((hmem _ _).1 (hBsub _ (hΛB k') (hY hv)))
        exact_mod_cast this
      have := mul_le_mul_of_nonneg_left hlev ha
      linarith
    rw [hset]
    refine (law_all_closed_le J β F hJF).trans (ENNReal.ofReal_le_ofReal ?_)
    -- `|F| ≥ (R - 1)²`
    have hFR : ((R - 1 : ℕ) : ℝ) ^ 2 ≤ F.card := by
      rw [hFcard]
      push_cast
      have h1 : ((R - 1 : ℕ) : ℝ) ≤ X.card := by exact_mod_cast hXc
      have h2 : ((R - 1 : ℕ) : ℝ) ≤ Y.card := by exact_mod_cast hYc
      nlinarith [Nat.cast_nonneg (α := ℝ) (R - 1)]
    have hβ0 : (0 : ℝ) ≤ β := β.coe_nonneg
    calc Real.exp (-((β : ℝ) * j₀ * F.card))
        ≤ Real.exp (-((β : ℝ) * (c * (L : ℝ) ^ (-(a * ((n : ℝ) + ℓ)))) *
            ((R - 1 : ℕ) : ℝ) ^ 2)) := by
          refine Real.exp_le_exp.2 (neg_le_neg ?_)
          rw [← hj₀_def]
          exact mul_le_mul_of_nonneg_left hFR (mul_nonneg hβ0 hj₀)
      _ ≤ 1 / (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) := by
          refine exp_neg_le_inv_two_mul_sq hc (by exact_mod_cast hβ) hL0 hN1 ?_
          refine hn.trans ?_
          rw [hRsub]
          nlinarith
      _ = 1 / (2 * (N : ℝ) ^ 2) := by rw [hNreal]
  -- the amplification step
  have hexp' : Real.exp (-((N : ℝ) / (8 * Real.exp 1))) ≤ 1 / 4 := by rwa [hNreal]
  have hstep := lt_tightnessScale_of_blocks q hNpos Λ hΛdisj hR2 hR hedge hexp'
  rw [hΛU, hball] at hstep
  set R' := tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ n + ℓ}.sym2 then q e else 0) (ball (n + ℓ)) with hR'_def
  set K := ⌈(N : ℝ) / (2 * Real.exp 1)⌉₊ with hK_def
  have hK : (L : ℝ) ^ ((d : ℝ) * ℓ) / (2 * Real.exp 1) ≤ K := by
    have hcast : (L : ℝ) ^ ((d : ℝ) * ℓ) = (N : ℝ) := by
      rw [hNreal, ← Real.rpow_natCast]; push_cast; ring_nf
    rw [hcast]
    exact Nat.le_ceil _
  have hamp := amplified_sq_ge hL0 hℓ hK hRreal hn
  have hle : (K : ℝ) * ((R : ℝ) - 1) ≤ R' := by
    rw [← hRsub]
    exact_mod_cast hstep.le
  have h0 : 0 ≤ (K : ℝ) * ((R : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  exact hamp.trans (pow_le_pow_left₀ h0 hle 2)

/-! ### Non-vacuity witnesses -/

/-- The scale of the example `L = 2`, `d = 3`, `α = 1`: `ℓ = 4` satisfies
`e^{-2^{12}/(8e)} ≤ 1/4`. -/
theorem amplification_scale_example_exp :
    Real.exp (-(((2 : ℕ) : ℝ) ^ (3 * 4) / (8 * Real.exp 1))) ≤ 1 / 4 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set x : ℝ := ((2 : ℕ) : ℝ) ^ (3 * 4) / (8 * Real.exp 1) with hx
  have hx3 : 3 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    norm_num
    linarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith [Real.add_one_le_exp x]

/-- The scale of that example: `ℓ = 4` satisfies `16 e² ≤ 2^{(3-1)·4} = 256`. -/
theorem amplification_scale_example_pow :
    16 * Real.exp 1 ^ 2 ≤ ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 1) * ((4 : ℕ) : ℝ)) := by
  have h8 : ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 1) * ((4 : ℕ) : ℝ)) = 256 := by
    rw [show (((3 : ℕ) : ℝ) - 1) * ((4 : ℕ) : ℝ) = ((8 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  rw [h8]
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

open Classical in
/-- **Non-vacuity witness** for `tightnessScale_hierarchical_amplification`: `L = 2`, `d = 3`,
`α = 1`, `c = 1`, `ℓ = 4` and the kernel `J(u, v) = 2^{-4 j}` when `u, v` first share a level-`j`
block. At `β = 1638400` the hypothesis holds at `n = 0` (the origin block is a single vertex, of
quantile `2`), so the amplified bound holds at `n = 4`. -/
example : ∃ J : Sym2 (ℕ →₀ (Fin 3 → ZMod 2)) → ℝ≥0,
    (∀ x u v, J s(u + x, v + x) = J s(u, v)) ∧
    (∀ u v, u ≠ v → (1 : ℝ) * ((2 : ℕ) : ℝ) ^ (-((((3 : ℕ) : ℝ) + 1) *
      (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v)) ∧
    (4 / 1) * ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * ((4 : ℕ) : ℝ)) *
        Real.log (2 * (((2 : ℕ) : ℝ) ^ (3 * 4)) ^ 2) / ((1638400 : ℝ≥0) : ℝ) *
        ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + ((4 : ℕ) : ℝ))) ≤
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin 3 → ZMod 2) |
        z.support.sup Nat.succ ≤ 0 + 4}.sym2 then intensityProfile J 1638400 e else 0)
        (finite_level_ball (0 + 4)).toFinset : ℝ) ^ 2 := by
  let k : (ℕ →₀ (Fin 3 → ZMod 2)) → ℝ≥0 := fun z =>
    ((2 : ℝ) ^ (-(4 * ((z.support.sup Nat.succ : ℕ) : ℝ)))).toNNReal
  obtain ⟨J, hJ⟩ := exists_sym2_kernel k (fun z => by simp only [k, Finsupp.support_neg])
  have hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v) := by
    intro x u v
    rw [hJ, hJ, add_sub_add_right_eq_sub]
  have hJl : ∀ u v, u ≠ v → (1 : ℝ) * ((2 : ℕ) : ℝ) ^ (-((((3 : ℕ) : ℝ) + 1) *
      (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v) := by
    intro u v _
    rw [hJ]
    simp only [k, one_mul, Real.coe_toNNReal _ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    norm_num
  refine ⟨J, hJt, hJl, ?_⟩
  have hball0 : (finite_level_ball (A := Fin 3 → ZMod 2) 0).toFinset = {0} := by
    ext z
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_singleton, Nat.le_zero,
      level_eq_zero_iff]
  have hn : (4 / 1) * ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * ((4 : ℕ) : ℝ)) *
        Real.log (2 * (((2 : ℕ) : ℝ) ^ (3 * 4)) ^ 2) / ((1638400 : ℝ≥0) : ℝ) *
        ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * ((0 : ℕ) : ℝ)) ≤
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin 3 → ZMod 2) |
        z.support.sup Nat.succ ≤ 0}.sym2 then intensityProfile J 1638400 e else 0)
        (finite_level_ball 0).toFinset : ℝ) ^ 2 := by
    rw [hball0, tightnessScale_singleton]
    have h16 : ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * ((4 : ℕ) : ℝ)) = 65536 := by
      rw [show (((3 : ℕ) : ℝ) + 1) * ((4 : ℕ) : ℝ) = ((16 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    have h0 : ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * ((0 : ℕ) : ℝ)) = 1 := by
      simp
    have hlog : Real.log (2 * (((2 : ℕ) : ℝ) ^ (3 * 4)) ^ 2) ≤ 25 := by
      have : (2 : ℝ) * (((2 : ℕ) : ℝ) ^ (3 * 4)) ^ 2 = 2 ^ 25 := by norm_num
      rw [this, Real.log_pow]
      have := Real.log_two_lt_d9
      norm_num
      linarith
    rw [h16, h0]
    have hβ : ((1638400 : ℝ≥0) : ℝ) = 1638400 := by norm_num
    rw [hβ]
    generalize Real.log (2 * (((2 : ℕ) : ℝ) ^ (3 * 4)) ^ 2) = Lg at hlog ⊢
    norm_num
    linarith
  exact tightnessScale_hierarchical_amplification (le_refl 2) one_pos one_pos J hJt hJl
    amplification_scale_example_exp amplification_scale_example_pow (by norm_num) 0 hn

open Classical in
/-- **Hierarchical block-quantile amplification, translation invariance off the diagonal.**
The statement of `tightnessScale_hierarchical_amplification` with translation invariance assumed
for distinct pairs only (the diagonal is arbitrary). -/
theorem tightnessScale_hierarchical_amplification_of_ne [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, u ≠ v → J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {β : ℝ≥0} (hβ : 0 < β) (n : ℕ)
    (hn : (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) /
        β * (L : ℝ) ^ (((d : ℝ) + α) * n) ≤
      (tightnessScale (fun e => if e ∈ {z : (ℕ →₀ (Fin d → ZMod L)) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2) :
    (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
        (L : ℝ) ^ (((d : ℝ) + α) * ((n : ℝ) + ℓ)) ≤
      (tightnessScale (fun e => if e ∈ {z : (ℕ →₀ (Fin d → ZMod L)) |
        z.support.sup Nat.succ ≤ n + ℓ}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball (n + ℓ)).toFinset : ℝ) ^ 2 := by
  set J' : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0 := fun e => if e.IsDiag then 0 else J e with hJ'def
  have hJJ' : ∀ u v, u ≠ v → J s(u, v) = J' s(u, v) := fun u v h => by simp [hJ'def, h]
  have hJt' : ∀ x u v, J' s(u + x, v + x) = J' s(u, v) := by
    intro x u v
    by_cases h : u = v
    · subst h
      simp [hJ'def]
    · have h' : u + x ≠ v + x := fun e => h (add_right_cancel e)
      rw [← hJJ' _ _ h', ← hJJ' _ _ h, hJt x u v h]
  have hJ'' : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
        J' s(u, v) := fun u v h => hJJ' u v h ▸ hJ u v h
  have hts : ∀ (S : Set (Sym2 (ℕ →₀ (Fin d → ZMod L)))) (Λ : Finset (ℕ →₀ (Fin d → ZMod L))),
      tightnessScale (fun e => if e ∈ S then intensityProfile J β e else 0) Λ =
        tightnessScale (fun e => if e ∈ S then intensityProfile J' β e else 0) Λ := by
    intro S Λ
    unfold tightnessScale
    congr 1
    ext m
    simp only [Set.mem_ofPred_eq]
    rw [law_event_eq_of_offDiagonal _ _ ?_ (measurableSet_le_maxClusterIntersection Λ m) ?_]
    · intro e he
      simp only [intensityProfile_eq_of_offDiagonal hJJ' β e he]
    · intro ω ω' h
      simp only [Set.mem_ofPred_eq, maxClusterIntersection, cluster,
        openGraph_eq_of_sdiff_diagSet_eq h]
  rw [hts] at hn ⊢
  exact tightnessScale_hierarchical_amplification hL hc hα J' hJt' hJ'' hexp hℓ hβ n hn


end Hierarchical

end PercLib.Models
