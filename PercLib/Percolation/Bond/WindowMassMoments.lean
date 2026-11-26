/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Mathematical reference: the tree-graph bound and the van den Berg-Kesten inequality; context:
C. Borgs, J. T. Chayes, R. van der Hofstad, G. Slade, J. Spencer, "Random subgraphs of finite
graphs: I. The scaling window under the triangle condition", Random Structures Algorithms 27
(2005).
-/
module

public import PercLib.Percolation.Bond.TreeGraph.Moments
public import PercLib.Percolation.Bond.ClusterPartition
public import PercLib.Probability.CountableBK
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Polynomial moments of the total squared cluster mass

For independent bond percolation on a finite vertex set of size `N`, with
`M = ⨆ v, E|C_v|`, every polynomial moment of `T = ∑_C |C|²` is bounded by a sum over
set partitions:
`E T^m ≤ ∑_{π ∈ 𝒫_m} N^{|π|} M^{4m - 3|π|} ∏_{B ∈ π} (4|B| - 5)‼`.
Consequently, if `M ≤ K N^{1/3}`, every real moment of `N^{-4/3} T` is bounded uniformly.

The proof expands `T^m` as a sum over `m` pairs of vertices, groups the pairs by the
clusters they occupy, and bounds the resulting disjoint occurrence by the BK inequality.
Each block is then a cluster moment, controlled by the tree-graph bound.

## Main results

* `PercLib.Probability.prodBernoulli_iDisjointOccurrence_le`: BK for a finite family.
* `PercLib.Percolation.Bond.lintegral_sum_component_sq_pow_le`: the partition bound.
* `PercLib.Percolation.Bond.lintegral_normalized_sum_component_sq_rpow_le`: uniform real
  moments of `N^{-4/3} ∑_C |C|²` under `M ≤ K N^{1/3}`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Finset
open scoped ENNReal Nat

namespace PercLib.Probability

variable {ι κ : Type*}

/-- **BK inequality for a finite family.** The event that increasing events `A i`, `i ∈ S`,
have pairwise disjoint finite open witnesses has probability at most `∏_{i ∈ S} P(A i)`. -/
theorem prodBernoulli_iDisjointOccurrence_le [Countable ι] [DecidableEq κ]
    (p : ι → unitInterval) (A : κ → Set (Set ι)) (hA : ∀ i, IsUpperSet (A i))
    (S : Finset κ) :
    prodBernoulli p {ω | ∃ F : κ → Set ι, (∀ i ∈ S, (F i).Finite ∧ F i ⊆ ω ∧ F i ∈ A i) ∧
        (S : Set κ).PairwiseDisjoint F} ≤ ∏ i ∈ S, prodBernoulli p (A i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [prod_insert ha]
    set D := {ω : Set ι | ∃ F : κ → Set ι, (∀ i ∈ S, (F i).Finite ∧ F i ⊆ ω ∧ F i ∈ A i) ∧
        (S : Set κ).PairwiseDisjoint F}
    have hD : IsUpperSet D := by
      rintro ω η hle ⟨F, hF, hd⟩
      exact ⟨F, fun i hi => ⟨(hF i hi).1, (hF i hi).2.1.trans hle, (hF i hi).2.2⟩, hd⟩
    have hsub : {ω : Set ι | ∃ F : κ → Set ι, (∀ i ∈ insert a S, (F i).Finite ∧ F i ⊆ ω ∧
        F i ∈ A i) ∧ ((insert a S : Finset κ) : Set κ).PairwiseDisjoint F} ⊆
        disjointOccurrence (A a) D := by
      rintro ω ⟨F, hF, hd⟩
      have hFa := hF a (mem_insert_self a S)
      have hFS : ∀ i ∈ S, (F i).Finite ∧ F i ⊆ ω ∧ F i ∈ A i :=
        fun i hi => hF i (mem_insert_of_mem hi)
      rw [mem_disjointOccurrence_iff_open (hA a) hD]
      refine ⟨F a, ⋃ i ∈ S, F i, hFa.1,
        Set.Finite.biUnion S.finite_toSet fun i hi => (hFS i hi).1, ?_, hFa.2.1,
        Set.iUnion₂_subset fun i hi => (hFS i hi).2.1, hFa.2.2, F,
        fun i hi => ⟨(hFS i hi).1, Set.subset_biUnion_of_mem (u := F) hi, (hFS i hi).2.2⟩,
        hd.subset (by simp)⟩
      refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
      exact hd (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)
    calc _ ≤ prodBernoulli p (disjointOccurrence (A a) D) := measure_mono hsub
      _ ≤ prodBernoulli p (A a) * prodBernoulli p D := countable_profile_bk p (hA a) hD
      _ ≤ _ := by gcongr

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- A connection is witnessed by the open edges inside the cluster: if `η` contains every
`ω`-open edge with both ends in the `ω`-cluster of `x`, then `x ↔ y` in `ω` implies the same
in `η`. -/
theorem mem_conn_of_forall_mem_cluster {ω η : Config V} {x y : V} (hω : ω ∈ conn x y)
    (h : ∀ e ∈ ω, (∀ v ∈ e, v ∈ cluster ω x) → e ∈ η) : η ∈ conn x y := by
  have key : ∀ {u : V} (W : (openGraph ω).Walk u y), u ∈ cluster ω x →
      (openGraph η).Reachable u y := by
    intro u W
    clear hω
    induction W with
    | nil => exact fun _ => SimpleGraph.Reachable.refl _
    | @cons u w y hadj p ih =>
      intro hu
      have hw : w ∈ cluster ω x := SimpleGraph.Reachable.trans hu hadj.reachable
      rw [openGraph_adj_iff] at hadj
      have he : s(u, w) ∈ η := h _ hadj.1 fun v hv => by
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact hu
        · exact hw
      exact SimpleGraph.Reachable.trans (mem_conn_of_mem hadj.2 he) (ih hw)
  obtain ⟨W⟩ := hω
  exact key W (mem_cluster_self ω x)

/-- Summing a product of block-restricted functions over all assignments factorises
over the blocks of a partition. -/
theorem sum_prod_parts_eq_prod_sum {α W R : Type*} [Fintype α] [DecidableEq α] [Fintype W]
    [CommSemiring R] (π : Finpartition (univ : Finset α))
    (g : ∀ B : Finset α, (B → W) → R) :
    ∑ z : α → W, ∏ B ∈ π.parts, g B (fun i => z i) = ∏ B ∈ π.parts, ∑ w : B → W, g B w := by
  rw [← Finset.prod_coe_sort π.parts (fun B => ∑ w : B → W, g B w), Fintype.prod_sum]
  let e : (α → W) ≃ (∀ B : π.parts, (B.1 → W)) :=
    { toFun := fun z B i => z i
      invFun := fun x a => x ⟨π.part a, π.part_mem.2 (mem_univ a)⟩
        ⟨a, π.mem_part (mem_univ a)⟩
      left_inv := fun z => rfl
      right_inv := by
        intro x
        funext B i
        obtain ⟨B, hB⟩ := B
        obtain ⟨a, ha⟩ := i
        have h : π.part a = B := π.part_eq_of_mem hB ha
        subst h
        rfl }
  rw [← e.sum_comp]
  exact sum_congr rfl fun z _ => (Finset.prod_coe_sort π.parts _).symm

/-- The event that the points of a block, paired as `w i = (x_i, y_i)`, all lie in one
cluster is increasing. -/
private theorem isUpperSet_blockConn {m : ℕ} (B : Finset (Fin m)) (w : B → V × V) :
    IsUpperSet {ω : Config V | ∀ i j : B, ω ∈ conn (w i).1 (w j).1 ∧ ω ∈ conn (w i).1 (w j).2} :=
  fun _ _ hle h i j =>
  ⟨conn_mono hle (h i j).1, conn_mono hle (h i j).2⟩

variable [Fintype V]

/-- Grouping `m` connected pairs by their clusters exhibits disjoint occurrence of the
block events for some partition of `Fin m`. -/
private theorem forall_conn_subset_iUnion {m : ℕ} (z : Fin m → V × V) :
    {ω : Config V | ∀ i, ω ∈ conn (z i).1 (z i).2} ⊆
      ⋃ π ∈ (univ : Finset (Finpartition (univ : Finset (Fin m)))),
        {ω | ∃ F : Finset (Fin m) → Set (Sym2 V),
          (∀ B ∈ π.parts, (F B).Finite ∧ F B ⊆ ω ∧ F B ∈
            {ω : Config V | ∀ i j : B, ω ∈ conn (z ↑i).1 (z ↑j).1 ∧ ω ∈ conn (z ↑i).1 (z ↑j).2}) ∧
          (π.parts : Set (Finset (Fin m))).PairwiseDisjoint F} := by
  classical
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  let s : Setoid (Fin m) := Setoid.ker fun i => cluster ω (z i).1
  let π := Finpartition.ofSetoid s
  have hrel : ∀ B ∈ π.parts, ∀ i ∈ B, ∀ j ∈ B, cluster ω (z i).1 = cluster ω (z j).1 := by
    intro B hB i hi j hj
    have : j ∈ π.part i := by rw [π.part_eq_of_mem hB hi]; exact hj
    exact Finpartition.mem_part_ofSetoid_iff_rel.mp this
  refine Set.mem_biUnion (x := π) (mem_univ _) ?_
  refine ⟨fun B => {e | e ∈ ω ∧ ∃ i ∈ B, ∀ v ∈ e, v ∈ cluster ω (z i).1}, ?_, ?_⟩
  · intro B hB
    refine ⟨Set.toFinite _, fun e he => he.1, ?_⟩
    intro i j
    have hc : cluster ω (z i.1).1 = cluster ω (z j.1).1 := hrel B hB i i.2 j j.2
    have h1 : ω ∈ conn (z i.1).1 (z j.1).1 := (cluster_eq_iff_conn ω _ _).mp hc
    have hw : ∀ e ∈ ω, (∀ v ∈ e, v ∈ cluster ω (z i.1).1) →
        e ∈ {e | e ∈ ω ∧ ∃ i ∈ B, ∀ v ∈ e, v ∈ cluster ω (z i).1} :=
      fun e he hv => ⟨he, i, i.2, hv⟩
    exact ⟨mem_conn_of_forall_mem_cluster h1 hw,
      mem_conn_of_forall_mem_cluster (conn_trans h1 (hω j)) hw⟩
  · intro B hB B' hB' hne
    refine Set.disjoint_left.mpr ?_
    rintro e ⟨-, i, hi, hv⟩ ⟨-, j, hj, hv'⟩
    obtain ⟨a, ha⟩ : ∃ a, a ∈ e := e.inductionOn fun a b => ⟨a, Sym2.mem_mk_left a b⟩
    have hij : cluster ω (z i).1 = cluster ω (z j).1 :=
      (cluster_eq_or_disjoint ω _ _).resolve_right
        (Set.not_disjoint_iff.mpr ⟨a, hv a ha, hv' a ha⟩)
    have hjB : j ∈ B := by
      rw [← π.part_eq_of_mem hB hi]
      exact Finpartition.mem_part_ofSetoid_iff_rel.mpr hij
    exact hne (π.eq_of_mem_parts hB hB' hjB hj)

omit [Fintype V] in
/-- The indicator of a finite conjunction of pairs of events is the product of indicators. -/
private theorem indicator_forall_and_eq_prod {ι : Type*} [Fintype ι] (S T : ι → Set (Config V))
    (ω : Config V) :
    {η : Config V | ∀ i, η ∈ S i ∧ η ∈ T i}.indicator (fun _ => (1 : ℝ≥0∞)) ω =
      ∏ i, (S i).indicator (fun _ => (1 : ℝ≥0∞)) ω * (T i).indicator (fun _ => 1) ω := by
  by_cases h : ∀ i, ω ∈ S i ∧ ω ∈ T i
  · rw [Set.indicator_of_mem (show ω ∈ {η : Config V | ∀ i, η ∈ S i ∧ η ∈ T i} from h)]
    exact (Finset.prod_eq_one fun i _ => by
      simp [Set.indicator_of_mem (h i).1, Set.indicator_of_mem (h i).2]).symm
  · rw [Set.indicator_of_notMem (show ω ∉ {η : Config V | ∀ i, η ∈ S i ∧ η ∈ T i} from h)]
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine (Finset.prod_eq_zero (mem_univ i) ?_).symm
    by_cases h1 : ω ∈ S i
    · simp [Set.indicator_of_notMem (hi h1)]
    · simp [Set.indicator_of_notMem h1]

omit [Fintype V] in
private theorem measurableSet_forall_and [Countable V] {ι : Type*} [Countable ι]
    (a b c : ι → V) :
    MeasurableSet {η : Config V | ∀ i, η ∈ conn (a i) (b i) ∧ η ∈ conn (a i) (c i)} := by
  have h : {η : Config V | ∀ i, η ∈ conn (a i) (b i) ∧ η ∈ conn (a i) (c i)} =
      ⋂ i, (conn (a i) (b i) ∩ conn (a i) (c i)) := by
    ext η; simp [Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun i => (measurableSet_conn _ _).inter (measurableSet_conn _ _)

/-- The cluster size as a finite sum of connection indicators. -/
private theorem encard_cluster_eq_sum (ω : Config V) (o : V) :
    ((cluster ω o).encard : ℝ≥0∞) = ∑ v, (conn o v).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [encard_cluster_eq_tsum, tsum_fintype]

/-- **One block.** Summing the probability that `2k` points (`k = |B|`) lie in one cluster
over all positions gives `∑_o E|C_o|^{2k-1} ≤ N (4k-5)‼ M^{4k-3}`. -/
private theorem sum_law_blockConn_le (q : Sym2 V → unitInterval) {m : ℕ} (B : Finset (Fin m))
    (hB : B.Nonempty) :
    ∑ w : B → V × V,
        law q {ω : Config V | ∀ i j : B, ω ∈ conn (w i).1 (w j).1 ∧ ω ∈ conn (w i).1 (w j).2} ≤
      (Fintype.card V : ℝ≥0∞) * (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞) *
        (⨆ x, chi q x) ^ (4 * #B - 3) := by
  classical
  obtain ⟨i0, hi0⟩ := hB
  set j0 : B := ⟨i0, hi0⟩
  have hk : 1 ≤ #B := card_pos.mpr ⟨i0, hi0⟩
  set M := ⨆ x, chi q x
  set c : Config V → V → V → ℝ≥0∞ := fun ω o v => (conn o v).indicator (fun _ => 1) ω
  set G : (B → V × V) → Set (Config V) :=
    fun w => {ω | ∀ j, ω ∈ conn (w j0).1 (w j).1 ∧ ω ∈ conn (w j0).1 (w j).2}
  have hGm : ∀ w, MeasurableSet (G w) := fun w =>
    measurableSet_forall_and (fun _ => (w j0).1) (fun j => (w j).1) (fun j => (w j).2)
  -- pointwise count
  have hpt : ∀ ω : Config V, ∑ w : B → V × V, (G w).indicator (fun _ => (1 : ℝ≥0∞)) ω =
      ∑ o, ((cluster ω o).encard : ℝ≥0∞) ^ (2 * #B - 1) := by
    intro ω
    set g : V → V × V → ℝ≥0∞ := fun o r => c ω o r.1 * c ω o r.2
    set h : V → B → V × V → ℝ≥0∞ := fun o j r => if j = j0 then (if r.1 = o then g o r else 0)
      else g o r
    have h1 : ∀ w : B → V × V, (G w).indicator (fun _ => (1 : ℝ≥0∞)) ω =
        ∑ o, ∏ j, h o j (w j) := by
      intro w
      rw [indicator_forall_and_eq_prod]
      rw [Finset.sum_eq_single (w j0).1 (fun o _ ho => ?_) (by simp)]
      · rw [Fintype.prod_eq_mul_prod_compl j0, Fintype.prod_eq_mul_prod_compl j0]
        simp only [h, g, c, ↓reduceIte]
        congr 1
        exact prod_congr rfl fun j hj => by
          have hne : j ≠ j0 := by simpa using hj
          simp [hne]
      · rw [Fintype.prod_eq_mul_prod_compl j0]
        simp [h, Ne.symm ho]
    have hsum : ∀ o, ∑ r : V × V, g o r = ((cluster ω o).encard : ℝ≥0∞) ^ 2 := by
      intro o
      rw [Fintype.sum_prod_type, sq, encard_cluster_eq_sum, Finset.sum_mul_sum]
    have hsum0 : ∀ o, ∑ r : V × V, h o j0 r = ((cluster ω o).encard : ℝ≥0∞) := by
      intro o
      simp only [h, ↓reduceIte]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single o (fun a _ ha => by simp [ha])
        (by simp), encard_cluster_eq_sum]
      simp only [↓reduceIte, g, c, conn_self, Set.indicator_of_mem (Set.mem_univ ω), one_mul]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun o _ => ?_
    rw [← Fintype.prod_sum, Fintype.prod_eq_mul_prod_compl j0, hsum0]
    rw [prod_congr rfl fun j hj => (show ∑ r, h o j r = _ by
      have hne : j ≠ j0 := by simpa using hj
      simp only [h, hne, ↓reduceIte]
      exact hsum o)]
    rw [prod_const, card_compl, card_singleton, Fintype.card_coe, ← pow_mul, ← pow_succ']
    congr 1
    omega
  calc ∑ w : B → V × V,
        law q {ω : Config V | ∀ i j : B, ω ∈ conn (w i).1 (w j).1 ∧ ω ∈ conn (w i).1 (w j).2}
        ≤ ∑ w, law q (G w) :=
        sum_le_sum fun w _ => measure_mono fun ω hω j => hω j0 j
    _ = ∫⁻ ω, ∑ o, ((cluster ω o).encard : ℝ≥0∞) ^ (2 * #B - 1) ∂law q := by
        simp_rw [← hpt]
        rw [lintegral_finsetSum _ fun w _ => measurable_const.indicator (hGm w)]
        exact sum_congr rfl fun w _ => (lintegral_indicator_one (hGm w)).symm
    _ = ∑ o, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (2 * #B - 1) ∂law q :=
        lintegral_finsetSum _ fun o _ => measurable_encard_pow o _
    _ ≤ ∑ _o : V, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞) * M ^ (4 * #B - 3) := by
        refine sum_le_sum fun o _ => ?_
        refine (lintegral_encard_pow_le_iSup q (2 * #B - 1) (by omega) o).trans ?_
        have e1 : 2 * (2 * #B - 1) - 3 = 4 * #B - 5 := by omega
        have e2 : 4 * #B - 3 = (2 * (2 * #B - 1) - 2) + 1 := by omega
        rw [e1, e2, pow_succ', mul_assoc]
        gcongr
        exact le_iSup (fun x => chi q x) o
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]

/-- The total squared cluster mass `∑_C |C|²` as the number of connected ordered pairs. -/
theorem sum_component_sq_eq_sum_indicator (ω : Config V) :
    ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) =
      ∑ p : V × V, (conn p.1 p.2).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [← tsum_cluster_ncard_eq_tsum_component_sq ω, tsum_fintype, Nat.cast_sum,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [← encard_cluster_eq_sum, ← ENat.toENNReal_coe, Set.Finite.cast_ncard_eq (Set.toFinite _)]

theorem measurable_sum_component_sq :
    Measurable fun ω : Config V =>
      ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) := by
  simp_rw [sum_component_sq_eq_sum_indicator]
  exact Finset.measurable_sum _ fun p _ => measurable_const.indicator (measurableSet_conn _ _)

/-- **Polynomial moments of the total squared cluster mass.** For independent bond
percolation on a finite vertex set with `N` vertices and `M = ⨆ v, E|C_v|`,
`E (∑_C |C|²)^m ≤ ∑_{π ∈ 𝒫_m} N^{|π|} M^{4m-3|π|} ∏_{B ∈ π} (4|B|-5)‼`. -/
theorem lintegral_sum_component_sq_pow_le (q : Sym2 V → unitInterval) (m : ℕ) :
    ∫⁻ ω, ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) ^ m
        ∂law q ≤
      ∑ π : Finpartition (univ : Finset (Fin m)),
        (Fintype.card V : ℝ≥0∞) ^ #π.parts * (⨆ x, chi q x) ^ (4 * m - 3 * #π.parts) *
          ∏ B ∈ π.parts, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞) := by
  classical
  set M := ⨆ x, chi q x
  set N := (Fintype.card V : ℝ≥0∞)
  set E : (Fin m → V × V) → Set (Config V) := fun z => {ω | ∀ i, ω ∈ conn (z i).1 (z i).2}
  have hEm : ∀ z, MeasurableSet (E z) := fun z => by
    have h := measurableSet_forall_and (fun i => (z i).1) (fun i => (z i).2) (fun i => (z i).2)
    simpa [E] using h
  have hpt : ∀ ω : Config V,
      ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞) ^ m =
        ∑ z : Fin m → V × V, (E z).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [sum_component_sq_eq_sum_indicator, ← Fin.prod_const, Fintype.prod_sum]
    refine sum_congr rfl fun z _ => ?_
    have := indicator_forall_and_eq_prod (fun i => conn (z i).1 (z i).2)
      (fun i => conn (z i).1 (z i).2) ω
    simp only [and_self] at this
    rw [show E z = {η | ∀ i, η ∈ conn (z i).1 (z i).2} from rfl, this]
    refine prod_congr rfl fun i _ => ?_
    by_cases h : ω ∈ conn (z i).1 (z i).2 <;> simp [h]
  have hlaw : ∀ z, law q (E z) ≤ ∑ π : Finpartition (univ : Finset (Fin m)),
      ∏ B ∈ π.parts,
        law q {ω : Config V | ∀ i j : B,
            ω ∈ conn (z ↑i).1 (z ↑j).1 ∧ ω ∈ conn (z ↑i).1 (z ↑j).2} := by
    intro z
    refine (measure_mono (forall_conn_subset_iUnion z)).trans
      ((measure_biUnion_finset_le _ _).trans (sum_le_sum fun π _ => ?_))
    exact prodBernoulli_iDisjointOccurrence_le q
      (fun B : Finset (Fin m) => {ω : Config V | ∀ i j : B,
        ω ∈ conn (z ↑i).1 (z ↑j).1 ∧ ω ∈ conn (z ↑i).1 (z ↑j).2})
      (fun B => isUpperSet_blockConn B (fun i : B => z i)) π.parts
  calc _ = ∑ z : Fin m → V × V, law q (E z) := by
        simp_rw [hpt]
        rw [lintegral_finsetSum _ fun z _ => measurable_const.indicator (hEm z)]
        exact sum_congr rfl fun z _ => lintegral_indicator_one (hEm z)
    _ ≤ ∑ z : Fin m → V × V, ∑ π : Finpartition (univ : Finset (Fin m)),
          ∏ B ∈ π.parts, law q {ω : Config V | ∀ i j : B,
              ω ∈ conn (z ↑i).1 (z ↑j).1 ∧ ω ∈ conn (z ↑i).1 (z ↑j).2} :=
        sum_le_sum fun z _ => hlaw z
    _ = ∑ π : Finpartition (univ : Finset (Fin m)),
          ∏ B ∈ π.parts, ∑ w : B → V × V, law q {ω : Config V | ∀ i j : B,
              ω ∈ conn (w i).1 (w j).1 ∧ ω ∈ conn (w i).1 (w j).2} := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun π _ => ?_
        rw [← sum_prod_parts_eq_prod_sum]
    _ ≤ ∑ π : Finpartition (univ : Finset (Fin m)),
          ∏ B ∈ π.parts, N * (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞) * M ^ (4 * #B - 3) :=
        sum_le_sum fun π _ => prod_le_prod fun B hB =>
          sum_law_blockConn_le q B (π.nonempty_of_mem_parts hB)
    _ = _ := by
        refine sum_congr rfl fun π _ => ?_
        rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_pow_eq_pow_sum]
        have hs : ∑ B ∈ π.parts, #B = m := by
          rw [π.sum_card_parts, card_univ, Fintype.card_fin]
        have h4 : ∑ B ∈ π.parts, (4 * #B - 3) + 3 * #π.parts = 4 * m := by
          have h4m : ∑ B ∈ π.parts, 4 * #B = 4 * m := by rw [← mul_sum, hs]
          rw [← h4m, card_eq_sum_ones, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun B hB => ?_
          have := card_pos.mpr (π.nonempty_of_mem_parts hB)
          omega
        rw [show ∑ B ∈ π.parts, (4 * #B - 3) = 4 * m - 3 * #π.parts by omega]
        ring

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

universe u

/-- **Uniform real moments of the normalised total squared cluster mass.** For every
`K` and every real `r > 0` there is a finite constant `C` such that, for every independent
bond model on a finite nonempty vertex set with `N` vertices and
`⨆ v, E|C_v| ≤ K N^{1/3}`, `E (N^{-4/3} ∑_C |C|²)^r ≤ C`. -/
theorem exists_lintegral_normalized_sum_component_sq_rpow_le (K : NNReal) {r : ℝ}
    (hr : 0 < r) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (V : Type u) [Fintype V] [Nonempty V] (q : Sym2 V → unitInterval),
      (⨆ x, chi q x) ≤ K * (Fintype.card V : ℝ≥0∞) ^ (1 / 3 : ℝ) →
      ∫⁻ ω, ((Fintype.card V : ℝ≥0∞) ^ (-(4 / 3 : ℝ)) *
        ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞)) ^ r
          ∂law q ≤ C := by
  classical
  set m := ⌈r⌉₊
  have hrm : r ≤ m := Nat.le_ceil r
  have hm0 : (0 : ℝ) < m := hr.trans_le hrm
  set Cm : ℝ≥0∞ := ∑ π : Finpartition (univ : Finset (Fin m)),
    (K : ℝ≥0∞) ^ (4 * m - 3 * #π.parts) * ∏ B ∈ π.parts, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞)
  have hCm : Cm ≠ ⊤ := ENNReal.sum_ne_top.mpr fun π _ =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.prod_ne_top fun B _ => ENNReal.natCast_ne_top _)
  refine ⟨Cm ^ (r / m), ENNReal.rpow_lt_top_of_nonneg (div_nonneg hr.le hm0.le) hCm, ?_⟩
  intro V _ _ q hM
  set N : ℝ≥0∞ := (Fintype.card V : ℝ≥0∞)
  have hN0 : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  set T : Config V → ℝ≥0∞ := fun ω =>
    ((∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 : ℕ) : ℝ≥0∞)
  set a : ℝ≥0∞ := N ^ (-(4 / 3 : ℝ))
  have ha : a ≠ ⊤ := by simp [a, ENNReal.rpow_eq_top_iff, hN0, hNt]
  have hint : ∫⁻ ω, (a * T ω) ^ m ∂law q ≤ Cm := by
    simp_rw [mul_pow]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ha)]
    refine (mul_le_mul_of_nonneg_left (lintegral_sum_component_sq_pow_le q m) zero_le).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun π _ => ?_
    have hle : #π.parts ≤ m := by
      calc #π.parts = ∑ B ∈ π.parts, 1 := card_eq_sum_ones _
        _ ≤ ∑ B ∈ π.parts, #B :=
          sum_le_sum fun B hB => card_pos.mpr (π.nonempty_of_mem_parts hB)
        _ = m := by rw [π.sum_card_parts, card_univ, Fintype.card_fin]
    have hkey : a ^ m * N ^ #π.parts * (N ^ (1 / 3 : ℝ)) ^ (4 * m - 3 * #π.parts) = 1 := by
      simp only [a, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      rw [← ENNReal.rpow_add _ _ hN0 hNt, ← ENNReal.rpow_add _ _ hN0 hNt,
        Nat.cast_sub (by omega)]
      push_cast
      rw [show -(4 / 3 : ℝ) * m + #π.parts + 1 / 3 * (4 * m - 3 * #π.parts) = 0 by ring,
        ENNReal.rpow_zero]
    calc a ^ m * (N ^ #π.parts * (⨆ x, chi q x) ^ (4 * m - 3 * #π.parts) *
          ∏ B ∈ π.parts, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞))
        ≤ a ^ m * (N ^ #π.parts * (K * N ^ (1 / 3 : ℝ)) ^ (4 * m - 3 * #π.parts) *
          ∏ B ∈ π.parts, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞)) := by gcongr
      _ = (a ^ m * N ^ #π.parts * (N ^ (1 / 3 : ℝ)) ^ (4 * m - 3 * #π.parts)) *
          ((K : ℝ≥0∞) ^ (4 * m - 3 * #π.parts) *
            ∏ B ∈ π.parts, (((4 * #B - 5)‼ : ℕ) : ℝ≥0∞)) := by ring
      _ = _ := by rw [hkey, one_mul]
  have hmeas : AEStronglyMeasurable (fun ω => a * T ω) (law q) :=
    (measurable_sum_component_sq.const_mul a).aestronglyMeasurable
  have hly := eLpNorm'_le_eLpNorm'_of_exponent_le hr hrm (law q) hmeas
  simp only [eLpNorm', enorm_eq_self, ENNReal.rpow_natCast] at hly
  have h1 : ∫⁻ ω, (a * T ω) ^ r ∂law q ≤ (∫⁻ ω, (a * T ω) ^ m ∂law q) ^ (r / m) := by
    have := ENNReal.rpow_le_rpow hly hr.le
    rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one,
      one_div_mul_eq_div] at this
  exact h1.trans (ENNReal.rpow_le_rpow hint (div_nonneg hr.le hm0.le))

end PercLib.Percolation.Bond
