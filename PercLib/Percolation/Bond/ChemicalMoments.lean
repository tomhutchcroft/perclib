/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: marks on a shortest open path and the iterated van den Berg-Kesten
inequality bound the moments of the chemical distance by powers of the susceptibility.
-/
module

public import PercLib.Percolation.Bond.Forest
public import PercLib.Probability.CountableBK
public import PercLib.Probability.OpenEventHarris
public import PercLib.Models.LongRange.RootIndependence
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Chemical-distance moments are bounded by powers of the susceptibility

The chemical distance is mathlib's `(openGraph ω).dist`, which is zero off the connection
event. For marks `z₁, …, z_k` the chain event
`o ↔ z₁ □ (z₁ ↔ z₂ □ (⋯ □ (z_k ↔ x)))` is written as the right fold
`(List.ofFn zs).foldr (fun z F b => disjointOccurrence (conn b z) (F z)) (fun b => conn b x) o`.

* Pointwise, an open path of length `ℓ` from `o` to `x` witnesses at least `C(ℓ + k, k)`
  chain events, one for each weakly ordered choice of `k` marks on it
  (`choose_le_tsum_indicator_foldr_conn`), and `ℓ ^ k ≤ k! C(ℓ + k, k)`.
* Iterated BK bounds the chain events, summed over marks and endpoint, by `C ^ (k + 1)`
  when every susceptibility is at most `C` (`tsum_law_foldr_conn_le`).

## Main results

* `lintegral_tsum_indicator_cluster_dist_pow_le`: if `χ(v) ≤ C` for every `v`, then
  `E ∑_{x ∈ K_o} d_ω(o,x)^k ≤ k! C^(k+1)` for every `k`.
* `lintegral_tsum_indicator_cluster_dist_pow_le_of_transitive`: the transitive form with
  `C = χ(o)`.
* `lintegral_tsum_indicator_cluster_dist_pow_eq`: for `k ≥ 1` the restriction to the
  cluster can be dropped.

This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal Nat

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Tuples of marks -/

/-- Splitting off the first entry of a tuple in an `ℝ≥0∞`-valued sum over lists of
length `k + 1`. -/
theorem tsum_ofFn_succ {α : Type*} (f : List α → ℝ≥0∞) (k : ℕ) :
    ∑' zs : Fin (k + 1) → α, f (List.ofFn zs) =
      ∑' z, ∑' zs : Fin k → α, f (z :: List.ofFn zs) := by
  rw [← (Fin.consEquiv fun _ => α).tsum_eq, ← ENNReal.tsum_prod]
  refine tsum_congr fun c => ?_
  simp [Fin.consEquiv, List.ofFn_succ]

/-! ### The chain events -/

/-- The chain event `a ↔ z₁ □ (z₁ ↔ z₂ □ (⋯ □ (z_k ↔ x)))` is increasing. -/
theorem isUpperSet_foldr_conn (x : V) (zs : List V) (a : V) :
    IsUpperSet (zs.foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
      disjointOccurrence (conn b z) (F z)) (fun b => conn b x) a) := by
  induction zs generalizing a with
  | nil => exact isUpperSet_conn a x
  | cons z zs ih => exact isUpperSet_disjointOccurrence (isUpperSet_conn a z) (ih z)

/-- With every mark at `a`, the chain event from `a` to `a` holds with no open edge. -/
theorem empty_mem_foldr_conn_replicate (k : ℕ) (a : V) :
    (∅ : Config V) ∈ (List.replicate k a).foldr (fun (z : V) (F : V → Set (Config V))
      (b : V) => disjointOccurrence (conn b z) (F z)) (fun b => conn b a) a := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl a
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons]
    exact (mem_disjointOccurrence_iff_open (isUpperSet_conn a a)
      (isUpperSet_foldr_conn a _ a) _).2
      ⟨∅, ∅, finite_empty, finite_empty, disjoint_empty _, subset_rfl, subset_rfl,
        SimpleGraph.Reachable.refl a, ih⟩

/-- **Iterated BK for chains.** If every susceptibility is at most `C`, then the chain
events with `k` marks, summed over the marks and the endpoint, have total probability at
most `C ^ (k + 1)`. -/
theorem tsum_law_foldr_conn_le [Countable V] (q : Sym2 V → unitInterval) {C : ℝ≥0∞}
    (hC : ∀ v, chi q v ≤ C) (k : ℕ) (a : V) :
    ∑' x, ∑' zs : Fin k → V, law q ((List.ofFn zs).foldr (fun (z : V)
      (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
      (fun b => conn b x) a) ≤ C ^ (k + 1) := by
  induction k generalizing a with
  | zero =>
    have h0 : ∀ x, ∑' zs : Fin 0 → V, law q ((List.ofFn zs).foldr (fun (z : V)
        (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
        (fun b => conn b x) a) = tau q a x := fun x => by simp [tau]
    rw [tsum_congr h0, ← chi_eq_tsum_tau, zero_add, pow_one]
    exact hC a
  | succ k ih =>
    calc ∑' x, ∑' zs : Fin (k + 1) → V, law q ((List.ofFn zs).foldr (fun (z : V)
          (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
          (fun b => conn b x) a)
        = ∑' x, ∑' z, ∑' zs : Fin k → V, law q (disjointOccurrence (conn a z)
          ((List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
            disjointOccurrence (conn b z) (F z)) (fun b => conn b x) z)) := by
          refine tsum_congr fun x => ?_
          rw [tsum_ofFn_succ (fun l => law q (l.foldr (fun (z : V)
            (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
            (fun b => conn b x) a))]
          rfl
      _ ≤ ∑' x, ∑' z, ∑' zs : Fin k → V, tau q a z * law q
          ((List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
            disjointOccurrence (conn b z) (F z)) (fun b => conn b x) z) := by
          refine ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun zs => ?_
          exact countable_profile_bk q (isUpperSet_conn a z) (isUpperSet_foldr_conn x _ z)
      _ = ∑' z, tau q a z * ∑' x, ∑' zs : Fin k → V, law q
          ((List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
            disjointOccurrence (conn b z) (F z)) (fun b => conn b x) z) := by
          rw [ENNReal.tsum_comm]
          simp_rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' z, tau q a z * C ^ (k + 1) :=
          ENNReal.tsum_le_tsum fun z => mul_le_mul_right (ih z) _
      _ = chi q a * C ^ (k + 1) := by rw [ENNReal.tsum_mul_right, chi_eq_tsum_tau]
      _ ≤ C ^ (k + 1 + 1) := by
          rw [pow_succ' C (k + 1)]
          exact mul_le_mul_left (hC a) _

/-! ### Counting marked chains on a path -/

/-- If a configuration connects `a ≠ b`, it contains an edge at `b`. -/
theorem exists_mem_of_mem_conn_of_ne {F : Config V} {a b : V} (h : F ∈ conn a b)
    (hab : a ≠ b) : ∃ c, s(b, c) ∈ F := by
  obtain ⟨p⟩ := SimpleGraph.Reachable.symm h
  cases p with
  | nil => exact absurd rfl hab
  | cons hadj _ => exact ⟨_, ((openGraph_adj_iff F _ _).1 hadj).1⟩

/-- **Marked chains on a path.** The edge set of a path of length `ℓ` from `o` to `x`
belongs to at least `C(ℓ + k, k)` chain events with `k` marks: one for each weakly ordered
choice of `k` vertices of the path. -/
theorem choose_le_tsum_indicator_foldr_conn {G : SimpleGraph V} {o x : V} (p : G.Walk o x)
    (hp : p.IsPath) (k : ℕ) :
    ((p.length + k).choose k : ℝ≥0∞) ≤ ∑' zs : Fin k → V,
      ((List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
        disjointOccurrence (conn b z) (F z)) (fun b => conn b x) o).indicator
        (fun _ => (1 : ℝ≥0∞)) {e | e ∈ p.edges} := by
  induction p generalizing k with
  | nil =>
    rename_i u
    simp only [SimpleGraph.Walk.length_nil, zero_add, Nat.choose_self, Nat.cast_one]
    refine le_trans ?_ (ENNReal.le_tsum (fun _ => u))
    rw [List.ofFn_const, indicator_of_mem]
    simpa using empty_mem_foldr_conn_replicate k u
  | cons h p ih =>
    rename_i a w t
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hp', hnot⟩ := hp
    have he : s(a, w) ∉ p.edges := fun he => hnot (p.fst_mem_support_of_mem_edges he)
    -- One step of the chain, moved from `w` back to `a` along the first edge.
    have key : ∀ (z : V) (zs : List V),
        {e | e ∈ p.edges} ∈ disjointOccurrence (conn w z) (zs.foldr (fun (z : V)
          (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
          (fun b => conn b t) z) →
        {e | e ∈ (SimpleGraph.Walk.cons h p).edges} ∈ disjointOccurrence (conn a z)
          (zs.foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
            disjointOccurrence (conn b z) (F z)) (fun b => conn b t) z) := by
      intro z zs hmem
      obtain ⟨A, H, hA, hH, hd, hAF, hHF, hAc, hHE⟩ :=
        (mem_disjointOccurrence_iff_open (isUpperSet_conn w z)
          (isUpperSet_foldr_conn t zs z) _).1 hmem
      refine (mem_disjointOccurrence_iff_open (isUpperSet_conn a z)
        (isUpperSet_foldr_conn t zs z) _).2
        ⟨insert s(a, w) A, H, hA.insert _, hH,
          disjoint_insert_left.2 ⟨fun h' => he (hHF h'), hd⟩, ?_, ?_,
          conn_trans (mem_conn_of_mem h.ne (mem_insert _ _)) (conn_mono (subset_insert _ _) hAc),
          hHE⟩
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, ofPred_or, ofPred_eq_eq_singleton,
          singleton_union]
        exact insert_subset_insert hAF
      · intro e' he'
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, mem_ofPred_eq]
        exact Or.inr (hHF he')
    -- No chain from `w` along `p` starts with the mark `a`.
    have hzero : ∀ zs : List V,
        {e | e ∈ p.edges} ∉ disjointOccurrence (conn w a) (zs.foldr (fun (z : V)
          (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
          (fun b => conn b t) a) := by
      intro zs hmem
      obtain ⟨A, H, -, -, -, hAF, -, hAc, -⟩ :=
        (mem_disjointOccurrence_iff_open (isUpperSet_conn w a)
          (isUpperSet_foldr_conn t zs a) _).1 hmem
      obtain ⟨c, hc⟩ := exists_mem_of_mem_conn_of_ne hAc h.ne.symm
      exact hnot (p.fst_mem_support_of_mem_edges (hAF hc))
    induction k with
    | zero =>
      simp only [Nat.choose_zero_right, Nat.cast_one]
      refine le_trans ?_ (ENNReal.le_tsum (fun i => i.elim0))
      rw [indicator_of_mem]
      exact mem_conn_of_walk_edges _ fun _ he' => he'
    | succ k ihk =>
      rw [tsum_ofFn_succ (fun l => (l.foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
          disjointOccurrence (conn b z) (F z)) (fun b => conn b t) a).indicator
          (fun _ => (1 : ℝ≥0∞)) {e | e ∈ (SimpleGraph.Walk.cons h p).edges}),
        ENNReal.tsum_eq_add_tsum_ite a]
      have hch : ((SimpleGraph.Walk.cons h p).length + (k + 1)).choose (k + 1) =
          ((SimpleGraph.Walk.cons h p).length + k).choose k +
            (p.length + (k + 1)).choose (k + 1) := by
        rw [SimpleGraph.Walk.length_cons, show p.length + 1 + (k + 1) = (p.length + 1 + k) + 1 by
          omega, Nat.choose_succ_succ', show p.length + 1 + k = p.length + (k + 1) by omega]
      rw [hch, Nat.cast_add]
      refine add_le_add (ihk.trans (ENNReal.tsum_le_tsum fun zs => ?_)) ?_
      · simp only [List.foldr_cons]
        by_cases hmem : {e | e ∈ (SimpleGraph.Walk.cons h p).edges} ∈
            (List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
              disjointOccurrence (conn b z) (F z)) (fun b => conn b t) a
        · rw [indicator_of_mem hmem, indicator_of_mem]
          exact (mem_disjointOccurrence_iff_open (isUpperSet_conn a a)
            (isUpperSet_foldr_conn t _ a) _).2
            ⟨∅, _, finite_empty, (SimpleGraph.Walk.cons h p).edges.finite_toSet,
              empty_disjoint _, empty_subset _, subset_rfl,
              SimpleGraph.Reachable.refl a, hmem⟩
        · rw [indicator_of_notMem hmem]
          positivity
      · refine (ih hp' (k + 1)).trans ?_
        rw [tsum_ofFn_succ (fun l => (l.foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
            disjointOccurrence (conn b z) (F z)) (fun b => conn b t) w).indicator
            (fun _ => (1 : ℝ≥0∞)) {e | e ∈ p.edges})]
        refine ENNReal.tsum_le_tsum fun z => ?_
        split_ifs with hz
        · subst hz
          simp only [List.foldr_cons]
          exact (ENNReal.tsum_eq_zero.2 fun zs => indicator_of_notMem (hzero _) _).le
        · refine ENNReal.tsum_le_tsum fun zs => ?_
          simp only [List.foldr_cons]
          by_cases hmem : {e | e ∈ p.edges} ∈ disjointOccurrence (conn w z)
              ((List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
                disjointOccurrence (conn b z) (F z)) (fun b => conn b t) z)
          · rw [indicator_of_mem hmem, indicator_of_mem (key z _ hmem)]
          · rw [indicator_of_notMem hmem]
            positivity

/-! ### Moments of the chemical distance -/

/-- **Pointwise bound.** `d_ω(o,x)^k 1{x ∈ K_o}` is at most `k!` times the number of mark
tuples `z₁, …, z_k` for which the chain `o ↔ z₁ □ ⋯ □ z_k ↔ x` occurs. -/
theorem indicator_cluster_dist_pow_le (ω : Config V) (o x : V) (k : ℕ) :
    (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x ≤
      k ! * ∑' zs : Fin k → V, ((List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V))
        (b : V) => disjointOccurrence (conn b z) (F z)) (fun b => conn b x) o).indicator
        (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases hx : x ∈ cluster ω o
  · rw [indicator_of_mem hx]
    obtain ⟨p, hp, hlen⟩ := SimpleGraph.Reachable.exists_path_of_dist hx
    have hsub : {e | e ∈ p.edges} ⊆ ω := fun e he => by
      have h' := p.edges_subset_edgeSet he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h'
      exact h'.1
    have hnat : (openGraph ω).dist o x ^ k ≤ k ! * ((openGraph ω).dist o x + k).choose k :=
      (Nat.pow_succ_le_ascFactorial _ k).trans <|
        (Nat.ascFactorial_le k (Nat.le_succ _)).trans
          (Nat.ascFactorial_eq_factorial_mul_choose _ k).le
    calc ((openGraph ω).dist o x : ℝ≥0∞) ^ k
        ≤ (k ! : ℝ≥0∞) * ((p.length + k).choose k : ℝ≥0∞) := by
          rw [hlen]; exact_mod_cast hnat
      _ ≤ _ := by
          gcongr
          refine (choose_le_tsum_indicator_foldr_conn p hp k).trans
            (ENNReal.tsum_le_tsum fun zs => ?_)
          by_cases hmem : {e | e ∈ p.edges} ∈ (List.ofFn zs).foldr (fun (z : V)
              (F : V → Set (Config V)) (b : V) => disjointOccurrence (conn b z) (F z))
              (fun b => conn b x) o
          · rw [indicator_of_mem hmem,
              indicator_of_mem (isUpperSet_foldr_conn x _ o hsub hmem)]
          · rw [indicator_of_notMem hmem]
            positivity
  · rw [indicator_of_notMem hx]
    positivity

/-- **Chemical-distance moments.** If every susceptibility is at most `C`, then
`E ∑_{x ∈ K_o} d_ω(o,x)^k ≤ k! C^(k+1)` for every `k`. -/
theorem lintegral_tsum_indicator_cluster_dist_pow_le [Countable V] (q : Sym2 V → unitInterval)
    {C : ℝ≥0∞} (hC : ∀ v, chi q v ≤ C) (o : V) (k : ℕ) :
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
      ∂law q ≤ k ! * C ^ (k + 1) := by
  set E : V → (Fin k → V) → Set (Config V) := fun x zs =>
    (List.ofFn zs).foldr (fun (z : V) (F : V → Set (Config V)) (b : V) =>
      disjointOccurrence (conn b z) (F z)) (fun b => conn b x) o
  have hmeas : ∀ x, Measurable fun ω : Config V => (k ! : ℝ≥0∞) *
      ∑' zs, (toMeasurable (law q) (E x zs)).indicator (fun _ => (1 : ℝ≥0∞)) ω := fun x =>
    (Measurable.tsum fun zs =>
      measurable_const.indicator (measurableSet_toMeasurable _ _)).const_mul _
  calc ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
        ∂law q
      ≤ ∫⁻ ω, ∑' x, (k ! : ℝ≥0∞) *
          ∑' zs, (toMeasurable (law q) (E x zs)).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂law q := by
        refine lintegral_mono fun ω => ENNReal.tsum_le_tsum fun x =>
          (indicator_cluster_dist_pow_le ω o x k).trans ?_
        gcongr with zs
        exact subset_toMeasurable _ _
    _ = k ! * ∑' x, ∑' zs, law q (E x zs) := by
        rw [lintegral_tsum fun x => (hmeas x).aemeasurable, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun x => ?_
        rw [lintegral_const_mul _ (Measurable.tsum fun zs =>
            measurable_const.indicator (measurableSet_toMeasurable _ _)),
          lintegral_tsum fun zs =>
            (measurable_const.indicator (measurableSet_toMeasurable _ _)).aemeasurable]
        congr 1
        refine tsum_congr fun zs => ?_
        rw [lintegral_indicator_const (measurableSet_toMeasurable _ _), one_mul,
          measure_toMeasurable]
    _ ≤ k ! * C ^ (k + 1) := by
        gcongr
        exact tsum_law_foldr_conn_le q hC k o

/-- **Chemical-distance moments, transitive form.** For a transitive law,
`E ∑_{x ∈ K_o} d_ω(o,x)^k ≤ k! χ^(k+1)`. -/
theorem lintegral_tsum_indicator_cluster_dist_pow_le_of_transitive [Countable V]
    (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V) (k : ℕ) :
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
      ∂law q ≤ k ! * chi q o ^ (k + 1) :=
  lintegral_tsum_indicator_cluster_dist_pow_le q (fun v =>
    (PercLib.Models.LongRange.lintegral_encard_cluster_eq_of_transitive q hq
      (fun n => (n : ℝ≥0∞)) v o).le) o k

/-- With finite susceptibility under a transitive law, every chemical-distance moment is
finite. -/
theorem lintegral_tsum_indicator_cluster_dist_pow_lt_top_of_transitive [Countable V]
    (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V)
    (hχ : chi q o ≠ ⊤) (k : ℕ) :
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
      ∂law q < ⊤ :=
  (lintegral_tsum_indicator_cluster_dist_pow_le_of_transitive q hq o k).trans_lt
    (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top hχ.lt_top))

/-- For `k ≥ 1` the chemical distance vanishes off the cluster, so the restriction to the
cluster in the moment can be dropped. -/
theorem tsum_indicator_cluster_dist_pow_eq (ω : Config V) (o : V) {k : ℕ} (hk : 1 ≤ k) :
    ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x =
      ∑' x, ((openGraph ω).dist o x : ℝ≥0∞) ^ k := by
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ cluster ω o
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, SimpleGraph.dist_eq_zero_of_not_reachable hx, Nat.cast_zero,
      zero_pow (by omega)]

/-- The moment identity of `tsum_indicator_cluster_dist_pow_eq`, integrated. -/
theorem lintegral_tsum_indicator_cluster_dist_pow_eq (q : Sym2 V → unitInterval) (o : V)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
        ∂law q =
      ∫⁻ ω, ∑' x, ((openGraph ω).dist o x : ℝ≥0∞) ^ k ∂law q :=
  lintegral_congr fun ω => tsum_indicator_cluster_dist_pow_eq ω o hk

end PercLib.Percolation.Bond
