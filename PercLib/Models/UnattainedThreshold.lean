/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface and the rooted-tree conventions of
`PercLib.Models.Tree`. No source text or code is copied.
-/
module

public import PercLib.Models.BinaryTree
public import PercLib.Percolation.Bond.Embedding
public import PercLib.Percolation.Bond.Host
public import PercLib.Percolation.Bond.IntensityMonotone
public import PercLib.Percolation.Bond.PathComparison
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Percolation.Bond.ZeroOne

/-! # AHY3: a global intensity threshold attained by no root

The vertex type is `ℕ × List (Fin 2)`: the disjoint union of rooted binary trees `T_k`,
`k = n + 1 ≥ 1`, the tree with index `n` being `{n} × List (Fin 2)`. The kernel `J` is
`c_n = log 2 / (1 + 1/(n+1))` on the tree edges of the `n`-th tree and `0` on all other
pairs. It enters through its defining equation `hJ` (no new definition); `exists_kernel`
shows such a kernel exists.

* `rootCriticalIntensity_eq`: every vertex of the `n`-th tree has root threshold
  `1 + 1/(n+1)`.
* `globalCriticalIntensity_eq_one`: the global threshold is `1`.
* `law_exists_cluster_infinite_at_one` and `law_exists_cluster_infinite_of_one_lt`: at
  `β = 1` there is almost surely no infinite cluster, and at every `β > 1` there is almost
  surely one. So the global threshold `1` is a strict lower bound of every root threshold.
* `encard_positive_neighbours_le_three`: every vertex has at most three neighbours of
  positive intensity.

Route: the binary-tree threshold `1/2` (`binaryTree_theta_pos_iff`) at the root of each
tree, transported to `ℕ × List (Fin 2)` by the embedding `u ↦ (n, u)` in one direction
(`law_cluster_infinite_le_of_embedding`) and by the containment of clusters in components
in the other (`ae_config_subset_host`, `law_map_preimage_sym2Map`); positive-path comparison
(`law_cluster_infinite_pos_iff_of_reachable`) moves it to every vertex of the tree.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-! ### The infimum of an open ray -/

/-- `inf {β : β > t} = t` among finite intensities. -/
theorem sInf_coe_gt_eq (t : ℝ) :
    sInf {b : ℝ≥0∞ | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧ t < (β : ℝ)} = ENNReal.ofReal t := by
  apply le_antisymm
  · refine le_of_forall_gt fun c hc => ?_
    obtain ⟨r, hr0, htr, hrc⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
    have htr' : t < r := by
      by_contra h
      exact absurd htr (not_lt.2 (ENNReal.ofReal_le_ofReal (not_lt.1 h)))
    refine lt_of_le_of_lt (sInf_le ⟨r.toNNReal, rfl, ?_⟩) ?_
    · rw [Real.coe_toNNReal _ hr0]; exact htr'
    · rw [ENNReal.ofNNReal_toNNReal]; exact hrc
  · refine le_sInf ?_
    rintro _ ⟨β, rfl, hβ⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hβ.le

/-! ### The model -/

/-- The edge condition of the model: the same tree, and one word is a child of the other. -/
theorem treeAdj_symm (a b : ℕ × List (Fin 2)) :
    (a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2)) ↔
      (b.1 = a.1 ∧ ((∃ x, a.2 = x :: b.2) ∨ ∃ x, b.2 = x :: a.2)) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩

/-- A kernel with the required values exists. -/
theorem exists_kernel : ∃ J : Sym2 (ℕ × List (Fin 2)) → ℝ≥0, ∀ a b,
    (J s(a, b) : ℝ) = if a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2) then
      Real.log 2 / (1 + 1 / ((a.1 : ℝ) + 1)) else 0 := by
  classical
  refine ⟨fun e => Sym2.lift ⟨fun a b =>
    if a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2) then
      Real.toNNReal (Real.log 2 / (1 + 1 / ((a.1 : ℝ) + 1))) else 0, fun a b => ?_⟩ e,
    fun a b => ?_⟩
  · by_cases h : a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2)
    · dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _
          (eq_true ((treeAdj_symm a b).1 h)),
        h.1]
    · dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false fun h' => h ((treeAdj_symm a b).2 h'))]
  · simp only [Sym2.lift_mk]
    split_ifs
    · exact Real.coe_toNNReal _ (div_nonneg (Real.log_nonneg one_le_two) (by positivity))
    · rfl

section Model

variable {J : Sym2 (ℕ × List (Fin 2)) → ℝ≥0}
  (hJ : ∀ a b, (J s(a, b) : ℝ) =
    if a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2) then
      Real.log 2 / (1 + 1 / ((a.1 : ℝ) + 1)) else 0)
include hJ

/-- The host graph: the disjoint union of the trees. -/
private theorem J_eq_zero_of_not_adj {a b : ℕ × List (Fin 2)}
    (h : ¬ (a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2))) : J s(a, b) = 0 := by
  have := hJ a b
  rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at this
  exact_mod_cast this

/-- The open probability of a tree edge of the `n`-th tree at intensity `β`. -/
private theorem intensityProfile_tree (β : ℝ≥0) (n : ℕ) (u w : List (Fin 2)) :
    ((intensityProfile J β s((n, u), (n, w)) : unitInterval) : ℝ) =
      if (∃ x, w = x :: u) ∨ ∃ x, u = x :: w then
        1 - Real.exp (-(β : ℝ) * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1)))) else 0 := by
  change 1 - Real.exp (-(β : ℝ) * (J s((n, u), (n, w)) : ℝ)) = _
  rw [hJ]
  simp only [true_and]
  split_ifs <;> simp


/-- The tree profile of the `n`-th tree is the binary-tree profile with edge probability
`1 - exp(-β c_n)`. -/
private theorem treeProfile_eq (β : ℝ≥0) (n : ℕ) (e : Sym2 (List (Fin 2))) (he : ¬ e.IsDiag) :
    intensityProfile J β (Sym2.map (Function.Embedding.sectR n (List (Fin 2))) e) =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨1 - Real.exp (-(β : ℝ) * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1)))), by
          constructor
          · rw [sub_nonneg, Real.exp_le_one_iff]
            have : 0 ≤ Real.log 2 / (1 + 1 / ((n : ℝ) + 1)) :=
              div_nonneg (Real.log_nonneg one_le_two) (by positivity)
            nlinarith [β.coe_nonneg]
          · linarith [Real.exp_pos (-(β : ℝ) * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1))))]⟩ :
          unitInterval)
      else 0 := by
  induction e using Sym2.ind with
  | h u w =>
  apply Subtype.ext
  rw [Sym2.map_mk, Function.Embedding.sectR_apply, Function.Embedding.sectR_apply,
    intensityProfile_tree hJ]
  by_cases h : (∃ x, w = x :: u) ∨ ∃ x, u = x :: w
  · have hm : s(u, w) ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet :=
      (kTree_adj_iff u w).2 h
    simp only [h, hm, ↓reduceIte]
  · have hm : s(u, w) ∉ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet :=
      fun h' => h ((kTree_adj_iff u w).1 h')
    simp only [h, hm, ↓reduceIte]
    rfl

/-- Clusters of the `n`-th tree's root stay in that tree: the root percolates in the union
exactly as in the binary tree. -/
private theorem law_root_eq (β : ℝ≥0) (n : ℕ) :
    law (intensityProfile J β) {ω | (cluster ω (n, [])).Infinite} =
      law (fun e => intensityProfile J β (Sym2.map (Function.Embedding.sectR n (List (Fin 2))) e))
        {ω | (cluster ω []).Infinite} := by
  set f := Function.Embedding.sectR n (List (Fin 2)) with hf
  apply le_antisymm
  · -- the host graph contains every open edge almost surely
    set G : SimpleGraph (ℕ × List (Fin 2)) := SimpleGraph.fromRel fun a b =>
      a.1 = b.1 ∧ ∃ x, b.2 = x :: a.2 with hG
    have hGadj : ∀ a b, G.Adj a b ↔
        a.1 = b.1 ∧ ((∃ x, b.2 = x :: a.2) ∨ ∃ x, a.2 = x :: b.2) := by
      intro a b
      rw [hG, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1.symm, Or.inr h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun hab => ?_, ?_⟩
        · subst hab
          rcases h2 with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
          · have := congrArg List.length hx; simp at this
        · rcases h2 with h2 | h2
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1.symm, h2⟩
    have hq : ∀ e, e ∉ G.edgeSet → intensityProfile J β e = 0 := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
      rw [SimpleGraph.mem_edgeSet, hGadj] at he
      apply Subtype.ext
      change 1 - Real.exp (-(β : ℝ) * (J s(a, b) : ℝ)) = 0
      rw [J_eq_zero_of_not_adj hJ he]
      simp
    have hae := ae_config_subset_host G (intensityProfile J β) hq
    rw [← law_map_preimage_sym2Map f, Measure.map_apply (measurable_preimage_sym2Map _)
      (measurableSet_cluster_infinite _)]
    refine measure_mono_ae ?_
    filter_upwards [hae] with ω hω hinf
    -- every vertex reachable from `(n, [])` is `(n, u)` with `u` reachable in the pull-back
    have hreach : ∀ {a w : ℕ × List (Fin 2)}, (openGraph ω).Reachable a w → ∀ u₀,
        a = (n, u₀) → (Sym2.map f ⁻¹' ω : Config (List (Fin 2))) ∈ conn [] u₀ →
        ∃ u, w = (n, u) ∧ (Sym2.map f ⁻¹' ω : Config (List (Fin 2))) ∈ conn [] u := by
      intro a w hr
      obtain ⟨p⟩ := hr
      induction p with
      | nil => exact fun u₀ ha h0 => ⟨u₀, ha, h0⟩
      | @cons a b c hab p ih =>
        intro u₀ ha h0
        rw [openGraph_adj_iff] at hab
        have hG' := hGadj a b |>.1 (hω hab.1)
        obtain ⟨b1, b2⟩ := b
        subst ha
        have hb1 : b1 = n := hG'.1.symm
        subst hb1
        refine ih b2 rfl (conn_trans h0 (mem_conn_of_mem (fun h => hab.2 (by rw [h])) ?_))
        change Sym2.map f s(u₀, b2) ∈ ω
        rw [Sym2.map_mk]
        exact hab.1
    have hsub : cluster ω (n, []) ⊆ f '' cluster (Sym2.map f ⁻¹' ω : Config (List (Fin 2))) [] := by
      intro w hw
      obtain ⟨u, rfl, hu⟩ := hreach hw [] rfl (by rw [conn_self]; trivial)
      exact ⟨u, hu, rfl⟩
    exact Set.Infinite.of_image f ((hinf : (cluster ω (n, [])).Infinite).mono hsub)
  · exact law_cluster_infinite_le_of_embedding f (q := fun e => intensityProfile J β
      (Sym2.map f e)) (fun e _ => le_rfl) []

omit hJ in
/-- `1/2 < 1 - exp(-β c_n)` exactly when `1 + 1/(n+1) < β`. -/
theorem half_lt_one_sub_exp_iff (β : ℝ) (n : ℕ) :
    1 / 2 < 1 - Real.exp (-β * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1)))) ↔
      1 + 1 / ((n : ℝ) + 1) < β := by
  have ht : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2 : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log two_pos, one_div]
  constructor
  · intro h
    have h' : Real.exp (-β * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1)))) < Real.exp (-Real.log 2) := by
      rw [← h2]; linarith
    rw [Real.exp_lt_exp] at h'
    have : Real.log 2 < β * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1))) := by linarith
    rw [mul_div_assoc', lt_div_iff₀ ht] at this
    nlinarith
  · intro h
    have : Real.log 2 < β * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1))) := by
      rw [mul_div_assoc', lt_div_iff₀ ht]; nlinarith
    have h' : Real.exp (-β * (Real.log 2 / (1 + 1 / ((n : ℝ) + 1)))) < Real.exp (-Real.log 2) := by
      rw [Real.exp_lt_exp]; linarith
    rw [← h2] at h'
    linarith

/-- At the root of the `n`-th tree: percolation exactly above `1 + 1/(n+1)`. -/
theorem law_root_pos_iff (β : ℝ≥0) (n : ℕ) :
    0 < law (intensityProfile J β) {ω | (cluster ω (n, [])).Infinite} ↔
      1 + 1 / ((n : ℝ) + 1) < β := by
  rw [law_root_eq hJ, binaryTree_theta_pos_iff _ _ (treeProfile_eq hJ β n)]
  exact half_lt_one_sub_exp_iff β n

/-- **The percolation threshold at every vertex.** For every vertex `(n, u)` and `β`,
`θ > 0` exactly when `β > 1 + 1/(n+1)`. -/
theorem law_cluster_infinite_pos_iff (β : ℝ≥0) (v : ℕ × List (Fin 2)) :
    0 < law (intensityProfile J β) {ω | (cluster ω v).Infinite} ↔
      1 + 1 / ((v.1 : ℝ) + 1) < β := by
  obtain ⟨n, u⟩ := v
  rcases eq_zero_or_pos β with rfl | hβ
  · have h0 := law_exists_cluster_infinite_eq_zero_of_forall_eq_zero
      (q := intensityProfile J 0) (intensityProfile_zero J)
    have : law (intensityProfile J 0) {ω | (cluster ω (n, u)).Infinite} = 0 :=
      measure_mono_null (fun ω (h : (cluster ω (n, u)).Infinite) =>
        (show ∃ x, (cluster ω x).Infinite from ⟨(n, u), h⟩)) h0
    rw [this]
    simp only [lt_self_iff_false, NNReal.coe_zero, false_iff, not_lt]
    positivity
  · rw [← law_root_pos_iff hJ β n]
    refine law_cluster_infinite_pos_iff_of_reachable _ ?_
    -- `(n, u)` is joined to `(n, [])` through positive-probability edges
    induction u with
    | nil => rfl
    | cons x u ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      refine (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨?_, by simp⟩
      change 0 < intensityProfile J β s((n, x :: u), (n, u))
      rw [intensityProfile_pos_iff J hβ]
      have h := hJ (n, x :: u) (n, u)
      have hc : (n, x :: u).1 = (n, u).1 ∧ ((∃ y, (n, u).2 = y :: (n, x :: u).2) ∨
          ∃ y, (n, x :: u).2 = y :: (n, u).2) := ⟨rfl, Or.inr ⟨x, rfl⟩⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
      have : 0 < Real.log 2 / (1 + 1 / ((n : ℝ) + 1)) :=
        div_pos (Real.log_pos one_lt_two) (by positivity)
      exact_mod_cast h ▸ this

/-- **Item 1.** Every vertex of the `n`-th tree has root threshold `1 + 1/(n+1)`. -/
theorem rootCriticalIntensity_eq (v : ℕ × List (Fin 2)) :
    rootCriticalIntensity J v = ENNReal.ofReal (1 + 1 / ((v.1 : ℝ) + 1)) := by
  rw [← sInf_coe_gt_eq, rootCriticalIntensity]
  congr 1
  ext b
  exact exists_congr fun β => and_congr_right' (law_cluster_infinite_pos_iff hJ β v)

/-- Some infinite cluster exists with positive probability exactly when `β > 1`. -/
theorem law_exists_pos_iff (β : ℝ≥0) :
    0 < law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} ↔ 1 < (β : ℝ) := by
  rw [law_exists_cluster_infinite_pos_iff]
  constructor
  · rintro ⟨v, hv⟩
    have := (law_cluster_infinite_pos_iff hJ β v).1 hv
    have : 0 < 1 / ((v.1 : ℝ) + 1) := by positivity
    linarith
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    exact ⟨(n, []), (law_cluster_infinite_pos_iff hJ β (n, [])).2 (by
      simp only; linarith)⟩

/-- **Item 2.** The global threshold is `1`. -/
theorem globalCriticalIntensity_eq_one : globalCriticalIntensity J = 1 := by
  rw [← ENNReal.ofReal_one, ← sInf_coe_gt_eq, globalCriticalIntensity]
  congr 1
  ext b
  exact exists_congr fun β => and_congr_right' (law_exists_pos_iff hJ β)

/-- **Item 3, at the threshold.** At `β = 1` there is almost surely no infinite cluster. -/
theorem law_exists_cluster_infinite_at_one :
    law (intensityProfile J 1) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
  by_contra h
  have := (law_exists_pos_iff hJ 1).1 (pos_iff_ne_zero.2 h)
  simp at this

/-- **Item 3, above the threshold.** At every `β > 1` there is almost surely an infinite
cluster. -/
theorem law_exists_cluster_infinite_of_one_lt {β : ℝ≥0} (hβ : 1 < β) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 1 := by
  rcases law_exists_cluster_infinite_eq_zero_or_one (intensityProfile J β) with h | h
  · have := (law_exists_pos_iff hJ β).2 (by exact_mod_cast hβ)
    rw [h] at this
    exact absurd this (lt_irrefl 0)
  · exact h

/-- **Item 4.** Every intensity is at most `log 2`, and every vertex has at most three
neighbours of positive intensity. -/
theorem kernel_le_log_two (e : Sym2 (ℕ × List (Fin 2))) : (J e : ℝ) ≤ Real.log 2 := by
  induction e using Sym2.ind with
  | h a b =>
  rw [hJ]
  split_ifs
  · rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ 1 / ((a.1 : ℝ) + 1) := by positivity
    nlinarith [Real.log_pos one_lt_two]
  · exact (Real.log_pos one_lt_two).le

theorem encard_positive_neighbours_le_three (v : ℕ × List (Fin 2)) :
    {w | 0 < J s(v, w)}.encard ≤ 3 := by
  obtain ⟨n, u⟩ := v
  have hsub : {w | 0 < J s((n, u), w)} ⊆ {(n, 0 :: u), (n, 1 :: u), (n, u.tail)} := by
    intro w hw
    have hw' : (0 : ℝ) < J s((n, u), w) := by exact_mod_cast hw
    rw [hJ] at hw'
    split_ifs at hw' with h
    · obtain ⟨w1, w2⟩ := w
      obtain ⟨h1, h2 | h2⟩ := h
      · obtain ⟨x, hx⟩ := h2
        simp only at h1 hx
        subst h1 hx
        fin_cases x <;> simp
      · obtain ⟨x, hx⟩ := h2
        simp only at h1 hx
        subst h1 hx
        simp
    · exact absurd hw' (lt_irrefl 0)
  refine (Set.encard_le_encard hsub).trans ?_
  refine (Set.encard_insert_le _ _).trans ?_
  rw [show (3 : ℕ∞) = 2 + 1 by norm_num]
  gcongr
  refine (Set.encard_insert_le _ _).trans ?_
  rw [Set.encard_singleton]
  norm_num

end Model

/-- **The unattained threshold.** Some countable intensity model has global threshold `1` while
every rooted threshold is strictly greater than `1`. -/
theorem exists_globalCriticalIntensity_eq_one_lt_rootCriticalIntensity :
    ∃ J : Sym2 (ℕ × List (Fin 2)) → ℝ≥0,
      globalCriticalIntensity J = 1 ∧ ∀ v, 1 < rootCriticalIntensity J v := by
  obtain ⟨J, hJ⟩ := exists_kernel
  refine ⟨J, globalCriticalIntensity_eq_one hJ, fun v => ?_⟩
  rw [rootCriticalIntensity_eq hJ v, ENNReal.one_lt_ofReal]
  have : 0 < 1 / ((v.1 : ℝ) + 1) := by positivity
  linarith

/-! ### Non-vacuity -/

/-- The model exists, and at `k = 1` (the tree with index `0`) the root threshold is `2`. -/
example : ∃ J : Sym2 (ℕ × List (Fin 2)) → ℝ≥0, rootCriticalIntensity J (0, []) = 2 ∧
    globalCriticalIntensity J = 1 := by
  obtain ⟨J, hJ⟩ := exists_kernel
  refine ⟨J, ?_, globalCriticalIntensity_eq_one hJ⟩
  rw [rootCriticalIntensity_eq hJ]
  norm_num

end PercLib.Models
