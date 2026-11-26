/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Cutoff clusters and the exact omitted row on the hierarchical lattice, and the sharp small-intensity
bound. New proofs from the existing hierarchical geometry, the row-sum and intensity theorems of
`PercLib.Percolation.Bond.RowSum` and `PercLib.Percolation.Bond.Intensity` and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679's ENNReal geometric series and graph reachability. No
upstream code is copied.
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.IntensityScaling
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PercLib.Percolation.Bond.ZeroOne
public import PercLib.Percolation.Bond.Diagonal.Probability

/-! # Cutoff clusters on the hierarchical lattice

The lattice is `ℕ →₀ (Fin d → ZMod L)`, the level of a displacement `z` is
`z.support.sup Nat.succ`, `N = L^d`, and the kernel is `J s(x,y) = C r^level(y − x)`.

* KL29 (a) `ae_cluster_subset_ball`: if the profile vanishes on pairs of level above `n`,
  almost surely every cluster lies in the level-`n` ball of its base vertex and has at most
  `N^n` points.
* KL29 (b) `tsum_level_gt_eq`: the kernel mass above level `n` is
  `C (N − 1) r / (1 − N r) · (N r)^n` (an identity in `ℝ≥0∞`, with no hypothesis).
* KL29 (c) `tsum_level_gt_intensity_le`: the omitted probability row of the exponential
  family is at most `β` times (b).
* B6KD (sharp form): with `M = C (N − 1) r / (1 − N r)` and `N r < 1`, the off-diagonal row
  of `J` is exactly `M`, so `β M < 1` gives `chi ≤ (1 − β M)⁻¹` and finite clusters, both
  thresholds are at least `M⁻¹`, and `M = 0` gives singleton clusters, `chi = 1` and
  infinite thresholds.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

/-! ### Clusters inside a host graph, allowing arbitrary loop probabilities -/

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- If the profile vanishes on every non-loop pair outside a graph `G`, then almost surely
the open graph is a subgraph of `G`. Loop probabilities are arbitrary. A corollary of
`ae_openGraph_le_support`. -/
theorem ae_openGraph_le_of_offDiagonal (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hq : ∀ x y, x ≠ y → ¬G.Adj x y → q s(x, y) = 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ G := by
  filter_upwards [ae_openGraph_le_support q] with ω hω
  intro x y hadj
  have h := hω hadj
  rw [SimpleGraph.fromEdgeSet_adj] at h
  by_contra hG
  have h0 : (0 : unitInterval) < q s(x, y) := h.1
  rw [hq x y h.2 hG] at h0
  exact lt_irrefl _ h0

/-- If the profile vanishes off the diagonal, almost surely every cluster is a singleton. -/
theorem ae_cluster_eq_singleton_of_offDiagonal (q : Sym2 V → unitInterval)
    (hq : ∀ x y, x ≠ y → q s(x, y) = 0) :
    ∀ᵐ ω ∂law q, ∀ x, cluster ω x = {x} := by
  filter_upwards [ae_openGraph_le_of_offDiagonal ⊥ q fun x y h _ => hq x y h] with ω hω
  intro x
  ext y
  constructor
  · intro hy
    exact (SimpleGraph.reachable_bot.1 (SimpleGraph.Reachable.mono hω hy)).symm
  · rintro rfl
    exact mem_cluster_self ω y

/-! ### Kernels that agree off the diagonal -/

omit [Countable V] in
/-- Kernels that agree off the diagonal give intensity profiles that agree off the diagonal. -/
theorem intensityProfile_eq_of_offDiagonal {J J' : Sym2 V → ℝ≥0}
    (h : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y)) (β : ℝ≥0) :
    ∀ e, ¬ e.IsDiag → intensityProfile J β e = intensityProfile J' β e := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    have hxy : x ≠ y := by simpa using he
    apply Subtype.ext
    change 1 - Real.exp (-(β : ℝ) * (J s(x, y) : ℝ)) =
      1 - Real.exp (-(β : ℝ) * (J' s(x, y) : ℝ))
    rw [h x y hxy]

omit [Countable V] in
/-- Configurations that agree off the diagonal have the same open graph. -/
theorem openGraph_eq_of_sdiff_diagSet_eq {ω ω' : Config V}
    (h : ω \ Sym2.diagSet = ω' \ Sym2.diagSet) : openGraph ω = openGraph ω' := by
  rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]

/-- The probability of an infinite cluster at `x` is diagonal-insensitive. -/
theorem law_cluster_infinite_eq_of_offDiagonal (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) (x : V) :
    law p {ω | (cluster ω x).Infinite} = law q {ω | (cluster ω x).Infinite} :=
  law_event_eq_of_offDiagonal p q hpq (measurableSet_cluster_infinite x) fun ω ω' hω => by
    simp only [Set.mem_ofPred_eq, cluster, openGraph_eq_of_sdiff_diagSet_eq hω]

/-- The probability that some cluster is infinite is diagonal-insensitive. -/
theorem law_exists_cluster_infinite_eq_of_offDiagonal (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) :
    law p {ω | ∃ x, (cluster ω x).Infinite} = law q {ω | ∃ x, (cluster ω x).Infinite} :=
  law_event_eq_of_offDiagonal p q hpq measurableSet_exists_cluster_infinite fun ω ω' hω => by
    simp only [Set.mem_ofPred_eq, cluster, openGraph_eq_of_sdiff_diagSet_eq hω]

/-- The root critical intensity depends only on the kernel off the diagonal. -/
theorem rootCriticalIntensity_eq_of_offDiagonal {J J' : Sym2 V → ℝ≥0}
    (h : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y)) (x : V) :
    rootCriticalIntensity J x = rootCriticalIntensity J' x := by
  unfold rootCriticalIntensity
  simp_rw [law_cluster_infinite_eq_of_offDiagonal _ _ (intensityProfile_eq_of_offDiagonal h _)]

/-- The global critical intensity depends only on the kernel off the diagonal. -/
theorem globalCriticalIntensity_eq_of_offDiagonal {J J' : Sym2 V → ℝ≥0}
    (h : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y)) :
    globalCriticalIntensity J = globalCriticalIntensity J' := by
  unfold globalCriticalIntensity
  simp_rw [law_exists_cluster_infinite_eq_of_offDiagonal _ _
    (intensityProfile_eq_of_offDiagonal h _)]

end PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-! ### KL29 (a): cutoff clusters lie in balls -/

omit [NeZero L] in
/-- Reachability in the graph of pairs of level at most `n` stays in the level-`n` ball. -/
theorem level_le_of_reachable (n : ℕ) {x y : ℕ →₀ (Fin d → ZMod L)}
    (h : (SimpleGraph.fromRel fun a b : ℕ →₀ (Fin d → ZMod L) =>
      (b - a).support.sup Nat.succ ≤ n).Reachable x y) :
    (y - x).support.sup Nat.succ ≤ n := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
    rw [SimpleGraph.fromRel_adj] at hab
    have hab' : (b - a).support.sup Nat.succ ≤ n := by
      rcases hab.2 with h | h
      · exact h
      · rwa [level_sub_comm]
    exact (level_sub_le_max a b c).trans (max_le hab' ih)

/-- The level-`n` ball around `x` has at most `N^n` points. -/
theorem encard_level_ball (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ) :
    {y : ℕ →₀ (Fin d → ZMod L) | (y - x).support.sup Nat.succ ≤ n}.encard =
      (((L ^ d) ^ n : ℕ) : ℕ∞) := by
  rw [level_ball_eq_translate, (add_right_injective x).encard_image,
    ← (finite_level_ball n).cast_ncard_eq, ← Nat.card_coe_set_eq]
  congr 1
  exact card_ball n

/-- **Cutoff clusters are trapped in balls.** If the profile vanishes on every pair of level above
`n` (only bonds of level at most `n` are retained), then almost surely every cluster lies in the
level-`n` ball of its base vertex, so its volume is at most `N^n`. Loop probabilities are arbitrary.
-/
theorem ae_cluster_subset_ball (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval) (n : ℕ)
    (hq : ∀ x y, n < (y - x).support.sup Nat.succ → q s(x, y) = 0) :
    ∀ᵐ ω ∂law q, ∀ x, cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} ∧
      (cluster ω x).encard ≤ (((L ^ d) ^ n : ℕ) : ℕ∞) := by
  let G := SimpleGraph.fromRel fun a b : ℕ →₀ (Fin d → ZMod L) =>
    (b - a).support.sup Nat.succ ≤ n
  have hG : ∀ x y, x ≠ y → ¬G.Adj x y → q s(x, y) = 0 := fun x y hxy hadj => by
    refine hq x y (not_le.1 fun h => hadj ?_)
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hxy, Or.inl h⟩
  filter_upwards [ae_openGraph_le_of_offDiagonal G q hG] with ω hω
  intro x
  have hsub : cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} := fun y hy =>
    level_le_of_reachable n (SimpleGraph.Reachable.mono hω hy)
  exact ⟨hsub, (Set.encard_le_encard hsub).trans_eq (encard_level_ball x n)⟩

/-! ### KL29 (b), (c): the omitted row -/

open Classical in
/-- **The omitted kernel mass.** The kernel mass above level `n` is
`C (N − 1) r / (1 − N r) · (N r)^n`. In `ℝ≥0∞` this holds with no hypothesis on `N r`. -/
theorem tsum_level_gt_eq (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ)) (n : ℕ)
    (x : ℕ →₀ (Fin d → ZMod L)) :
    (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
      (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
        ((L : ℝ≥0∞) ^ d * r) ^ n := by
  set ρ : ℝ≥0∞ := (L : ℝ≥0∞) ^ d * r
  set a : ℝ≥0∞ := (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r
  have h1 : (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
      ∑' z : ℕ →₀ (Fin d → ZMod L), (fun m : ℕ => if n < m then
        (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ m else 0) (z.support.sup Nat.succ) := by
    rw [← (Equiv.addLeft x).tsum_eq]
    refine tsum_congr fun z => ?_
    simp [hJ]
  rw [h1, tsum_radial_eq (d := d) (L := L) (fun m : ℕ => if n < m then
    (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ m else 0)]
  have hcard (k : ℕ) : (L ^ d) ^ (k + 1) - (L ^ d) ^ k = (L ^ d - 1) * (L ^ d) ^ k := by
    rw [pow_succ, Nat.mul_sub_right_distrib, one_mul, mul_comm]
  simp only [Nat.not_lt_zero, ite_false, zero_add, hcard]
  have h2 : ∀ k : ℕ, (((L ^ d - 1) * (L ^ d) ^ k : ℕ) : ℝ≥0∞) *
      (if n < k + 1 then (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (k + 1) else 0) =
      if n ≤ k then a * ρ ^ k else 0 := by
    intro k
    by_cases hk : n ≤ k
    · rw [ite_eq_left (by omega), ite_eq_left hk]
      simp only [a, ρ]
      push_cast
      ring
    · rw [ite_eq_right (by omega), ite_eq_right hk, mul_zero]
  simp_rw [h2]
  have h3 : (∑' k : ℕ, if n ≤ k then a * ρ ^ k else 0) =
      ∑' j : ℕ, (fun k : ℕ => if n ≤ k then a * ρ ^ k else 0) (j + n) := by
    refine ((add_left_injective n).tsum_eq fun k hk => ?_).symm
    have hk' : n ≤ k := by
      by_contra h
      exact hk (by simp [h])
    exact ⟨k - n, by simp only; omega⟩
  rw [h3]
  simp only [Nat.le_add_left, ite_true, pow_add]
  rw [ENNReal.tsum_mul_left]
  simp_rw [mul_comm (ρ ^ _) (ρ ^ n)]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]
  ring

/-- **The omitted probability row.** In the exponential family the omitted probability row above
level `n` is at most `β` times the omitted kernel mass. -/
theorem tsum_level_gt_intensity_le (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ)) (β : ℝ≥0) (n : ℕ)
    (x : ℕ →₀ (Fin d → ZMod L)) :
    (∑' y, if n < (y - x).support.sup Nat.succ then
        (unitInterval.toNNReal (intensityProfile J β s(x, y)) : ℝ≥0∞) else 0) ≤
      (β : ℝ≥0∞) * ((C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
        ((L : ℝ≥0∞) ^ d * r) ^ n) := by
  rw [← tsum_level_gt_eq J C r hJ n x, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs
  · rw [← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β _)
  · simp

/-! ### B6KD, sharp form -/

/-- With `N r < 1`, the off-diagonal row of the hierarchical kernel is exactly
`M = C (N − 1) r / (1 − N r)`. -/
theorem rowSum_hierarchical_eq (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (v : ℕ →₀ (Fin d → ZMod L)) :
    rowSum (fun e => (J e : ℝ≥0∞)) v =
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) := by
  have h := tsum_level_gt_eq J C r hJ 0 v
  rw [pow_zero, mul_one] at h
  have e : rowSum (fun e => (J e : ℝ≥0∞)) v =
      ∑' w, if 0 < (w - v).support.sup Nat.succ then (J s(v, w) : ℝ≥0∞) else 0 := by
    refine tsum_congr fun w => ?_
    by_cases hw : w = v
    · simp [hw]
    · have : 0 < (w - v).support.sup Nat.succ :=
        Nat.pos_of_ne_zero fun h0 => hw ((level_sub_eq_zero_iff v w).1 h0).symm
      simp [hw, this]
  rw [e, h]
  have hne : (1 - (L : ℝ≥0) ^ d * r) ≠ 0 := (tsub_pos_of_lt hr).ne'
  rw [ENNReal.coe_div hne]
  push_cast
  rfl

/-- **Susceptibility.** With `N r < 1` and `β M < 1`, `chi ≤ (1 − β M)⁻¹`. -/
theorem chi_intensity_le_hierarchical_sharp (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : ℕ →₀ (Fin d → ZMod L)) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  chi_intensity_le J _ (fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le) β hβ x

/-- **Finiteness.** With `N r < 1` and `β M < 1`, almost surely every cluster is
finite. -/
theorem law_exists_infinite_hierarchical_eq_zero (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0 :=
  law_exists_infinite_intensity_eq_zero J _
    (fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le) β hβ

/-- **Global threshold.** With `N r < 1`, the global threshold is at least `M⁻¹`
(and is `⊤` when `M = 0`). -/
theorem inv_le_globalCriticalIntensity_hierarchical_sharp
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) :
    ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      globalCriticalIntensity J :=
  inv_le_globalCriticalIntensity J _ fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le

/-- **Root threshold.** With `N r < 1`, every root threshold is at least `M⁻¹`. -/
theorem inv_le_rootCriticalIntensity_hierarchical_sharp
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (x : ℕ →₀ (Fin d → ZMod L)) :
    ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      rootCriticalIntensity J x :=
  inv_le_rootCriticalIntensity J _ (fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le) x

/-- **`M = 0`.** With `N r < 1` and `M = 0`: at every parameter every cluster is
almost surely a singleton, `chi = 1`, and both thresholds are `⊤`. -/
theorem hierarchical_of_M_eq_zero (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1)
    (hM : C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) = 0) (β : ℝ≥0) :
    (∀ᵐ ω ∂law (intensityProfile J β), ∀ x, cluster ω x = {x}) ∧
      (∀ x, chi (intensityProfile J β) x = 1) ∧
      globalCriticalIntensity J = ⊤ ∧ ∀ x, rootCriticalIntensity J x = ⊤ := by
  have hrow0 : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 0 := fun v => by
    rw [rowSum_hierarchical_eq J C r hJ hr v, hM, ENNReal.coe_zero]
  refine ⟨ae_cluster_eq_singleton_of_offDiagonal _ fun x y hxy => ?_,
    chi_intensity_eq_one_of_rowSum_zero J hrow0 β,
    globalCriticalIntensity_eq_top_of_rowSum_zero J hrow0,
    rootCriticalIntensity_eq_top_of_rowSum_zero J hrow0⟩
  refine intensityProfile_eq_zero_of_eq_zero J ?_ β
  have hx := hrow0 x
  rw [rowSum_def] at hx
  have h0 := ENNReal.tsum_eq_zero.1 (nonpos_iff_eq_zero.1 hx) y
  rw [ite_eq_right (Ne.symm hxy), ENNReal.coe_eq_zero] at h0
  exact h0

/-! ### Kernels prescribed off the diagonal only

The statements above take the radial identity on all pairs, including the diagonal. The
versions below assume it for distinct pairs only (the diagonal is arbitrary) and transfer
through the all-pairs kernel of `exists_hierarchical_kernel`. -/

/-- **Cutoff clusters are trapped in balls, every configuration.** If every open pair has level at
most `n`, every cluster lies in the level-`n` ball of its base vertex and has at most `N^n`
vertices. -/
theorem cluster_subset_level_ball_of_forall (n : ℕ) (ω : Config (ℕ →₀ (Fin d → ZMod L)))
    (hω : ∀ a b, a ≠ b → s(a, b) ∈ ω → (b - a).support.sup Nat.succ ≤ n)
    (x : (ℕ →₀ (Fin d → ZMod L))) :
    cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} ∧
      (cluster ω x).encard ≤ (((L ^ d) ^ n : ℕ) : ℕ∞) := by
  have hle : openGraph ω ≤ SimpleGraph.fromRel fun a b : (ℕ →₀ (Fin d → ZMod L)) =>
      (b - a).support.sup Nat.succ ≤ n := by
    intro a b hab
    rw [openGraph_adj_iff] at hab
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hab.2, Or.inl (hω a b hab.2 hab.1)⟩
  have hsub : cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} := fun y hy =>
    level_le_of_reachable n (SimpleGraph.Reachable.mono hle hy)
  exact ⟨hsub, (Set.encard_le_encard hsub).trans_eq (encard_level_ball x n)⟩

omit [NeZero L] in
private theorem ne_of_lt_level {n : ℕ} {x y : (ℕ →₀ (Fin d → ZMod L))}
    (h : n < (y - x).support.sup Nat.succ) :
    x ≠ y := by
  rintro rfl
  simp at h

/-- `tsum_level_gt_eq` with the kernel prescribed off the diagonal only. -/
theorem tsum_level_gt_eq_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ)) (n : ℕ)
    (x : (ℕ →₀ (Fin d → ZMod L))) :
    (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
      (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
        ((L : ℝ≥0∞) ^ d * r) ^ n := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  rw [← tsum_level_gt_eq J' C r hJ' n x]
  refine tsum_congr fun y => ?_
  split_ifs with h
  · rw [hJ x y (ne_of_lt_level h), hJ' x y]
  · rfl

/-- `tsum_level_gt_intensity_le` with the kernel prescribed off the diagonal only. -/
theorem tsum_level_gt_intensity_le_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ)) (β : ℝ≥0)
    (n : ℕ) (x : (ℕ →₀ (Fin d → ZMod L))) :
    (∑' y, if n < (y - x).support.sup Nat.succ then
        (unitInterval.toNNReal (intensityProfile J β s(x, y)) : ℝ≥0∞) else 0) ≤
      (β : ℝ≥0∞) * ((C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
        ((L : ℝ≥0∞) ^ d * r) ^ n) := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  refine le_trans (le_of_eq ?_) (tsum_level_gt_intensity_le J' C r hJ' β n x)
  refine tsum_congr fun y => ?_
  split_ifs with h
  · rw [intensityProfile_eq_of_offDiagonal hJJ' β s(x, y) (by simpa using ne_of_lt_level h)]
  · rfl

/-- **Sharp subcritical bound** with the kernel prescribed off the diagonal only. -/
theorem chi_intensity_le_hierarchical_sharp_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : (ℕ →₀ (Fin d → ZMod L))) :
    chi (intensityProfile J β) x ≤
      (1 - (β : ℝ≥0∞) *
        ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞))⁻¹ := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [chi_eq_of_offDiagonal _ _ (intensityProfile_eq_of_offDiagonal hJJ' β) x]
  exact chi_intensity_le_hierarchical_sharp J' C r hJ' hr β hβ x

/-- **Sharp subcritical bound**, no infinite cluster, with the kernel prescribed off the diagonal
only. -/
theorem law_exists_infinite_hierarchical_eq_zero_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [law_exists_cluster_infinite_eq_of_offDiagonal _ _
    (intensityProfile_eq_of_offDiagonal hJJ' β)]
  exact law_exists_infinite_hierarchical_eq_zero J' C r hJ' hr β hβ

/-- **Sharp threshold bound**, global threshold, with the kernel prescribed off the diagonal only.
-/
theorem inv_le_globalCriticalIntensity_hierarchical_sharp_of_ne
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) :
    ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      globalCriticalIntensity J := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [globalCriticalIntensity_eq_of_offDiagonal hJJ']
  exact inv_le_globalCriticalIntensity_hierarchical_sharp J' C r hJ' hr

/-- **Sharp threshold bound**, root threshold, with the kernel prescribed off the diagonal only. -/
theorem inv_le_rootCriticalIntensity_hierarchical_sharp_of_ne
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (x : (ℕ →₀ (Fin d → ZMod L))) :
    ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      rootCriticalIntensity J x := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [rootCriticalIntensity_eq_of_offDiagonal hJJ']
  exact inv_le_rootCriticalIntensity_hierarchical_sharp J' C r hJ' hr x

/-- **The case `M = 0`.** If `M = 0` (with `N r < 1`), every off-diagonal intensity vanishes. -/
theorem eq_zero_of_hierarchical_M_eq_zero (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1)
    (hM : C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) = 0)
    {x y : (ℕ →₀ (Fin d → ZMod L))} (hxy : x ≠ y) : J s(x, y) = 0 := by
  have hden : (1 - (L : ℝ≥0) ^ d * r) ≠ 0 := (tsub_pos_of_lt hr).ne'
  rcases div_eq_zero_iff.1 hM with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with hC | hN
      · rw [hJ x y hxy, hC, zero_mul]
      · exfalso
        have hN' : L ^ d - 1 = 0 := by exact_mod_cast hN
        have hcard : Fintype.card (Fin d → ZMod L) ≤ 1 := by
          rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
          omega
        have := Fintype.card_le_one_iff_subsingleton.1 hcard
        exact hxy (Finsupp.ext fun i => Subsingleton.elim _ _)
    · have hlv : (y - x).support.sup Nat.succ ≠ 0 := by
        rw [Ne, level_eq_zero_iff, sub_eq_zero]
        exact fun e => hxy e.symm
      rw [hJ x y hxy, h, zero_pow hlv, mul_zero]
  · exact absurd h hden

/-- **`M = 0`**, with the kernel prescribed off the diagonal only. -/
theorem hierarchical_of_M_eq_zero_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1)
    (hM : C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) = 0) (β : ℝ≥0) :
    (∀ᵐ ω ∂law (intensityProfile J β), ∀ x, cluster ω x = {x}) ∧
      (∀ x, chi (intensityProfile J β) x = 1) ∧
      globalCriticalIntensity J = ⊤ ∧ ∀ x, rootCriticalIntensity J x = ⊤ := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  obtain ⟨-, hchi, hglob, hroot⟩ := hierarchical_of_M_eq_zero J' C r hJ' hr hM β
  refine ⟨?_, fun x => ?_, ?_, fun x => ?_⟩
  · exact ae_cluster_eq_singleton_of_offDiagonal _ fun x y hxy =>
      intensityProfile_eq_zero_of_eq_zero J
        (eq_zero_of_hierarchical_M_eq_zero J C r hJ hr hM hxy) β
  · rw [chi_eq_of_offDiagonal _ _ (intensityProfile_eq_of_offDiagonal hJJ' β) x]
    exact hchi x
  · rw [globalCriticalIntensity_eq_of_offDiagonal hJJ']
    exact hglob
  · rw [rootCriticalIntensity_eq_of_offDiagonal hJJ']
    exact hroot x

/-- **Subcritical bound for `2Nr ≤ 1`**, `χ`, with `2Nr ≤ 1` and the kernel prescribed off the
diagonal only. -/
theorem chi_intensity_le_hierarchical_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * ((2 * C : ℝ≥0) : ℝ≥0∞) < 1)
    (x : (ℕ →₀ (Fin d → ZMod L))) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) * ((2 * C : ℝ≥0) : ℝ≥0∞))⁻¹ := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [chi_eq_of_offDiagonal _ _ (intensityProfile_eq_of_offDiagonal hJJ' β) x]
  exact chi_intensity_le_hierarchical J' C r hJ' hr β hβ x

/-- **Subcritical bound for `2Nr ≤ 1`**, global threshold, with the kernel prescribed off the
diagonal only. -/
theorem inv_le_globalCriticalIntensity_hierarchical_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) :
    ((2 * C : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [globalCriticalIntensity_eq_of_offDiagonal hJJ']
  exact inv_le_globalCriticalIntensity_hierarchical J' C r hJ' hr

/-- **Subcritical bound for `2Nr ≤ 1`**, root threshold, with the kernel prescribed off the diagonal
only. -/
theorem inv_le_rootCriticalIntensity_hierarchical_of_ne (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) (x : (ℕ →₀ (Fin d → ZMod L))) :
    ((2 * C : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x := by
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C r
  have hJJ' : ∀ x y, x ≠ y → J s(x, y) = J' s(x, y) := fun x y h => by rw [hJ x y h, hJ' x y]
  rw [rootCriticalIntensity_eq_of_offDiagonal hJJ']
  exact inv_le_rootCriticalIntensity_hierarchical J' C r hJ' hr x

end PercLib.Models

/-! ### Non-vacuity witnesses -/
section Witnesses

open PercLib.Models

/-- `L = 2, d = 1, C = 1, r = 1/4`: `N r = 1/2` and `M = 1/2`. At `β = 1` the
susceptibility is at most `2`, clusters are almost surely finite, both thresholds are at
least `2`, and the omitted kernel mass above level `n` is `2⁻¹ · 2⁻ⁿ`. -/
example (x : ℕ →₀ (Fin 1 → ZMod 2)) (n : ℕ) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
      (1 * ((2 ^ 1 - 1 : ℕ) : ℝ≥0) * (1 / 4) / (1 - (2 : ℝ≥0) ^ 1 * (1 / 4)) : ℝ≥0) = 1 / 2 ∧
      chi (intensityProfile J 1) x ≤ (1 - ((1 : ℝ≥0) : ℝ≥0∞) * ((1 / 2 : ℝ≥0) : ℝ≥0∞))⁻¹ ∧
      law (intensityProfile J 1) {ω | ∃ x, (cluster ω x).Infinite} = 0 ∧
      ((1 / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
      (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
        ((1 : ℝ≥0) : ℝ≥0∞) * ((2 ^ 1 - 1 : ℕ) : ℝ≥0∞) * ((1 / 4 : ℝ≥0) : ℝ≥0∞) /
          (1 - ((2 : ℕ) : ℝ≥0∞) ^ 1 * ((1 / 4 : ℝ≥0) : ℝ≥0∞)) *
          (((2 : ℕ) : ℝ≥0∞) ^ 1 * ((1 / 4 : ℝ≥0) : ℝ≥0∞)) ^ n := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  have hr : ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4) < 1 := by norm_num
  have hM : (1 * ((2 ^ 1 - 1 : ℕ) : ℝ≥0) * (1 / 4) / (1 - (2 : ℝ≥0) ^ 1 * (1 / 4)) : ℝ≥0) =
      1 / 2 := by
    rw [show (2 : ℝ≥0) ^ 1 * (1 / 4) = 1 / 2 by norm_num,
      show (1 : ℝ≥0) - 1 / 2 = 1 / 2 by
        rw [← NNReal.coe_inj]; rw [NNReal.coe_sub (by norm_num)]; norm_num]
    norm_num
  have hM' : (1 * ((2 ^ 1 - 1 : ℕ) : ℝ≥0) * (1 / 4) / (1 - ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4)) :
      ℝ≥0) = 1 / 2 := by exact_mod_cast hM
  have hβ : ((1 : ℝ≥0) : ℝ≥0∞) * ((1 / 2 : ℝ≥0) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]; norm_num
  refine ⟨J, hM, ?_, ?_, ?_, tsum_level_gt_eq J 1 (1 / 4) hJ n x⟩
  · have := chi_intensity_le_hierarchical_sharp J 1 (1 / 4) hJ hr 1 (by rw [hM']; exact hβ) x
    rwa [hM'] at this
  · exact law_exists_infinite_hierarchical_eq_zero J 1 (1 / 4) hJ hr 1 (by rw [hM']; exact hβ)
  · have := inv_le_globalCriticalIntensity_hierarchical_sharp J 1 (1 / 4) hJ hr
    rwa [hM'] at this

/-- `C = 0`: `M = 0`, so every cluster is almost surely a singleton, `chi = 1` and the
thresholds are `⊤`. -/
example (β : ℝ≥0) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
      (∀ᵐ ω ∂PercLib.Percolation.Bond.law (intensityProfile J β), ∀ x, cluster ω x = {x}) ∧
      globalCriticalIntensity J = ⊤ := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 0 (1 / 4)
  have hr : ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4) < 1 := by norm_num
  obtain ⟨h1, -, h3, -⟩ := hierarchical_of_M_eq_zero J 0 (1 / 4) hJ hr (by simp) β
  exact ⟨J, h1, h3⟩

end Witnesses
