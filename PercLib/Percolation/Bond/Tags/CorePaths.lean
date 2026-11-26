/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.PathComparison
public import PercLib.Percolation.Bond.PathLowerBounds
public import PercLib.Percolation.Bond.Pivotal
public import PercLib.Percolation.Bond.RowSumDecay
public import PercLib.Percolation.Bond.SelfAvoidingChi
public import PercLib.Percolation.Bond.TreeCounting

/-! Correspondence wrappers for path lower bounds, pivotal pairs, walk-length decay, bounded
degree path counting and path comparison of roots.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

open Classical in
/-- The bonds of a walk are all open with probability the product of their probabilities,
which bounds the two-point function from below. -/
@[tag "9IPM"]
theorem law_walk_open_le_tau (q : Sym2 V → unitInterval) {x y : V}
    (p : (⊤ : SimpleGraph V).Walk x y) :
    law q {ω | (p.edges.toFinset : Set (Sym2 V)) ⊆ ω} =
      ∏ e ∈ p.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) ∧
    (∏ e ∈ p.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ≤ tau q x y :=
  ⟨PercLib.Probability.prodBernoulli_subset q p.edges.toFinset, prod_le_tau_of_walk q p⟩

/-- Pivotal pairs for a connection: the endpoint characterisation for off-diagonal pairs,
diagonal pairs are never pivotal, on the connection event every pivotal pair is open and
lies on every open walk, and their number is at most the open distance. -/
@[tag "61PY"]
theorem pivotal_pairs_connection (ω : Config V) (x y : V) :
    (∀ a b : V, a ≠ b →
      ((insert s(a, b) ω ∈ conn x y ∧ ω \ {s(a, b)} ∉ conn x y) ↔
        ω \ {s(a, b)} ∉ conn x y ∧
          ((ω \ {s(a, b)} ∈ conn x a ∧ ω \ {s(a, b)} ∈ conn y b) ∨
            (ω \ {s(a, b)} ∈ conn x b ∧ ω \ {s(a, b)} ∈ conn y a)))) ∧
    (∀ e : Sym2 V, e.IsDiag → ¬ (insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y)) ∧
    (ω ∈ conn x y → ∀ e : Sym2 V, (insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y) →
      e ∈ ω ∧ ∀ w : (openGraph ω).Walk x y, e ∈ w.edges) ∧
    (ω ∈ conn x y →
      {e : Sym2 V | insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y}.encard ≤
        (openGraph ω).dist x y) :=
  ⟨fun a b hab => pivotal_conn_iff ω x y a b hab,
    fun _ he => not_pivotal_conn_of_isDiag ω x y he,
    fun hω _ he => ⟨mem_of_pivotal hω he.2, fun w => mem_edges_of_pivotal he.2 w⟩,
    fun hω => encard_pivotal_le_dist hω⟩

open Classical in
/-- With off-diagonal rows at most `m < 1`: the two-point mass on vertices all of whose
support walks from `x` have length at least `k` is at most `m^k/(1-m)`, the pointwise bound,
and the two-point function vanishes off the support component. -/
@[tag "VYCM"]
theorem tau_walk_length_decay [Countable V] (q : Sym2 V → unitInterval) (m : ℝ≥0∞)
    (hrow : ∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v ≤ m)
    (hm : m < 1) (x : V) :
    (∀ k : ℕ, ∑' y, (if ∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length
      then tau q x y else 0) ≤ m ^ k * (1 - m)⁻¹) ∧
    (∀ (y : V) (k : ℕ), (∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length) →
      tau q x y ≤ m ^ k * (1 - m)⁻¹) ∧
    (∀ y : V, ¬ (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y → tau q x y = 0) :=
  ⟨fun k => tsum_tau_walk_length_ge_le q m hrow hm x k,
    fun _ _ hk => tau_le_pow_of_walk_length_ge q m hrow hm hk,
    fun _ h => tau_eq_zero_of_not_reachable q h⟩

/-- Bounded degree tree counting: `P(|K_x| ≥ n+1) ≤ (Δ² p)^n` and `χ(x) ≤ (1 - Δ² p)⁻¹`. -/
@[tag "TEYS"]
theorem bounded_degree_volume_tail_chi [Countable V] (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (x : V) :
    (∀ n : ℕ, law q {ω | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard} ≤
      ((Δ : ℝ≥0∞) ^ 2 * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n) ∧
    chi q x ≤ (1 - (Δ : ℝ≥0∞) ^ 2 * (unitInterval.toNNReal p : ℝ≥0∞))⁻¹ :=
  ⟨fun n => law_le_encard_cluster_le G hΔ q p hoff hle x n,
    chi_le_inv_one_sub_of_degree_le G hΔ q p hoff hle x⟩

/-- Bounded degree two-point decay from a lower bound `D` on host walk lengths, and the
closed form of the series when `r = (Δ - 1) p < 1`. -/
@[tag "UOHI"]
theorem tau_le_of_walk_length_ge_closed_form [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval)
    (p : unitInterval) (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p) {x y : V} (hxy : x ≠ y) {D : ℕ}
    (hD : ∀ w : G.Walk x y, D ≤ w.length) :
    tau q x y ≤ (∑' n : ℕ, if D ≤ n + 1 then
      (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) else 0) ∧
    (((Δ : ℝ≥0∞) - 1) * (unitInterval.toNNReal p : ℝ≥0∞) < 1 →
      (∑' n : ℕ, if D ≤ n + 1 then
        (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1)
          else 0) =
        (Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) *
          (((Δ : ℝ≥0∞) - 1) * (unitInterval.toNNReal p : ℝ≥0∞)) ^ (max D 1 - 1) /
          (1 - ((Δ : ℝ≥0∞) - 1) * (unitInterval.toNNReal p : ℝ≥0∞))) := by
  refine ⟨tau_le_of_degree_le_of_length_ge G hΔ q p hoff hle hxy hD, fun hr => ?_⟩
  set P : ℝ≥0∞ := (unitInterval.toNNReal p : ℝ≥0∞)
  set r : ℝ≥0∞ := ((Δ : ℝ≥0∞) - 1) * P
  set k : ℕ := max D 1 - 1
  have hterm : ∀ n : ℕ, (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * P ^ (n + 1) =
      (Δ : ℝ≥0∞) * P * r ^ n := by
    intro n
    simp only [r, mul_pow, pow_succ]
    ring
  have hcond : ∀ n : ℕ, D ≤ n + 1 ↔ k ≤ n := by
    intro n
    simp only [k]
    omega
  simp_rw [hterm, hcond]
  rw [← (ENNReal.summable).sum_add_tsum_nat_add' (k := k)]
  have hzero : ∑ i ∈ range k, (if k ≤ i then (Δ : ℝ≥0∞) * P * r ^ i else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [not_le.2 hi]
  rw [hzero, zero_add]
  have hshift : ∀ i : ℕ, (if k ≤ i + k then (Δ : ℝ≥0∞) * P * r ^ (i + k) else 0) =
      (Δ : ℝ≥0∞) * P * r ^ k * r ^ i := by
    intro i
    simp only [Nat.le_add_left k i, ↓reduceIte, pow_add]
    ring
  simp_rw [hshift]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]

open Classical in
/-- Comparison of two roots joined by a walk `γ`: the volume tails, the percolation
probability and the susceptibility at `x` dominate `ρ_γ` times those at `y`; positivity of
the percolation probability and finiteness of the susceptibility are constant on components
of the support graph. -/
@[tag "C3OO"]
theorem path_comparison_of_roots [Countable V] (q : Sym2 V → unitInterval) :
    (∀ {x y : V} (γ : (⊤ : SimpleGraph V).Walk x y) (n : ℕ),
      (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) *
          law q {ω | (n : ℕ∞) ≤ (cluster ω y).encard} ≤
        law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard}) ∧
    (∀ {x y : V} (γ : (⊤ : SimpleGraph V).Walk x y),
      (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) *
        law q {ω | (cluster ω y).Infinite} ≤ law q {ω | (cluster ω x).Infinite}) ∧
    (∀ {x y : V} (γ : (⊤ : SimpleGraph V).Walk x y),
      (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) * chi q y ≤ chi q x) ∧
    (∀ {x y : V}, (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y →
      (0 < law q {ω | (cluster ω x).Infinite} ↔ 0 < law q {ω | (cluster ω y).Infinite})) ∧
    (∀ {x y : V}, (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y →
      (chi q x ≠ ∞ ↔ chi q y ≠ ∞)) :=
  ⟨fun γ n => prod_edges_mul_law_le_encard_le q γ n,
    fun γ => prod_edges_mul_law_cluster_infinite_le q γ,
    fun γ => prod_edges_mul_chi_le q γ,
    fun h => law_cluster_infinite_pos_iff_of_reachable q h,
    fun h => chi_ne_top_iff_of_reachable q h⟩

end PercLib.Percolation.Bond
