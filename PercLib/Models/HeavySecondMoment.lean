/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Host
public import PercLib.Percolation.Bond.ClusterMoments
public import PercLib.Percolation.Bond.VolumeTails
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Susceptibility two with infinite second moment (HRS7)

The vertex type is `Option (Σ k : ℕ, Fin (2^(k+1)))`: a root `none` and, for each `k`, a
path `C_k` on `Fin (2^(k+1))`. The profile `q` is `1` on the path edges, `4^(-(k+1))` on
the pair joining the root to the endpoint `0` of `C_k`, and `0` on every other pair. It
enters through the hypotheses `hpath`, `hroot` and `hsupp` (no new definition);
`exists_profile` shows such a profile exists.

* `chi_root_eq_two`: `χ(root) = 2`.
* `ae_cluster_root_finite`: the cluster of the root is finite almost surely.
* `lintegral_encard_sq_eq_top`: `E|K_root|² = ⊤`.
* `lintegral_exp_eq_top`: `E exp(t |K_root|) = ⊤` for every `t > 0`.
* `iSup_chi_eq_top`: `sup_v χ(v) = ⊤`.
* `connected_fromEdgeSet_pos`: the support graph `{e | 0 < q e}` is connected.

So the uniform hypothesis `sup_v χ(v) < ⊤` of Y84V cannot be weakened to `χ(o) < ⊤`.
Almost surely every path edge is open and only pairs of positive probability are open; on
that event the root is joined to a vertex of `C_k` exactly when the pair joining the root
to `C_k` is open.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-- `∑' v : Option α, f v = f none + ∑' a, f (some a)` in `ℝ≥0∞`. -/
theorem tsum_option_ennreal {α : Type*} (f : Option α → ℝ≥0∞) :
    ∑' v, f v = f none + ∑' a, f (some a) := by
  rw [← (Equiv.optionEquivSumPUnit.{0} α).symm.tsum_eq,
    Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  rw [tsum_fintype]
  simp

section Model

variable {q : Sym2 (Option (Σ k : ℕ, Fin (2 ^ (k + 1)))) → unitInterval}
  (hpath : ∀ (k : ℕ) (i j : Fin (2 ^ (k + 1))), i.val + 1 = j.val →
    q s(some ⟨k, i⟩, some ⟨k, j⟩) = 1)
  (hroot : ∀ k : ℕ, (q s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) : ℝ) = (1 / 4) ^ (k + 1))
  (hsupp : ∀ a b, q s(a, b) ≠ 0 →
    (∃ (k : ℕ) (i j : Fin (2 ^ (k + 1))), a = some ⟨k, i⟩ ∧ b = some ⟨k, j⟩ ∧
      (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∨
    ∃ k : ℕ, (a = none ∧ b = some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) ∨
      (b = none ∧ a = some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩))

include hpath in
/-- Almost surely every path edge is open and every open pair has positive probability. -/
theorem ae_good :
    ∀ᵐ ω ∂law q, (∀ (k : ℕ) (i : Fin (2 ^ (k + 1))) (h : i.val + 1 < 2 ^ (k + 1)),
      s(some ⟨k, i⟩, some ⟨k, ⟨i.val + 1, h⟩⟩) ∈ ω) ∧ ∀ e ∈ ω, q e ≠ 0 := by
  refine Filter.Eventually.and ?_ ?_
  · refine ae_all_iff.2 fun k => ae_all_iff.2 fun i => ?_
    by_cases h : i.val + 1 < 2 ^ (k + 1)
    · have hq := hpath k i ⟨i.val + 1, h⟩ rfl
      have h1 : law q {ω | s(some ⟨k, i⟩, some ⟨k, ⟨i.val + 1, h⟩⟩) ∈ ω} = 1 := by
        rw [law, prodBernoulli_setOf_mem, hq]; simp
      have h0 := (prob_compl_eq_zero_iff (measurableSet_mem _)).2 h1
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      simp only [Set.mem_ofPred_eq, not_forall] at hω
      obtain ⟨h', hω⟩ := hω
      exact hω
    · exact Filter.Eventually.of_forall fun ω h' => absurd h' h
  · refine ae_all_iff.2 fun e => ?_
    by_cases he : q e = 0
    · have h0 : law q {ω | e ∈ ω} = 0 := by
        rw [law, prodBernoulli_setOf_mem, he]; simp
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      simp only [Set.mem_ofPred_eq, not_forall, not_not] at hω
      obtain ⟨h1, -⟩ := hω
      exact h1
    · exact Filter.Eventually.of_forall fun ω _ => he

include hsupp in
/-- If every open pair has positive probability, an open path from outside `C_k` into `C_k`
uses the pair joining the root to `C_k`. -/
theorem root_mem_of_walk {ω : Config (Option (Σ k : ℕ, Fin (2 ^ (k + 1))))}
    (hω : ∀ e ∈ ω, q e ≠ 0) (k : ℕ) {a b : Option (Σ k : ℕ, Fin (2 ^ (k + 1)))}
    (p : (openGraph ω).Walk a b) (ha : ∀ i, a ≠ some ⟨k, i⟩) (hb : ∃ i, b = some ⟨k, i⟩) :
    s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) ∈ ω := by
  induction p with
  | nil =>
    obtain ⟨i, hi⟩ := hb
    exact absurd hi (ha i)
  | @cons a c b hadj p ih =>
    by_cases hc : ∃ i, c = some ⟨k, i⟩
    · rw [openGraph_adj_iff] at hadj
      rcases hsupp a c (hω _ hadj.1) with ⟨k', i', j', rfl, rfl, -⟩ | ⟨k', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · obtain ⟨i, hi⟩ := hc
        obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 (Option.some.inj hi)
        exact absurd rfl (ha i')
      · obtain ⟨i, hi⟩ := hc
        obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 (Option.some.inj hi)
        exact hadj.1
      · obtain ⟨i, hi⟩ := hc
        exact absurd hi (by simp)
    · exact ih (fun i h => hc ⟨i, h⟩) hb

/-- Along open path edges, the endpoint `0` of `C_k` is joined to every vertex of `C_k`. -/
theorem reachable_along_path {ω : Config (Option (Σ k : ℕ, Fin (2 ^ (k + 1))))}
    (hω : ∀ (k : ℕ) (i : Fin (2 ^ (k + 1))) (h : i.val + 1 < 2 ^ (k + 1)),
      s(some ⟨k, i⟩, some ⟨k, ⟨i.val + 1, h⟩⟩) ∈ ω)
    (k n : ℕ) (h : n < 2 ^ (k + 1)) :
    (openGraph ω).Reachable (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) (some ⟨k, ⟨n, h⟩⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
    rw [openGraph_adj_iff]
    refine ⟨hω k ⟨n, by omega⟩ h, ?_⟩
    intro heq
    have := congrArg (fun v => Option.elim v 0 fun s => (s.2 : ℕ)) heq
    simp at this

include hpath hsupp in
/-- Almost surely the root is joined to a vertex of `C_k` exactly when the pair joining the
root to `C_k` is open. -/
theorem ae_conn_root_iff (k : ℕ) (i : Fin (2 ^ (k + 1))) :
    ∀ᵐ ω ∂law q, (ω ∈ conn none (some ⟨k, i⟩) ↔
      s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) ∈ ω) := by
  filter_upwards [ae_good hpath] with ω hω
  constructor
  · intro h
    obtain ⟨p⟩ := h
    exact root_mem_of_walk hsupp hω.2 k p (fun i h => by simp at h) ⟨i, rfl⟩
  · intro h
    have hadj : (openGraph ω).Adj none (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) := by
      rw [openGraph_adj_iff]; exact ⟨h, by simp⟩
    exact hadj.reachable.trans (reachable_along_path hω.1 k i.val i.2)

include hpath in
/-- Almost surely the endpoint `0` of `C_k` is joined to every vertex of `C_k`. -/
theorem ae_conn_path (k : ℕ) (i : Fin (2 ^ (k + 1))) :
    ∀ᵐ ω ∂law q, ω ∈ conn (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) (some ⟨k, i⟩) := by
  filter_upwards [ae_good hpath] with ω hω
  exact reachable_along_path hω.1 k i.val i.2

include hroot in
/-- The pair joining the root to `C_k` is open with probability `4^(-(k+1))`. -/
theorem law_root_edge (k : ℕ) :
    law q {ω | s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) ∈ ω} = (4⁻¹ : ℝ≥0∞) ^ (k + 1) := by
  rw [law, prodBernoulli_setOf_mem]
  have h : (unitInterval.toNNReal (q s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩)) : ℝ≥0∞) =
      ENNReal.ofReal (q s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) : ℝ) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (q _).2.1]; rfl
  rw [h, hroot, ENNReal.ofReal_pow (by norm_num), one_div,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

include hpath hroot hsupp in
/-- `τ(root, v) = 4^(-(k+1))` for every vertex `v` of `C_k`. -/
theorem tau_root (k : ℕ) (i : Fin (2 ^ (k + 1))) :
    tau q none (some ⟨k, i⟩) = (4⁻¹ : ℝ≥0∞) ^ (k + 1) := by
  rw [tau, ← law_root_edge hroot k]
  exact measure_congr (Filter.eventuallyEqSet_iff.2 (ae_conn_root_iff hpath hsupp k i))

/-- `∑_k 2^(k+1) 4^(-(k+1)) = 1`. -/
theorem tsum_two_pow_mul_four_inv_pow :
    ∑' k : ℕ, (2 ^ (k + 1) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ (k + 1) = 1 := by
  have h : ∀ k : ℕ, (2 ^ (k + 1) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ (k + 1) = 2⁻¹ * (2⁻¹) ^ k := by
    intro k
    rw [← mul_pow, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul, pow_succ']
  simp_rw [h]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

include hpath hroot hsupp in
/-- **Item 1.** `χ(root) = 2`. -/
theorem chi_root_eq_two : chi q none = 2 := by
  rw [chi_eq_tsum_tau, tsum_option_ennreal, tau_self, ENNReal.tsum_sigma']
  simp_rw [tau_root hpath hroot hsupp, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [tsum_two_pow_mul_four_inv_pow, one_add_one_eq_two]

include hpath hroot hsupp in
/-- **Item 2.** The cluster of the root is finite almost surely. -/
theorem ae_cluster_root_finite : ∀ᵐ ω ∂law q, (cluster ω none).Finite := by
  have h := law_cluster_infinite_eq_zero_of_chi_ne_top q none
    (by rw [chi_root_eq_two hpath hroot hsupp]; exact ENNReal.ofNat_ne_top)
  rw [ae_iff]
  simpa using h

include hpath hroot hsupp in
/-- **Item 3.** `E|K_root|² = ⊤`. -/
theorem lintegral_encard_sq_eq_top :
    ∫⁻ ω, ((cluster ω none).encard : ℝ≥0∞) ^ 2 ∂law q = ⊤ := by
  rw [lintegral_cluster_sq, ← ENNReal.tsum_prod]
  refine top_le_iff.1 ?_
  set g : (Σ k : ℕ, Fin (2 ^ (k + 1)) × Fin (2 ^ (k + 1))) →
      Option (Σ k : ℕ, Fin (2 ^ (k + 1))) × Option (Σ k : ℕ, Fin (2 ^ (k + 1))) :=
    fun p => (some ⟨p.1, p.2.1⟩, some ⟨p.1, p.2.2⟩) with hg
  have hginj : Function.Injective g := by
    rintro ⟨k, i, j⟩ ⟨k', i', j'⟩ h
    simp only [hg, Prod.mk.injEq, Option.some.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨⟨rfl, h1⟩, -, h2⟩ := h
    rw [heq_iff_eq] at h1 h2
    subst h1 h2
    rfl
  refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hginj
    fun x => law q (conn none x.1 ∩ conn none x.2))
  have hterm : ∀ p : Σ k : ℕ, Fin (2 ^ (k + 1)) × Fin (2 ^ (k + 1)),
      law q (conn none (g p).1 ∩ conn none (g p).2) = (4⁻¹ : ℝ≥0∞) ^ (p.1 + 1) := by
    rintro ⟨k, i, j⟩
    rw [← law_root_edge hroot k]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [ae_conn_root_iff hpath hsupp k i, ae_conn_root_iff hpath hsupp k j]
      with ω hi hj
    exact ⟨fun h => hi.1 h.1, fun h => ⟨hi.2 h, hj.2 h⟩⟩
  simp_rw [hterm]
  rw [ENNReal.tsum_sigma']
  simp_rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∀ k : ℕ, ((2 ^ (k + 1) * 2 ^ (k + 1) : ℕ) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ (k + 1) = 1 := by
    intro k
    push_cast
    rw [← mul_pow, ← mul_pow, show (2 : ℝ≥0∞) * 2 = 4 by norm_num,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  simp_rw [h1]
  rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

include hpath hroot hsupp in
/-- **Item 4.** `E exp(t |K_root|) = ⊤` for every `t > 0`. -/
theorem lintegral_exp_eq_top {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (cluster ω none).ncard)) ∂law q = ⊤ := by
  have hle : ∀ ω : Config (Option (Σ k : ℕ, Fin (2 ^ (k + 1)))),
      ENNReal.ofReal (t ^ 2 / 2) * ((cluster ω none).ncard : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (Real.exp (t * (cluster ω none).ncard)) := by
    intro ω
    set n : ℝ := ((cluster ω none).ncard : ℝ) with hn
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg ht.le hn0)
    rw [show ((cluster ω none).ncard : ℝ≥0∞) = ENNReal.ofReal n by
      rw [hn, ENNReal.ofReal_natCast], ← ENNReal.ofReal_pow hn0,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ t * n := mul_nonneg ht.le hn0
    nlinarith [sq_nonneg (t * n)]
  have hae : (fun ω : Config (Option (Σ k : ℕ, Fin (2 ^ (k + 1)))) =>
      ((cluster ω none).ncard : ℝ≥0∞) ^ 2) =ᵐ[law q]
      fun ω => ((cluster ω none).encard : ℝ≥0∞) ^ 2 := by
    filter_upwards [ae_cluster_root_finite hpath hroot hsupp] with ω hω
    rw [← hω.cast_ncard_eq, ENat.toENNReal_coe]
  refine top_le_iff.1 (le_trans ?_ (lintegral_mono hle))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_congr_ae hae,
    lintegral_encard_sq_eq_top hpath hroot hsupp, ENNReal.mul_top]
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

include hpath in
/-- **Item 5.** `sup_v χ(v) = ⊤`. -/
theorem iSup_chi_eq_top : ⨆ v, chi q v = ⊤ := by
  have hk : ∀ k : ℕ, (2 ^ (k + 1) : ℝ≥0∞) ≤ chi q (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) := by
    intro k
    rw [chi_eq_tsum_tau]
    have hinj : Function.Injective fun i : Fin (2 ^ (k + 1)) =>
        (some ⟨k, i⟩ : Option (Σ k : ℕ, Fin (2 ^ (k + 1)))) := by
      intro i j h
      simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact h
    refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
    have h1 : ∀ i : Fin (2 ^ (k + 1)), tau q (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩)
        (some ⟨k, i⟩) = 1 := by
      intro i
      have h := (ae_iff_measure_eq (μ := law q) (measurableSet_conn _ _).nullMeasurableSet).1
        (ae_conn_path hpath k i)
      rw [tau]
      exact h.trans measure_univ
    simp_rw [h1, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast
    rfl
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (r : ℝ)
  have hr : (r : ℝ≥0∞) ≤ 2 ^ (n + 1) := by
    have h1 : (r : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hn.le
    have h2 : (n : ℝ≥0∞) ≤ 2 ^ (n + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right one_lt_two n.lt_succ_self)).le
    exact h1.trans h2
  exact hr.trans ((hk n).trans (le_iSup (fun v => chi q v) _))

end Model

/-! ### Connected host

The support graph `{e | 0 < q e}` is connected: each path `C_k` is joined internally by edges
of probability one and to the root by an edge of probability `4^(-(k+1))`. -/

/-- **The support graph of the heavy-second-moment model is connected.** If `q` is one on
consecutive vertices of each path `C_k` and positive on the pair joining the root to the
endpoint `0` of `C_k`, then `fromEdgeSet {e | 0 < q e}` is connected. -/
theorem connected_fromEdgeSet_pos {q : Sym2 (Option (Σ k : ℕ, Fin (2 ^ (k + 1)))) → unitInterval}
    (hpath : ∀ (k : ℕ) (i j : Fin (2 ^ (k + 1))), i.val + 1 = j.val →
      q s(some ⟨k, i⟩, some ⟨k, j⟩) = 1)
    (hroot : ∀ k : ℕ, (q s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) : ℝ) = (1 / 4) ^ (k + 1)) :
    (SimpleGraph.fromEdgeSet {e | 0 < q e}).Connected := by
  set G := SimpleGraph.fromEdgeSet {e | 0 < q e}
  have hroot' : ∀ k : ℕ, G.Reachable none (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) := by
    intro k
    refine SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).2 ⟨?_, by simp⟩)
    change (0 : ℝ) < (q s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) : ℝ)
    rw [hroot k]
    positivity
  have hstep : ∀ (k n : ℕ) (h : n < 2 ^ (k + 1)),
      G.Reachable (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) (some ⟨k, ⟨n, h⟩⟩) := by
    intro k n
    induction n with
    | zero => intro h; exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      intro h
      refine (ih (Nat.lt_of_succ_lt h)).trans (SimpleGraph.Adj.reachable
        ((SimpleGraph.fromEdgeSet_adj _).2 ⟨?_, ?_⟩))
      · change 0 < q s(some ⟨k, ⟨n, Nat.lt_of_succ_lt h⟩⟩, some ⟨k, ⟨n + 1, h⟩⟩)
        rw [hpath k _ _ rfl]
        exact zero_lt_one
      · simp
  refine (SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨none, fun w => ?_⟩
  rcases w with _ | ⟨k, ⟨n, h⟩⟩
  · exact SimpleGraph.Reachable.refl _
  · exact (hroot' k).trans (hstep k n h)

/-! ### The profile exists -/

/-- A profile with the required values exists. -/
theorem exists_profile : ∃ q : Sym2 (Option (Σ k : ℕ, Fin (2 ^ (k + 1)))) → unitInterval,
    (∀ (k : ℕ) (i j : Fin (2 ^ (k + 1))), i.val + 1 = j.val →
      q s(some ⟨k, i⟩, some ⟨k, j⟩) = 1) ∧
    (∀ k : ℕ, (q s(none, some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) : ℝ) = (1 / 4) ^ (k + 1)) ∧
    (∀ a b, q s(a, b) ≠ 0 →
      (∃ (k : ℕ) (i j : Fin (2 ^ (k + 1))), a = some ⟨k, i⟩ ∧ b = some ⟨k, j⟩ ∧
        (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∨
      ∃ k : ℕ, (a = none ∧ b = some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) ∨
        (b = none ∧ a = some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩)) := by
  classical
  let P : Option (Σ k : ℕ, Fin (2 ^ (k + 1))) → Option (Σ k : ℕ, Fin (2 ^ (k + 1))) → Prop :=
    fun a b => ∃ (k : ℕ) (i j : Fin (2 ^ (k + 1))), a = some ⟨k, i⟩ ∧ b = some ⟨k, j⟩ ∧
      (i.val + 1 = j.val ∨ j.val + 1 = i.val)
  let R : Option (Σ k : ℕ, Fin (2 ^ (k + 1))) → Option (Σ k : ℕ, Fin (2 ^ (k + 1))) → Prop :=
    fun a b => ∃ k : ℕ, (a = none ∧ b = some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) ∨
      (b = none ∧ a = some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩)
  have hP : ∀ a b, P a b ↔ P b a := by
    intro a b
    constructor <;> rintro ⟨k, i, j, h1, h2, h3⟩ <;> exact ⟨k, j, i, h2, h1, h3.symm⟩
  have hR : ∀ a b, R a b ↔ R b a := by
    intro a b
    constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, h.symm⟩
  let L : Option (Σ k : ℕ, Fin (2 ^ (k + 1))) → ℕ := fun a => a.elim 0 Sigma.fst
  let g : Option (Σ k : ℕ, Fin (2 ^ (k + 1))) → Option (Σ k : ℕ, Fin (2 ^ (k + 1))) →
      unitInterval := fun a b =>
    if P a b then 1 else if R a b then
      ⟨(1 / 4) ^ (L a + L b + 1), by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
    else 0
  have hg : ∀ a b, g a b = g b a := by
    intro a b
    simp only [g, hP a b, hR a b, add_comm (L a)]
  refine ⟨fun e => Sym2.lift ⟨g, hg⟩ e, ?_, ?_, ?_⟩
  · intro k i j h
    have hp : P (some ⟨k, i⟩) (some ⟨k, j⟩) := ⟨k, i, j, rfl, rfl, Or.inl h⟩
    change g _ _ = 1
    simp only [g, hp, ↓reduceIte]
  · intro k
    have hnP : ¬ P none (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) := by
      rintro ⟨k', i, j, h1, -⟩
      exact absurd h1 (by simp)
    have hr : R none (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) := ⟨k, Or.inl ⟨rfl, rfl⟩⟩
    change ((g none (some ⟨k, ⟨0, Nat.two_pow_pos _⟩⟩) : unitInterval) : ℝ) = _
    simp only [g, hnP, hr, ↓reduceIte, L, Option.elim_none, Option.elim_some, zero_add]
  · intro a b h
    by_contra hc
    rw [not_or] at hc
    apply h
    change g a b = 0
    have h1 : ¬ P a b := hc.1
    have h2 : ¬ R a b := hc.2
    simp only [g, h1, h2, ↓reduceIte]

/-- The model: `χ(root) = 2` while `E|K_root|² = ⊤` and `sup_v χ(v) = ⊤`. -/
example : ∃ q : Sym2 (Option (Σ k : ℕ, Fin (2 ^ (k + 1)))) → unitInterval,
    chi q none = 2 ∧ ∫⁻ ω, ((cluster ω none).encard : ℝ≥0∞) ^ 2 ∂law q = ⊤ ∧
      ⨆ v, chi q v = ⊤ := by
  obtain ⟨q, hpath, hroot, hsupp⟩ := exists_profile
  exact ⟨q, chi_root_eq_two hpath hroot hsupp, lintegral_encard_sq_eq_top hpath hroot hsupp,
    iSup_chi_eq_top hpath⟩

end PercLib.Models
