/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
Mathematical reference: the path-counting bound `p_c(ℤ^d) ≥ 1/μ_d`
(Grimmett, *Percolation*, 2nd ed., Theorem 1.33; Hammersley 1957).
-/
module

public import PercLib.Models.PathCount
public import PercLib.Models.Tree
public import PercLib.Percolation.Bond.SelfAvoidingChi
public import PercLib.Percolation.Bond.IndependentLayer
public import PercLib.Percolation.Bond.VolumeTails

/-!
# Susceptibility below the inverse connective constant

On any countable graph `G`, for a profile vanishing off `G` (away from the diagonal) and at
most `p` on the edges of `G`, the susceptibility at `x` is bounded by the path series
`∑_n c_n(x) p^n`, where `c_n(x)` counts the `G`-paths of length `n` from `x`
(`chi_le_tsum_card_paths_mul_pow`). On `ℤ^d` the series is `∑_n c_n p^n` with the rooted
self-avoiding path counts `pathCount d 0 n`, and it converges when `p μ_d < 1`, `μ_d` being
the connective constant (`tsum_pathCount_mul_pow_lt_top`, a root test). Hence every cluster
is almost surely finite, and the critical parameter of homogeneous nearest-neighbour bond
percolation on `ℤ^d` is at least `μ_d⁻¹` (`inv_le_sInf_of_tendsto_pathCount`).

## Main results

* `chi_le_tsum_card_paths_mul_pow`
* `ENNReal.tsum_coe_mul_pow_lt_top_of_tendsto_rpow_inv`
* `chi_le_tsum_pathCount_mul_pow`, `tsum_pathCount_mul_pow_lt_top`
* `ae_cluster_finite_of_mul_lt_one`
* `inv_le_sInf_of_tendsto_pathCount`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Probability
open scoped ENNReal NNReal

/-- **Root test in `ℝ≥0∞`.** If `u_n^{1/n} → μ` and `p μ < 1`, then `∑_n u_n p^n < ∞`. -/
theorem ENNReal.tsum_coe_mul_pow_lt_top_of_tendsto_rpow_inv {u : ℕ → ℝ≥0} {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (u n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) {p : ℝ≥0}
    (hp : (p : ℝ) * μ < 1) :
    ∑' n, (u n : ℝ≥0∞) * (p : ℝ≥0∞) ^ n < ∞ := by
  have hμ0 : 0 ≤ μ := ge_of_tendsto' hμ fun n => Real.rpow_nonneg (NNReal.coe_nonneg _) _
  obtain ⟨lam, hlam, hplam⟩ : ∃ lam : ℝ, μ < lam ∧ (p : ℝ) * lam < 1 := by
    rcases eq_or_lt_of_le p.coe_nonneg with h | h
    · exact ⟨μ + 1, by linarith, by rw [← h]; simp⟩
    · obtain ⟨lam, h1, h2⟩ := exists_between ((lt_div_iff₀' h).2 hp)
      exact ⟨lam, h1, (lt_div_iff₀' h).1 h2⟩
  have hlam0 : 0 < lam := hμ0.trans_lt hlam
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hμ.eventually (gt_mem_nhds hlam))
  have hu : ∀ n, N + 1 ≤ n → (u n : ℝ) ≤ lam ^ n := by
    intro n hn
    have h1 := hN n (by omega)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have := pow_le_pow_left₀ (Real.rpow_nonneg (NNReal.coe_nonneg _) _) h1.le n
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), inv_mul_cancel₀ hn0,
      Real.rpow_one] at this
  set r : ℝ≥0∞ := ENNReal.ofReal ((p : ℝ) * lam) with hr
  have hr1 : r < 1 := ENNReal.ofReal_lt_one.2 hplam
  have hle : ∀ n, (u n : ℝ≥0∞) * (p : ℝ≥0∞) ^ n ≤
      (if n < N + 1 then (u n : ℝ≥0∞) * (p : ℝ≥0∞) ^ n else 0) + r ^ n := by
    intro n
    split_ifs with h
    · exact le_self_add
    · rw [zero_add, hr, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow p.coe_nonneg,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (u n : ℝ) * (p : ℝ) ^ n ≤ lam ^ n * (p : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (hu n (by omega)) (by positivity)
        _ = ((p : ℝ) * lam) ^ n := by ring
  calc ∑' n, (u n : ℝ≥0∞) * (p : ℝ≥0∞) ^ n
      ≤ ∑' n, ((if n < N + 1 then (u n : ℝ≥0∞) * (p : ℝ≥0∞) ^ n else 0) + r ^ n) :=
        ENNReal.tsum_le_tsum hle
    _ = ∑' n, (if n < N + 1 then (u n : ℝ≥0∞) * (p : ℝ≥0∞) ^ n else 0) + ∑' n, r ^ n :=
        ENNReal.tsum_add
    _ < ∞ := by
        rw [tsum_eq_sum (s := Finset.range (N + 1)) fun n hn => by
          rw [Finset.mem_range] at hn
          simp [hn]]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 fun n _ => ?_,
          tsum_geometric_lt_top.2 hr1⟩
        split_ifs
        · exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
        · exact ENNReal.zero_lt_top

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- The probability that a `G`-path of length `n` is open is at most `p^n`. -/
theorem law_edges_subset_le_pow (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (p : unitInterval) (hle : ∀ e ∈ G.edgeSet, q e ≤ p) {x y : V} (r : G.Path x y) {n : ℕ}
    (hr : r.1.length = n) :
    law q {ω : Config V | (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} ≤
      (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
  cases n with
  | zero => simpa using prob_le_one
  | succ n => exact law_path_open_le G q p hle r hr

/-- **The path series bounds the susceptibility.** On a countable graph `G` with finitely many
paths of each length from `x`, for a profile vanishing off `G` away from the diagonal and at
most `p` on `G`, `χ(x) ≤ ∑_n c_n(x) p^n`, where `c_n(x)` counts the `G`-paths of length `n`
from `x` (the length-zero path accounts for `x` itself). -/
theorem chi_le_tsum_card_paths_mul_pow [Countable V] (G : SimpleGraph V)
    (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (x : V) (hfin : ∀ n, Finite {r : Σ y, G.Path x y // r.2.1.length = n}) :
    chi q x ≤ ∑' n : ℕ, (Nat.card {r : Σ y, G.Path x y // r.2.1.length = n} : ℝ≥0∞) *
      (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
  classical
  set P : ℕ → Type _ := fun n => {r : Σ y, G.Path x y // r.2.1.length = n}
  set c : ℕ → ℝ≥0∞ := fun n => (unitInterval.toNNReal p : ℝ≥0∞) ^ n
  have hτ : ∀ y, tau q x y ≤ ∑' n, ∑' r : P n, if r.1.1 = y then c n else 0 := by
    intro y
    set A : (n : ℕ) → P n → Set (Config V) := fun n r =>
      if r.1.1 = y then {ω | (r.1.2.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} else ∅
    have hsub : ∀ᵐ ω ∂law q, ω ∈ conn x y → ω ∈ ⋃ n, ⋃ r : P n, A n r := by
      filter_upwards [ae_exists_path_of_mem_conn G q hoff x y] with ω hω hconn
      obtain ⟨r, hr⟩ := hω hconn
      refine mem_iUnion.2 ⟨r.1.length, mem_iUnion.2 ⟨⟨⟨y, r⟩, rfl⟩, ?_⟩⟩
      simp only [A, ite_true]
      exact hr
    have : ∀ n, Countable (P n) := fun n => (hfin n).to_countable
    calc tau q x y ≤ law q (⋃ n, ⋃ r : P n, A n r) := measure_mono_ae hsub
      _ ≤ ∑' n, law q (⋃ r : P n, A n r) := measure_iUnion_le _
      _ ≤ ∑' n, ∑' r : P n, law q (A n r) :=
          ENNReal.tsum_le_tsum fun n => measure_iUnion_le _
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun r => ?_
          simp only [A]
          split_ifs
          · exact law_edges_subset_le_pow G q p hle r.1.2 r.2
          · simp
  rw [chi_eq_tsum_tau]
  calc ∑' y, tau q x y
      ≤ ∑' y, ∑' n, ∑' r : P n, (if r.1.1 = y then c n else 0) := ENNReal.tsum_le_tsum hτ
    _ = ∑' n, ∑' r : P n, ∑' y, (if r.1.1 = y then c n else 0) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun n => ENNReal.tsum_comm
    _ = ∑' n, ∑' _r : P n, c n := by
        refine tsum_congr fun n => tsum_congr fun r => ?_
        simp
    _ = _ := by
        refine tsum_congr fun n => ?_
        have := hfin n
        rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe]

/-! ### Nearest-neighbour percolation on `ℤ^d` -/

section Lattice

open PercLib.Models.Site

variable {d : ℕ}

/-- **The lattice path series bounds the susceptibility.** For a profile on `ℤ^d` vanishing on
non-loop pairs that are not nearest-neighbour bonds and at most `p` on the bonds,
`χ(x) ≤ ∑_n c_n p^n`. -/
theorem chi_le_tsum_pathCount_mul_pow (q : Sym2 (Fin d → ℤ) → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ (zdGraph d).edgeSet → q e = 0)
    (hle : ∀ e ∈ (zdGraph d).edgeSet, q e ≤ p) (x : Fin d → ℤ) :
    chi q x ≤ ∑' n : ℕ, (pathCount d 0 n : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
  refine (chi_le_tsum_card_paths_mul_pow (zdGraph d) q p hoff hle x
    fun n => finite_paths_length d n x).trans_eq (tsum_congr fun n => ?_)
  rw [← pathCount_eq_pathCount_zero x n, pathCount_eq_natCard]

/-- **The lattice path series converges below the inverse connective constant.** If
`c_n^{1/n} → μ` and `p μ < 1`, then `∑_n c_n p^n < ∞`. -/
theorem tsum_pathCount_mul_pow_lt_top {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (pathCount d 0 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ))
    (p : unitInterval) (hpμ : (p : ℝ) * μ < 1) :
    ∑' n : ℕ, (pathCount d 0 n : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) ^ n < ∞ := by
  have := ENNReal.tsum_coe_mul_pow_lt_top_of_tendsto_rpow_inv
    (u := fun n => (pathCount d 0 n : ℝ≥0)) (by simpa using hμ) (p := unitInterval.toNNReal p) hpμ
  simpa using this

/-- Below the inverse connective constant the susceptibility is finite at every root. -/
theorem chi_lt_top_of_mul_lt_one {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (pathCount d 0 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ))
    (q : Sym2 (Fin d → ℤ) → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ (zdGraph d).edgeSet → q e = 0)
    (hle : ∀ e ∈ (zdGraph d).edgeSet, q e ≤ p) (hpμ : (p : ℝ) * μ < 1) (x : Fin d → ℤ) :
    chi q x < ∞ :=
  (chi_le_tsum_pathCount_mul_pow q p hoff hle x).trans_lt (tsum_pathCount_mul_pow_lt_top hμ p hpμ)

/-- Below the inverse connective constant every open cluster is almost surely finite. -/
theorem ae_cluster_finite_of_mul_lt_one {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (pathCount d 0 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ))
    (q : Sym2 (Fin d → ℤ) → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ (zdGraph d).edgeSet → q e = 0)
    (hle : ∀ e ∈ (zdGraph d).edgeSet, q e ≤ p) (hpμ : (p : ℝ) * μ < 1) :
    ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite :=
  ae_all_iff.2 fun x =>
    ae_cluster_finite_of_chi_lt_top (chi_lt_top_of_mul_lt_one hμ q p hoff hle hpμ x)

open Classical in
/-- With every nearest-neighbour bond open with probability one, the cluster of the origin is
almost surely infinite (`d ≥ 1`). -/
theorem ae_cluster_zero_infinite_of_eq_one (hd : 1 ≤ d) :
    ∀ᵐ ω ∂law (fun e => if e ∈ (zdGraph d).edgeSet then (1 : unitInterval) else 0),
      (cluster ω (0 : Fin d → ℤ)).Infinite := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  filter_upwards [PercLib.Models.ae_edgeSet_subset_of_forall_eq_one (zdGraph d) _
    fun e he => ite_eq_left he] with ω hω
  have hle : zdGraph d ≤ openGraph ω := fun x y hxy =>
    (openGraph_adj_iff ω x y).2 ⟨hω hxy, hxy.ne⟩
  have huniv : cluster ω 0 = univ :=
    eq_univ_of_forall fun y => ((zdGraph_connected d).preconnected 0 y).mono hle
  rw [huniv]
  exact infinite_univ

open Classical in
/-- **The critical parameter of nearest-neighbour bond percolation is at least `μ_d⁻¹`.** With
`p_c = inf {p ∈ [0,1] : P_p(|K(0)| = ∞) > 0}` for the homogeneous profile on the bonds of
`ℤ^d` (`d ≥ 1`), `μ_d⁻¹ ≤ p_c`. -/
theorem inv_le_sInf_of_tendsto_pathCount (hd : 1 ≤ d) {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (pathCount d 0 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
    μ⁻¹ ≤ sInf {p : ℝ | ∃ h : p ∈ unitInterval,
      0 < law (fun e => if e ∈ (zdGraph d).edgeSet then (⟨p, h⟩ : unitInterval) else 0)
        {ω | (cluster ω (0 : Fin d → ℤ)).Infinite}} := by
  obtain ⟨μ', hμ', -, hμ'1, -⟩ := exists_tendsto_card_paths_rpow hd
  have hμ1 : 1 ≤ μ := by rw [tendsto_nhds_unique hμ hμ']; exact hμ'1
  have hμpos : 0 < μ := by linarith
  refine le_csInf ⟨1, unitInterval.one_mem, ?_⟩ ?_
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [measure_eq_zero_iff_ae_notMem] at h0
    obtain ⟨ω, h1, h2⟩ := ((ae_cluster_zero_infinite_of_eq_one (d := d) hd).and h0).exists
    exact h2 h1
  · rintro p ⟨hp, hpos⟩
    by_contra hlt
    push Not at hlt
    have hpμ : p * μ < 1 := by
      have := mul_lt_mul_of_pos_right hlt hμpos
      rwa [inv_mul_cancel₀ hμpos.ne'] at this
    have hfin := ae_cluster_finite_of_mul_lt_one hμ
      (fun e => if e ∈ (zdGraph d).edgeSet then (⟨p, hp⟩ : unitInterval) else 0) ⟨p, hp⟩
      (fun e _ he => ite_eq_right he) (fun e he => le_of_eq (ite_eq_left he)) hpμ
    have h0 : law (fun e => if e ∈ (zdGraph d).edgeSet then (⟨p, hp⟩ : unitInterval) else 0)
        {ω | (cluster ω (0 : Fin d → ℤ)).Infinite} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hfin] with ω hω
      exact fun h => h (hω 0)
    exact hpos.ne' h0

end Lattice

end PercLib.Percolation.Bond
