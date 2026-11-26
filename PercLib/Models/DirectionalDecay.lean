/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, no upstream code. Mathematical reference: the directional rate
`m(v) = lim -(1/n) log τ(0, n v)` of a translation-invariant bond percolation (Fekete's lemma);
lattice path counting with the connective constant as in N. Madras and G. Slade, *The
Self-Avoiding Walk* (1993), §1.2; the long-range power-law intensities as in
L. S. Schulman, *J. Phys. A* 16 (1983) and C. M. Newman and L. S. Schulman,
*Comm. Math. Phys.* 104 (1986) (locators to be checked).
-/
module

public import PercLib.Models.ConnectiveConstant
public import PercLib.Percolation.Bond.CorrelationLength
public import PercLib.Percolation.Bond.PathLowerBounds
public import PercLib.Percolation.Bond.SelfAvoiding
public import PercLib.Models.LongRange.PowerLaw
public import PercLib.Models.LongRange.Defs
public import PercLib.Models.TranslationInvariant
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.Cylinder
public import PercLib.Probability.BernoulliDivergence
public import PercLib.Probability.Transport.Reindexing

/-!
# Directional decay rates on `ℤ^d`

Write `‖v‖₁ = ∑ᵢ |vᵢ|` and `m_q(v) = lim_n -(1/n) log τ_q(0, n v)` (the limit of
`tendsto_neg_log_tau_div`).

For homogeneous nearest-neighbour percolation on `ℤ^d` (profile `p` on the edges of
`zdGraph d`, `0` off them) with `0 < p` and `p μ_d < 1`, where `μ_d` is the connective
constant, the rate exists and `‖v‖₁ log(1/(p μ_d)) ≤ m_p(v) ≤ ‖v‖₁ log(1/p)`; in particular
`m_p(v) > 0` for `v ≠ 0`. The lower bound on `τ` is a geodesic of `n ‖v‖₁` edges; the upper
bound is the union bound over `ℤ^d`-paths from `0` to `n v`, all of length at least `n ‖v‖₁`,
with `c_ℓ ≤ λ^ℓ` for large `ℓ` and every `λ > μ_d`.

For the power-law intensities `q_β(x, y) = 1 - exp(-β ‖y - x‖^{-d-α})` (sup norm), the rate is
`0` in every direction, while `χ ≤ (1 - βM)⁻¹` when `βM < 1`, `M = ∑_{z ≠ 0} ‖z‖^{-d-α}`.

## Main results

* `PercLib.Percolation.Bond.tau_le_tsum_host_paths`: union bound over the paths of a host graph.
* `PercLib.Percolation.Bond.pow_length_le_tau`: a single host walk bounds `τ` from below.
* `PercLib.Percolation.Bond.tau_map_iso_hostProfile`: the host profile is invariant under
  graph automorphisms.
* `PercLib.Models.Site.exists_tendsto_neg_log_tau_div_nearestNeighbour`: the two-sided bound
  on the nearest-neighbour rate.
* `PercLib.Models.Site.tendsto_neg_log_tau_div_powerLaw_zero`: the power-law rate vanishes.
* `PercLib.Models.Site.chi_intensity_powerLaw_le`: the power-law susceptibility bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The union bound over the paths of a host graph -/

/-- **Union bound over host paths.** If `q` vanishes off the edges of `G` and is at most `p`
on them, then `τ(x, y) ≤ ∑_{G-paths r : x → y} p^{|r|}`. -/
theorem tau_le_tsum_host_paths [Countable V] (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (p : unitInterval) (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p) (x y : V) :
    tau q x y ≤ ∑' r : G.Path x y, (unitInterval.toNNReal p : ℝ≥0∞) ^ r.1.length := by
  classical
  have : Countable (G.Walk x y) := Function.Injective.countable SimpleGraph.Walk.support_injective
  have hsub : conn x y ≤ᵐ[law q] ⋃ r : G.Path x y,
      {ω : Config V | (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
    filter_upwards [ae_openGraph_le_of_zero_off_diagonal G q hoff] with ω hω hconn
    obtain ⟨r, hr⟩ := (hconn : (openGraph ω).Reachable x y).exists_isPath
    refine Set.mem_iUnion.2 ⟨⟨r.mapLe hω, hr.mapLe hω⟩, fun e he => ?_⟩
    simp only [Finset.mem_coe, List.mem_toFinset, SimpleGraph.Walk.edges_mapLe_eq_edges] at he
    have := r.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  calc tau q x y ≤ law q (⋃ r : G.Path x y,
        {ω : Config V | (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω}) := measure_mono_ae hsub
    _ ≤ ∑' r : G.Path x y, law q {ω : Config V | (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} :=
        measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum fun r => by
        rw [law, PercLib.Probability.prodBernoulli_subset]
        have hcard : r.1.edges.toFinset.card = r.1.length := by
          rw [List.toFinset_card_of_nodup r.2.isTrail.edges_nodup, SimpleGraph.Walk.length_edges]
        rw [← hcard, ← Finset.prod_const]
        refine Finset.prod_le_prod fun e he => ?_
        exact ENNReal.coe_le_coe.2 (hle e (r.1.edges_subset_edgeSet (List.mem_toFinset.1 he)))

/-- **A single host walk.** If `q = p` on the edges of `G`, every `G`-walk `w : x → y` gives
`p^{|w|} ≤ τ(x, y)`. -/
theorem pow_length_le_tau [DecidableEq V] (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (p : unitInterval) (hq : ∀ e ∈ G.edgeSet, q e = p) {x y : V} (w : G.Walk x y) :
    (unitInterval.toNNReal p : ℝ≥0∞) ^ w.length ≤ tau q x y := by
  have hw := prod_le_tau_of_walk q (w.mapLe le_top)
  refine le_trans ?_ hw
  simp only [SimpleGraph.Walk.edges_mapLe_eq_edges]
  have hp1 : (unitInterval.toNNReal p : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (show unitInterval.toNNReal p ≤ 1 from p.2.2)
  rw [Finset.prod_congr rfl fun e he => by
    rw [hq e (w.edges_subset_edgeSet (List.mem_toFinset.1 he))], Finset.prod_const]
  refine pow_le_pow_of_le_one bot_le hp1 ?_
  calc w.edges.toFinset.card ≤ w.edges.length := List.toFinset_card_le _
    _ = w.length := SimpleGraph.Walk.length_edges w

open Classical in
/-- **Automorphism invariance of the host profile.** The two-point function of the profile
`p` on the edges of `G` and `0` off them is invariant under every automorphism of `G`. -/
theorem tau_map_iso_hostProfile (G : SimpleGraph V) (p : unitInterval) (φ : G ≃g G)
    (x y : V) :
    tau (fun e => if e ∈ G.edgeSet then p else 0) (φ x) (φ y) =
      tau (fun e => if e ∈ G.edgeSet then p else 0) x y := by
  have hinv : ∀ e, (fun e => if e ∈ G.edgeSet then p else 0) (Sym2.map φ.toEquiv e) =
      (fun e => if e ∈ G.edgeSet then p else 0) e := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      change (if G.Adj (φ a) (φ b) then p else 0) = _
      rw [φ.map_adj_iff]
  exact tau_apply_eq_of_map_law_eq φ.toEquiv
    (PercLib.Probability.prodBernoulli_map_image_sym2_invariant
      (fun e => if e ∈ G.edgeSet then p else 0) φ.toEquiv hinv) x y

end PercLib.Percolation.Bond

namespace PercLib.Models.Site

open PercLib.Percolation.Bond

variable {d : ℕ}

/-! ### Nearest-neighbour percolation -/

section NearestNeighbour

open Classical in
/-- The nearest-neighbour profile is invariant under translations. -/
theorem tau_zdGraph_add_add (p : unitInterval) (x y g : Fin d → ℤ) :
    tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) (x + g) (y + g) =
      tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) x y := by
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := d) g
  simpa [hφ] using tau_map_iso_hostProfile (zdGraph d) p φ x y

/-- `‖n v‖₁ = n ‖v‖₁`, in the spelling of `exists_walk_length_eq_l1`. -/
theorem sum_natAbs_nsmul (n : ℕ) (v : Fin d → ℤ) :
    ∑ i, ((n • v) i - (0 : Fin d → ℤ) i).natAbs = n * ∑ i, (v i).natAbs := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Int.natAbs_mul]

open Classical in
/-- **Geodesic lower bound.** `p^{n ‖v‖₁} ≤ τ(0, n v)`. -/
theorem pow_le_tau_zdGraph (p : unitInterval) (n : ℕ) (v : Fin d → ℤ) :
    (unitInterval.toNNReal p : ℝ≥0∞) ^ (n * ∑ i, (v i).natAbs) ≤
      tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) 0 (n • v) := by
  obtain ⟨w, hw⟩ := exists_walk_length_eq_l1 (d := d) 0 (n • v)
  rw [sum_natAbs_nsmul] at hw
  rw [← hw]
  exact pow_length_le_tau (zdGraph d) _ p (fun e he => ite_eq_left he) w

/-- The `ℤ^d`-paths of length `ℓ` from `0` to a fixed `y` are at most as many as all
`ℤ^d`-paths of length `ℓ` from `0`. -/
theorem enatCard_paths_le (y : Fin d → ℤ) (ℓ : ℕ) :
    ENat.card {r : (zdGraph d).Path 0 y // r.1.length = ℓ} ≤
      (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = ℓ} : ℕ∞) := by
  have := finite_paths_length d ℓ 0
  rw [← ENat.card_eq_coe_natCard]
  refine ENat.card_le_card_of_injective (f := fun r => ⟨⟨y, r.1⟩, r.2⟩) fun a b h => ?_
  have h' := (Sigma.mk.inj_iff.1 (Subtype.mk.inj h)).2
  exact Subtype.ext (eq_of_heq h')

open Classical in
/-- **Union bound for nearest-neighbour percolation.** If `c_ℓ ≤ λ^ℓ` for every `ℓ ≥ N`,
then `τ(0, y) ≤ (pλ)^{‖y‖₁}/(1 - pλ)` whenever `‖y‖₁ ≥ N`. -/
theorem tau_zdGraph_le {p : unitInterval} {lam : ℝ≥0∞} {N : ℕ}
    (hc : ∀ ℓ, N ≤ ℓ →
      (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = ℓ} : ℝ≥0∞) ≤ lam ^ ℓ)
    (y : Fin d → ℤ) (hy : N ≤ ∑ i, (y i - (0 : Fin d → ℤ) i).natAbs) :
    tau (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) 0 y ≤
      ((unitInterval.toNNReal p : ℝ≥0∞) * lam) ^ (∑ i, (y i - (0 : Fin d → ℤ) i).natAbs) *
        (1 - (unitInterval.toNNReal p : ℝ≥0∞) * lam)⁻¹ := by
  set L := ∑ i, (y i - (0 : Fin d → ℤ) i).natAbs
  set P := (unitInterval.toNNReal p : ℝ≥0∞)
  have h1 := tau_le_tsum_host_paths (zdGraph d) (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
    p (fun e _ he => ite_eq_right he) (fun e he => le_of_eq (ite_eq_left he)) 0 y
  refine h1.trans ?_
  -- Group the paths by length.
  rw [← (Equiv.sigmaFiberEquiv fun r : (zdGraph d).Path 0 y => r.1.length).tsum_eq,
    ENNReal.tsum_sigma']
  have hfib : ∀ ℓ, ∑' r : {r : (zdGraph d).Path 0 y // r.1.length = ℓ},
      P ^ (((Equiv.sigmaFiberEquiv fun r : (zdGraph d).Path 0 y => r.1.length) ⟨ℓ, r⟩).1.length) ≤
      (if L ≤ ℓ then (P * lam) ^ L * (P * lam) ^ (ℓ - L) else 0) := by
    intro ℓ
    simp only [Equiv.sigmaFiberEquiv_apply]
    rw [tsum_congr fun r : {r : (zdGraph d).Path 0 y // r.1.length = ℓ} => by rw [r.2],
      ENNReal.tsum_const]
    split_ifs with hL
    · have hcard := enatCard_paths_le y ℓ
      calc (ENat.card {r : (zdGraph d).Path 0 y // r.1.length = ℓ} : ℝ≥0∞) * P ^ ℓ
          ≤ (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = ℓ} : ℝ≥0∞) * P ^ ℓ := by
            gcongr
            exact_mod_cast hcard
        _ ≤ lam ^ ℓ * P ^ ℓ := mul_le_mul' (hc ℓ (hy.trans hL)) le_rfl
        _ = (P * lam) ^ L * (P * lam) ^ (ℓ - L) := by
            rw [← pow_add, Nat.add_sub_cancel' hL, mul_pow, mul_comm]
    · have hempty : IsEmpty {r : (zdGraph d).Path 0 y // r.1.length = ℓ} := ⟨fun r => hL (by
        rw [← r.2]; exact l1_le_length r.1.1)⟩
      rw [(ENat.card_eq_zero_iff_empty _).2 hempty]
      simp
  refine (ENNReal.tsum_le_tsum hfib).trans (le_of_eq ?_)
  -- The geometric tail.
  have hinj : Function.Injective fun k : ℕ => k + L := fun a b h => by simpa using h
  rw [← hinj.tsum_eq (f := fun ℓ => if L ≤ ℓ then (P * lam) ^ L * (P * lam) ^ (ℓ - L) else 0)
    (fun ℓ hℓ => by
      by_contra h
      apply hℓ
      have : ¬ L ≤ ℓ := fun hL => h ⟨ℓ - L, by simp only; omega⟩
      simp [this])]
  simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, Nat.add_sub_cancel]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

open Classical in
/-- **Directional rate of nearest-neighbour percolation.** For homogeneous nearest-neighbour
percolation on `ℤ^d` with `0 < p`, `p μ_d < 1` (`μ_d` the connective constant, the limit of
`c_n^{1/n}`), the directional rate `m_p(v) = lim -(1/n) log τ(0, n v)` exists and
`‖v‖₁ log(1/(p μ_d)) ≤ m_p(v) ≤ ‖v‖₁ log(1/p)`. -/
theorem exists_tendsto_neg_log_tau_div_nearestNeighbour (hd : 1 ≤ d) {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
      p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ))
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hpμ : (p : ℝ) * μ < 1) (v : Fin d → ℤ) :
    ∃ m : ℝ, Tendsto (fun n : ℕ => -Real.log (tau (fun e => if e ∈ (zdGraph d).edgeSet then p
        else 0) 0 (n • v)).toReal / n) atTop (𝓝 m) ∧
      (∑ i, (v i).natAbs : ℕ) * Real.log (1 / ((p : ℝ) * μ)) ≤ m ∧
      m ≤ (∑ i, (v i).natAbs : ℕ) * Real.log (1 / (p : ℝ)) := by
  set q : Sym2 (Fin d → ℤ) → unitInterval := fun e => if e ∈ (zdGraph d).edgeSet then p else 0
    with hq
  set K : ℕ := ∑ i, (v i).natAbs with hK
  set P : ℝ := (p : ℝ) with hP
  -- `μ ≥ 1`
  obtain ⟨μ', hμ', -, hμ'1, -⟩ := exists_tendsto_card_paths_rpow hd
  have hμμ' : μ = μ' := tendsto_nhds_unique hμ hμ'
  have hμpos : 0 < μ := by linarith
  -- `τ(0, n v) ≥ p^{nK} > 0`
  have hP' : (unitInterval.toNNReal p : ℝ≥0∞) = ENNReal.ofReal P := by
    rw [hP, ← ENNReal.ofReal_coe_nnreal]; rfl
  have hlow : ∀ n : ℕ, P ^ (n * K) ≤ (tau q 0 (n • v)).toReal := by
    intro n
    have h := pow_le_tau_zdGraph (d := d) p n v
    rw [hP', ← ENNReal.ofReal_pow (by positivity)] at h
    exact (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one _ _ _))).1 h
  have hpos : ∀ n : ℕ, 0 < tau q 0 (n • v) := by
    intro n
    have h := pow_le_tau_zdGraph (d := d) p n v
    refine lt_of_lt_of_le (ENNReal.pow_pos ?_ _) h
    rw [hP']; exact ENNReal.ofReal_pos.2 hp0
  have hτpos : ∀ n : ℕ, 0 < (tau q 0 (n • v)).toReal := fun n => tau_toReal_pos (hpos n)
  obtain ⟨m, hm⟩ : ∃ m, Tendsto (fun n : ℕ => -Real.log (tau q 0 (n • v)).toReal / n) atTop
      (𝓝 m) := ⟨_, tendsto_neg_log_tau_div q v (tau_zdGraph_add_add p) hpos⟩
  refine ⟨m, hm, ?_, ?_⟩
  · -- lower bound
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · rw [hK0, Nat.cast_zero, zero_mul]
      exact ge_of_tendsto' hm fun n => div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg n)
    -- for every `λ ∈ (μ, 1/p)`
    have hstep : ∀ lam : ℝ, μ < lam → P * lam < 1 → (K : ℝ) * Real.log (1 / (P * lam)) ≤ m := by
      intro lam hlam hPl
      have hlam0 : 0 < lam := hμpos.trans hlam
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hμ.eventually (gt_mem_nhds hlam))
      have hc : ∀ ℓ, N + 1 ≤ ℓ → (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
          p.2.1.length = ℓ} : ℝ≥0∞) ≤ ENNReal.ofReal lam ^ ℓ := by
        intro ℓ hℓ
        have h1 := hN ℓ (by omega)
        have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
        have hcr : (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = ℓ} : ℝ) ≤
            lam ^ ℓ := by
          have := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) h1.le ℓ
          rwa [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
            inv_mul_cancel₀ hℓ0, Real.rpow_one] at this
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hlam0.le]
        exact ENNReal.ofReal_le_ofReal hcr
      -- the upper bound on `τ` for `n ≥ N + 1`
      have hup : ∀ n : ℕ, N + 1 ≤ n →
          (tau q 0 (n • v)).toReal ≤ (P * lam) ^ (n * K) / (1 - P * lam) := by
        intro n hn
        have hl1 := sum_natAbs_nsmul (d := d) n v
        have hy : N + 1 ≤ ∑ i, ((n • v) i - (0 : Fin d → ℤ) i).natAbs := by
          rw [hl1]; nlinarith
        have h := tau_zdGraph_le (p := p) hc (n • v) hy
        rw [hl1, hP', ← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity),
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)] at h
        rw [div_eq_mul_inv]
        exact ENNReal.toReal_le_of_le_ofReal (by
          have : 0 < 1 - P * lam := by linarith
          positivity) h
      have hPl0 : 0 < P * lam := by positivity
      have hlower : ∀ n : ℕ, N + 1 ≤ n →
          (K : ℝ) * Real.log (1 / (P * lam)) + Real.log (1 - P * lam) / n ≤
            -Real.log (tau q 0 (n • v)).toReal / n := by
        intro n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hl := Real.log_le_log (hτpos n) (hup n hn)
        rw [Real.log_div (by positivity) (by linarith), Real.log_pow] at hl
        rw [le_div_iff₀ hnpos, add_mul, div_mul_cancel₀ _ hnpos.ne', one_div, Real.log_inv]
        push_cast at hl ⊢
        nlinarith
      have hlim : Tendsto (fun n : ℕ => (K : ℝ) * Real.log (1 / (P * lam)) +
          Real.log (1 - P * lam) / n) atTop (𝓝 ((K : ℝ) * Real.log (1 / (P * lam)))) := by
        have := (tendsto_const_nhds (x := Real.log (1 - P * lam))).div_atTop
          tendsto_natCast_atTop_atTop
        simpa using (tendsto_const_nhds (x := (K : ℝ) * Real.log (1 / (P * lam)))).add this
      exact le_of_tendsto_of_tendsto hlim hm (eventually_atTop.2 ⟨N + 1, hlower⟩)
    -- let `λ ↓ μ`
    have hcont : Tendsto (fun lam : ℝ => (K : ℝ) * Real.log (1 / (P * lam))) (𝓝[>] μ)
        (𝓝 ((K : ℝ) * Real.log (1 / (P * μ)))) := by
      have hPμ0 : 0 < P * μ := mul_pos hp0 hμpos
      have hc0 : ContinuousAt (fun lam : ℝ => P * lam) μ := by fun_prop
      have hc1 : ContinuousAt (fun lam : ℝ => 1 / (P * lam)) μ :=
        continuousAt_const.div hc0 hPμ0.ne'
      have hc2 : ContinuousAt (fun lam : ℝ => (K : ℝ) * Real.log (1 / (P * lam))) μ :=
        continuousAt_const.mul (hc1.log (one_div_pos.2 hPμ0).ne')
      exact hc2.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ lam in 𝓝[>] μ, (K : ℝ) * Real.log (1 / (P * lam)) ≤ m := by
      have h1 : ∀ᶠ lam in 𝓝 μ, P * lam < 1 :=
        (show ContinuousAt (fun lam : ℝ => P * lam) μ by fun_prop).eventually (gt_mem_nhds hpμ)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds] with lam hl1 hl2
      exact hstep lam hl1 hl2
    exact le_of_tendsto hcont hev
  · -- upper bound
    refine le_of_tendsto hm (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hl := Real.log_le_log (by positivity) (hlow n)
    rw [Real.log_pow] at hl
    rw [div_le_iff₀ hnpos, one_div, Real.log_inv]
    push_cast at hl ⊢
    nlinarith

open Classical in
/-- **Directional rate of nearest-neighbour percolation, with `p < μ_d⁻¹`.** The form of
`exists_tendsto_neg_log_tau_div_nearestNeighbour` with the hypothesis `p < μ_d⁻¹`, adding that
the rate is positive for `v ≠ 0`. -/
theorem exists_tendsto_neg_log_tau_div_nearestNeighbour_of_lt_inv (hd : 1 ≤ d) {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
      p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ))
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hpμ : (p : ℝ) < μ⁻¹) (v : Fin d → ℤ) :
    ∃ m : ℝ, Tendsto (fun n : ℕ => -Real.log (tau (fun e => if e ∈ (zdGraph d).edgeSet then p
        else 0) 0 (n • v)).toReal / n) atTop (𝓝 m) ∧
      (∑ i, (v i).natAbs : ℕ) * Real.log (1 / ((p : ℝ) * μ)) ≤ m ∧
      m ≤ (∑ i, (v i).natAbs : ℕ) * Real.log (1 / (p : ℝ)) ∧
      (v ≠ 0 → 0 < m) := by
  obtain ⟨μ', hμ', -, hμ'1, -⟩ := exists_tendsto_card_paths_rpow hd
  have hμpos : 0 < μ := by rw [tendsto_nhds_unique hμ hμ']; linarith
  have hpμ' : (p : ℝ) * μ < 1 := by
    have := mul_lt_mul_of_pos_right hpμ hμpos
    rwa [inv_mul_cancel₀ hμpos.ne'] at this
  obtain ⟨m, hm, hlo, hhi⟩ :=
    exists_tendsto_neg_log_tau_div_nearestNeighbour hd hμ p hp0 hpμ' v
  refine ⟨m, hm, hlo, hhi, fun hv => lt_of_lt_of_le ?_ hlo⟩
  have hK : 0 < ∑ i, (v i).natAbs := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact Finset.sum_pos' (fun j _ => Nat.zero_le _) ⟨i, Finset.mem_univ _, Int.natAbs_pos.2 hi⟩
  have hlog : 0 < Real.log (1 / ((p : ℝ) * μ)) :=
    Real.log_pos ((one_lt_div (mul_pos hp0 hμpos)).2 hpμ')
  have hK' : (0 : ℝ) < (∑ i, (v i).natAbs : ℕ) := by exact_mod_cast hK
  positivity

end NearestNeighbour

/-! ### Power-law intensities -/

section PowerLaw

open PercLib.Models.LongRange

/-- The radial kernel of a profile `K` for the sup norm, at integer points, is a function of
`y - x`. -/
theorem radialKernel_normSeminorm (K : ℝ → ℝ) (x y : Fin d → ℤ) :
    radialKernel (normSeminorm ℝ (Fin d → ℝ)) K s(x, y) =
      if y - x = 0 then 0 else (K ‖y - x‖).toNNReal := by
  rw [radialKernel_mk, normSeminorm_intCast, norm_sub_rev]
  by_cases h : x = y
  · subst h; simp
  · have h' : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    simp [h, h']

/-- The power-law weights `‖z‖^{-d-α}` on `ℤ^d \ {0}` are summable for `α > 0`. -/
theorem summable_powerLaw (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    Summable (fun z : Fin d → ℤ => if z = 0 then (0 : ℝ) else ‖z‖ ^ (-((d : ℝ) + α))) :=
  (summable_powerLaw_iff hd α).2 hα

/-- **Zero directional rate for power-law intensities.** For the power-law intensities
`q_β = 1 - exp(-β ‖y - x‖^{-d-α})` (sup norm) with `β > 0`, `-(1/n) log τ(0, n v) → 0` for
every `v`. -/
theorem tendsto_neg_log_tau_div_powerLaw_zero {α : ℝ} (hα : 0 < α) {β : NNReal} (hβ : 0 < β)
    (v : Fin d → ℤ) :
    Tendsto (fun n : ℕ => -Real.log (tau (intensityProfile (radialKernel
        (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) 0
          (n • v)).toReal / n) atTop (𝓝 0) := by
  set q := intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
    (powerLawProfile 1 ((d : ℝ) + α))) β with hq
  by_cases hv : v = 0
  · subst hv
    simp [tau_self]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hb : (0 : ℝ) < β := hβ
  set a : ℝ := (d : ℝ) + α with ha
  set e₁ : ℝ := 1 - Real.exp (-1) with he₁
  have he₁pos : 0 < e₁ := by
    rw [he₁, sub_pos]
    exact (Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)).trans_eq Real.exp_zero
  -- `τ(0, nv) ≥ q(0, nv) ≥ t_n (1 - e⁻¹)` with `t_n = β (n ‖v‖)^{-a} ≤ 1`
  have hτ : ∀ n : ℕ, 1 ≤ n → ((β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a) ≤ 1) →
      (β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a) * e₁ ≤ (tau q 0 (n • v)).toReal := by
    intro n hn ht1
    have hnv : (0 : Fin d → ℤ) ≠ n • v := by
      intro h
      have : n • v = 0 := h.symm
      rw [smul_eq_zero] at this
      rcases this with h | h
      · omega
      · exact hv h
    -- the single edge
    have hw := prod_le_tau_of_walk q
      (SimpleGraph.Walk.cons (show (⊤ : SimpleGraph (Fin d → ℤ)).Adj 0 (n • v) from hnv)
        SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.toFinset_cons,
      List.toFinset_nil, insert_empty_eq, Finset.prod_singleton] at hw
    have hnorm : ‖n • v‖ = (n : ℝ) * ‖v‖ := by
      rw [← natCast_zsmul, norm_smul, Int.norm_natCast]
    have hqv : (q s(0, n • v) : ℝ) = 1 - Real.exp (-((β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a))) := by
      rw [hq]
      change 1 - Real.exp (-(β : ℝ) * ((radialKernel _ _ s(0, n • v) : NNReal) : ℝ)) = _
      rw [radialKernel_normSeminorm, ite_eq_right (by simpa using hnv.symm), sub_zero,
        powerLawProfile, one_mul, Real.coe_toNNReal _ (Real.rpow_nonneg (norm_nonneg _) _),
        hnorm, neg_mul]
    have h1 := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one _ _ _)) hw
    rw [ENNReal.coe_toReal] at h1
    change (q s(0, n • v) : ℝ) ≤ _ at h1
    rw [hqv] at h1
    have htpos : 0 < (β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have h2 := PercLib.Probability.mul_one_sub_exp_neg_le htpos ht1
    rw [one_mul] at h2
    exact h2.trans h1
  -- eventually `t_n ≤ 1`
  have ha0 : 0 < a := by rw [ha]; positivity
  have hnv : Tendsto (fun n : ℕ => (n : ℝ) * ‖v‖) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hvpos
  have ht0 : Tendsto (fun n : ℕ => (β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop ha0).comp hnv
    simpa using this.const_mul (β : ℝ)
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ (β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a) ≤ 1 :=
    (eventually_ge_atTop 1).and (ht0.eventually (eventually_le_nhds one_pos))
  -- the upper envelope
  have hlogn : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  set c₀ : ℝ := -Real.log e₁ - Real.log β + a * Real.log ‖v‖ with hc₀
  have hup : Tendsto (fun n : ℕ => c₀ / n + a * (Real.log n / n)) atTop (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := c₀)).div_atTop tendsto_natCast_atTop_atTop
    simpa using h1.add (hlogn.const_mul a)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg n)) ?_
  filter_upwards [hev] with n ⟨hn1, ht1⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have htpos : 0 < (β : ℝ) * ((n : ℝ) * ‖v‖) ^ (-a) := by positivity
  have hl := Real.log_le_log (by positivity) (hτ n hn1 ht1)
  rw [Real.log_mul htpos.ne' he₁pos.ne', Real.log_mul hb.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_mul hnpos.ne' hvpos.ne'] at hl
  have key : -Real.log (tau q 0 (n • v)).toReal ≤ c₀ + a * Real.log n := by
    rw [hc₀]; nlinarith
  calc -Real.log (tau q 0 (n • v)).toReal / n ≤ (c₀ + a * Real.log n) / n :=
        div_le_div_of_nonneg_right key hnpos.le
    _ = c₀ / n + a * (Real.log n / n) := by ring

/-- **Susceptibility bound for power-law intensities.** If `β M < 1` with
`M = ∑_{z ≠ 0} ‖z‖^{-d-α}`, then `χ(q_β) ≤ (1 - βM)⁻¹`. -/
theorem chi_intensity_powerLaw_le (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (β : NNReal)
    (hβ : (β : ℝ) * ∑' z : Fin d → ℤ, (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))) β) x ≤
      ENNReal.ofReal (1 - (β : ℝ) * ∑' z : Fin d → ℤ,
        (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))))⁻¹ := by
  set f : (Fin d → ℤ) → ℝ := fun z => if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α)) with hf
  have hf0 : ∀ z, 0 ≤ f z := powerLaw_nonneg _
  have hs : Summable f := summable_powerLaw hd hα
  set M : NNReal := (∑' z, f z).toNNReal with hM
  have hMr : (M : ℝ) = ∑' z, f z := Real.coe_toNNReal _ (tsum_nonneg hf0)
  have hk : ∑' z, ((f z).toNNReal : ℝ≥0∞) ≤ M :=
    le_of_eq (ENNReal.ofReal_tsum_of_nonneg hf0 hs).symm
  have hβM : (β : ℝ≥0∞) * M < 1 := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
      NNReal.coe_mul, hMr]
    simpa using hβ
  have hJ : ∀ x y : Fin d → ℤ, radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) s(x, y) = (f (y - x)).toNNReal := by
    intro x y
    rw [radialKernel_normSeminorm]
    by_cases h : y - x = 0 <;> simp [h, f, powerLawProfile]
  have h := PercLib.Models.chi_intensity_le_of_translationInvariant _ (fun z => (f z).toNNReal)
    hJ M hk β hβM x
  refine h.trans (le_of_eq ?_)
  have h1 : (β : ℝ≥0∞) * M = ENNReal.ofReal ((β : ℝ) * ∑' z, f z) := by
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg β), ENNReal.ofReal_coe_nnreal, ← hMr,
      ENNReal.ofReal_coe_nnreal]
  have h2 : 0 < 1 - (β : ℝ) * ∑' z, f z := by linarith
  rw [h1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity),
    ENNReal.ofReal_inv_of_pos h2]

end PowerLaw

/-! ### Non-vacuity witnesses -/

section Witness

open PercLib.Models.LongRange

open Classical in
/-- The nearest-neighbour rate bound on `ℤ` at `p = 1/2`: there `μ₁ ≤ 1`, so `p < μ₁⁻¹`, and
the rate exists with the two-sided bound and is positive, for `v = 1`. -/
example : ∃ μ : ℝ, Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph 1).Path 0 y //
      p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧
    ∃ m : ℝ, Tendsto (fun n : ℕ => -Real.log (tau (fun e => if e ∈ (zdGraph 1).edgeSet then
        (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0) 0
          (n • (fun _ => 1 : Fin 1 → ℤ))).toReal / n) atTop (𝓝 m) ∧
      (∑ i, ((fun _ => 1 : Fin 1 → ℤ) i).natAbs : ℕ) * Real.log (1 / ((1 / 2 : ℝ) * μ)) ≤ m ∧
      m ≤ (∑ i, ((fun _ => 1 : Fin 1 → ℤ) i).natAbs : ℕ) * Real.log (1 / (1 / 2 : ℝ)) ∧
      ((fun _ => 1 : Fin 1 → ℤ) ≠ 0 → 0 < m) := by
  obtain ⟨μ, hμ, -, h1μ, hμ1⟩ := exists_tendsto_card_paths_rpow (d := 1) le_rfl
  refine ⟨μ, hμ, exists_tendsto_neg_log_tau_div_nearestNeighbour_of_lt_inv le_rfl hμ _
    (by norm_num) ?_ _⟩
  push_cast at hμ1
  change (1 / 2 : ℝ) < μ⁻¹
  calc (1 / 2 : ℝ) < 1 := by norm_num
    _ ≤ μ⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)

/-- The zero power-law rate on `ℤ` with `α = β = 1`. -/
example : Tendsto (fun n : ℕ => -Real.log (tau (intensityProfile (radialKernel
    (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 (((1 : ℕ) : ℝ) + 1))) 1) 0
      (n • (fun _ => 1 : Fin 1 → ℤ))).toReal / n) atTop (𝓝 0) :=
  tendsto_neg_log_tau_div_powerLaw_zero one_pos one_pos _

/-- The power-law susceptibility bound on `ℤ` with `α = 1` and `β = 1/8`: here `M ≤ 4`, so
`β M < 1`. -/
example : chi (intensityProfile (radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
    (powerLawProfile 1 (((1 : ℕ) : ℝ) + 1))) (1 / 8)) 0 ≤
      ENNReal.ofReal (1 - ((1 / 8 : NNReal) : ℝ) * ∑' z : Fin 1 → ℤ,
        (if z = 0 then 0 else ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1))))⁻¹ := by
  refine chi_intensity_powerLaw_le le_rfl one_pos (1 / 8) ?_ 0
  set f : (Fin 1 → ℤ) → ℝ := fun z => if z = 0 then 0 else ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1))
  have hf0 : ∀ z, 0 ≤ f z := fun z => powerLaw_nonneg _ z
  have hs : Summable f := (summable_powerLaw_iff le_rfl 1).2 one_pos
  have htail := tsum_ofReal_powerLaw_tail_le (d := 1) le_rfl one_pos le_rfl
  have hle : ∀ z : Fin 1 → ℤ, ENNReal.ofReal (f z) ≤
      ENNReal.ofReal (if (1 : ℝ) ≤ ‖z‖ then ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1)) else 0) := by
    intro z
    by_cases hz : z = 0
    · simp [f, hz]
    · simp [f, hz, one_le_norm_of_ne_zero hz]
  have hM : ∑' z, f z ≤ 4 := by
    have h := (ENNReal.tsum_le_tsum hle).trans htail
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hs] at h
    have h4 : (((2 * 1 * 3 ^ (1 - 1) : ℕ) : ℝ) * ((1 + 1 / 1) * (1 : ℝ) ^ (-(1 : ℝ)))) = 4 := by
      norm_num
    rw [h4] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 h
  change ((1 / 8 : NNReal) : ℝ) * ∑' z, f z < 1
  have h8 : ((1 / 8 : NNReal) : ℝ) = 1 / 8 := by norm_num
  rw [h8]
  linarith

end Witness

end PercLib.Models.Site
