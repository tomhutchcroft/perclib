/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the universal tightness, quantile moment and finite-set hyperscaling
assertions. All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Percolation.Bond.Tightness.Moments
public import PercLib.Percolation.Bond.Tightness.TruncatedMean
public import PercLib.Percolation.Bond.Tightness.WindowTails
public import PercLib.Percolation.Bond.Forest

/-!
# Universal tightness and hyperscaling: correspondence

Wiki correspondence for universal tightness, quantile moments and finite-set hyperscaling.

## Main results

* `universal_upper_lower_tails`
* `rooted_upper_tail`
* `tails_from_witness_splitting`
* `moment_le_quantile_pow`
* `expected_maximum_comparable`
* `finite_set_hyperscaling`
* `finite_window_hyperscaling`
* `hyperscaling_exponent_inequalities`
* `exponent_relations_sampled_root`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Nat

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The universal upper tail of the largest intersection at the quantile scale and the
universal lower tail, for every profile and every finite nonempty observation set. -/
@[tag "4724"]
theorem universal_upper_lower_tails [Countable V] :
    ∀ (q : Sym2 V → unitInterval) (Λ : Finset V), Λ.Nonempty →
      (∀ a : ℝ, 1 ≤ a →
        law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-a / 9))) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        law q {ω | (maxClusterIntersection Λ ω : ℝ) < ε * (tightnessScale q Λ : ℝ)} ≤
          ENNReal.ofReal (27 * ε)) :=
  fun q _Λ hΛ => ⟨fun _a ha => law_mul_tightnessScale_le_maxClusterIntersection_le q hΛ ha,
    fun _ε hε hε1 => law_maxClusterIntersection_lt_mul_tightnessScale_le q hΛ hε hε1⟩

/-- The rooted upper tail: `P(X_u ≥ a M) ≤ e^{1 - a/9} P(X_u ≥ M)` for every root. -/
@[tag "21D4"]
theorem rooted_upper_tail [Countable V] :
    ∀ (q : Sym2 V → unitInterval) (Λ : Finset V), Λ.Nonempty → ∀ (u : V) (a : ℝ), 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp (1 - a / 9)) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} := by
  intro q Λ hΛ u a ha
  refine (law_mul_tightnessScale_le_clusterIntersection_le q hΛ u ha).trans_eq ?_
  rw [sub_eq_add_neg, ← neg_div, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- The BK step for the maximum and for a rooted intersection, together with its three
consequences: the upper tail, the rooted upper tail and the lower tail at scale `M`. -/
@[tag "12NL"]
theorem tails_from_witness_splitting [Countable V] (q : Sym2 V → unitInterval)
    (Λ : Finset V) (hΛ : Λ.Nonempty) :
    (∀ (l : ℝ), 1 ≤ l → ∀ k : ℕ, 1 ≤ k →
      law q {ω | (3 : ℝ) ^ k * l ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
          law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ (3 ^ (k - 1) + 1) ∧
      ∀ u : V,
        law q {ω | (3 : ℝ) ^ k * l ≤ (clusterIntersection Λ ω u : ℝ)} ≤
          law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ (3 ^ (k - 1)) *
            law q {ω | l ≤ (clusterIntersection Λ ω u : ℝ)}) ∧
    (∀ r : ℝ, 1 ≤ r →
      law q {ω | r * (tightnessScale q Λ : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-r / 9))) ∧
    (∀ (u : V) (r : ℝ), 1 ≤ r →
      law q {ω | r * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp (1 - r / 9)) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u}) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      law q {ω | (maxClusterIntersection Λ ω : ℝ) < ε * (tightnessScale q Λ : ℝ)} ≤
        ENNReal.ofReal (27 * ε)) :=
  ⟨fun _l hl _k hk => ⟨law_three_pow_mul_le_maxClusterIntersection_le q hΛ hl hk,
      fun u => law_three_pow_mul_le_clusterIntersection_le q Λ u hl hk⟩,
    fun _r hr => law_mul_tightnessScale_le_maxClusterIntersection_le q hΛ hr,
    rooted_upper_tail q Λ hΛ,
    fun _ε hε hε1 => law_maxClusterIntersection_lt_mul_tightnessScale_le q hΛ hε hε1⟩

/-- Deterministic bounds: `1 ≤ Z ≤ |Λ|` for every configuration and `2 ≤ M ≤ |Λ| + 1`. -/
@[tag "AU8B"]
theorem maximum_and_quantile_bounds (q : Sym2 V → unitInterval) {Λ : Finset V}
    (hΛ : Λ.Nonempty) :
    (∀ ω, 1 ≤ maxClusterIntersection Λ ω ∧ maxClusterIntersection Λ ω ≤ Λ.card) ∧
    2 ≤ tightnessScale q Λ ∧ tightnessScale q Λ ≤ Λ.card + 1 :=
  ⟨fun ω => ⟨one_le_maxClusterIntersection hΛ ω,
    Finset.sup_le fun v _ => clusterIntersection_le_card Λ ω v⟩,
    two_le_tightnessScale q hΛ, tightnessScale_le_card_add_one q Λ⟩

/-- Every moment of the largest intersection is at most an explicit constant, independent
of the graph, the profile and `Λ`, times the matching power of `M`. -/
@[tag "2FN1"]
theorem moment_le_quantile_pow [Countable V] :
    ∀ (q : Sym2 V → unitInterval) (Λ : Finset V), Λ.Nonempty → ∀ k : ℕ,
      ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ k ∂(law q) ≤
        (20 * 18 ^ k * k ! : ℝ≥0∞) * (tightnessScale q Λ : ℝ≥0∞) ^ k :=
  fun q _ hΛ k => lintegral_maxClusterIntersection_pow_le q hΛ k

/-- The expected largest intersection is comparable to `M`:
`(M - 1)/e ≤ E Z`, `M/(2e) ≤ E Z` and `E Z ≤ 360 M`. -/
@[tag "AWWZ"]
theorem expected_maximum_comparable [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) :
    ENNReal.ofReal (((tightnessScale q Λ : ℝ) - 1) * Real.exp (-1)) ≤
        ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ∂(law q) ∧
    ENNReal.ofReal ((tightnessScale q Λ : ℝ) / (2 * Real.exp 1)) ≤
        ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ∂(law q) ∧
    ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ∂(law q) ≤
        360 * (tightnessScale q Λ : ℝ≥0∞) := by
  refine ⟨lintegral_maxClusterIntersection_ge_sub_one q hΛ,
    lintegral_maxClusterIntersection_ge q hΛ, ?_⟩
  have h := moment_le_quantile_pow q Λ hΛ 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h
  refine h.trans_eq ?_
  norm_num

/-- On a finite vertex type: stability of `M` under nearby smaller profiles, left
stability along the intensity family including the endpoint, and the endpoint transfer
of a squared-quantile bound. -/
@[tag "0SB0"]
theorem finite_quantile_stability [Finite V] (Λ : Finset V) :
    (∀ q : Sym2 V → unitInterval,
      ∀ᶠ p in 𝓝 q, p ≤ q → tightnessScale p Λ = tightnessScale q Λ) ∧
    (∀ (J : Sym2 V → ℝ≥0) (b : ℝ≥0), ∀ᶠ a in 𝓝[Set.Iic b] b,
      tightnessScale (intensityProfile J a) Λ = tightnessScale (intensityProfile J b) Λ) ∧
    (∀ (J : Sym2 V → ℝ≥0) (b : ℝ≥0), 0 < b → ∀ C : ℝ,
      (∀ a : ℝ≥0, 0 < a → a < b →
        (a : ℝ) * (tightnessScale (intensityProfile J a) Λ : ℝ) ^ 2 ≤ C) →
      (b : ℝ) * (tightnessScale (intensityProfile J b) Λ : ℝ) ^ 2 ≤ C) :=
  ⟨fun _ => eventually_tightnessScale_eq_of_profile_le id continuousAt_id Λ,
    fun J b => finite_quantile_left_stable J Λ b,
    fun J _ hb _ hC => finite_quantile_sq_bound_at_endpoint J Λ hb hC⟩

/-- Lower rooted moments from the quantile: the partition bound, the quantile lower bound,
and, when all full-cluster `p`-th moments over `Λ` equal `m` (extended values allowed),
`m ≥ M^(p+1)/(e 2^(p+1) |Λ|)`. -/
@[tag "LQ6Y"]
theorem quantile_lower_rooted_moments [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) {p : ℝ} (hp : 0 ≤ p) (m : ℝ≥0∞) :
    ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ (p + 1) ∂(law q) ≤
        ∑ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ^ p ∂(law q) ∧
    ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ (p + 1) / (Real.exp 1 * 2 ^ (p + 1))) ≤
        ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ (p + 1) ∂(law q) ∧
    ((∀ x ∈ Λ, ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ p ∂(law q) = m) →
      ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ (p + 1) /
        (Real.exp 1 * 2 ^ (p + 1) * Λ.card)) ≤ m) := by
  have h1 := lintegral_rpow_max_le_sum q hΛ hp
  have h2 := le_lintegral_rpow_max q hΛ hp
  refine ⟨h1, h2, fun hm => ?_⟩
  have hle : ∀ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ^ p ∂(law q) ≤ m := by
    intro x hx
    rw [← hm x hx]
    refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp
    have hc : (clusterIntersection Λ ω x : ℕ∞) ≤ (cluster ω x).encard :=
      calc (clusterIntersection Λ ω x : ℕ∞) = (cluster ω x ∩ (Λ : Set V)).encard :=
            (Λ.finite_toSet.subset Set.inter_subset_right).cast_ncard_eq
        _ ≤ (cluster ω x).encard := Set.encard_le_encard Set.inter_subset_left
    simpa using ENat.toENNReal_le.mpr hc
  have hsum : ∑ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ^ p ∂(law q) ≤
      m * Λ.card := by
    refine (Finset.sum_le_sum hle).trans_eq ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard : (0 : ℝ) < Λ.card := by exact_mod_cast Finset.card_pos.mpr hΛ
  rw [← div_div, ENNReal.ofReal_div_of_pos hcard, ENNReal.ofReal_natCast]
  exact ENNReal.div_le_of_le_mul ((h2.trans h1).trans hsum)

/-- Finite-set hyperscaling from a uniform cluster tail and rooted damping, with the
explicit constants `C₁ = (4eL)^{δ/(δ+1)}`, `C₂ = L (4eL)^{(δ-1)/(δ+1)}`,
`L = C (δ/(δ-1) + 9 e^{8/9})`. -/
@[tag "WRHL"]
theorem finite_set_hyperscaling [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 1 < δ)
    (hclus : ∀ (x : V) (n : ℕ), 1 ≤ n →
      law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / δ))))
    (hdamp : ∀ (u : V) (a : ℝ), 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp 1) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9))) :
    (tightnessScale q Λ : ℝ) ≤
        (4 * Real.exp 1 * (C * (δ / (δ - 1) + 9 * Real.exp (8 / 9)))) ^ (δ / (δ + 1)) *
          (Λ.card : ℝ) ^ (δ / (δ + 1)) ∧
    ∀ x : V, (Λ.card : ℝ≥0∞)⁻¹ * ∑ v ∈ Λ, tau q x v ≤
      ENNReal.ofReal (C * (δ / (δ - 1) + 9 * Real.exp (8 / 9)) *
        (4 * Real.exp 1 * (C * (δ / (δ - 1) + 9 * Real.exp (8 / 9)))) ^ ((δ - 1) / (δ + 1)) *
        (Λ.card : ℝ) ^ (-2 / (δ + 1))) :=
  ⟨tightnessScale_le_of_cluster_tail q hΛ hC hδ hclus hdamp,
    avg_tau_le_of_cluster_tail q hΛ hC hδ hclus hdamp⟩

/-- Finite-window hyperscaling in independent bond percolation from a uniform window tail
`P(|K_u ∩ Λ| ≥ n) ≤ A n^{-θ}`, with `H_θ = (1-θ)⁻¹ + 9e^{8/9}`; for `θ ≤ 1/2` the
constant is bounded by the universal `4e(2 + 9e^{8/9})²`. -/
@[tag "UVQ6"]
theorem finite_window_hyperscaling [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ (u : V) (n : ℕ), 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ))) :
    (tightnessScale q Λ : ℝ) ≤
        (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) * A * Λ.card) ^ (1 / (1 + θ)) ∧
    (∀ u : V, ∑ v ∈ Λ, tau q u v ≤ ENNReal.ofReal (((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) *
      (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9))) ^ ((1 - θ) / (1 + θ)) *
      A ^ (2 / (1 + θ)) * (Λ.card : ℝ) ^ ((1 - θ) / (1 + θ)))) ∧
    (θ ≤ 1 / 2 → ∀ u : V, ∑ v ∈ Λ, tau q u v ≤ ENNReal.ofReal
      (4 * Real.exp 1 * (2 + 9 * Real.exp (8 / 9)) ^ 2 * A ^ (2 / (1 + θ)) *
        (Λ.card : ℝ) ^ ((1 - θ) / (1 + θ)))) := by
  refine ⟨tightnessScale_le_of_window_tail q hΛ hA hθ0 hθ1 htail,
    sum_tau_le_of_window_tail q hΛ hA hθ0 hθ1 htail, fun hθ u => ?_⟩
  refine (sum_tau_le_of_window_tail q hΛ hA hθ0 hθ1 htail u).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set H := (1 - θ)⁻¹ + 9 * Real.exp (8 / 9) with hHdef
  set c := (1 - θ) / (1 + θ) with hc
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have he89 : 1 ≤ Real.exp (8 / 9) := Real.one_le_exp (by norm_num)
  have hinv0 : 0 ≤ (1 - θ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hinv2 : (1 - θ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hH9 : 9 ≤ H := by rw [hHdef]; nlinarith
  have hHle : H ≤ 2 + 9 * Real.exp (8 / 9) := by rw [hHdef]; linarith
  have hbase : 1 ≤ 4 * Real.exp 1 * H := by nlinarith
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by linarith)]
    linarith
  have hpow : (4 * Real.exp 1 * H) ^ c ≤ 4 * Real.exp 1 * H := by
    calc (4 * Real.exp 1 * H) ^ c ≤ (4 * Real.exp 1 * H) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hc1
      _ = 4 * Real.exp 1 * H := Real.rpow_one _
  have hpow0 : 0 ≤ (4 * Real.exp 1 * H) ^ c := Real.rpow_nonneg (by linarith) c
  have hkey : H * (4 * Real.exp 1 * H) ^ c ≤ 4 * Real.exp 1 * (2 + 9 * Real.exp (8 / 9)) ^ 2 :=
    calc H * (4 * Real.exp 1 * H) ^ c ≤ H * (4 * Real.exp 1 * H) :=
          mul_le_mul_of_nonneg_left hpow (by linarith)
      _ ≤ (2 + 9 * Real.exp (8 / 9)) * (4 * Real.exp 1 * (2 + 9 * Real.exp (8 / 9))) := by
          apply mul_le_mul hHle _ (by nlinarith) (by linarith)
          nlinarith
      _ = _ := by ring
  have hA' : 0 ≤ A ^ (2 / (1 + θ)) := Real.rpow_nonneg hA _
  have hN' : 0 ≤ (Λ.card : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hA') hN'

/-- Polynomial window tails at one root acquire exponential damping at scale `18M`, and
give fractional moments of every order `p > θ`. -/
@[tag "MJEP"]
theorem window_tail_damping_and_moments [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ n : ℕ, 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ))) :
    (∀ n : ℕ, 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤
        ENNReal.ofReal (Real.exp 1 * A * (18 / (n : ℝ)) ^ θ *
          Real.exp (-(n : ℝ) / (18 * tightnessScale q Λ)))) ∧
    (∀ p : ℝ, θ < p →
      ∫⁻ ω, ENNReal.ofReal ((clusterIntersection Λ ω u : ℝ) ^ p) ∂(law q) ≤
        ENNReal.ofReal (Real.exp 1 * A * 18 ^ p * p * Real.Gamma (p - θ) *
          (tightnessScale q Λ : ℝ) ^ (p - θ))) :=
  ⟨law_le_clusterIntersection_le_damped q hΛ u hA hθ0 hθ1 htail,
    fun _ hp => lintegral_rpow_clusterIntersection_le q hΛ u hA hθ0 hθ1 htail hp⟩

/-- Hyperscaling exponent inequalities for a family of windows `Λ_R`, under the uniform
cluster tail of `finite_set_hyperscaling` (rooted damping is supplied by universal
tightness): `d_f/d ≤ δ/(δ+1)`, `s ≤ d(δ-1)/(δ+1)`, and `δ = s = 2` forces `d ≥ 6`. -/
@[tag "7VCS"]
theorem hyperscaling_exponent_inequalities [Countable V] (q : Sym2 V → unitInterval)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 1 < δ)
    (hclus : ∀ (x : V) (n : ℕ), 1 ≤ n →
      law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / δ))))
    (Λ : ℝ → Finset V) (hne : ∀ᶠ R in atTop, (Λ R).Nonempty) (o : V) {d df σ : ℝ}
    (hd : 0 < d)
    (hspos : ∀ᶠ R in atTop, 0 < (∑ v ∈ Λ R, tau q o v).toReal)
    (hN : Tendsto (fun R => Real.log ((Λ R).card : ℝ) / Real.log R) atTop (𝓝 d))
    (hM : Tendsto (fun R => Real.log (tightnessScale q (Λ R) : ℝ) / Real.log R) atTop (𝓝 df))
    (hs : Tendsto (fun R => Real.log (∑ v ∈ Λ R, tau q o v).toReal / Real.log R) atTop
      (𝓝 σ)) :
    df / d ≤ δ / (δ + 1) ∧ σ ≤ d * (δ - 1) / (δ + 1) ∧ (δ = 2 → σ = 2 → 6 ≤ d) := by
  set L := C * (δ / (δ - 1) + 9 * Real.exp (8 / 9)) with hLdef
  have hL : 0 ≤ L := mul_nonneg hC (add_nonneg (div_pos (by linarith) (by linarith)).le
    (by positivity))
  have hmain := dimension_bounds_of_hyperscaling (N := fun R => ((Λ R).card : ℝ))
    (Mr := fun R => (tightnessScale q (Λ R) : ℝ))
    (s := fun R => (∑ v ∈ Λ R, tau q o v).toReal)
    (C₁ := (4 * Real.exp 1 * L) ^ (δ / (δ + 1)))
    (C₂ := L * (4 * Real.exp 1 * L) ^ ((δ - 1) / (δ + 1))) hd hδ
    (by
      filter_upwards [hne, hspos] with R hR hsR
      refine ⟨by exact_mod_cast Finset.card_pos.mpr hR, ?_, hsR⟩
      have := two_le_tightnessScale q hR
      have : (2 : ℝ) ≤ tightnessScale q (Λ R) := by exact_mod_cast this
      linarith)
    hN hM hs
    (by
      filter_upwards [hne] with R hR
      exact tightnessScale_le_of_cluster_tail q hR hC hδ hclus
        fun u _a ha => law_mul_tightnessScale_le_clusterIntersection_le q hR u ha)
    (by
      filter_upwards [hne] with R hR
      have h := avg_tau_le_of_cluster_tail q hR hC hδ hclus
        (fun u _a ha => law_mul_tightnessScale_le_clusterIntersection_le q hR u ha) o
      have hnn : 0 ≤ L * (4 * Real.exp 1 * L) ^ ((δ - 1) / (δ + 1)) *
          ((Λ R).card : ℝ) ^ (-2 / (δ + 1)) :=
        mul_nonneg (mul_nonneg hL (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h' := ENNReal.toReal_le_of_le_ofReal hnn h
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast] at h'
      rw [div_eq_inv_mul]
      exact h')
  refine ⟨hmain.1, hmain.2, ?_⟩
  rintro rfl rfl
  have h2 := hmain.2
  norm_num at h2
  linarith

open Classical in
/-- Exponent relations for the sampled-root variable and the window intersections of a
family of profiles and windows; the counting identity is proved, not assumed. When
`κ = 0`, `d_f = dδ/(δ+1)` and `α = d(δ-1)/(δ+1)`. -/
@[tag "DEZI"]
theorem exponent_relations_sampled_root [Countable V] (q : ℝ → Sym2 V → unitInterval)
    (Λ : ℝ → Finset V) {v EN : ℝ → ℝ} {F : ℕ → ℝ} {d df κ α δ : ℝ}
    (hdf : 0 < df) (hδ : 0 < δ)
    (hΛ : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c * r ^ d ≤ ((Λ r).card : ℝ) ∧ ((Λ r).card : ℝ) ≤ C * r ^ d)
    (hv : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ df ≤ v r ∧ v r ≤ C * r ^ df)
    (hEN : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ^ κ ≤ EN r ∧ EN r ≤ C * r ^ κ)
    (hES : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c * (v r ^ 2 * EN r) ≤ (∫⁻ ω, ∑ D ∈ (Λ r).image (fun x => (Λ r).filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) ^ 2 ∂law (q r)).toReal ∧
      (∫⁻ ω, ∑ D ∈ (Λ r).image (fun x => (Λ r).filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) ^ 2 ∂law (q r)).toReal ≤ C * (v r ^ 2 * EN r))
    (hEX : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c * r ^ α ≤ (((Λ r).card : ℝ≥0∞)⁻¹ *
        ∑ x ∈ Λ r, ∫⁻ ω, (clusterIntersection (Λ r) ω x : ℝ≥0∞) ∂law (q r)).toReal ∧
      (((Λ r).card : ℝ≥0∞)⁻¹ *
        ∑ x ∈ Λ r, ∫⁻ ω, (clusterIntersection (Λ r) ω x : ℝ≥0∞) ∂law (q r)).toReal ≤
          C * r ^ α)
    (hF : ∃ c C : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (n : ℝ) ^ (-1 / δ) ≤ F n ∧ F n ≤ C * (n : ℝ) ^ (-1 / δ))
    (hFv : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c * (v r * EN r / (Λ r).card) ≤ F ⌈v r⌉₊ ∧ F ⌈v r⌉₊ ≤ C * (v r * EN r / (Λ r).card)) :
    α = 2 * df + κ - d ∧ df / δ = d - df - κ ∧ 0 < d - df - κ ∧
      (κ = 0 → df = d * δ / (δ + 1) ∧ α = d * (δ - 1) / (δ + 1)) := by
  have hOB : ∀ᶠ r in atTop,
      (((Λ r).card : ℝ≥0∞)⁻¹ *
        ∑ x ∈ Λ r, ∫⁻ ω, (clusterIntersection (Λ r) ω x : ℝ≥0∞) ∂law (q r)).toReal =
      (∫⁻ ω, ∑ D ∈ (Λ r).image (fun x => (Λ r).filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) ^ 2 ∂law (q r)).toReal / ((Λ r).card : ℝ) := by
    refine Eventually.of_forall fun r => ?_
    have h := avg_lintegral_pow_clusterIntersection (law (q r)) (Λ r) 1
    simp only [pow_one, one_add_one_eq_two] at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_inv_mul]
  obtain ⟨h1, h2, h3⟩ := exponent_relations (Λ := fun r => ((Λ r).card : ℝ)) hdf hδ hΛ hv hEN
    hES hEX hOB hF hFv
  refine ⟨h1, h2, h3, fun hκ => ?_⟩
  subst hκ
  have hδ1 : δ + 1 ≠ 0 := by linarith
  have hdf' : df = d * δ / (δ + 1) := by
    rw [eq_div_iff hδ1]
    field_simp at h2
    linarith
  refine ⟨hdf', ?_⟩
  rw [h1, hdf']
  field_simp
  ring

/-! ### Non-vacuity of 7VCS

The zero profile on `ℕ` with windows `{0, …, ⌈R⌉₊ - 1}`: every cluster is a single
vertex almost surely, so `C = 1`, `δ = 2` give the cluster tail, `M = 2`, the averaged
two-point sum is one, and the exponents are `d = 1`, `d_f = 0`, `s = 0`. -/

theorem ae_eq_empty_zero_profile :
    ∀ᵐ ω ∂law (fun _ : Sym2 ℕ => (0 : unitInterval)), ω = ∅ := by
  filter_upwards [ae_config_subset_positive (fun _ : Sym2 ℕ => (0 : unitInterval))] with ω hω
  exact Set.subset_empty_iff.mp fun e he => (lt_irrefl (0 : ℝ) (hω he))

theorem law_zero_profile_eq_zero {S : Set (Config ℕ)} (hS : (∅ : Config ℕ) ∉ S) :
    law (fun _ : Sym2 ℕ => (0 : unitInterval)) S = 0 := by
  refine measure_mono_null (fun ω hω (h : ω = ∅) => hS (h ▸ hω)) ?_
  exact ae_iff.mp ae_eq_empty_zero_profile

theorem tightnessScale_zero_profile {Λ : Finset ℕ} (hΛ : Λ.Nonempty) :
    tightnessScale (fun _ : Sym2 ℕ => (0 : unitInterval)) Λ = 2 := by
  refine le_antisymm ?_ (two_le_tightnessScale _ hΛ)
  rw [tightnessScale_le_iff, law_zero_profile_eq_zero]
  · exact zero_le
  · intro h
    have h' : 2 ≤ maxClusterIntersection Λ ∅ := h
    have : maxClusterIntersection Λ (∅ : Config ℕ) ≤ 1 := by
      apply Finset.sup_le
      intro v _
      rw [cluster_empty]
      exact (Set.ncard_le_ncard Set.inter_subset_left (Set.finite_singleton v)).trans
        (Set.ncard_singleton v).le
    omega

theorem tendsto_log_ceil_div_log :
    Tendsto (fun R : ℝ => Real.log ((Finset.range ⌈R⌉₊).card : ℝ) / Real.log R) atTop
      (𝓝 1) := by
  have hup : Tendsto (fun R : ℝ => 1 + Real.log 2 / Real.log R) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with R hR
    rw [Finset.card_range, le_div_iff₀ (Real.log_pos hR), one_mul]
    exact Real.log_le_log (by linarith) (Nat.le_ceil R)
  · filter_upwards [eventually_gt_atTop 1] with R hR
    have hl := Real.log_pos hR
    rw [Finset.card_range, div_le_iff₀ hl, add_mul, one_mul, div_mul_cancel₀ _ hl.ne',
      ← Real.log_mul (show R ≠ 0 by intro h; linarith) (show (2 : ℝ) ≠ 0 by norm_num)]
    refine Real.log_le_log (by exact_mod_cast Nat.ceil_pos.mpr (by linarith)) ?_
    have := Nat.ceil_lt_add_one (show 0 ≤ R by linarith)
    linarith

example : (0 : ℝ) / 1 ≤ 2 / (2 + 1) ∧ (0 : ℝ) ≤ 1 * (2 - 1) / (2 + 1) ∧
    ((2 : ℝ) = 2 → (0 : ℝ) = 2 → 6 ≤ (1 : ℝ)) := by
  have hsum : ∀ R : ℝ, 0 < R →
      ∑ v ∈ Finset.range ⌈R⌉₊, tau (fun _ : Sym2 ℕ => (0 : unitInterval)) 0 v = 1 := by
    intro R hR
    rw [Finset.sum_eq_single 0]
    · exact tau_self _ 0
    · intro b _ hb
      exact law_zero_profile_eq_zero fun h => hb ((empty_mem_conn_iff 0 b).mp h).symm
    · intro h
      exact (h (Finset.mem_range.mpr (Nat.ceil_pos.mpr hR))).elim
  refine hyperscaling_exponent_inequalities (fun _ : Sym2 ℕ => (0 : unitInterval))
    (C := 1) zero_le_one one_lt_two ?_ (fun R => Finset.range ⌈R⌉₊) ?_ 0 one_pos ?_
    tendsto_log_ceil_div_log ?_ ?_
  · intro x n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp only [Nat.cast_one, Real.one_rpow, mul_one, ENNReal.ofReal_one]
      exact prob_le_one
    · rw [law_zero_profile_eq_zero]
      · exact zero_le
      · intro hω
        have hω' : (n : ℕ∞) ≤ (cluster (∅ : Config ℕ) x).encard := hω
        rw [cluster_empty, Set.encard_singleton] at hω'
        have : n ≤ 1 := by exact_mod_cast hω'
        omega
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact ⟨0, Finset.mem_range.mpr (Nat.ceil_pos.mpr hR)⟩
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [hsum R hR]
    exact one_pos
  · refine ((tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [tightnessScale_zero_profile ⟨0, Finset.mem_range.mpr (Nat.ceil_pos.mpr hR)⟩]
    norm_num
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [hsum R hR]
    simp

end PercLib.Percolation.Bond
