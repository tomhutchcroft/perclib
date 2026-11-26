/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Source motivation: T. Hutchcroft, arXiv:2008.11197v2,
§2 (consequences of universal tightness), and the wiki statements LQ6Y, OB0A, WRHL and UVQ6. No
source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.WindowPartition
public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Percolation.Bond.ClusterMoments
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Finite-set hyperscaling

Fix a finite nonempty `Λ`, write `X_x = |K_x ∩ Λ|`, `Z = max_{x ∈ Λ} X_x` and
`M = tightnessScale q Λ`. The traces of the clusters on `Λ` are the image
`Λ.image fun x => Λ.filter (· ∈ cluster ω x)` (no new definition).

* `sum_function_clusterIntersection`: `∑_{x ∈ Λ} f(X_x) = ∑_D |D| f(|D|)` for every `f`.
* OB0A, `avg_lintegral_pow_clusterIntersection` and its window form: under a uniform root,
  `E X_U^m = |Λ|⁻¹ E ∑_D |D|^(m+1)`, under any measure on configurations.
* OB0A for real `m ≥ 0`, `lintegral_avg_rpow_clusterIntersection` and the window bounds
  `rpow_div_mul_lintegral_card_le_window`, `window_le_rpow_div_mul_lintegral_card` via the
  expected number `E N` of traces with size in `[a v, b v]`.
* LQ6Y, `lintegral_rpow_max_le_sum` and `le_lintegral_rpow_max`:
  `∑_{x ∈ Λ} E X_x^p ≥ E Z^(p+1) ≥ M^(p+1) / (e 2^(p+1))` for real `p ≥ 0`.
* `lintegral_clusterIntersection_le_of_tail`: a window tail `P(n ≤ X_u) ≤ A n^(-θ)`,
  `0 ≤ θ < 1`, and the rooted damping of `UniversalTightness` give
  `E X_u ≤ H_θ A M^(1-θ)` with `H_θ = (1-θ)⁻¹ + 9 e^(8/9)`.
* UVQ6, `tightnessScale_le_of_window_tail` and `sum_tau_le_of_window_tail`.
* WRHL, `tightnessScale_le_of_cluster_tail` and `avg_tau_le_of_cluster_tail`, for a
  cluster tail `P(n ≤ |K_x|) ≤ C n^(-1/δ)`, `δ > 1`, with `L = C (δ/(δ-1) + 9 e^(8/9))`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The partition identity for every function of the trace size -/

open Classical in
/-- `∑_{x ∈ Λ} f(|K_x ∩ Λ|) = ∑_D |D| • f(|D|)` over the traces `D` of clusters on `Λ`. -/
theorem sum_function_clusterIntersection {β : Type*} [AddCommMonoid β] (Λ : Finset V)
    (ω : Config V) (f : ℕ → β) :
    ∑ x ∈ Λ, f (clusterIntersection Λ ω x) =
      ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)), D.card • f D.card := by
  simp_rw [clusterIntersection_eq_card_filter]
  rw [Finset.sum_comp (fun D : Finset V => f D.card) (fun x => Λ.filter (· ∈ cluster ω x))]
  refine Finset.sum_congr rfl fun D hD => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hD
  have hfib : Λ.filter (fun a => Λ.filter (· ∈ cluster ω a) = Λ.filter (· ∈ cluster ω x)) =
      Λ.filter (· ∈ cluster ω x) :=
    Finset.filter_congr fun a ha => filter_cluster_eq_iff Λ ω ha
  rw [hfib]

open Classical in
/-- The expectation form: `∑_{x ∈ Λ} E f(X_x) = E ∑_D |D| f(|D|)`. -/
theorem sum_lintegral_function_clusterIntersection [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) (f : ℕ → ℝ≥0∞) :
    ∑ x ∈ Λ, ∫⁻ ω, f (clusterIntersection Λ ω x) ∂μ =
      ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) * f D.card ∂μ := by
  rw [← lintegral_finsetSum (f := fun x ω => f (clusterIntersection Λ ω x)) _
    fun x _ => measurable_from_nat.comp (measurable_clusterIntersection Λ x)]
  refine lintegral_congr fun ω => ?_
  rw [sum_function_clusterIntersection]
  simp only [nsmul_eq_mul]

/-! ### OB0A: moments under a uniform root -/

open Classical in
/-- **Sampled-root moments.** Under a uniform root `U` on `Λ` independent of `ω`,
`E X_U^m = |Λ|⁻¹ E ∑_D |D|^(m+1)`. -/
theorem avg_lintegral_pow_clusterIntersection [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) (m : ℕ) :
    (Λ.card : ℝ≥0∞)⁻¹ * ∑ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ^ m ∂μ =
      (Λ.card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) ^ (m + 1) ∂μ := by
  rw [sum_lintegral_function_clusterIntersection μ Λ fun n => (n : ℝ≥0∞) ^ m]
  simp only [pow_succ']

open Classical in
/-- **Window form.** For `a, b, v ∈ ℝ`, the moment restricted to the window
`a v ≤ X_U ≤ b v` is `|Λ|⁻¹ E ∑_{D : a v ≤ |D| ≤ b v} |D|^(m+1)`. -/
theorem avg_lintegral_pow_clusterIntersection_window [Countable V]
    (μ : Measure (Config V)) (Λ : Finset V) (m : ℕ) (a b v : ℝ) :
    (Λ.card : ℝ≥0∞)⁻¹ * ∑ x ∈ Λ, ∫⁻ ω,
        (if a * v ≤ (clusterIntersection Λ ω x : ℝ) ∧ (clusterIntersection Λ ω x : ℝ) ≤ b * v
          then (clusterIntersection Λ ω x : ℝ≥0∞) ^ m else 0) ∂μ =
      (Λ.card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
        (if a * v ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ b * v
          then (D.card : ℝ≥0∞) ^ (m + 1) else 0) ∂μ := by
  rw [sum_lintegral_function_clusterIntersection μ Λ fun n =>
    if a * v ≤ (n : ℝ) ∧ (n : ℝ) ≤ b * v then (n : ℝ≥0∞) ^ m else 0]
  congr 1
  refine lintegral_congr fun ω => Finset.sum_congr rfl fun D _ => ?_
  split_ifs <;> simp [pow_succ']

/-! ### LQ6Y: the partition bound and the quantile lower bound -/

open Classical in
/-- The largest trace is one of the traces. -/
theorem exists_trace_eq_max (Λ : Finset V) (hΛ : Λ.Nonempty) (ω : Config V) :
    ∃ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
      D.card = maxClusterIntersection Λ ω := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup Λ hΛ
    (fun v => (cluster ω v ∩ (Λ : Set V)).ncard)
  refine ⟨_, Finset.mem_image_of_mem _ hx, ?_⟩
  rw [maxClusterIntersection, hmax, ← clusterIntersection_eq_card_filter]
  rfl

/-- **First inequality.** `E Z^(p+1) ≤ ∑_{x ∈ Λ} E X_x^p` for real `p ≥ 0`. -/
theorem lintegral_rpow_max_le_sum [Countable V] (q : Sym2 V → unitInterval) {Λ : Finset V}
    (hΛ : Λ.Nonempty) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ (p + 1) ∂(law q) ≤
      ∑ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ^ p ∂(law q) := by
  rw [sum_lintegral_function_clusterIntersection (law q) Λ fun n => (n : ℝ≥0∞) ^ p]
  refine lintegral_mono fun ω => ?_
  obtain ⟨D, hD, hDc⟩ := exists_trace_eq_max Λ hΛ ω
  rw [← hDc, ENNReal.rpow_add_of_nonneg _ _ hp zero_le_one, ENNReal.rpow_one, mul_comm]
  exact Finset.single_le_sum (f := fun D : Finset V => (D.card : ℝ≥0∞) * (D.card : ℝ≥0∞) ^ p)
    (fun _ _ => bot_le) hD

/-- The largest intersection is measurable. -/
theorem measurable_maxClusterIntersection [Countable V] (Λ : Finset V) :
    Measurable (fun ω : Config V => maxClusterIntersection Λ ω) := by
  refine measurable_to_countable' fun n => ?_
  have h : (fun ω : Config V => maxClusterIntersection Λ ω) ⁻¹' {n} =
      {ω | n ≤ maxClusterIntersection Λ ω} \ {ω | n + 1 ≤ maxClusterIntersection Λ ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    omega
  rw [h]
  exact (measurableSet_le_maxClusterIntersection Λ n).diff
    (measurableSet_le_maxClusterIntersection Λ (n + 1))

/-- **Second inequality.** `M^(p+1) / (e 2^(p+1)) ≤ E Z^(p+1)` for real `p ≥ 0`. -/
theorem le_lintegral_rpow_max [Countable V] (q : Sym2 V → unitInterval) {Λ : Finset V}
    (hΛ : Λ.Nonempty) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ (p + 1) / (Real.exp 1 * 2 ^ (p + 1))) ≤
      ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ (p + 1) ∂(law q) := by
  set M := tightnessScale q Λ with hM
  have hM2 : 2 ≤ M := two_le_tightnessScale q hΛ
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmeas : Measurable fun ω : Config V => (maxClusterIntersection Λ ω : ℝ≥0∞) ^ (p + 1) :=
    (measurable_from_nat.comp (measurable_maxClusterIntersection Λ)).pow_const _
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := law q) hmeas.aemeasurable
    (((M - 1 : ℕ) : ℝ≥0∞) ^ (p + 1))
  have hsub : {ω : Config V | M - 1 ≤ maxClusterIntersection Λ ω} ⊆
      {ω | ((M - 1 : ℕ) : ℝ≥0∞) ^ (p + 1) ≤ (maxClusterIntersection Λ ω : ℝ≥0∞) ^ (p + 1)} :=
    fun ω hω => ENNReal.rpow_le_rpow (by exact_mod_cast hω) hp1
  have hstrict := lt_law_max_tail_of_lt_tightnessScale q Λ (show M - 1 < M by omega)
  refine le_trans ?_ (le_trans (mul_le_mul' le_rfl ((hstrict.le).trans (measure_mono hsub)))
    hmarkov)
  -- the real inequality `(M/2)^(p+1) / e ≤ (M-1)^(p+1) e⁻¹`
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hM1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by linarith
  have hcast : ((M - 1 : ℕ) : ℝ≥0∞) ^ (p + 1) = ENNReal.ofReal (((M : ℝ) - 1) ^ (p + 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hM1 hp1]
    congr 1
    rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub (by omega), ENNReal.ofReal_natCast]
  rw [hcast, ← ENNReal.ofReal_mul (Real.rpow_nonneg hM1 _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : (0 : ℝ) < 2 ^ (p + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : ((M : ℝ) / 2) ^ (p + 1) ≤ ((M : ℝ) - 1) ^ (p + 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hp1
  rw [Real.div_rpow (by positivity) (by norm_num)] at hhalf
  rw [Real.exp_neg, div_le_iff₀ (by positivity)]
  calc (M : ℝ) ^ (p + 1) = (M : ℝ) ^ (p + 1) / 2 ^ (p + 1) * 2 ^ (p + 1) := by
        field_simp
    _ ≤ ((M : ℝ) - 1) ^ (p + 1) * 2 ^ (p + 1) := by gcongr
    _ = ((M : ℝ) - 1) ^ (p + 1) * (Real.exp 1)⁻¹ * (Real.exp 1 * 2 ^ (p + 1)) := by
        field_simp

/-! ### Two real series bounds -/

/-- `(1-θ)(n+1)^(-θ) ≤ (n+1)^(1-θ) - n^(1-θ)` for `0 ≤ θ < 1`. -/
theorem one_sub_mul_rpow_neg_le (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) * ((n : ℝ) + 1) ^ (-θ) ≤ ((n : ℝ) + 1) ^ (1 - θ) - (n : ℝ) ^ (1 - θ) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have ha0 : 0 < a := by linarith
  have hbern := rpow_one_add_le_one_add_mul_self (s := -(1 / a))
    (by rw [neg_le_neg_iff, div_le_one ha0]; exact ha1) (p := 1 - θ) (by linarith)
    (by linarith)
  have hn : (n : ℝ) = (1 + -(1 / a)) * a := by rw [ha]; field_simp; ring
  have hnn : 0 ≤ 1 + -(1 / a) := by
    rw [← sub_eq_add_neg, sub_nonneg, div_le_one ha0]; exact ha1
  have hsplit : (n : ℝ) ^ (1 - θ) = (1 + -(1 / a)) ^ (1 - θ) * a ^ (1 - θ) := by
    rw [hn, Real.mul_rpow hnn ha0.le]
  have hpow : a ^ (-θ) = a ^ (1 - θ) / a := by
    rw [← Real.rpow_sub_one ha0.ne']; ring_nf
  rw [hsplit, hpow]
  have hap : 0 ≤ a ^ (1 - θ) := Real.rpow_nonneg ha0.le _
  calc (1 - θ) * (a ^ (1 - θ) / a) = a ^ (1 - θ) - (1 + (1 - θ) * -(1 / a)) * a ^ (1 - θ) := by
        field_simp; ring
    _ ≤ a ^ (1 - θ) - (1 + -(1 / a)) ^ (1 - θ) * a ^ (1 - θ) := by
        gcongr

/-- `∑_{n < M} (n+1)^(-θ) ≤ M^(1-θ) / (1-θ)` for `0 ≤ θ < 1`. -/
theorem sum_rpow_neg_le (M : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (-θ) ≤ (M : ℝ) ^ (1 - θ) / (1 - θ) := by
  have hs : 0 < 1 - θ := by linarith
  rw [le_div_iff₀ hs, Finset.sum_mul]
  have htel := Finset.sum_range_sub (fun i : ℕ => (i : ℝ) ^ (1 - θ)) M
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at htel
  rw [Real.zero_rpow hs.ne', sub_zero] at htel
  rw [← htel]
  exact Finset.sum_le_sum fun n _ => by
    rw [mul_comm]; exact one_sub_mul_rpow_neg_le n hθ0 hθ1

/-- `∑_{k < N} e^(-(k+1) x) ≤ 1/x` for `x > 0`. -/
theorem sum_exp_neg_le (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ∑ k ∈ Finset.range N, Real.exp (-(((k : ℝ) + 1) * x)) ≤ 1 / x := by
  set r := Real.exp (-x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hterm : ∀ k : ℕ, Real.exp (-(((k : ℝ) + 1) * x)) = r * r ^ k := by
    intro k
    rw [hr, ← pow_succ', ← Real.exp_nat_mul]; push_cast; ring_nf
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeom : (1 - r) * ∑ i ∈ Finset.range N, r ^ i ≤ 1 := by
    rw [mul_neg_geom_sum]; linarith [pow_pos hr0 N]
  have hsum : ∑ i ∈ Finset.range N, r ^ i ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ (by linarith), mul_comm]; exact hgeom
  have hexp : r * (1 + x) ≤ 1 := by
    have h := Real.add_one_le_exp x
    have : r * Real.exp x = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  calc r * ∑ i ∈ Finset.range N, r ^ i ≤ r * (1 / (1 - r)) := by gcongr
    _ ≤ 1 / x := by
        rw [mul_one_div, div_le_div_iff₀ (by linarith) hx]
        linarith

/-! ### The layer-cake formula for counts -/

/-- `E X = ∑_{n ≥ 0} P(n + 1 ≤ X)` for a measurable `ℕ`-valued `X`. -/
theorem lintegral_nat_eq_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → ℕ}
    (hX : Measurable X) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | n + 1 ≤ X ω} := by
  have hset : ∀ n : ℕ, MeasurableSet {ω | n + 1 ≤ X ω} := fun n =>
    hX (measurableSet_Ici (a := n + 1))
  have hpt : ∀ ω, (X ω : ℝ≥0∞) =
      ∑' n : ℕ, {ω | n + 1 ≤ X ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (X ω)) fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      exact Set.indicator_of_notMem (by simp only [Set.mem_ofPred_eq]; omega) _]
    rw [Finset.sum_congr rfl fun n hn => Set.indicator_of_mem
      (by simp only [Set.mem_ofPred_eq]; exact Finset.mem_range.1 hn) _]
    simp
  simp_rw [hpt]
  rw [lintegral_tsum fun n => (measurable_const.indicator (hset n)).aemeasurable]
  exact tsum_congr fun n => lintegral_indicator_one (hset n)

/-! ### The first moment of a window count from its tail -/

/-- **First moment from a window tail and rooted damping.** Let `M ≥ 1`. If
`P(n ≤ X_u) ≤ A n^(-θ)` for `n ≥ 1`, with `A ≥ 0` and `0 ≤ θ < 1`, and the rooted damping
`P(a M ≤ X_u) ≤ e · P(M ≤ X_u) · e^(-a/9)` holds for `a ≥ 1` (the third conjunct of
`UniversalTightness` at `M = tightnessScale q Λ`), then
`E X_u ≤ ((1-θ)⁻¹ + 9 e^(8/9)) A M^(1-θ)`. -/
theorem lintegral_clusterIntersection_le_of_tail [Countable V] (q : Sym2 V → unitInterval)
    (Λ : Finset V) (u : V) {M : ℕ} (hM : 1 ≤ M) {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (htail : ∀ n : ℕ, 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ)))
    (hdamp : ∀ a : ℝ, 1 ≤ a →
      law q {ω | a * (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp 1) * law q {ω | M ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9))) :
    ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) ≤
      ENNReal.ofReal (((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) * A * (M : ℝ) ^ (1 - θ)) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  set b : ℕ → ℝ := fun n => if n + 1 ≤ M then A * ((n : ℝ) + 1) ^ (-θ)
    else A * (M : ℝ) ^ (-θ) * Real.exp (1 - ((n : ℝ) + 1) / (9 * M)) with hbdef
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    simp only [hbdef]
    split_ifs
    · exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
    · exact mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hM0.le _)) (Real.exp_pos _).le
  have hb : ∀ n : ℕ, law q {ω | n + 1 ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (b n) := by
    intro n
    by_cases hn : n + 1 ≤ M
    · simp only [hbdef, hn, ↓reduceIte]
      have := htail (n + 1) (by omega)
      simpa using this
    · simp only [hbdef, hn, ↓reduceIte]
      set a : ℝ := ((n : ℝ) + 1) / M with ha
      have ha1 : 1 ≤ a := by
        rw [ha, le_div_iff₀ hM0, one_mul]
        have : (M : ℝ) < n + 1 := by exact_mod_cast (show M < n + 1 by omega)
        linarith
      have hev : {ω : Config V | n + 1 ≤ clusterIntersection Λ ω u} =
          {ω | a * (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} := by
        ext ω
        simp only [Set.mem_ofPred_eq, ha, div_mul_cancel₀ _ hM0.ne']
        constructor
        · intro h; exact_mod_cast h
        · intro h; exact_mod_cast h
      rw [hev]
      refine (hdamp a ha1).trans ?_
      have hMt := htail M hM
      calc ENNReal.ofReal (Real.exp 1) * law q {ω | M ≤ clusterIntersection Λ ω u} *
            ENNReal.ofReal (Real.exp (-a / 9))
          ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (A * (M : ℝ) ^ (-θ)) *
            ENNReal.ofReal (Real.exp (-a / 9)) := by gcongr
        _ = ENNReal.ofReal (A * (M : ℝ) ^ (-θ) * Real.exp (1 - ((n : ℝ) + 1) / (9 * M))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
              (mul_nonneg hA (Real.rpow_nonneg hM0.le _)))]
          congr 1
          rw [show 1 - ((n : ℝ) + 1) / (9 * M) = 1 + -a / 9 by rw [ha]; field_simp; ring,
            Real.exp_add]
          ring
  rw [lintegral_nat_eq_tsum _ (measurable_clusterIntersection Λ u)]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  refine (Finset.sum_le_sum fun n _ => hb n).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => hb0 n]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real estimate
  have hle : ∑ n ∈ Finset.range N, b n ≤ ∑ n ∈ Finset.range (M + N), b n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun n _ _ => hb0 n
  rw [Finset.sum_range_add] at hle
  have h1 : ∑ n ∈ Finset.range M, b n ≤ A * ((M : ℝ) ^ (1 - θ) / (1 - θ)) := by
    rw [Finset.sum_congr rfl fun n hn => show b n = A * ((n : ℝ) + 1) ^ (-θ) by
      simp only [hbdef, show n + 1 ≤ M by have := Finset.mem_range.1 hn; omega, ↓reduceIte],
      ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_rpow_neg_le M hθ0 hθ1) hA
  have h2 : ∑ k ∈ Finset.range N, b (M + k) ≤
      A * (M : ℝ) ^ (-θ) * Real.exp (8 / 9) * (9 * M) := by
    rw [Finset.sum_congr rfl fun k _ => show b (M + k) = A * (M : ℝ) ^ (-θ) * Real.exp (8 / 9) *
        Real.exp (-(((k : ℝ) + 1) * (1 / (9 * M)))) by
      simp only [hbdef, show ¬ M + k + 1 ≤ M by omega, ↓reduceIte]
      have he : Real.exp (1 - ((M + k : ℕ) + 1 : ℝ) / (9 * M)) =
          Real.exp (8 / 9) * Real.exp (-(((k : ℝ) + 1) * (1 / (9 * M)))) := by
        rw [← Real.exp_add]; congr 1; push_cast; field_simp; ring
      rw [he]; ring, ← Finset.mul_sum]
    have hc : 0 ≤ A * (M : ℝ) ^ (-θ) * Real.exp (8 / 9) :=
      mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hM0.le _)) (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ((sum_exp_neg_le N (by positivity)).trans_eq ?_) hc
    field_simp
  have hMpow : (M : ℝ) ^ (-θ) * M = (M : ℝ) ^ (1 - θ) := by
    rw [← Real.rpow_add_one hM0.ne', neg_add_eq_sub]
  have hs : 0 < 1 - θ := by linarith
  calc ∑ n ∈ Finset.range N, b n
      ≤ A * ((M : ℝ) ^ (1 - θ) / (1 - θ)) + A * (M : ℝ) ^ (-θ) * Real.exp (8 / 9) * (9 * M) :=
        hle.trans (add_le_add h1 h2)
    _ = ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) * A * ((M : ℝ) ^ (-θ) * M) := by
        rw [← hMpow]; field_simp
    _ = _ := by rw [hMpow]

/-- `E|K_u ∩ Λ| = ∑_{v ∈ Λ} τ(u, v)`. -/
theorem lintegral_clusterIntersection_eq_sum_tau [Countable V] (q : Sym2 V → unitInterval)
    (Λ : Finset V) (u : V) :
    ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) = ∑ v ∈ Λ, tau q u v := by
  have hpt : ∀ ω : Config V, (clusterIntersection Λ ω u : ℝ≥0∞) =
      ∑ v ∈ Λ, (conn u v).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [← encard_cluster_inter_finset_eq_sum, clusterIntersection,
      ← (Λ.finite_toSet.subset Set.inter_subset_right).cast_ncard_eq, ENat.toENNReal_coe]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun v _ => measurable_const.indicator (measurableSet_conn u v)]
  exact Finset.sum_congr rfl fun v _ => lintegral_indicator_one (measurableSet_conn u v)

/-! ### Hyperscaling bounds from a window tail and rooted damping -/

/-- The scale from a window tail: `M ≤ (4 e H_θ A |Λ|)^(1/(1+θ))`, where
`H_θ = (1-θ)⁻¹ + 9 e^(8/9)`, assuming `P(n ≤ X_u) ≤ A n^(-θ)` and rooted damping for
every root. -/
theorem tightnessScale_le_of_tail_damp [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ (u : V) (n : ℕ), 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ)))
    (hdamp : ∀ (u : V) (a : ℝ), 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp 1) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9))) :
    (tightnessScale q Λ : ℝ) ≤
      (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) * A * Λ.card) ^ (1 / (1 + θ)) := by
  set M := tightnessScale q Λ with hMdef
  set H : ℝ := (1 - θ)⁻¹ + 9 * Real.exp (8 / 9) with hH
  have hs : 0 < 1 - θ := by linarith
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hM2 : 2 ≤ M := two_le_tightnessScale q hΛ
  have hM0 : (0 : ℝ) < M := by have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
                               linarith
  have hX : ∀ u, ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) ≤
      ENNReal.ofReal (H * A * (M : ℝ) ^ (1 - θ)) := fun u =>
    lintegral_clusterIntersection_le_of_tail q Λ u (by omega) hA hθ0 hθ1 (htail u) (hdamp u)
  have h1 := le_lintegral_rpow_max q hΛ (p := 1) zero_le_one
  have h2 := lintegral_rpow_max_le_sum q hΛ (p := 1) zero_le_one
  have h3 : ∑ x ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω x : ℝ≥0∞) ^ (1 : ℝ) ∂(law q) ≤
      ENNReal.ofReal (Λ.card * (H * A * (M : ℝ) ^ (1 - θ))) := by
    simp_rw [ENNReal.rpow_one]
    refine (Finset.sum_le_sum fun x _ => hX x).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ((h1.trans h2).trans h3)
  have h4 : (2 : ℝ) ^ ((1 : ℝ) + 1) = 4 := by norm_num
  rw [h4] at hreal
  -- `M^(1+θ) ≤ 4 e H A |Λ|`
  have hsplit : (M : ℝ) ^ ((1 : ℝ) + 1) = (M : ℝ) ^ (1 + θ) * (M : ℝ) ^ (1 - θ) := by
    rw [← Real.rpow_add hM0]; ring_nf
  have hpos : 0 < (M : ℝ) ^ (1 - θ) := Real.rpow_pos_of_pos hM0 _
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hkey : (M : ℝ) ^ (1 + θ) ≤ 4 * Real.exp 1 * H * A * Λ.card := by
    rw [hsplit, div_le_iff₀ (by positivity)] at hreal
    have : (M : ℝ) ^ (1 + θ) * (M : ℝ) ^ (1 - θ) ≤
        (4 * Real.exp 1 * H * A * Λ.card) * (M : ℝ) ^ (1 - θ) := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  have hθ' : (1 + θ) ≠ 0 := by linarith
  calc (M : ℝ) = ((M : ℝ) ^ (1 + θ)) ^ (1 + θ)⁻¹ := (Real.rpow_rpow_inv hM0.le hθ').symm
    _ ≤ (4 * Real.exp 1 * H * A * Λ.card) ^ (1 / (1 + θ)) := by
        rw [one_div]
        exact Real.rpow_le_rpow (Real.rpow_nonneg hM0.le _) hkey (by positivity)

/-- The root sum from a window tail:
`∑_{v ∈ Λ} τ(u,v) ≤ H_θ (4 e H_θ)^((1-θ)/(1+θ)) A^(2/(1+θ)) |Λ|^((1-θ)/(1+θ))`. -/
theorem sum_tau_le_of_tail_damp [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ (u : V) (n : ℕ), 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ)))
    (hdamp : ∀ (u : V) (a : ℝ), 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp 1) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9)))
    (u : V) :
    ∑ v ∈ Λ, tau q u v ≤ ENNReal.ofReal (((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) *
      (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9))) ^ ((1 - θ) / (1 + θ)) *
      A ^ (2 / (1 + θ)) * (Λ.card : ℝ) ^ ((1 - θ) / (1 + θ))) := by
  set M := tightnessScale q Λ with hMdef
  set H : ℝ := (1 - θ)⁻¹ + 9 * Real.exp (8 / 9) with hH
  have hs : 0 < 1 - θ := by linarith
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hM2 : 2 ≤ M := two_le_tightnessScale q hΛ
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hMle := tightnessScale_le_of_tail_damp q hΛ hA hθ0 hθ1 htail hdamp
  rw [← lintegral_clusterIntersection_eq_sum_tau]
  refine (lintegral_clusterIntersection_le_of_tail q Λ u (by omega) hA hθ0 hθ1 (htail u)
    (hdamp u)).trans (ENNReal.ofReal_le_ofReal ?_)
  set c : ℝ := (1 - θ) / (1 + θ) with hc
  have hpow : (M : ℝ) ^ (1 - θ) ≤ (4 * Real.exp 1 * H * A * Λ.card) ^ c := by
    calc (M : ℝ) ^ (1 - θ) ≤ ((4 * Real.exp 1 * H * A * Λ.card) ^ (1 / (1 + θ))) ^ (1 - θ) :=
          Real.rpow_le_rpow hM0 hMle hs.le
      _ = _ := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; rw [hc]; ring
  have hsplit : (4 * Real.exp 1 * H * A * Λ.card) ^ c =
      (4 * Real.exp 1 * H) ^ c * A ^ c * (Λ.card : ℝ) ^ c := by
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _),
      Real.mul_rpow (by positivity) hA]
  have hA2 : A * A ^ c = A ^ (2 / (1 + θ)) := by
    have h : (1 : ℝ) + c = 2 / (1 + θ) := by rw [hc]; field_simp; ring
    rw [← h, Real.rpow_add' hA (by rw [h]; positivity), Real.rpow_one]
  calc H * A * (M : ℝ) ^ (1 - θ) ≤ H * A * (4 * Real.exp 1 * H * A * Λ.card) ^ c :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hH0 hA)
    _ = H * (4 * Real.exp 1 * H) ^ c * (A * A ^ c) * (Λ.card : ℝ) ^ c := by
        rw [hsplit]; ring
    _ = _ := by rw [hA2]

/-! ### UVQ6 -/

/-- **Scale.** By universal tightness, under a window tail
`P(n ≤ X_u) ≤ A n^(-θ)` (`0 ≤ θ < 1`, all `u`, `n ≥ 1`):
`M ≤ (4 e H_θ A |Λ|)^(1/(1+θ))`. -/
theorem tightnessScale_le_of_window_tail [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {A θ : ℝ} (hA : 0 ≤ A)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ (u : V) (n : ℕ), 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ))) :
    (tightnessScale q Λ : ℝ) ≤
      (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) * A * Λ.card) ^ (1 / (1 + θ)) :=
  tightnessScale_le_of_tail_damp q hΛ hA hθ0 hθ1 htail fun u _a ha =>
    law_mul_tightnessScale_le_clusterIntersection_le q hΛ u ha

/-- **Root sum.** Under the hypotheses of `tightnessScale_le_of_window_tail`,
`∑_{v ∈ Λ} τ(u,v) ≤ H_θ (4 e H_θ)^((1-θ)/(1+θ)) A^(2/(1+θ)) |Λ|^((1-θ)/(1+θ))`. -/
theorem sum_tau_le_of_window_tail [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {A θ : ℝ} (hA : 0 ≤ A)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ (u : V) (n : ℕ), 1 ≤ n →
      law q {ω | n ≤ clusterIntersection Λ ω u} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ)))
    (u : V) :
    ∑ v ∈ Λ, tau q u v ≤ ENNReal.ofReal (((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) *
      (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9))) ^ ((1 - θ) / (1 + θ)) *
      A ^ (2 / (1 + θ)) * (Λ.card : ℝ) ^ ((1 - θ) / (1 + θ))) :=
  sum_tau_le_of_tail_damp q hΛ hA hθ0 hθ1 htail (fun u _a ha =>
    law_mul_tightnessScale_le_clusterIntersection_le q hΛ u ha) u

/-! ### WRHL -/

/-- A cluster tail bounds every window tail. -/
theorem law_le_clusterIntersection_le_cluster (q : Sym2 V → unitInterval) (Λ : Finset V)
    (u : V) (n : ℕ) :
    law q {ω | n ≤ clusterIntersection Λ ω u} ≤ law q {ω | (n : ℕ∞) ≤ (cluster ω u).encard} := by
  refine measure_mono fun ω (hω : n ≤ clusterIntersection Λ ω u) => ?_
  change (n : ℕ∞) ≤ (cluster ω u).encard
  calc (n : ℕ∞) ≤ (clusterIntersection Λ ω u : ℕ∞) := by exact_mod_cast hω
    _ = (cluster ω u ∩ (Λ : Set V)).encard :=
        (Λ.finite_toSet.subset Set.inter_subset_right).cast_ncard_eq
    _ ≤ (cluster ω u).encard := Set.encard_le_encard Set.inter_subset_left

private theorem one_sub_inv_inv {δ : ℝ} (hδ : 1 < δ) : (1 - 1 / δ)⁻¹ = δ / (δ - 1) := by
  have : δ ≠ 0 := by linarith
  have : δ - 1 ≠ 0 := by linarith
  field_simp

/-- **Scale.** If `δ > 1`, `C ≥ 0`, `P(n ≤ |K_x|) ≤ C n^(-1/δ)` for all `x` and
`n ≥ 1`, and rooted damping holds for every root, then with
`L = C (δ/(δ-1) + 9 e^(8/9))`: `M ≤ (4 e L)^(δ/(δ+1)) |Λ|^(δ/(δ+1))`. -/
theorem tightnessScale_le_of_cluster_tail [Countable V] (q : Sym2 V → unitInterval)
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
        (Λ.card : ℝ) ^ (δ / (δ + 1)) := by
  have hδ0 : 0 < δ := by linarith
  have h := tightnessScale_le_of_tail_damp q hΛ hC (θ := 1 / δ) (by positivity)
    (by rw [div_lt_one hδ0]; exact hδ)
    (fun u n hn => (law_le_clusterIntersection_le_cluster q Λ u n).trans (hclus u n hn)) hdamp
  rw [one_sub_inv_inv hδ, show (1 : ℝ) / (1 + 1 / δ) = δ / (δ + 1) by field_simp,
    show 4 * Real.exp 1 * (δ / (δ - 1) + 9 * Real.exp (8 / 9)) * C * (Λ.card : ℝ) =
      4 * Real.exp 1 * (C * (δ / (δ - 1) + 9 * Real.exp (8 / 9))) * Λ.card by ring] at h
  have hH : 0 ≤ δ / (δ - 1) + 9 * Real.exp (8 / 9) := by
    have : 0 < δ - 1 := by linarith
    positivity
  rwa [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)] at h

/-- **Uniform-root two-point function.** Under the hypotheses of
`tightnessScale_le_of_cluster_tail`, for every `x`,
`|Λ|⁻¹ ∑_{v ∈ Λ} τ(x,v) ≤ L (4 e L)^((δ-1)/(δ+1)) |Λ|^(-2/(δ+1))`. -/
theorem avg_tau_le_of_cluster_tail [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 1 < δ)
    (hclus : ∀ (x : V) (n : ℕ), 1 ≤ n →
      law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / δ))))
    (hdamp : ∀ (u : V) (a : ℝ), 1 ≤ a →
      law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
        ENNReal.ofReal (Real.exp 1) *
          law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
          ENNReal.ofReal (Real.exp (-a / 9)))
    (x : V) :
    (Λ.card : ℝ≥0∞)⁻¹ * ∑ v ∈ Λ, tau q x v ≤
      ENNReal.ofReal (C * (δ / (δ - 1) + 9 * Real.exp (8 / 9)) *
        (4 * Real.exp 1 * (C * (δ / (δ - 1) + 9 * Real.exp (8 / 9)))) ^ ((δ - 1) / (δ + 1)) *
        (Λ.card : ℝ) ^ (-2 / (δ + 1))) := by
  have hδ0 : 0 < δ := by linarith
  have hδ1 : 0 < δ - 1 := by linarith
  set H : ℝ := δ / (δ - 1) + 9 * Real.exp (8 / 9) with hHdef
  have hH : 0 ≤ H := by rw [hHdef]; positivity
  have hcard : (0 : ℝ) < Λ.card := by exact_mod_cast hΛ.card_pos
  have h := sum_tau_le_of_tail_damp q hΛ hC (θ := 1 / δ) (by positivity)
    (by rw [div_lt_one hδ0]; exact hδ)
    (fun u n hn => (law_le_clusterIntersection_le_cluster q Λ u n).trans (hclus u n hn))
    hdamp x
  set c : ℝ := (δ - 1) / (δ + 1) with hc
  rw [one_sub_inv_inv hδ, show (1 - 1 / δ) / (1 + 1 / δ) = c by rw [hc]; field_simp,
    show (2 : ℝ) / (1 + 1 / δ) = 1 + c by rw [hc]; field_simp; ring] at h
  rw [← hHdef] at h
  have hinv : (Λ.card : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Λ.card : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast]
  rw [hinv]
  refine (mul_le_mul' le_rfl h).trans ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hcard.le)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  have e1 : (4 * Real.exp 1 * (C * H)) ^ c = (4 * Real.exp 1 * H) ^ c * C ^ c := by
    rw [show 4 * Real.exp 1 * (C * H) = (4 * Real.exp 1 * H) * C by ring,
      Real.mul_rpow (by positivity) hC]
  have hcpos : 0 < c := by rw [hc]; exact div_pos hδ1 (by linarith)
  have hc1 : (1 : ℝ) + c ≠ 0 := by linarith
  have e2 : C ^ (1 + c) = C * C ^ c := by rw [Real.rpow_add' hC hc1, Real.rpow_one]
  have hce : c = 1 + -2 / (δ + 1) := by rw [hc]; field_simp; ring
  have e3 : (Λ.card : ℝ) ^ c = Λ.card * (Λ.card : ℝ) ^ (-2 / (δ + 1)) := by
    rw [hce, Real.rpow_add' (Nat.cast_nonneg _) (by rw [← hce]; exact hcpos.ne'),
      Real.rpow_one]
  rw [e1, e2, e3]
  field_simp

/-! ### Non-vacuity -/

/-- On `Unit` every cluster is the single vertex. -/
theorem encard_cluster_unit (ω : Config Unit) (x : Unit) : (cluster ω x).encard = 1 := by
  rw [show cluster ω x = {x} from
    Set.eq_singleton_iff_unique_mem.2 ⟨mem_cluster_self _ _, fun _ _ => Subsingleton.elim _ _⟩,
    Set.encard_singleton]

theorem clusterIntersection_unit (ω : Config Unit) (u : Unit) :
    clusterIntersection {()} ω u = 1 := by
  rw [clusterIntersection_eq_card_filter]
  simp [Subsingleton.elim u (), mem_cluster_self]

/-- The cluster tail of `finite_set_hyperscaling` with `C = 1`, `δ = 2` holds on `Unit`. -/
theorem cluster_tail_unit (q : Sym2 Unit → unitInterval) (x : Unit) (n : ℕ) (hn : 1 ≤ n) :
    law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} ≤
      ENNReal.ofReal (1 * (n : ℝ) ^ (-(1 / (2 : ℝ)))) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp only [Nat.cast_one, Real.one_rpow, mul_one, ENNReal.ofReal_one]
    exact prob_le_one
  · have hempty : {ω : Config Unit | (n : ℕ∞) ≤ (cluster ω x).encard} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, encard_cluster_unit]
      exact_mod_cast h
    rw [hempty, measure_empty]
    exact zero_le

/-- Rooted damping holds on `Unit` with `Λ = {()}`: the window count is one and `M = 2`. -/
theorem damp_unit (q : Sym2 Unit → unitInterval) (u : Unit) (a : ℝ) (ha : 1 ≤ a) :
    law q {ω | a * (tightnessScale q {()} : ℝ) ≤ (clusterIntersection {()} ω u : ℝ)} ≤
      ENNReal.ofReal (Real.exp 1) *
        law q {ω | tightnessScale q {()} ≤ clusterIntersection {()} ω u} *
        ENNReal.ofReal (Real.exp (-a / 9)) := by
  have hempty : {ω : Config Unit |
      a * (tightnessScale q {()} : ℝ) ≤ (clusterIntersection {()} ω u : ℝ)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le,
      tightnessScale_singleton, clusterIntersection_unit]
    push_cast
    linarith
  rw [hempty, measure_empty]
  exact zero_le

/-- `finite_set_hyperscaling` with all hypotheses satisfied: `Unit`, `Λ = {()}`, `C = 1`, `δ = 2`.
-/
example (q : Sym2 Unit → unitInterval) :
    (tightnessScale q {()} : ℝ) ≤
      (4 * Real.exp 1 * (1 * (2 / (2 - 1) + 9 * Real.exp (8 / 9)))) ^ ((2 : ℝ) / (2 + 1)) *
        (({()} : Finset Unit).card : ℝ) ^ ((2 : ℝ) / (2 + 1)) :=
  tightnessScale_le_of_cluster_tail q (Finset.singleton_nonempty _) zero_le_one
    (by norm_num) (cluster_tail_unit q) (damp_unit q)

example (q : Sym2 Unit → unitInterval) :
    (({()} : Finset Unit).card : ℝ≥0∞)⁻¹ * ∑ v ∈ ({()} : Finset Unit), tau q () v ≤
      ENNReal.ofReal (1 * (2 / (2 - 1) + 9 * Real.exp (8 / 9)) *
        (4 * Real.exp 1 * (1 * (2 / (2 - 1) + 9 * Real.exp (8 / 9)))) ^ (((2 : ℝ) - 1) / (2 + 1)) *
        (({()} : Finset Unit).card : ℝ) ^ (-2 / ((2 : ℝ) + 1))) :=
  avg_tau_le_of_cluster_tail q (Finset.singleton_nonempty _) zero_le_one (by norm_num)
    (cluster_tail_unit q) (damp_unit q) ()

/-- `finite_window_hyperscaling` with all hypotheses satisfied: `Unit`, `A = 1`, `θ = 0`. -/
example (q : Sym2 Unit → unitInterval) :
    (tightnessScale q {()} : ℝ) ≤
      (4 * Real.exp 1 * ((1 - 0)⁻¹ + 9 * Real.exp (8 / 9)) * 1 *
        ({()} : Finset Unit).card) ^ (1 / (1 + (0 : ℝ))) :=
  tightnessScale_le_of_window_tail q (Finset.singleton_nonempty _)
    zero_le_one le_rfl zero_lt_one fun u n hn =>
      (law_le_clusterIntersection_le_cluster q _ u n).trans ((cluster_tail_unit q u n hn).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
          zero_le_one)))

/-- The lower rooted moments and `avg_lintegral_pow_clusterIntersection` on a singleton window,
where `M = 2` and every count is one. -/
example (q : Sym2 Unit → unitInterval) :
    ENNReal.ofReal (2 ^ ((1 : ℝ) + 1) / (Real.exp 1 * 2 ^ ((1 : ℝ) + 1))) ≤
      ∑ x ∈ ({()} : Finset Unit),
        ∫⁻ ω, (clusterIntersection {()} ω x : ℝ≥0∞) ^ (1 : ℝ) ∂(law q) := by
  have h := (le_lintegral_rpow_max q (Finset.singleton_nonempty ()) zero_le_one).trans
    (lintegral_rpow_max_le_sum q (Finset.singleton_nonempty ()) zero_le_one)
  rwa [tightnessScale_singleton, Nat.cast_ofNat] at h

open Classical in
example (q : Sym2 Unit → unitInterval) (m : ℕ) :
    (({()} : Finset Unit).card : ℝ≥0∞)⁻¹ *
        ∑ x ∈ ({()} : Finset Unit), ∫⁻ ω, (clusterIntersection {()} ω x : ℝ≥0∞) ^ m ∂(law q) =
      (({()} : Finset Unit).card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ ({()} : Finset Unit).image
        (fun x => ({()} : Finset Unit).filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) ^ (m + 1) ∂(law q) :=
  avg_lintegral_pow_clusterIntersection (law q) {()} m


/-! ### OB0A for real exponents, inside the expectation -/

open Classical in
/-- **Sampled-root expectation of a trace functional.** With `U` uniform on `Λ` and
independent of `ω`, written as the average over `u ∈ Λ` inside the expectation,
`E f(X_U) = |Λ|⁻¹ E ∑_D |D| f(|D|)` under any measure on configurations. -/
theorem lintegral_avg_function_clusterIntersection [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) (f : ℕ → ℝ≥0∞) :
    ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ, f (clusterIntersection Λ ω u) ∂μ =
      (Λ.card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) * f D.card ∂μ := by
  have hm : Measurable fun ω : Config V => ∑ u ∈ Λ, f (clusterIntersection Λ ω u) :=
    Finset.measurable_sum Λ fun u _ =>
      measurable_from_nat.comp (measurable_clusterIntersection Λ u)
  rw [lintegral_const_mul _ hm]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [sum_function_clusterIntersection]
  simp only [nsmul_eq_mul]

/-- `n · n^m = n^(m+1)` in `ℝ≥0∞` for real `m ≥ 0`. -/
theorem mul_rpow_eq_rpow_add_one (x : ℝ≥0∞) {m : ℝ} (hm : 0 ≤ m) :
    x * x ^ m = x ^ (m + 1) := by
  rw [ENNReal.rpow_add_of_nonneg _ _ hm zero_le_one, ENNReal.rpow_one, mul_comm]

open Classical in
/-- **Sampled-root moments, real exponent.** For real `m ≥ 0` and `U` uniform on `Λ`
independent of `ω`, `E X_U^m = |Λ|⁻¹ E ∑_D |D|^(m+1)`, under any measure on configurations. -/
theorem lintegral_avg_rpow_clusterIntersection [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) {m : ℝ} (hm : 0 ≤ m) :
    ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ, (clusterIntersection Λ ω u : ℝ≥0∞) ^ m ∂μ =
      (Λ.card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
        (D.card : ℝ≥0∞) ^ (m + 1) ∂μ := by
  rw [lintegral_avg_function_clusterIntersection μ Λ fun n => (n : ℝ≥0∞) ^ m]
  simp only [mul_rpow_eq_rpow_add_one _ hm]

open Classical in
/-- **Window form, real exponent.** For real `m ≥ 0` and `a, b, v ∈ ℝ`,
`E[X_U^m 1{a v ≤ X_U ≤ b v}] = |Λ|⁻¹ E ∑_{D : a v ≤ |D| ≤ b v} |D|^(m+1)`. -/
theorem lintegral_avg_rpow_clusterIntersection_window [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) {m : ℝ} (hm : 0 ≤ m) (a b v : ℝ) :
    ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ,
        (if a * v ≤ (clusterIntersection Λ ω u : ℝ) ∧ (clusterIntersection Λ ω u : ℝ) ≤ b * v
          then (clusterIntersection Λ ω u : ℝ≥0∞) ^ m else 0) ∂μ =
      (Λ.card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
        (if a * v ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ b * v
          then (D.card : ℝ≥0∞) ^ (m + 1) else 0) ∂μ := by
  rw [lintegral_avg_function_clusterIntersection μ Λ fun n =>
    if a * v ≤ (n : ℝ) ∧ (n : ℝ) ≤ b * v then (n : ℝ≥0∞) ^ m else 0]
  congr 1
  refine lintegral_congr fun ω => Finset.sum_congr rfl fun D _ => ?_
  split_ifs <;> simp [mul_rpow_eq_rpow_add_one _ hm]

open Classical in
/-- `c · #{D : P D} = ∑_D (if P D then c else 0)` for the traces of clusters on `Λ`. -/
theorem mul_card_filter_image_eq_sum_ite (Λ : Finset V) (ω : Config V) (P : Finset V → Prop)
    [DecidablePred P] (c : ℝ≥0∞) :
    c * (((Λ.image fun x => Λ.filter (· ∈ cluster ω x)).filter P).card : ℝ≥0∞) =
      ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)), if P D then c else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

open Classical in
/-- **Lower window bound.** For real `m ≥ 0`, with `N` the number of traces of size in
`[a v, b v]`, `(a v)^(m+1) / |Λ| · E N ≤ E[X_U^m 1{a v ≤ X_U ≤ b v}]`. -/
theorem rpow_div_mul_lintegral_card_le_window [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) {m : ℝ} (hm : 0 ≤ m) (a b v : ℝ) :
    ENNReal.ofReal (a * v) ^ (m + 1) / Λ.card *
        ∫⁻ ω, (((Λ.image fun x => Λ.filter (· ∈ cluster ω x)).filter
          fun D => a * v ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ b * v).card : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ,
        (if a * v ≤ (clusterIntersection Λ ω u : ℝ) ∧ (clusterIntersection Λ ω u : ℝ) ≤ b * v
          then (clusterIntersection Λ ω u : ℝ≥0∞) ^ m else 0) ∂μ := by
  have hc : ENNReal.ofReal (a * v) ^ (m + 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  rw [lintegral_avg_rpow_clusterIntersection_window μ Λ hm, ENNReal.div_eq_inv_mul, mul_assoc,
    ← lintegral_const_mul' _ _ hc]
  refine mul_le_mul' le_rfl (lintegral_mono fun ω => ?_)
  rw [mul_card_filter_image_eq_sum_ite]
  refine Finset.sum_le_sum fun D _ => ?_
  split_ifs with h
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h.1) (by linarith)
  · exact le_rfl

open Classical in
/-- **Upper window bound.** For real `m ≥ 0`, with `N` the number of traces of size in
`[a v, b v]`, `E[X_U^m 1{a v ≤ X_U ≤ b v}] ≤ (b v)^(m+1) / |Λ| · E N`. -/
theorem window_le_rpow_div_mul_lintegral_card [Countable V] (μ : Measure (Config V))
    (Λ : Finset V) {m : ℝ} (hm : 0 ≤ m) (a b v : ℝ) :
    ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ,
        (if a * v ≤ (clusterIntersection Λ ω u : ℝ) ∧ (clusterIntersection Λ ω u : ℝ) ≤ b * v
          then (clusterIntersection Λ ω u : ℝ≥0∞) ^ m else 0) ∂μ ≤
      ENNReal.ofReal (b * v) ^ (m + 1) / Λ.card *
        ∫⁻ ω, (((Λ.image fun x => Λ.filter (· ∈ cluster ω x)).filter
          fun D => a * v ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ b * v).card : ℝ≥0∞) ∂μ := by
  have hc : ENNReal.ofReal (b * v) ^ (m + 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  rw [lintegral_avg_rpow_clusterIntersection_window μ Λ hm, ENNReal.div_eq_inv_mul, mul_assoc,
    ← lintegral_const_mul' _ _ hc]
  refine mul_le_mul' le_rfl (lintegral_mono fun ω => ?_)
  rw [mul_card_filter_image_eq_sum_ite]
  refine Finset.sum_le_sum fun D _ => ?_
  split_ifs with h
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h.2) (by linarith)
  · exact le_rfl

end PercLib.Percolation.Bond
