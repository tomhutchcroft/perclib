/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: truncated means of the cluster intersection from universal
tightness. From the tightness theorems of this library and pinned mathlib's Markov inequality and
exponential bounds. No upstream code is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Percolation.Bond.Tightness.Hyperscaling
public import PercLib.Percolation.Bond.Transport

/-! # Truncated window means from rooted tightness (R7)

Fix a countable `V`, a profile `q`, a finite nonempty `Λ` and a root `u`. Write
`X_u = clusterIntersection Λ ω u = |K_u ∩ Λ|`, `M = tightnessScale q Λ` and
`μ_u = ∫⁻ X_u ∂(law q)`.

* `exp_neg_ten_div_le_half` (item 1): `e^{-10} / (M (1 - e^{-1/(9M)})) ≤ 1/2` for `M ≥ 2`.
* `lintegral_clusterIntersection_div_two_le` (item 2, R7):
  `μ_u / 2 ≤ ∫⁻ min(X_u, 99 M)`. The excess `E[(X_u - 99M)_+] = ∑_k P(X_u ≥ 99M + k + 1)` is
  bounded term by term by the rooted bound of `universalTightness`, then by Markov's
  inequality `M P(X_u ≥ M) ≤ μ_u`; in total it is at most `9 e^{-10} μ_u ≤ μ_u / 2`.
* `lintegral_clusterIntersection_min_ge` (item 3): `(1/2) min(1, t/(99M)) μ_u ≤ ∫⁻ min(X_u, t)`.
* `le_sum_lintegral_clusterIntersection` and
  `le_card_mul_lintegral_clusterIntersection_of_transitive` (item 4, R1 averaged):
  `M² / (4e) ≤ ∑_{v ∈ Λ} μ_v`, and `M²/(4e) ≤ |Λ| μ_o` when automorphisms of the law
  preserving `Λ` act transitively on `Λ`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Item 1: the scalar lemma -/

/-- `e^{-10} ≤ 1/61`. -/
theorem exp_neg_ten_le : Real.exp (-10) ≤ 1 / 61 := by
  rw [Real.exp_neg, inv_eq_one_div]
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- **Item 1.** For every integer `M ≥ 2`, `e^{-10} / (M (1 - e^{-1/(9M)})) ≤ 1/2`. -/
theorem exp_neg_ten_div_le_half {M : ℕ} (hM : 2 ≤ M) :
    Real.exp (-10) / (M * (1 - Real.exp (-1 / (9 * M)))) ≤ 1 / 2 := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have he : Real.exp (-1 / (9 * M)) ≤ (1 + 1 / (9 * (M : ℝ)))⁻¹ := by
    rw [neg_div, Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (9 * (M : ℝ)))])
  have hid : (M : ℝ) * (1 - (1 + 1 / (9 * (M : ℝ)))⁻¹) = M / (9 * M + 1) := by
    field_simp
    ring
  have hD : 1 / 10 ≤ (M : ℝ) * (1 - Real.exp (-1 / (9 * M))) := by
    calc (1 : ℝ) / 10 ≤ M / (9 * M + 1) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          linarith
      _ = M * (1 - (1 + 1 / (9 * (M : ℝ)))⁻¹) := hid.symm
      _ ≤ M * (1 - Real.exp (-1 / (9 * M))) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left he 1) hM0.le
  rw [div_le_iff₀ (by linarith)]
  linarith [exp_neg_ten_le]

/-! ### Item 2: R7 -/

/-- The cluster intersection is at most `|Λ|`. -/
theorem clusterIntersection_le_card (Λ : Finset V) (ω : Config V) (u : V) :
    clusterIntersection Λ ω u ≤ Λ.card := by
  classical
  rw [clusterIntersection_eq_card_filter]
  exact Finset.card_filter_le _ _

/-- The mean of the cluster intersection is finite. -/
theorem lintegral_clusterIntersection_ne_top (q : Sym2 V → unitInterval) (Λ : Finset V)
    (u : V) : ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top Λ.card) ?_
  calc ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) ≤ ∫⁻ _, (Λ.card : ℝ≥0∞) ∂(law q) :=
        lintegral_mono fun ω => Nat.cast_le.2 (clusterIntersection_le_card Λ ω u)
    _ = Λ.card := by simp

/-- **R7.** Truncating the cluster intersection at `99 M` keeps half of its mean:
`μ_u / 2 ≤ ∫⁻ min(X_u, 99 M)`. -/
theorem lintegral_clusterIntersection_div_two_le [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) :
    (∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q)) / 2 ≤
      ∫⁻ ω, min (clusterIntersection Λ ω u : ℝ≥0∞)
        ((99 * tightnessScale q Λ : ℕ) : ℝ≥0∞) ∂(law q) := by
  set M := tightnessScale q Λ with hM
  set X : Config V → ℕ := fun ω => clusterIntersection Λ ω u with hX
  have hXm : Measurable X := measurable_clusterIntersection Λ u
  have hM2 : 2 ≤ M := two_le_tightnessScale q hΛ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set μ := ∫⁻ ω, (X ω : ℝ≥0∞) ∂(law q) with hμ
  have hμt : μ ≠ ⊤ := lintegral_clusterIntersection_ne_top q Λ u
  -- `μ` is the truncated mean plus the excess.
  have hdec : μ = ∫⁻ ω, min (X ω : ℝ≥0∞) ((99 * M : ℕ) : ℝ≥0∞) ∂(law q) +
      ∫⁻ ω, ((X ω - 99 * M : ℕ) : ℝ≥0∞) ∂(law q) := by
    have hm1 : Measurable fun ω => min (X ω : ℝ≥0∞) ((99 * M : ℕ) : ℝ≥0∞) :=
      (Measurable.of_discrete (f := fun n : ℕ => min (n : ℝ≥0∞) ((99 * M : ℕ) : ℝ≥0∞))).comp hXm
    rw [← lintegral_add_left hm1]
    refine lintegral_congr fun ω => ?_
    rcases le_total (X ω) (99 * M) with h | h
    · rw [min_eq_left (Nat.cast_le.2 h), Nat.sub_eq_zero_of_le h, Nat.cast_zero, add_zero]
    · rw [min_eq_right (Nat.cast_le.2 h), ← Nat.cast_add, Nat.add_sub_cancel' h]
  -- The excess as a tail sum, bounded term by term.
  have hterm : ∀ k : ℕ, law q {ω | k + 1 ≤ X ω - 99 * M} ≤
      ENNReal.ofReal (Real.exp 1) * law q {ω | M ≤ X ω} *
        (ENNReal.ofReal (Real.exp (-11)) *
          ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * (1 / (9 * M)))))) := by
    intro k
    set a : ℝ := ((99 * M + k + 1 : ℕ) : ℝ) / M with ha
    have ha1 : 1 ≤ a := by
      rw [ha, le_div_iff₀ hM0, one_mul]
      exact_mod_cast (show M ≤ 99 * M + k + 1 by omega)
    have h := (universalTightness V q Λ hΛ).2.2 u a ha1
    have hset : {ω | k + 1 ≤ X ω - 99 * M} =
        {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} := by
      ext ω
      simp only [mem_ofPred_eq, ha, ← hM, div_mul_cancel₀ _ hM0.ne', hX]
      rw [Nat.cast_le]
      omega
    have hexp : Real.exp (-a / 9) =
        Real.exp (-11) * Real.exp (-(((k : ℝ) + 1) * (1 / (9 * M)))) := by
      rw [← Real.exp_add]
      congr 1
      rw [ha]
      push_cast
      field_simp
      ring
    rw [hset, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hexp]
    exact h
  have htail : ∫⁻ ω, ((X ω - 99 * M : ℕ) : ℝ≥0∞) ∂(law q) ≤
      ENNReal.ofReal (Real.exp 1) * law q {ω | M ≤ X ω} *
        (ENNReal.ofReal (Real.exp (-11)) * ENNReal.ofReal (9 * M)) := by
    have hm2 : Measurable fun ω => X ω - 99 * M :=
      (Measurable.of_discrete (f := fun n : ℕ => n - 99 * M)).comp hXm
    rw [lintegral_nat_eq_tsum _ hm2]
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ((sum_exp_neg_le n (by positivity)).trans ?_)
    rw [one_div_one_div]
  -- Markov.
  have hmarkov : (M : ℝ≥0∞) * law q {ω | M ≤ X ω} ≤ μ := by
    have h := mul_meas_ge_le_lintegral₀ (μ := law q)
      ((Measurable.of_discrete (f := fun n : ℕ => (n : ℝ≥0∞))).comp hXm).aemeasurable (M : ℝ≥0∞)
    have hs : {ω | (M : ℝ≥0∞) ≤ (X ω : ℝ≥0∞)} = {ω | M ≤ X ω} := by
      ext ω
      simp only [mem_ofPred_eq, Nat.cast_le]
    simp only [Function.comp_def] at h
    rwa [hs] at h
  have hc : ENNReal.ofReal (9 * Real.exp (-10)) ≤ 2⁻¹ := by
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ by
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [exp_neg_ten_le]
  have hexcess : ∫⁻ ω, ((X ω - 99 * M : ℕ) : ℝ≥0∞) ∂(law q) ≤ μ / 2 := by
    refine htail.trans ?_
    calc ENNReal.ofReal (Real.exp 1) * law q {ω | M ≤ X ω} *
          (ENNReal.ofReal (Real.exp (-11)) * ENNReal.ofReal (9 * M))
        = ENNReal.ofReal (9 * Real.exp (-10)) * ((M : ℝ≥0∞) * law q {ω | M ≤ X ω}) := by
          have he : Real.exp 1 * Real.exp (-11) = Real.exp (-10) := by
            rw [← Real.exp_add]
            norm_num
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast,
            ENNReal.ofReal_mul (by norm_num), ← he,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ 2⁻¹ * μ := mul_le_mul' hc hmarkov
      _ = μ / 2 := by rw [div_eq_mul_inv, mul_comm]
  -- Conclude.
  have hhalf : μ / 2 ≠ ⊤ := ENNReal.div_ne_top hμt (by norm_num)
  refine ENNReal.le_of_add_le_add_right hhalf ?_
  calc μ / 2 + μ / 2 = μ := ENNReal.add_halves μ
    _ = _ := hdec
    _ ≤ _ := add_le_add le_rfl hexcess

/-! ### Item 3: truncation at any level -/

/-- **Truncation at any level.** For every `t`,
`(1/2) min(1, t / (99 M)) μ_u ≤ ∫⁻ min(X_u, t)`. -/
theorem lintegral_clusterIntersection_min_ge [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) (t : ℝ≥0∞) :
    2⁻¹ * min 1 (t / ((99 * tightnessScale q Λ : ℕ) : ℝ≥0∞)) *
        ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) ≤
      ∫⁻ ω, min (clusterIntersection Λ ω u : ℝ≥0∞) t ∂(law q) := by
  set T : ℝ≥0∞ := ((99 * tightnessScale q Λ : ℕ) : ℝ≥0∞)
  have hT0 : T ≠ 0 := by
    have := two_le_tightnessScale q hΛ
    simp only [T, ne_eq, Nat.cast_eq_zero]
    omega
  have hTt : T ≠ ⊤ := ENNReal.natCast_ne_top _
  set c := min 1 (t / T)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcT : c * T ≤ t :=
    (mul_le_mul' (min_le_right _ _) le_rfl).trans (ENNReal.div_mul_cancel hT0 hTt).le
  calc 2⁻¹ * c * ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q)
      = c * ((∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q)) / 2) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ c * ∫⁻ ω, min (clusterIntersection Λ ω u : ℝ≥0∞) T ∂(law q) :=
        mul_le_mul' le_rfl (lintegral_clusterIntersection_div_two_le q hΛ u)
    _ = ∫⁻ ω, c * min (clusterIntersection Λ ω u : ℝ≥0∞) T ∂(law q) :=
        (lintegral_const_mul' c _ (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)).symm
    _ ≤ _ := lintegral_mono fun ω => by
        refine le_min ?_ ?_
        · exact (mul_le_mul' hc1 (min_le_left _ _)).trans (one_mul _).le
        · exact (mul_le_mul' le_rfl (min_le_right _ _)).trans hcT

/-! ### Item 4: R1, averaged form -/

/-- **R1, averaged.** `M² / (4e) ≤ ∑_{v ∈ Λ} ∫⁻ X_v` (the `p = 1` case of the lower rooted moments).
-/
theorem le_sum_lintegral_clusterIntersection [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) :
    ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ 2 / (4 * Real.exp 1)) ≤
      ∑ v ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω v : ℝ≥0∞) ∂(law q) := by
  have h1 := le_lintegral_rpow_max q hΛ (p := 1) zero_le_one
  have h2 := lintegral_rpow_max_le_sum q hΛ (p := 1) zero_le_one
  simp only [ENNReal.rpow_one] at h2
  have e : (tightnessScale q Λ : ℝ) ^ ((1 : ℝ) + 1) / (Real.exp 1 * 2 ^ ((1 : ℝ) + 1)) =
      (tightnessScale q Λ : ℝ) ^ 2 / (4 * Real.exp 1) := by
    rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [e] at h1
  exact h1.trans h2

/-- Cluster intersections are carried along a bijection preserving `Λ`. -/
theorem clusterIntersection_image (Λ : Finset V) (σ : V ≃ V) (hσ : ∀ w, σ w ∈ Λ ↔ w ∈ Λ)
    (ω : Config V) (x : V) :
    clusterIntersection Λ (Sym2.map σ '' ω) (σ x) = clusterIntersection Λ ω x := by
  have hpre : σ ⁻¹' (Λ : Set V) = Λ := by
    ext w
    exact hσ w
  rw [clusterIntersection, cluster_image, ← Set.image_inter_preimage, hpre,
    Set.ncard_image_of_injective _ σ.injective]
  rfl

/-- **R1 under transitivity.** If for every `v ∈ Λ` some bijection preserving the law and
`Λ` maps `o` to `v`, then `M² / (4e) ≤ |Λ| ∫⁻ X_o`. -/
theorem le_card_mul_lintegral_clusterIntersection_of_transitive [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (o : V)
    (hT : ∀ v ∈ Λ, ∃ σ : V ≃ V, σ o = v ∧
      (law q).map (fun ω => Sym2.map σ '' ω) = law q ∧ ∀ w, σ w ∈ Λ ↔ w ∈ Λ) :
    ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ 2 / (4 * Real.exp 1)) ≤
      Λ.card * ∫⁻ ω, (clusterIntersection Λ ω o : ℝ≥0∞) ∂(law q) := by
  have hv : ∀ v ∈ Λ, ∫⁻ ω, (clusterIntersection Λ ω v : ℝ≥0∞) ∂(law q) =
      ∫⁻ ω, (clusterIntersection Λ ω o : ℝ≥0∞) ∂(law q) := by
    intro v hvΛ
    obtain ⟨σ, hσo, hlaw, hσΛ⟩ := hT v hvΛ
    conv_lhs => rw [← hlaw, ← hσo]
    rw [lintegral_map_image_sym2Map]
    simp_rw [clusterIntersection_image Λ σ hσΛ]
  rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_congr rfl hv]
  exact le_sum_lintegral_clusterIntersection q hΛ

/-! ### Non-vacuity: `Λ = {v}`, `M = 2`, `X_v = 1` -/

/-- With `Λ = {v}`, the cluster intersection is one, the scale is two, and item 2 reads
`1/2 ≤ 1`. -/
example (q : Sym2 ℕ → unitInterval) :
    (∫⁻ ω, (clusterIntersection {0} ω 0 : ℝ≥0∞) ∂(law q)) / 2 ≤
      ∫⁻ ω, min (clusterIntersection {0} ω 0 : ℝ≥0∞)
        ((99 * tightnessScale q {0} : ℕ) : ℝ≥0∞) ∂(law q) ∧
      tightnessScale q {0} = 2 ∧ ∀ ω, clusterIntersection {(0 : ℕ)} ω 0 = 1 :=
  ⟨lintegral_clusterIntersection_div_two_le q (Finset.singleton_nonempty 0) 0,
    tightnessScale_singleton q 0, fun ω => by
      classical
      have h := clusterIntersection_le_max {(0 : ℕ)} ω (Finset.mem_singleton_self 0)
      rw [maxClusterIntersection_singleton] at h
      have h1 : 1 ≤ clusterIntersection {(0 : ℕ)} ω 0 := by
        rw [clusterIntersection_eq_card_filter, Nat.one_le_iff_ne_zero, ne_eq,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        simp [mem_cluster_self]
      omega⟩

/-- Items 3 and 4 with `Λ = {v}`: every hypothesis holds; in item 4 the identity is the
transitive bijection. -/
example (q : Sym2 ℕ → unitInterval) (t : ℝ≥0∞) :
    2⁻¹ * min 1 (t / ((99 * tightnessScale q {0} : ℕ) : ℝ≥0∞)) *
        ∫⁻ ω, (clusterIntersection {0} ω 0 : ℝ≥0∞) ∂(law q) ≤
      ∫⁻ ω, min (clusterIntersection {0} ω 0 : ℝ≥0∞) t ∂(law q) ∧
    ENNReal.ofReal ((tightnessScale q {0} : ℝ) ^ 2 / (4 * Real.exp 1)) ≤
      ({0} : Finset ℕ).card * ∫⁻ ω, (clusterIntersection {0} ω 0 : ℝ≥0∞) ∂(law q) :=
  ⟨lintegral_clusterIntersection_min_ge q (Finset.singleton_nonempty 0) 0 t,
    le_card_mul_lintegral_clusterIntersection_of_transitive q (Finset.singleton_nonempty 0) 0
      fun v hv => ⟨Equiv.refl ℕ, (Finset.mem_singleton.1 hv).symm,
        by simp, fun _ => Iff.rfl⟩⟩

end PercLib.Percolation.Bond
