/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc, files
`PercLib/CriticalLRP/Tightness/LemmaI26Averaging.lean` (blob 817aa6d768) and
`PercLib/CriticalLRP/Analysis/LatticeBallAsymptotic.lean` (blob 245577addf), contributed by
`yujinhkim`. Licence: Apache-2.0, as declared in those files' headers and in
`third_party/critical-lrp/NOTICE.md` of that commit (upstream origin
`yujinhkim/Critical-Long-range-percolation` at 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf, not
independently verified). Changes: the argument (deterministic counting, translation averaging,
Markov) is kept and rewritten on the bond interface: the source's `FiniteVolume.box`,
`linfNorm`, `latticeBall`, `clusterVolIn`, `ballClusterCount`, `shiftConfig` and `edianMaxVol` are
replaced by mathlib's sup norm on `Fin d → ℤ`, the `Finset.Icc` ball of
`Models/LongRange/PowerLaw.lean`, `clusterIntersection`, the push-forward `Sym2.map σ ''` of
`Percolation/Bond/Transport.lean` and `tightnessScale`; no definition is added; focused imports;
`autoImplicit` off.
-/
module

public import PercLib.Models.LongRange.PowerLaw
public import PercLib.Percolation.Bond.Tightness.FiniteQuantile
public import PercLib.Percolation.Bond.Tightness.Hyperscaling
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Models.TranslationInvariant
public import PercLib.Probability.Transport.Reindexing

/-! # The quantile scale bounds the cluster moments on `ℤ^d` (Lemma I.2.6)

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.2.6. On
`ℤ^d = Fin d → ℤ` with the sup norm, `B_n = Finset.Icc (-n) n = {z | ‖z‖ ≤ n}` has
`(2n+1)^d` points. Let `q` be a profile invariant under every translation and
`M_n = tightnessScale q B_n`.

* `le_card_mul_law_clusterIntersection_ball` and `law_clusterIntersection_ball_ge` (item 1):
  `P(|K_0 ∩ B_{2n}| ≥ M_n - 1) ≥ (M_n - 1)/(e (2n+1)^d)`. If some cluster has `m` points in
  `B_n`, every one of them sees at least `m` points of its cluster in the ball of radius `2n`
  around itself; averaging over the translates gives the bound.
* `rpow_div_le_lintegral_clusterIntersection_ball`, `rpow_div_le_lintegral_encard_cluster`
  (item 2): for real `p > 0`, `(M_n - 1)^{p+1}/(e (2n+1)^d) ≤ E|K_0 ∩ B_{2n}|^p ≤ E|K_0|^p`;
  `norm_le_iff_norm_le_floor` gives the real-radius form (`B_r = B_{⌊r⌋}`).
* `tendsto_card_ball_div_two_mul_pow` (item 3): `#{z | ‖z‖ ≤ r} / (2r)^d → 1`.
* `intensityProfile_translation_invariant` (item 4): `intensityProfile J β` satisfies the
  hypothesis whenever `J` is translation invariant.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

variable {d : ℕ}

/-! ### Geometry -/

/-- **`B_n ⊆ B_{2n}(x)` for `x ∈ B_n`.** -/
theorem sub_mem_ball_two_mul {n : ℕ} {x y : Fin d → ℤ}
    (hx : x ∈ Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ)))
    (hy : y ∈ Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) :
    y - x ∈ Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ)) (fun _ => ((2 * n : ℕ) : ℤ)) := by
  rw [mem_Icc_iff_norm_le] at hx hy ⊢
  calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
    _ ≤ n + n := add_le_add hy hx
    _ = ((2 * n : ℕ) : ℝ) := by push_cast; ring

/-- For `r ≥ 0` the real ball of radius `r` is the ball of radius `⌊r⌋`. -/
theorem norm_le_iff_norm_le_floor {r : ℝ} (hr : 0 ≤ r) (z : Fin d → ℤ) :
    ‖z‖ ≤ r ↔ ‖z‖ ≤ (⌊r⌋₊ : ℝ) := by
  constructor
  · intro h
    rw [← natCast_floor_norm z]
    exact_mod_cast Nat.floor_le_floor h
  · intro h
    exact h.trans (Nat.floor_le hr)

/-! ### Transport of cluster intersections -/

/-- Cluster intersections are carried along a bijection that moves the window with them. -/
theorem clusterIntersection_map_image {V : Type*} (Λ : Finset V) (σ : V ≃ V) (ω : Config V)
    (y : V) :
    clusterIntersection (Λ.map σ.toEmbedding) (Sym2.map σ '' ω) (σ y) =
      clusterIntersection Λ ω y := by
  rw [clusterIntersection, clusterIntersection, cluster_image, Finset.coe_map,
    Equiv.coe_toEmbedding, ← Set.image_inter σ.injective,
    Set.ncard_image_of_injective _ σ.injective]

/-- A translation-invariant profile has a translation-invariant law. -/
theorem law_map_addRight_eq (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (a : Fin d → ℤ) :
    (law q).map (fun ω => Sym2.map (Equiv.addRight a) '' ω) = law q :=
  PercLib.Probability.prodBernoulli_map_image_sym2_invariant q (Equiv.addRight a)
    fun e => hq a e

/-- Under a translation-invariant law, `P(|K_x ∩ B_{2n}(x)| ≥ m) = P(|K_0 ∩ B_{2n}| ≥ m)`. -/
theorem law_clusterIntersection_translate (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (W : Finset (Fin d → ℤ)) (m : ℕ)
    (x : Fin d → ℤ) :
    law q {ω | m ≤ clusterIntersection (W.map (Equiv.addRight x).toEmbedding) ω x} =
      law q {ω | m ≤ clusterIntersection W ω 0} := by
  conv_lhs => rw [← law_map_addRight_eq q hq x]
  rw [map_image_sym2Map_apply]
  congr 1
  ext ω
  simp only [mem_preimage, mem_ofPred_eq]
  have h := clusterIntersection_map_image W (Equiv.addRight x) ω 0
  rw [show (Equiv.addRight x) 0 = x from zero_add x] at h
  rw [h]

/-! ### Item 1: the averaging bound -/

/-- **Deterministic counting.** If some cluster has at least `m` points in `B_n`, then at
least `m` points `x ∈ B_n` have `|K_x ∩ B_{2n}(x)| ≥ m`. -/
theorem le_card_filter_clusterIntersection (n m : ℕ) (ω : Config (Fin d → ℤ))
    (h : m ≤ maxClusterIntersection (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) ω) :
    m ≤ ((Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))).filter fun x =>
      m ≤ clusterIntersection ((Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ))
        (fun _ => ((2 * n : ℕ) : ℤ))).map (Equiv.addRight x).toEmbedding) ω x).card := by
  classical
  set Λ := Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ)) with hΛ
  have hne : Λ.Nonempty := ⟨0, by rw [hΛ, mem_Icc_iff_norm_le]; simp⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_mem_eq_sup Λ hne
    (fun v => (cluster ω v ∩ (Λ : Set (Fin d → ℤ))).ncard)
  have hmw : m ≤ (cluster ω w ∩ (Λ : Set (Fin d → ℤ))).ncard := by
    rw [← hmax]
    exact h
  set S := cluster ω w ∩ (Λ : Set (Fin d → ℤ))
  have hSfin : S.Finite := Λ.finite_toSet.subset Set.inter_subset_right
  have hsub : S ⊆ ((Λ.filter fun x => m ≤ clusterIntersection ((Finset.Icc
      (fun _ : Fin d => -((2 * n : ℕ) : ℤ)) (fun _ => ((2 * n : ℕ) : ℤ))).map
        (Equiv.addRight x).toEmbedding) ω x : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) := by
    intro x hx
    obtain ⟨hxc, hxΛ⟩ := hx
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hxΛ, hmw.trans ?_⟩)
    have hcl : cluster ω w = cluster ω x := cluster_eq_of_mem_conn hxc
    refine Set.ncard_le_ncard (fun y hy => ⟨?_, ?_⟩) ((Finset.finite_toSet _).subset
      Set.inter_subset_right)
    · rw [← hcl]
      exact hy.1
    · rw [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image]
      refine ⟨y - x, Finset.mem_coe.2 (sub_mem_ball_two_mul hxΛ hy.2), ?_⟩
      simp
  calc m ≤ S.ncard := hmw
    _ ≤ _ := by
        have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        rwa [Set.ncard_coe_finset] at this

/-- **Item 1, product form.** For a translation-invariant profile and `m = M_n - 1`,
`(M_n - 1) e^{-1} ≤ (2n+1)^d P(|K_0 ∩ B_{2n}| ≥ M_n - 1)`. -/
theorem le_card_mul_law_clusterIntersection_ball (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (n : ℕ) :
    ENNReal.ofReal (((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) * Real.exp (-1)) ≤
      (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) *
        law q {ω | tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ)))
            - 1 ≤ clusterIntersection (Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ))
              (fun _ => ((2 * n : ℕ) : ℤ))) ω 0} := by
  classical
  set Λ := Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ)) with hΛ
  set W := Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ)) (fun _ => ((2 * n : ℕ) : ℤ))
  set m := tightnessScale q Λ - 1 with hm
  have hne : Λ.Nonempty := ⟨0, by rw [hΛ, mem_Icc_iff_norm_le]; simp⟩
  have hM2 := two_le_tightnessScale q hne
  -- `P(max ≥ m) > e^{-1}` by minimality of the quantile.
  have hmin := lt_law_max_tail_of_lt_tightnessScale q Λ (show m < tightnessScale q Λ by omega)
  -- Count of good translates.
  set E : (Fin d → ℤ) → Set (Config (Fin d → ℤ)) := fun x =>
    {ω | m ≤ clusterIntersection (W.map (Equiv.addRight x).toEmbedding) ω x}
  have hEm : ∀ x, MeasurableSet (E x) := fun x =>
    (measurable_clusterIntersection _ x) (measurableSet_Ici (a := m))
  have hpt : ∀ ω, (m : ℝ≥0∞) * {ω | m ≤ maxClusterIntersection Λ ω}.indicator 1 ω ≤
      ∑ x ∈ Λ, (E x).indicator 1 ω := by
    intro ω
    by_cases hω : m ≤ maxClusterIntersection Λ ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | m ≤ maxClusterIntersection Λ ω} from hω),
        Pi.one_apply, mul_one]
      have hc := le_card_filter_clusterIntersection n m ω hω
      calc (m : ℝ≥0∞) ≤ ((Λ.filter fun x => ω ∈ E x).card : ℝ≥0∞) := by exact_mod_cast hc
        _ = ∑ x ∈ Λ, (E x).indicator 1 ω := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            by_cases hx : ω ∈ E x <;> simp [hx]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | m ≤ maxClusterIntersection Λ ω} from hω),
        mul_zero]
      exact zero_le
  have hmaxm : MeasurableSet {ω : Config (Fin d → ℤ) | m ≤ maxClusterIntersection Λ ω} :=
    (measurable_maxClusterIntersection Λ) (measurableSet_Ici (a := m))
  have hint : (m : ℝ≥0∞) * law q {ω | m ≤ maxClusterIntersection Λ ω} ≤
      ∑ x ∈ Λ, law q (E x) := by
    calc (m : ℝ≥0∞) * law q {ω | m ≤ maxClusterIntersection Λ ω}
        = ∫⁻ ω, (m : ℝ≥0∞) * {ω | m ≤ maxClusterIntersection Λ ω}.indicator 1 ω ∂(law q) := by
          rw [lintegral_const_mul _ ((measurable_one).indicator hmaxm),
              lintegral_indicator_one hmaxm]
      _ ≤ ∫⁻ ω, ∑ x ∈ Λ, (E x).indicator 1 ω ∂(law q) := lintegral_mono hpt
      _ = ∑ x ∈ Λ, law q (E x) := by
          rw [lintegral_finsetSum _ fun x _ => (measurable_one).indicator (hEm x)]
          exact Finset.sum_congr rfl fun x _ => lintegral_indicator_one (hEm x)
  have htrans : ∀ x, law q (E x) = law q {ω | m ≤ clusterIntersection W ω 0} := fun x =>
    law_clusterIntersection_translate q hq W m x
  rw [Finset.sum_congr rfl fun x _ => htrans x, Finset.sum_const, nsmul_eq_mul, hΛ,
    card_Icc_ball] at hint
  refine le_trans ?_ hint
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact mul_le_mul' le_rfl hmin.le

/-- **Item 1 (averaging bound).** `P(|K_0 ∩ B_{2n}| ≥ M_n - 1) ≥ (M_n - 1)/(e (2n+1)^d)`. -/
theorem law_clusterIntersection_ball_ge (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (n : ℕ) :
    ENNReal.ofReal (((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) ≤
      law q {ω | tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ)))
          - 1 ≤ clusterIntersection (Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ))
            (fun _ => ((2 * n : ℕ) : ℤ))) ω 0} := by
  have h := le_card_mul_law_clusterIntersection_ball q hq n
  have hc : (0 : ℝ) < (((2 * n + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast pow_pos (by omega) d
  have hc' : (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos (by omega) d).ne'
  have e : ((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ)) =
      ((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) * Real.exp (-1) / ((2 * n + 1) ^ d : ℕ) := by
    rw [Real.exp_neg]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_natCast]
  exact ENNReal.div_le_of_le_mul' h

/-! ### Item 2: moments -/

/-- **Lemma I.2.6, window form.** For real `p > 0`,
`(M_n - 1)^{p+1}/(e (2n+1)^d) ≤ E|K_0 ∩ B_{2n}|^p`. -/
theorem rpow_div_le_lintegral_clusterIntersection_ball (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) ≤
      ∫⁻ ω, (clusterIntersection (Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ))
        (fun _ => ((2 * n : ℕ) : ℤ))) ω 0 : ℝ≥0∞) ^ p ∂(law q) := by
  set m := tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) - 1
  set W := Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ)) (fun _ => ((2 * n : ℕ) : ℤ))
  have h1 := law_clusterIntersection_ball_ge q hq n
  have hX : Measurable fun ω : Config (Fin d → ℤ) => (clusterIntersection W ω 0 : ℝ≥0∞) ^ p :=
    (measurable_from_nat.comp (measurable_clusterIntersection W 0)).pow_const p
  have hmarkov := mul_meas_ge_le_lintegral₀ hX.aemeasurable (μ := law q) ((m : ℝ≥0∞) ^ p)
  have hsub : {ω | m ≤ clusterIntersection W ω 0} ⊆
      {ω | (m : ℝ≥0∞) ^ p ≤ (clusterIntersection W ω 0 : ℝ≥0∞) ^ p} := fun ω hω =>
    ENNReal.rpow_le_rpow (Nat.cast_le.2 hω) hp.le
  have hsplit : ENNReal.ofReal ((m : ℝ) ^ (p + 1) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) =
      (m : ℝ≥0∞) ^ p * ENNReal.ofReal ((m : ℝ) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) := by
    rw [Real.rpow_add' (Nat.cast_nonneg _) (by linarith), Real.rpow_one, mul_div_assoc,
      ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _), ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) hp.le]
  rw [hsplit]
  exact (mul_le_mul' le_rfl (h1.trans (measure_mono hsub))).trans hmarkov

/-- **Lemma I.2.6.** For real `p > 0`, `(M_n - 1)^{p+1}/(e (2n+1)^d) ≤ E|K_0|^p`. -/
theorem rpow_div_le_lintegral_encard_cluster (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) ≤
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law q) := by
  refine (rpow_div_le_lintegral_clusterIntersection_ball q hq n hp).trans
    (lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp.le)
  set W := Finset.Icc (fun _ : Fin d => -((2 * n : ℕ) : ℤ)) (fun _ => ((2 * n : ℕ) : ℤ))
  have hfin : (cluster ω 0 ∩ (W : Set (Fin d → ℤ))).Finite :=
    W.finite_toSet.subset Set.inter_subset_right
  rw [clusterIntersection, ← ENat.toENNReal_coe, ENat.toENNReal_le, hfin.cast_ncard_eq]
  exact Set.encard_le_encard Set.inter_subset_left

/-! ### Item 3: ball asymptotics -/

/-- `(2⌊r⌋ + 1)/r → 2`. -/
theorem tendsto_two_mul_natFloor_add_one_div :
    Tendsto (fun r : ℝ => (2 * (⌊r⌋₊ : ℝ) + 1) / r) atTop (𝓝 2) := by
  have h := (tendsto_nat_floor_div_atTop (R := ℝ)).const_mul (2 : ℝ)
  have hsum := h.add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  convert hsum using 1
  · funext r
    ring
  · norm_num

/-- **Ball asymptotics.** `#{z ∈ ℤ^d | ‖z‖ ≤ r} / (2r)^d → 1` as `r → ∞`. -/
theorem tendsto_card_ball_div_two_mul_pow (d : ℕ) :
    Tendsto (fun r : ℝ => (Nat.card {z : Fin d → ℤ // ‖z‖ ≤ r} : ℝ) / (2 * r) ^ d) atTop
      (𝓝 1) := by
  have h := (tendsto_two_mul_natFloor_add_one_div.pow d).div_const ((2 : ℝ) ^ d)
  have hne : (2 : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_self hne] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hcard : Nat.card {z : Fin d → ℤ // ‖z‖ ≤ r} = (2 * ⌊r⌋₊ + 1) ^ d := by
    rw [← card_norm_le d ⌊r⌋₊]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun z => norm_le_iff_norm_le_floor hr.le z)
  rw [hcard, div_pow, mul_pow]
  push_cast
  field_simp

/-! ### Item 4: long-range profiles -/

/-- A translation-invariant kernel gives a translation-invariant profile at every intensity. -/
theorem intensityProfile_translation_invariant {J : Sym2 (Fin d → ℤ) → NNReal}
    (hJ : ∀ a e, J (Sym2.map (· + a) e) = J e) (β : NNReal) :
    ∀ a e, intensityProfile J β (Sym2.map (· + a) e) = intensityProfile J β e :=
  fun a e => Subtype.ext (by simp only [intensityProfile, hJ])

/-- **Lemma I.2.6 for long-range percolation.** For a translation-invariant kernel `J` and every
intensity `β`, `(M_n - 1)^{p+1}/(e (2n+1)^d) ≤ E_β|K_0|^p` for real `p > 0`. -/
theorem rpow_div_le_lintegral_encard_cluster_intensity {J : Sym2 (Fin d → ℤ) → NNReal}
    (hJ : ∀ a e, J (Sym2.map (· + a) e) = J e) (β : NNReal) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((tightnessScale (intensityProfile J β)
        (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) /
          (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) ≤
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law (intensityProfile J β)) :=
  rpow_div_le_lintegral_encard_cluster _ (intensityProfile_translation_invariant hJ β) n hp

/-! ### Non-vacuity -/

/-- The zero kernel is translation invariant, so Lemma I.2.6 applies to it (and to the zero
profile) at every `n`, `β` and `p > 0`. -/
example (n : ℕ) (β : NNReal) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((tightnessScale (intensityProfile (fun _ : Sym2 (Fin 2 → ℤ) => (0 : NNReal)) β)
        (Finset.Icc (fun _ : Fin 2 => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) /
          (Real.exp 1 * ((2 * n + 1) ^ 2 : ℕ))) ≤
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law (intensityProfile
        (fun _ : Sym2 (Fin 2 → ℤ) => (0 : NNReal)) β)) :=
  rpow_div_le_lintegral_encard_cluster_intensity (fun _ _ => rfl) β n hp

/-- The nearest-neighbour kernel on `ℤ` (unit mass at `±1`, via `exists_sym2_kernel`) is
nonzero and translation invariant; the averaging bound holds for it at every `β` and `n`. -/
example (β : NNReal) (n : ℕ) : ∃ J : Sym2 (Fin 1 → ℤ) → NNReal, J ≠ 0 ∧
    ENNReal.ofReal (((tightnessScale (intensityProfile J β)
        (Finset.Icc (fun _ : Fin 1 => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) /
          (Real.exp 1 * ((2 * n + 1) ^ 1 : ℕ))) ≤
      law (intensityProfile J β)
        {ω | tightnessScale (intensityProfile J β)
            (Finset.Icc (fun _ : Fin 1 => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 ≤
          clusterIntersection (Finset.Icc (fun _ : Fin 1 => -((2 * n : ℕ) : ℤ))
            (fun _ => ((2 * n : ℕ) : ℤ))) ω 0} := by
  set a : Fin 1 → ℤ := Pi.single 0 1
  set k : (Fin 1 → ℤ) → NNReal := fun z => (if z = a then 1 else 0) + (if z = -a then 1 else 0)
  obtain ⟨J, hJ⟩ := PercLib.Models.exists_sym2_kernel k (PercLib.Models.twoPointKernel_neg a)
  have hT : ∀ b e, J (Sym2.map (· + b) e) = J e := fun b e => by
    induction e using Sym2.ind with
    | _ x y => rw [Sym2.map_mk, hJ, hJ, add_sub_add_right_eq_sub]
  refine ⟨J, fun h => ?_, law_clusterIntersection_ball_ge _
    (intensityProfile_translation_invariant hT β) n⟩
  have h0 := congrFun h s(0, a)
  rw [hJ] at h0
  simp [k] at h0

end PercLib.Models.LongRange
