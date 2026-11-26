/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied. Mathematical reference:
the ghost bound for the mass gained from an independent layer (`law_added_volume_ge_mul_le`)
combined with Karamata's theorem for a regularly varying volume tail.
-/
module

public import PercLib.Analysis.RegularVariation.TruncatedMean
public import PercLib.Percolation.Bond.IndependentLayer.AddedVolume
public import PercLib.Percolation.Bond.IndependentLayer.Conditional
public import PercLib.Probability.OpenEventHarris

/-!
# A regularly varying volume tail makes omitted cluster mass negligible

Let `q` be a transitive bond profile with a.s. finite root cluster volume `X = |K_o|`, and
write `F t = P(X > t)` and `H(c) = E min(1, c X)`. Couple a lower profile `q₀` to `q` by an
independent layer `s` (so that `σ (σ q₀ · σ s) = q`), with second-layer rows at most `a`.
Writing `C` for the lower root cluster and `K` for the root cluster of the union, the ghost
bound for the added mass gives
`(1 - e^{-δ}) P(|K \ C| ≥ δ z) ≤ H(a H(1/z))` for `z, δ > 0`,
and the layer-cake formula gives `H(c) = c ∫_0^{1/c} F`. If `F` is regularly varying of
index `-ρ` with `0 < ρ < 1`, Karamata's theorem turns this into the negligibility of the
omitted mass on the scale of `F`.

## Main results

* `lintegral_min_mul_encard_eq`: `E min(1, c X) = c ∫_0^{1/c} P(X > t) dt`;
* `law_added_volume_ge_le_lintegral_min`: the bound
  `(1 - e^{-δ}) P(|K \ C| ≥ δ z) ≤ H(a H(1/z))`;
* `tendsto_limsup_law_added_volume_ge`: the omitted cluster mass is negligible.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory PercLib.Probability PercLib.Analysis
open scoped Topology ENNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The cluster volume, as an extended nonnegative real, is measurable. -/
theorem measurable_encard_cluster_ennreal [Countable V] (x : V) :
    Measurable (fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞)) :=
  (measurable_of_countable _).comp (measurable_encard_cluster x)

/-- **Truncated mean of the cluster volume.** For `c > 0`,
`E min(1, c |K_o|) = c ∫_0^{1/c} P(|K_o| > t) dt`. -/
theorem lintegral_min_mul_encard_eq [Countable V] (q : Sym2 V → I) (o : V) {c : ℝ}
    (hc : 0 < c) :
    ∫⁻ ω, min 1 (ENNReal.ofReal c * ((cluster ω o).encard : ℝ≥0∞)) ∂(law q) =
      ENNReal.ofReal (c * ∫ t in (0 : ℝ)..1 / c,
        (law q {ω | ENNReal.ofReal t < ((cluster ω o).encard : ℝ≥0∞)}).toReal) := by
  set F : ℝ → ℝ := fun t =>
    (law q {ω | ENNReal.ofReal t < ((cluster ω o).encard : ℝ≥0∞)}).toReal with hF
  have hFa : Antitone F := by
    intro t u htu
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htu) hω
  have hmin : ∀ ω, min 1 (ENNReal.ofReal c * ((cluster ω o).encard : ℝ≥0∞)) =
      ENNReal.ofReal c * min (ENNReal.ofReal (1 / c)) ((cluster ω o).encard : ℝ≥0∞) := by
    intro ω
    rw [← min_mul_mul_left, ← ENNReal.ofReal_mul hc.le, mul_one_div_cancel hc.ne',
      ENNReal.ofReal_one]
  simp_rw [hmin]
  rw [lintegral_const_mul _ ((measurable_const).min (measurable_encard_cluster_ennreal o)),
    lintegral_min_eq_lintegral_tail _ (measurable_encard_cluster_ennreal o),
    ENNReal.ofReal_mul hc.le]
  congr 1
  have h1c : 0 ≤ 1 / c := (one_div_pos.2 hc).le
  rw [intervalIntegral.integral_of_le h1c, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal]
  · refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  · exact (hFa.intervalIntegrable (a := 0) (b := 1 / c)).1.mono_set
      (by intro t ht; simpa [uIoc_of_le h1c] using ht) |>.mono_set Ioo_subset_Ioc_self
  · exact Eventually.of_forall fun t => ENNReal.toReal_nonneg

/-- Adding a layer only enlarges the root cluster, so the truncated means of the lower
cluster volume are at most those of the union model. -/
theorem lintegral_min_mul_encard_le_union [Countable V] (q₀ s : Sym2 V → I) (o : V)
    (c : ℝ≥0∞) :
    ∫⁻ ω, min 1 (c * ((cluster ω o).encard : ℝ≥0∞)) ∂(law q₀) ≤
      ∫⁻ ω, min 1 (c * ((cluster ω o).encard : ℝ≥0∞))
        ∂(law fun e => σ (σ (q₀ e) * σ (s e))) := by
  set g : Config V → ℝ≥0∞ := fun ω => min 1 (c * ((cluster ω o).encard : ℝ≥0∞)) with hg
  have hgm : Measurable g :=
    measurable_const.min (measurable_const.mul (measurable_encard_cluster_ennreal o))
  have hu : Measurable fun x : Config V × Config V => x.1 ∪ x.2 :=
    Measurable.of_mem fun e => ((measurable_set_mem e).comp measurable_fst).or
      ((measurable_set_mem e).comp measurable_snd)
  have hR : ∫⁻ ω, g ω ∂(law fun e => σ (σ (q₀ e) * σ (s e))) =
      ∫⁻ x, g (x.1 ∪ x.2) ∂((law q₀).prod (law s)) := by
    rw [law, ← prodBernoulli_prod_map_union, lintegral_map hgm hu]
    rfl
  have hL : ∫⁻ ω, g ω ∂(law q₀) = ∫⁻ x, g x.1 ∂((law q₀).prod (law s)) := by
    rw [lintegral_prod (fun x : Config V × Config V => g x.1)
      (hgm.comp measurable_fst).aemeasurable]
    simp
  change ∫⁻ ω, g ω ∂(law q₀) ≤ ∫⁻ ω, g ω ∂(law fun e => σ (σ (q₀ e) * σ (s e)))
  rw [hL, hR]
  refine lintegral_mono fun x => min_le_min_left _ (mul_le_mul_right ?_ _)
  exact ENat.toENNReal_le.2 (Set.encard_le_encard (cluster_mono subset_union_left o))

/-- If the union cluster is a.s. finite, so is the lower cluster. -/
theorem ae_cluster_finite_of_union [Countable V] (q₀ s : Sym2 V → I) (o : V)
    (hfin : ∀ᵐ ω ∂(law fun e => σ (σ (q₀ e) * σ (s e))), (cluster ω o).Finite) :
    ∀ᵐ ω ∂(law q₀), (cluster ω o).Finite := by
  have hu : Measurable fun x : Config V × Config V => x.1 ∪ x.2 :=
    Measurable.of_mem fun e => ((measurable_set_mem e).comp measurable_fst).or
      ((measurable_set_mem e).comp measurable_snd)
  rw [law, ← prodBernoulli_prod_map_union] at hfin
  have h := Measure.ae_ae_of_ae_prod (ae_of_ae_map hu.aemeasurable hfin)
  filter_upwards [h] with ω hω
  obtain ⟨ω', hω'⟩ := hω.exists
  exact hω'.subset (cluster_mono subset_union_left o)

/-- The ghost transform is at most the truncated mean: `E[1 - e^{-hX}] ≤ E min(1, hX)`. -/
theorem lintegral_ghost_le_lintegral_min (μ : Measure (Config V)) (o : V) {h : ℝ}
    (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂μ ≤
      ∫⁻ ω, min 1 (ENNReal.ofReal h * ((cluster ω o).encard : ℝ≥0∞)) ∂μ :=
  lintegral_mono fun _ => le_min tsub_le_self (one_sub_exp_le_mul hh _)

/-- **Omitted mass and truncated means.** Let `q` be transitive with a.s. finite root
cluster, and `σ (σ q₀ · σ s) = q` with second-layer rows at most `a`. Writing
`H(c) = E_q min(1, c |K_o|)`, for `z > 0` and every `δ`,
`(1 - e^{-δ}) P(|K \ C| ≥ δ z) ≤ H(a H(1/z))`. -/
theorem law_added_volume_ge_le_lintegral_min [Countable V] (q q₀ s : Sym2 V → I) (o : V)
    (hq : (fun e => σ (σ (q₀ e) * σ (s e))) = q)
    (hT : ∀ x y : V, ∃ τ : V ≃ V, τ x = y ∧ ∀ e, q (Sym2.map τ e) = q e)
    (hfin : ∀ᵐ ω ∂(law q), (cluster ω o).Finite) {a : ℝ≥0∞}
    (ha : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ a) {z δ : ℝ}
    (hz : 0 < z) :
    ENNReal.ofReal (1 - Real.exp (-δ)) *
        ((law q₀).prod (law s))
          {x | ENNReal.ofReal (δ * z) ≤ ((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞)} ≤
      ∫⁻ ω, min 1 ((a * ∫⁻ ω', min 1 (ENNReal.ofReal z⁻¹ *
          ((cluster ω' o).encard : ℝ≥0∞)) ∂(law q)) * ((cluster ω o).encard : ℝ≥0∞))
        ∂(law q) := by
  have hh : 0 < z⁻¹ := inv_pos.2 hz
  have hfin₀ := ae_cluster_finite_of_union q₀ s o (hq ▸ hfin)
  set n : ℕ := ⌈δ * z⌉₊ with hn
  have htail := law_added_volume_ge_mul_le q₀ s o hh hfin₀ ha (n : ℕ∞)
  rw [hq] at htail
  -- the real event is the integer event at `⌈δ z⌉₊`
  have hset : {x : Config V × Config V |
      ENNReal.ofReal (δ * z) ≤ ((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞)} =
      {x | (n : ℕ∞) ≤ (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard} := by
    ext x
    simp only [mem_ofPred_eq]
    generalize (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard = k
    induction k using ENat.recTopCoe with
    | top => simp
    | coe k =>
      rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, Nat.cast_le,
        ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg k), hn, Nat.ceil_le]
  -- the integer threshold has a larger ghost deficit
  have hdef : ENNReal.ofReal (1 - Real.exp (-δ)) ≤
      1 - EReal.exp (-((z⁻¹ : ℝ) : EReal) * ((((n : ℕ∞) : ℝ≥0∞) : EReal))) := by
    rw [neg_mul, exp_neg_mul_natCast_eq, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (sub_le_sub_left (Real.exp_le_exp.2 ?_) _)
    have hle : δ * z ≤ n := Nat.le_ceil _
    rw [neg_le_neg_iff, le_inv_mul_iff₀ hz]
    linarith
  -- the supremum of ghost transforms is the root truncated mean bound
  have hM : (⨆ v, ∫⁻ ω', (1 - EReal.exp (-((z⁻¹ : ℝ) : EReal) *
      (((cluster ω' v).encard : ℝ≥0∞) : EReal))) ∂(law q)) ≤
      ∫⁻ ω', min 1 (ENNReal.ofReal z⁻¹ * ((cluster ω' o).encard : ℝ≥0∞)) ∂(law q) := by
    refine iSup_le fun v => ?_
    simp_rw [neg_mul]
    rw [lintegral_ghost_eq_of_transitive q hT z⁻¹ o v]
    exact lintegral_ghost_le_lintegral_min _ o hh
  rw [hset]
  refine (mul_le_mul_left hdef _).trans ?_
  simp_rw [← neg_mul] at htail
  refine htail.trans ((lintegral_mono fun ω => min_le_min_left _
    (mul_le_mul_left (mul_le_mul_right hM _) _)).trans ?_)
  rw [← hq]
  exact lintegral_min_mul_encard_le_union q₀ s o _

/-- **A regularly varying volume tail makes omitted cluster mass negligible.** Let `q` be a
transitive bond profile whose root cluster volume `X = |K_o|` is a.s. finite, with
`F t = P(X > t)` regularly varying of index `-ρ`, `0 < ρ < 1`. Let `z_R → ∞` along `l` and
`c F(z_R) ≤ η_R ≤ C F(z_R)` eventually, with `c > 0`. For each `s ≥ 1` and `R`, let
`σ (σ q₀ · σ s') = q` (a lower profile coupled to `q` by an independent layer `s'`) with
layer rows at most `a_{R,s}`, and suppose `limsup_R a_{R,s} z_R η_R ≤ b(s)` with
`b(s) → 0`. Then for every `δ > 0`,
`lim_{s → ∞} limsup_R η_R⁻¹ P(|K \ C_{R,s}| ≥ δ z_R) = 0`. -/
theorem tendsto_limsup_law_added_volume_ge [Countable V] (q : Sym2 V → I) (o : V) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hT : ∀ x y : V, ∃ τ : V ≃ V, τ x = y ∧ ∀ e, q (Sym2.map τ e) = q e)
    (hfin : ∀ᵐ ω ∂(law q), (cluster ω o).Finite)
    (hrv : RegularlyVarying (-ρ) fun t =>
      (law q {ω | ENNReal.ofReal t < ((cluster ω o).encard : ℝ≥0∞)}).toReal)
    {ι : Type*} {l : Filter ι} {z η : ι → ℝ} (hz : Tendsto z l atTop)
    (hη : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ R in l,
      c * (law q {ω | ENNReal.ofReal (z R) < ((cluster ω o).encard : ℝ≥0∞)}).toReal ≤ η R ∧
      η R ≤ C * (law q {ω | ENNReal.ofReal (z R) < ((cluster ω o).encard : ℝ≥0∞)}).toReal)
    (q₀ s' : ι → ℝ → Sym2 V → I) (a : ι → ℝ → ℝ≥0∞) (b : ℝ → ℝ)
    (hq : ∀ R s, 1 ≤ s → (fun e => σ (σ (q₀ R s e) * σ (s' R s e))) = q)
    (ha : ∀ R s, 1 ≤ s → ∀ u, rowSum (fun e => unitInterval.toENNReal (s' R s e)) u ≤ a R s)
    (hb : Tendsto b atTop (𝓝 0))
    (hab : ∀ s, 1 ≤ s →
      limsup (fun R => a R s * ENNReal.ofReal (z R * η R)) l ≤ ENNReal.ofReal (b s))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun s => limsup (fun R => (ENNReal.ofReal (η R))⁻¹ *
        ((law (q₀ R s)).prod (law (s' R s)))
          {x | ENNReal.ofReal (δ * z R) ≤
            ((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞)}) l) atTop (𝓝 0) := by
  set F : ℝ → ℝ := fun t =>
    (law q {ω | ENNReal.ofReal t < ((cluster ω o).encard : ℝ≥0∞)}).toReal with hF
  have hFa : Antitone F := by
    intro t u htu
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htu) hω
  set H : ℝ≥0∞ → ℝ≥0∞ := fun c =>
    ∫⁻ ω, min 1 (c * ((cluster ω o).encard : ℝ≥0∞)) ∂(law q) with hH
  have hHmono : Monotone H := fun c c' hcc' =>
    lintegral_mono fun ω => min_le_min_left _ (mul_le_mul_left hcc' _)
  -- `H (c / z) = (c / z) ∫_0^{z/c} F`
  have hHeq : ∀ c z : ℝ, 0 < c → 0 < z →
      H (ENNReal.ofReal (c / z)) = ENNReal.ofReal (c / z * ∫ t in (0 : ℝ)..z / c, F t) := by
    intro c z hc hz
    have := lintegral_min_mul_encard_eq q o (div_pos hc hz)
    rwa [one_div_div] at this
  obtain ⟨c₀, C, hc₀, hηF⟩ := hη
  have hd : 0 < 1 - Real.exp (-δ) := by
    have := Real.exp_lt_exp.2 (neg_lt_zero.2 hδ)
    rw [Real.exp_zero] at this
    linarith
  set D : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-δ)) with hD
  have hD0 : D ≠ 0 := (ENNReal.ofReal_pos.2 hd).ne'
  -- the root normalization: eventually `H (1/z) ≤ A η`
  set A : ℝ := 2 / (1 - ρ) / c₀ with hA
  have hApos : 0 < A := div_pos (div_pos two_pos (by linarith)) hc₀
  have hK1 := tendsto_mul_integral_div_of_regularlyVarying hρ1 one_pos hFa hrv
  rw [Real.one_rpow] at hK1
  have hH1 : ∀ᶠ R in l, H (ENNReal.ofReal (z R)⁻¹) ≤ ENNReal.ofReal (A * η R) := by
    filter_upwards [hz.eventually (hK1.eventually (gt_mem_nhds (show 1 / (1 - ρ) < 2 / (1 - ρ)
      from div_lt_div_of_pos_right one_lt_two (by linarith)))),
      hz.eventually hrv.eventually_pos, hz.eventually (eventually_gt_atTop 0), hηF]
      with R hR hFR hzR hηR
    simp only [div_one] at hR
    rw [← one_div, hHeq 1 (z R) one_pos hzR, div_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 / z R * ∫ t in (0 : ℝ)..z R, F t ≤ 2 / (1 - ρ) * F (z R) := by
      rw [div_lt_iff₀ hFR] at hR; exact hR.le
    calc 1 / z R * ∫ t in (0 : ℝ)..z R, F t ≤ 2 / (1 - ρ) * F (z R) := h1
      _ = A * (c₀ * F (z R)) := by rw [hA]; field_simp
      _ ≤ A * η R := mul_le_mul_of_nonneg_left hηR.1 hApos.le
  -- the bound at fixed `s`
  set bs : ℝ → ℝ := fun s => max (b s) 0 + 1 / s with hbs
  set B : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (2 * (A * bs s) ^ ρ / (1 - ρ) / c₀) / D with hB
  have hbound : ∀ s, 1 ≤ s → limsup (fun R => (ENNReal.ofReal (η R))⁻¹ *
      ((law (q₀ R s)).prod (law (s' R s)))
        {x | ENNReal.ofReal (δ * z R) ≤
          ((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞)}) l ≤ B s := by
    intro s hs
    have hbs0 : 0 < bs s := by
      have : 0 < 1 / s := one_div_pos.2 (by linarith)
      have := le_max_right (b s) 0
      simp only [hbs]; linarith
    set c : ℝ := A * bs s with hc
    have hcpos : 0 < c := mul_pos hApos hbs0
    have hKc := tendsto_mul_integral_div_of_regularlyVarying hρ1 hcpos hFa hrv
    have hlt : limsup (fun R => a R s * ENNReal.ofReal (z R * η R)) l <
        ENNReal.ofReal (bs s) := by
      refine (hab s hs).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hbs0).2 ?_)
      have : 0 < 1 / s := one_div_pos.2 (by linarith)
      have := le_max_left (b s) 0
      simp only [hbs]; linarith
    refine limsup_le_of_le (by isBoundedDefault) ?_
    have hrate : c ^ ρ / (1 - ρ) < 2 * c ^ ρ / (1 - ρ) := by
      have : 0 < c ^ ρ / (1 - ρ) := div_pos (Real.rpow_pos_of_pos hcpos _) (by linarith)
      rw [mul_div_assoc]; linarith
    filter_upwards [eventually_lt_of_limsup_lt hlt, hH1,
      hz.eventually (hKc.eventually (gt_mem_nhds hrate)),
      hz.eventually hrv.eventually_pos, hz.eventually (eventually_gt_atTop 0), hηF]
      with R hRa hRH hRc hFR hzR hηR
    have hηpos : 0 < η R := lt_of_lt_of_le (mul_pos hc₀ hFR) hηR.1
    -- `a H(1/z) ≤ c / z`
    have harg : a R s * H (ENNReal.ofReal (z R)⁻¹) ≤ ENNReal.ofReal (c / z R) := by
      calc a R s * H (ENNReal.ofReal (z R)⁻¹) ≤ a R s * ENNReal.ofReal (A * η R) :=
            mul_le_mul_right hRH _
        _ = ENNReal.ofReal (A / z R) * (a R s * ENNReal.ofReal (z R * η R)) := by
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (A / z R)) (a R s), mul_assoc,
              ← ENNReal.ofReal_mul (div_pos hApos hzR).le,
              show A / z R * (z R * η R) = A * η R by field_simp]
        _ ≤ ENNReal.ofReal (A / z R) * ENNReal.ofReal (bs s) := mul_le_mul_right hRa.le _
        _ = ENNReal.ofReal (c / z R) := by
            rw [← ENNReal.ofReal_mul (div_pos hApos hzR).le, hc]; congr 1; ring
    have hmain := law_added_volume_ge_le_lintegral_min q (q₀ R s) (s' R s) o (hq R s hs) hT
      hfin (ha R s hs) (δ := δ) hzR
    -- `H (c / z) ≤ (2 c^ρ / (1 - ρ) / c₀) η`
    have hHc : H (ENNReal.ofReal (c / z R)) ≤
        ENNReal.ofReal (2 * c ^ ρ / (1 - ρ) / c₀ * η R) := by
      rw [hHeq c (z R) hcpos hzR]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_lt_iff₀ hFR] at hRc
      calc c / z R * ∫ t in (0 : ℝ)..z R / c, F t ≤ 2 * c ^ ρ / (1 - ρ) * F (z R) := hRc.le
        _ = 2 * c ^ ρ / (1 - ρ) / c₀ * (c₀ * F (z R)) := by field_simp
        _ ≤ 2 * c ^ ρ / (1 - ρ) / c₀ * η R :=
            mul_le_mul_of_nonneg_left hηR.1
              (div_nonneg (div_nonneg (mul_nonneg zero_le_two
                (Real.rpow_nonneg hcpos.le _)) (by linarith)) hc₀.le)
    have hP : D * ((law (q₀ R s)).prod (law (s' R s)))
        {x | ENNReal.ofReal (δ * z R) ≤
          ((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞)} ≤
        ENNReal.ofReal (2 * c ^ ρ / (1 - ρ) / c₀) * ENNReal.ofReal (η R) := by
      refine hmain.trans ((hHmono harg).trans (hHc.trans_eq ?_))
      rw [ENNReal.ofReal_mul (div_nonneg (div_nonneg (mul_nonneg zero_le_two
        (Real.rpow_nonneg hcpos.le _)) (by linarith)) hc₀.le)]
    have hη0 : ENNReal.ofReal (η R) ≠ 0 := (ENNReal.ofReal_pos.2 hηpos).ne'
    rw [hB, ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl ENNReal.ofReal_ne_top), mul_comm,
      ← mul_assoc]
    calc D * (ENNReal.ofReal (η R))⁻¹ * _ = (ENNReal.ofReal (η R))⁻¹ * (D * _) := by ring
      _ ≤ (ENNReal.ofReal (η R))⁻¹ *
          (ENNReal.ofReal (2 * c ^ ρ / (1 - ρ) / c₀) * ENNReal.ofReal (η R)) :=
          mul_le_mul_right hP _
      _ = ENNReal.ofReal (2 * c ^ ρ / (1 - ρ) / c₀) := by
          rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hη0 ENNReal.ofReal_ne_top, mul_one]
  -- the bound tends to zero
  have hbs : Tendsto bs atTop (𝓝 0) := by
    have h1 : Tendsto (fun s => max (b s) 0) atTop (𝓝 (max 0 0)) :=
      hb.max tendsto_const_nhds
    have h2 : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    change Tendsto (fun s => max (b s) 0 + 1 / s) atTop (𝓝 0)
    have h3 := h1.add h2
    rwa [max_self, add_zero] at h3
  have hBt : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun s => 2 * (A * bs s) ^ ρ / (1 - ρ) / c₀) atTop
        (𝓝 (2 * (A * 0) ^ ρ / (1 - ρ) / c₀)) :=
      ((((hbs.const_mul A).rpow_const (Or.inr hρ0.le)).const_mul 2).div_const _).div_const _
    rw [mul_zero, Real.zero_rpow hρ0.ne', mul_zero, zero_div, zero_div] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    have h3 := ENNReal.Tendsto.div_const h2 (Or.inr hD0)
    rwa [ENNReal.zero_div] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBt
    (Eventually.of_forall fun _ => bot_le) ((eventually_ge_atTop 1).mono hbound)

end PercLib.Percolation.Bond
