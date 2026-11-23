/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1. The cap increments and weights are abbreviations from `Analysis.CapFlux.Defs`; no
source theorem is restated with a weakened statement.
-/
module

public import PercLib.Analysis.CapFlux.Defs
public import PercLib.Models.LongRange.PowerLawFluxSummability
public import PercLib.Analysis.MonotoneDerivLimit
public import PercLib.Percolation.Bond.RestorationFibreMajorant
public import PercLib.Models.LongRange.PowerLawCappedFluxInterface

/-!
# Monotone convergence of capped pivotal fluxes

The capped pivotal increments increase with their caps and converge to the uncapped increments.
Dominated convergence and uncapped-series summability prove monotonicity and pointwise convergence
  of
the corresponding series. At the source root `0`, the established power-law summability supplies
these pointwise inputs without `hfac`; uncapped flux continuity remains a separate input.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open PercLib.Percolation.Bond
open PercLib.Models.LongRange

namespace PercLib.Analysis.CapFlux

noncomputable section


/-! ### The arithmetic of the cap increment -/

/-- **The `ℕ∞`-cap as a real minimum.** The interface cap `n ⊓ (B : ℕ∞)`, coerced to `ℝ`, is the
real part of the extended-nonnegative minimum `min n (B : ℝ≥0∞)`. -/
theorem toNat_inf_toReal (n : ℕ∞) (B : ℕ) :
    ((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) = (min (n : ℝ≥0∞) (B : ℝ≥0∞)).toReal := by
  cases n with
  | top => simp
  | coe k =>
    have h1 : ((↑k ⊓ (B : ℕ∞) : ℕ∞)) = ↑(min k B) := by simp [min_def]
    rw [h1, ENat.toNat_natCast]
    rcases le_total k B with h | h
    · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
      simp
    · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
      simp

/-- The finite-cap form: on a finite volume the extended minimum is the real minimum. -/
theorem toReal_min_cap {x : ℝ≥0∞} (hx : x ≠ ⊤) (B : ℕ) :
    (min x (B : ℝ≥0∞)).toReal = min x.toReal (B : ℝ) := by
  rw [ENNReal.toReal_min hx (by simp), ENNReal.toReal_natCast]

/-- **A power difference grows when both arguments grow and the difference grows.** -/
theorem pow_sub_pow_le_pow_sub_pow {u v u' v' : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (huu : u ≤ u')
    (hvv : v ≤ v') (hsub : u - v ≤ u' - v') (p : ℕ) :
    u ^ p - v ^ p ≤ u' ^ p - v' ^ p := by
  have hu : 0 ≤ u := hv.trans hvu
  have hu' : 0 ≤ u' := hu.trans huu
  have e1 : u ^ p - v ^ p = (u - v) * ∑ i ∈ Finset.range p, u ^ i * v ^ (p - 1 - i) := by
    rw [(Commute.all u v).mul_geom_sum₂ p]
  have e2 : u' ^ p - v' ^ p = (u' - v') * ∑ i ∈ Finset.range p, u' ^ i * v' ^ (p - 1 - i) := by
    rw [(Commute.all u' v').mul_geom_sum₂ p]
  rw [e1, e2]
  refine mul_le_mul hsub (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_nonneg fun i _ => ?_)
    (by linarith)
  · exact mul_le_mul (pow_le_pow_left₀ hu huu i) (pow_le_pow_left₀ hv hvv (p - 1 - i))
      (pow_nonneg hv _) (pow_nonneg hu' _)
  · exact mul_nonneg (pow_nonneg hu i) (pow_nonneg hv (p - 1 - i))

/-- The uncapped loss `x - y` dominates the capped one, for `0 ≤ y ≤ x`. -/
theorem min_sub_min_le_sub {x y : ℝ} (_hy : 0 ≤ y) (hyx : y ≤ x) (B : ℕ) :
    min x (B : ℝ) - min y (B : ℝ) ≤ x - y := by
  rcases le_total (B : ℝ) y with hB | hB
  · have h1 : min y (B : ℝ) = (B : ℝ) := min_eq_right hB
    have h2 : min x (B : ℝ) = (B : ℝ) := min_eq_right (hB.trans hyx)
    rw [h1, h2]; linarith
  · have h1 : min y (B : ℝ) = y := min_eq_left hB
    rw [h1]
    have h2 : min x (B : ℝ) ≤ x := min_le_left _ _
    linarith

/-- **Pointwise monotonicity in the cap.** For `0 ≤ y ≤ x` and every `p`, the capped power
difference `min x B ^ p - min y B ^ p` is monotone in the cap `B`. -/
theorem capdiff_mono_real {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (p : ℕ) :
    Monotone fun B : ℕ => (min x (B : ℝ)) ^ p - (min y (B : ℝ)) ^ p := by
  intro B B' hBB
  have hBB' : (B : ℝ) ≤ (B' : ℝ) := by exact_mod_cast hBB
  refine pow_sub_pow_le_pow_sub_pow (v := min y (B:ℝ)) (u := min x (B:ℝ))
    (u' := min x (B':ℝ)) (v' := min y (B':ℝ)) (le_min hy (by positivity)) ?_ ?_ ?_
    (PercLib.Analysis.min_sub_min_le_of_le hyx hBB') p
  · exact min_le_min hyx le_rfl
  · exact min_le_min le_rfl hBB'
  · exact min_le_min le_rfl hBB'

/-- The capped power difference is nonnegative. -/
theorem capdiff_nonneg_real {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (p : ℕ) (B : ℕ) :
    0 ≤ (min x (B : ℝ)) ^ p - (min y (B : ℝ)) ^ p := by
  have h : min y (B:ℝ) ≤ min x (B:ℝ) := min_le_min hyx le_rfl
  have h0 : 0 ≤ min y (B:ℝ) := le_min hy (by positivity)
  exact sub_nonneg.2 (pow_le_pow_left₀ h0 h p)

/-- The capped power difference is dominated by the uncapped one. -/
theorem capdiff_le_real {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (p : ℕ) (B : ℕ) :
    (min x (B : ℝ)) ^ p - (min y (B : ℝ)) ^ p ≤ x ^ p - y ^ p := by
  refine pow_sub_pow_le_pow_sub_pow (v := min y (B:ℝ)) (u := min x (B:ℝ)) (u' := x) (v' := y)
    (le_min hy (by positivity)) (min_le_min hyx le_rfl) (min_le_left x _) (min_le_left y _)
    (min_sub_min_le_sub hy hyx B) p

/-- The capped power difference tends to the uncapped one as the cap grows. -/
theorem capdiff_tendsto_real {x y : ℝ} (_hy : 0 ≤ y) (_hyx : y ≤ x) (p : ℕ) :
    Tendsto (fun B : ℕ => (min x (B : ℝ)) ^ p - (min y (B : ℝ)) ^ p) atTop
      (𝓝 (x ^ p - y ^ p)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max x y)
  refine (tendsto_const_nhds (x := x ^ p - y ^ p)).congr' ?_
  filter_upwards [eventually_ge_atTop N] with B hB
  have hBN : ((N : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hx : x ≤ (B : ℝ) := le_trans (le_max_left x y) (le_trans hN.le hBN)
  have hy' : y ≤ (B : ℝ) := le_trans (le_max_right x y) (le_trans hN.le hBN)
  rw [min_eq_left hx, min_eq_left hy']



variable {d : ℕ}

/-- `capInc` in the interface's `ℕ∞`-cap shape. -/
theorem capInc_eq_toNat (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p B : ℕ)
    (ω : Config (Fin d → ℤ)) :
    capInc o e p B ω =
      ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
        (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p) := by
  simp only [capInc]
  rw [toNat_inf_toReal, toNat_inf_toReal]

/-- `capInc` as a real minimum on the a.e. finite event. -/
theorem capInc_eq_min {o : Fin d → ℤ} {e : Sym2 (Fin d → ℤ)} {p B : ℕ}
    {ω : Config (Fin d → ℤ)}
    (h1 : ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    capInc o e p B ω =
      (min ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal (B : ℝ)) ^ p -
        (min ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal (B : ℝ)) ^ p := by
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top h1 (encard_cluster_sdiff_le_insert_coe ω e o)
  simp only [capInc]
  rw [toReal_min_cap h1 B, toReal_min_cap h2 B]

/-- `capIncLim` as a real difference on the a.e. finite event. -/
theorem capIncLim_eq {o : Fin d → ℤ} {e : Sym2 (Fin d → ℤ)} {p : ℕ}
    {ω : Config (Fin d → ℤ)} (h1 : ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    capIncLim o e p ω = ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ^ p :=
  toReal_pow_sub_pow (encard_cluster_sdiff_le_insert_coe ω e o) h1 p

theorem capIncLim_nonneg (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p : ℕ)
    (ω : Config (Fin d → ℤ)) : 0 ≤ capIncLim o e p ω := ENNReal.toReal_nonneg

section AE

variable {μ : Measure (Config (Fin d → ℤ))}

variable {o : Fin d → ℤ} {e : Sym2 (Fin d → ℤ)} {p : ℕ}

theorem capInc_mono_ae (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    {B B' : ℕ} (hBB : B ≤ B') : capInc o e p B ≤ᵐ[μ] capInc o e p B' := by
  filter_upwards [hfin] with ω h1
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top h1 (encard_cluster_sdiff_le_insert_coe ω e o)
  rw [capInc_eq_min h1, capInc_eq_min h1]
  refine capdiff_mono_real ?_ ?_ p hBB
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_mono h1 (encard_cluster_sdiff_le_insert_coe ω e o)

theorem capInc_nonneg_ae' (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (B : ℕ) : 0 ≤ᵐ[μ] capInc o e p B := by
  filter_upwards [hfin] with ω h1
  rw [capInc_eq_min h1]
  exact capdiff_nonneg_real ENNReal.toReal_nonneg
    (ENNReal.toReal_mono h1 (encard_cluster_sdiff_le_insert_coe ω e o)) p B

theorem capInc_le_ae (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (B : ℕ) : capInc o e p B ≤ᵐ[μ] capIncLim o e p := by
  filter_upwards [hfin] with ω h1
  rw [capInc_eq_min h1, capIncLim_eq h1]
  exact capdiff_le_real ENNReal.toReal_nonneg
    (ENNReal.toReal_mono h1 (encard_cluster_sdiff_le_insert_coe ω e o)) p B

theorem capInc_tendsto_ae (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun B : ℕ => capInc o e p B ω) atTop (𝓝 (capIncLim o e p ω)) := by
  filter_upwards [hfin] with ω h1
  rw [show capIncLim o e p ω = ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ^ p from capIncLim_eq h1]
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top h1 (encard_cluster_sdiff_le_insert_coe ω e o)
  refine (capdiff_tendsto_real ENNReal.toReal_nonneg
    (ENNReal.toReal_mono h1 (encard_cluster_sdiff_le_insert_coe ω e o)) p).congr ?_
  intro B
  rw [capInc_eq_min h1]

end AE



/-! ### The single-pair integral: monotone and convergent in the cap -/

/-- `|u ^ p - v ^ p| ≤ B ^ p` for `0 ≤ v ≤ u ≤ B`. -/
theorem abs_pow_sub_pow_le {u v B : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (huB : u ≤ B) (p : ℕ) :
    |u ^ p - v ^ p| ≤ B ^ p := by
  have hu : 0 ≤ u := hv.trans hvu
  have h1 : v ^ p ≤ u ^ p := pow_le_pow_left₀ hv hvu p
  have h2 : u ^ p ≤ B ^ p := pow_le_pow_left₀ hu huB p
  rw [abs_le]
  constructor
  · have : 0 ≤ u ^ p := pow_nonneg hu p
    linarith
  · have : 0 ≤ v ^ p := pow_nonneg hv p
    linarith

variable {μ : Measure (Config (Fin d → ℤ))} [IsFiniteMeasure μ]
variable {o : Fin d → ℤ} {e : Sym2 (Fin d → ℤ)} {p : ℕ}

theorem measurable_capInc (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p B : ℕ) :
    Measurable fun ω => capInc o e p B ω := by
  have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster (insert e ω) o).encard : ℝ≥0∞) := measurable_encard_cluster_insert_coe e o
  have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) := measurable_encard_cluster_sdiff_coe e o
  exact ((ENNReal.measurable_toReal.comp (h1.min measurable_const)).pow_const p).sub
    ((ENNReal.measurable_toReal.comp (h2.min measurable_const)).pow_const p)

theorem measurable_capIncLim (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p : ℕ) :
    Measurable fun ω => capIncLim o e p ω := by
  have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster (insert e ω) o).encard : ℝ≥0∞) := measurable_encard_cluster_insert_coe e o
  have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) := measurable_encard_cluster_sdiff_coe e o
  exact ENNReal.measurable_toReal.comp ((h1.pow_const p).sub (h2.pow_const p))

theorem integrable_capInc (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) (p B : ℕ) :
    Integrable (capInc o e p B) μ := by
  refine Integrable.of_bound (measurable_capInc o e p B).aestronglyMeasurable ((B : ℝ) ^ p) ?_
  filter_upwards with ω
  refine abs_pow_sub_pow_le (u := (min ((cluster (insert e ω) o).encard : ℝ≥0∞) (B : ℝ≥0∞)).toReal)
    (v := (min ((cluster (ω \ {e}) o).encard : ℝ≥0∞) (B : ℝ≥0∞)).toReal) (B := (B : ℝ))
    ENNReal.toReal_nonneg ?_ ?_ p
  · exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
      (min_le_min (encard_cluster_sdiff_le_insert_coe ω e o) le_rfl)
  · exact ENNReal.toReal_mono (by simp) (min_le_right _ _)

omit [IsFiniteMeasure μ] in
theorem integral_capInc_nonneg (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (B : ℕ) : 0 ≤ ∫ ω, capInc o e p B ω ∂μ :=
  integral_nonneg_of_ae (capInc_nonneg_ae' hfin B)

theorem integral_capInc_mono (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    Monotone fun B : ℕ => ∫ ω, capInc o e p B ω ∂μ := by
  intro B B' hBB
  exact integral_mono_ae (integrable_capInc o e p B) (integrable_capInc o e p B')
    (capInc_mono_ae hfin hBB)

omit [IsFiniteMeasure μ] in
theorem integrable_capIncLim (hp : 1 ≤ p)
    (hins : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    Integrable (capIncLim o e p) μ := by
  have hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o) p hp hins
  refine Integrable.mono' (integrable_toReal_pow_encard_cluster_insert e o p hins)
    (measurable_capIncLim o e p).aestronglyMeasurable ?_
  filter_upwards [hfin] with ω h1
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono h1 (encard_cluster_sdiff_le_insert_coe ω e o)
  have h0 : 0 ≤ ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal := ENNReal.toReal_nonneg
  have hmono : ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p := pow_le_pow_left₀ h0 h2 p
  have hnn : 0 ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ^ p := sub_nonneg.2 hmono
  rw [capIncLim_eq h1, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact sub_le_self _ (pow_nonneg ENNReal.toReal_nonneg p)

theorem integral_capInc_le (hp : 1 ≤ p)
    (hins : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) (B : ℕ) :
    ∫ ω, capInc o e p B ω ∂μ ≤ ∫ ω, capIncLim o e p ω ∂μ := by
  have hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o) p hp hins
  exact integral_mono_ae (integrable_capInc o e p B) (integrable_capIncLim hp hins)
    (capInc_le_ae hfin B)

omit [IsFiniteMeasure μ] in
theorem integral_capInc_tendsto (hp : 1 ≤ p)
    (hins : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    Tendsto (fun B : ℕ => ∫ ω, capInc o e p B ω ∂μ) atTop
      (𝓝 (∫ ω, capIncLim o e p ω ∂μ)) := by
  have hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o) p hp hins
  refine tendsto_integral_of_dominated_convergence
    (fun ω => ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p)
    (fun B => (measurable_capInc o e p B).aestronglyMeasurable)
    (integrable_toReal_pow_encard_cluster_insert e o p hins) (fun B => ?_)
    (capInc_tendsto_ae hfin)
  filter_upwards [hfin] with ω h1
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono h1 (encard_cluster_sdiff_le_insert_coe ω e o)
  have h0 : 0 ≤ ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal := ENNReal.toReal_nonneg
  have hmono : ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p := pow_le_pow_left₀ h0 h2 p
  rw [capInc_eq_min h1, Real.norm_eq_abs, abs_of_nonneg (capdiff_nonneg_real h0 h2 p B)]
  calc (min ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal (B : ℝ)) ^ p -
        (min ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal (B : ℝ)) ^ p
      ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal ^ p := capdiff_le_real h0 h2 p B
    _ ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p :=
        sub_le_self _ (pow_nonneg ENNReal.toReal_nonneg p)

/-! ### The pair series: monotone and convergent in the cap -/

theorem cappedFlux_mono (hp : 1 ≤ p) (c : Sym2 (Fin d → ℤ) → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hins : ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤)
    (hsum : Summable fun e => c e * ∫ ω, capIncLim o e p ω ∂μ) :
    Monotone fun B : ℕ => ∑' e, c e * ∫ ω, capInc o e p B ω ∂μ := by
  have hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ := fun e =>
    ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o) p hp (hins e)
  intro B B' hBB
  refine Summable.tsum_le_tsum (fun e => ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_left
      (integral_mono_ae (integrable_capInc o e p B) (integrable_capInc o e p B')
        (capInc_mono_ae (hfin e) hBB)) (hc e)
  · exact Summable.of_nonneg_of_le
      (fun e => mul_nonneg (hc e) (integral_capInc_nonneg (hfin e) B))
      (fun e => mul_le_mul_of_nonneg_left (integral_capInc_le hp (hins e) B) (hc e)) hsum
  · exact Summable.of_nonneg_of_le
      (fun e => mul_nonneg (hc e) (integral_capInc_nonneg (hfin e) B'))
      (fun e => mul_le_mul_of_nonneg_left (integral_capInc_le hp (hins e) B') (hc e)) hsum

theorem cappedFlux_tendsto (hp : 1 ≤ p) (c : Sym2 (Fin d → ℤ) → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hins : ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤)
    (hsum : Summable fun e => c e * ∫ ω, capIncLim o e p ω ∂μ) :
    Tendsto (fun B : ℕ => ∑' e, c e * ∫ ω, capInc o e p B ω ∂μ) atTop
      (𝓝 (∑' e, c e * ∫ ω, capIncLim o e p ω ∂μ)) := by
  have hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ := fun e =>
    ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o) p hp (hins e)
  refine tendsto_tsum_of_dominated_convergence hsum (fun e => ?_) ?_
  · exact (integral_capInc_tendsto hp (hins e)).const_mul (c e)
  · filter_upwards with B
    intro e
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc e) (integral_capInc_nonneg (hfin e) B))]
    exact mul_le_mul_of_nonneg_left (integral_capInc_le hp (hins e) B) (hc e)


/-! ### The power-law weight and the two cap inputs -/

theorem plWeight_nonneg {d : ℕ} {α : ℝ} (hα : 0 < α) (β : ℝ≥0) {r : ℝ} (hr : 0 < r)
    (e : Sym2 (Fin d → ℤ)) : 0 ≤ plWeight α β r e := by
  have h1 : (0 : ℝ) ≤ (radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (fun s => if s < r then 1 else 0) e : ℝ) := (radialKernel _ _ e).coe_nonneg
  have h2 : (0 : ℝ) ≤ ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hr.le _)
  have h3 : (0 : ℝ) < Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)) := Real.exp_pos _
  rw [plWeight]
  exact mul_nonneg h1 (mul_nonneg (mul_nonneg β.coe_nonneg h2) h3.le)

variable {d : ℕ}

/-- **`hflux_mono` from uncapped summability** (general root). -/
theorem hflux_mono_powerLaw_of_summable (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p)
    (o : Fin d → ℤ) {u v : ℝ} (hu : 0 < u) (_huv : u < v)
    (hsum : ∀ r ∈ Ioo u v, Summable fun e => plWeight (d := d) α β r e *
      ∫ ω, capIncLim o e p ω ∂(law (intensityProfile (cutoffKernel
        (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β))) :
    ∀ r ∈ Ioo u v, Monotone fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      plWeight (d := d) α β r e *
        ∫ ω, capInc o e p B ω ∂(law (intensityProfile (cutoffKernel
          (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β)) := by
  intro r hr
  have hrpos : 0 < r := lt_trans hu hr.1
  refine cappedFlux_mono (p := p) (o := o) hp (plWeight (d := d) α β r)
    (fun e => plWeight_nonneg hα β hrpos e) (fun e => ?_) (hsum r hr)
  exact insert_moments_of_vertex_moments (N := normSeminorm ℝ (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α)) β p r o (fun y => by
      rw [lintegral_encard_pow_cutoffKernel_eq (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r β p y 0]
      exact lintegral_cutoffKernel_powerLaw_pow_ne_top hd hα hβ hrpos 0 p) e

/-- **`hflux_lim` from uncapped summability** (general root). -/
theorem hflux_lim_powerLaw_of_summable (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p)
    (o : Fin d → ℤ) {u v : ℝ} (hu : 0 < u) (_huv : u < v)
    (hsum : ∀ r ∈ Ioo u v, Summable fun e => plWeight (d := d) α β r e *
      ∫ ω, capIncLim o e p ω ∂(law (intensityProfile (cutoffKernel
        (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β))) :
    ∀ r ∈ Ioo u v, Tendsto (fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      plWeight (d := d) α β r e *
        ∫ ω, capInc o e p B ω ∂(law (intensityProfile (cutoffKernel
          (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 (∑' e : Sym2 (Fin d → ℤ), plWeight (d := d) α β r e *
        ∫ ω, capIncLim o e p ω ∂(law (intensityProfile (cutoffKernel
          (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) := by
  intro r hr
  have hrpos : 0 < r := lt_trans hu hr.1
  refine cappedFlux_tendsto (p := p) (o := o) hp (plWeight (d := d) α β r)
    (fun e => plWeight_nonneg hα β hrpos e) (fun e => ?_) (hsum r hr)
  exact insert_moments_of_vertex_moments (N := normSeminorm ℝ (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α)) β p r o (fun y => by
      rw [lintegral_encard_pow_cutoffKernel_eq (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r β p y 0]
      exact lintegral_cutoffKernel_powerLaw_pow_ne_top hd hα hβ hrpos 0 p) e

/-- **The uncapped weighted pivotal series is summable at the root.** This is production's
`summable_norm_cutoffKernel_powerLaw_flux_of_high_temp`, rewritten in the shapes of this file. -/
theorem summable_capIncLim_powerLaw_zero (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∀ r ∈ Ioo u v, Summable fun e => plWeight (d := d) α β r e *
      ∫ ω, capIncLim (0 : Fin d → ℤ) e p ω ∂(law (intensityProfile (cutoffKernel
        (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β)) := by
  intro r hr
  refine Summable.of_norm (f := fun e => plWeight (d := d) α β r e *
    ∫ ω, capIncLim (0 : Fin d → ℤ) e p ω ∂(law (intensityProfile (cutoffKernel
      (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β))) ?_
  simpa only [plWeight, capIncLim] using
    summable_norm_cutoffKernel_powerLaw_flux_of_high_temp hd hα hβ hp hu hcorner r hr

/-- **`hflux_mono` at the root, unconditionally in the high-temperature region.** -/
theorem hflux_mono_powerLaw_zero (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∀ r ∈ Ioo u v, Monotone fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      plWeight (d := d) α β r e *
        ∫ ω, capInc (0 : Fin d → ℤ) e p B ω ∂(law (intensityProfile (cutoffKernel
          (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β)) :=
  hflux_mono_powerLaw_of_summable (d := d) hd hα hβ p hp 0 hu huv
    (summable_capIncLim_powerLaw_zero hd hα hβ hp hu hcorner)

/-- **`hflux_lim` at the root, unconditionally in the high-temperature region.** -/
theorem hflux_lim_powerLaw_zero (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∀ r ∈ Ioo u v, Tendsto (fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      plWeight (d := d) α β r e *
        ∫ ω, capInc (0 : Fin d → ℤ) e p B ω ∂(law (intensityProfile (cutoffKernel
          (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 (∑' e : Sym2 (Fin d → ℤ), plWeight (d := d) α β r e *
        ∫ ω, capIncLim (0 : Fin d → ℤ) e p ω ∂(law (intensityProfile (cutoffKernel
          (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) :=
  hflux_lim_powerLaw_of_summable (d := d) hd hα hβ p hp 0 hu huv
    (summable_capIncLim_powerLaw_zero hd hα hβ hp hu hcorner)

/-! ### Assembly against the interface at the root -/

/-- **The two pointwise cap inputs of `PowerLawCappedFluxInterface` at the root, in the
interface's own integrand shape.**  Both are proved; the only hypothesis is `1 ≤ p` (the case
`p = 0` is trivial and is `hflux_mono_zero_p_zero`/`hflux_lim_zero_p_zero` below). -/
theorem hflux_mono_powerLaw_zero_toNat (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∀ r ∈ Ioo u v, Monotone fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)) := by
  intro r hr
  have h := (hflux_mono_powerLaw_zero hd hα hβ hp hu huv hcorner) r hr
  intro B B' hBB
  have h' := h hBB
  simpa only [plWeight, ← capInc_eq_toNat] using h'

/-- `hflux_lim` of the interface at the root, in the interface's own integrand shape. -/
theorem hflux_lim_powerLaw_zero_toNat (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∀ r ∈ Ioo u v, Tendsto (fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
              ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) := by
  intro r hr
  have h := (hflux_lim_powerLaw_zero hd hα hβ hp hu huv hcorner) r hr
  refine h.congr' ?_
  filter_upwards with B
  simp only [plWeight, ← capInc_eq_toNat]

/-! ### The derivative at the root from the two cap inputs -/

/-- **Derivative-level cap removal at the root, with both pointwise cap inputs proved.**  This is
`hasDerivAt_uncappedMoment_powerLaw_of_flux` at `o = 0` with `hflux_mono` and `hflux_lim`
supplied by `hflux_mono_powerLaw_zero_toNat` and `hflux_lim_powerLaw_zero_toNat`.  The single
remaining hypothesis is the continuity of the uncapped weighted pivotal flux on the window, which
is the small-tail input of the programme (not claimed here). -/
theorem hasDerivAt_uncappedMoment_powerLaw_zero_of_flux_cont (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {u v R r₀ : ℝ} (hu : 0 < u) (huv : u < v) (hvR : v ≤ R)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (hr₀ : r₀ ∈ Ioo u v)
    (hflux_cont : ContinuousOn (fun r =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v)) :
    HasDerivAt (fun r => (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal)
      (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r₀ then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r₀ ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r₀ e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β))) r₀ :=
  hasDerivAt_uncappedMoment_powerLaw_of_flux (R := R) hd hα hβ p 0 hu huv hvR hI hr₀
    (hflux_mono_powerLaw_zero_toNat hd hα hβ hp hu huv hI)
    (hflux_lim_powerLaw_zero_toNat hd hα hβ hp hu huv hI) hflux_cont

/-! ### The order-zero case of the two interface inputs -/

/-- `hflux_mono` at `p = 0`: every capped increment vanishes. -/
theorem hflux_mono_powerLaw_zero_toNat_p_zero {α : ℝ} {β : ℝ≥0} {r : ℝ} :
    Monotone fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0 -
            (((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)) := by
  have h : (fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0 -
            (((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) = fun _ => 0 := by
    funext B
    simp
  rw [h]
  exact monotone_const

/-- `hflux_lim` at `p = 0`: both sides are the zero series. -/
theorem hflux_lim_powerLaw_zero_toNat_p_zero {α : ℝ} {β : ℝ≥0} {r : ℝ} :
    Tendsto (fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0 -
            (((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
          ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ 0 -
              ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ 0).toReal)
              ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) := by
  have h : (fun B : ℕ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0 -
            (((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ 0)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) = fun _ => 0 := by
    funext B
    simp
  rw [h]
  have h0 : (∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ 0 -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ 0).toReal)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) = 0 := by
    simp
  rw [h0]
  exact tendsto_const_nhds

end

end PercLib.Analysis.CapFlux
