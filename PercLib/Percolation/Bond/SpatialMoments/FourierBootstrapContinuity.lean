/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Defs
public import PercLib.Percolation.Bond.SpatialMoments.FourierRatioContinuity
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Continuity of the canonical Fourier bootstrap functions

The susceptibility parameter and ratio supremum use the actual intensity-family
continuity theorems. Resolvent differences are controlled uniformly by the parameter
difference under a finite susceptibility envelope. The positive three-resolvent
factor then permits the normalized second-difference supremum to vary continuously.

## Main results

* `continuousAt_susceptibilityWalkParameter_intensity`: the actual normalization is continuous.
* `continuousAt_fourierRatioSup_intensity`: the canonical ratio supremum is continuous.
* `nearestNeighborResolvent_le_chi`: the model susceptibility bounds every resolvent.
* `abs_bootstrapTripleProduct_inv_sub_le`: quantitative uniform variation of the denominator factor.
* `continuousAt_fourierDifferenceSup_intensity`: continuity of the actual third bootstrap function.
-/

@[expose] public section

noncomputable section

open Filter Set Real PercLib.Analysis PercLib.Models.Site
open scoped Topology ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The actual susceptibility normalization belongs to the subcritical parameter interval. -/
theorem susceptibilityWalkParameter_mem_Ico (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hchi : chi q 0 ≠ ⊤) : susceptibilityWalkParameter q ∈ Ico (0 : ℝ) 1 :=
  one_sub_inv_toReal_chi_mem_Ico q 0 hchi

/-- The actual susceptibility normalization is continuous at finite susceptibility. -/
theorem continuousAt_susceptibilityWalkParameter_intensity
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => susceptibilityWalkParameter (intensityProfile J b)) β := by
  have h1 : (1 : ℝ) ≤ (chi (intensityProfile J β) 0).toReal := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono hchi (one_le_chi (intensityProfile J β) 0)
  exact continuousAt_const.sub
    ((continuousAt_toReal_chi_intensity J hJ 0 hL hchi).inv₀ (by linarith))

/-- Compatibility with the actual ratio-continuity theorem, using the canonical definitions. -/
theorem continuousAt_fourierRatioSup_intensity (hd : 0 < d)
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => fourierRatioSup (intensityProfile J b)) β := by
  simpa only [fourierRatioSup, tauFourier_def, susceptibilityWalkParameter_def,
    nearestNeighborSymbol_def] using continuousAt_fourier_ratio_sup hd J hJ hL hchi

/-- Every resolvent at the actual normalization is bounded by susceptibility. -/
theorem nearestNeighborResolvent_le_chi (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤) (k : Fin d → ℝ) :
    nearestNeighborResolvent (susceptibilityWalkParameter q) k ≤ (chi q 0).toReal := by
  simpa only [susceptibilityWalkParameter, sub_sub_cancel, inv_inv] using
    nearestNeighborResolvent_le_inv_one_sub hd (susceptibilityWalkParameter_mem_Ico q hchi) k

private theorem abs_resolvent_sub_le (hd : 0 < d) {lam mu M : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) (hmu : mu ∈ Ico (0 : ℝ) 1)
    (hClam : ∀ z : Fin d → ℝ, nearestNeighborResolvent lam z ≤ M)
    (hCmu : ∀ z : Fin d → ℝ, nearestNeighborResolvent mu z ≤ M) (k : Fin d → ℝ) :
    |nearestNeighborResolvent lam k - nearestNeighborResolvent mu k| ≤ M ^ 2 * |lam - mu| := by
  have hdenlam := nearestNeighborResolvent_den_pos hd hlam k
  have hdenmu := nearestNeighborResolvent_den_pos hd hmu k
  have hposlam := (nearestNeighborResolvent_pos hd hlam k).le
  have hposmu := (nearestNeighborResolvent_pos hd hmu k).le
  have hM : 0 ≤ M := hposlam.trans (hClam k)
  have heq : |nearestNeighborResolvent lam k - nearestNeighborResolvent mu k| =
      (|lam - mu| * |nearestNeighborSymbol k|) *
        (nearestNeighborResolvent lam k * nearestNeighborResolvent mu k) := by
    simp only [nearestNeighborResolvent]
    rw [← Real.dist_eq, dist_inv_inv₀ hdenlam.ne' hdenmu.ne', Real.dist_eq,
      Real.norm_of_nonneg hdenlam.le, Real.norm_of_nonneg hdenmu.le,
      show (1 - lam * nearestNeighborSymbol k) - (1 - mu * nearestNeighborSymbol k) =
        (mu - lam) * nearestNeighborSymbol k by ring,
      abs_mul, abs_sub_comm mu lam, div_eq_mul_inv, mul_inv]
  rw [heq]
  have hprod : nearestNeighborResolvent lam k * nearestNeighborResolvent mu k ≤ M ^ 2 := by
    simpa only [pow_two] using mul_le_mul (hClam k) (hCmu k) hposmu hM
  calc
    _ ≤ |lam - mu| * M ^ 2 := mul_le_mul
      (mul_le_of_le_one_right (abs_nonneg _) (nearestNeighborSymbol_abs_le_one hd k))
      hprod (mul_nonneg hposlam hposmu) (abs_nonneg _)
    _ = _ := by ring

private theorem abs_tripleProduct_sub_le (hd : 0 < d) {lam mu M : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) (hmu : mu ∈ Ico (0 : ℝ) 1)
    (hClam : ∀ z : Fin d → ℝ, nearestNeighborResolvent lam z ≤ M)
    (hCmu : ∀ z : Fin d → ℝ, nearestNeighborResolvent mu z ≤ M) (k l : Fin d → ℝ) :
    |bootstrapTripleProduct lam k l - bootstrapTripleProduct mu k l| ≤
      6 * M ^ 3 * |lam - mu| := by
  have hM : 0 ≤ M := (nearestNeighborResolvent_pos hd hlam l).le.trans (hClam l)
  have hprod (a b : Fin d → ℝ) :
      |nearestNeighborResolvent lam a * nearestNeighborResolvent lam b -
        nearestNeighborResolvent mu a * nearestNeighborResolvent mu b| ≤
        2 * M ^ 3 * |lam - mu| := by
    calc
      _ = |(nearestNeighborResolvent lam a - nearestNeighborResolvent mu a) *
          nearestNeighborResolvent lam b + nearestNeighborResolvent mu a *
          (nearestNeighborResolvent lam b - nearestNeighborResolvent mu b)| := by congr 1; ring
      _ ≤ |(nearestNeighborResolvent lam a - nearestNeighborResolvent mu a) *
          nearestNeighborResolvent lam b| + |nearestNeighborResolvent mu a *
          (nearestNeighborResolvent lam b - nearestNeighborResolvent mu b)| := abs_add_le _ _
      _ = |nearestNeighborResolvent lam a - nearestNeighborResolvent mu a| *
          nearestNeighborResolvent lam b + nearestNeighborResolvent mu a *
          |nearestNeighborResolvent lam b - nearestNeighborResolvent mu b| := by
        rw [abs_mul, abs_mul, abs_of_pos (nearestNeighborResolvent_pos hd hlam b),
          abs_of_pos (nearestNeighborResolvent_pos hd hmu a)]
      _ ≤ (M ^ 2 * |lam - mu|) * M + M * (M ^ 2 * |lam - mu|) := by
        apply add_le_add
        · exact mul_le_mul (abs_resolvent_sub_le hd hlam hmu hClam hCmu a) (hClam b)
            (nearestNeighborResolvent_pos hd hlam b).le (by positivity)
        · exact mul_le_mul (hCmu a) (abs_resolvent_sub_le hd hlam hmu hClam hCmu b)
            (abs_nonneg _) hM
      _ = _ := by ring
  have hsum := abs_add_le
    (nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam l -
      nearestNeighborResolvent mu (l - k) * nearestNeighborResolvent mu l +
      (nearestNeighborResolvent lam l * nearestNeighborResolvent lam (l + k) -
        nearestNeighborResolvent mu l * nearestNeighborResolvent mu (l + k)))
    (nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam (l + k) -
      nearestNeighborResolvent mu (l - k) * nearestNeighborResolvent mu (l + k))
  have htwo := abs_add_le
    (nearestNeighborResolvent lam (l - k) * nearestNeighborResolvent lam l -
      nearestNeighborResolvent mu (l - k) * nearestNeighborResolvent mu l)
    (nearestNeighborResolvent lam l * nearestNeighborResolvent lam (l + k) -
      nearestNeighborResolvent mu l * nearestNeighborResolvent mu (l + k))
  unfold bootstrapTripleProduct
  have heq (a b c A B C : ℝ) : (a + b + c) - (A + B + C) =
      (a - A + (b - B)) + (c - C) := by ring
  rw [heq]
  linarith [hprod (l - k) l, hprod l (l + k), hprod (l - k) (l + k)]

/-- The inverse denominator factor varies uniformly with the walk parameter under
a common resolvent bound. The hypotheses are bounds on the actual canonical resolvents. -/
theorem abs_bootstrapTripleProduct_inv_sub_le (hd : 0 < d) {lam mu M : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) (hmu : mu ∈ Ico (0 : ℝ) 1)
    (hClam : ∀ z : Fin d → ℝ, nearestNeighborResolvent lam z ≤ M)
    (hCmu : ∀ z : Fin d → ℝ, nearestNeighborResolvent mu z ≤ M) (k l : Fin d → ℝ) :
    |(bootstrapTripleProduct lam k l)⁻¹ - (bootstrapTripleProduct mu k l)⁻¹| ≤
      (32 / 3 : ℝ) * M ^ 3 * |lam - mu| := by
  have hlamV := three_quarters_le_bootstrapTripleProduct hd hlam k l
  have hmuV := three_quarters_le_bootstrapTripleProduct hd hmu k l
  have hlampos : 0 < bootstrapTripleProduct lam k l := by linarith
  have hmupos : 0 < bootstrapTripleProduct mu k l := by linarith
  have hinvlam : (bootstrapTripleProduct lam k l)⁻¹ ≤ (4 / 3 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) hlamV
    norm_num [one_div] at h ⊢
    exact h
  have hinvmu : (bootstrapTripleProduct mu k l)⁻¹ ≤ (4 / 3 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) hmuV
    norm_num [one_div] at h ⊢
    exact h
  have hprod : (bootstrapTripleProduct lam k l)⁻¹ *
      (bootstrapTripleProduct mu k l)⁻¹ ≤ (16 / 9 : ℝ) := by
    nlinarith [mul_le_mul hinvlam hinvmu (inv_pos.mpr hmupos).le (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  rw [← Real.dist_eq, dist_inv_inv₀ hlampos.ne' hmupos.ne', Real.dist_eq,
    Real.norm_of_nonneg hlampos.le, Real.norm_of_nonneg hmupos.le, div_eq_mul_inv, mul_inv]
  calc
    _ ≤ (6 * M ^ 3 * |lam - mu|) * (16 / 9 : ℝ) :=
      mul_le_mul (abs_tripleProduct_sub_le hd hlam hmu hClam hCmu k l) hprod
        (mul_nonneg (inv_pos.mpr hlampos).le (inv_pos.mpr hmupos).le)
        (le_trans (abs_nonneg _) (abs_tripleProduct_sub_le hd hlam hmu hClam hCmu k l))
    _ = _ := by ring

private theorem eventually_uniform_mul_sub_lt {α I : Type*} {a : Filter α}
    {F G : α → I → ℝ} {f g : I → ℝ} {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : ∀ i, |f i| ≤ M) (hGbound : ∀ᶠ b in a, ∀ i, |G b i| ≤ N)
    (hF : ∀ ε : ℝ, 0 < ε → ∀ᶠ b in a, ∀ i, |F b i - f i| < ε)
    (hG : ∀ ε : ℝ, 0 < ε → ∀ᶠ b in a, ∀ i, |G b i - g i| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ b in a, ∀ i, |F b i * G b i - f i * g i| < ε := by
  intro ε hε
  let δ := ε / (2 * (N + M + 1))
  have hden : 0 < 2 * (N + M + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : 2 * (N + M + 1) * δ = ε := by
    dsimp [δ]
    exact mul_div_cancel₀ ε hden.ne'
  filter_upwards [hGbound, hF δ hδ, hG δ hδ] with b hb hFb hGb i
  have hbound : |F b i * G b i - f i * g i| ≤ δ * N + M * δ := by
    calc
      _ = |(F b i - f i) * G b i + f i * (G b i - g i)| := by congr 1; ring
      _ ≤ |(F b i - f i) * G b i| + |f i * (G b i - g i)| := abs_add_le _ _
      _ = |F b i - f i| * |G b i| + |f i| * |G b i - g i| := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul (hFb i).le (hb i) (abs_nonneg _) hδ.le)
        (mul_le_mul (hf i) (hGb i).le (abs_nonneg _) hM)
  nlinarith

/-- The canonical third Fourier bootstrap function is continuous at every finite-
susceptibility parameter of a transitive finite-range intensity family. The complete
normalization `U = 200 (1 - D) V` is used, with its local bounds proved from susceptibility. -/
theorem continuousAt_fourierDifferenceSup_intensity (hd : 0 < d)
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => fourierDifferenceSup (intensityProfile J b)) β := by
  let q := fun b : ℝ≥0 => intensityProfile J b
  let lam := fun b : ℝ≥0 => susceptibilityWalkParameter (q b)
  let P := {p : (Fin d → ℝ) × (Fin d → ℝ) // 0 < 1 - nearestNeighborSymbol p.1}
  let A := fun (b : ℝ≥0) (p : P) =>
    |(fwdDiff p.1.1)^[2] (tauFourier (q b)) (p.1.2 - p.1.1)| /
      ∑ i, (1 - cos (p.1.1 i))
  let B := fun (b : ℝ≥0) (p : P) => (bootstrapTripleProduct (lam b) p.1.1 p.1.2)⁻¹
  let Q := fun (b : ℝ≥0) (p : P) =>
    |(fwdDiff p.1.1)^[2] (tauFourier (q b)) (p.1.2 - p.1.1)| /
      bootstrapMajorant (lam b) p.1.1 p.1.2
  change ContinuousAt (fun b => ⨆ p : P, Q b p) β
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have : Nonempty P := by
    refine ⟨⟨(fun _ => Real.pi, 0), ?_⟩⟩
    simp [nearestNeighborSymbol, hd0]
  have hdelta (p : P) : 0 < ∑ i, (1 - cos (p.1.1 i)) := by
    rw [sum_one_sub_cos_eq_mul_deficit hd]
    exact mul_pos hdpos p.2
  have hlam (b : ℝ≥0) (hb : chi (q b) 0 ≠ ⊤) : lam b ∈ Ico (0 : ℝ) 1 :=
    susceptibilityWalkParameter_mem_Ico (q b) hb
  have hB (b : ℝ≥0) (hb : chi (q b) 0 ≠ ⊤) (p : P) : |B b p| ≤ (4 / 3 : ℝ) := by
    have hV := three_quarters_le_bootstrapTripleProduct hd (hlam b hb) p.1.1 p.1.2
    have hVpos : 0 < bootstrapTripleProduct (lam b) p.1.1 p.1.2 := by linarith
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) hV
    norm_num [one_div] at h
    simpa only [B, abs_of_pos (inv_pos.mpr hVpos)] using h
  have hQ (b : ℝ≥0) (hb : chi (q b) 0 ≠ ⊤) (p : P) :
      Q b p = ((d : ℝ) / 200) * (A b p * B b p) := by
    have hV := three_quarters_le_bootstrapTripleProduct hd (hlam b hb) p.1.1 p.1.2
    have hVne : bootstrapTripleProduct (lam b) p.1.1 p.1.2 ≠ 0 := by linarith
    dsimp only [Q, A, B]
    rw [sum_one_sub_cos_eq_mul_deficit hd, bootstrapMajorant_def]
    field_simp [hd0, p.2.ne', hVne]
  have hrow : Summable fun x => (tau (q β) 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi)
  have hweight : Summable fun x => (1 + ‖x‖ ^ 2) * (tau (q β) 0 x).toReal := by
    simpa only [sub_zero] using
      summable_one_add_norm_sq_mul_tau_intensity J hJ 0 hR hrange hchi
  have hw2 : Summable fun x => |(tau (q β) 0 x).toReal| * ‖x‖ ^ 2 := by
    apply hweight.of_norm_bounded
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)),
      abs_of_nonneg ENNReal.toReal_nonneg]
    nlinarith [ENNReal.toReal_nonneg (a := tau (q β) 0 x)]
  let K := 2 * (d : ℝ) * ∑' x, |(tau (q β) 0 x).toReal| * ‖x‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg (by norm_num) hdpos.le)
      (tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hA (p : P) : |A β p| ≤ K := by
    have hraw := abs_tsum_lattice_cos_second_difference_le_norm_sq hrow hw2 p.1.2 p.1.1
    have hAnonneg : 0 ≤ A β p := div_nonneg (abs_nonneg _) (hdelta p).le
    rw [abs_of_nonneg hAnonneg]
    apply (div_le_iff₀ (hdelta p)).2
    simpa only [fwdDiff_two_at_sub, tauFourier_def, Pi.sub_apply, Pi.add_apply, K] using hraw
  have hAcont : ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ≥0 in 𝓝 β, ∀ p : P,
      |A b p - A β p| < ε := by
    intro ε hε
    filter_upwards [eventually_normalized_fourier_second_difference_sub_lt
      J hJ hL hR hrange hchi ε hε] with b hb p
    have hp := hb p.1.2 p.1.1 (hdelta p)
    have hle : |A b p - A β p| ≤
        |((fwdDiff p.1.1)^[2] (tauFourier (q b)) (p.1.2 - p.1.1) -
          (fwdDiff p.1.1)^[2] (tauFourier (q β)) (p.1.2 - p.1.1)) /
          ∑ i, (1 - cos (p.1.1 i))| := by
      dsimp only [A]
      rw [← sub_div, abs_div, abs_div, abs_of_pos (hdelta p)]
      exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) (hdelta p).le
    apply hle.trans_lt
    simpa only [fwdDiff_two_at_sub, tauFourier_def, q] using hp
  obtain ⟨η, hη, hupper⟩ := exists_pos_chi_intensity_add_lt_top
    (fun x => hJ 0 x) hL hchi.lt_top
  let M := (chi (q (β + η)) 0).toReal
  have hnear : ∀ᶠ b : ℝ≥0 in 𝓝 β, chi (q b) 0 ≠ ⊤ ∧ (chi (q b) 0).toReal ≤ M := by
    filter_upwards [Iio_mem_nhds (lt_add_of_pos_right β hη)] with b hb
    have hc := chi_mono (intensityProfile_mono J hb.le) 0
    exact ⟨ne_top_of_le_ne_top hupper.ne hc, ENNReal.toReal_mono hupper.ne hc⟩
  have hbaseM : (chi (q β) 0).toReal ≤ M := ENNReal.toReal_mono hupper.ne
    (chi_mono (intensityProfile_mono J
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ η from zero_le))) 0)
  have hcontlam : ContinuousAt lam β :=
    continuousAt_susceptibilityWalkParameter_intensity J hJ hL hchi
  have hBcont : ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ≥0 in 𝓝 β, ∀ p : P,
      |B b p - B β p| < ε := by
    intro ε hε
    have hzero : Tendsto (fun b : ℝ≥0 => (32 / 3 : ℝ) * M ^ 3 * |lam b - lam β|)
        (𝓝 β) (𝓝 0) := by
      simpa only [sub_self, abs_zero, mul_zero] using
        ((hcontlam.tendsto.sub_const (lam β)).abs.const_mul ((32 / 3 : ℝ) * M ^ 3))
    filter_upwards [hnear, hzero.eventually (Iio_mem_nhds hε)] with b hb hsmall p
    exact (abs_bootstrapTripleProduct_inv_sub_le hd (hlam b hb.1) (hlam β hchi)
      (fun z => (nearestNeighborResolvent_le_chi hd (q b) hb.1 z).trans hb.2)
      (fun z => (nearestNeighborResolvent_le_chi hd (q β) hchi z).trans hbaseM)
      p.1.1 p.1.2).trans_lt hsmall
  have hproduct := eventually_uniform_mul_sub_lt hK (by norm_num : (0 : ℝ) ≤ 4 / 3) hA
    (hnear.mono fun b hb p => hB b hb.1 p) hAcont hBcont
  have hscale : 0 < (d : ℝ) / 200 := div_pos hdpos (by norm_num)
  have hbounded : BddAbove (range (Q β)) := by
    refine ⟨((d : ℝ) / 200) * (K * (4 / 3)), ?_⟩
    rintro _ ⟨p, rfl⟩
    rw [hQ β hchi p]
    apply mul_le_mul_of_nonneg_left _ hscale.le
    exact (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul (hA p) (hB β hchi p) (abs_nonneg _) hK))
  apply tendsto_ciSup_of_uniform_abs_sub_lt hbounded
  intro ε hε
  filter_upwards [hnear, hproduct (ε / ((d : ℝ) / 200)) (div_pos hε hscale)]
    with b hb hprod p
  rw [hQ b hb.1 p, hQ β hchi p, ← mul_sub, abs_mul, abs_of_pos hscale]
  exact (mul_lt_mul_of_pos_left (hprod p) hscale).trans_eq (mul_div_cancel₀ ε hscale.ne')

end PercLib.Percolation.Bond.Lace
