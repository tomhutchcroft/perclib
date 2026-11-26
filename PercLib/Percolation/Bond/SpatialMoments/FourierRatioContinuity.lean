/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.SpatialMoments.FourierContinuity

/-!
# Continuity of the actual Fourier-ratio supremum

Comparable finite-susceptibility profiles have an exact absolute row difference equal
to their susceptibility difference. Actual susceptibility continuity in a transitive
intensity family therefore gives uniform continuity of its cosine transform. This
proves continuity of the supremum of the absolute Fourier ratio, without requiring
finite range, Fourier positivity, or a supremum-finiteness premise.

## Main results

* `tsum_abs_tau_toReal_sub_eq_abs_chi_toReal_sub`: the exact comparable-profile row identity.
* `one_sub_inv_toReal_chi_mem_Ico`: the actual susceptibility parameter lies in `[0,1)`.
* `eventually_fourier_ratio_sub_lt`: uniform continuity over all real frequencies.
* `continuousAt_fourier_ratio_sup`: continuity of the actual absolute Fourier-ratio supremum.
-/

@[expose] public section

noncomputable section

open Filter Set Real PercLib.Models.Site PercLib.Analysis
open scoped Topology ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- For comparable profiles with finite susceptibilities, the absolute difference
of the two-point rows sums to the absolute susceptibility difference. -/
theorem tsum_abs_tau_toReal_sub_eq_abs_chi_toReal_sub
    {q r : Sym2 V → unitInterval} (hcomp : q ≤ r ∨ r ≤ q) (o : V)
    (hq : chi q o ≠ ⊤) (hr : chi r o ≠ ⊤) :
    (∑' x, |(tau q o x).toReal - (tau r o x).toReal|) =
      |(chi q o).toReal - (chi r o).toReal| := by
  have hforward {p s : Sym2 V → unitInterval} (hps : p ≤ s) (hs : chi s o ≠ ⊤) :
      (∑' x, |(tau s o x).toReal - (tau p o x).toReal|) =
        |(chi s o).toReal - (chi p o).toReal| := by
    have hp : chi p o ≠ ⊤ := ne_top_of_le_ne_top hs (chi_mono hps o)
    have ht (t : Sym2 V → unitInterval) (x : V) : tau t o x ≠ ⊤ :=
      ((tau_le_one t o x).trans_lt ENNReal.one_lt_top).ne
    have hsum (t : Sym2 V → unitInterval) (h : chi t o ≠ ⊤) :
        Summable fun x => (tau t o x).toReal :=
      ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact h)
    have hnonneg (x : V) : 0 ≤ (tau s o x).toReal - (tau p o x).toReal :=
      sub_nonneg.mpr (ENNReal.toReal_mono (ht s x) (tau_mono hps o x))
    simp_rw [abs_of_nonneg (hnonneg _)]
    rw [(hsum s hs).tsum_sub (hsum p hp),
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hs (chi_mono hps o)))]
    simp only [chi_eq_tsum_tau, ENNReal.tsum_toReal_eq (ht s), ENNReal.tsum_toReal_eq (ht p)]
  rcases hcomp with h | h
  · simpa only [abs_sub_comm] using hforward h hr
  · exact hforward h hq

/-- At finite susceptibility the actual parameter `1 - χ⁻¹` lies in `[0,1)`. -/
theorem one_sub_inv_toReal_chi_mem_Ico (q : Sym2 V → unitInterval) (o : V)
    (hchi : chi q o ≠ ⊤) : 1 - (chi q o).toReal⁻¹ ∈ Ico (0 : ℝ) 1 := by
  have h1 : 1 ≤ (chi q o).toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hchi (one_le_chi q o)
  have hpos : 0 < (chi q o).toReal := lt_of_lt_of_le zero_lt_one h1
  have hinv : (chi q o).toReal⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one h1
  exact ⟨sub_nonneg.mpr hinv, by linarith [inv_pos.mpr hpos]⟩

private theorem abs_cosine_tsum_le {ι : Type*} {f : ι → ℝ}
    (hf : Summable f) (t : ι → ℝ) :
    |∑' x, f x * cos (t x)| ≤ ∑' x, |f x| := by
  rw [← Real.norm_eq_abs]
  apply (summable_mul_cos hf t).hasSum.norm_le_of_bounded hf.abs.hasSum
  intro x
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

private theorem abs_one_sub_mul_le_two {lam D : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) (hD : |D| ≤ 1) : |1 - lam * D| ≤ 2 := by
  calc
    _ ≤ |(1 : ℝ)| + |lam * D| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (1 : ℝ) 0 (lam * D)
    _ = 1 + lam * |D| := by rw [abs_one, abs_mul, abs_of_nonneg hlam.1]
    _ ≤ 1 + lam := add_le_add le_rfl (mul_le_of_le_one_right hlam.1 hD)
    _ ≤ 2 := by linarith [hlam.2]

private theorem abs_ratio_sub_le {a b lam mu D A B : ℝ}
    (hlam : lam ∈ Ico (0 : ℝ) 1) (hD : |D| ≤ 1)
    (ha : |a - b| ≤ A) (hb : |b| ≤ B) :
    |a * (1 - lam * D) - b * (1 - mu * D)| ≤ 2 * A + B * |lam - mu| := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  calc
    _ = |(a - b) * (1 - lam * D) + b * (mu - lam) * D| := by congr 1; ring
    _ ≤ |(a - b) * (1 - lam * D)| + |b * (mu - lam) * D| := abs_add_le _ _
    _ = |a - b| * |1 - lam * D| + |b| * |lam - mu| * |D| := by
      rw [abs_mul, abs_mul, abs_mul, abs_sub_comm mu lam]
    _ ≤ A * 2 + B * |lam - mu| := by
      apply add_le_add
      · exact mul_le_mul ha (abs_one_sub_mul_le_two hlam hD) (abs_nonneg _) hA
      · exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD).trans
          (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    _ = _ := by ring

variable {d : ℕ}

private theorem abs_average_cos_le_one (hd : 0 < d) (k : Fin d → ℝ) :
    |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ≤ 1 := by
  have hdim : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : |∑ i, cos (k i)| ≤ (d : ℝ) := by
    calc
      _ ≤ ∑ i, |cos (k i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => abs_cos_le_one (k i)
      _ = _ := by simp
  rw [abs_mul, abs_of_pos (inv_pos.mpr hdim)]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hdim.le)).trans_eq
    (inv_mul_cancel₀ hdim.ne')

private theorem abs_tau_cosine_tsum_le_chi (q : Sym2 (LatticeSite d) → unitInterval)
    (hchi : chi q 0 ≠ ⊤) (k : Fin d → ℝ) :
    |∑' x, (tau q 0 x).toReal * cos (∑ i, k i * (x i : ℝ))| ≤ (chi q 0).toReal := by
  have hs : Summable fun x => (tau q 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi)
  have ht (x : LatticeSite d) : tau q 0 x ≠ ⊤ :=
    ((tau_le_one q 0 x).trans_lt ENNReal.one_lt_top).ne
  simpa only [abs_of_nonneg ENNReal.toReal_nonneg, chi_eq_tsum_tau,
    ENNReal.tsum_toReal_eq ht] using abs_cosine_tsum_le hs (fun x => ∑ i, k i * (x i : ℝ))

/-- The actual Fourier ratio varies uniformly over every real frequency near a
finite-susceptibility intensity. Finite range and Fourier positivity are not needed. -/
theorem eventually_fourier_ratio_sub_lt (hd : 0 < d)
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    let T := fun (b : ℝ≥0) (k : Fin d → ℝ) =>
      ∑' x, (tau (intensityProfile J b) 0 x).toReal * cos (∑ i, k i * (x i : ℝ))
    let lam := fun b : ℝ≥0 => 1 - (chi (intensityProfile J b) 0).toReal⁻¹
    let D := fun k : Fin d → ℝ => (d : ℝ)⁻¹ * ∑ i, cos (k i)
    ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ≥0 in 𝓝 β, ∀ k : Fin d → ℝ,
      |T b k * (1 - lam b * D k) - T β k * (1 - lam β * D k)| < ε := by
  dsimp only
  intro ε hε
  let chiR := fun b : ℝ≥0 => (chi (intensityProfile J b) 0).toReal
  let lam := fun b : ℝ≥0 => 1 - (chiR b)⁻¹
  have hcont := continuousAt_toReal_chi_intensity J hJ 0 hL hchi
  change ContinuousAt chiR β at hcont
  have hpos : 0 < chiR β := by
    have h1 : (1 : ℝ) ≤ chiR β := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono hchi (one_le_chi (intensityProfile J β) 0)
    exact lt_of_lt_of_le zero_lt_one h1
  have hlam : ContinuousAt lam β := continuousAt_const.sub (hcont.inv₀ hpos.ne')
  have hzero : Tendsto (fun b => 2 * |chiR b - chiR β| +
      chiR β * |lam b - lam β|) (𝓝 β) (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using
      ((hcont.tendsto.sub_const (chiR β)).abs.const_mul 2).add
        ((hlam.tendsto.sub_const (lam β)).abs.const_mul (chiR β))
  obtain ⟨η, hη, hupper⟩ := exists_pos_chi_intensity_add_lt_top
    (fun x => hJ 0 x) hL hchi.lt_top
  have hnear : ∀ᶠ b : ℝ≥0 in 𝓝 β, chi (intensityProfile J b) 0 ≠ ⊤ := by
    filter_upwards [Iio_mem_nhds (lt_add_of_pos_right β hη)] with b hb
    exact ne_top_of_le_ne_top hupper.ne (chi_mono (intensityProfile_mono J hb.le) 0)
  filter_upwards [hnear, hzero.eventually (Iio_mem_nhds hε)] with b hb hsmall k
  have hsum (c : ℝ≥0) (hc : chi (intensityProfile J c) 0 ≠ ⊤) :
      Summable fun x => (tau (intensityProfile J c) 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hc)
  have hcomp : intensityProfile J b ≤ intensityProfile J β ∨
      intensityProfile J β ≤ intensityProfile J b := by
    rcases le_total b β with h | h
    · exact Or.inl (intensityProfile_mono J h)
    · exact Or.inr (intensityProfile_mono J h)
  have hdiff : |(∑' x, (tau (intensityProfile J b) 0 x).toReal *
      cos (∑ i, k i * (x i : ℝ))) - ∑' x, (tau (intensityProfile J β) 0 x).toReal *
      cos (∑ i, k i * (x i : ℝ))| ≤ |chiR b - chiR β| := by
    have h := abs_cosine_tsum_le ((hsum b hb).sub (hsum β hchi))
      (fun x => ∑ i, k i * (x i : ℝ))
    simp_rw [sub_mul] at h
    rw [(summable_mul_cos (hsum b hb) _).tsum_sub
      (summable_mul_cos (hsum β hchi) _)] at h
    exact h.trans_eq (tsum_abs_tau_toReal_sub_eq_abs_chi_toReal_sub hcomp 0 hb hchi)
  exact (abs_ratio_sub_le (one_sub_inv_toReal_chi_mem_Ico _ 0 hb)
    (abs_average_cos_le_one hd k) hdiff (abs_tau_cosine_tsum_le_chi _ hchi k)).trans_lt hsmall

/-- The supremum of the absolute actual Fourier ratio is continuous at every
finite-susceptibility intensity of a transitive finite-row model. Its boundedness
is derived from `|T(k)| ≤ χ` and `0 ≤ 1 - χ⁻¹ < 1`. -/
theorem continuousAt_fourier_ratio_sup (hd : 0 < d)
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    let T := fun (b : ℝ≥0) (k : Fin d → ℝ) =>
      ∑' x, (tau (intensityProfile J b) 0 x).toReal * cos (∑ i, k i * (x i : ℝ))
    let lam := fun b : ℝ≥0 => 1 - (chi (intensityProfile J b) 0).toReal⁻¹
    let D := fun k : Fin d → ℝ => (d : ℝ)⁻¹ * ∑ i, cos (k i)
    ContinuousAt (fun b => ⨆ k : Fin d → ℝ, |T b k * (1 - lam b * D k)|) β := by
  let T := fun (b : ℝ≥0) (k : Fin d → ℝ) =>
    ∑' x, (tau (intensityProfile J b) 0 x).toReal * cos (∑ i, k i * (x i : ℝ))
  let lam := fun b : ℝ≥0 => 1 - (chi (intensityProfile J b) 0).toReal⁻¹
  let D := fun k : Fin d → ℝ => (d : ℝ)⁻¹ * ∑ i, cos (k i)
  change ContinuousAt (fun b => ⨆ k : Fin d → ℝ, |T b k * (1 - lam b * D k)|) β
  have hbounded : BddAbove (range (fun k : Fin d → ℝ => |T β k * (1 - lam β * D k)|)) := by
    refine ⟨2 * (chi (intensityProfile J β) 0).toReal, ?_⟩
    rintro _ ⟨k, rfl⟩
    change |T β k * (1 - lam β * D k)| ≤ 2 * (chi (intensityProfile J β) 0).toReal
    rw [abs_mul]
    calc
      _ ≤ (chi (intensityProfile J β) 0).toReal * 2 :=
        mul_le_mul (abs_tau_cosine_tsum_le_chi _ hchi k)
          (abs_one_sub_mul_le_two (one_sub_inv_toReal_chi_mem_Ico _ 0 hchi)
            (abs_average_cos_le_one hd k)) (abs_nonneg _) ENNReal.toReal_nonneg
      _ = _ := by ring
  apply tendsto_ciSup_of_uniform_abs_sub_lt hbounded
  intro ε hε
  filter_upwards [eventually_fourier_ratio_sub_lt hd J hJ hL hchi ε hε] with b hb k
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans_lt (hb k)

end PercLib.Percolation.Bond
