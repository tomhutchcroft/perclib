/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourierDifference
public import PercLib.Percolation.Bond.SpatialMoments.IntensityContinuity

/-!
# Uniform continuity of normalized Fourier second differences

For a transitive finite-range intensity model, finite susceptibility gives weighted
absolute continuity of the actual two-point function. The lattice cosine estimate
turns this into uniform continuity of the Fourier second difference divided by the
coordinate cosine deficit. Only frequencies with positive deficit enter the quotient.

## Main results

* `summable_one_add_norm_sq_mul_tau_intensity`: the actual finite-susceptibility weighted row.
* `eventually_normalized_fourier_second_difference_sub_lt`: uniform control over both
  frequencies at every finite-susceptibility intensity, including zero.
* `continuousAt_normalized_fourier_second_difference_sup`: continuity of the normalized
  absolute supremum in positive dimension, with boundedness derived from spatial moments.
-/

@[expose] public section

noncomputable section

open Filter Set Real PercLib.Models.Site PercLib.Analysis
open scoped Topology ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {d : ℕ}

private theorem abs_normalized_lattice_second_difference_sub_le
    {f g : (Fin d → ℤ) → ℝ} (hf : Summable f) (hg : Summable g)
    (hw : Summable (fun x => (1 + ‖x‖ ^ 2) * |f x - g x|))
    (l k : Fin d → ℝ) (hk : 0 < ∑ i, (1 - cos (k i))) :
    let T := fun (h : (Fin d → ℤ) → ℝ) (z : Fin d → ℝ) =>
      ∑' x, h x * cos (∑ i, z i * (x i : ℝ))
    |((T f (l - k) + T f (l + k) - 2 * T f l) -
        (T g (l - k) + T g (l + k) - 2 * T g l)) / ∑ i, (1 - cos (k i))| ≤
      2 * (d : ℝ) * ∑' x, (1 + ‖x‖ ^ 2) * |f x - g x| := by
  dsimp only
  have hle (x : Fin d → ℤ) : |f x - g x| * ‖x‖ ^ 2 ≤
      (1 + ‖x‖ ^ 2) * |f x - g x| := by
    nlinarith [abs_nonneg (f x - g x)]
  have hw2 : Summable (fun x => |f x - g x| * ‖x‖ ^ 2) := by
    apply hw.of_norm_bounded
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact hle x
  have hmass := hw2.tsum_le_tsum hle hw
  have h := abs_tsum_lattice_cos_second_difference_le_norm_sq (hf.sub hg) hw2 l k
  have hdiff (z : Fin d → ℝ) :
      (∑' x, (f x - g x) * cos (∑ i, z i * (x i : ℝ))) =
        (∑' x, f x * cos (∑ i, z i * (x i : ℝ))) -
        ∑' x, g x * cos (∑ i, z i * (x i : ℝ)) := by
    simp_rw [sub_mul]
    exact (summable_mul_cos hf _).tsum_sub (summable_mul_cos hg _)
  change |((∑' x, (f x - g x) * cos (∑ i, (l - k) i * (x i : ℝ))) +
      (∑' x, (f x - g x) * cos (∑ i, (l + k) i * (x i : ℝ))) -
      2 * (∑' x, (f x - g x) * cos (∑ i, l i * (x i : ℝ))))| ≤ _ at h
  rw [hdiff, hdiff, hdiff] at h
  rw [abs_div, abs_of_pos hk]
  apply (div_le_iff₀ hk).2
  calc
    _ ≤ 2 * (d : ℝ) * (∑' x, |f x - g x| * ‖x‖ ^ 2) *
        ∑ i, (1 - cos (k i)) := by
      convert h using 1
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by positivity)) hk.le

/-- In a transitive finite-range intensity family, finite susceptibility gives
a summable two-point row weighted by one plus squared displacement. -/
theorem summable_one_add_norm_sq_mul_tau_intensity
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (o : LatticeSite d) {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) o ≠ ⊤) :
    Summable fun x => (1 + ‖x - o‖ ^ 2) * (tau (intensityProfile J β) o x).toReal := by
  apply summable_one_add_norm_sq_mul_tau_toReal _ o hchi
  apply (spatialMoment_sq_lt_top_of_finiteRange_of_transitive _ o hR ?_ ?_ hchi).ne
  · intro x y hxy
    apply Subtype.ext
    simp [intensityProfile, hrange x y hxy]
  · intro x y
    obtain ⟨σ, hσ, hp⟩ := hJ x y
    exact ⟨σ, hσ, intensityProfile_map_eq hp β⟩

/-- The Fourier second differences of the actual two-point functions, divided by
the coordinate cosine deficit, vary uniformly over both frequencies near every
finite-susceptibility intensity. The intensity parameter may be zero. -/
theorem eventually_normalized_fourier_second_difference_sub_lt
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    let T := fun (b : ℝ≥0) (z : Fin d → ℝ) =>
      ∑' x, (tau (intensityProfile J b) 0 x).toReal * cos (∑ i, z i * (x i : ℝ))
    ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ≥0 in 𝓝 β, ∀ l k : Fin d → ℝ,
      0 < ∑ i, (1 - cos (k i)) →
      |((T b (l - k) + T b (l + k) - 2 * T b l) -
          (T β (l - k) + T β (l + k) - 2 * T β l)) / ∑ i, (1 - cos (k i))| < ε := by
  dsimp only
  intro ε hε
  have hweight (b : ℝ≥0) (hb : chi (intensityProfile J b) 0 ≠ ⊤) :
      Summable fun x => (1 + ‖x‖ ^ 2) * (tau (intensityProfile J b) 0 x).toReal := by
    simpa only [sub_zero] using
      summable_one_add_norm_sq_mul_tau_intensity J hJ 0 hR hrange hb
  have hbase : Summable fun x => (tau (intensityProfile J β) 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi)
  obtain ⟨η, hη, hupper⟩ := exists_pos_chi_intensity_add_lt_top
    (fun x => hJ 0 x) hL hchi.lt_top
  have hnear : ∀ᶠ b : ℝ≥0 in 𝓝 β, chi (intensityProfile J b) 0 ≠ ⊤ := by
    filter_upwards [Iio_mem_nhds (lt_add_of_pos_right β hη)] with b hb
    exact ne_top_of_le_ne_top hupper.ne (chi_mono (intensityProfile_mono J hb.le) 0)
  have hzero : Tendsto
      (fun b : ℝ≥0 => 2 * (d : ℝ) * ∑' x, (1 + ‖x‖ ^ 2) *
        |(tau (intensityProfile J b) 0 x).toReal - (tau (intensityProfile J β) 0 x).toReal|)
      (𝓝 β) (𝓝 0) := by
    simpa only [sub_zero, mul_zero] using
      (tendsto_norm_sq_weighted_tau_intensity J hJ 0 hL hR hrange hchi).const_mul (2 * (d : ℝ))
  have hsmall := hzero.eventually (Iio_mem_nhds hε)
  filter_upwards [hnear, hsmall] with b hb hsmall l k hk
  have hrow : Summable fun x => (tau (intensityProfile J b) 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hb)
  have hwdiff : Summable fun x => (1 + ‖x‖ ^ 2) *
      |(tau (intensityProfile J b) 0 x).toReal - (tau (intensityProfile J β) 0 x).toReal| := by
    convert ((hweight b hb).sub (hweight β hchi)).abs using 1
    ext x
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2)]
  exact (abs_normalized_lattice_second_difference_sub_le hrow hbase hwdiff l k hk).trans_lt hsmall

private theorem tendsto_ciSup_of_uniform_abs_sub_lt {α I : Type*} [Nonempty I]
    {F : α → I → ℝ} {g : I → ℝ} {a : Filter α} (hg : BddAbove (range g))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ b in a, ∀ i, |F b i - g i| < ε) :
    Tendsto (fun b => ⨆ i, F b i) a (𝓝 (⨆ i, g i)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with b hb
  have hupper (i : I) : F b i ≤ (⨆ j, g j) + ε / 2 := by
    have hgi := le_ciSup hg i
    have hi := (abs_lt.mp (hb i)).2
    linarith
  have hbdd : BddAbove (range (F b)) := by
    refine ⟨(⨆ j, g j) + ε / 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hupper i
  have hsupupper : (⨆ i, F b i) ≤ (⨆ i, g i) + ε / 2 := ciSup_le hupper
  have hsuplower : (⨆ i, g i) ≤ (⨆ i, F b i) + ε / 2 := by
    apply ciSup_le
    intro i
    have hFi := le_ciSup hbdd i
    have hi := (abs_lt.mp (hb i)).1
    linarith
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- In positive dimension, the supremum of the absolute Fourier second difference
divided by the coordinate cosine deficit is continuous at every finite-susceptibility
intensity. Its boundedness follows from the second spatial moment; no maximizing
frequency or supremum-finiteness hypothesis is required. -/
theorem continuousAt_normalized_fourier_second_difference_sup (hd : 0 < d)
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    let T := fun (b : ℝ≥0) (z : Fin d → ℝ) =>
      ∑' x, (tau (intensityProfile J b) 0 x).toReal * cos (∑ i, z i * (x i : ℝ))
    ContinuousAt (fun b => ⨆ p : {p : (Fin d → ℝ) × (Fin d → ℝ) //
        0 < ∑ i, (1 - cos (p.2 i))},
      |T b (p.1.1 - p.1.2) + T b (p.1.1 + p.1.2) - 2 * T b p.1.1| /
        ∑ i, (1 - cos (p.1.2 i))) β := by
  let T := fun (b : ℝ≥0) (z : Fin d → ℝ) =>
    ∑' x, (tau (intensityProfile J b) 0 x).toReal * cos (∑ i, z i * (x i : ℝ))
  let P := {p : (Fin d → ℝ) × (Fin d → ℝ) // 0 < ∑ i, (1 - cos (p.2 i))}
  let Q := fun (b : ℝ≥0) (p : P) =>
    |T b (p.1.1 - p.1.2) + T b (p.1.1 + p.1.2) - 2 * T b p.1.1| /
      ∑ i, (1 - cos (p.1.2 i))
  change ContinuousAt (fun b => ⨆ p : P, Q b p) β
  have : Nonempty P := by
    refine ⟨⟨(0, fun _ => Real.pi), ?_⟩⟩
    dsimp
    simp only [cos_pi, sub_neg_eq_add, one_add_one_eq_two, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    positivity
  have hrow : Summable fun x => (tau (intensityProfile J β) 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi)
  have hweight : Summable fun x => (1 + ‖x‖ ^ 2) *
      |(tau (intensityProfile J β) 0 x).toReal - 0| := by
    simpa only [sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] using
      summable_one_add_norm_sq_mul_tau_intensity J hJ 0 hR hrange hchi
  have hbounded : BddAbove (range (Q β)) := by
    refine ⟨2 * (d : ℝ) * ∑' x, (1 + ‖x‖ ^ 2) *
      |(tau (intensityProfile J β) 0 x).toReal - 0|, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hp := abs_normalized_lattice_second_difference_sub_le
      (g := fun _ => 0) hrow summable_zero hweight p.1.1 p.1.2 p.2
    simpa only [Q, T, zero_mul, tsum_zero, add_zero, mul_zero, sub_zero,
      abs_div, abs_of_pos p.2] using hp
  apply tendsto_ciSup_of_uniform_abs_sub_lt hbounded
  intro ε hε
  filter_upwards [eventually_normalized_fourier_second_difference_sub_lt
    J hJ hL hR hrange hchi ε hε] with b hb p
  have hp := hb p.1.1 p.1.2 p.2
  have hle : |Q b p - Q β p| ≤
      |((T b (p.1.1 - p.1.2) + T b (p.1.1 + p.1.2) - 2 * T b p.1.1) -
        (T β (p.1.1 - p.1.2) + T β (p.1.1 + p.1.2) - 2 * T β p.1.1)) /
        ∑ i, (1 - cos (p.1.2 i))| := by
    dsimp only [Q]
    rw [← sub_div, abs_div, abs_div, abs_of_pos p.2]
    exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) p.2.le
  exact hle.trans_lt hp

end PercLib.Percolation.Bond
