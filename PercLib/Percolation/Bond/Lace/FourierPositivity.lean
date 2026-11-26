/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: finite-cluster averaging by the mass-transport principle,
followed by the character Gram identity.
-/
module

public import PercLib.Percolation.Bond.ClusterMassTransport
public import PercLib.Percolation.Bond.IndependentLayer
public import PercLib.Percolation.Bond.Lace.Fourier

/-!
# Positivity of the two-point Fourier transform

For a translation-invariant bond law with finite susceptibility, the Fourier transform
of its two-point function has nonnegative real part. Finite-cluster mass transport
averages the nonnegative observable `∑_{x ∈ C_u} (1 + Re ψ(x-u))`. The resulting
cluster average is at least the cluster size by the character Gram identity. Finite
susceptibility permits subtracting the common cluster-size expectation.

## Main results

* `sum_character_sub_re_eq_normSq`: the finite character Gram identity.
* `tsum_tau_mul_character_re_nonneg`: nonnegativity of the real character transform.
* `re_tsum_tau_mul_character_nonneg`: the corresponding complex-transform statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- A finite character Gram form is the squared modulus of the character sum. -/
theorem sum_character_sub_re_eq_normSq (C : Finset G) (ψ : AddChar G Circle) :
    ∑ u ∈ C, ∑ x ∈ C, (ψ (x - u) : ℂ).re =
      Complex.normSq (∑ x ∈ C, (ψ x : ℂ)) := by
  have hsub (x u : G) : (ψ (x - u) : ℂ) = (ψ x : ℂ) * star (ψ u : ℂ) := by
    calc
      _ = ((ψ x * (ψ u)⁻¹ : Circle) : ℂ) := by
        congr 1
        rw [AddChar.map_sub_eq_div, div_eq_mul_inv]
      _ = _ := by rw [Circle.coe_mul, Circle.coe_inv_eq_conj]; rfl
  have hreal (x u : G) : (ψ (x - u) : ℂ).re =
      (ψ x : ℂ).re * (ψ u : ℂ).re + (ψ x : ℂ).im * (ψ u : ℂ).im := by
    rw [hsub, Complex.star_def, Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [hreal]
  simp_rw [sum_add_distrib, ← sum_mul, ← mul_sum]
  have hre : (∑ x ∈ C, (ψ x : ℂ)).re = ∑ x ∈ C, (ψ x : ℂ).re :=
    map_sum Complex.reAddGroupHom _ _
  have him : (∑ x ∈ C, (ψ x : ℂ)).im = ∑ x ∈ C, (ψ x : ℂ).im :=
    map_sum Complex.imAddGroupHom _ _
  rw [Complex.normSq_apply, hre, him]

private theorem character_re_abs_le_one (ψ : AddChar G Circle) (x : G) :
    |(ψ x : ℂ).re| ≤ 1 := by
  simpa only [Circle.norm_coe] using Complex.abs_re_le_norm (ψ x : ℂ)

private theorem one_add_character_re_nonneg (ψ : AddChar G Circle) (x : G) :
    0 ≤ 1 + (ψ x : ℂ).re := by
  have h := (abs_le.mp (character_re_abs_le_one ψ x)).1
  linarith

private theorem card_sq_le_sum_character_weight (C : Finset G) (ψ : AddChar G Circle) :
    (C.card : ℝ≥0∞) ^ 2 ≤
      ∑ u ∈ C, ∑ x ∈ C, ENNReal.ofReal (1 + (ψ (x - u) : ℂ).re) := by
  have hreal : (C.card : ℝ) ^ 2 ≤ ∑ u ∈ C, ∑ x ∈ C, (1 + (ψ (x - u) : ℂ).re) := by
    simp_rw [sum_add_distrib]
    rw [sum_character_sub_re_eq_normSq]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    nlinarith [Complex.normSq_nonneg (∑ x ∈ C, (ψ x : ℂ))]
  have h := ENNReal.ofReal_le_ofReal hreal
  have hconvert : ENNReal.ofReal (∑ u ∈ C, ∑ x ∈ C, (1 + (ψ (x - u) : ℂ).re)) =
      ∑ u ∈ C, ∑ x ∈ C, ENNReal.ofReal (1 + (ψ (x - u) : ℂ).re) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun u _ =>
      sum_nonneg fun x _ => one_add_character_re_nonneg ψ (x - u))]
    apply sum_congr rfl
    intro u hu
    exact ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      one_add_character_re_nonneg ψ (x - u))
  rw [hconvert] at h
  simpa only [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h

section Probability

variable [Countable G]

/-- The character transform of a translation-invariant two-point function with finite
susceptibility is nonnegative. The proof uses finite clusters and mass transport. -/
theorem tsum_tau_mul_character_re_nonneg (q : Sym2 G → unitInterval)
    (hq : ∀ g x y : G, q s(g + x, g + y) = q s(x, y))
    (hchi : chi q 0 < ⊤) (ψ : AddChar G Circle) :
    0 ≤ ∑' x, (tau q 0 x).toReal * (ψ x : ℂ).re := by
  classical
  let f : Config G → G → ℝ≥0∞ := fun ω u =>
    ∑' x, (conn u x).indicator (fun _ => ENNReal.ofReal (1 + (ψ (x - u) : ℂ).re)) ω
  have hf (u : G) : Measurable fun ω => f ω u :=
    Measurable.tsum fun x => measurable_const.indicator (measurableSet_conn u x)
  have hfact (g : G) (ω : Config G) (u : G) :
      f (Sym2.map (g + ·) '' ω) (g + u) = f ω u := by
    dsimp only [f]
    rw [← (Equiv.addLeft g).tsum_eq]
    apply tsum_congr
    intro x
    have hmem := image_mem_conn_iff (Equiv.addLeft g) ω u x
    change (Sym2.map (g + ·) '' ω ∈ conn (g + u) (g + x) ↔ ω ∈ conn u x) at hmem
    simp only [Equiv.coe_addLeft, add_sub_add_left_eq_sub]
    by_cases hx : ω ∈ conn u x
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]
  have : Countable (Multiplicative G) := Countable.of_equiv G Multiplicative.ofAdd
  have havg := lintegral_indicator_cluster_finite_eq_average_law
    (Γ := Multiplicative G) q hq f hf hfact
  change
    (∫⁻ ω, {ω | (cluster ω (0 : G)).Finite}.indicator (fun ω => f ω 0) ω ∂law q) =
      ∫⁻ ω, {ω | (cluster ω (0 : G)).Finite}.indicator
        (fun ω => ((cluster ω 0).encard : ℝ≥0∞)⁻¹ *
          ∑' u, (cluster ω 0).indicator (f ω) u) ω ∂law q at havg
  have hfin := ae_cluster_finite_of_chi_lt_top hchi
  have havg' : (∫⁻ ω, f ω 0 ∂law q) =
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞)⁻¹ *
        ∑' u, (cluster ω 0).indicator (f ω) u ∂law q := by
    calc
      _ = ∫⁻ ω, {ω | (cluster ω (0 : G)).Finite}.indicator (fun ω => f ω 0) ω ∂law q := by
        apply lintegral_congr_ae
        filter_upwards [hfin] with ω hω
        rw [Set.indicator_of_mem (show ω ∈ {ω | (cluster ω (0 : G)).Finite} from hω)]
      _ = _ := havg.trans (lintegral_congr_ae (by
        filter_upwards [hfin] with ω hω
        rw [Set.indicator_of_mem (show ω ∈ {ω | (cluster ω (0 : G)).Finite} from hω)]))
  have hpoint (ω : Config G) (hω : (cluster ω 0).Finite) :
      ((cluster ω 0).encard : ℝ≥0∞) ≤ ((cluster ω 0).encard : ℝ≥0∞)⁻¹ *
        ∑' u, (cluster ω 0).indicator (f ω) u := by
    let C := hω.toFinset
    have hC : (C : Set G) = cluster ω 0 := hω.coe_toFinset
    have hcard : ((cluster ω 0).encard : ℝ≥0∞) = C.card := by
      rw [← hC]
      simp
    have hC0 : (C.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr
        ⟨0, by simpa only [C, Set.Finite.mem_toFinset] using mem_cluster_self ω 0⟩
    have hfC (u : G) (hu : u ∈ C) :
        f ω u = ∑ x ∈ C, ENNReal.ofReal (1 + (ψ (x - u) : ℂ).re) := by
      have hu' : u ∈ cluster ω 0 := by simpa only [← hC, Finset.mem_coe] using hu
      have hK : cluster ω u = cluster ω 0 := (cluster_eq_of_mem_conn hu').symm
      dsimp only [f]
      rw [tsum_eq_sum (s := C)]
      · apply sum_congr rfl
        intro x hx
        apply Set.indicator_of_mem
        change x ∈ cluster ω u
        rw [hK, ← hC]
        exact hx
      · intro x hx
        apply Set.indicator_of_notMem
        change x ∉ cluster ω u
        simpa only [hK, ← hC, Finset.mem_coe] using hx
    have hout : (∑' u, (cluster ω 0).indicator (f ω) u) =
        ∑ u ∈ C, ∑ x ∈ C, ENNReal.ofReal (1 + (ψ (x - u) : ℂ).re) := by
      rw [tsum_eq_sum (s := C)]
      · apply sum_congr rfl
        intro u hu
        rw [Set.indicator_of_mem (by simpa only [← hC, Finset.mem_coe] using hu), hfC u hu]
      · intro u hu
        exact Set.indicator_of_notMem (by simpa only [← hC, Finset.mem_coe] using hu) _
    rw [hcard, hout]
    calc
      (C.card : ℝ≥0∞) = (C.card : ℝ≥0∞)⁻¹ * (C.card : ℝ≥0∞) ^ 2 := by
        rw [sq, ← mul_assoc, ENNReal.inv_mul_cancel hC0 (by simp), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl (card_sq_le_sum_character_weight C ψ)
  have hmass : chi q 0 ≤ ∑' x, tau q 0 x * ENNReal.ofReal (1 + (ψ x : ℂ).re) := by
    calc
      chi q 0 ≤ ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞)⁻¹ *
          ∑' u, (cluster ω 0).indicator (f ω) u ∂law q := by
        apply lintegral_mono_ae
        filter_upwards [hfin] with ω hω
        exact hpoint ω hω
      _ = ∫⁻ ω, f ω 0 ∂law q := havg'.symm
      _ = _ := by
        rw [show (fun ω => f ω 0) = fun ω => ∑' x,
          (conn 0 x).indicator (fun _ => ENNReal.ofReal (1 + (ψ x : ℂ).re)) ω by
            funext ω
            simp only [f, sub_zero]]
        rw [lintegral_tsum fun x =>
          (measurable_const.indicator (measurableSet_conn 0 x)).aemeasurable]
        apply tsum_congr
        intro x
        rw [lintegral_indicator_const (measurableSet_conn 0 x), mul_comm]
        rfl
  have hsum : Summable fun x => (tau q 0 x).toReal :=
    ENNReal.summable_toReal (by rw [← chi_eq_tsum_tau]; exact hchi.ne)
  have hsumre : Summable fun x => (tau q 0 x).toReal * (ψ x : ℂ).re :=
    hsum.of_norm_bounded fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (character_re_abs_le_one ψ x)
        ENNReal.toReal_nonneg).trans_eq (mul_one _)
  have hbound : (∑' x, tau q 0 x * ENNReal.ofReal (1 + (ψ x : ℂ).re)) ≤ 2 * chi q 0 := by
    rw [chi_eq_tsum_tau, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro x
    have hc : ENNReal.ofReal (1 + (ψ x : ℂ).re) ≤ 2 := by
      have h := (abs_le.mp (character_re_abs_le_one ψ x)).2
      exact (ENNReal.ofReal_le_ofReal (by linarith : 1 + (ψ x : ℂ).re ≤ 2)).trans_eq (by simp)
    exact (mul_le_mul' le_rfl hc).trans_eq (mul_comm _ _)
  have hfinite : (∑' x, tau q 0 x * ENNReal.ofReal (1 + (ψ x : ℂ).re)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hchi.ne) hbound
  have hreal := ENNReal.toReal_mono hfinite hmass
  have htau (x : G) : tau q 0 x ≠ ⊤ :=
    ((tau_le_one q 0 x).trans_lt ENNReal.one_lt_top).ne
  rw [chi_eq_tsum_tau, ENNReal.tsum_toReal_eq htau,
    ENNReal.tsum_toReal_eq (fun x =>
      ENNReal.mul_ne_top (htau x) ENNReal.ofReal_ne_top)] at hreal
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (one_add_character_re_nonneg ψ _),
    mul_add, mul_one] at hreal
  rw [hsum.tsum_add hsumre] at hreal
  linarith

/-- The real part of the absolutely convergent complex two-point transform is nonnegative. -/
theorem re_tsum_tau_mul_character_nonneg (q : Sym2 G → unitInterval)
    (hq : ∀ g x y : G, q s(g + x, g + y) = q s(x, y))
    (hchi : chi q 0 < ⊤) (ψ : AddChar G Circle) :
    0 ≤ (∑' x, ((tau q 0 x).toReal : ℂ) * (ψ x : ℂ)).re := by
  have hs : Summable fun x => ‖((tau q 0 x).toReal : ℂ) * (ψ x : ℂ)‖ := by
    simpa only [norm_mul, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, mul_one] using
      (ENNReal.summable_toReal (by
        rw [← chi_eq_tsum_tau]
        exact hchi.ne : (∑' x, tau q 0 x) ≠ ⊤))
  rw [Complex.re_tsum hs.of_norm]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] using tsum_tau_mul_character_re_nonneg q hq hchi ψ

end Probability

end PercLib.Percolation.Bond.Lace
