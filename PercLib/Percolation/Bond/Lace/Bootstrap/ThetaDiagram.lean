/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original application of actual two-point Fourier positivity to the theta graph.
No upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.Theta
public import PercLib.Percolation.Bond.Lace.FourierPositivity
public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborIntegrals
public import PercLib.Percolation.Bond.Lace.Bootstrap.OriginTriangle

/-!
# The actual theta diagram is bounded by the triangle squared

## Main results

For a translation-invariant lattice bond profile with finite susceptibility,
the sum of the cubes of the two-point convolution is at most the square of the
triangle diagram. Fourier positivity is proved from the actual percolation law;
neither a Fourier identity nor positivity is an additional hypothesis.
-/

@[expose] public section
noncomputable section

open MeasureTheory UnitAddTorus PercLib.Analysis DiscreteConvolution
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

private theorem tau_theta_real_le_triangle_sq
    (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ x y g : Fin d → ℤ, q s(x + g, y + g) = q s(x, y))
    (hchi : chi q 0 ≠ ⊤) :
    let T := fun x => (tau q 0 x).toReal
    (∑' x, ((T ⋆ᵣ₊ T) x) ^ 3) ≤ ((T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) 0) ^ 2 := by
  let T := fun x => (tau q 0 x).toReal
  let H := T ⋆ᵣ₊ T
  let R := T ⋆ᵣ₊ H
  let S := fun t : UnitAddTorus (Fin d) => ∑' x, (T x : ℂ) * mFourier x t
  let F := fun t : UnitAddTorus (Fin d) => (S t).re
  let μ : Measure (UnitAddTorus (Fin d)) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have hH : Summable H := summable_addRingConvolution_real hT hT
  have hR : Summable R := summable_addRingConvolution_real hT hH
  have hTC : Summable fun x => ‖(T x : ℂ)‖ := by simpa only [Complex.norm_real] using hT.norm
  have hHC : Summable fun x => ‖(H x : ℂ)‖ := by simpa only [Complex.norm_real] using hH.norm
  have hRC : Summable fun x => ‖(R x : ℂ)‖ := by simpa only [Complex.norm_real] using hR.norm
  have heT : Function.Even T := by
    intro x
    apply congrArg ENNReal.toReal
    calc
      tau q 0 (-x) = tau q x 0 := by
        simpa only [zero_sub] using (tau_eq_rooted_of_add_right q hq x 0).symm
      _ = _ := tau_comm q x 0
  have heH : Function.Even H := even_addRingConvolution heT heT
  have hFourier (t : UnitAddTorus (Fin d)) :
      (∑' x, (H x : ℂ) * mFourier x t) = (F t ^ 2 : ℝ) ∧
      (∑' x, (R x : ℂ) * mFourier x t) = (F t ^ 3 : ℝ) ∧ 0 ≤ F t := by
    let ψ : AddChar (Fin d → ℤ) Circle :=
      { toFun := fun x => ⟨mFourier x t, mem_sphere_zero_iff_norm.mpr (norm_mFourier_apply x t)⟩
        map_zero_eq_one' := by apply Subtype.ext; simp [mFourier_zero]
        map_add_eq_mul' := fun x y => by apply Subtype.ext; exact mFourier_add }
    have hψ (x : Fin d → ℤ) : (ψ x : ℂ) = mFourier x t := rfl
    have hS : S t = (F t : ℂ) := by
      apply Complex.ext
      · rfl
      · have h := im_tsum_ofReal_mul_addChar_eq_zero_of_even heT ψ
        simpa only [hψ, Complex.ofReal_im] using h
    have hHrep := tsum_addRingConvolution_mul_addChar
      (fun x => (T x : ℂ)) (fun x => (T x : ℂ)) ψ hTC hTC
    simp only [← ofReal_addRingConvolution, hψ] at hHrep
    change (∑' x, (H x : ℂ) * mFourier x t) = S t * S t at hHrep
    have hHreal : (∑' x, (H x : ℂ) * mFourier x t) = (F t ^ 2 : ℝ) := by
      rw [hHrep, hS]
      push_cast
      ring
    have hRrep := tsum_addRingConvolution_mul_addChar
      (fun x => (T x : ℂ)) (fun x => (H x : ℂ)) ψ hTC hHC
    simp only [← ofReal_addRingConvolution, hψ] at hRrep
    change (∑' x, (R x : ℂ) * mFourier x t) = S t * (∑' x, (H x : ℂ) * mFourier x t) at hRrep
    have hRreal : (∑' x, (R x : ℂ) * mFourier x t) = (F t ^ 3 : ℝ) := by
      rw [hRrep, hS, hHreal]
      push_cast
      ring
    refine ⟨hHreal, hRreal, ?_⟩
    have hn := re_tsum_tau_mul_character_nonneg q
      (fun g x y => by simpa only [add_comm] using hq x y g) (lt_top_iff_ne_top.mpr hchi) ψ
    simpa only [hψ] using hn
  have hF : Continuous F := Complex.continuous_re.comp (continuous_tsum_mul_mFourier _ hTC)
  have hF0 (t) : 0 ≤ F t := (hFourier t).2.2
  have hHrep (t) := (hFourier t).1
  have hRrep (t) := (hFourier t).2.1
  have hθ := integral_two_mFourier_series_triangle_eq (fun x => (H x : ℂ)) hHC
  dsimp only at hθ
  have hpow (x : Fin d → ℤ) : (H x : ℂ) * (H (-x) : ℂ) * (H (-x) : ℂ) = (H x ^ 3 : ℝ) := by
    rw [heH x]
    push_cast
    ring
  simp_rw [hHrep, hpow, ← Complex.ofReal_mul, integral_complex_ofReal,
    ← Complex.ofReal_tsum] at hθ
  have hθreal : (∫ s, ∫ t, F s ^ 2 * F t ^ 2 * F (s + t) ^ 2 ∂μ ∂μ) =
      ∑' x, H x ^ 3 := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hθ
  have htriangle := mFourierCoeff_tsum_mul (fun x => (R x : ℂ)) hRC 0
  change (∫ t : UnitAddTorus (Fin d),
    mFourier (-0) t * (∑' x, (R x : ℂ) * mFourier x t) ∂μ) = (R 0 : ℂ) at htriangle
  simp only [neg_zero, mFourier_zero, ContinuousMap.one_apply, one_mul] at htriangle
  simp_rw [hRrep, integral_complex_ofReal] at htriangle
  have htriangleReal : (∫ t, F t ^ 3 ∂μ) = R 0 := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re htriangle
  have h := integral_torus_theta_le_cube_sq F hF hF0
  change (∫ s, ∫ t, F s ^ 2 * F t ^ 2 * F (s + t) ^ 2 ∂μ ∂μ) ≤ (∫ t, F t ^ 3 ∂μ) ^ 2 at h
  rwa [hθreal, htriangleReal] at h

/-- The actual theta graph is at most the square of the actual triangle, with
constant one. The sole analytic finiteness premise is finite susceptibility. -/
theorem tsum_tau_pair_cube_le_triangle_sq
    (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ x y g : Fin d → ℤ, q s(x + g, y + g) = q s(x, y))
    (hchi : chi q 0 ≠ ⊤) :
    (∑' v, (∑' u, tau q 0 u * tau q u v) ^ 3) ≤
      (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ^ 2 := by
  let T := tau q 0
  let H := T ⋆ᵣ₊ T
  let R := T ⋆ᵣ₊ H
  have hT : (∑' x, T x) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have hTz (x) : T x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q 0 x)
  have hH : (∑' x, H x) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hT
  have hHz (x) : H x ≠ ⊤ := addRingConvolution_ennreal_ne_top hT hT x
  have hR0 : R 0 ≠ ⊤ := addRingConvolution_ennreal_ne_top hT hH 0
  have hθ : (∑' x, H x ^ 3) ≠ ⊤ := by
    have hfinite : (∑' x, H x) * (∑' x, H x) ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top hH (ENNReal.pow_ne_top hH)
    apply ne_top_of_le_ne_top hfinite
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro x
    calc
      H x ^ 3 = H x * (H x ^ 2) := by ring
      _ ≤ H x * ((∑' y, H y) ^ 2) := mul_le_mul' le_rfl
        (pow_le_pow_left₀ (show 0 ≤ H x from zero_le) (ENNReal.le_tsum x) 2)
  have hpair (v : Fin d → ℤ) : (∑' u, tau q 0 u * tau q u v) = H v := by
    dsimp only [H]
    rw [addRingConvolution_eq_tsum_sub]
    apply tsum_congr
    intro u
    rw [tau_eq_rooted_of_add_right q hq u v]
  have htriangle : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) = R 0 := by
    symm
    simpa only [sub_self, tau_comm q (0 : Fin d → ℤ)] using tau_three_neg_eq_triangle q hq 0
  simp_rw [hpair]
  rw [htriangle]
  apply (ENNReal.toReal_le_toReal hθ (ENNReal.pow_ne_top hR0)).mp
  rw [ENNReal.tsum_toReal_eq (fun x => ENNReal.pow_ne_top (hHz x)), ENNReal.toReal_pow]
  have hrealH (x) : (H x).toReal =
      ((fun y => (T y).toReal) ⋆ᵣ₊ (fun y => (T y).toReal)) x :=
    toReal_addRingConvolution_ennreal hTz hTz x
  have hrealR : (R 0).toReal =
      ((fun y => (T y).toReal) ⋆ᵣ₊ (fun y => (H y).toReal)) 0 :=
    toReal_addRingConvolution_ennreal hTz hHz 0
  simp only [ENNReal.toReal_pow, hrealR, hrealH]
  exact tau_theta_real_le_triangle_sq q hq hchi

/-- The zero profile attains equality with both diagrams equal to one, in every
lattice dimension. Thus the universal prefactor one cannot be decreased. -/
theorem zero_profile_theta_and_triangle :
    (∑' v : Fin d → ℤ,
      (∑' u, tau (fun _ => 0) 0 u * tau (fun _ => 0) u v) ^ 3) = 1 ∧
    (∑' u : Fin d → ℤ, ∑' v,
      tau (fun _ => 0) 0 u * tau (fun _ => 0) u v * tau (fun _ => 0) v 0) = 1 := by
  classical
  have ht (x y : Fin d → ℤ) :
      tau (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) x y = if x = y then 1 else 0 := by
    by_cases hxy : x = y
    · subst y
      simp only [tau_self, ↓reduceIte]
    · rw [ite_eq_right hxy]
      apply le_antisymm _ zero_le
      have h := tau_le_tsum_offDiagonal_mul_tau
        (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)) hxy
      simpa [offDiagonal_apply] using h
  simp [ht, eq_comm]

end PercLib.Percolation.Bond.Lace
