/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the real Fourier form of the percolation lace expansion.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.ConvolutionWeight
public import PercLib.Percolation.Bond.Lace.FourierPositivity

/-!
# The real canonical Fourier equation and positive denominator

Translation invariance of the unordered bond profile makes the rooted two-point,
step, and signed lace kernels even. Their character transforms are therefore real.
The actual canonical complex equation consequently gives an equation between real
character sums. If the absolute mass of the signed lace kernel is less than one,
finite-cluster Fourier positivity makes both the two-point transform and the
denominator strictly positive.

## Main results

* `even_tau_rooted`, `even_laceSum_rooted`, `even_offDiagonal_rooted`: canonical evenness.
* `abs_tsum_mul_re_addChar_le`: the absolute Fourier bound by the absolute kernel mass.
* `canonical_lace_real_fourier_equation`: the actual real scalar equation.
* `canonical_lace_real_fourier_pos`: strict positivity and the real quotient under
  absolute signed coefficient mass less than one.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The rooted two-point kernel is even under translation invariance. -/
theorem even_tau_rooted (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    Function.Even (fun x => (tau q 0 x).toReal) := by
  intro x
  apply congrArg ENNReal.toReal
  calc
    tau q 0 (-x) = tau q x 0 := by
      simpa only [zero_sub] using (tau_eq_rooted_of_add_right q hq x 0).symm
    _ = tau q 0 x := tau_comm q x 0

/-- The rooted off-diagonal step kernel is even under translation invariance. -/
theorem even_offDiagonal_rooted (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    Function.Even (fun x => (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal) := by
  intro x
  simpa only [Equiv.neg_apply, neg_zero] using congrArg ENNReal.toReal
    (offDiagonal_apply_equiv q (Equiv.neg G) (profile_neg_eq_of_add_right q hq) 0 x)

/-- A unitary character transform is bounded by the absolute mass of a summable real kernel. -/
theorem abs_tsum_mul_re_addChar_le {f : G → ℝ} (hf : Summable f) (ψ : AddChar G Circle) :
    |∑' x, f x * (ψ x : ℂ).re| ≤ ∑' x, |f x| := by
  have hs : Summable (fun x => ‖(f x : ℂ) * (ψ x : ℂ)‖) := by
    simpa only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real] using hf.norm
  rw [← re_tsum_ofReal_mul_addChar hf ψ]
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs).trans_eq
    (tsum_congr fun x => by
      simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]))

variable [Countable G]

/-- The actual infinite signed lace kernel is even, without an additional symmetry input. -/
theorem even_laceSum_rooted (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    Function.Even (laceSum q 0) := by
  intro x
  simp only [laceSum, laceCoefficient_neg q hq]

/-- The actual canonical Fourier equation between real character sums. All imaginary
parts vanish by the proved evenness of the canonical kernels. -/
theorem canonical_lace_real_fourier_equation
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hJ : (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) ≠ ⊤)
    (hτ : (∑' y, tau q 0 y) ≠ ⊤)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n 0 u) ≠ ⊤)
    (ψ : AddChar G Circle) :
    let T : ℝ := ∑' x, (tau q 0 x).toReal * (ψ x : ℂ).re
    let P : ℝ := ∑' x, laceSum q 0 x * (ψ x : ℂ).re
    let J : ℝ := ∑' x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal * (ψ x : ℂ).re
    T = 1 + P + (1 + P) * J * T := by
  have hTi := im_tsum_ofReal_mul_addChar_eq_zero_of_even (even_tau_rooted q hq) ψ
  have hPi := im_tsum_ofReal_mul_addChar_eq_zero_of_even (even_laceSum_rooted q hq) ψ
  have hJi := im_tsum_ofReal_mul_addChar_eq_zero_of_even (even_offDiagonal_rooted q hq) ψ
  have h := congrArg Complex.re (canonical_lace_fourier_equation q hq hJ hτ hmass ψ)
  dsimp only at h ⊢
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
    Complex.add_im, Complex.one_im, hTi, hPi, hJi, add_zero,
    mul_zero, zero_mul, sub_zero] at h
  rw [re_tsum_ofReal_mul_addChar (ENNReal.summable_toReal hτ) ψ,
    re_tsum_ofReal_mul_addChar (summable_laceSum q 0 hmass) ψ,
    re_tsum_ofReal_mul_addChar (ENNReal.summable_toReal hJ) ψ] at h
  exact h

/-- Absolute signed lace mass less than one gives a strictly positive actual two-point
transform and Fourier denominator. Nonnegativity of the transform is derived by
finite-cluster mass transport, rather than assumed. -/
theorem canonical_lace_real_fourier_pos
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hJ : (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) ≠ ⊤)
    (hτ : (∑' y, tau q 0 y) ≠ ⊤)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n 0 u) ≠ ⊤)
    (hsmall : (∑' x, |laceSum q 0 x|) < 1)
    (ψ : AddChar G Circle) :
    let T : ℝ := ∑' x, (tau q 0 x).toReal * (ψ x : ℂ).re
    let P : ℝ := ∑' x, laceSum q 0 x * (ψ x : ℂ).re
    let J : ℝ := ∑' x, (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal * (ψ x : ℂ).re
    0 < T ∧ 0 < 1 - (1 + P) * J ∧ T = (1 + P) / (1 - (1 + P) * J) := by
  let T : ℝ := ∑' x, (tau q 0 x).toReal * (ψ x : ℂ).re
  let P : ℝ := ∑' x, laceSum q 0 x * (ψ x : ℂ).re
  let J : ℝ := ∑' x, (offDiagonal (fun a b : G =>
    (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal * (ψ x : ℂ).re
  change 0 < T ∧ 0 < 1 - (1 + P) * J ∧ T = (1 + P) / (1 - (1 + P) * J)
  have hP : |P| < 1 :=
    (abs_tsum_mul_re_addChar_le (summable_laceSum q 0 hmass) ψ).trans_lt hsmall
  have hnum : 0 < 1 + P := by linarith [(abs_lt.mp hP).1]
  have hnonneg : 0 ≤ T := tsum_tau_mul_character_re_nonneg q
    (fun g x y => by simpa only [add_comm g x, add_comm g y] using hq x y g)
    (by rw [chi_eq_tsum_tau]; exact hτ.lt_top) ψ
  have heq : T = 1 + P + (1 + P) * J * T :=
    canonical_lace_real_fourier_equation q hq hJ hτ hmass ψ
  have hT : 0 < T := by
    by_contra! h
    have hz : T = 0 := le_antisymm h hnonneg
    rw [hz, mul_zero, add_zero] at heq
    linarith
  have hprod : (1 - (1 + P) * J) * T = 1 + P := by nlinarith [heq]
  have hdeneq : 1 - (1 + P) * J = (1 + P) / T := (eq_div_iff hT.ne').2 hprod
  have hden : 0 < 1 - (1 + P) * J := by
    rw [hdeneq]
    exact div_pos hnum hT
  refine ⟨hT, hden, (eq_div_iff hden.ne').2 ?_⟩
  simpa only [mul_comm] using hprod

end PercLib.Percolation.Bond.Lace
