/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs for the canonical lace expansion; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Infinite
public import PercLib.Percolation.Bond.Lace.Transport
public import PercLib.Percolation.Bond.Lace.Fourier
public import PercLib.Percolation.Bond.IndependentLayer
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Fourier transform of the canonical infinite lace expansion

## Main results

Translation invariance of the profile roots the two-point and step kernels.
Finite step mass, susceptibility, and total coefficient mass justify Fourier
summation of the proved infinite expansion. The transformed equation and its
nonzero denominator are conclusions, not additional hypotheses.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- On a group, the addition-fiber convolution is the usual difference sum. -/
theorem addRingConvolution_eq_tsum_sub {R : Type*}
    [NonUnitalNonAssocSemiring R] [TopologicalSpace R] (f g : G → R) (x : G) :
    DiscreteConvolution.addRingConvolution f g x = ∑' u, f u * g (x - u) := by
  classical
  let e : G ≃ DiscreteConvolution.addFiber x :=
    { toFun := fun u => ⟨(u, x - u),
        DiscreteConvolution.mem_addFiber.mpr (by rw [add_comm, sub_add_cancel])⟩
      invFun := fun p => p.val.1
      left_inv := fun _ => rfl
      right_inv := fun p => by
        apply Subtype.ext
        change (p.val.1, x - p.val.1) = p.val
        apply Prod.ext
        · rfl
        have hp := DiscreteConvolution.mem_addFiber.mp p.property
        dsimp
        exact sub_eq_iff_eq_add.mpr (hp.symm.trans (add_comm _ _)) }
  exact (e.tsum_eq (fun p => f p.val.1 * g p.val.2)).symm

/-- Absolute summability is closed under the existing discrete convolution. -/
theorem summable_norm_addRingConvolution (f g : G → ℂ)
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun x => ‖DiscreteConvolution.addRingConvolution f g x‖ := by
  classical
  have hs := (summable_mul_of_summable_norm hf hg).hasSum.tsum_fiberwise
    (fun p : G × G => p.1 + p.2)
  have hset (x : G) : (fun p : G × G => p.1 + p.2) ⁻¹' {x} =
      DiscreteConvolution.addFiber x := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, DiscreteConvolution.mem_addFiber]
  have hfiber (x : G) :
      (∑' p : (fun p : G × G => p.1 + p.2) ⁻¹' {x}, f p.val.1 * g p.val.2) =
        DiscreteConvolution.addRingConvolution f g x := by
    rw [hset]
    rfl
  exact (hs.summable.congr hfiber).norm

/-- The nested convolution agrees with the two intermediate vertices in the
lace equation. This reindexing does not require summability hypotheses. -/
theorem addRingConvolution_nested_eq_tsum (f g h : G → ℂ) (x : G) :
    DiscreteConvolution.addRingConvolution f
      (DiscreteConvolution.addRingConvolution g h) x =
        ∑' u, ∑' v, f u * g (v - u) * h (x - v) := by
  classical
  rw [addRingConvolution_eq_tsum_sub]
  apply tsum_congr
  intro u
  rw [addRingConvolution_eq_tsum_sub, ← tsum_mul_left]
  rw [← (Equiv.addRight u).tsum_eq
    (fun v => f u * g (v - u) * h (x - v))]
  apply tsum_congr
  intro v
  have hx : x - (v + u) = x - u - v := by abel
  simp only [Equiv.coe_addRight, add_sub_cancel_right, hx, mul_assoc]

/-- Rooting the actual two-point function uses invariance of the Bernoulli law. -/
theorem tau_eq_rooted_of_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x y : G) :
    tau q x y = tau q 0 (y - x) := by
  classical
  have hp : ∀ a, q (Sym2.map (Equiv.addRight (-x)) a) = q a := by
    intro a
    induction a using Sym2.ind with
    | _ u v => exact hq u v (-x)
  have ht := tau_eq_of_map_law (Equiv.addRight (-x))
    (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q _ hp) x y
  simpa only [Equiv.coe_addRight, add_neg_cancel, sub_eq_add_neg] using ht.symm

/-- The off-diagonal step kernel has the same rooting convention. -/
theorem offDiagonal_eq_rooted_of_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x y : G) :
    offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x y =
      offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 (y - x) := by
  classical
  have hp : ∀ a, q (Sym2.map (Equiv.addRight (-x)) a) = q a := by
    intro a
    induction a using Sym2.ind with
    | _ u v => exact hq u v (-x)
  simpa only [Equiv.coe_addRight, add_neg_cancel, sub_eq_add_neg] using
    (offDiagonal_apply_equiv q (Equiv.addRight (-x)) hp x y).symm

/-- Translation invariance turns finite susceptibility at zero into the
almost-sure finite-cluster hypotheses required at every cutting vertex. -/
theorem ae_deleted_cluster_finite_of_summable_tau [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hτ : (∑' y, tau q 0 y) ≠ ⊤) (a u v : G) :
    ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite := by
  classical
  have hrow : (∑' y, tau q a y) = ∑' y, tau q 0 y := by
    simp_rw [tau_eq_rooted_of_add_right q hq a]
    simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
      (Equiv.addRight (-a)).tsum_eq (tau q 0)
  have hχ : chi q a < ⊤ := by
    rw [chi_eq_tsum_tau, hrow]
    exact lt_top_iff_ne_top.mpr hτ
  filter_upwards [ae_cluster_finite_of_chi_lt_top hχ] with ω hω
  exact hω.subset (cluster_mono sdiff_subset a)

/-- Finite step mass supplies the uniform continuation bound for the infinite
expansion, with constant exactly the step mass. -/
theorem step_tau_le_step_mass_of_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (u z : G) :
    (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v z) ≤
        ∑' v, offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v := by
  classical
  calc
    _ ≤ ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v :=
      ENNReal.tsum_le_tsum fun v => mul_le_of_le_one_right' (tau_le_one q v z)
    _ = ∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 (v - u) :=
      tsum_congr fun v => offDiagonal_eq_rooted_of_add_right q hq u v
    _ = _ := by
      simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
        (Equiv.addRight (-u)).tsum_eq
          (offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0)

open scoped Classical in
/-- The proved infinite expansion, expressed using canonical rooted complex
kernels and mathlib's discrete convolution. -/
theorem canonical_lace_convolution_equation [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hfin : ∀ a u v : G, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite)
    (hJ : (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) ≠ ⊤)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n 0 u) ≠ ⊤) (y : G) :
    let T : G → ℂ := fun x => (tau q 0 x).toReal
    let P : G → ℂ := fun x => laceSum q 0 x
    let J : G → ℂ := fun x => (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal
    T y = (if y = 0 then 1 else 0) + P y +
      DiscreteConvolution.addRingConvolution J T y +
        DiscreteConvolution.addRingConvolution P
          (DiscreteConvolution.addRingConvolution J T) y := by
  dsimp only
  rw [addRingConvolution_eq_tsum_sub, addRingConvolution_nested_eq_tsum]
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (infinite_lace_expansion q 0 y hfin _ hJ
      (step_tau_le_step_mass_of_add_right q hq) hmass)
  simp only [Complex.ofReal_add, Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_zero, apply_ite] at h
  have hstep :
      (∑' v, ((offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v).toReal : ℂ) *
          (tau q v y).toReal) =
      ∑' v, ((offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v).toReal : ℂ) *
          (tau q 0 (y - v)).toReal := by
    apply tsum_congr
    intro v
    rw [tau_eq_rooted_of_add_right q hq v y]
  have hdouble :
      (∑' u, ∑' v, (laceSum q 0 u : ℂ) *
        (offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal *
            (tau q v y).toReal) =
      ∑' u, ∑' v, (laceSum q 0 u : ℂ) *
        (offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 (v - u)).toReal *
            (tau q 0 (y - v)).toReal := by
    apply tsum_congr
    intro u
    apply tsum_congr
    intro v
    rw [tau_eq_rooted_of_add_right q hq v y, offDiagonal_eq_rooted_of_add_right q hq u v]
  rw [hstep, hdouble] at h
  simpa only [eq_comm] using h

open scoped Classical in
/-- Fourier summation of a summable convolution equation. The canonical
application below supplies this premise from the proved lace expansion. -/
theorem fourier_eq_of_lace_convolution_equation [Countable G]
    (T P J : G → ℂ) (ψ : AddChar G Circle)
    (hT : Summable fun x => ‖T x‖) (hP : Summable fun x => ‖P x‖)
    (hJ : Summable fun x => ‖J x‖)
    (heq : ∀ y, T y = (if y = 0 then 1 else 0) + P y +
      DiscreteConvolution.addRingConvolution J T y +
        DiscreteConvolution.addRingConvolution P
          (DiscreteConvolution.addRingConvolution J T) y) :
    (∑' x, T x * (ψ x : ℂ)) = 1 + (∑' x, P x * (ψ x : ℂ)) +
      (1 + ∑' x, P x * (ψ x : ℂ)) * (∑' x, J x * (ψ x : ℂ)) *
        (∑' x, T x * (ψ x : ℂ)) := by
  have hJT := summable_norm_addRingConvolution J T hJ hT
  have hPJT := summable_norm_addRingConvolution P _ hP hJT
  have hw (f : G → ℂ) (hf : Summable fun x => ‖f x‖) :
      Summable (fun x => f x * (ψ x : ℂ)) := by
    apply Summable.of_norm
    simpa only [norm_mul, Circle.norm_coe, mul_one] using hf
  have hδ : Summable (fun x : G => (if x = 0 then 1 else 0 : ℂ) * (ψ x : ℂ)) := by
    have heqδ : (fun x : G => (if x = 0 then 1 else 0 : ℂ) * (ψ x : ℂ)) =
        fun x => if x = 0 then 1 else 0 := by
      funext x
      by_cases hx : x = 0 <;> simp [hx]
    rw [heqδ]
    exact (hasSum_ite_eq (0 : G) (1 : ℂ)).summable
  have hδsum : (∑' x : G, (if x = 0 then 1 else 0 : ℂ) * (ψ x : ℂ)) = 1 := by
    simp only [ite_mul, one_mul, zero_mul, tsum_ite_eq, AddChar.map_zero_eq_one,
      Circle.coe_one]
  calc
    _ = ∑' x, ((if x = 0 then 1 else 0) + P x +
        DiscreteConvolution.addRingConvolution J T x +
          DiscreteConvolution.addRingConvolution P
            (DiscreteConvolution.addRingConvolution J T) x) * (ψ x : ℂ) :=
      tsum_congr fun x => congrArg (fun z => z * (ψ x : ℂ)) (heq x)
    _ = (∑' x : G, (if x = 0 then 1 else 0 : ℂ) * (ψ x : ℂ)) +
        (∑' x, P x * (ψ x : ℂ)) +
        (∑' x, DiscreteConvolution.addRingConvolution J T x * (ψ x : ℂ)) +
        (∑' x, DiscreteConvolution.addRingConvolution P
          (DiscreteConvolution.addRingConvolution J T) x * (ψ x : ℂ)) := by
      simp_rw [add_mul]
      rw [((hδ.add (hw P hP)).add (hw _ hJT)).tsum_add (hw _ hPJT),
        (hδ.add (hw P hP)).tsum_add (hw _ hJT), hδ.tsum_add (hw P hP)]
    _ = 1 + (∑' x, P x * (ψ x : ℂ)) +
        (∑' x, J x * (ψ x : ℂ)) * (∑' x, T x * (ψ x : ℂ)) +
        (∑' x, P x * (ψ x : ℂ)) *
          ((∑' x, J x * (ψ x : ℂ)) * (∑' x, T x * (ψ x : ℂ))) := by
      rw [hδsum, tsum_addRingConvolution_mul_addChar P _ ψ hP hJT,
        tsum_addRingConvolution_mul_addChar J T ψ hJ hT]
    _ = _ := by ring

/-- The actual canonical lace kernels satisfy the transformed equation.
Finiteness of susceptibility supplies every finite-cluster hypothesis. -/
theorem canonical_lace_fourier_equation [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hJ : (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) ≠ ⊤)
    (hτ : (∑' y, tau q 0 y) ≠ ⊤)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n 0 u) ≠ ⊤)
    (ψ : AddChar G Circle) :
    let T : ℂ := ∑' x, ((tau q 0 x).toReal : ℂ) * (ψ x : ℂ)
    let P : ℂ := ∑' x, (laceSum q 0 x : ℂ) * (ψ x : ℂ)
    let J : ℂ := ∑' x, ((offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal : ℂ) * (ψ x : ℂ)
    T = 1 + P + (1 + P) * J * T := by
  classical
  have hTnorm : Summable (fun x : G => ‖((tau q 0 x).toReal : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      using ENNReal.summable_toReal hτ
  have hJnorm : Summable (fun x : G => ‖((offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      using ENNReal.summable_toReal hJ
  have hPnorm : Summable (fun x : G => ‖(laceSum q 0 x : ℂ)‖) := by
    simpa only [Complex.norm_real] using (summable_laceSum q 0 hmass).norm
  exact fourier_eq_of_lace_convolution_equation _ _ _ ψ hTnorm hPnorm hJnorm
    (canonical_lace_convolution_equation q hq
      (ae_deleted_cluster_finite_of_summable_tau q hq hτ) hJ hmass)

/-- The Fourier quotient for the canonical lace expansion, including
nonvanishing of its denominator as a proved conclusion. -/
@[tag "PI55"]
theorem canonical_lace_fourier_quotient [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hJ : (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) ≠ ⊤)
    (hτ : (∑' y, tau q 0 y) ≠ ⊤)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n 0 u) ≠ ⊤)
    (ψ : AddChar G Circle) :
    let T : ℂ := ∑' x, ((tau q 0 x).toReal : ℂ) * (ψ x : ℂ)
    let P : ℂ := ∑' x, (laceSum q 0 x : ℂ) * (ψ x : ℂ)
    let J : ℂ := ∑' x, ((offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 x).toReal : ℂ) * (ψ x : ℂ)
    1 - (1 + P) * J ≠ 0 ∧ T = (1 + P) / (1 - (1 + P) * J) := by
  classical
  have h := canonical_lace_fourier_equation q hq hJ hτ hmass ψ
  exact ⟨lace_fourier_denominator_ne_zero h, eq_lace_fourier_quotient h⟩

end PercLib.Percolation.Bond.Lace
