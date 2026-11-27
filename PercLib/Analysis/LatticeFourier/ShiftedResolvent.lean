/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.ShiftedSeries
public import PercLib.Analysis.LatticeFourier.Characters
public import PercLib.Analysis.LatticeFourier.TorusIntegration
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Shifted nearest-neighbour resolvents

The finite nearest-neighbour direction law has nonnegative weights summing to one.
Its geometric walk expansion gives positive absolutely summable Fourier coefficients
for the massive resolvent and for every symbol power times that resolvent. The
positive-series inequality therefore controls arbitrary shifts without translating
the squared-symbol weight.

## Main results

* `exists_nonneg_summable_resolvent_coefficients`: the actual finite-walk construction.
* `integral_nearestNeighborSymbol_sq_mul_shifted_resolvents_le`: the weighted shifted bound.
* `integral_shifted_nearestNeighborResolvents_le`: the unweighted shifted bound.

The parameter is strictly below one. No critical-integrability assertion is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory UnitAddTorus Metric Real

namespace PercLib.Analysis

private theorem mFourier_sum_fin {ι : Type*} [Fintype ι] (n : ℕ)
    (v : Fin n → ι → ℤ) (t : UnitAddTorus ι) :
    mFourier (∑ i, v i) t = ∏ i, mFourier (v i) t := by
  induction n with
  | zero => simp [mFourier_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, mFourier_add, ih]

/-- The geometric walk expansion of a finite probability law supplies explicit
nonnegative summable coefficients for a symbol power times its massive resolvent. -/
theorem exists_nonneg_summable_resolvent_coefficients
    {ι A : Type*} [Fintype ι] [Fintype A]
    (w : A → ℝ) (v : A → ι → ℤ) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∃ W : (Σ n : ℕ, Fin (n + m) → A) → ℝ,
      (∀ p, 0 ≤ W p) ∧ Summable W ∧
      ∀ t : UnitAddTorus ι,
        (∑' p, (W p : ℂ) * mFourier (∑ i, v (p.2 i)) t) =
          (∑ a, (w a : ℂ) * mFourier (v a) t) ^ m *
            (1 - (r : ℂ) * ∑ a, (w a : ℂ) * mFourier (v a) t)⁻¹ := by
  classical
  let W : (Σ n : ℕ, Fin (n + m) → A) → ℝ := fun p => r ^ p.1 * ∏ i, w (p.2 i)
  have hW0 (p) : 0 ≤ W p := mul_nonneg (pow_nonneg hr0 _) (Finset.prod_nonneg fun i _ => hw0 _)
  have hmass (n : ℕ) : (∑' s : Fin (n + m) → A, W ⟨n, s⟩) = r ^ n := by
    simp only [tsum_fintype, W, ← Finset.mul_sum, ← Fintype.sum_pow, hw1, one_pow, mul_one]
  have hW : Summable W := by
    apply (summable_sigma_of_nonneg hW0).2
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    simpa only [hmass] using summable_geometric_of_lt_one hr0 hr1
  refine ⟨W, hW0, hW, ?_⟩
  intro t
  let F : ℂ := ∑ a, (w a : ℂ) * mFourier (v a) t
  have hF : ‖F‖ ≤ 1 := by
    calc
      _ ≤ ∑ a, ‖(w a : ℂ) * mFourier (v a) t‖ := norm_sum_le _ _
      _ = ∑ a, w a := by
        apply Finset.sum_congr rfl
        intro a _
        simp [norm_mFourier_apply, Complex.norm_real, Real.norm_of_nonneg (hw0 a)]
      _ = 1 := hw1
  have hrF : ‖(r : ℂ) * F‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    exact (mul_le_of_le_one_right hr0 hF).trans_lt hr1
  have hpoint (n : ℕ) :
      (∑' s : Fin (n + m) → A, (W ⟨n, s⟩ : ℂ) * mFourier (∑ i, v (s i)) t) =
        F ^ m * ((r : ℂ) * F) ^ n := by
    simp only [tsum_fintype, W, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod,
      mFourier_sum_fin, mul_assoc, ← Finset.prod_mul_distrib]
    rw [← Finset.mul_sum, ← Fintype.sum_pow (fun a => (w a : ℂ) * mFourier (v a) t)]
    dsimp only [F]
    rw [pow_add, mul_pow]
    ring
  have hC : Summable fun p => (W p : ℂ) * mFourier (∑ i, v (p.2 i)) t := by
    apply hW.of_norm_bounded
    intro p
    simp [norm_mFourier_apply, Complex.norm_real, Real.norm_of_nonneg (hW0 p)]
  rw [hC.tsum_sigma' (fun _ => Summable.of_finite)]
  simp_rw [hpoint]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hrF]

/-- The finite nearest-neighbour direction law has the canonical cosine symbol
in the physical frequency convention. -/
theorem nearestNeighbor_direction_symbol {d : ℕ} (hd : 0 < d) (k : Fin d → ℝ) :
    (∑ a : Fin d × Bool, (((2 * d : ℝ)⁻¹ : ℝ) : ℂ) *
      mFourier (Function.update (0 : Fin d → ℤ) a.1 (if a.2 then 1 else -1))
        (fun i => ((k i / (2 * π) : ℝ) : UnitAddCircle))) =
      (nearestNeighborSymbol k : ℂ) := by
  classical
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have hdir (i : Fin d) :
      (∑ b : Bool,
        mFourier (Function.update (0 : Fin d → ℤ) i (if b then 1 else -1))
          (fun j => ((k j / (2 * π) : ℝ) : UnitAddCircle))) =
        ((2 * Real.cos (k i) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [mFourier_div_two_pi_eq_latticeCharacter, Function.update_apply,
        Finset.sum_ite_eq', Complex.cos_ofReal_re]
      ring
    · simp [mFourier_div_two_pi_eq_latticeCharacter, Function.update_apply,
        Finset.sum_ite_eq']
  simp_rw [hdir]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul]
  congr 1
  rw [← Finset.mul_sum, nearestNeighborSymbol]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- Every nonnegative integer symbol power admits the shifted resolvent comparison.
It follows from the actual finite nearest-neighbour walk coefficients. -/
theorem integral_nearestNeighborSymbol_pow_mul_shifted_resolvents_le
    {d : ℕ} (hd : 0 < d) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m : ℕ) (a b : Fin d → ℝ) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ m * nearestNeighborResolvent r l *
        nearestNeighborResolvent r (l + a) * nearestNeighborResolvent r (l + b)) ≤
      ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol l ^ m * nearestNeighborResolvent r l ^ 3) := by
  classical
  let v : Fin d × Bool → Fin d → ℤ := fun p =>
    Function.update 0 p.1 (if p.2 then 1 else -1)
  let w : Fin d × Bool → ℝ := fun _ => (2 * d : ℝ)⁻¹
  have hw0 (p) : 0 ≤ w p := by dsimp [w]; positivity
  have hw1 : ∑ p, w p = 1 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp [w, Fintype.card_prod]
    field_simp
  let F : UnitAddTorus (Fin d) → ℂ := fun t => ∑ p, (w p : ℂ) * mFourier (v p) t
  let R : UnitAddTorus (Fin d) → ℂ := fun t => (1 - (r : ℂ) * F t)⁻¹
  let q : (Fin d → ℝ) → UnitAddTorus (Fin d) := fun k i => ((k i / (2 * π) : ℝ) : UnitAddCircle)
  have hF (k) : F (q k) = (nearestNeighborSymbol k : ℂ) :=
    nearestNeighbor_direction_symbol hd k
  have hR (k) : R (q k) = (nearestNeighborResolvent r k : ℂ) := by
    simp only [R, hF, nearestNeighborResolvent, Complex.ofReal_inv,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]
  have hq (k l : Fin d → ℝ) : q k + q l = q (k + l) := by
    funext i
    simp only [q, Pi.add_apply, add_div, AddCircle.coe_add]
  obtain ⟨W, hW0, hW, hWrep⟩ :=
    exists_nonneg_summable_resolvent_coefficients w v hw0 hw1 hr0 hr1 m
  obtain ⟨U, hU0, hU, hUrep⟩ :=
    exists_nonneg_summable_resolvent_coefficients w v hw0 hw1 hr0 hr1 0
  have h := norm_integral_shifted_mFourier_series_mul_three_le W U U
    (fun p => ∑ i, v (p.2 i)) (fun p => ∑ i, v (p.2 i)) (fun p => ∑ i, v (p.2 i))
    hW hU hU hW0 hU0 hU0 (q a) (q b)
  simp_rw [hWrep, hUrep, pow_zero, one_mul] at h
  change ‖∫ t : UnitAddTorus (Fin d),
      (F t ^ m * R t) * R (t + q a) * R (t + q b)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ ≤
    (∫ t : UnitAddTorus (Fin d), (F t ^ m * R t) * R t * R t
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)).re at h
  rw [integral_unitTorus_eq_normalized_box, integral_unitTorus_eq_normalized_box] at h
  change ‖((2 * π) ^ d)⁻¹ • (∫ l in ball (0 : Fin d → ℝ) π,
      (F (q l) ^ m * R (q l)) * R (q l + q a) * R (q l + q b))‖ ≤
    (((2 * π) ^ d)⁻¹ • (∫ l in ball (0 : Fin d → ℝ) π,
      (F (q l) ^ m * R (q l)) * R (q l) * R (q l))).re at h
  simp_rw [hq, hF, hR, ← Complex.ofReal_pow, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.real_smul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re] at h
  have hpow (l : Fin d → ℝ) :
      (nearestNeighborSymbol l ^ m * nearestNeighborResolvent r l) *
          nearestNeighborResolvent r l * nearestNeighborResolvent r l =
        nearestNeighborSymbol l ^ m * nearestNeighborResolvent r l ^ 3 := by ring
  simp_rw [hpow] at h
  exact (le_abs_self _).trans h

/-- The squared-symbol weighted triangle is largest when both shifts vanish. -/
theorem integral_nearestNeighborSymbol_sq_mul_shifted_resolvents_le
    {d : ℕ} (hd : 0 < d) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (a b : Fin d → ℝ) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l *
        nearestNeighborResolvent r (l + a) * nearestNeighborResolvent r (l + b)) ≤
      ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) :=
  integral_nearestNeighborSymbol_pow_mul_shifted_resolvents_le hd hr0 hr1 2 a b

/-- The unweighted massive triangle is also largest at simultaneous zero shifts. -/
theorem integral_shifted_nearestNeighborResolvents_le
    {d : ℕ} (hd : 0 < d) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (a b : Fin d → ℝ) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborResolvent r l * nearestNeighborResolvent r (l + a) *
        nearestNeighborResolvent r (l + b)) ≤
      ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborResolvent r l ^ 3) := by
  simpa only [pow_zero, one_mul] using
    integral_nearestNeighborSymbol_pow_mul_shifted_resolvents_le hd hr0 hr1 0 a b

end PercLib.Analysis
