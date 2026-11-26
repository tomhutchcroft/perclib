/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface and the intensity family `intensityProfile`. The
statements follow the wiki tags 1EWX, MTYL and HRS7 (host connectivity). No source text or
code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import Mathlib.Analysis.Complex.Exponential

/-!
# Normalized transitive models at small intensity

Let `J` be an intensity whose off-diagonal rows sum to exactly one, and let
`q = intensityProfile J β` with `0 < β < 1`. Writing
`Δ = ∑' u v, τ(o,u) τ(u,v) τ(v,o)` for the closed triangle at `o`:

* `chi_bounds` (1EWX): `1 + β - β²/2 ≤ χ(o) ≤ (1 - β)⁻¹`;
* `triangle_bounds` (1EWX): `1 ≤ Δ ≤ 1 + 3 m² + m³` with `m = β / (1 - β)`.

Neither bound uses transitivity: they hold at every root under the row hypothesis alone.
`chi_bounds_of_transitive` and `triangle_bounds_of_transitive` restate them with a transitivity
hypothesis, which is then unused.

With transitivity, the integrated mean-field inequality for the susceptibility gives:

* `locallyLipschitzOn_chi_Ioo_zero_one` (1EWX): `β ↦ χ_β(o)` is locally Lipschitz on `(0, 1)`;
* `ae_hasDerivAt_chi_le_inv_one_sub_sq` (1EWX): `χ'(β) ≤ (1 - β)⁻²` for almost every
  `β ∈ (0, 1)`;
* `ae_hasDerivAt_chi_lt_triangle_formula` (1EWX): for almost every `β ∈ (0, 1/100)`,
  `χ'(β) < χ (χ - Δ) / (3 β² Δ²)`, so the stronger triangle formula fails there.

The deterministic core is `tsum_triangle_le`: for a nonnegative matrix that is one on the
diagonal and whose off-diagonal rows sum to at most `m`, the closed triangle at a vertex
is at most `1 + 3 m² + m³`.
-/

@[expose] public section
noncomputable section

open MeasureTheory PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.NormalizedSmallIntensity

variable {V : Type*}

/-! ### Elementary estimates -/

/-- `1 - exp (-t) ≥ t (1 - t / 2)` for `t ≥ 0`. -/
theorem mul_one_sub_half_le_one_sub_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    t * (1 - t / 2) ≤ 1 - Real.exp (-t) := by
  have hE := Real.quadratic_le_exp_of_nonneg ht
  have hpos : 0 < 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
  have key : 1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hE hpos.le, sq_nonneg (t ^ 2)]
  have hneg : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
    calc Real.exp (-t) = Real.exp (-t) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-t) * (Real.exp t * (1 - t + t ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = 1 - t + t ^ 2 / 2 := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  nlinarith

/-- An intensity at most one opens a pair with probability at least `β (1 - β / 2) J e`. -/
theorem ofReal_mul_le_intensityProfile (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V)
    (he : J e ≤ 1) :
    ENNReal.ofReal ((β : ℝ) * (1 - (β : ℝ) / 2)) * (J e : ℝ≥0∞) ≤
      (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) := by
  have hJ : (J e : ℝ) ≤ 1 := by exact_mod_cast he
  have hJ0 : (0 : ℝ) ≤ J e := (J e).coe_nonneg
  have hβ0 : (0 : ℝ) ≤ β := β.coe_nonneg
  have hval : ((unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0) : ℝ) =
      1 - Real.exp (-((β : ℝ) * (J e : ℝ))) := by
    change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) = _
    rw [neg_mul]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul'
    (J e).coe_nonneg, hval]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_one_sub_half_le_one_sub_exp_neg (mul_nonneg hβ0 hJ0)
  have : (β : ℝ) * (1 - (β : ℝ) / 2) * (J e : ℝ) ≤
      (β : ℝ) * (J e : ℝ) * (1 - (β : ℝ) * (J e : ℝ) / 2) := by
    nlinarith [mul_nonneg hβ0 hβ0, mul_nonneg (mul_nonneg hβ0 hβ0) hJ0,
      mul_nonneg (mul_nonneg (mul_nonneg hβ0 hβ0) hJ0) (sub_nonneg.2 hJ)]
  linarith

/-! ### The deterministic triangle bound -/

open Classical in
/-- Picking the diagonal entry from the left. -/
theorem tsum_ite_eq_mul_left (u : V) (f : V → ℝ≥0∞) :
    ∑' v, (if u = v then (1 : ℝ≥0∞) else 0) * f v = f u := by
  rw [tsum_eq_single u (fun v hv => by simp [Ne.symm hv])]
  simp

open Classical in
/-- Picking the diagonal entry from the right. -/
theorem tsum_mul_ite_eq_right (o : V) (f : V → ℝ≥0∞) :
    ∑' v, f v * (if v = o then (1 : ℝ≥0∞) else 0) = f o := by
  rw [tsum_eq_single o (fun v hv => by simp [hv])]
  simp

open Classical in
/-- **Closed triangle of `δ + t`.** If `t` vanishes on the diagonal and its rows sum to at
most `m`, the closed triangle of `δ + t` at `o` is at most `1 + 3 m² + m³`. -/
theorem tsum_triangle_le_of_add (t : V → V → ℝ≥0∞) (m : ℝ≥0∞) (ht0 : ∀ x, t x x = 0)
    (hrow : ∀ x, ∑' y, t x y ≤ m) (o : V) :
    ∑' u, ∑' v, ((if o = u then 1 else 0) + t o u) * ((if u = v then 1 else 0) + t u v) *
      ((if v = o then 1 else 0) + t v o) ≤ 1 + 3 * m ^ 2 + m ^ 3 := by
  have hent : ∀ x y, t x y ≤ m := fun x y => (ENNReal.le_tsum y).trans (hrow x)
  -- the two-step sum from `u` back to `o`
  have hinner : ∀ u, ∑' v, ((if u = v then 1 else 0) + t u v) *
      ((if v = o then 1 else 0) + t v o) ≤ (if u = o then 1 else 0) + 2 * t u o + m ^ 2 := by
    intro u
    have hW : ∑' v, t u v * t v o ≤ m ^ 2 :=
      calc ∑' v, t u v * t v o ≤ ∑' v, t u v * m :=
            ENNReal.tsum_le_tsum fun v => by gcongr; exact hent v o
        _ = (∑' v, t u v) * m := ENNReal.tsum_mul_right
        _ ≤ m * m := by gcongr; exact hrow u
        _ = m ^ 2 := (sq m).symm
    simp_rw [add_mul, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, tsum_ite_eq_mul_left,
      tsum_ite_eq_mul_left, tsum_mul_ite_eq_right]
    calc (if u = o then (1 : ℝ≥0∞) else 0) + t u o + (t u o + ∑' v, t u v * t v o)
        ≤ (if u = o then 1 else 0) + t u o + (t u o + m ^ 2) := by gcongr
      _ = _ := by ring
  calc ∑' u, ∑' v, ((if o = u then 1 else 0) + t o u) * ((if u = v then 1 else 0) + t u v) *
        ((if v = o then 1 else 0) + t v o)
      = ∑' u, ((if o = u then 1 else 0) + t o u) * ∑' v, ((if u = v then 1 else 0) + t u v) *
          ((if v = o then 1 else 0) + t v o) := by
        simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u, ((if o = u then 1 else 0) + t o u) *
          ((if u = o then 1 else 0) + 2 * t u o + m ^ 2) :=
        ENNReal.tsum_le_tsum fun u => by gcongr; exact hinner u
    _ = ((if o = o then 1 else 0) + 2 * t o o + m ^ 2) +
          ∑' u, t o u * ((if u = o then 1 else 0) + 2 * t u o + m ^ 2) := by
        rw [← tsum_ite_eq_mul_left o (fun u => (if u = o then 1 else 0) + 2 * t u o + m ^ 2),
          ← ENNReal.tsum_add]
        exact tsum_congr fun u => by ring
    _ = (1 + 2 * t o o + m ^ 2) + (t o o + 2 * ∑' u, t o u * t u o + m ^ 2 * ∑' u, t o u) := by
        simp only [ite_true]
        congr 1
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_mul_ite_eq_right (f := fun u => t o u),
          ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 2
        all_goals first | exact tsum_congr fun u => by ring | (funext u; ring)
    _ ≤ (1 + 2 * 0 + m ^ 2) + (0 + 2 * m ^ 2 + m ^ 2 * m) := by
        rw [ht0 o]
        gcongr
        · calc ∑' u, t o u * t u o ≤ ∑' u, t o u * m :=
                ENNReal.tsum_le_tsum fun u => by gcongr; exact hent u o
            _ = (∑' u, t o u) * m := ENNReal.tsum_mul_right
            _ ≤ m * m := by gcongr; exact hrow o
            _ = m ^ 2 := (sq m).symm
        · exact hrow o
    _ = 1 + 3 * m ^ 2 + m ^ 3 := by ring

open Classical in
/-- **Closed triangle.** For `a` equal to one on the diagonal, with off-diagonal rows
summing to at most `m`, `∑' u v, a o u * a u v * a v o ≤ 1 + 3 m² + m³`. -/
theorem tsum_triangle_le (a : V → V → ℝ≥0∞) (m : ℝ≥0∞) (ha : ∀ x, a x x = 1)
    (hrow : ∀ x, (∑' y, if y = x then 0 else a x y) ≤ m) (o : V) :
    ∑' u, ∑' v, a o u * a u v * a v o ≤ 1 + 3 * m ^ 2 + m ^ 3 := by
  have hsplit : ∀ x y, a x y = (if x = y then 1 else 0) + (if y = x then 0 else a x y) := by
    intro x y
    by_cases h : x = y
    · subst h; simp [ha]
    · simp [h, Ne.symm h]
  have := tsum_triangle_le_of_add (fun x y => if y = x then 0 else a x y) m (by simp) hrow o
  refine Eq.trans_le ?_ this
  refine tsum_congr fun u => tsum_congr fun v => ?_
  rw [← hsplit o u, ← hsplit u v, ← hsplit v o]

/-! ### Susceptibility and triangle bounds for normalized rows -/

variable [Countable V]

/-- Below `β = 1`, `(1 - β)⁻¹ = 1 + β / (1 - β)`. -/
theorem inv_one_sub_eq_one_add (β : ℝ≥0) (hβ : β < 1) :
    (1 - (β : ℝ≥0∞))⁻¹ = 1 + (β : ℝ≥0∞) / (1 - β) := by
  have h1 : (1 - (β : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hβ)).ne'
  have h2 : (1 - (β : ℝ≥0∞)) ≠ ⊤ := by finiteness
  calc (1 - (β : ℝ≥0∞))⁻¹ = (1 - β + β) / (1 - β) := by
        rw [tsub_add_cancel_of_le (by exact_mod_cast hβ.le), one_div]
    _ = (1 - β) / (1 - β) + β / (1 - β) := (ENNReal.div_add_div_same).symm
    _ = 1 + (β : ℝ≥0∞) / (1 - β) := by rw [ENNReal.div_self h1 h2]

open Classical in
/-- If off-diagonal rows of `J` sum to at most one and `β < 1`, every off-diagonal row of
the two-point function sums to at most `β / (1 - β)`. -/
theorem tsum_tau_offDiag_le (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 1) (β : ℝ≥0)
    (hβ : β < 1) (x : V) :
    (∑' y, if y = x then 0 else tau (intensityProfile J β) x y) ≤ (β : ℝ≥0∞) / (1 - β) := by
  have hchi := chi_intensity_le J 1 (by simpa using hrow) β (by simpa using hβ) x
  rw [chi_eq_tsum_tau, ENNReal.tsum_eq_add_tsum_ite x, tau_self, ENNReal.coe_one, mul_one,
    inv_one_sub_eq_one_add β hβ] at hchi
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 hchi

open Classical in
/-- **Susceptibility bounds.** If every off-diagonal row of `J` sums to exactly one
and `0 ≤ β < 1`, then `1 + β - β²/2 ≤ χ(o) ≤ (1 - β)⁻¹` at every root. -/
theorem chi_bounds (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1) (β : ℝ≥0)
    (hβ : β < 1) (o : V) :
    ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) o ∧
      chi (intensityProfile J β) o ≤ (1 - (β : ℝ≥0∞))⁻¹ := by
  refine ⟨?_, by simpa using chi_intensity_le J 1 (fun v => (hrow v).le) β (by simpa using hβ) o⟩
  have hβ1 : (β : ℝ) < 1 := by exact_mod_cast hβ
  have hβ0 : (0 : ℝ) ≤ β := β.coe_nonneg
  have hc0 : 0 ≤ (β : ℝ) * (1 - (β : ℝ) / 2) := mul_nonneg hβ0 (by linarith)
  simp only [rowSum_def] at hrow
  have hJle : ∀ y, y ≠ o → J s(o, y) ≤ 1 := by
    intro y hy
    have h := ENNReal.le_tsum (f := fun w => if w = o then 0 else (J s(o, w) : ℝ≥0∞)) y
    simp only [hy, ite_false, hrow o] at h
    exact_mod_cast h
  calc ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2)
      = 1 + ENNReal.ofReal ((β : ℝ) * (1 - (β : ℝ) / 2)) * 1 := by
        rw [mul_one, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hc0]
        congr 1; ring
    _ = 1 + rowSum (fun e => ENNReal.ofReal ((β : ℝ) * (1 - (β : ℝ) / 2)) * (J e : ℝ≥0∞))
        o := by
        simp only [rowSum_def]
        rw [← hrow o, ← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun y => by split_ifs <;> simp
    _ ≤ 1 + rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o := by
        simp only [rowSum_def]
        gcongr with y
        split_ifs with hy
        · exact le_rfl
        · exact ofReal_mul_le_intensityProfile J β _ (hJle y hy)
    _ ≤ chi (intensityProfile J β) o := one_add_rowSum_le_chi _ o

/-- **Triangle bounds.** If every off-diagonal row of `J` sums to at most one and
`β < 1`, then `1 ≤ Δ ≤ 1 + 3 m² + m³` with `m = β / (1 - β)`, at every root. -/
theorem triangle_bounds (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 1) (β : ℝ≥0)
    (hβ : β < 1) (o : V) :
    1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
        tau (intensityProfile J β) v o ∧
      ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v o ≤
        1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3 := by
  set q := intensityProfile J β
  refine ⟨?_, tsum_triangle_le (tau q) _ (tau_self q) (tsum_tau_offDiag_le J hrow β hβ) o⟩
  calc (1 : ℝ≥0∞) = tau q o o * tau q o o * tau q o o := by simp [tau_self]
    _ ≤ ∑' v, tau q o o * tau q o v * tau q v o :=
        ENNReal.le_tsum (f := fun v => tau q o o * tau q o v * tau q v o) o
    _ ≤ _ := ENNReal.le_tsum (f := fun u => ∑' v, tau q o u * tau q u v * tau q v o) o

/-- The bounds on `χ`, with an (unused) transitivity hypothesis. -/
theorem chi_bounds_of_transitive (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1)
    (_htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (β : ℝ≥0) (_hβ0 : 0 < β) (hβ : β < 1) (o : V) :
    ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) o ∧
      chi (intensityProfile J β) o ≤ (1 - (β : ℝ≥0∞))⁻¹ :=
  chi_bounds J hrow β hβ o

/-- The bounds on `Δ`, with an (unused) transitivity hypothesis. -/
theorem triangle_bounds_of_transitive (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1)
    (_htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (β : ℝ≥0) (_hβ0 : 0 < β) (hβ : β < 1) (o : V) :
    1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
        tau (intensityProfile J β) v o ∧
      ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v o ≤
        1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3 :=
  triangle_bounds J (fun v => (hrow v).le) β hβ o

/-! ### Non-vacuity: the nearest-neighbour kernel `1/2` on `ℤ` -/

/-- The nearest-neighbour kernel of weight `1/2` on `ℤ` exists. -/
theorem exists_line_kernel :
    ∃ J : Sym2 ℤ → ℝ≥0, ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0 :=
  ⟨Sym2.lift ⟨fun a b => if |b - a| = 1 then 1 / 2 else 0, fun a b => by simp only [abs_sub_comm]⟩,
    fun _ _ => rfl⟩

/-- Every off-diagonal row of the nearest-neighbour kernel `1/2` sums to exactly one. -/
theorem line_rowSum (J : Sym2 ℤ → ℝ≥0) (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0)
    (v : ℤ) : rowSum (fun e => (J e : ℝ≥0∞)) v = 1 := by
  rw [rowSum_def, tsum_eq_sum (s := {v - 1, v + 1})]
  · rw [Finset.sum_pair (by omega)]
    simp only [hJ, show v - 1 ≠ v by omega, show v + 1 ≠ v by omega, ite_false,
      show v - 1 - v = -1 by ring, show v + 1 - v = 1 by ring, abs_neg, abs_one, ite_true]
    rw [← ENNReal.coe_add, add_halves, ENNReal.coe_one]
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    split_ifs with h
    · rfl
    · rw [hJ]
      have : |w - v| ≠ 1 := by
        intro h1
        rcases abs_eq (zero_le_one' ℤ) |>.1 h1 with h2 | h2 <;> omega
      simp [this]

/-- The nearest-neighbour kernel is transitive in the spelling of `chi_bounds_of_transitive`. -/
theorem line_transitive (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0) :
    ∀ x y : ℤ, ∃ σ : ℤ ≃ ℤ, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := by
  intro x y
  refine ⟨Equiv.addRight (y - x), by simp, fun e => ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, Equiv.coe_addRight, hJ]
    congr 3
    ring

/-- Non-vacuity: the hypotheses of `chi_bounds_of_transitive` and `triangle_bounds_of_transitive`
hold on `ℤ` with the kernel `1/2` on nearest-neighbour pairs, for every `0 < β < 1`. -/
example (β : ℝ≥0) (hβ0 : 0 < β) (hβ : β < 1) :
    ∃ J : Sym2 ℤ → ℝ≥0,
      (ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) 0 ∧
        chi (intensityProfile J β) 0 ≤ (1 - (β : ℝ≥0∞))⁻¹) ∧
      (1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) 0 u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v 0 ∧
        ∑' u, ∑' v, tau (intensityProfile J β) 0 u * tau (intensityProfile J β) u v *
            tau (intensityProfile J β) v 0 ≤
          1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3) := by
  obtain ⟨J, hJ⟩ := exists_line_kernel
  exact ⟨J, chi_bounds_of_transitive J (fun v => by convert line_rowSum J hJ v)
      (line_transitive J hJ) β hβ0 hβ 0,
    triangle_bounds_of_transitive J (fun v => by convert line_rowSum J hJ v)
      (line_transitive J hJ) β hβ0 hβ 0⟩


/-! ### Regularity of `χ` and failure of the stronger triangle formula -/

/-- Real form of `chi_bounds` at a real intensity `0 ≤ β < 1`: `χ` is finite and
`1 + β - β²/2 ≤ χ ≤ (1 - β)⁻¹`. -/
theorem toReal_chi_bounds (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1)
    (o : V) :
    chi (intensityProfile J β.toNNReal) o ≠ ⊤ ∧
      1 + β - β ^ 2 / 2 ≤ (chi (intensityProfile J β.toNNReal) o).toReal ∧
      (chi (intensityProfile J β.toNNReal) o).toReal ≤ (1 - β)⁻¹ := by
  have hb : β.toNNReal < 1 := by
    rw [Real.toNNReal_lt_one]; exact hβ
  have hbβ : ((β.toNNReal : ℝ≥0) : ℝ) = β := Real.coe_toNNReal β hβ0
  obtain ⟨hlo, hhi⟩ := chi_bounds J hrow β.toNNReal hb o
  rw [hbβ] at hlo
  have hsub : (1 - ((β.toNNReal : ℝ≥0) : ℝ≥0∞)) ≠ 0 :=
    (tsub_pos_of_lt (by exact_mod_cast hb)).ne'
  have htop : (1 - ((β.toNNReal : ℝ≥0) : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hsub
  have hne : chi (intensityProfile J β.toNNReal) o ≠ ⊤ := ne_top_of_le_ne_top htop hhi
  refine ⟨hne, (ENNReal.ofReal_le_iff_le_toReal hne).1 hlo, ?_⟩
  refine (ENNReal.toReal_mono htop hhi).trans_eq ?_
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le (by exact_mod_cast hb.le) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.coe_toReal, hbβ]

/-- Real form of `triangle_bounds` at a real intensity `0 ≤ β < 1`: with
`Δ = ∑' u v, τ(o,u) τ(u,v) τ(v,o)`, `1 ≤ Δ.toReal ≤ 1 + 3 m² + m³` for `m = β / (1 - β)`. -/
theorem toReal_triangle_bounds (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1)
    (o : V) :
    1 ≤ (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) o u *
        tau (intensityProfile J β.toNNReal) u v * tau (intensityProfile J β.toNNReal) v o).toReal ∧
      (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) o u *
        tau (intensityProfile J β.toNNReal) u v *
          tau (intensityProfile J β.toNNReal) v o).toReal ≤
        1 + 3 * (β / (1 - β)) ^ 2 + (β / (1 - β)) ^ 3 := by
  have hb : β.toNNReal < 1 := by
    rw [Real.toNNReal_lt_one]; exact hβ
  obtain ⟨hlo, hhi⟩ := triangle_bounds J hrow β.toNNReal hb o
  have hm : ((β.toNNReal : ℝ≥0) : ℝ≥0∞) / (1 - (β.toNNReal : ℝ≥0∞)) =
      ENNReal.ofReal (β / (1 - β)) := by
    rw [ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_sub _ hβ0, ENNReal.ofReal_one]
    rfl
  have hm0 : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  have hrhs : (1 : ℝ≥0∞) + 3 * (((β.toNNReal : ℝ≥0) : ℝ≥0∞) / (1 - (β.toNNReal : ℝ≥0∞))) ^ 2 +
      (((β.toNNReal : ℝ≥0) : ℝ≥0∞) / (1 - (β.toNNReal : ℝ≥0∞))) ^ 3 =
      ENNReal.ofReal (1 + 3 * (β / (1 - β)) ^ 2 + (β / (1 - β)) ^ 3) := by
    rw [hm, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hm0, ENNReal.ofReal_pow hm0]
    norm_num
  rw [hrhs] at hhi
  have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  refine ⟨?_, ENNReal.toReal_le_of_le_ofReal (by positivity) hhi⟩
  simpa using ENNReal.toReal_mono hne hlo

/-- **Arithmetic core of the failure of the stronger triangle formula.** If `0 < β ≤ 1/100`,
`1 + β - β²/2 ≤ x`, `1 ≤ d ≤ 1 + 3 m² + m³` with `m = β / (1 - β)`, and
`D ≤ (1 - β)⁻²`, then `D < x (x - d) / (3 β² d²)`. -/
theorem lt_mul_sub_div_of_small {β x d D : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 100)
    (hx : 1 + β - β ^ 2 / 2 ≤ x) (hd1 : 1 ≤ d)
    (hd : d ≤ 1 + 3 * (β / (1 - β)) ^ 2 + (β / (1 - β)) ^ 3) (hD : D ≤ ((1 - β) ^ 2)⁻¹) :
    D < x * (x - d) / (3 * β ^ 2 * d ^ 2) := by
  set m := β / (1 - β) with hm_def
  have h1β : 0 < 1 - β := by linarith
  have hm0 : 0 ≤ m := div_nonneg hβ0.le h1β.le
  have hm : m ≤ 2 * β := by
    rw [hm_def, div_le_iff₀ h1β]; nlinarith
  have hm2 : m ^ 2 ≤ 4 * β ^ 2 := by nlinarith
  have hm3 : m ^ 3 ≤ 8 * β ^ 3 := by
    have := pow_le_pow_left₀ hm0 hm 3
    nlinarith
  have hd' : d ≤ 1 + 13 * β ^ 2 := by nlinarith
  have hd2 : d ≤ 2 := by nlinarith
  have hx1 : 1 ≤ x := by nlinarith
  have hxd : β / 2 ≤ x - d := by nlinarith
  have hD2 : D ≤ 2 := by
    refine hD.trans ?_
    rw [inv_le_comm₀ (by positivity) two_pos]
    nlinarith
  have hden : 0 < 3 * β ^ 2 * d ^ 2 := by positivity
  rw [lt_div_iff₀ hden]
  have hprod : β / 2 ≤ x * (x - d) := by nlinarith
  have hbound : D * (3 * β ^ 2 * d ^ 2) ≤ 24 * β ^ 2 := by
    calc D * (3 * β ^ 2 * d ^ 2) ≤ 2 * (3 * β ^ 2 * d ^ 2) :=
          mul_le_mul_of_nonneg_right hD2 hden.le
      _ ≤ 2 * (3 * β ^ 2 * 2 ^ 2) := by gcongr
      _ = 24 * β ^ 2 := by ring
  nlinarith

variable (J : Sym2 V → ℝ≥0)
  (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
  (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1)

include hrow in
/-- Below `β = 1` the susceptibility of a normalized model is finite. -/
theorem chi_ne_top_of_mem_Ioo (o : V) :
    ∀ β ∈ Set.Ioo (0 : ℝ) 1, chi (intensityProfile J β.toNNReal) o ≠ ⊤ :=
  fun _ hβ => (toReal_chi_bounds J hrow hβ.1.le hβ.2 o).1

include hJ hrow in
/-- **Local Lipschitz continuity on `(0, 1)`.** In a transitive model whose off-diagonal
rows sum to one, `β ↦ χ_β(o)` is locally Lipschitz on `(0, 1)`. -/
theorem locallyLipschitzOn_chi_Ioo_zero_one (o : V) :
    LocallyLipschitzOn (Set.Ioo 0 1)
      (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) :=
  locallyLipschitzOn_chi J hJ o (by rw [hrow]; exact ENNReal.one_ne_top) le_rfl
    (chi_ne_top_of_mem_Ioo J hrow o)

include hJ hrow in
/-- **Derivative bound on `(0, 1)`.** In a transitive model whose off-diagonal rows sum to
one, almost every `β ∈ (0, 1)` has a derivative `χ'(β) ≤ (1 - β)⁻²`. -/
theorem ae_hasDerivAt_chi_le_inv_one_sub_sq (o : V) :
    ∀ᵐ β, β ∈ Set.Ioo (0 : ℝ) 1 → ∃ D,
      HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) D β ∧
      D ≤ ((1 - β) ^ 2)⁻¹ := by
  have hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤ := by rw [hrow]; exact ENNReal.one_ne_top
  filter_upwards [ae_differentiableAt_chi J hJ o hR le_rfl (chi_ne_top_of_mem_Ioo J hrow o)]
    with β hβ hmem
  have hd := (hβ hmem).hasDerivAt
  refine ⟨_, hd, ?_⟩
  have hD := (hasDerivAt_chi_mem_Icc J hJ o hR le_rfl (chi_ne_top_of_mem_Ioo J hrow o) hmem
    hd).2
  obtain ⟨-, hx0, hx1⟩ := toReal_chi_bounds J hrow hmem.1.le hmem.2 o
  rw [hrow, ENNReal.toReal_one, one_mul] at hD
  refine hD.trans ?_
  rw [← inv_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hx1 2

include hJ hrow in
/-- **The stronger triangle formula fails at small intensity.** In a transitive model whose
off-diagonal rows sum to one, almost every `β ∈ (0, 1/100)` has a derivative
`χ'(β) < χ (χ - Δ) / (3 β² Δ²)`, where `Δ = ∑' u v, τ(o,u) τ(u,v) τ(v,o)`. -/
theorem ae_hasDerivAt_chi_lt_triangle_formula (o : V) :
    ∀ᵐ β, β ∈ Set.Ioo (0 : ℝ) (1 / 100) → ∃ D,
      HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) D β ∧
      D < (chi (intensityProfile J β.toNNReal) o).toReal *
          ((chi (intensityProfile J β.toNNReal) o).toReal -
            (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) o u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v o).toReal) /
          (3 * β ^ 2 * (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) o u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v o).toReal ^ 2) := by
  filter_upwards [ae_hasDerivAt_chi_le_inv_one_sub_sq J hJ hrow o] with β hβ hmem
  have hmem' : β ∈ Set.Ioo (0 : ℝ) 1 := ⟨hmem.1, hmem.2.trans (by norm_num)⟩
  obtain ⟨D, hd, hD⟩ := hβ hmem'
  obtain ⟨-, hx, -⟩ := toReal_chi_bounds J hrow hmem'.1.le hmem'.2 o
  obtain ⟨hd1, hd2⟩ := toReal_triangle_bounds J (fun v => (hrow v).le) hmem'.1.le hmem'.2 o
  exact ⟨D, hd, lt_mul_sub_div_of_small hmem.1 hmem.2.le hx hd1 hd2 hD⟩

end PercLib.Models.NormalizedSmallIntensity
