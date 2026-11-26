/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Logarithmic exponents of eventually positive real functions: asymptotic equivalence to
`c x^α` implies `Θ(x^α)`, which implies logarithmic exponent `α`, and neither converse
holds. New proofs against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
The logarithmic exponent is written out as `Tendsto (fun x => log (f x) / log x) atTop (𝓝 α)`;
no definition is introduced.
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic exponents

Asymptotic equivalence to `c x^α` implies `Θ(x^α)`, which implies logarithmic exponent `α`; neither
converse holds.

## Main results

* `isTheta_rpow_of_isEquivalent`
* `tendsto_log_div_log_of_isTheta_rpow`
* `tendsto_log_div_log_of_isEquivalent`
* `tendsto_log_div_log_rpow_mul_log_rpow_mul_log_log_rpow`
* `isTheta_rpow_mul_log_rpow_mul_log_log_rpow_iff`
* `isTheta_two_add_sin_mul_rpow`
* `not_isEquivalent_two_add_sin_mul_rpow`
-/

@[expose] public section

open Filter Asymptotics Real
open scoped Topology

namespace PercLib.Analysis

/-- If `f =Θ g` and both are eventually positive, then `log f - log g` is bounded. -/
theorem isBigO_log_sub_log_of_isTheta {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ∀ᶠ x in l, 0 < f x) (hg : ∀ᶠ x in l, 0 < g x) (h : f =Θ[l] g) :
    (fun x => log (f x) - log (g x)) =O[l] (fun _ => (1 : ℝ)) := by
  obtain ⟨C, hC, hCw⟩ := h.1.exists_pos
  obtain ⟨D, hD, hDw⟩ := h.2.exists_pos
  refine IsBigO.of_bound (|log C| + |log D|) ?_
  filter_upwards [hf, hg, hCw.bound, hDw.bound] with x hfx hgx h1 h2
  rw [Real.norm_of_nonneg hfx.le, Real.norm_of_nonneg hgx.le] at h1 h2
  have l1 : log (f x) ≤ log C + log (g x) := by
    rw [← log_mul hC.ne' hgx.ne']; exact log_le_log hfx h1
  have l2 : log (g x) ≤ log D + log (f x) := by
    rw [← log_mul hD.ne' hfx.ne']; exact log_le_log hgx h2
  rw [norm_one, mul_one, Real.norm_eq_abs, abs_le]
  constructor
  · linarith [le_abs_self (log D), abs_nonneg (log C)]
  · linarith [le_abs_self (log C), abs_nonneg (log D)]

/-- A function tending to infinity dominates the constant `1`. -/
theorem one_isLittleO_of_tendsto_atTop {F : ℝ → ℝ} (h : Tendsto F atTop atTop) :
    (fun _ => (1 : ℝ)) =o[atTop] F := by
  rw [isLittleO_one_left_iff]
  simp only [Real.norm_eq_abs]
  exact tendsto_abs_atTop_atTop.comp h

/-- A function `f` has logarithmic exponent `α` as soon as `log f - α log` is `o(log)`. -/
theorem tendsto_log_div_log_of_isLittleO {f : ℝ → ℝ} {α : ℝ}
    (h : (fun x => log (f x) - α * log x) =o[atTop] log) :
    Tendsto (fun x => log (f x) / log x) atTop (𝓝 α) := by
  have h0 := h.tendsto_div_nhds_zero
  have h1 : Tendsto (fun x => (log (f x) - α * log x) / log x + α) atTop (𝓝 (0 + α)) :=
    h0.add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have : log x ≠ 0 := (log_pos hx).ne'
  field_simp
  ring

/-- `Θ(x^α)` implies logarithmic exponent `α` for an eventually positive function. -/
theorem tendsto_log_div_log_of_isTheta_rpow {f : ℝ → ℝ} {α : ℝ}
    (hf : ∀ᶠ x in atTop, 0 < f x) (h : f =Θ[atTop] fun x => x ^ α) :
    Tendsto (fun x => log (f x) / log x) atTop (𝓝 α) := by
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < x ^ α := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact rpow_pos_of_pos hx α
  have hb := isBigO_log_sub_log_of_isTheta hf hpos h
  have hlog : (fun _ => (1 : ℝ)) =o[atTop] log := one_isLittleO_of_tendsto_atTop tendsto_log_atTop
  refine tendsto_log_div_log_of_isLittleO ((hb.trans_isLittleO hlog).congr' ?_ .rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [log_rpow hx]

/-- Asymptotic equivalence to `c x^α` with `c > 0` implies `Θ(x^α)`. -/
theorem isTheta_rpow_of_isEquivalent {f : ℝ → ℝ} {α c : ℝ} (hc : 0 < c)
    (h : f ~[atTop] fun x => c * x ^ α) : f =Θ[atTop] fun x => x ^ α :=
  h.isTheta.trans ((isTheta_const_mul_left hc.ne').2 (isTheta_refl _ _))

/-- Asymptotic equivalence to `c x^α` with `c > 0` implies logarithmic exponent `α`. -/
theorem tendsto_log_div_log_of_isEquivalent {f : ℝ → ℝ} {α c : ℝ} (hc : 0 < c)
    (hf : ∀ᶠ x in atTop, 0 < f x) (h : f ~[atTop] fun x => c * x ^ α) :
    Tendsto (fun x => log (f x) / log x) atTop (𝓝 α) :=
  tendsto_log_div_log_of_isTheta_rpow hf (isTheta_rpow_of_isEquivalent hc h)

/-- `log ∘ log = o(log)` at infinity. -/
theorem isLittleO_log_log_log_atTop : (fun x => log (log x)) =o[atTop] log :=
  isLittleO_log_id_atTop.comp_tendsto tendsto_log_atTop

/-- `log ∘ log ∘ log = o(log)` at infinity. -/
theorem isLittleO_log_log_log_log_atTop : (fun x => log (log (log x))) =o[atTop] log :=
  (isLittleO_log_id_atTop.comp_tendsto
    (tendsto_log_atTop.comp tendsto_log_atTop)).trans isLittleO_log_log_log_atTop

/-- For `x > e^e`, the logarithm of `x^α (log x)^b (log log x)^c` splits into three terms. -/
theorem log_rpow_mul_log_rpow_mul_log_log_rpow {x : ℝ} (α b c : ℝ)
    (hx0 : 0 < x) (hx : exp 1 < log x) :
    log (x ^ α * log x ^ b * log (log x) ^ c) =
      α * log x + b * log (log x) + c * log (log (log x)) := by
  have hl : 0 < log x := (exp_pos 1).trans hx
  have hll : 1 < log (log x) := by
    rw [← log_exp 1]; exact log_lt_log (exp_pos 1) hx
  have hll0 : 0 < log (log x) := one_pos.trans hll
  rw [log_mul (by positivity) (rpow_pos_of_pos hll0 c).ne',
    log_mul (rpow_pos_of_pos hx0 α).ne' (rpow_pos_of_pos hl b).ne',
    log_rpow hx0, log_rpow hl, log_rpow hll0]

/-- Eventually `log x > e`. -/
theorem eventually_exp_one_lt_log : ∀ᶠ x in atTop, exp 1 < log x :=
  tendsto_log_atTop.eventually_gt_atTop _

/-- `x^α (log x)^b (log log x)^c` is eventually positive. -/
theorem eventually_pos_rpow_mul_log_rpow_mul_log_log_rpow (α b c : ℝ) :
    ∀ᶠ x in atTop, 0 < x ^ α * log x ^ b * log (log x) ^ c := by
  filter_upwards [eventually_exp_one_lt_log, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hl : 0 < log x := (exp_pos 1).trans hx
  have hll : 0 < log (log x) := by
    rw [← log_one]; exact log_lt_log one_pos ((one_lt_exp_iff.2 one_pos).trans hx)
  positivity

/-- For all real `b, c`, the function `x^α (log x)^b (log log x)^c` has logarithmic
exponent `α`. -/
theorem tendsto_log_div_log_rpow_mul_log_rpow_mul_log_log_rpow (α b c : ℝ) :
    Tendsto (fun x => log (x ^ α * log x ^ b * log (log x) ^ c) / log x) atTop (𝓝 α) := by
  refine tendsto_log_div_log_of_isLittleO ?_
  have h := (isLittleO_log_log_log_atTop.const_mul_left b).add
    (isLittleO_log_log_log_log_atTop.const_mul_left c)
  refine h.congr' ?_ .rfl
  filter_upwards [eventually_exp_one_lt_log, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [log_rpow_mul_log_rpow_mul_log_log_rpow α b c hx0 hx]
  ring

/-- The function `x^α (log x)^b (log log x)^c` is `Θ(x^α)` exactly when `b = c = 0`. -/
theorem isTheta_rpow_mul_log_rpow_mul_log_log_rpow_iff (α b c : ℝ) :
    ((fun x => x ^ α * log x ^ b * log (log x) ^ c) =Θ[atTop] fun x => x ^ α) ↔
      b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hpos : ∀ᶠ x : ℝ in atTop, 0 < x ^ α := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact rpow_pos_of_pos hx α
    have hb := isBigO_log_sub_log_of_isTheta
      (eventually_pos_rpow_mul_log_rpow_mul_log_log_rpow α b c) hpos h
    -- `b log log x + c log log log x` is bounded.
    have hb' : (fun x => b * log (log x) + c * log (log (log x))) =O[atTop]
        (fun _ => (1 : ℝ)) := by
      refine hb.congr' ?_ .rfl
      filter_upwards [eventually_exp_one_lt_log, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      rw [log_rpow_mul_log_rpow_mul_log_log_rpow α b c hx0 hx, log_rpow hx0]
      ring
    have hL : Tendsto (fun x => log (log x)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_log_atTop
    -- Dividing by `log log x` forces `b = 0`.
    have hb0 : b = 0 := by
      have h1 : Tendsto (fun x => (b * log (log x) + c * log (log (log x))) / log (log x))
          atTop (𝓝 0) :=
        (hb'.trans_isLittleO (one_isLittleO_of_tendsto_atTop hL)).tendsto_div_nhds_zero
      have h2 : Tendsto (fun x => b + c * (log (log (log x)) / log (log x))) atTop
          (𝓝 (b + c * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul
          ((isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero))
      rw [mul_zero, add_zero] at h2
      refine tendsto_nhds_unique (h2.congr' ?_) h1
      filter_upwards [hL.eventually_gt_atTop 0] with x hx
      field_simp
    subst hb0
    -- Then `c log log log x` is bounded although `log log log x → ∞`, forcing `c = 0`.
    refine ⟨rfl, ?_⟩
    by_contra hc
    have h3 : (fun x => log (log (log x))) =O[atTop] (fun _ => (1 : ℝ)) :=
      (isBigO_const_mul_left_iff hc).1 (hb'.congr' (by simp) .rfl)
    have hLL : Tendsto (fun x => log (log (log x))) atTop atTop := tendsto_log_atTop.comp hL
    exact isLittleO_irrefl' ((hLL.eventually_gt_atTop 0).frequently.mono
      fun x (hx : 0 < log (log (log x))) => by simpa using hx.ne')
      (h3.trans_isLittleO (one_isLittleO_of_tendsto_atTop hLL))
  · rintro ⟨rfl, rfl⟩
    simpa using isTheta_refl (fun x : ℝ => x ^ α) atTop

/-- The sine function has no limit at infinity. -/
theorem not_tendsto_sin_atTop (L : ℝ) : ¬Tendsto sin atTop (𝓝 L) := by
  intro h
  have hseq : ∀ a : ℝ, Tendsto (fun n : ℕ => a + n * (2 * π)) atTop atTop := fun a =>
    tendsto_atTop_add_const_left _ a
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 L) :=
    (h.comp (hseq 0)).congr fun n => by simpa [Function.comp] using sin_add_nat_mul_two_pi 0 n
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 L) :=
    (h.comp (hseq (π / 2))).congr fun n => by simp [Function.comp]
  have e0 : (0 : ℝ) = L := tendsto_nhds_unique tendsto_const_nhds h0
  have e1 : (1 : ℝ) = L := tendsto_nhds_unique tendsto_const_nhds h1
  exact one_ne_zero (e1.trans e0.symm)

/-- `Θ(x^α)` does not imply asymptotic equivalence to `c x^α` for any `c > 0`: the
eventually positive function `(2 + sin x) x^α` is `Θ(x^α)`. -/
theorem isTheta_two_add_sin_mul_rpow (α : ℝ) :
    (fun x => (2 + sin x) * x ^ α) =Θ[atTop] fun x => x ^ α := by
  have hs : ∀ x : ℝ, 1 ≤ 2 + sin x ∧ 2 + sin x ≤ 3 := fun x =>
    ⟨by linarith [neg_one_le_sin x], by linarith [sin_le_one x]⟩
  refine ⟨IsBigO.of_bound 3 (Eventually.of_forall fun x => ?_),
    IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)⟩
  · have hn : ‖2 + sin x‖ = 2 + sin x := Real.norm_of_nonneg (by linarith [hs x])
    rw [norm_mul, hn]
    exact mul_le_mul_of_nonneg_right (hs x).2 (norm_nonneg _)
  · have hn : ‖2 + sin x‖ = 2 + sin x := Real.norm_of_nonneg (by linarith [hs x])
    rw [norm_mul, hn, one_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) (hs x).1

/-- The function `(2 + sin x) x^α` is not asymptotically equivalent to `c x^α` for any
`c > 0`, although it is `Θ(x^α)`. -/
theorem not_isEquivalent_two_add_sin_mul_rpow (α : ℝ) {c : ℝ} (hc : 0 < c) :
    ¬(fun x => (2 + sin x) * x ^ α) ~[atTop] fun x => c * x ^ α := by
  intro h
  have hz : ∀ᶠ x : ℝ in atTop, c * x ^ α ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (mul_pos hc (rpow_pos_of_pos hx α)).ne'
  have h1 := (isEquivalent_iff_tendsto_one hz).1 h
  have h2 : Tendsto (fun x => c * ((2 + sin x) * x ^ α / (c * x ^ α)) - 2) atTop
      (𝓝 (c * 1 - 2)) := (h1.const_mul c).sub_const 2
  refine not_tendsto_sin_atTop (c * 1 - 2) (h2.congr' ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have : x ^ α ≠ 0 := (rpow_pos_of_pos hx α).ne'
  field_simp
  ring

/-! ### Non-vacuity witnesses -/

/-- `2 x^3` is asymptotically equivalent to `2 x^3`, hence `Θ(x^3)` with logarithmic
exponent `3`. -/
example : (fun x : ℝ => 2 * x ^ (3 : ℝ)) =Θ[atTop] (fun x => x ^ (3 : ℝ)) ∧
    Tendsto (fun x : ℝ => log (2 * x ^ (3 : ℝ)) / log x) atTop (𝓝 3) := by
  have hf : ∀ᶠ x : ℝ in atTop, 0 < 2 * x ^ (3 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos two_pos (rpow_pos_of_pos hx _)
  exact ⟨isTheta_rpow_of_isEquivalent two_pos (IsEquivalent.refl),
    tendsto_log_div_log_of_isEquivalent two_pos hf IsEquivalent.refl⟩

/-- With `b = 1, c = 0`: `x^α log x` has logarithmic exponent `α` and is not `Θ(x^α)`. -/
example (α : ℝ) :
    Tendsto (fun x => log (x ^ α * log x ^ (1 : ℝ) * log (log x) ^ (0 : ℝ)) / log x)
        atTop (𝓝 α) ∧
      ¬(fun x => x ^ α * log x ^ (1 : ℝ) * log (log x) ^ (0 : ℝ)) =Θ[atTop]
        fun x => x ^ α :=
  ⟨tendsto_log_div_log_rpow_mul_log_rpow_mul_log_log_rpow α 1 0, fun h =>
    one_ne_zero ((isTheta_rpow_mul_log_rpow_mul_log_log_rpow_iff α 1 0).1 h).1⟩

/-- The `sin` example with `α = 0`, `c = 2`. -/
example : (fun x => (2 + sin x) * x ^ (0 : ℝ)) =Θ[atTop] (fun x => x ^ (0 : ℝ)) ∧
    ¬(fun x => (2 + sin x) * x ^ (0 : ℝ)) ~[atTop] fun x => 2 * x ^ (0 : ℝ) :=
  ⟨isTheta_two_add_sin_mul_rpow 0, not_isEquivalent_two_add_sin_mul_rpow 0 two_pos⟩

end PercLib.Analysis
