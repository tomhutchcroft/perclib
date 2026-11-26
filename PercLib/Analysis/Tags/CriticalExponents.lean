/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the critical-exponents assertion UBFE, proved from
`LogExponent.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.LogExponent
public import PercLib.Analysis.LogExponent.Defs

/-!
# Critical exponents: correspondence

Wiki correspondence for the hierarchy of asymptotic notions, from
`PercLib/Analysis/LogExponent.lean`.

## Main results

* `log_exponent_hierarchy`
* `asymptotic_comparison_and_log_exponent_conventions`
-/

@[expose] public section
noncomputable section

open Filter Asymptotics Real
open scoped Topology

namespace PercLib.Analysis

/-- **UBFE.** Asymptotic equivalence `f ~ c x^α` (`c > 0`) implies `f ≍ x^α`; `f ≍ x^α` with
`f` eventually positive implies logarithmic exponent `α`; `x^α (log x)^b (log log x)^c` has
logarithmic exponent `α` and is `≍ x^α` only when `b = c = 0`; and for every `α` some eventually
positive `f ≍ x^α` is not asymptotically equivalent to any `c x^α`. -/
@[tag "UBFE"]
theorem log_exponent_hierarchy :
    (∀ (f : ℝ → ℝ) (α c : ℝ), 0 < c → (f ~[atTop] fun x => c * x ^ α) →
      f =Θ[atTop] fun x => x ^ α) ∧
    (∀ (f : ℝ → ℝ) (α : ℝ), (∀ᶠ x in atTop, 0 < f x) → (f =Θ[atTop] fun x => x ^ α) →
      Tendsto (fun x => log (f x) / log x) atTop (𝓝 α)) ∧
    (∀ α b c : ℝ,
      Tendsto (fun x => log (x ^ α * log x ^ b * log (log x) ^ c) / log x) atTop (𝓝 α) ∧
      (((fun x => x ^ α * log x ^ b * log (log x) ^ c) =Θ[atTop] fun x => x ^ α) ↔
        b = 0 ∧ c = 0)) ∧
    (∀ α : ℝ, ∃ f : ℝ → ℝ, (∀ᶠ x in atTop, 0 < f x) ∧ (f =Θ[atTop] fun x => x ^ α) ∧
      ∀ c, ¬ f ~[atTop] fun x => c * x ^ α) := by
  refine ⟨fun f α c hc h => isTheta_rpow_of_isEquivalent hc h,
    fun f α hf h => tendsto_log_div_log_of_isTheta_rpow hf h,
    fun α b c => ⟨tendsto_log_div_log_rpow_mul_log_rpow_mul_log_log_rpow α b c,
      isTheta_rpow_mul_log_rpow_mul_log_log_rpow_iff α b c⟩, fun α => ?_⟩
  have hs : ∀ x : ℝ, 1 ≤ 2 + sin x := fun x => by linarith [neg_one_le_sin x]
  refine ⟨fun x => (2 + sin x) * x ^ α, ?_, isTheta_two_add_sin_mul_rpow α, fun c => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos (by linarith [hs x]) (rpow_pos_of_pos hx α)
  rcases lt_or_ge 0 c with hc | hc
  · exact not_isEquivalent_two_add_sin_mul_rpow α hc
  · -- for `c ≤ 0`, `f ~ c x^α` would force `f ≤ c x^α / 2 ≤ 0` eventually
    intro h
    obtain ⟨x, hx⟩ := ((h.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)).and
      (eventually_gt_atTop (0 : ℝ))).exists
    obtain ⟨hb, hx0⟩ := hx
    have hxa : 0 < x ^ α := rpow_pos_of_pos hx0 α
    have hv : c * x ^ α ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hxa.le
    have hf : 0 < (2 + sin x) * x ^ α := mul_pos (by linarith [hs x]) hxa
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonpos hv] at hb
    have := le_abs_self ((2 + sin x) * x ^ α - c * x ^ α)
    linarith

/-- **Asymptotic equivalence, comparison and logarithmic power exponent.** For eventually
nonzero `g`, `f ~ g` (mathlib's `IsEquivalent`) iff `f/g → 1`. For eventually positive `f, g`,
`f ≍ g` (mathlib's `IsTheta`) iff `c g ≤ f ≤ C g` eventually for some `0 < c ≤ C`. The
logarithmic power exponent `α` (`HasLogExponent atTop f α`) is `log f(x)/log x → α`, and for
eventually positive `f` it is equivalent to `f(x) = x^{α + o(1)}`. At a parameter tending to
zero (`HasLogExponent (𝓝[>] 0) f α`) it is `log f(ε)/log ε → α`, equivalently
`f(ε) = ε^{α + o(1)}`. -/
@[tag "PHLF"]
theorem asymptotic_comparison_and_log_exponent_conventions :
    (∀ f g : ℝ → ℝ, (∀ᶠ x in atTop, g x ≠ 0) →
      (f ~[atTop] g ↔ Tendsto (f / g) atTop (𝓝 1))) ∧
    (∀ f g : ℝ → ℝ, (∀ᶠ x in atTop, 0 < f x) → (∀ᶠ x in atTop, 0 < g x) →
      (f =Θ[atTop] g ↔
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ x in atTop, c * g x ≤ f x ∧ f x ≤ C * g x)) ∧
    (∀ (f : ℝ → ℝ) (α : ℝ),
      HasLogExponent atTop f α ↔ Tendsto (fun x => log (f x) / log x) atTop (𝓝 α)) ∧
    (∀ (f : ℝ → ℝ) (α : ℝ), (∀ᶠ x in atTop, 0 < f x) →
      (HasLogExponent atTop f α ↔
        ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ x in atTop, f x = x ^ (α + e x))) ∧
    (∀ (f : ℝ → ℝ) (α : ℝ),
      HasLogExponent (𝓝[>] 0) f α ↔ Tendsto (fun ε => log (f ε) / log ε) (𝓝[>] 0) (𝓝 α)) ∧
    (∀ (f : ℝ → ℝ) (α : ℝ), (∀ᶠ ε in 𝓝[>] 0, 0 < f ε) →
      (HasLogExponent (𝓝[>] 0) f α ↔
        ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧ ∀ᶠ ε in 𝓝[>] 0, f ε = ε ^ (α + e ε))) :=
  ⟨fun _ _ hg => isEquivalent_iff_tendsto_one hg,
    fun _ _ hf hg => isTheta_iff_exists_const_mul_le hf hg,
    fun _ _ => hasLogExponent_iff,
    fun _ _ hf => hasLogExponent_atTop_iff_exists_rpow hf,
    fun _ _ => hasLogExponent_iff,
    fun _ _ hf => hasLogExponent_nhdsGT_zero_iff_exists_rpow hf⟩

end PercLib.Analysis
