/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference: the
standard logarithmic conventions for critical exponents.
-/
module

public import PercLib.Analysis.LogExponent

/-!
# Logarithmic power exponents

A function `f` has *logarithmic power exponent* `α` along a filter `l` on `ℝ` when
`log f(x) / log x → α` along `l`. The two cases of interest are `l = atTop` and, for a
parameter tending to zero, `l = 𝓝[>] 0` (where `log ε < 0`).

Asymptotic equivalence `f ~ g` and two-sided comparison `f ≍ g` are mathlib's
`Asymptotics.IsEquivalent` and `Asymptotics.IsTheta`; for eventually positive functions the
latter is the existence of `0 < c ≤ C` with `c g ≤ f ≤ C g` eventually.

## Main definitions

* `PercLib.Analysis.HasLogExponent l f α`: `log f(x) / log x → α` along `l`.

## Main results

* `hasLogExponent_iff_exists_rpow`: along a filter eventually in `(0, ∞) \ {1}`, and for
  eventually positive `f`, `HasLogExponent l f α ↔ f(x) = x^{α + o(1)}`;
  `hasLogExponent_atTop_iff_exists_rpow`, `hasLogExponent_nhdsGT_zero_iff_exists_rpow`.
* `isTheta_iff_exists_const_mul_le`: for eventually positive `f, g`, `f =Θ g` iff
  `c g ≤ f ≤ C g` eventually for some `0 < c ≤ C`.
* `hasLogExponent_of_isTheta_rpow`: `f ≍ x^α` implies logarithmic exponent `α` at infinity.
-/

@[expose] public section
noncomputable section

open Filter Asymptotics Real
open scoped Topology

namespace PercLib.Analysis

/-- `f` has logarithmic power exponent `α` along `l`: `log f(x) / log x → α`. Along `atTop`
this is the exponent at infinity, along `𝓝[>] 0` the exponent of a parameter tending to zero. -/
def HasLogExponent (l : Filter ℝ) (f : ℝ → ℝ) (α : ℝ) : Prop :=
  Tendsto (fun x => log (f x) / log x) l (𝓝 α)

variable {l : Filter ℝ} {f g : ℝ → ℝ} {α β : ℝ}

theorem hasLogExponent_iff :
    HasLogExponent l f α ↔ Tendsto (fun x => log (f x) / log x) l (𝓝 α) :=
  Iff.rfl

/-- The logarithmic exponent is unique along a nontrivial filter. -/
theorem HasLogExponent.unique [l.NeBot] (hα : HasLogExponent l f α)
    (hβ : HasLogExponent l f β) : α = β :=
  tendsto_nhds_unique hα hβ

/-- The logarithmic exponent only depends on the eventual values of `f`. -/
theorem HasLogExponent.congr' (h : HasLogExponent l f α) (hfg : f =ᶠ[l] g) :
    HasLogExponent l g α :=
  Tendsto.congr' (hfg.mono fun x hx => by simp only [hx]) h

theorem hasLogExponent_congr' (hfg : f =ᶠ[l] g) :
    HasLogExponent l f α ↔ HasLogExponent l g α :=
  ⟨fun h => h.congr' hfg, fun h => h.congr' hfg.symm⟩

/-- **`f(x) = x^{α + o(1)}`.** Along a filter eventually in `(0, ∞) \ {1}`, an eventually
positive `f` has logarithmic exponent `α` iff `f(x) = x^{α + e(x)}` eventually for some
`e → 0`. -/
theorem hasLogExponent_iff_exists_rpow (hl : ∀ᶠ x in l, 0 < x ∧ x ≠ 1)
    (hf : ∀ᶠ x in l, 0 < f x) :
    HasLogExponent l f α ↔
      ∃ e : ℝ → ℝ, Tendsto e l (𝓝 0) ∧ ∀ᶠ x in l, f x = x ^ (α + e x) := by
  constructor
  · intro h
    refine ⟨fun x => log (f x) / log x - α, by simpa using h.sub_const α, ?_⟩
    filter_upwards [hl, hf] with x ⟨hx0, hx1⟩ hfx
    have hlog : log x ≠ 0 := log_ne_zero_of_pos_of_ne_one hx0 hx1
    rw [add_sub_cancel, rpow_def_of_pos hx0,
      show log x * (log (f x) / log x) = log (f x) by field_simp, exp_log hfx]
  · rintro ⟨e, he, hfe⟩
    have : Tendsto (fun x => α + e x) l (𝓝 α) := by simpa using he.const_add α
    refine this.congr' ?_
    filter_upwards [hl, hfe] with x ⟨hx0, hx1⟩ hfx
    have hlog : log x ≠ 0 := log_ne_zero_of_pos_of_ne_one hx0 hx1
    rw [hfx, log_rpow hx0]
    field_simp

/-- `f(x) = x^{α + o(1)}` as `x → ∞`. -/
theorem hasLogExponent_atTop_iff_exists_rpow (hf : ∀ᶠ x in atTop, 0 < f x) :
    HasLogExponent atTop f α ↔
      ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ x in atTop, f x = x ^ (α + e x) :=
  hasLogExponent_iff_exists_rpow ((eventually_gt_atTop 1).mono fun _ hx =>
    ⟨zero_lt_one.trans hx, hx.ne'⟩) hf

/-- `f(ε) = ε^{α + o(1)}` as `ε ↓ 0`. -/
theorem hasLogExponent_nhdsGT_zero_iff_exists_rpow (hf : ∀ᶠ x in 𝓝[>] 0, 0 < f x) :
    HasLogExponent (𝓝[>] 0) f α ↔
      ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧ ∀ᶠ x in 𝓝[>] 0, f x = x ^ (α + e x) :=
  hasLogExponent_iff_exists_rpow (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos)
    fun _ hx => ⟨hx.1, hx.2.ne⟩) hf

/-- **Two-sided comparison of positive functions.** For eventually positive `f` and `g`,
`f =Θ g` iff `c g ≤ f ≤ C g` eventually for some constants `0 < c ≤ C`. -/
theorem isTheta_iff_exists_const_mul_le (hf : ∀ᶠ x in l, 0 < f x) (hg : ∀ᶠ x in l, 0 < g x) :
    f =Θ[l] g ↔ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ x in l, c * g x ≤ f x ∧ f x ≤ C * g x := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨C, hC⟩ := isBigO_iff.1 h₁
    obtain ⟨C', hC'⟩ := isBigO_iff.1 h₂
    have hpos : 0 < max C' 1 := lt_max_of_lt_right one_pos
    refine ⟨(max C' 1)⁻¹, max C (max C' 1)⁻¹, inv_pos.2 hpos, le_max_right _ _, ?_⟩
    filter_upwards [hf, hg, hC, hC'] with x hfx hgx hCx hC'x
    rw [Real.norm_of_nonneg hfx.le, Real.norm_of_nonneg hgx.le] at hCx hC'x
    refine ⟨?_, hCx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgx.le)⟩
    rw [inv_mul_le_iff₀ hpos]
    exact hC'x.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hfx.le)
  · rintro ⟨c, C, hc, -, hcC⟩
    refine ⟨isBigO_iff.2 ⟨C, ?_⟩, isBigO_iff.2 ⟨c⁻¹, ?_⟩⟩
    · filter_upwards [hf, hg, hcC] with x hfx hgx hx
      rw [Real.norm_of_nonneg hfx.le, Real.norm_of_nonneg hgx.le]
      exact hx.2
    · filter_upwards [hf, hg, hcC] with x hfx hgx hx
      rw [Real.norm_of_nonneg hfx.le, Real.norm_of_nonneg hgx.le, inv_mul_eq_div,
        le_div_iff₀ hc, mul_comm]
      exact hx.1

/-- Two-sided power comparison `f ≍ x^α` implies logarithmic exponent `α` at infinity. -/
theorem hasLogExponent_of_isTheta_rpow (hf : ∀ᶠ x in atTop, 0 < f x)
    (h : f =Θ[atTop] fun x => x ^ α) : HasLogExponent atTop f α :=
  tendsto_log_div_log_of_isTheta_rpow hf h

end PercLib.Analysis
