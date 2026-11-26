/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Dilation rule for continuum limits of multipoint connection probabilities under a regularly
varying normalisation (wiki article `multipoint-trees`). New proofs; nothing is copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Analysis.RegularVariation.Defs

/-!
# Regularly varying normalisation fixes the dilation exponent

Let `f` be eventually positive with `f (c s) / f s → c ^ σ` for every `c > 0`. If the rescaled
`k`-point connection probabilities `f(λ)^k τ_k(⌊λ x_1⌋, …, ⌊λ x_k⌋)` of a bond law on `ℤ^d`
converge, as `λ → ∞` through the reals, to a finite limit `T_k(x)` at every tuple of pairwise
distinct points, then `T_k(c x) = c^{-kσ} T_k(x)` for every `c > 0`.

The analytic core is `tendsto_mul_pow_comp_const_mul`: if `f s ^ k * u s → L` and
`f (c s) / f s → r ≠ 0`, then `f s ^ k * u (c s) → r⁻¹ ^ k * L`.

## Main results

* `tendsto_mul_pow_comp_const_mul`: change of scale in a normalised limit.
* `Bond.multipointLimit_smul`: the dilation rule `T_k(c x) = c^{-kσ} T_k(x)`.
* `Bond.multipointLimit_smul_of_regularlyVarying`: the same with `f` regularly varying in the
  sense of `PercLib.Analysis.RegularlyVarying`.
-/

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory

namespace PercLib

/-- **Change of scale in a normalised limit.** If `f s ^ k * u s → L` as `s → ∞`, `c > 0`,
`f` is eventually nonzero and `f (c s) / f s → r ≠ 0`, then `f s ^ k * u (c s) → r⁻¹ ^ k * L`. -/
theorem tendsto_mul_pow_comp_const_mul {f u : ℝ → ℝ} {k : ℕ} {c r L : ℝ} (hc : 0 < c)
    (hf : ∀ᶠ s in atTop, f s ≠ 0) (hr : r ≠ 0)
    (hratio : Tendsto (fun s => f (c * s) / f s) atTop (𝓝 r))
    (hu : Tendsto (fun s => f s ^ k * u s) atTop (𝓝 L)) :
    Tendsto (fun s => f s ^ k * u (c * s)) atTop (𝓝 (r⁻¹ ^ k * L)) := by
  have hcs : Tendsto (fun s : ℝ => c * s) atTop atTop := tendsto_id.const_mul_atTop hc
  have h1 : Tendsto (fun s => ((f (c * s) / f s)⁻¹) ^ k * (f (c * s) ^ k * u (c * s)))
      atTop (𝓝 (r⁻¹ ^ k * L)) :=
    ((hratio.inv₀ hr).pow k).mul (hu.comp hcs)
  refine h1.congr' ?_
  filter_upwards [hcs.eventually hf] with s hs
  have := pow_ne_zero k hs
  rw [inv_div, div_pow]
  field_simp

namespace Percolation.Bond

variable {d k : ℕ}

/-- **Dilation rule for multipoint continuum limits.** Let `f` be eventually positive with
`f (c λ) / f λ → c ^ σ` for every `c > 0`, and suppose that for every tuple `x` of pairwise
distinct points of `ℝ^d` the rescaled connection probability
`f(λ)^k τ_k(⌊λ x_1⌋, …, ⌊λ x_k⌋)` (floors coordinatewise) tends to `T x` as `λ → ∞` through the
reals. Then `T (c • x) = c ^ (-(k σ)) * T x` for every `c > 0` and every such `x`. -/
theorem multipointLimit_smul (q : Sym2 (Fin d → ℤ) → unitInterval) {σ : ℝ} {f : ℝ → ℝ}
    (hpos : ∀ᶠ s in atTop, 0 < f s)
    (hf : ∀ c : ℝ, 0 < c → Tendsto (fun s => f (c * s) / f s) atTop (𝓝 (c ^ σ)))
    (T : (Fin k → Fin d → ℝ) → ℝ)
    (hT : ∀ x : Fin k → Fin d → ℝ, Function.Injective x →
      Tendsto (fun s => f s ^ k * (law q {ω : Config (Fin d → ℤ) |
        ∀ i j, ω ∈ conn (fun l => ⌊s * x i l⌋) (fun l => ⌊s * x j l⌋)}).toReal) atTop (𝓝 (T x)))
    {c : ℝ} (hc : 0 < c) {x : Fin k → Fin d → ℝ} (hx : Function.Injective x) :
    T (c • x) = c ^ (-((k : ℝ) * σ)) * T x := by
  have hcx : Function.Injective (c • x) := fun i j h => hx (smul_right_injective _ hc.ne' h)
  have hlim := tendsto_mul_pow_comp_const_mul hc (hpos.mono fun s hs => hs.ne')
    (Real.rpow_pos_of_pos hc σ).ne' (hf c hc) (hT x hx)
  have hlim' : Tendsto (fun s => f s ^ k * (law q {ω : Config (Fin d → ℤ) |
        ∀ i j, ω ∈ conn (fun l => ⌊s * (c • x) i l⌋) (fun l => ⌊s * (c • x) j l⌋)}).toReal) atTop
      (𝓝 ((c ^ σ)⁻¹ ^ k * T x)) := by
    refine hlim.congr fun s => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm s c]
  rw [tendsto_nhds_unique (hT _ hcx) hlim', ← Real.rpow_neg hc.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hc.le, neg_mul, mul_comm σ]

/-- `multipointLimit_smul` with `f` regularly varying with index `σ`
(`PercLib.Analysis.RegularlyVarying`). -/
theorem multipointLimit_smul_of_regularlyVarying (q : Sym2 (Fin d → ℤ) → unitInterval)
    {σ : ℝ} {f : ℝ → ℝ} (hf : Analysis.RegularlyVarying σ f)
    (T : (Fin k → Fin d → ℝ) → ℝ)
    (hT : ∀ x : Fin k → Fin d → ℝ, Function.Injective x →
      Tendsto (fun s => f s ^ k * (law q {ω : Config (Fin d → ℤ) |
        ∀ i j, ω ∈ conn (fun l => ⌊s * x i l⌋) (fun l => ⌊s * x j l⌋)}).toReal) atTop (𝓝 (T x)))
    {c : ℝ} (hc : 0 < c) {x : Fin k → Fin d → ℝ} (hx : Function.Injective x) :
    T (c • x) = c ^ (-((k : ℝ) * σ)) * T x :=
  multipointLimit_smul q hf.2.1 hf.2.2 T hT hc hx

end Percolation.Bond

end PercLib
