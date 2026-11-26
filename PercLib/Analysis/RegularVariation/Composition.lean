/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Composition of regularly varying functions, following Bingham–Goldie–Teugels, *Regular
Variation*, Proposition 1.5.7(iii), and its use for the change from cutoff radius to spatial
radius in T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1. New proofs;
nothing is copied.
-/
module

public import PercLib.Analysis.RegularVariation.UniformConvergence
public import PercLib.Analysis.RegularVariation.LevelInverse

/-! # Composition of regularly varying functions

If `f` is regularly varying with index `ρ` and `g` is regularly varying with index `σ > 0`,
then `f ∘ g` is regularly varying with index `ρ * σ` (BGT Proposition 1.5.7(iii)). The proof
uses `g → ∞`, the limit `g (c x) / g x → c ^ σ`, and the uniform convergence theorem for `f`
on a compact multiplier interval around `c ^ σ`. Measurability on a tail, which
`RegularlyVarying` includes, suffices: no global measurability of `f` is assumed.

The second part applies this to a change of normalization: with `χ`, `m` regularly varying of
indices `α`, `2α` and `q` regularly varying of index `1/γ`, `γ = max 1 (α/2)`, the functions
`R ↦ 4 χ (q R) / m (q R)` and `R ↦ m (q R) / 4` are regularly varying of indices `-β`, `2β`,
where `β = α / γ = min α 2`.

## Main results

* `RegularlyVarying.comp`: `f ∘ g` is regularly varying with index `ρ * σ`.
* `RegularlyVarying.const_mul_comp_div_comp`, `RegularlyVarying.comp_div_const`: the general
  indices of `c * χ (q R) / m (q R)` and `m (q R) / c`.
* `div_max_one_div_two_eq_min`, `div_max_one_div_two_eq_two_of_two_lt`: the index arithmetic
  `α / max 1 (α/2) = min α 2`.
* `regularlyVarying_four_mul_comp_div_comp`, `regularlyVarying_comp_div_four`,
  `four_mul_comp_div_comp_mul_comp_div_four`, `eq_two_of_two_lt_of_eq_div_max`: the
  spatial-normalization forms.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PercLib.Analysis

/-! ### Composition -/

/-- **Composition of regularly varying functions** (BGT Proposition 1.5.7(iii)): if `f` is
regularly varying with index `ρ` and `g` is regularly varying with index `σ > 0`, then `f ∘ g`
is regularly varying with index `ρ * σ`. -/
theorem RegularlyVarying.comp {ρ σ : ℝ} {f g : ℝ → ℝ} (hf : RegularlyVarying ρ f)
    (hg : RegularlyVarying σ g) (hσ : 0 < σ) : RegularlyVarying (ρ * σ) (f ∘ g) := by
  obtain ⟨a, F, hF, hFf, hFrv⟩ := hf.exists_measurable_eqOn
  have hgt : Tendsto g atTop atTop := hg.tendsto_atTop' hσ
  have hev : F ∘ g =ᶠ[atTop] f ∘ g :=
    (hgt.eventually (eventually_ge_atTop a)).mono fun x hx => hFf _ hx
  refine RegularlyVarying.congr' ?_ hev
  obtain ⟨b, hb⟩ := hg.measurable_tail
  refine ⟨⟨b, hF.comp hb⟩, hgt.eventually hFrv.eventually_pos, fun c hc => ?_⟩
  set L : ℝ := c ^ σ with hLdef
  have hL : 0 < L := Real.rpow_pos_of_pos hc σ
  have hcx : Tendsto (fun x => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have hlam : Tendsto (fun x => g (c * x) / g x) atTop (𝓝 L) := hg.tendsto hc
  -- the error term `F (g (c x)) / F (g x) - (g (c x) / g x) ^ ρ` tends to `0`
  have hD : Tendsto (fun x => F (g (c * x)) / F (g x) - (g (c * x) / g x) ^ ρ) atTop
      (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Y, -, hY⟩ := tendsto_uniformly_abs_ratio_of_regularlyVarying hF hFrv
      (half_pos hL) (by linarith : L / 2 ≤ 2 * L) (half_pos hε)
    have hIcc : Icc (L / 2) (2 * L) ∈ 𝓝 L := Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [hgt.eventually (eventually_ge_atTop Y),
      hgt.eventually (eventually_gt_atTop 0), hgt.eventually hFrv.eventually_pos,
      (hgt.comp hcx).eventually hFrv.eventually_pos, hlam hIcc] with x hxY hx0 hFx hFcx hxl
    have hgc : g (c * x) / g x * g x = g (c * x) := div_mul_cancel₀ _ hx0.ne'
    have h := hY (g x) hxY _ hxl
    rw [hgc, abs_of_pos hFx, abs_of_pos (show 0 < F (g (c * x)) from hFcx)] at h
    rw [Real.dist_eq, sub_zero]
    exact h.trans_lt (half_lt_self hε)
  have hpow : Tendsto (fun x => (g (c * x) / g x) ^ ρ) atTop (𝓝 (L ^ ρ)) :=
    hlam.rpow_const (Or.inl hL.ne')
  have hsum := hD.add hpow
  rw [zero_add, hLdef, ← Real.rpow_mul hc.le, mul_comm σ ρ] at hsum
  refine hsum.congr' (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, sub_add_cancel]

/-! ### Quotients and multiples of compositions -/

/-- With `χ`, `m`, `q` regularly varying of indices `a`, `b`, `s > 0`, the function
`R ↦ c * χ (q R) / m (q R)` (`c > 0`) is regularly varying with index `(a - b) * s`. -/
theorem RegularlyVarying.const_mul_comp_div_comp {a b s c : ℝ} {χ m q : ℝ → ℝ}
    (hχ : RegularlyVarying a χ) (hm : RegularlyVarying b m) (hq : RegularlyVarying s q)
    (hs : 0 < s) (hc : 0 < c) :
    RegularlyVarying ((a - b) * s) (fun R => c * χ (q R) / m (q R)) := by
  have h := (((hχ.comp hq hs).mul (hm.comp hq hs).inv)).const_mul hc
  rw [show a * s + -(b * s) = (a - b) * s by ring] at h
  refine h.congr' (Eventually.of_forall fun R => ?_)
  simp only [Function.comp_apply, div_eq_mul_inv, mul_assoc]

/-- With `m`, `q` regularly varying of indices `b`, `s > 0`, the function `R ↦ m (q R) / c`
(`c > 0`) is regularly varying with index `b * s`. -/
theorem RegularlyVarying.comp_div_const {b s c : ℝ} {m q : ℝ → ℝ}
    (hm : RegularlyVarying b m) (hq : RegularlyVarying s q) (hs : 0 < s) (hc : 0 < c) :
    RegularlyVarying (b * s) (fun R => m (q R) / c) :=
  ((hm.comp hq hs).const_mul (inv_pos.2 hc)).congr'
    (Eventually.of_forall fun R => by simp only [Function.comp_apply, div_eq_inv_mul])

/-! ### Index arithmetic -/

/-- `α / max 1 (α / 2) = min α 2` (for `α ≤ 2` the maximum is `1`). -/
theorem div_max_one_div_two_eq_min (α : ℝ) : α / max 1 (α / 2) = min α 2 := by
  rcases le_total α 2 with h | h
  · rw [max_eq_left (by linarith), min_eq_left h, div_one]
  · rw [max_eq_right (by linarith), min_eq_right h]
    field_simp

/-- For `α > 2`, `α / max 1 (α / 2) = 2`. -/
theorem div_max_one_div_two_eq_two_of_two_lt {α : ℝ} (hα : 2 < α) :
    α / max 1 (α / 2) = 2 := by
  rw [div_max_one_div_two_eq_min α, min_eq_right hα.le]

/-! ### Spatial normalization -/

/-- If `χ`, `m`, `q` are regularly varying of indices `α`, `2α`, `1/γ` with
`γ = max 1 (α / 2)` and `β = α / γ`, then `R ↦ 4 χ (q R) / m (q R)` is regularly
varying with index `-β`. -/
theorem regularlyVarying_four_mul_comp_div_comp {α γ β : ℝ} {χ m q : ℝ → ℝ}
    (hγ : γ = max 1 (α / 2)) (hβ : β = α / γ) (hχ : RegularlyVarying α χ)
    (hm : RegularlyVarying (2 * α) m) (hq : RegularlyVarying (1 / γ) q) :
    RegularlyVarying (-β) (fun R => 4 * χ (q R) / m (q R)) := by
  have hγ0 : 0 < γ := hγ ▸ lt_max_of_lt_left one_pos
  have h := hχ.const_mul_comp_div_comp hm hq (one_div_pos.2 hγ0) four_pos
  rwa [show (α - 2 * α) * (1 / γ) = -β by rw [hβ]; ring] at h

/-- If `m`, `q` are regularly varying of indices `2α`, `1/γ` with `γ = max 1 (α / 2)` and
`β = α / γ`, then `R ↦ m (q R) / 4` is regularly varying with index `2β`. -/
theorem regularlyVarying_comp_div_four {α γ β : ℝ} {m q : ℝ → ℝ}
    (hγ : γ = max 1 (α / 2)) (hβ : β = α / γ) (hm : RegularlyVarying (2 * α) m)
    (hq : RegularlyVarying (1 / γ) q) :
    RegularlyVarying (2 * β) (fun R => m (q R) / 4) := by
  have hγ0 : 0 < γ := hγ ▸ lt_max_of_lt_left one_pos
  have h := hm.comp_div_const hq (one_div_pos.2 hγ0) four_pos
  rwa [show 2 * α * (1 / γ) = 2 * β by rw [hβ]; ring] at h

/-- The product identity `(4 χ (q R) / m (q R)) * (m (q R) / 4) = χ (q R)` when `m` does not
vanish. -/
theorem four_mul_comp_div_comp_mul_comp_div_four {χ m q : ℝ → ℝ} (hm : ∀ r, m r ≠ 0) (R : ℝ) :
    4 * χ (q R) / m (q R) * (m (q R) / 4) = χ (q R) := by
  have := hm (q R)
  field_simp

/-- If `β = α / γ` with `γ = max 1 (α / 2)` and `α > 2`, then `β = 2`. -/
theorem eq_two_of_two_lt_of_eq_div_max {α γ β : ℝ} (hγ : γ = max 1 (α / 2))
    (hβ : β = α / γ) (hα : 2 < α) : β = 2 := by
  rw [hβ, hγ, div_max_one_div_two_eq_two_of_two_lt hα]

end PercLib.Analysis
