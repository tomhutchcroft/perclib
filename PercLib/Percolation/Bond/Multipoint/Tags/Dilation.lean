/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the dilation rule of multipoint continuum limits under a regularly
varying normalisation (wiki article `multipoint-trees`). All mathematical inputs are proved in
the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Multipoint.Dilation

/-!
# Regularly varying normalisation fixes the dilation exponent: correspondence

Wiki correspondence for the dilation rule `T_k(c x) = c^{-kσ} T_k(x)`; it restates
`PercLib.Percolation.Bond.multipointLimit_smul`.

## Main results

* `multipointLimit_smul_of_ratio_tendsto`
-/

@[expose] public section
noncomputable section
open Filter Topology

namespace PercLib.Percolation.Bond

/-- For a bond law `q` on `ℤ^d` and an integer `k ≥ 2`, let `f` be eventually positive with
`f (c λ) / f λ → c ^ σ` for every `c > 0`. If for every tuple `x` of pairwise distinct points of
`ℝ^d` the limit `T x = lim_{λ → ∞} f(λ)^k τ_k(⌊λ x_1⌋, …, ⌊λ x_k⌋)` exists (`λ` real, floors
coordinatewise, `τ_k` the probability that the marked vertices lie in one cluster), then
`T (c x) = c^{-kσ} T x` for every `c > 0`. -/
@[tag "5PBL"]
theorem multipointLimit_smul_of_ratio_tendsto (d k : ℕ) (_hk : 2 ≤ k)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (σ : ℝ) (f : ℝ → ℝ)
    (hpos : ∀ᶠ s in atTop, 0 < f s)
    (hf : ∀ c : ℝ, 0 < c → Tendsto (fun s => f (c * s) / f s) atTop (𝓝 (c ^ σ)))
    (T : (Fin k → Fin d → ℝ) → ℝ)
    (hT : ∀ x : Fin k → Fin d → ℝ, Function.Injective x →
      Tendsto (fun s => f s ^ k * (law q {ω : Config (Fin d → ℤ) |
        ∀ i j, ω ∈ conn (fun l => ⌊s * x i l⌋) (fun l => ⌊s * x j l⌋)}).toReal) atTop (𝓝 (T x)))
    (c : ℝ) (hc : 0 < c) (x : Fin k → Fin d → ℝ) (hx : Function.Injective x) :
    T (c • x) = c ^ (-((k : ℝ) * σ)) * T x :=
  multipointLimit_smul q hpos hf T hT hc hx

end PercLib.Percolation.Bond
