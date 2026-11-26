/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from contributor yujinhkim, repository `yujinhkim/lrp`, branch `critical-lrp-1`,
commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/VolumeMoments/ErrorTerms.lean`. Licence: Apache-2.0 as declared in that
revision's file headers and `third_party/critical-lrp/NOTICE.md`. Upstream origin:
`yujinhkim/Critical-Long-range-percolation`, revision
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified).
Changes: the source definitions `oneSubE0`, `cE1`, `oneSubEbar1`, `cE2` and `oneSubEbar2` are
written out inline in the statements (no new definition); positivity hypotheses that the
algebra uses only through non-vanishing are weakened to `≠ 0`; namespace `PercLib.Analysis`;
focused imports, no disabled linters or `autoImplicit`. The analytic bootstrap of the same
source directory (`VolumeMoments/Bootstrap.lean`) is `PercLib/Analysis/RiccatiBootstrap.lean`.

Mathematical reference: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Section I.4.1, the passages (I.4.5) ⟹ (I.4.6) (p. 35) and
(I.4.14) ⟹ (I.4.15) (p. 43).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The error terms of the first- and second-moment ODEs

The paper defines, with `A = E|K|`, `A₂ = E|K|²`, `b = |B_r|`, `J = |J'(r)|`,
`S = E[|K| ∑_{y ∈ B_r} |K_y|]`, `T = E[|K|² |K ∩ B_r|]` and
`U = E[|K| ∑_{y ∈ B_r} 1(y ∉ K) |K_y|²]`,

* `1 - 𝓔_{0,r} = J b r^{α+1}`,
* `𝓔_{1,r} = (b A² - S + T) / (b A²)` and `1 - Ē_{1,r} = (1 - 𝓔_{1,r})(1 - 𝓔_{0,r})`,
* `𝓔_{2,r} = (b A A₂ - U) / (b A A₂)` and
  `1 - Ē_{2,r} = (1 - 𝓔_{2,r})(1 + 𝓗_r)(1 - 𝓔_{0,r})`, where `A = (α/β) r^α (1 + 𝓗_r)`.

These quantities are written out in the statements below. Nothing probabilistic is asserted:
the expectations are real numbers, and the two theorems say that the definitions turn the
right-hand sides of (I.4.5) and (I.4.14) into those of (I.4.6) and (I.4.15).

## Main results

* `mul_sub_eq_one_sub_errorBar_one_mul_sq`: `β J (S - T) = (1 - Ē_{1,r}) β r^{-α-1} A²`;
* `mul_eq_one_sub_errorBar_two_mul`: `3 β J U = 3 α (1 - Ē_{2,r}) r^{-1} A₂`.
-/

@[expose] public section

namespace PercLib.Analysis

/-- **The passage (I.4.5) ⟹ (I.4.6).** With `𝓔_{1,r} = (b A² - S + T) / (b A²)` and
`1 - 𝓔_{0,r} = J b r^{α+1}`, the right-hand side `β J (S - T)` of (I.4.5) equals
`(1 - 𝓔_{1,r})(1 - 𝓔_{0,r}) β r^{-α-1} A²`. -/
theorem mul_sub_eq_one_sub_errorBar_one_mul_sq {A S T b J β r α : ℝ} (hA : A ≠ 0)
    (hb : b ≠ 0) (hr : 0 < r) :
    β * J * (S - T)
      = (1 - (b * A ^ 2 - S + T) / (b * A ^ 2)) * (J * b * r ^ (α + 1))
          * β * r ^ (-α - 1) * A ^ 2 := by
  have hrpow : r ^ (α + 1) * r ^ (-α - 1) = 1 := by
    rw [← Real.rpow_add hr]
    norm_num
  have hbA : b * A ^ 2 ≠ 0 := mul_ne_zero hb (pow_ne_zero 2 hA)
  have hE : 1 - (b * A ^ 2 - S + T) / (b * A ^ 2) = (S - T) / (b * A ^ 2) := by
    field_simp
    ring
  rw [hE]
  calc β * J * (S - T)
      = (S - T) / (b * A ^ 2) * (b * A ^ 2) * J * β * (r ^ (α + 1) * r ^ (-α - 1)) := by
        rw [hrpow, div_mul_cancel₀ _ hbA]
        ring
    _ = _ := by ring

/-- **The passage (I.4.14) ⟹ (I.4.15).** With `A = (α/β) r^α (1 + H)`,
`𝓔_{2,r} = (b A A₂ - U) / (b A A₂)` and `1 - 𝓔_{0,r} = J b r^{α+1}`, the right-hand side
`3 β J U` of (I.4.14) equals `3 α (1 - 𝓔_{2,r})(1 + H)(1 - 𝓔_{0,r}) r^{-1} A₂`. -/
theorem mul_eq_one_sub_errorBar_two_mul {A A₂ U b J β r α H : ℝ} (hA : A ≠ 0) (hA₂ : A₂ ≠ 0)
    (hb : b ≠ 0) (hr : 0 < r) (hβ : β ≠ 0) (hAr : A = α / β * r ^ α * (1 + H)) :
    3 * β * J * U
      = 3 * α * ((1 - (b * A * A₂ - U) / (b * A * A₂)) * (1 + H) * (J * b * r ^ (α + 1)))
          * r ^ (-1 : ℝ) * A₂ := by
  have hbAA : b * A * A₂ ≠ 0 := mul_ne_zero (mul_ne_zero hb hA) hA₂
  have hE : 1 - (b * A * A₂ - U) / (b * A * A₂) = U / (b * A * A₂) := by
    field_simp
    ring
  have hβA : α * r ^ α * (1 + H) = β * A := by
    rw [hAr]
    field_simp
  have hrpow : r ^ (α + 1) * r ^ (-1 : ℝ) = r ^ α := by
    rw [← Real.rpow_add hr]
    norm_num
  rw [hE]
  calc 3 * β * J * U
      = 3 * (β * A) * (U / (b * A * A₂)) * J * b * A₂ := by
        field_simp
    _ = 3 * (α * r ^ α * (1 + H)) * (U / (b * A * A₂)) * J * b * A₂ := by rw [hβA]
    _ = _ := by
        rw [← hrpow]
        ring

end PercLib.Analysis
