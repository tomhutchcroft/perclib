/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the Erdős–Rényi critical-window parametrisation.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.ErdosRenyi.Defs

/-!
# Erdős–Rényi critical-window scale: correspondence

## Main results

* `erdosRenyiWindow_def_and_tendsto`
-/

@[expose] public section

open Filter Topology

namespace PercLib.Models

/-- The Erdős–Rényi critical window: `p = 1/n + λ n^{-4/3}` with `λ ∈ ℝ` fixed as `n → ∞`. For
each `λ` this is a probability for all large `n`, `n p → 1`, and `λ` is recovered as
`(p - 1/n) n^{4/3}`. -/
@[tag "X9N1"]
theorem erdosRenyiWindow_def_and_tendsto :
    (∀ (n : ℕ) (t : ℝ), erdosRenyiWindow n t = 1 / n + t * (n : ℝ) ^ (-(4 / 3 : ℝ))) ∧
    (∀ t : ℝ, ∀ᶠ n : ℕ in atTop, erdosRenyiWindow n t ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t : ℝ, Tendsto (fun n : ℕ => (n : ℝ) * erdosRenyiWindow n t) atTop (𝓝 1)) ∧
    (∀ (n : ℕ) (t : ℝ), n ≠ 0 →
      (erdosRenyiWindow n t - 1 / n) * (n : ℝ) ^ (4 / 3 : ℝ) = t) :=
  ⟨erdosRenyiWindow_def, eventually_erdosRenyiWindow_mem_Icc,
    tendsto_natCast_mul_erdosRenyiWindow,
    fun _ t hn => erdosRenyiWindow_sub_inv_mul_rpow hn t⟩

end PercLib.Models
