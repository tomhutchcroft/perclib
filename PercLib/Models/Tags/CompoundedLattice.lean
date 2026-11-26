/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the normalisation of a polynomially compounded lattice law (wiki
article `branching-random-walk`). All mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.CompoundedLattice

/-!
# Normalisation of a polynomially compounded lattice law: correspondence

Restates `compoundedLattice_mass_eq_top_of_pos`, `tsum_ofReal_ite_div_eq_one` and
`compoundedLattice_mass_eq_one`.

## Main results

* `compoundedLattice_normalization`
-/

@[expose] public section
noncomputable section
open scoped ENNReal

namespace PercLib

/-- Let `w : ℤ^d → [0, ∞)` be summable with `H = ∑_{x ≠ 0} w(x) > 0`, `α > 0`, and
`T(t) = t^{-1-α/2} / ζ(1+α/2)` for `t ≥ 1`, with `ζ(s) = ∑_{n ≥ 1} n^{-s}`. If `w(0) > 0`, then
`∑_{t ≥ 1} T(t) U^{*t}` with `U = w / H` has infinite total mass. The functions
`U^*(x) = 1_{x ≠ 0} w(x) / H` and `D^* = ∑_{t ≥ 1} T(t) (U^*)^{*t}` have total mass one.
Convolution powers are `Nat.rec` from the indicator of `0`; masses are extended reals. -/
@[tag "DTYB"]
theorem compoundedLattice_normalization (d : ℕ) (w : (Fin d → ℤ) → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : Summable w) (hH : 0 < ∑' x, if x = 0 then 0 else w x) (α : ℝ) (hα : 0 < α) :
    (0 < w 0 →
      ∑' x, ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) + 1) ^ (-(1 + α / 2)) /
          ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + α / 2))) *
        (Nat.rec (fun z => if z = 0 then 1 else 0)
          (fun _ ν z => ∑' y, ν y * ENNReal.ofReal (w (z - y) /
            ∑' x, if x = 0 then 0 else w x)) (t + 1) :
          (Fin d → ℤ) → ℝ≥0∞) x = ∞) ∧
    ∑' x, ENNReal.ofReal ((if x = 0 then 0 else w x) / ∑' x, if x = 0 then 0 else w x) = 1 ∧
    ∑' x, ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) + 1) ^ (-(1 + α / 2)) /
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + α / 2))) *
      (Nat.rec (fun z => if z = 0 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * ENNReal.ofReal ((if z - y = 0 then 0 else w (z - y)) /
          ∑' x, if x = 0 then 0 else w x)) (t + 1) :
        (Fin d → ℤ) → ℝ≥0∞) x = 1 :=
  ⟨fun h0 => compoundedLattice_mass_eq_top_of_pos w hw0 hw hH h0 hα,
    tsum_ofReal_ite_div_eq_one w hw0 hw hH, compoundedLattice_mass_eq_one w hw0 hw hH hα⟩

end PercLib
