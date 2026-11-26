/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.Coupling.Monotone

/-!
# Monotone product coupling: correspondence

Wiki correspondence for the coupling of all product laws by thresholding one family of
independent uniform variables.

## Main results

* `bond_uniform_threshold_coupling`
-/

@[expose] public section

open MeasureTheory

namespace PercLib.Probability

/-- Independent uniforms `U e` on the bonds give `ω_q = {e | U e ≤ q e}` with law the product
measure of `q` for every profile `q`, and for every outcome `U` the configuration `ω_q` increases
with `q`, simultaneously for all profiles. -/
@[tag "2ML7"] theorem bond_uniform_threshold_coupling {V : Type*} :
    (∀ q : Sym2 V → unitInterval,
      (Measure.infinitePi fun _ : Sym2 V => (volume : Measure unitInterval)).map
        (fun U => {e | U e ≤ q e}) = prodBernoulli q) ∧
    ∀ U : Sym2 V → unitInterval, Monotone fun q : Sym2 V → unitInterval => {e | U e ≤ q e} :=
  ⟨infinitePi_volume_map_setOf_le_eq_prodBernoulli, monotone_setOf_le_apply⟩

end PercLib.Probability
