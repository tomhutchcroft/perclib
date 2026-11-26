/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the mass-transport property of a group action, from
`MassTransport/Defs.lean`. No new definitions. Mathematical reference: Lyons and Peres,
*Probability on Trees and Networks*, Section 8.2.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.MassTransport.Defs

/-!
# The mass-transport property: correspondence

Wiki correspondence for the definition `PercLib.HasMassTransport`, from
`PercLib/Probability/MassTransport/Defs.lean`.

## Main results

* `PercLib.hasMassTransport_iff`
-/

@[expose] public section

open scoped ENNReal

namespace PercLib

variable (Γ V : Type*) [Group Γ] [MulAction Γ V]

/-- **N0HM.** An action of `Γ` on `V` has the mass-transport property exactly when every
diagonally invariant `F : V → V → [0, ∞]` satisfies `∑_v F (o, v) = ∑_v F (v, o)` for each
`o ∈ V`. -/
@[tag "N0HM"]
theorem hasMassTransport_iff : HasMassTransport Γ V ↔
  ∀ F : V → V → ℝ≥0∞, (∀ (g : Γ) (x y : V), F (g • x) (g • y) = F x y) →
    ∀ o : V, ∑' v, F o v = ∑' v, F v o :=
  Iff.rfl

end PercLib
