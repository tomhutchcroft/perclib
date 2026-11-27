/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The mass-transport property of a group action. New for this project against pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied. Mathematical reference:
the mass-transport principle and unimodularity, Lyons and Peres, *Probability on Trees and
Networks*, Section 8.2.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.MassTransport

/-!
# The mass-transport property of an action

An action of a group `Γ` on a set `V` has the mass-transport property if every diagonally
invariant function `F : V → V → ℝ≥0∞` (`F (g • x) (g • y) = F x y`) satisfies
`∑' v, F o v = ∑' v, F v o` for every base point `o`. For a transitive action it suffices to
check one base point. Transitivity alone does not imply the property; it is a form of
unimodularity.

## Main definitions

* `PercLib.HasMassTransport Γ V`: the action of `Γ` on `V` has the mass-transport property.

## Main results

* `PercLib.hasMassTransport_iff_of_pretransitive`: for a transitive action, the property at
  one base point is equivalent to the property.
* `PercLib.hasMassTransport_self`: a group acting on itself by left multiplication has the
  mass-transport property.
* `PercLib.hasMassTransport_multiplicative_self`: an additive group acting on itself by
  translation has the mass-transport property.
-/

@[expose] public section

open scoped ENNReal

namespace PercLib

variable (Γ V : Type*) [Group Γ] [MulAction Γ V]

/-- **The mass-transport property of an action.** Every diagonally invariant function
`F : V → V → [0, ∞]`, meaning `F (g • x) (g • y) = F x y`, satisfies
`∑_v F (o, v) = ∑_v F (v, o)` for each `o ∈ V`; the sums may be infinite. For a transitive
action this is the same as asking it at one fixed `o`
(`hasMassTransport_iff_of_pretransitive`). -/
def HasMassTransport : Prop :=
  ∀ F : V → V → ℝ≥0∞, (∀ (g : Γ) (x y : V), F (g • x) (g • y) = F x y) →
    ∀ o : V, ∑' v, F o v = ∑' v, F v o

variable {Γ V}

theorem HasMassTransport.tsum_eq (h : HasMassTransport Γ V) {F : V → V → ℝ≥0∞}
    (hF : ∀ (g : Γ) (x y : V), F (g • x) (g • y) = F x y) (o : V) :
    ∑' v, F o v = ∑' v, F v o :=
  h F hF o

/-- For a diagonally invariant `F`, the outgoing sum `∑_v F (x, v)` is constant on orbits. -/
theorem tsum_smul_left_eq_of_invariant {F : V → V → ℝ≥0∞}
    (hF : ∀ (g : Γ) (x y : V), F (g • x) (g • y) = F x y) (g : Γ) (x : V) :
    ∑' v, F (g • x) v = ∑' v, F x v := by
  rw [← (MulAction.toPerm g : Equiv.Perm V).tsum_eq]
  exact tsum_congr fun v ↦ hF g x v

/-- For a diagonally invariant `F`, the incoming sum `∑_v F (v, x)` is constant on orbits. -/
theorem tsum_smul_right_eq_of_invariant {F : V → V → ℝ≥0∞}
    (hF : ∀ (g : Γ) (x y : V), F (g • x) (g • y) = F x y) (g : Γ) (x : V) :
    ∑' v, F v (g • x) = ∑' v, F v x := by
  rw [← (MulAction.toPerm g : Equiv.Perm V).tsum_eq]
  exact tsum_congr fun v ↦ hF g v x

/-- For a transitive action, the mass-transport property may be checked at one base point. -/
theorem hasMassTransport_iff_of_pretransitive [MulAction.IsPretransitive Γ V] (o : V) :
    HasMassTransport Γ V ↔
      ∀ F : V → V → ℝ≥0∞, (∀ (g : Γ) (x y : V), F (g • x) (g • y) = F x y) →
        ∑' v, F o v = ∑' v, F v o := by
  refine ⟨fun h F hF ↦ h F hF o, fun h F hF x ↦ ?_⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Γ o x
  rw [tsum_smul_left_eq_of_invariant hF, tsum_smul_right_eq_of_invariant hF]
  exact h F hF

/-- A group acting on itself by left multiplication has the mass-transport property. -/
theorem hasMassTransport_self : HasMassTransport Γ Γ := by
  rw [hasMassTransport_iff_of_pretransitive (1 : Γ)]
  exact fun F hF ↦ Probability.tsum_mass_transport F hF

/-- An additive group acting on itself by translation (as `Multiplicative G`) has the
mass-transport property. -/
theorem hasMassTransport_multiplicative_self (G : Type*) [AddGroup G] :
    HasMassTransport (Multiplicative G) G := by
  intro F hF o
  have h : ∀ v, F o v = F (o + -v + o) o := fun v ↦ by
    have := hF (Multiplicative.ofAdd (o + -v)) o v
    simp only [ofAdd_smul, vadd_eq_add, neg_add_cancel_right] at this
    exact this.symm
  simp_rw [h]
  exact ((Equiv.neg G).trans ((Equiv.addLeft o).trans (Equiv.addRight o))).tsum_eq
    (fun w ↦ F w o)


end PercLib
