/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface and the intensity family `intensityProfile`. No source
text or code is copied. Mathematical reference: the nearest-neighbour model on `ℤ`; the
mass-transport principle as in Lyons and Peres, *Probability on Trees and Networks*,
Section 8.2.
-/
module

public import PercLib.Models.NormalizedSmallIntensityLine
public import PercLib.Probability.MassTransport.Defs

/-!
# Symmetry and finiteness of the nearest-neighbour model on `ℤ`

On `ℤ` let `J = 1/2` on nearest-neighbour pairs and `0` elsewhere (the hypothesis `hJ`).
The weights are invariant under the translation action of `Multiplicative ℤ`, which is
transitive and has the mass-transport property; the support graph `{e | 0 < J e}` is
connected; and the susceptibility of `intensityProfile J β` is finite at every intensity.

## Main results

* `line_map_smul_eq`: `J` is invariant under translations.
* `line_connected`: the graph of pairs of positive weight is connected.
* `line_chi_lt_top`: `χ < ∞` at every intensity `β`.
-/

@[expose] public section
noncomputable section

open PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.NormalizedSmallIntensity

variable (J : Sym2 ℤ → ℝ≥0) (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0)
include hJ

/-- The nearest-neighbour weights are invariant under every translation of `ℤ`. -/
theorem line_map_smul_eq (g : Multiplicative ℤ) (e : Sym2 ℤ) :
    J (Sym2.map (g • ·) e) = J e := by
  have hg : ∀ x : ℤ, g • x = g.toAdd + x := fun _ ↦ rfl
  induction e using Sym2.ind with
  | _ a b => simp only [Sym2.map_mk, hg, hJ, add_sub_add_left_eq_sub]

/-- The graph of pairs of positive nearest-neighbour weight is connected. -/
theorem line_connected : (SimpleGraph.fromEdgeSet {e | 0 < J e}).Connected := by
  have hadj : ∀ n : ℤ, (SimpleGraph.fromEdgeSet {e | 0 < J e}).Adj n (n + 1) := fun n ↦ by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by simp [hJ], by omega⟩
  have hr : ∀ n : ℤ, (SimpleGraph.fromEdgeSet {e | 0 < J e}).Reachable 0 n := by
    intro n
    induction n using Int.induction_on with
    | zero => rfl
    | succ k ih => exact ih.trans (hadj k).reachable
    | pred k ih =>
      have h := (hadj (-(k : ℤ) - 1)).symm.reachable
      rw [sub_add_cancel] at h
      exact ih.trans h
  rw [SimpleGraph.connected_iff]
  exact ⟨fun a b ↦ (hr a).symm.trans (hr b), ⟨0⟩⟩

/-- The susceptibility of the nearest-neighbour model is finite at every intensity. -/
theorem line_chi_lt_top (β : ℝ≥0) (a : ℤ) : chi (intensityProfile J β) a < ⊤ := by
  rw [line_chi_eq J hJ]
  exact ENNReal.ofReal_lt_top

end PercLib.Models.NormalizedSmallIntensity
