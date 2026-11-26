/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's definitions of the hierarchical lattice, its distance and
its balls. No upstream code is copied and no definition is added. Mathematical reference:
T. Hutchcroft, *The critical two-point function for long-range percolation on the hierarchical
lattice*, arXiv:2103.17013v1, Section 1.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.Hierarchical.Basic

/-!
# The hierarchical lattice (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `HierarchicalLattice.exists_addEquiv_directSum`: the lattice is the direct sum of copies of
  `(ℤ/Lℤ)^d`.
* `HierarchicalLattice.hierDist_spec_and_card_ball`: the distance and the ball volume.
* `HierarchicalLattice.commonBall_spec_and_regDist_eq`: the smallest common ball, the
  regularized distance and radial kernels.
-/

@[expose] public section
noncomputable section

open DirectSum

namespace PercLib.Models.HierarchicalLattice

universe u

variable {d L : ℕ}

/-- **Hierarchical lattice.** The vertex group `HierarchicalLattice d L = ℕ →₀ (Fin d → ZMod L)`
is `ℍ_L^d = ⨁_{i ≥ 1} (ℤ/Lℤ)^d`: it is additively isomorphic to the direct sum of copies of
`(ℤ/Lℤ)^d` by an isomorphism preserving every coordinate (index `i` here is coordinate `i + 1`
of the source). -/
@[tag "XMYD"]
theorem exists_addEquiv_directSum :
    ∃ e : HierarchicalLattice d L ≃+ ⨁ _ : ℕ, (Fin d → ZMod L), ∀ x i, e x i = x i :=
  ⟨toDirectSum, toDirectSum_apply⟩

/-- **Hierarchical distance and ball volume.** Let `L ≥ 2`. Vertices are finitely supported
sequences; the distance `hierDist x x` of a vertex to itself is `0`, and for `x ≠ y` the
distance is `L ^ (i + 1)`, where `i` is the largest index with `x i ≠ y i` (coordinate `i + 1`
of the source, so this is `L ^ max {i : x_i ≠ y_i}` in the source's indexing). A ball of radius
`L ^ n` contains `L ^ (d n)` vertices. -/
@[tag "T6SL"]
theorem hierDist_spec_and_card_ball (hL : 2 ≤ L) :
    (∀ x : HierarchicalLattice d L, hierDist x x = 0) ∧
      (∀ x y : HierarchicalLattice d L, x ≠ y →
        ∃ i, x i ≠ y i ∧ (∀ j, x j ≠ y j → j ≤ i) ∧ hierDist x y = L ^ (i + 1)) ∧
      ∀ (x : HierarchicalLattice d L) (n : ℕ),
        Nat.card {z : HierarchicalLattice d L | hierDist z x ≤ L ^ n} = L ^ (d * n) := by
  exact ⟨hierDist_self, fun x y h => exists_hierDist_eq_pow_of_ne h,
    card_setOf_hierDist_le hL⟩

/-- **Smallest common hierarchical ball and regularized distance.** Let `L ≥ 2`. For vertices
`x, y`, `Λ(x, y) = commonBall x y` is the hierarchical ball about `x` of radius
`L ^ level (y - x)`; it contains `x` and `y` and is contained in every ball `ball z n` (radius
`L ^ n` about `z`) containing both. The regularized distance is
`⟨x - y⟩ = regDist x y = max 1 ‖x - y‖`, which equals `L ^ level (x - y)`. A kernel `J` is radial
(`IsRadial J`) when it depends only on the distance; equivalently, on the level of the
displacement. -/
@[tag "JCRB"]
theorem commonBall_spec_and_regDist_eq (hL : 2 ≤ L) :
    (∀ x y : HierarchicalLattice d L,
      commonBall x y = ball x (level (y - x)) ∧ x ∈ commonBall x y ∧ y ∈ commonBall x y ∧
        ∀ (z : HierarchicalLattice d L) (n : ℕ), x ∈ ball z n → y ∈ ball z n →
          commonBall x y ⊆ ball z n) ∧
      (∀ x y : HierarchicalLattice d L,
        regDist x y = max 1 (hierDist x y) ∧ regDist x y = L ^ level (x - y)) ∧
      ∀ {β : Type u} (J : Sym2 (HierarchicalLattice d L) → β),
        (IsRadial J ↔ ∃ f : ℕ → β, ∀ x y, J s(x, y) = f (hierDist x y)) ∧
          (IsRadial J ↔ ∃ f : ℕ → β, ∀ x y, J s(x, y) = f (level (y - x))) := by
  have : NeZero L := ⟨by omega⟩
  exact ⟨fun x y => ⟨commonBall_def x y, left_mem_commonBall x y, right_mem_commonBall x y,
      fun _ _ hx hy => commonBall_subset_of_mem hx hy⟩,
    fun x y => ⟨regDist_def x y, regDist_eq_pow x y⟩,
    fun J => ⟨Iff.rfl, isRadial_iff_level hL J⟩⟩

end PercLib.Models.HierarchicalLattice
