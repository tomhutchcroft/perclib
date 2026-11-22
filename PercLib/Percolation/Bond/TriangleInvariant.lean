/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference: the
second triangle-diagram comparison `B ≤ A` for an invariant connection kernel, through the
positivity of `T ⊙ T³ - T² ⊙ T²` and the invariant trace given by mass transport.
-/
module

public import PercLib.Analysis.HadamardQuadForm
public import PercLib.Percolation.Bond.TriangleComparison
public import PercLib.Probability.MassTransport.Defs

/-!
# The second triangle-diagram comparison for an invariant connection kernel

Let `T(x,y)` be the connection probability of a probability law on configurations, with
`T²(x,y) = ∑_u T(x,u) T(u,y)` and `T³(x,y) = ∑_{u,w} T(x,u) T(u,w) T(w,y)` as sums in `[0, ∞]`.
Suppose a group `Γ` acts on the vertices, the action has the mass-transport property, and
`T(g x, g y) = T(x, y)`. Then

`B = ∑_v T²(o,v)³ ≤ A = ∑_v T(o,v) T²(o,v) T³(o,v)`,

and if the action is moreover transitive, `A ≤ Δ²` with `Δ = T³(o,o)`.

The proof applies the quadratic-form comparison for `T ⊙ T³ - T² ⊙ T²`
(`PercLib.Analysis.tsum_quadForm_hadamard_sq_le_of_posSemidef`) to the vector `T(o, ·)`, and
identifies both sides by the trace identity `∑_{x,y} T(o,x) P(x,y) T(y,o) = ∑_y P(o,y) T²(y,o)`
for invariant `P`, a consequence of mass transport. All sums are in `[0, ∞]`, so no
summability hypothesis (such as finite susceptibility) is needed. A group acting on itself by
left multiplication is the special case of the regular action.

## Main results

* `PercLib.tsum_tsum_mul_mul_eq_of_hasMassTransport`: the invariant trace identity.
* `tsum_connProb_sq_entry_pow_three_le_triangle_weighted`: `B ≤ A` under mass transport.
* `triangle_weighted_le_sq_of_isPretransitive`: `A ≤ Δ²` for a transitive invariant action.
* `tsum_connProb_sq_entry_pow_three_le_triangle_weighted_of_group`,
  `triangle_weighted_le_sq_of_group`: `B ≤ A` and `A ≤ Δ²` for a countable group with a
  left-invariant connection kernel.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib

variable {Γ V : Type*} [Group Γ] [MulAction Γ V]

/-- Reindexing a sum over the middle vertex by `g`: for diagonally invariant kernels `K` and
`L`, `∑_u K(g x, u) L(u, g y) = ∑_u K(x, u) L(u, y)`. -/
theorem tsum_mul_smul_eq_of_invariant {K L : V → V → ℝ≥0∞}
    (hK : ∀ (g : Γ) (x y : V), K (g • x) (g • y) = K x y)
    (hL : ∀ (g : Γ) (x y : V), L (g • x) (g • y) = L x y) (g : Γ) (x y : V) :
    ∑' u, K (g • x) u * L u (g • y) = ∑' u, K x u * L u y := by
  rw [← (MulAction.toPerm g : Equiv.Perm V).tsum_eq]
  simp only [MulAction.toPerm_apply, hK, hL]

/-- **Invariant trace identity.** If the action has the mass-transport property and `T`, `P`
are diagonally invariant, then
`∑_{x,y} T(o,x) P(x,y) T(y,o) = ∑_y P(o,y) ∑_x T(y,x) T(x,o)`. -/
theorem tsum_tsum_mul_mul_eq_of_hasMassTransport (hMT : HasMassTransport Γ V)
    {T P : V → V → ℝ≥0∞} (hT : ∀ (g : Γ) (x y : V), T (g • x) (g • y) = T x y)
    (hP : ∀ (g : Γ) (x y : V), P (g • x) (g • y) = P x y) (o : V) :
    ∑' x, ∑' y, T o x * P x y * T y o = ∑' y, P o y * ∑' x, T y x * T x o := by
  set F : V → V → ℝ≥0∞ := fun a x => ∑' y, T a x * P x y * T y a with hF
  have hFinv : ∀ (g : Γ) (a x : V), F (g • a) (g • x) = F a x := by
    intro g a x
    simp only [hF]
    rw [← (MulAction.toPerm g : Equiv.Perm V).tsum_eq]
    simp only [MulAction.toPerm_apply, hT, hP]
  have h := hMT.tsum_eq hFinv o
  simp only [hF] at h
  rw [h, ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

end PercLib

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- `T²` is symmetric. -/
theorem connProb_sq_entry_comm (μ : Measure (Config V)) (x y : V) :
    ∑' u, connProb μ x u * connProb μ u y = ∑' u, connProb μ y u * connProb μ u x :=
  tsum_congr fun u => by rw [connProb_comm μ x u, connProb_comm μ u y, mul_comm]

section MassTransport

variable {Γ : Type*} [Group Γ] [MulAction Γ V]

/-- **Second triangle-diagram comparison under mass transport.** If the action of `Γ` on `V`
has the mass-transport property and the connection kernel is invariant, then
`∑_v T²(o,v)³ ≤ ∑_v T(o,v) T²(o,v) T³(o,v)`. -/
theorem tsum_connProb_sq_entry_pow_three_le_triangle_weighted [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] (hMT : HasMassTransport Γ V)
    (hinv : ∀ (g : Γ) (x y : V), connProb μ (g • x) (g • y) = connProb μ x y) (o : V) :
    ∑' v, (∑' u, connProb μ o u * connProb μ u v) ^ 3 ≤
      ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
        (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) := by
  set T := connProb μ with hTdef
  have h2inv : ∀ (g : Γ) (x y : V),
      ∑' u, T (g • x) u * T u (g • y) = ∑' u, T x u * T u y :=
    tsum_mul_smul_eq_of_invariant hinv hinv
  have h3inv : ∀ (g : Γ) (x y : V),
      ∑' u, ∑' w, T (g • x) u * T u w * T w (g • y) = ∑' u, ∑' w, T x u * T u w * T w y := by
    intro g x y
    rw [← (MulAction.toPerm g : Equiv.Perm V).tsum_eq]
    refine tsum_congr fun u => ?_
    rw [← (MulAction.toPerm g : Equiv.Perm V).tsum_eq]
    simp only [MulAction.toPerm_apply, hinv]
  have hquad := Analysis.tsum_quadForm_hadamard_sq_le_of_posSemidef T
    (fun x y => connProb_ne_top μ x y) (fun F => posSemidef_connProb μ (fun u : F => (u : V)))
    (T o) (fun x => connProb_ne_top μ o x)
  have hsymm : ∀ P : V → V → ℝ≥0∞, ∑' x, ∑' y, T o x * P x y * T o y =
      ∑' x, ∑' y, T o x * P x y * T y o := fun P =>
    tsum_congr fun x => tsum_congr fun y => by rw [hTdef, connProb_comm μ o y]
  rw [hsymm (fun x y => (∑' u, T x u * T u y) ^ 2),
    hsymm (fun x y => T x y * ∑' u, ∑' w, T x u * T u w * T w y)] at hquad
  simp only [hTdef] at hquad
  have hB := PercLib.tsum_tsum_mul_mul_eq_of_hasMassTransport hMT hinv
    (P := fun x y => (∑' u, T x u * T u y) ^ 2) (fun g x y => by simp only [h2inv]) o
  have hA := PercLib.tsum_tsum_mul_mul_eq_of_hasMassTransport hMT hinv
    (P := fun x y => T x y * ∑' u, ∑' w, T x u * T u w * T w y)
    (fun g x y => by simp only [hinv, h3inv]) o
  simp only [hTdef] at hA hB
  rw [hA, hB] at hquad
  simp only [hTdef]
  convert hquad using 1
  · refine tsum_congr fun v => ?_
    rw [connProb_sq_entry_comm μ v o]
    ring
  · refine tsum_congr fun v => ?_
    rw [connProb_sq_entry_comm μ v o]
    ring

/-- A transitive action preserving the connection kernel supplies, for all `x` and `y`, a
kernel-preserving bijection sending `x` to `y`. -/
theorem exists_equiv_connProb_eq_of_isPretransitive [MulAction.IsPretransitive Γ V]
    (μ : Measure (Config V))
    (hinv : ∀ (g : Γ) (x y : V), connProb μ (g • x) (g • y) = connProb μ x y) (x y : V) :
    ∃ σ : V ≃ V, σ x = y ∧ ∀ a b, connProb μ (σ a) (σ b) = connProb μ a b := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Γ x y
  exact ⟨MulAction.toPerm g, rfl, fun a b => hinv g a b⟩

/-- **First comparison for a transitive action.** If the connection kernel is invariant under a
transitive action, `∑_v T(o,v) T²(o,v) T³(o,v) ≤ T³(o,o)²`. -/
theorem triangle_weighted_le_sq_of_isPretransitive [Countable V]
    [MulAction.IsPretransitive Γ V] (μ : Measure (Config V)) [IsFiniteMeasure μ]
    (hinv : ∀ (g : Γ) (x y : V), connProb μ (g • x) (g • y) = connProb μ x y) (o : V) :
    ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
        (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
      (∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o) ^ 2 :=
  triangle_weighted_le_sq_of_transitive μ
    (exists_equiv_connProb_eq_of_isPretransitive μ hinv) o

end MassTransport

/-- **Second triangle-diagram comparison on a countable group.** For a connection kernel on a
countable group invariant under left multiplication, `∑_v T²(o,v)³ ≤ ∑_v T(o,v) T²(o,v) T³(o,v)`
for every `o`. -/
theorem tsum_connProb_sq_entry_pow_three_le_triangle_weighted_of_group {G : Type*}
    [Group G] [Countable G] (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (hinv : ∀ g x y : G, connProb μ (g * x) (g * y) = connProb μ x y) (o : G) :
    ∑' v, (∑' u, connProb μ o u * connProb μ u v) ^ 3 ≤
      ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
        (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) :=
  tsum_connProb_sq_entry_pow_three_le_triangle_weighted (Γ := G) μ hasMassTransport_self
    (fun g x y => hinv g x y) o

/-- **First comparison on a countable group.** For a connection kernel on a countable group
invariant under left multiplication, `∑_v T(o,v) T²(o,v) T³(o,v) ≤ T³(o,o)²`. -/
theorem triangle_weighted_le_sq_of_group {G : Type*} [Group G] [Countable G]
    (μ : Measure (Config G)) [IsFiniteMeasure μ]
    (hinv : ∀ g x y : G, connProb μ (g * x) (g * y) = connProb μ x y) (o : G) :
    ∑' v, connProb μ o v * (∑' u, connProb μ o u * connProb μ u v) *
        (∑' u, ∑' w, connProb μ o u * connProb μ u w * connProb μ w v) ≤
      (∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o) ^ 2 :=
  triangle_weighted_le_sq_of_isPretransitive (Γ := G) μ (fun g x y => hinv g x y) o

end PercLib.Percolation.Bond
