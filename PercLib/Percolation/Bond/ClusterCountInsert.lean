/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
the elementary merging argument for components of a finite graph, the monotone product
coupling, and the loop-insensitivity of graph observables.
-/
module

public import PercLib.Percolation.Bond.ClusterCount
public import PercLib.Percolation.Bond.Diagonal.Probability

/-!
# Opening one pair: the exact change in the number of clusters

On a finite vertex type, write `κ(ω)` for the number of open clusters. Opening the pair
`s(a, b)` merges the clusters of `a` and `b` when they are distinct and changes nothing
otherwise, so `κ(ω ∪ {ab}) = κ(ω) - 1{a ↮ b}`. The expected number of clusters is
antitone in the profile even when the profiles are ordered only off the diagonal.

## Main results

* `reachable_insert_iff_of_reachable`: opening a pair whose ends are already joined does not
  change reachability.
* `card_connectedComponent_insert`: the exact formula `κ(ω ∪ {ab}) + 1{a ↮ b} = κ(ω)`.
* `integral_card_connectedComponent_eq_of_offDiagonal`: `E κ` depends only on the
  off-diagonal profile.
* `integral_card_connectedComponent_anti_of_offDiagonal`: `E_{q'} κ ≤ E_q κ` when
  `q e ≤ q' e` for every non-diagonal pair `e`.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Opening a pair whose ends are already joined does not change reachability. -/
theorem reachable_insert_iff_of_reachable {ω : Config V} {a b : V}
    (hab : (openGraph ω).Reachable a b) (u w : V) :
    (openGraph (insert s(a, b) ω)).Reachable u w ↔ (openGraph ω).Reachable u w := by
  refine ⟨fun h => ?_, fun h => h.mono (openGraph_mono (subset_insert _ _))⟩
  rcases reachable_or_of_reachable_insert ω a b u w h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exact h1.trans (hab.trans h2.symm)
  · exact h1.trans (hab.symm.trans h2.symm)

/-- **Opening one pair: the exact formula.** On a finite vertex type, opening `s(a, b)`
lowers the number of clusters by one if `a` and `b` were not joined, and leaves it
unchanged otherwise (in particular for a loop or an already open pair). -/
theorem card_connectedComponent_insert [Finite V] (ω : Config V) (a b : V)
    [Decidable ((openGraph ω).Reachable a b)] :
    Nat.card (openGraph (insert s(a, b) ω)).ConnectedComponent +
        (if (openGraph ω).Reachable a b then 0 else 1) =
      Nat.card (openGraph ω).ConnectedComponent := by
  classical
  have hle' := card_connectedComponent_le_insert_add_one ω s(a, b)
  have hle : openGraph ω ≤ openGraph (insert s(a, b) ω) := openGraph_mono (subset_insert _ _)
  let φ := ConnectedComponent.map (Hom.ofLE hle)
  have hφ : Function.Surjective φ := ConnectedComponent.surjective_map_ofLE hle
  have := Fintype.ofFinite (openGraph ω).ConnectedComponent
  have := Fintype.ofFinite (openGraph (insert s(a, b) ω)).ConnectedComponent
  split_ifs with hab
  · rw [add_zero]
    have hinj : Function.Injective φ := by
      intro C₁ C₂ h
      obtain ⟨u, rfl⟩ := C₁.exists_rep
      obtain ⟨v, rfl⟩ := C₂.exists_rep
      exact ConnectedComponent.sound
        ((reachable_insert_iff_of_reachable hab u v).1 (ConnectedComponent.exact h))
    exact (Nat.card_eq_of_bijective φ ⟨hinj, hφ⟩).symm
  · have hninj : ¬ Function.Injective φ := by
      intro hinj
      have hab' : (openGraph (insert s(a, b) ω)).Reachable a b :=
        (openGraph_adj_iff _ a b).2 ⟨mem_insert _ _, fun h => hab (h ▸ Reachable.refl a)⟩
          |>.reachable
      refine hab (ConnectedComponent.exact (hinj ?_))
      exact ConnectedComponent.sound hab'
    have hlt := Fintype.card_lt_of_surjective_not_injective φ hφ hninj
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hlt
    omega

/-- The number of clusters does not see loops. -/
theorem card_connectedComponent_sdiff_diagSet (ω : Config V) :
    Nat.card (openGraph (ω \ Sym2.diagSet)).ConnectedComponent =
      Nat.card (openGraph ω).ConnectedComponent := by
  rw [openGraph_sdiff_diagSet]

/-- **The expected number of clusters ignores the diagonal profile.** -/
theorem integral_card_connectedComponent_eq_of_offDiagonal [Fintype V]
    (p q : Sym2 V → unitInterval) (hpq : ∀ e, ¬ e.IsDiag → p e = q e) :
    ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law p =
      ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q := by
  set κ : Config V → ℕ := fun ω => Nat.card (openGraph ω).ConnectedComponent
  have hκ : Measurable κ := measurable_of_finite κ
  have hmap := law_map_eq_of_offDiagonal p q hpq κ hκ card_connectedComponent_sdiff_diagSet
  have h : ∀ r : Sym2 V → unitInterval,
      ∫ ω, (κ ω : ℝ) ∂law r = ∫ n, (n : ℝ) ∂(law r).map κ := fun r =>
    (integral_map hκ.aemeasurable (measurable_of_countable _).aestronglyMeasurable).symm
  change ∫ ω, (κ ω : ℝ) ∂law p = ∫ ω, (κ ω : ℝ) ∂law q
  rw [h p, h q, hmap]

/-- **Larger profiles off the diagonal give fewer clusters on average.** If `q e ≤ q' e`
for every non-diagonal pair `e` (diagonal values unrestricted), then `E_{q'} κ ≤ E_q κ`. -/
theorem integral_card_connectedComponent_anti_of_offDiagonal [Fintype V]
    {q q' : Sym2 V → unitInterval} (h : ∀ e, ¬ e.IsDiag → q e ≤ q' e) :
    ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q' ≤
      ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂law q := by
  classical
  set q₀ : Sym2 V → unitInterval := fun e => if e.IsDiag then 0 else q e
  set q₀' : Sym2 V → unitInterval := fun e => if e.IsDiag then 0 else q' e
  rw [integral_card_connectedComponent_eq_of_offDiagonal q q₀ (fun e hd => by simp [q₀, hd]),
    integral_card_connectedComponent_eq_of_offDiagonal q' q₀' (fun e hd => by simp [q₀', hd])]
  refine integral_card_connectedComponent_anti fun e => ?_
  by_cases hd : e.IsDiag
  · simp [q₀, q₀', hd]
  · simpa [q₀, q₀', hd] using h e hd

end PercLib.Percolation.Bond
