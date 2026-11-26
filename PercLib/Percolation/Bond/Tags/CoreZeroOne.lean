/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Ergodic
public import PercLib.Percolation.Bond.ZeroOne

/-! Correspondence wrappers for the zero-one law of infinite-cluster existence and ergodicity of
translation-invariant bond laws.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PercLib.Percolation.Bond

/-- On a countable vertex set the event that an infinite cluster exists is measurable and
has probability zero or one, for every profile. -/
@[tag "H0OC"]
theorem exists_cluster_infinite_zero_one {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) :
    MeasurableSet {ω : Config V | ∃ x, (cluster ω x).Infinite} ∧
    (law q {ω | ∃ x, (cluster ω x).Infinite} = 0 ∨
      law q {ω | ∃ x, (cluster ω x).Infinite} = 1) :=
  ⟨measurableSet_exists_cluster_infinite, law_exists_cluster_infinite_eq_zero_or_one q⟩

/-- For a translation-invariant profile on an infinite group: invariant measurable events
are trivial, invariant measurable `ℕ∞`-valued observables are almost surely constant, and
the law is mixing along every sequence of distinct translations. -/
@[tag "WUAF"]
theorem translation_invariant_ergodic {G : Type*} [AddGroup G] [Infinite G]
    (q : Sym2 G → unitInterval) (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    (∀ A : Set (Config G), MeasurableSet A →
      (∀ g : G, (fun ω : Config G => Sym2.map (· + g) '' ω) ⁻¹' A = A) →
      law q A = 0 ∨ law q A = 1) ∧
    (∀ f : Config G → ℕ∞, Measurable f →
      (∀ (g : G) (ω : Config G), f (Sym2.map (· + g) '' ω) = f ω) →
      ∃ c : ℕ∞, ∀ᵐ ω ∂(law q), f ω = c) ∧
    (∀ g : ℕ → G, Function.Injective g → ∀ A B : Set (Config G),
      MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => law q (A ∩ (fun ω : Config G => Sym2.map (· + g n) '' ω) ⁻¹' B))
        atTop (𝓝 (law q A * law q B))) := by
  refine ⟨fun A hA hinv => law_eq_zero_or_one_of_translation_invariant q hq hA hinv,
    fun f hf hinv => ae_eq_const_of_translation_invariant q hq hf hinv,
    fun g hg A B hA hB => ?_⟩
  choose e he using fun n => exists_equiv_sym2Map_add (g n)
  have h := PercLib.Probability.prodBernoulli_tendsto_inter_preimage q e
    (fun n => by rw [he n]; exact measurePreserving_image_sym2Map_add q hq (g n))
    (PercLib.Probability.eventually_forall_notMem_of_finite e fun i j => by
      simp only [he]
      exact finite_setOf_sym2Map_add_eq hg i j) hA hB
  simp only [he] at h
  exact h

end PercLib.Percolation.Bond
