/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Association wrappers for existing diagonal, standard-Borel and block-independence
results on the canonical configuration space. No probability law is redefined.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Diagonal.Probability
public import PercLib.Probability.Defs
public import PercLib.Probability.Tags.ProductModel

/-!
# Symmetries of the configuration space: correspondence

Wiki correspondence for loop erasure, diagonal insensitivity, the standard Borel structure and block
independence.

## Main results

* `loop_erasure_transport`
* `diagonal_insensitive_cluster_laws`
* `countable_configuration_standardBorel`
* `disjoint_block_independence`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PercLib.Probability

open PercLib.Percolation.Bond

open Classical in
/-- Loop erasure is measurable, transports the law, and preserves the laws of all
measurable insensitive observables and the probabilities of insensitive events. -/
@[tag "LNKT"] theorem loop_erasure_transport {V α : Type*} [MeasurableSpace α]
    (p : Sym2 V → unitInterval) :
    Measurable (fun ω : Config V => ω \ Sym2.diagSet) ∧
    (law p).map (fun ω => ω \ Sym2.diagSet) =
      law (fun e => if e.IsDiag then 0 else p e) ∧
    (∀ q : Sym2 V → unitInterval, (∀ e, ¬ e.IsDiag → p e = q e) →
      ∀ f : Config V → α, Measurable f →
        (∀ ω, f (ω \ Sym2.diagSet) = f ω) → (law p).map f = (law q).map f) ∧
    (∀ q : Sym2 V → unitInterval, (∀ e, ¬ e.IsDiag → p e = q e) →
      ∀ A : Set (Config V), MeasurableSet A →
        (∀ ω, ω \ Sym2.diagSet ∈ A ↔ ω ∈ A) → law p A = law q A) := by
  refine ⟨measurable_sdiff_diagSet, law_map_sdiff_diagSet p,
    fun q hpq f hf hdiag => law_map_eq_of_offDiagonal p q hpq f hf hdiag, ?_⟩
  intro q hpq A hA hdiag
  apply law_event_eq_of_offDiagonal p q hpq hA
  intro ω ω' h
  rw [← hdiag ω, ← hdiag ω', h]

/-- Off-diagonal agreement preserves two-point functions, ENat-valued cluster laws,
susceptibility and all measurable nonnegative functions of the cluster volume. -/
@[tag "EYCQ"] theorem diagonal_insensitive_cluster_laws {V : Type*} [Countable V]
    (p q : Sym2 V → unitInterval) (hpq : ∀ e, ¬ e.IsDiag → p e = q e) :
    (∀ x y, tau p x y = tau q x y) ∧
    (∀ x, (law p).map (fun ω => (cluster ω x).encard) =
      (law q).map (fun ω => (cluster ω x).encard)) ∧
    (∀ x, chi p x = chi q x) ∧
    (∀ x (A : Set ℕ∞), MeasurableSet A →
      law p {ω | (cluster ω x).encard ∈ A} =
        law q {ω | (cluster ω x).encard ∈ A}) ∧
    (∀ x (g : ℕ∞ → ℝ≥0∞), Measurable g →
      ∫⁻ ω, g (cluster ω x).encard ∂law p =
        ∫⁻ ω, g (cluster ω x).encard ∂law q) := by
  refine ⟨tau_eq_of_offDiagonal p q hpq, cluster_volume_law_eq_of_offDiagonal p q hpq,
    chi_eq_of_offDiagonal p q hpq, ?_, ?_⟩
  · intro x A hA
    have h := congrArg (fun μ : Measure ℕ∞ => μ A)
      (cluster_volume_law_eq_of_offDiagonal p q hpq x)
    simpa only [Measure.map_apply (measurable_encard_cluster x) hA,
      Set.preimage] using h
  · intro x g hg
    rw [← lintegral_map hg (measurable_encard_cluster x),
      cluster_volume_law_eq_of_offDiagonal p q hpq,
      lintegral_map hg (measurable_encard_cluster x)]

/-- The existing coordinate sigma-algebra on countable configurations is standard
Borel, including configurations indexed by unordered vertex pairs. -/
@[tag "784S"] theorem countable_configuration_standardBorel {I : Type*} [Countable I] :
    StandardBorelSpace (Set I) ∧ StandardBorelSpace (Config I) :=
  ⟨inferInstance, inferInstance⟩

/-- Disjoint deterministic blocks have independent restrictions and observables,
their event probabilities factor under the restricted profiles, and membership
coordinates are mutually independent. There is no countability hypothesis. -/
@[tag "DYU8"] theorem disjoint_block_independence {I α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (p : I → unitInterval) (S T : Set I) (hST : Disjoint S T) :
    IndepFun (fun ω : Set I => (Subtype.val ⁻¹' ω : Set S))
      (fun ω : Set I => (Subtype.val ⁻¹' ω : Set T)) (prodBernoulli p) ∧
    (∀ (A : Set (Set S)) (B : Set (Set T)), MeasurableSet A → MeasurableSet B →
      prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set S) ∈ A ∧
        (Subtype.val ⁻¹' ω : Set T) ∈ B} =
        prodBernoulli (fun i : S => p i) A * prodBernoulli (fun i : T => p i) B) ∧
    (∀ (f : Set S → α) (g : Set T → β), Measurable f → Measurable g →
      IndepFun (fun ω : Set I => f (Subtype.val ⁻¹' ω))
        (fun ω : Set I => g (Subtype.val ⁻¹' ω)) (prodBernoulli p)) ∧
    iIndepFun (fun i (ω : Set I) => i ∈ ω) (prodBernoulli p) := by
  refine ⟨prodBernoulli_indepFun_blocks p S T hST, ?_,
    fun f g hf hg => prodBernoulli_indepFun_block_observables p S T hST f g hf hg,
    prodBernoulli_iIndepFun_mem p⟩
  intro A B hA hB
  have h := prodBernoulli_block_inter p S T hST A B hA hB
  change prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set S) ∈ A ∧
    (Subtype.val ⁻¹' ω : Set T) ∈ B} =
    prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set S) ∈ A} *
      prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set T) ∈ B} at h
  rw [h,
    prodBernoulli_restrict_apply p S A hA, prodBernoulli_restrict_apply p T B hB]

/-! Non-vacuity: endpoint diagonals, infinite volume, empty configurations and
two infinite coordinate blocks are all covered by the tagged assertions. -/

example (p : Sym2 Bool → unitInterval) (x : Bool) :
    chi (fun e => if e.IsDiag then 0 else p e) x =
      chi (fun e => if e.IsDiag then 1 else p e) x :=
  (diagonal_insensitive_cluster_laws _ _ (fun e he => by simp [he])).2.2.1 x

example : chi (fun e : Sym2 ℕ => if e.IsDiag then 0 else 1) 0 = ∞ := by
  rw [(diagonal_insensitive_cluster_laws _ (fun _ => 1)
    (fun e he => by simp [he])).2.2.1]
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := by
    ext y
    simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]
  simp [chi, law, prodBernoulli_const, hc]

example : StandardBorelSpace (Set Empty) :=
  countable_configuration_standardBorel.1

example (p : ℤ → unitInterval) :
    IndepFun (fun ω : Set ℤ => (Subtype.val ⁻¹' ω : Set (Iio (0 : ℤ))))
      (fun ω : Set ℤ => (Subtype.val ⁻¹' ω : Set (Ici (0 : ℤ)))) (prodBernoulli p) :=
  (disjoint_block_independence (α := Unit) (β := Unit) p (Iio 0) (Ici 0)
    (Set.disjoint_left.mpr (by
      intro i hi hj
      exact (not_lt_of_ge (show 0 ≤ i from hj)) (show i < 0 from hi)))).1

end PercLib.Probability
