/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-20. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Tightness.FromBK
public import PercLib.Percolation.Bond.DisjointUnion
public import PercLib.Probability.DeterministicModification

/-!
# The quantile of a profile restricted to a finite block

Let `S` be a finite set of vertices of a countable vertex type `V`, let `Λ ⊆ S`, and let
`q` be a profile. Write `q|S` for `q` restricted to the pairs inside `S`
(`fun e => if e ∈ (S : Set V).sym2 then q e else 0`) and `q_S` for its pull-back
`q ∘ Sym2.map Subtype.val` to the subtype `↥S`.

* `maxClusterIntersection_inter_sym2`: for every configuration `ω`, the largest
  intersection with `Λ` of the clusters of `ω ∩ S.sym2` equals the one for the pulled-back
  configuration on `↥S` and the pulled-back set `Λ.subtype (· ∈ S)`. No open pair of
  `ω ∩ S.sym2` leaves `S`, and loops are discarded by the open graph, so these
  clusters stay in `S`.
* `law_restrict_le_maxClusterIntersection`: the tail laws agree.
* `tightnessScale_restrict`: `tightnessScale (q|S) Λ = tightnessScale q_S (Λ.subtype (· ∈ S))`.
* `intensityProfile_comp_sym2Map`: the pull-back of `intensityProfile J β` along any map of
  vertices is `intensityProfile (J ∘ Sym2.map f) β` (definitional).
* `restrict_quantile_left_stable`, `restrict_quantile_sq_bound_at_endpoint`: the endpoint
  lemmas of `FiniteQuantile.lean` for block-restricted quantiles on an arbitrary countable
  (possibly infinite) vertex type.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Deterministic transport -/

/-- **Clusters of the restricted configuration stay in the block.** For `Λ ⊆ S`, the
largest intersection with `Λ` of the clusters of `ω ∩ S.sym2` is the largest intersection
with `Λ.subtype (· ∈ S)` of the clusters of the pulled-back configuration on `↥S`. -/
theorem maxClusterIntersection_inter_sym2 [DecidableEq V] (S : Finset V) {Λ : Finset V}
    (hΛ : Λ ⊆ S) (ω : Config V) :
    maxClusterIntersection Λ (ω ∩ (S : Set V).sym2) =
      maxClusterIntersection (Λ.subtype (· ∈ S))
        (Sym2.map (Subtype.val : S → V) ⁻¹' ω) := by
  set ω' : Config V := ω ∩ (S : Set V).sym2
  have hpre : (Sym2.map (Subtype.val : S → V) ⁻¹' ω' : Config S) =
      Sym2.map Subtype.val ⁻¹' ω := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [ω', Set.mem_preimage, Sym2.map_mk, Set.mem_inter_iff, Set.mk_mem_sym2_iff,
        Finset.mem_coe, a.2, b.2, and_true]
  have hclosed : ∀ (a : S) (z : V), z ∉ range (Subtype.val : S → V) →
      s((a : V), z) ∉ ω' := by
    intro a z hz h
    have hz' : z ∈ S := (Set.mk_mem_sym2_iff.1 h.2).2
    exact hz ⟨⟨z, hz'⟩, rfl⟩
  have hcl : ∀ a : S, cluster ω' (a : V) =
      Subtype.val '' cluster (Sym2.map (Subtype.val : S → V) ⁻¹' ω) a := by
    intro a
    rw [cluster_image_of_closed ω' Subtype.val_injective hclosed a, hpre]
  have hΛmap : (Λ.subtype (· ∈ S)).map (Function.Embedding.subtype _) = Λ := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem (fun x hx => hΛ hx)]
  have hsup := Finset.sup_map (Λ.subtype (· ∈ S)) (Function.Embedding.subtype _)
    (fun v => (cluster ω' v ∩ (Λ : Set V)).ncard)
  rw [hΛmap] at hsup
  have hcoe : ((Λ.subtype (· ∈ S) : Finset S) : Set S) =
      (Subtype.val : S → V) ⁻¹' (Λ : Set V) := by
    ext x
    simp
  unfold maxClusterIntersection
  rw [hsup]
  congr 1
  funext a
  simp only [Function.comp_apply, Function.Embedding.coe_subtype]
  rw [hcl a, ← Set.image_inter_preimage, ← hcoe,
    Set.ncard_image_of_injective _ Subtype.val_injective]

/-! ### Transport of laws and of the quantile -/

/-- **Transport of the tail law.** -/
theorem law_restrict_le_maxClusterIntersection [Countable V] [DecidableEq V]
    (q : Sym2 V → unitInterval)
    (S : Finset V) [DecidablePred (· ∈ (S : Set V).sym2)] {Λ : Finset V} (hΛ : Λ ⊆ S)
    (n : ℕ) :
    law (fun e => if e ∈ (S : Set V).sym2 then q e else 0)
        {ω | n ≤ maxClusterIntersection Λ ω} =
      law (fun e : Sym2 S => q (Sym2.map Subtype.val e))
        {ω | n ≤ maxClusterIntersection (Λ.subtype (· ∈ S)) ω} := by
  rw [law, ← PercLib.Probability.prodBernoulli_map_inter q _,
    Measure.map_apply (by fun_prop) (measurableSet_le_maxClusterIntersection Λ n)]
  have hlaw := law_map_preimage_map q (Subtype.val_injective (p := (· ∈ S)))
  rw [show (fun e : Sym2 S => q (Sym2.map Subtype.val e)) = q ∘ Sym2.map Subtype.val from rfl,
    ← hlaw, Measure.map_apply (measurable_preimage_map _)
      (measurableSet_le_maxClusterIntersection _ n)]
  congr 1
  ext ω
  change n ≤ maxClusterIntersection Λ (ω ∩ (S : Set V).sym2) ↔ n ≤ _
  rw [maxClusterIntersection_inter_sym2 S hΛ ω]

/-- **Transport of the quantile.** The quantile of `Λ ⊆ S` under the profile restricted to
the pairs inside `S` equals the quantile of the pulled-back set on the finite subtype `↥S`
under the pulled-back profile. -/
theorem tightnessScale_restrict [Countable V] [DecidableEq V]
    (q : Sym2 V → unitInterval) (S : Finset V)
    [DecidablePred (· ∈ (S : Set V).sym2)] {Λ : Finset V} (hΛ : Λ ⊆ S) :
    tightnessScale (fun e => if e ∈ (S : Set V).sym2 then q e else 0) Λ =
      tightnessScale (fun e : Sym2 S => q (Sym2.map Subtype.val e)) (Λ.subtype (· ∈ S)) := by
  unfold tightnessScale
  congr 1
  ext n
  simp only [mem_ofPred_eq]
  rw [law_restrict_le_maxClusterIntersection q S hΛ n]

/-- **Pull-back of the intensity profile.** Pulling `intensityProfile J β` back along a map
of vertices gives the intensity profile of the pulled-back intensity. -/
theorem intensityProfile_comp_sym2Map {W : Type*} (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (f : W → V) :
    (fun e : Sym2 W => intensityProfile J β (Sym2.map f e)) =
      intensityProfile (fun e => J (Sym2.map f e)) β :=
  rfl

/-- The block-restricted intensity quantile is the intensity quantile of the finite block. -/
theorem tightnessScale_restrict_intensityProfile [Countable V] [DecidableEq V]
    (J : Sym2 V → ℝ≥0)
    (β : ℝ≥0) (S : Finset V) [DecidablePred (· ∈ (S : Set V).sym2)] {Λ : Finset V}
    (hΛ : Λ ⊆ S) :
    tightnessScale (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J β e else 0) Λ =
      tightnessScale (intensityProfile (fun e : Sym2 S => J (Sym2.map Subtype.val e)) β)
        (Λ.subtype (· ∈ S)) := by
  rw [tightnessScale_restrict _ S hΛ, intensityProfile_comp_sym2Map]

/-! ### The endpoint lemmas for block-restricted quantiles -/

/-- **Left stability of the block-restricted quantile**, on any countable vertex type. -/
theorem restrict_quantile_left_stable [Countable V] [DecidableEq V]
    (J : Sym2 V → ℝ≥0) (S : Finset V)
    [DecidablePred (· ∈ (S : Set V).sym2)] {Λ : Finset V} (hΛ : Λ ⊆ S) (b : ℝ≥0) :
    ∀ᶠ a in 𝓝[Set.Iic b] b,
      tightnessScale (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J a e else 0) Λ =
        tightnessScale
          (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J b e else 0) Λ := by
  filter_upwards [finite_quantile_left_stable
    (fun e : Sym2 S => J (Sym2.map Subtype.val e)) (Λ.subtype (· ∈ S)) b] with a ha
  rw [tightnessScale_restrict_intensityProfile J a S hΛ,
    tightnessScale_restrict_intensityProfile J b S hΛ]
  exact ha

/-- **Squared-quantile bound at the endpoint for block-restricted quantiles**, on any
countable vertex type: a bound `a M_S(a)² ≤ C` for every `0 < a < b` passes to `b`, with the
full endpoint quantile. -/
theorem restrict_quantile_sq_bound_at_endpoint [Countable V] [DecidableEq V]
    (J : Sym2 V → ℝ≥0)
    (S : Finset V) [DecidablePred (· ∈ (S : Set V).sym2)] {Λ : Finset V} (hΛ : Λ ⊆ S)
    {b : ℝ≥0} (hb : 0 < b) {C : ℝ}
    (hC : ∀ a : ℝ≥0, 0 < a → a < b →
      (a : ℝ) * (tightnessScale
        (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J a e else 0) Λ : ℝ) ^ 2
        ≤ C) :
    (b : ℝ) * (tightnessScale
      (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J b e else 0) Λ : ℝ) ^ 2
      ≤ C := by
  rw [tightnessScale_restrict_intensityProfile J b S hΛ]
  refine finite_quantile_sq_bound_at_endpoint _ _ hb fun a ha hab => ?_
  rw [← tightnessScale_restrict_intensityProfile J a S hΛ]
  exact hC a ha hab

/-! ### Non-vacuity -/

open Classical in
/-- On the infinite vertex type `ℕ`, with a nonzero kernel and a two-vertex block, the
endpoint lemma's hypotheses hold and give a genuine bound. -/
example : (tightnessScale (fun e => if e ∈ (({0, 1} : Finset ℕ) : Set ℕ).sym2 then
    intensityProfile (fun _ : Sym2 ℕ => 1) 1 e else 0) {0, 1} : ℝ) ^ 2 ≤ 9 := by
  have hbound : ∀ a : ℝ≥0, (tightnessScale (fun e =>
      if e ∈ (({0, 1} : Finset ℕ) : Set ℕ).sym2 then
        intensityProfile (fun _ : Sym2 ℕ => 1) a e else 0) {0, 1} : ℝ) ≤ 3 := by
    intro a
    have hm := tightnessScale_le_card_add_one (fun e => if e ∈ (({0, 1} : Finset ℕ) :
      Set ℕ).sym2 then intensityProfile (fun _ : Sym2 ℕ => 1) a e else 0) {0, 1}
    have hc : ({0, 1} : Finset ℕ).card = 2 := rfl
    rw [hc] at hm
    exact_mod_cast hm
  have h := restrict_quantile_sq_bound_at_endpoint (fun _ : Sym2 ℕ => 1) {0, 1}
    (Λ := {0, 1}) subset_rfl (b := 1) (by norm_num) (C := 9) (by
      intro a _ ha
      have hm' := hbound a
      have hm0 : (0 : ℝ) ≤ tightnessScale (fun e => if e ∈ (({0, 1} : Finset ℕ) :
        Set ℕ).sym2 then intensityProfile (fun _ : Sym2 ℕ => 1) a e else 0) {0, 1} :=
        Nat.cast_nonneg _
      have ha' : (a : ℝ) < 1 := ha
      have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
      nlinarith)
  simpa using h

end PercLib.Percolation.Bond
