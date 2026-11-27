/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Original finite-volume exhaustion proofs using the canonical intensity law and the
proved boundary Russo identity. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.BoundaryRusso.ClusterDistribution
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The integrated infinite-volume boundary Russo identity

## Main results

* `tendsto_integral_boundarySusceptibility_restrict`: finite-domain boundary expectations
  converge to the actual finite-cluster distribution sum.
* `intervalIntegrable_tsum_law_cluster_eq_mul_boundarySusceptibility`: this expected boundary
  susceptibility is interval integrable under a row cap and finite uniform susceptibility
  at the upper endpoint.
* `chi_sub_eq_integral_boundarySusceptibility`: on a positive parameter interval, the actual
  susceptibility increment equals the integral of that boundary expectation.

The root cluster and its complementary domain play different roles: restrictions of the
root cluster eventually stabilize when that cluster is finite, while complementary
connection probabilities increase with the volume once the excluded set is fixed. The
configuration limit and the parameter-integral limit use separate dominated-convergence
arguments. No infinite-volume derivative or critical-cluster hypothesis is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Restricting an intensity kernel along an embedding cannot increase its rooted
off-diagonal row sum. Loops are discarded on both sides. -/
theorem rowSum_comp_sym2Map_le {W : Type*} (f : V ↪ W)
    (J : Sym2 W → ℝ≥0) (u : V) :
    rowSum (fun e => (J (Sym2.map f e) : ℝ≥0∞)) u ≤
      rowSum (fun e => (J e : ℝ≥0∞)) (f u) := by
  classical
  rw [rowSum_def, rowSum_def]
  simpa only [Sym2.map_mk, f.injective.eq_iff] using
    ENNReal.tsum_comp_le_tsum_of_injective f.injective
      (fun w => if w = f u then 0 else (J s(f u, w) : ℝ≥0∞))

/-- The same ambient row and susceptibility caps dominate boundary functionals in
every embedded vertex domain, with the restricted canonical intensity kernel. -/
theorem boundarySusceptibility_comp_sym2Map_le [Countable V] {W : Type*} [Countable W]
    (f : V ↪ W) (J : Sym2 W → ℝ≥0) (β : ℝ≥0) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤) (C : Finset V) :
    boundarySusceptibility (fun e => J (Sym2.map f e)) β C ≤
      (C.card : ℝ) * (R : ℝ) * (⨆ v, chi (intensityProfile J β) v).toReal := by
  have hχle : (⨆ v, chi (intensityProfile (fun e => J (Sym2.map f e)) β) v) ≤
      ⨆ v, chi (intensityProfile J β) v := by
    refine iSup_le fun v => ?_
    exact (chi_le_of_embedding f
      (q := intensityProfile (fun e => J (Sym2.map f e)) β)
      (q' := intensityProfile J β) (fun _ _ => le_rfl) v).trans (le_iSup _ (f v))
  refine (boundarySusceptibility_le_card_mul_row_cap _ β R
    (fun v => (rowSum_comp_sym2Map_le f J v).trans (hrow (f v)))
    (ne_top_of_le_ne_top hχ hχle) C).trans ?_
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hχ hχle) (by positivity)

/-- Pulling back a configuration along an embedding preserves connections when the
ambient connection is restricted to the image of the original vertex domain. -/
theorem mem_localConn_preimage_sym2Map_iff {W : Type*} (f : V ↪ W)
    (ω : Config W) (A : Set V) (x y : V) :
    (Sym2.map f ⁻¹' ω : Config V) ∈ localConn A x y ↔
      ω ∈ localConn (f '' A) (f x) (f y) := by
  classical
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · let e : ((openGraph (Sym2.map f ⁻¹' ω)).induce A) ≃g
          ((openGraph ω).induce (f '' A)) :=
        { toEquiv := Equiv.Set.image f A f.injective
          map_rel_iff' := by
            intro a b
            simp [SimpleGraph.induce, SimpleGraph.comap_adj, openGraph_adj_iff,
              f.injective.eq_iff, Subtype.coe_inj] }
      rw [mem_localConn_iff_reachable hx hy,
        mem_localConn_iff_reachable (mem_image_of_mem f hx) (mem_image_of_mem f hy)]
      exact (SimpleGraph.Iso.reachable_iff (φ := e)).symm
    · rw [localConn_of_notMem_right hy,
        localConn_of_notMem_right (fun h => hy (f.injective.mem_set_image.mp h))]
      simp
  · rw [localConn_of_notMem hx,
      localConn_of_notMem (fun h => hx (f.injective.mem_set_image.mp h))]
    simp

/-- Exact law transport for internal connections under a vertex embedding. Only the
source domain needs to be countable for the event to be measurable. -/
theorem law_localConn_preimage_sym2Map [Countable V] {W : Type*}
    (f : V ↪ W) (q : Sym2 W → unitInterval) (A : Set V) (x y : V) :
    law (fun e => q (Sym2.map f e)) (localConn A x y) =
      law q (localConn (f '' A) (f x) (f y)) := by
  rw [← law_map_preimage_sym2Map f q,
    Measure.map_apply (measurable_preimage_sym2Map f) (measurableSet_localConn A x y)]
  congr 1
  ext ω
  exact mem_localConn_preimage_sym2Map_iff f ω A x y

/-- The image of a cluster in a restricted configuration is exactly the internal cluster
in the original configuration. This is not the intersection with the full cluster. -/
theorem image_cluster_preimage_subtype_eq_localCluster (ω : Config V) (A : Set V)
    (o : A) :
    Subtype.val '' cluster (Sym2.map (Subtype.val : A → V) ⁻¹' ω) o =
      localCluster ω A o := by
  ext v
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨o.2, v.2, ?_⟩
    rw [openGraph_induce]
    exact hv
  · rintro ⟨_, hv, h⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    change (openGraph (Sym2.map (Subtype.val : A → V) ⁻¹' ω)).Reachable o ⟨v, hv⟩
    rwa [openGraph_induce] at h

/-- The boundary functional in an embedded domain uses the ambient law with all
complementary connections restricted to that domain. The inner connection probability
already vanishes when its starting vertex belongs to the excluded cluster. -/
theorem boundarySusceptibility_comp_sym2Map_eq [Countable V] {W : Type*}
    (f : V ↪ W) (J : Sym2 W → ℝ≥0) (β : ℝ≥0) (C : Finset V) :
    boundarySusceptibility (fun e => J (Sym2.map f e)) β C =
      ∑ u ∈ C, ∑' v, (J s(f u, f v) : ℝ) *
        ∑' w, (law (intensityProfile J β)).real
          (localConn (f '' (C : Set V)ᶜ) (f v) (f w)) := by
  classical
  rw [boundarySusceptibility_eq]
  have hq : intensityProfile (fun e => J (Sym2.map f e)) β =
      fun e => intensityProfile J β (Sym2.map f e) := rfl
  rw [hq]
  simp_rw [measureReal_def, law_localConn_preimage_sym2Map f (intensityProfile J β)]
  refine Finset.sum_congr rfl fun u _ => tsum_congr fun v => ?_
  by_cases hv : v ∈ C
  · have hv' : f v ∉ f '' (C : Set V)ᶜ := by
      intro h
      exact (f.injective.mem_set_image.mp h) hv
    simp [hv, localConn_of_notMem hv']
  · simp [hv, Sym2.map_mk]

open Classical in
/-- A finite-domain boundary susceptibility is exactly the ambient-law boundary sum
whose connection paths are restricted to that domain minus the excluded finite cluster.
Indices outside the domain contribute zero, so extending the sums introduces no term. -/
theorem boundarySusceptibility_finset_restrict_eq (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (F : Finset V) (C : Finset (F : Set V)) :
    let f : (F : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    let D := C.map f
    boundarySusceptibility (fun e => J (Sym2.map f e)) β C =
      ∑ u ∈ D, ∑' v, (J s(u, v) : ℝ) *
        ∑' w, (law (intensityProfile J β)).real
          (localConn ((F : Set V) ∩ (D : Set V)ᶜ) v w) := by
  intro f D
  have hD : (D : Set V) = f '' (C : Set (F : Set V)) := Finset.coe_map f C
  have hr : Set.range f = (F : Set V) := by
    ext v
    simp [f]
  have himage : f '' (C : Set (F : Set V))ᶜ = (F : Set V) ∩ (D : Set V)ᶜ := by
    rw [Set.image_compl_eq_range_sdiff_image f.injective, hr, ← hD]
    rfl
  rw [boundarySusceptibility_comp_sym2Map_eq f J β C, himage]
  change _ = ∑ u ∈ C.map f, _
  rw [Finset.sum_map]
  simp only [tsum_fintype]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [tsum_eq_sum (s := F) (fun v hv => by
    have hv' : v ∉ (F : Set V) ∩ (D : Set V)ᶜ := fun h => hv h.1
    simp [localConn_of_notMem hv'])]
  conv_rhs => rw [← Finset.sum_finset_coe]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  rw [tsum_eq_sum (s := F) (fun w hw => by
    have hw' : w ∉ (F : Set V) ∩ (D : Set V)ᶜ := fun h => hw h.1
    simp [localConn_of_notMem_right hw'])]
  conv_rhs => rw [← Finset.sum_finset_coe]
  rfl

/-- Finite paths inside a fixed domain are eventually contained in its intersections
with an increasing exhaustion. Endpoints outside the fixed domain remain disconnected. -/
theorem localConn_eq_iUnion_inter_of_exhaustion
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    (A : Set V) (x y : V) :
    localConn A x y = ⋃ n, localConn (S n ∩ A) x y := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, hy, ⟨w⟩⟩
    let p := w.map (SimpleGraph.Embedding.induce A).toHom
    have hA : ∀ v ∈ p.support.toFinset, v ∈ A := by
      intro v hv
      simp only [p, SimpleGraph.Walk.support_map, List.mem_toFinset, List.mem_map] at hv
      obtain ⟨u, _, rfl⟩ := hv
      exact u.2
    have hsub : (p.support.toFinset : Set V) ⊆ ⋃ n, S n := by
      intro v _
      exact mem_iUnion.mpr (hcover v)
    obtain ⟨n, hn⟩ := hS.directed_le.exists_mem_subset_of_finset_subset_biUnion hsub
    have hp : ∀ v ∈ p.support, v ∈ S n ∩ A := by
      intro v hv
      have hv' : v ∈ p.support.toFinset := by simpa using hv
      exact ⟨hn hv', hA v hv'⟩
    exact mem_iUnion.mpr ⟨n, hp x p.start_mem_support, hp y p.end_mem_support,
      ⟨p.induce _ hp⟩⟩
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact localConn_mono_set inter_subset_right x y hn

/-- Actual complementary-domain probabilities converge along a vertex exhaustion. -/
theorem tendsto_law_localConn_inter_of_exhaustion (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    (A : Set V) (x y : V) :
    Tendsto (fun n => law q (localConn (S n ∩ A) x y)) atTop
      (𝓝 (law q (localConn A x y))) := by
  have hmono : Monotone fun n => localConn (S n ∩ A) x y :=
    monotone_localConn (fun _ _ h => inter_subset_inter_left A (hS h)) x y
  have h := tendsto_measure_iUnion_atTop (μ := law q) hmono
  simpa only [← localConn_eq_iUnion_inter_of_exhaustion hS hcover A x y,
    Function.comp_def] using h

/-- The same exhaustion limit for real connection probabilities; finiteness comes
from the actual probability law. -/
theorem tendsto_lawReal_localConn_inter_of_exhaustion (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    (A : Set V) (x y : V) :
    Tendsto (fun n => (law q).real (localConn (S n ∩ A) x y)) atTop
      (𝓝 ((law q).real (localConn A x y))) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (tendsto_law_localConn_inter_of_exhaustion q hS hcover A x y)

/-- For a fixed excluded finite cluster, the actual finite-domain boundary sums converge
to the boundary susceptibility. Both sums are dominated by the ambient row and susceptibility
bounds; no monotonicity of a random excluded cluster is asserted. -/
theorem tendsto_boundarySusceptibility_domain_sum [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤)
    (C : Finset V) {S : ℕ → Set V} (hS : Monotone S)
    (hcover : ∀ v, ∃ n, v ∈ S n) :
    Tendsto (fun n => ∑ u ∈ C, ∑' v, (J s(u, v) : ℝ) *
        ∑' w, (law (intensityProfile J β)).real
          (localConn (S n ∩ (C : Set V)ᶜ) v w)) atTop
      (𝓝 (boundarySusceptibility J β C)) := by
  classical
  let q := intensityProfile J β
  let M := ⨆ v, chi q v
  have hne (v : V) : (∑' w, law q (localConn (C : Set V)ᶜ v w)) ≠ ⊤ :=
    ne_top_of_le_ne_top hχ ((tsum_law_deleted_le_chi q C v).trans (le_iSup _ v))
  have hsum (v : V) : Summable fun w => (law q).real (localConn (C : Set V)ᶜ v w) := by
    simpa only [measureReal_def] using ENNReal.summable_toReal (hne v)
  have hprob (n : ℕ) (v w : V) :
      (law q).real (localConn (S n ∩ (C : Set V)ᶜ) v w) ≤
        (law q).real (localConn (C : Set V)ᶜ v w) :=
    measureReal_mono (localConn_mono_set inter_subset_right v w) (measure_ne_top _ _)
  have hinner (v : V) :
      Tendsto (fun n => ∑' w, (law q).real (localConn (S n ∩ (C : Set V)ᶜ) v w))
        atTop (𝓝 (∑' w, (law q).real (localConn (C : Set V)ᶜ v w))) := by
    refine tendsto_tsum_of_dominated_convergence (hsum v)
      (fun w => tendsto_lawReal_localConn_inter_of_exhaustion q hS hcover _ v w) ?_
    exact Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact hprob n v w
  have hinnerle (n : ℕ) (v : V) :
      (∑' w, (law q).real (localConn (S n ∩ (C : Set V)ᶜ) v w)) ≤
        ∑' w, (law q).real (localConn (C : Set V)ᶜ v w) :=
    ((hsum v).of_nonneg_of_le (fun _ => measureReal_nonneg) (hprob n v)).tsum_le_tsum
      (hprob n v) (hsum v)
  have hlim (u : V) (hu : u ∈ C) :
      Tendsto (fun n => ∑' v, (J s(u, v) : ℝ) *
        ∑' w, (law q).real (localConn (S n ∩ (C : Set V)ᶜ) v w)) atTop
        (𝓝 (∑' v, (J s(u, v) : ℝ) *
          ∑' w, (law q).real (localConn (C : Set V)ᶜ v w))) := by
    have hbound : (∑' v, (J s(u, v) : ℝ≥0∞) *
        ∑' w, law q (localConn (C : Set V)ᶜ v w)) ≤ R * M := by
      calc
        _ ≤ ∑' v, (if v = u then 0 else (J s(u, v) : ℝ≥0∞)) * M := by
          refine ENNReal.tsum_le_tsum fun v => ?_
          by_cases hv : v ∈ C
          · simp [localConn_of_notMem (show v ∉ (C : Set V)ᶜ from fun h => h hv)]
          · have hvu : v ≠ u := fun h => hv (h ▸ hu)
            rw [ite_eq_right hvu]
            exact mul_le_mul_right
              ((tsum_law_deleted_le_chi q C v).trans (le_iSup _ v)) _
        _ = rowSum (fun e => (J e : ℝ≥0∞)) u * M := by
          rw [rowSum_def, ENNReal.tsum_mul_right]
        _ ≤ R * M := mul_le_mul_left (hrow u) _
    have hout : Summable fun v => (J s(u, v) : ℝ) *
        ∑' w, (law q).real (localConn (C : Set V)ᶜ v w) := by
      have hf := ENNReal.summable_toReal
        (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hχ) hbound)
      convert hf using 1
      funext v
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
        ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
      rfl
    refine tendsto_tsum_of_dominated_convergence hout
      (fun v => (hinner v).const_mul (J s(u, v) : ℝ)) ?_
    exact Eventually.of_forall fun n v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hinnerle n v) (J s(u, v)).coe_nonneg
  have heq : boundarySusceptibility J β C =
      ∑ u ∈ C, ∑' v, (J s(u, v) : ℝ) *
        ∑' w, (law q).real (localConn (C : Set V)ᶜ v w) := by
    rw [boundarySusceptibility_eq]
    refine Finset.sum_congr rfl fun u _ => tsum_congr fun v => ?_
    by_cases hv : v ∈ C
    · simp [hv, localConn_of_notMem (show v ∉ (C : Set V)ᶜ from fun h => h hv)]
    · simp [hv, q]
  rw [heq]
  exact tendsto_finsetSum C hlim

open Classical in
/-- Finite-domain boundary expectations converge to the actual finite-cluster distribution
sum. The configurations are all compared under one ambient law; only the fixed-cluster
connection sums use monotonicity. -/
theorem tendsto_integral_boundarySusceptibility_restrict [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤)
    (S : ℕ → Finset V) (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    (ho : ∀ n, o ∈ S n) :
    Tendsto (fun n : ℕ => ∫ ω : Config (S n : Set V),
        boundarySusceptibility
          (fun e : Sym2 (S n : Set V) => J (Sym2.map (fun v : (S n : Set V) => (v : V)) e)) β
          (Set.toFinite (cluster ω ⟨o, ho n⟩)).toFinset
        ∂law (intensityProfile
          (fun e : Sym2 (S n : Set V) => J (Sym2.map (fun v : (S n : Set V) => (v : V)) e)) β))
      atTop (𝓝 (∑' C : Finset V,
        (law (intensityProfile J β)).real {ω : Config V | cluster ω o = (C : Set V)} *
          boundarySusceptibility J β C)) := by
  let q := intensityProfile J β
  let M := (⨆ v, chi q v).toReal
  let f (n : ℕ) : (S n : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let C (n : ℕ) (ω : Config V) : Finset (S n : Set V) :=
    (Set.toFinite (cluster (Sym2.map (f n) ⁻¹' ω) ⟨o, ho n⟩)).toFinset
  let D (n : ℕ) (ω : Config V) : Finset V := (C n ω).map (f n)
  let B (n : ℕ) (ω : Config V) : ℝ :=
    boundarySusceptibility (fun e => J (Sym2.map (f n) e)) β (C n ω)
  let F (ω : Config V) : ℝ :=
    if h : (cluster ω o).Finite then boundarySusceptibility J β h.toFinset else 0
  have hroot : chi q o ≠ ⊤ := ne_top_of_le_ne_top hχ (le_iSup _ o)
  have hfin := ae_cluster_finite_of_chi_lt_top hroot.lt_top
  have hD (n : ℕ) (ω : Config V) : (D n ω : Set V) = localCluster ω (S n : Set V) o := by
    rw [show D n ω = (C n ω).map (f n) from rfl, Finset.coe_map]
    simp only [C, Set.Finite.coe_toFinset]
    exact image_cluster_preimage_subtype_eq_localCluster ω (S n : Set V) ⟨o, ho n⟩
  have hBm (n : ℕ) : Measurable (B n) := by
    exact (Measurable.of_discrete (f := fun ω : Config (S n : Set V) =>
      boundarySusceptibility (fun e => J (Sym2.map (f n) e)) β
        (Set.toFinite (cluster ω ⟨o, ho n⟩)).toFinset)).comp
      (measurable_preimage_sym2Map (f n))
  have hvolm : Measurable (fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster o)
  have hvoli : Integrable (fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞).toReal)
      (law q) := integrable_toReal_of_lintegral_ne_top hvolm.aemeasurable hroot
  have hbound (n : ℕ) : ∀ᵐ ω ∂law q,
      ‖B n ω‖ ≤ (R : ℝ) * M * ((cluster ω o).encard : ℝ≥0∞).toReal := by
    filter_upwards [hfin] with ω hω
    have hsub : (D n ω : Set V) ⊆ cluster ω o := by
      rw [hD]
      exact (localCluster_subset ω (S n : Set V) o).trans inter_subset_left
    have hcard : (C n ω).card ≤ (cluster ω o).ncard := by
      have h := Set.ncard_le_ncard hsub hω
      simpa [D] using h
    have hcardR : ((C n ω).card : ℝ) ≤ ((cluster ω o).ncard : ℝ) := by exact_mod_cast hcard
    have hv : ((cluster ω o).encard : ℝ≥0∞).toReal = ((cluster ω o).ncard : ℝ) := by
      rw [← hω.cast_ncard_eq]
      simp
    rw [Real.norm_eq_abs, abs_of_nonneg (boundarySusceptibility_nonneg _ _ _)]
    calc
      B n ω ≤ ((C n ω).card : ℝ) * (R : ℝ) * M :=
        boundarySusceptibility_comp_sym2Map_le (f n) J β R hrow hχ (C n ω)
      _ = (R : ℝ) * M * ((C n ω).card : ℝ) := by ring
      _ ≤ (R : ℝ) * M * ((cluster ω o).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hcardR (by positivity)
      _ = _ := by rw [hv]
  have hlim : ∀ᵐ ω ∂law q, Tendsto (fun n => B n ω) atTop (𝓝 (F ω)) := by
    filter_upwards [hfin] with ω hω
    have hS' : Monotone fun n => (S n : Set V) := fun _ _ h => hS h
    have hevent : ∀ᶠ n in atTop, D n ω = hω.toFinset := by
      filter_upwards [eventually_localCluster_eq_cluster_of_finite hS' hcover ω o hω]
        with n hn
      apply Finset.coe_injective
      rw [hD, hn, hω.coe_toFinset]
    have htarget : F ω = boundarySusceptibility J β hω.toFinset := by simp [F, hω]
    rw [htarget]
    have ht := tendsto_boundarySusceptibility_domain_sum J β R hrow hχ hω.toFinset hS' hcover
    apply ht.congr'
    filter_upwards [hevent] with n hn
    have h := boundarySusceptibility_finset_restrict_eq J β (S n) (C n ω)
    change B n ω = ∑ u ∈ D n ω, ∑' v, (J s(u, v) : ℝ) *
      ∑' w, (law q).real (localConn ((S n : Set V) ∩ (D n ω : Set V)ᶜ) v w) at h
    rw [hn] at h
    exact h.symm
  have ht := tendsto_integral_of_dominated_convergence
    (fun ω => (R : ℝ) * M * ((cluster ω o).encard : ℝ≥0∞).toReal)
    (fun n => (hBm n).aestronglyMeasurable) (hvoli.const_mul _) hbound hlim
  have hmap (n : ℕ) : (∫ ω : Config (S n : Set V),
      boundarySusceptibility (fun e => J (Sym2.map (f n) e)) β
        (Set.toFinite (cluster ω ⟨o, ho n⟩)).toFinset
      ∂law (intensityProfile (fun e => J (Sym2.map (f n) e)) β)) =
      ∫ ω, B n ω ∂law q := by
    change (∫ ω : Config (S n : Set V),
      boundarySusceptibility (fun e => J (Sym2.map (f n) e)) β
        (Set.toFinite (cluster ω ⟨o, ho n⟩)).toFinset
      ∂law (fun e => q (Sym2.map (f n) e))) = _
    rw [← law_map_preimage_sym2Map (f n) q,
      integral_map (measurable_preimage_sym2Map (f n)).aemeasurable
        (Measurable.of_discrete).aestronglyMeasurable]
  have ht' : Tendsto (fun n => ∫ ω, B n ω ∂law q) atTop
      (𝓝 (∑' C : Finset V, (law q).real {ω : Config V | cluster ω o = (C : Set V)} *
        boundarySusceptibility J β C)) := by
    simpa only [F, integral_finite_cluster_functional_eq_tsum q o
      (fun C => boundarySusceptibility J β C) (boundarySusceptibility_nonneg J β)] using ht
  exact ht'.congr' (Eventually.of_forall fun n => (hmap n).symm)

open Classical in
/-- Finite-volume boundary expectations are continuous in the real intensity parameter,
including the truncation to nonnegative intensities at zero. -/
theorem continuous_integral_boundarySusceptibility_finite [Fintype V]
    (J : Sym2 V → ℝ≥0) (o : V) :
    Continuous (fun t : ℝ => ∫ ω, boundarySusceptibility J t.toNNReal
      (Set.toFinite (cluster ω o)).toFinset ∂law (intensityProfile J t.toNNReal)) := by
  have hq : Continuous (fun t : ℝ => intensityProfile J t.toNNReal) := by
    exact continuous_pi fun e =>
      ((continuous_intensityProfile J e).subtype_mk
        (fun β => (intensityProfile J β e).property)).comp continuous_real_toNNReal
  have hp (E : Set (Config V)) :
      Continuous (fun t : ℝ => (law (intensityProfile J t.toNNReal)).real E) := by
    have h : Continuous (fun t : ℝ => law (intensityProfile J t.toNNReal) E) :=
      (PercLib.Probability.continuous_prodBernoulli_finite_apply E).comp hq
    exact continuous_iff_continuousAt.mpr fun t =>
      (ENNReal.continuousAt_toReal (measure_ne_top (law (intensityProfile J t.toNNReal)) E)).comp
        (f := fun s : ℝ => law (intensityProfile J s.toNNReal) E) h.continuousAt
  have hPhi (C : Finset V) : Continuous (fun t : ℝ => boundarySusceptibility J t.toNNReal C) := by
    simp only [boundarySusceptibility_eq, tsum_fintype]
    apply continuous_finsetSum
    intro u _
    apply continuous_finsetSum
    intro v _
    exact continuous_const.mul (continuous_finsetSum _ fun w _ => hp _)
  have heq : (fun t : ℝ => ∫ ω, boundarySusceptibility J t.toNNReal
      (Set.toFinite (cluster ω o)).toFinset ∂law (intensityProfile J t.toNNReal)) =
      fun t => ∑ C : Set V,
        (law (intensityProfile J t.toNNReal)).real {ω | cluster ω o = C} *
          boundarySusceptibility J t.toNNReal C.toFinite.toFinset := by
    funext t
    exact integral_cluster_functional_eq_sum _ o
      (fun C => boundarySusceptibility J t.toNNReal C.toFinite.toFinset)
  rw [heq]
  exact continuous_finsetSum _ fun C _ => (hp _).mul (hPhi _)

/-- The real finite-cluster probability sum has the same quantitative bound as its
extended nonnegative version; the proof explicitly verifies finiteness before conversion. -/
theorem tsum_lawReal_cluster_eq_mul_boundarySusceptibility_le [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤) :
    (∑' C : Finset V, (law (intensityProfile J β)).real
        {ω : Config V | cluster ω o = (C : Set V)} * boundarySusceptibility J β C) ≤
      (R : ℝ) * (⨆ v, chi (intensityProfile J β) v).toReal *
        (chi (intensityProfile J β) o).toReal := by
  have hf : (R : ℝ≥0∞) * (⨆ v, chi (intensityProfile J β) v) *
      chi (intensityProfile J β) o ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hχ)
      (ne_top_of_le_ne_top hχ (le_iSup _ o))
  have h := ENNReal.toReal_mono hf
    (tsum_law_cluster_eq_mul_ofReal_boundarySusceptibility_le J β o R hrow hχ)
  rw [ENNReal.tsum_toReal_eq (fun _ =>
    ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)] at h
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, measureReal_def,
    ENNReal.toReal_ofReal (boundarySusceptibility_nonneg J β _)] using h

open Classical in
/-- A finite embedded-domain boundary expectation is bounded uniformly by the ambient
row cap and squared uniform susceptibility. -/
theorem integral_boundarySusceptibility_comp_sym2Map_le [Fintype V]
    {W : Type*} [Countable W] (f : V ↪ W) (J : Sym2 W → ℝ≥0) (β : ℝ≥0) (o : V)
    (R : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤) :
    (∫ ω, boundarySusceptibility (fun e => J (Sym2.map f e)) β
      (Set.toFinite (cluster ω o)).toFinset
      ∂law (intensityProfile (fun e => J (Sym2.map f e)) β)) ≤
        (R : ℝ) * (⨆ v, chi (intensityProfile J β) v).toReal ^ 2 := by
  let K := fun e => J (Sym2.map f e)
  have hχle : (⨆ v, chi (intensityProfile K β) v) ≤
      ⨆ v, chi (intensityProfile J β) v := by
    exact iSup_le fun v => (chi_le_of_embedding f
      (q := intensityProfile K β) (q' := intensityProfile J β) (fun _ _ => le_rfl) v).trans
        (le_iSup _ (f v))
  have heq := integral_finite_cluster_functional_eq_tsum (intensityProfile K β) o
    (fun C => boundarySusceptibility K β C) (boundarySusceptibility_nonneg K β)
  have hfun : (fun ω : Config V => if h : (cluster ω o).Finite then
      boundarySusceptibility K β h.toFinset else 0) =
      (fun ω => boundarySusceptibility K β (Set.toFinite (cluster ω o)).toFinset) := by
    funext ω
    rw [dite_eq_left (Set.toFinite _)]
  rw [hfun] at heq
  rw [heq]
  refine (tsum_lawReal_cluster_eq_mul_boundarySusceptibility_le K β o R
    (fun v => (rowSum_comp_sym2Map_le f J v).trans (hrow (f v)))
    (ne_top_of_le_ne_top hχ hχle)).trans ?_
  rw [sq, ← mul_assoc]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hχ hχle) R.coe_nonneg)
    (ENNReal.toReal_mono hχ ((le_iSup _ o).trans hχle)) ENNReal.toReal_nonneg
    (by positivity)

/-- Susceptibility on a restricted vertex domain is exactly the expected internal-cluster
volume under the ambient law. Infinite values are permitted. -/
theorem chi_preimage_subtype_eq_lintegral_localCluster [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (o : A) :
    chi (fun e => q (Sym2.map (Subtype.val : A → V) e)) o =
      ∫⁻ ω, ((localCluster ω A o).encard : ℝ≥0∞) ∂law q := by
  let f : A ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  rw [chi]
  change (∫⁻ ω : Config A, ((cluster ω o).encard : ℝ≥0∞)
    ∂law (fun e => q (Sym2.map f e))) = _
  rw [← law_map_preimage_sym2Map f q]
  have hm : Measurable (fun ω : Config A => ((cluster ω o).encard : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster o)
  rw [lintegral_map hm (measurable_preimage_sym2Map f)]
  apply lintegral_congr
  intro ω
  rw [← image_cluster_preimage_subtype_eq_localCluster ω A o,
    Subtype.val_injective.encard_image]
  rfl

open Classical in
/-- The actual finite-domain susceptibilities converge to the full susceptibility along
a vertex exhaustion, before any real conversion or finite-susceptibility assumption. -/
theorem tendsto_chi_preimage_subtype_of_exhaustion [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (S : ℕ → Finset V)
    (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (ho : ∀ n, o ∈ S n) :
    Tendsto (fun n => chi
      (fun e => q (Sym2.map (fun v : (S n : Set V) => (v : V)) e)) ⟨o, ho n⟩)
      atTop (𝓝 (chi q o)) := by
  have hS' : Monotone fun n => (S n : Set V) := fun _ _ h => hS h
  have hm : Monotone (fun n => ∫⁻ ω, ((localCluster ω (S n : Set V) o).encard : ℝ≥0∞)
      ∂law q) := by
    intro n m hnm
    exact lintegral_mono fun ω => ENat.toENNReal_le.mpr
      (Set.encard_le_encard (monotone_induce_cluster hS' ω o hnm))
  have h := tendsto_atTop_iSup hm
  rw [← chi_eq_iSup_lintegral_induce q hS' hcover o] at h
  convert h using 1
  funext n
  exact chi_preimage_subtype_eq_lintegral_localCluster q (S n : Set V) ⟨o, ho n⟩

open Classical in
/-- The actual expected boundary susceptibility is interval integrable under a finite
row cap and finite uniform susceptibility at the upper endpoint. -/
theorem intervalIntegrable_tsum_law_cluster_eq_mul_boundarySusceptibility [Countable V]
    (J : Sym2 V → ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    {a b : ℝ} (hab : a ≤ b)
    (hχ : (⨆ v, chi (intensityProfile J b.toNNReal) v) ≠ ⊤) :
    IntervalIntegrable (fun t => ∑' C : Finset V,
      (law (intensityProfile J t.toNNReal)).real {ω : Config V | cluster ω o = (C : Set V)} *
        boundarySusceptibility J t.toNNReal C) volume a b := by
  obtain ⟨T, hT, hcoverT⟩ := exists_finset_exhaustion (V := V)
  let S (n : ℕ) := insert o (T n)
  have hS : Monotone S := fun _ _ h => Finset.insert_subset_insert _ (hT h)
  have hcover : ∀ v, ∃ n, v ∈ S n := by
    intro v
    obtain ⟨n, hn⟩ := hcoverT v
    exact ⟨n, Finset.mem_insert_of_mem hn⟩
  have ho (n : ℕ) : o ∈ S n := Finset.mem_insert_self _ _
  let f (n : ℕ) : (S n : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let g (n : ℕ) (t : ℝ) : ℝ := ∫ ω : Config (S n : Set V),
    boundarySusceptibility (fun e => J (Sym2.map (f n) e)) t.toNNReal
      (Set.toFinite (cluster ω ⟨o, ho n⟩)).toFinset
    ∂law (intensityProfile (fun e => J (Sym2.map (f n) e)) t.toNNReal)
  let H (t : ℝ) : ℝ := ∑' C : Finset V,
    (law (intensityProfile J t.toNNReal)).real {ω : Config V | cluster ω o = (C : Set V)} *
      boundarySusceptibility J t.toNNReal C
  let M := (⨆ v, chi (intensityProfile J b.toNNReal) v).toReal
  have hχle (t : ℝ) (ht : t ≤ b) : (⨆ v, chi (intensityProfile J t.toNNReal) v) ≤
      ⨆ v, chi (intensityProfile J b.toNNReal) v := by
    exact iSup_le fun v => (chi_mono
      (fun e => intensityProfile_mono J (Real.toNNReal_le_toNNReal ht) e) v).trans (le_iSup _ v)
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun n => g n t) atTop (𝓝 (H t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact tendsto_integral_boundarySusceptibility_restrict J t.toNNReal o R hrow
      (ne_top_of_le_ne_top hχ (hχle t ht.2)) S hS hcover ho
  have hmeas : AEStronglyMeasurable H (volume.restrict (Ioc a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (continuous_integral_boundarySusceptibility_finite
        (fun e => J (Sym2.map (f n) e)) ⟨o, ho n⟩).aestronglyMeasurable) hlim
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖H t‖ ≤ (R : ℝ) * M ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnn : 0 ≤ H t := tsum_nonneg fun C =>
      mul_nonneg measureReal_nonneg (boundarySusceptibility_nonneg _ _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine (tsum_lawReal_cluster_eq_mul_boundarySusceptibility_le J t.toNNReal o R hrow
      (ne_top_of_le_ne_top hχ (hχle t ht.2))).trans ?_
    rw [sq, ← mul_assoc]
    gcongr
    · exact ENNReal.toReal_mono hχ (hχle t ht.2)
    · exact ENNReal.toReal_mono hχ ((le_iSup _ o).trans (hχle t ht.2))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (R : ℝ) * M ^ 2)
    volume a b).1.mono' hmeas hbound

open Classical in
/-- The actual susceptibility increment is the integral of the expected boundary
susceptibility. The finite-volume Russo identities pass to the limit under an actual
row cap and finite uniform susceptibility at the upper endpoint; no infinite-volume
derivative, critical-cluster, or independence premise is assumed. -/
theorem chi_sub_eq_integral_boundarySusceptibility [Countable V]
    (J : Sym2 V → ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hχ : (⨆ v, chi (intensityProfile J b.toNNReal) v) ≠ ⊤) :
    (chi (intensityProfile J b.toNNReal) o).toReal -
        (chi (intensityProfile J a.toNNReal) o).toReal =
      ∫ t in a..b, ∑' C : Finset V,
        (law (intensityProfile J t.toNNReal)).real
          {ω : Config V | cluster ω o = (C : Set V)} *
          boundarySusceptibility J t.toNNReal C := by
  obtain ⟨T, hT, hcoverT⟩ := exists_finset_exhaustion (V := V)
  let S (n : ℕ) := insert o (T n)
  have hS : Monotone S := fun _ _ h => Finset.insert_subset_insert _ (hT h)
  have hcover : ∀ v, ∃ n, v ∈ S n := by
    intro v
    obtain ⟨n, hn⟩ := hcoverT v
    exact ⟨n, Finset.mem_insert_of_mem hn⟩
  have ho (n : ℕ) : o ∈ S n := Finset.mem_insert_self _ _
  let f (n : ℕ) : (S n : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let K (n : ℕ) : Sym2 (S n : Set V) → ℝ≥0 := fun e => J (Sym2.map (f n) e)
  let g (n : ℕ) (t : ℝ) : ℝ := ∫ ω : Config (S n : Set V),
    boundarySusceptibility (K n) t.toNNReal (Set.toFinite (cluster ω ⟨o, ho n⟩)).toFinset
      ∂law (intensityProfile (K n) t.toNNReal)
  let H (t : ℝ) : ℝ := ∑' C : Finset V,
    (law (intensityProfile J t.toNNReal)).real {ω : Config V | cluster ω o = (C : Set V)} *
      boundarySusceptibility J t.toNNReal C
  let M := (⨆ v, chi (intensityProfile J b.toNNReal) v).toReal
  have hχle (t : ℝ) (ht : t ≤ b) : (⨆ v, chi (intensityProfile J t.toNNReal) v) ≤
      ⨆ v, chi (intensityProfile J b.toNNReal) v := by
    exact iSup_le fun v => (chi_mono
      (fun e => intensityProfile_mono J (Real.toNNReal_le_toNNReal ht) e) v).trans (le_iSup _ v)
  have hχt (t : ℝ) (ht : t ≤ b) : (⨆ v, chi (intensityProfile J t.toNNReal) v) ≠ ⊤ :=
    ne_top_of_le_ne_top hχ (hχle t ht)
  have hcont (n : ℕ) : Continuous (g n) :=
    continuous_integral_boundarySusceptibility_finite (K n) ⟨o, ho n⟩
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun n => g n t) atTop (𝓝 (H t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact tendsto_integral_boundarySusceptibility_restrict J t.toNNReal o R hrow
      (hχt t ht.2) S hS hcover ho
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖g n t‖ ≤ (R : ℝ) * M ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnn : 0 ≤ g n t := integral_nonneg fun _ => boundarySusceptibility_nonneg _ _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine (integral_boundarySusceptibility_comp_sym2Map_le (f n) J t.toNNReal
      ⟨o, ho n⟩ R hrow (hχt t ht.2)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hχ (hχle t ht.2)) 2)
      R.coe_nonneg
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc a b)) (fun _ : ℝ => (R : ℝ) * M ^ 2)
    (fun n => (hcont n).aestronglyMeasurable)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (R : ℝ) * M ^ 2)
      volume a b).1 hbound hlim
  have hDCT' : Tendsto (fun n => ∫ t in a..b, g n t) atTop (𝓝 (∫ t in a..b, H t)) := by
    simpa only [intervalIntegral.integral_of_le hab] using hDCT
  have hFTC (n : ℕ) : (∫ t in a..b, g n t) =
      (chi (intensityProfile (K n) b.toNNReal) ⟨o, ho n⟩).toReal -
        (chi (intensityProfile (K n) a.toNNReal) ⟨o, ho n⟩).toReal := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => (chi (intensityProfile (K n) t.toNNReal) ⟨o, ho n⟩).toReal)
      (fun t ht => ?_)
      ((hcont n).intervalIntegrable a b)
    have hat : a ≤ t := (show t ∈ Icc a b from by simpa only [uIcc_of_le hab] using ht).1
    exact hasDerivAt_toReal_chi_eq_integral_boundarySusceptibility (K n) ⟨o, ho n⟩
      (ha.trans_le hat)
  have hchiLim (t : ℝ) (ht : t ≤ b) :
      Tendsto (fun n => (chi (intensityProfile (K n) t.toNNReal) ⟨o, ho n⟩).toReal)
        atTop (𝓝 (chi (intensityProfile J t.toNNReal) o).toReal) := by
    exact (ENNReal.tendsto_toReal
      (ne_top_of_le_ne_top (hχt t ht) (le_iSup _ o))).comp
        (tendsto_chi_preimage_subtype_of_exhaustion (intensityProfile J t.toNNReal)
          o S hS hcover ho)
  have hends : Tendsto (fun n => ∫ t in a..b, g n t) atTop
      (𝓝 ((chi (intensityProfile J b.toNNReal) o).toReal -
        (chi (intensityProfile J a.toNNReal) o).toReal)) := by
    simp_rw [hFTC]
    exact (hchiLim b le_rfl).sub (hchiLim a hab)
  exact tendsto_nhds_unique hends hDCT'

end PercLib.Percolation.Bond
