/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The transitive finite-set criterion: root independence of the susceptibility, of the
infinite-cluster probability and of the threshold for transitive intensities, and the
regularity in the intensity of the boundary functional of a finite set. New proofs from
the transport, boundary-contraction and intensity theorems of this library and pinned
mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679's Weierstrass M-test. No upstream code
is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.BoundaryContraction
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.IntensityMonotone
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Probability.Transport.Reindexing
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # The transitive finite-set criterion

For a finite `S ∋ x`, `τ_S(x,u)` is the probability that `x` and `u` are joined inside `S`
and `Φ_q(x,S) = ∑_{u ∈ S} ∑'_{v ∉ S} τ_S(x,u) q s(u,v)`; both are written out. A kernel
`J` is transitive when `∀ x y, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e`.

* XONW / QXWF: under transitivity, `chi`, the probability of an infinite cluster and the
  root threshold do not depend on the root, and the root threshold equals the global one.
* `monotone_boundaryFlux_intensity` and `continuous_boundaryFlux_intensity`: for a fixed
  finite `S ∋ o`, `β ↦ Φ_{q_β}(o,S)` is monotone and, when the off-diagonal rows of `J`
  are finite, continuous on `ℝ≥0`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Root independence under transitivity (XONW / QXWF) -/

/-- An automorphism of the kernel preserves the law at every intensity. -/
theorem law_intensityProfile_map_eq (J : Sym2 V → ℝ≥0) (σ : V ≃ V)
    (hσ : ∀ e, J (Sym2.map σ e) = J e) (β : ℝ≥0) :
    (law (intensityProfile J β)).map (fun ω => Sym2.map σ '' ω) =
      law (intensityProfile J β) :=
  PercLib.Probability.prodBernoulli_map_image_sym2_invariant _ σ fun e =>
    Subtype.ext (by simp only [intensityProfile, hσ])

/-- **Root independence of the susceptibility.** Under transitivity the susceptibility does not
depend on the root. -/
theorem chi_eq_of_transitive [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (β : ℝ≥0)
    (x y : V) : chi (intensityProfile J β) x = chi (intensityProfile J β) y := by
  obtain ⟨σ, hσx, hσ⟩ := hT x y
  rw [← hσx]
  exact (chi_apply_eq_of_map_law_eq σ (law_intensityProfile_map_eq J σ hσ β) x).symm

/-- **Root independence of the percolation probability.** Under transitivity the probability of an
infinite cluster does not depend on the root. -/
theorem law_cluster_infinite_eq_of_transitive [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (β : ℝ≥0)
    (x y : V) :
    law (intensityProfile J β) {ω | (cluster ω x).Infinite} =
      law (intensityProfile J β) {ω | (cluster ω y).Infinite} := by
  obtain ⟨σ, hσx, hσ⟩ := hT x y
  rw [← hσx]
  exact (law_cluster_infinite_apply_eq_of_map_law_eq σ
    (law_intensityProfile_map_eq J σ hσ β) x).symm

/-- **Root independence of the threshold.** Under transitivity the root threshold does not depend on
the root. -/
theorem rootCriticalIntensity_eq_of_transitive [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (x y : V) :
    rootCriticalIntensity J x = rootCriticalIntensity J y := by
  unfold rootCriticalIntensity
  simp_rw [law_cluster_infinite_eq_of_transitive J hT _ x y]

/-- **Root and global thresholds agree.** Under transitivity the root threshold equals the global
threshold. No connectivity of the support of `J` is assumed: the event that some cluster is infinite
is a countable union of root events of equal probability. -/
theorem rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive [Countable V]
    (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (x : V) :
    rootCriticalIntensity J x = globalCriticalIntensity J := by
  unfold rootCriticalIntensity globalCriticalIntensity
  congr 1
  ext b
  constructor
  · rintro ⟨β, rfl, h⟩
    exact ⟨β, rfl, h.trans_le (measure_mono fun ω hω => ⟨x, hω⟩)⟩
  · rintro ⟨β, rfl, h⟩
    refine ⟨β, rfl, ?_⟩
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    have hU : {ω : Config V | ∃ y, (cluster ω y).Infinite} =
        ⋃ y, {ω | (cluster ω y).Infinite} := by
      ext ω; simp
    rw [hU, measure_iUnion_null fun y => by
      rw [← law_cluster_infinite_eq_of_transitive J hT β x y]; exact h0] at h
    exact lt_irrefl _ h

/-! ### Regularity of the boundary functional in the intensity -/

open Classical in
/-- **Regularity of `Φ`, monotonicity.** For a fixed finite `S`, the boundary functional
`β ↦ Φ_{q_β}(o,S)` is monotone. -/
theorem monotone_boundaryFlux_intensity [Countable V] (J : Sym2 V → ℝ≥0) (S : Finset V) (o : V) :
    Monotone fun β : ℝ≥0 => boundaryFlux (intensityProfile J β) S o := by
  intro β₁ β₂ h
  refine Finset.sum_le_sum fun u _ => ENNReal.tsum_le_tsum fun v => ?_
  split_ifs
  · exact le_rfl
  · exact mul_le_mul' (law_intensityProfile_mono (isUpperSet_localConn _ o u)
      (measurableSet_localConn _ o u) J h)
      (ENNReal.coe_le_coe.2 (intensityProfile_mono J h _))

/-- The profile depends continuously on the intensity, as a point of the product space. -/
theorem continuous_intensityProfile_pi (J : Sym2 V → ℝ≥0) :
    Continuous fun β : ℝ≥0 => intensityProfile J β :=
  continuous_pi fun e => (continuous_intensityProfile J e).subtype_mk _

/-- An internal connection probability is continuous in the intensity. -/
theorem continuous_law_localConn_intensity (J : Sym2 V → ℝ≥0) (S : Finset V) (x u : V) :
    Continuous fun β : ℝ≥0 => law (intensityProfile J β)
      (localConn (S : Set V) x u) :=
  (continuous_law_localConn S x u).comp (continuous_intensityProfile_pi J)

open Classical in
/-- The exterior row of `u` is continuous in the intensity when the off-diagonal row of `J`
at `u` is finite. -/
theorem continuous_exteriorRow_intensity (J : Sym2 V → ℝ≥0) (S : Finset V) {u : V}
    (huS : u ∈ S)
    (hrow : rowSum (fun e => (J e : ℝ≥0∞)) u < ∞) :
    Continuous fun β : ℝ≥0 => ∑' v, (if v ∈ S then 0 else
      (unitInterval.toNNReal (intensityProfile J β s(u, v)) : ℝ≥0∞)) := by
  classical
  -- The off-diagonal row of `J` at `u` is summable.
  set g : V → ℝ≥0 := fun v => if v = u then 0 else J s(u, v) with hg
  have hgs : Summable fun v => (g v : ℝ) := by
    refine NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hrow)
    refine tsum_congr fun v => ?_
    simp only [hg]
    split_ifs <;> simp
  -- The real exterior terms.
  set r : V → ℝ≥0 → ℝ := fun v β => if v ∈ S then 0 else 1 - Real.exp (-(β : ℝ) * J s(u, v))
    with hr
  have hr0 : ∀ v β, 0 ≤ r v β := fun v β => by
    simp only [hr]
    split_ifs
    · exact le_rfl
    · have : Real.exp (-(β : ℝ) * J s(u, v)) ≤ 1 :=
        Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 β.2) (J _).2)
      linarith
  have hrle : ∀ v β, r v β ≤ β * g v := fun v β => by
    simp only [hr, hg]
    split_ifs with h1 h2
    · simp
    · positivity
    · rename_i h2; exact absurd (h2 ▸ huS) h1
    · have := Real.add_one_le_exp (-(β : ℝ) * J s(u, v))
      linarith
  have hcont : ∀ v, Continuous (r v) := fun v => by
    simp only [hr]
    split_ifs
    · exact continuous_const
    · fun_prop
  -- Continuity of the real sum on each `Iio b`, by the Weierstrass M-test.
  have hon : ∀ b : ℝ≥0, ContinuousOn (fun β => ∑' v, r v β) (Iio b) := fun b =>
    continuousOn_tsum (fun v => (hcont v).continuousOn) (hgs.mul_left (b : ℝ))
      fun v β hβ => by
        rw [Real.norm_of_nonneg (hr0 v β)]
        exact (hrle v β).trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hβ.le)
          (g v).2)
  have hreal : Continuous fun β => ∑' v, r v β :=
    continuous_iff_continuousAt.2 fun β =>
      (hon (β + 1)).continuousAt (Iio_mem_nhds (lt_add_one β))
  -- Identify the `ℝ≥0∞` sum with `ofReal` of the real sum.
  have heq : (fun β : ℝ≥0 => ∑' v, (if v ∈ S then 0 else
      (unitInterval.toNNReal (intensityProfile J β s(u, v)) : ℝ≥0∞))) =
      fun β => ENNReal.ofReal (∑' v, r v β) := by
    funext β
    have hs : Summable fun v => r v β :=
      Summable.of_nonneg_of_le (hr0 · β) (hrle · β) (hgs.mul_left (β : ℝ))
    rw [ENNReal.ofReal_tsum_of_nonneg (hr0 · β) hs]
    refine tsum_congr fun v => ?_
    simp only [hr]
    split_ifs
    · simp
    · rw [← ENNReal.ofReal_coe_nnreal]
      rfl
  rw [heq]
  exact ENNReal.continuous_ofReal.comp hreal

open Classical in
/-- **Regularity of `Φ`, continuity.** If the off-diagonal rows of `J` are finite, then
for a fixed finite `S` the boundary functional `β ↦ Φ_{q_β}(o,S)` is continuous on `ℝ≥0`. -/
theorem continuous_boundaryFlux_intensity (J : Sym2 V → ℝ≥0)
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ∞) (S : Finset V)
    (o : V) :
    Continuous fun β : ℝ≥0 => boundaryFlux (intensityProfile J β) S o := by
  refine continuous_finsetSum _ fun u hu => ?_
  have hfac : (fun β : ℝ≥0 => ∑' v, (if v ∈ S then 0 else
      law (intensityProfile J β) (localConn (S : Set V) o u) *
      (unitInterval.toNNReal (intensityProfile J β s(u, v)) : ℝ≥0∞))) =
      fun β => law (intensityProfile J β) (localConn (S : Set V) o u) *
        ∑' v, (if v ∈ S then 0 else
          (unitInterval.toNNReal (intensityProfile J β s(u, v)) : ℝ≥0∞)) := by
    funext β
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun v => ?_
    split_ifs <;> simp
  rw [hfac]
  have hτ := continuous_law_localConn_intensity J S o u
  have hR := continuous_exteriorRow_intensity J S hu (hrow u)
  refine continuous_iff_continuousAt.2 fun β => ?_
  refine ENNReal.Tendsto.mul hτ.continuousAt (Or.inr ?_) hR.continuousAt (Or.inr ?_)
  · -- The exterior row is finite.
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := β))
      (hrow u)))
    rw [rowSum_def, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun v => ?_
    split_ifs with h1 h2
    · exact zero_le
    · exact zero_le
    · rename_i h2; exact absurd (h2 ▸ hu) h1
    · rw [← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β _)
  · exact (prob_le_one.trans_lt ENNReal.one_lt_top).ne

/-! ### Transport of the boundary functional -/

/-- Internal connections in the image of a domain pull back along a vertex bijection. -/
theorem localConn_of_image (σ : V ≃ V) (ω : Config V) {S T : Set V}
    (hST : ∀ v, v ∈ T → σ.symm v ∈ S) {a b : V}
    (h : Sym2.map σ '' ω ∈ localConn T (σ a) (σ b)) :
    ω ∈ localConn S a b := by
  obtain ⟨ha, hb, r⟩ := h
  let ψ : (openGraph (Sym2.map σ '' ω)).induce T →g (openGraph ω).induce S :=
    { toFun := fun v => ⟨σ.symm v, hST v v.2⟩
      map_rel' := fun {v w} hvw => by
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] at hvw ⊢
        have h := openGraph_image_adj_iff σ ω (σ.symm v) (σ.symm w)
        simp only [Equiv.apply_symm_apply] at h
        exact h.1 hvw }
  have ea : ψ ⟨σ a, ha⟩ = ⟨a, by simpa using hST _ ha⟩ := Subtype.ext (σ.symm_apply_apply a)
  have eb : ψ ⟨σ b, hb⟩ = ⟨b, by simpa using hST _ hb⟩ := Subtype.ext (σ.symm_apply_apply b)
  have r' := r.map ψ
  rw [ea, eb] at r'
  exact ⟨_, _, r'⟩

/-- Under an automorphism of the kernel, the internal connection probability of an image
domain is at most that of the domain. -/
theorem law_localConn_image_le [Countable V] (J : Sym2 V → ℝ≥0) (σ : V ≃ V)
    (hσ : ∀ e, J (Sym2.map σ e) = J e) (β : ℝ≥0) {S T : Set V}
    (hST : ∀ v, v ∈ T → σ.symm v ∈ S) (a b : V) :
    law (intensityProfile J β) (localConn T (σ a) (σ b)) ≤
      law (intensityProfile J β) (localConn S a b) := by
  conv_lhs => rw [← law_intensityProfile_map_eq J σ hσ β, map_image_sym2Map_apply]
  exact measure_mono fun ω hω => localConn_of_image σ ω hST hω

open Classical in
/-- Under an automorphism `σ` of the kernel, the boundary functional at `(σ o, σ S)` is at
most the boundary functional at `(o, S)`. -/
theorem boundaryFlux_map_le [Countable V] (J : Sym2 V → ℝ≥0) (σ : V ≃ V)
    (hσ : ∀ e, J (Sym2.map σ e) = J e) (β : ℝ≥0) (S : Finset V) (o : V) :
    boundaryFlux (intensityProfile J β) (S.map σ.toEmbedding) (σ o) ≤
    boundaryFlux (intensityProfile J β) S o := by
  rw [boundaryFlux_def, boundaryFlux_def, Finset.sum_map]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← σ.tsum_eq]
  refine ENNReal.tsum_le_tsum fun v => ?_
  have hv' : σ v ∈ S.map σ.toEmbedding ↔ v ∈ S := by simp
  by_cases hv : v ∈ S
  · rw [ite_eq_left (hv'.2 hv), ite_eq_left hv]
  · rw [ite_eq_right (mt hv'.1 hv), ite_eq_right hv]
    have hq : intensityProfile J β s(σ.toEmbedding u, σ v) = intensityProfile J β s(u, v) := by
      rw [Equiv.coe_toEmbedding, ← Sym2.map_mk]
      exact Subtype.ext (by simp only [intensityProfile, hσ])
    rw [hq]
    refine mul_le_mul_left ?_ _
    exact law_localConn_image_le J σ hσ β (S := (S : Set V))
      (T := ((S.map σ.toEmbedding : Finset V) : Set V))
      (fun w hw => by simpa using hw) o u

/-! ### Contraction persists (item 3) -/

open Classical in
/-- **Contraction persists.** Under transitivity and finite off-diagonal rows, if
`Φ_{q_{β₀}}(o,S) < 1` for one finite `S ∋ o`, then there is `ε > 0` with
`chi q_{β₀+ε} x < ⊤` for every `x`. -/
theorem exists_chi_lt_top_of_boundaryFlux_lt_one [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ∞)
    (S : Finset V) {o : V} (hoS : o ∈ S) (β₀ : ℝ≥0)
    (hΦ : boundaryFlux (intensityProfile J β₀) S o < 1) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ x, chi (intensityProfile J (β₀ + ε)) x < ⊤ := by
  set Φ : ℝ≥0 → ℝ≥0∞ := fun β => boundaryFlux (intensityProfile J β) S o
  have hc : Continuous Φ := continuous_boundaryFlux_intensity J hrow S o
  -- Some `ε > 0` keeps `Φ` below one.
  have ht : Tendsto (fun ε : ℝ≥0 => Φ (β₀ + ε)) (𝓝[>] 0) (𝓝 (Φ β₀)) := by
    have : Tendsto (fun ε : ℝ≥0 => β₀ + ε) (𝓝 0) (𝓝 β₀) := by
      simpa using (tendsto_const_nhds (x := β₀)).add (tendsto_id (x := 𝓝 (0 : ℝ≥0)))
    exact ((hc.tendsto β₀).comp this).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hε1, hε0⟩ :=
    ((ht.eventually (gt_mem_nhds hΦ)).and self_mem_nhdsWithin).exists
  refine ⟨ε, hε0, fun x => ?_⟩
  -- Transport `S` to every root.
  let σ : V → V ≃ V := fun x => Classical.choose (hT o x)
  have hσx : ∀ x, σ x o = x := fun x => (Classical.choose_spec (hT o x)).1
  have hσJ : ∀ x e, J (Sym2.map (σ x) e) = J e := fun x => (Classical.choose_spec (hT o x)).2
  let Sx : V → Finset V := fun x => S.map (σ x).toEmbedding
  have hSx : ∀ x, x ∈ Sx x := fun x => by
    simp only [Sx, Finset.mem_map_equiv]
    have h : (σ x).symm x = o := by rw [Equiv.symm_apply_eq]; exact (hσx x).symm
    rw [h]
    exact hoS
  have hcard : ∀ x, (Sx x).card ≤ S.card := fun x => by simp [Sx]
  have hΦx : ∀ x, boundaryFlux (intensityProfile J (β₀ + ε)) (Sx x) x ≤
      Φ (β₀ + ε) := fun x => by
    have h := boundaryFlux_map_le J (σ x) (hσJ x) (β₀ + ε) S o
    simp only [hσx x] at h
    exact h
  have hchi := chi_le_of_boundary_contraction_card (intensityProfile J (β₀ + ε)) Sx hSx hcard
    hε1 hΦx x
  refine hchi.trans_lt (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ?_)
  exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hε1)

open Classical in
/-- **Contraction persists, threshold form.** Under the same hypotheses,
`β₀ < rootCriticalIntensity J o`. -/
theorem lt_rootCriticalIntensity_of_boundaryFlux_lt_one [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ∞)
    (S : Finset V) {o : V} (hoS : o ∈ S) (β₀ : ℝ≥0)
    (hΦ : boundaryFlux (intensityProfile J β₀) S o < 1) :
    (β₀ : ℝ≥0∞) < rootCriticalIntensity J o := by
  obtain ⟨ε, hε0, hchi⟩ := exists_chi_lt_top_of_boundaryFlux_lt_one J hT hrow S hoS β₀ hΦ
  have h0 := law_cluster_infinite_eq_zero_of_chi_ne_top _ o (hchi o).ne
  have hle : ((β₀ + ε : ℝ≥0) : ℝ≥0∞) ≤ rootCriticalIntensity J o := by
    unfold rootCriticalIntensity
    refine le_sInf ?_
    rintro b ⟨β, rfl, hpos⟩
    by_contra hlt
    rw [not_le, ENNReal.coe_lt_coe] at hlt
    have := law_intensityProfile_mono (isUpperSet_cluster_infinite o)
      (measurableSet_cluster_infinite o) J hlt.le
    rw [h0] at this
    exact (lt_irrefl _ (hpos.trans_le this))
  exact lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lt_add_of_pos_right β₀ hε0)) hle

/-! ### R84Z (item 4) -/

open Classical in
/-- **The boundary flux at the threshold.** Under transitivity and finite off-diagonal rows, if the
root threshold `β_c` is finite then for every finite `S ∋ o`:
`1 ≤ Φ_{q_{β_c}}(o,S) ≤ β_c ∑_{u ∈ S} τ_{S,β_c}(o,u) ∑'_{v ∉ S} J s(u,v)`. -/
theorem one_le_boundaryFlux_at_rootCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ∞) {o : V}
    (hc : rootCriticalIntensity J o < ⊤) (S : Finset V) (hoS : o ∈ S) :
    1 ≤ boundaryFlux (intensityProfile J (rootCriticalIntensity J o).toNNReal) S o ∧
    boundaryFlux (intensityProfile J (rootCriticalIntensity J o).toNNReal) S o ≤
    rootCriticalIntensity J o * ∑ u ∈ S,
      law (intensityProfile J (rootCriticalIntensity J o).toNNReal)
        (localConn (S : Set V) o u) *
      ∑' v, (if v ∈ S then 0 else (J s(u, v) : ℝ≥0∞)) := by
  set βc := (rootCriticalIntensity J o).toNNReal with hβc
  have hβc' : (βc : ℝ≥0∞) = rootCriticalIntensity J o := ENNReal.coe_toNNReal hc.ne
  constructor
  · by_contra h
    rw [not_le] at h
    have := lt_rootCriticalIntensity_of_boundaryFlux_lt_one J hT hrow S hoS βc h
    rw [hβc'] at this
    exact lt_irrefl _ this
  · rw [← hβc', Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← mul_assoc, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv : v ∈ S
    · simp [hv]
    · rw [ite_eq_right hv, ite_eq_right hv]
      calc _ ≤ law (intensityProfile J βc)
              (localConn (S : Set V) o u) *
              ((βc : ℝ≥0∞) * (J s(u, v) : ℝ≥0∞)) := by
            refine mul_le_mul' le_rfl ?_
            rw [← ENNReal.coe_mul]
            exact ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J βc _)
        _ = _ := by ring

/-! ### Non-vacuity witnesses -/

/-- The constant kernel on `ZMod 2` is transitive, by the translations `σ = (· + c)`. -/
theorem transitive_const_zmod_two :
    ∀ x y : ZMod 2, ∃ σ : ZMod 2 ≃ ZMod 2, σ x = y ∧
      ∀ e, (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) (Sym2.map σ e) = (fun _ => 1) e :=
  fun x y => ⟨Equiv.addRight (y - x), by simp, fun _ => rfl⟩

/-- The zero kernel is transitive on any type, by transpositions. -/
theorem transitive_zero {W : Type*} [DecidableEq W] :
    ∀ x y : W, ∃ σ : W ≃ W, σ x = y ∧
      ∀ e, (fun _ : Sym2 W => (0 : ℝ≥0)) (Sym2.map σ e) = (fun _ => 0) e :=
  fun x y => ⟨Equiv.swap x y, Equiv.swap_apply_left x y, fun _ => rfl⟩

open Classical in
/-- On `ZMod 2` with the constant kernel: root independence, root = global threshold, and
continuity of `Φ` for `S = {0}` (the rows are finite). -/
example (β : ℝ≥0) :
    chi (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) β) 0 =
        chi (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) β) 1 ∧
      rootCriticalIntensity (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) 0 =
        globalCriticalIntensity (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) ∧
      Continuous fun β : ℝ≥0 => ∑ u ∈ ({0} : Finset (ZMod 2)), ∑' v, (if v ∈ ({0} : Finset _)
        then 0 else
        law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) β)
          (localConn (({0} : Finset (ZMod 2)) : Set (ZMod 2)) 0 u) *
        (unitInterval.toNNReal (intensityProfile (fun _ => (1 : ℝ≥0)) β s(u, v)) : ℝ≥0∞)) :=
  ⟨chi_eq_of_transitive _ transitive_const_zmod_two β 0 1,
    rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive _ transitive_const_zmod_two 0,
    by
      have h := continuous_boundaryFlux_intensity (V := ZMod 2) (fun _ => 1) (fun u => by
        rw [rowSum_def, tsum_fintype]
        exact ENNReal.sum_lt_top.2 fun _ _ => by split_ifs <;> simp) {0} 0
      simp only [boundaryFlux_def] at h
      convert h⟩

open Classical in
/-- The zero kernel with `S = {o}`: `Φ = 0 < 1`, so the susceptibility is finite just above `β₀ = 1`
and `1 < rootCriticalIntensity` (in fact it is `⊤`, and
`one_le_boundaryFlux_at_rootCriticalIntensity` is vacuous). -/
example (o : ZMod 2) :
    (∃ ε : ℝ≥0, 0 < ε ∧ ∀ x, chi (intensityProfile (fun _ : Sym2 (ZMod 2) => (0 : ℝ≥0))
      (1 + ε)) x < ⊤) ∧
      ((1 : ℝ≥0) : ℝ≥0∞) < rootCriticalIntensity (fun _ : Sym2 (ZMod 2) => (0 : ℝ≥0)) o := by
  have hrow : ∀ u : ZMod 2,
      rowSum (fun e => ((fun _ : Sym2 (ZMod 2) => (0 : ℝ≥0)) e : ℝ≥0∞)) u < ∞ :=
    fun u => by simp
  have hΦ : ∑ u ∈ ({o} : Finset (ZMod 2)), ∑' v, (if v ∈ ({o} : Finset (ZMod 2)) then 0 else
      law (intensityProfile (fun _ : Sym2 (ZMod 2) => (0 : ℝ≥0)) 1)
        (localConn (({o} : Finset (ZMod 2)) : Set (ZMod 2)) o u) *
      (unitInterval.toNNReal (intensityProfile (fun _ => (0 : ℝ≥0)) 1 s(u, v)) : ℝ≥0∞)) < 1 := by
    have hz : ∀ e : Sym2 (ZMod 2),
        intensityProfile (fun _ : Sym2 (ZMod 2) => (0 : ℝ≥0)) 1 e = 0 :=
      fun e => intensityProfile_eq_zero_of_eq_zero _ rfl 1
    simp [hz]
  exact ⟨exists_chi_lt_top_of_boundaryFlux_lt_one _ transitive_zero (by convert hrow) {o}
      (Finset.mem_singleton_self o) 1 (by rw [boundaryFlux_def]; convert hΦ),
    lt_rootCriticalIntensity_of_boundaryFlux_lt_one _ transitive_zero (by convert hrow) {o}
      (Finset.mem_singleton_self o) 1 (by rw [boundaryFlux_def]; convert hΦ)⟩

end PercLib.Percolation.Bond
