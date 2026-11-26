/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: sharpness of the phase transition for transitive summable
kernels, assembled from the finite-set criterion, the escape-probability derivative and the
supercritical density bound of this library. No upstream code is copied, no definition is added and
no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.WiredDerivativeFormula
public import PercLib.Percolation.Bond.SupercriticalDensity
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Models.FreeGroupTree

/-! # Sharpness for transitive summable kernels

Let `V` be countable, `J : Sym2 V → ℝ≥0` transitive
(`∀ x y, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e`) with summable rows, and
`q_β = intensityProfile J β`. For a finite `S ∋ o` write
`Φ_β(o,S) = ∑_{u ∈ S} ∑'_{v ∉ S} τ_{S,β}(o,u) q_β(u,v)` (in the spelling of
`lt_rootCriticalIntensity_of_boundaryFlux_lt_one`) and
`t = sup {β | ∃ S ∋ o finite, Φ_β(o,S) < 1}` in `ℝ≥0∞`.

* `chi_lt_top_of_lt_rootCriticalIntensity` (item 1): `β < β_c ⇒ χ(q_β, o) < ⊤`;
  `chi_lt_top_of_lt_rootCriticalIntensity'` gives it at every vertex.
* `rootCriticalIntensity_eq_sSup_boundaryFlux_lt_one` and
  `rootCriticalIntensity_eq_sSup_chi_lt_top` (item 2): `β_c = t = sup {β | χ(q_β, o) < ⊤}`;
  `globalCriticalIntensity_eq_sSup_boundaryFlux_lt_one` and
  `globalCriticalIntensity_eq_sSup_chi_lt_top` add the global threshold.
* `one_sub_div_le_law_cluster_infinite` (item 3, L0TE): for `β > β_c`,
  `P_β(|K_o| = ∞) ≥ 1 - β_c/β` in `ℝ≥0∞`.

Route: for `β > t` every `Φ_β(o,T) ≥ 1`, so the escape derivative of
`WiredDerivativeFormula.lean` satisfies `f' ≥ (1 - f)/β`, and `SupercriticalDensity.lean`
gives `β_c ≤ t` and the density bound. Conversely a set with `Φ_β(o,S) < 1` gives
`β < β_c` and finite `χ` slightly above `β` (`FiniteSetCriterion.lean`).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Conversions -/

/-- The cluster of `o` leaves `Λ` exactly when `o` is joined to a vertex outside `Λ`. -/
theorem setOf_not_cluster_subset_eq_iUnion_conn (Λ : Set V) (o : V) :
    {ω : Config V | ¬ cluster ω o ⊆ Λ} = ⋃ y ∈ Λᶜ, conn o y := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, exists_prop, Set.not_subset]
  exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h2, h1⟩ => ⟨y, h1, h2⟩⟩

/-- Summable real rows give finite off-diagonal rows in `ℝ≥0∞`. -/
theorem offDiag_rowSum_lt_top_of_summable (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (u : V) :
    rowSum (fun e => (J e : ℝ≥0∞)) u < ∞ := by
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun v => ?_)
    (ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 (hJ u))).lt_top
  split_ifs <;> simp

open Classical in
/-- With summable rows, the boundary functional in `ℝ≥0∞` is the `ENNReal.ofReal` of its
real form, the form used by `deriv_law_escape_ge`. -/
theorem boundaryFlux_eq_ofReal (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (β : ℝ≥0) (T : Finset V) (o : V) :
    boundaryFlux (intensityProfile J β) T o =
    ENNReal.ofReal (∑ u ∈ T, (law (intensityProfile J β)).real
          (localConn (T : Set V) o u) *
        ∑' v, if v ∈ T then 0 else (intensityProfile J β s(u, v) : ℝ)) := by
  have hnn : ∀ u v, 0 ≤ if v ∈ T then (0 : ℝ) else (intensityProfile J β s(u, v) : ℝ) :=
    fun u v => by split_ifs <;> simp [unitInterval.nonneg]
  rw [ENNReal.ofReal_sum_of_nonneg fun u _ =>
    mul_nonneg measureReal_nonneg (tsum_nonneg (hnn u))]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hs : Summable fun v => if v ∈ T then (0 : ℝ) else (intensityProfile J β s(u, v) : ℝ) := by
    refine Summable.of_nonneg_of_le (hnn u) (fun v => ?_) ((hJ u).mul_left (β : ℝ))
    split_ifs
    · positivity
    · have := NNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β s(u, v))
      simpa using this
  rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal (measure_ne_top _ _),
    ENNReal.ofReal_tsum_of_nonneg (hnn u) hs, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  split_ifs
  · simp
  · congr 1
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg unitInterval.nonneg']
    rfl

/-! ### The differential inequality above the flux threshold -/

open Classical in
/-- If `Φ_β(o,T) ≥ 1` for every `β > t` and every finite `T ∋ o`, then on `(t, ∞)` every
escape probability `f_Λ` has a derivative with `f_Λ' ≥ (1 - f_Λ)/β`, in the form taken by
`law_cluster_infinite_ge_of_escape_deriv`. -/
theorem escape_deriv_of_one_le_boundaryFlux [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) {t : ℝ} (ht : 0 ≤ t)
    (hΦ : ∀ β : ℝ≥0, t < β → ∀ T : Finset V, o ∈ T →
      1 ≤ boundaryFlux (intensityProfile J β) T o) :
    ∀ Λ : Finset V, o ∈ Λ → ∀ s, t < s →
      HasDerivAt (fun r : ℝ =>
        (law (intensityProfile J r.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal)
        (deriv (fun r : ℝ => (law (intensityProfile J r.toNNReal)).real
          {ω | ¬ cluster ω o ⊆ Λ}) s) s ∧
      (1 - (law (intensityProfile J s.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal) / s ≤
        deriv (fun r : ℝ => (law (intensityProfile J r.toNNReal)).real
          {ω | ¬ cluster ω o ⊆ Λ}) s := by
  intro Λ hoΛ s hs
  have hs0 : 0 < s := ht.trans_lt hs
  have he : ∀ r : ℝ, (law (intensityProfile J r.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal
      = (law (intensityProfile J r.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ} := fun r => by
    rw [setOf_not_cluster_subset_eq_iUnion_conn]
    rfl
  simp only [he]
  refine ⟨(hasDerivAt_law_escape J hJ Λ hoΛ hs0).differentiableAt.hasDerivAt, ?_⟩
  refine le_trans ?_ (deriv_law_escape_ge J hJ Λ hoΛ hs0)
  have hf : 0 ≤ (1 - (law (intensityProfile J s.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ}) / s :=
    div_nonneg (sub_nonneg.2 measureReal_le_one) hs0.le
  refine le_mul_of_one_le_right hf ?_
  refine (Finset.le_inf'_iff _ _).2 fun T hT => ?_
  have hoT : o ∈ T := (Finset.mem_filter.1 hT).2
  have h1 := hΦ s.toNNReal (by rwa [Real.coe_toNNReal _ hs0.le]) T hoT
  rw [boundaryFlux_eq_ofReal J hJ, ENNReal.one_le_ofReal] at h1
  exact h1

/-! ### The two inequalities between `β_c` and the flux threshold -/

open Classical in
/-- If `Φ_β(o,S) < 1` for some finite `S ∋ o`, then `β < β_c`; so the flux threshold is at
most `β_c`. -/
theorem sSup_boundaryFlux_lt_one_le_rootCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    sSup ((↑) '' {β : ℝ≥0 | ∃ S : Finset V, o ∈ S ∧
      boundaryFlux (intensityProfile J β) S o < 1}) ≤
      rootCriticalIntensity J o := by
  refine sSup_le ?_
  rintro _ ⟨β, ⟨S, hoS, hΦ⟩, rfl⟩
  exact (lt_rootCriticalIntensity_of_boundaryFlux_lt_one J hT
    (offDiag_rowSum_lt_top_of_summable J hJ) S hoS β hΦ).le

open Classical in
/-- **`β_c ≤ t`.** Above the flux threshold every `Φ_β(o,T) ≥ 1`, the escape probabilities
satisfy `f' ≥ (1 - f)/β`, and the cluster of `o` is infinite with positive probability. -/
theorem rootCriticalIntensity_le_sSup_boundaryFlux_lt_one [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    rootCriticalIntensity J o ≤
      sSup ((↑) '' {β : ℝ≥0 | ∃ S : Finset V, o ∈ S ∧
        boundaryFlux (intensityProfile J β) S o < 1}) := by
  set t : ℝ≥0∞ := sSup ((↑) '' {β : ℝ≥0 | ∃ S : Finset V, o ∈ S ∧
        boundaryFlux (intensityProfile J β) S o < 1}) with ht
  rcases eq_or_ne t ⊤ with htop | htop
  · rw [htop]
    exact le_top
  have hle := rootCriticalIntensity_le_of_escape_deriv J o ENNReal.toReal_nonneg _
    (escape_deriv_of_one_le_boundaryFlux J hJ o ENNReal.toReal_nonneg fun β hβ T hoT => by
      by_contra h
      rw [not_le] at h
      have hmem : (β : ℝ≥0∞) ≤ t := le_sSup ⟨β, ⟨T, hoT, h⟩, rfl⟩
      have := ENNReal.toReal_mono htop hmem
      rw [ENNReal.coe_toReal] at this
      exact absurd hβ (not_lt.2 this))
  rwa [ENNReal.ofReal_toReal htop] at hle

/-! ### Items 1 to 3 -/

open Classical in
/-- **Item 2, the flux threshold.** Under transitivity and summable rows,
`β_c = sup {β | ∃ S ∋ o finite, Φ_β(o,S) < 1}`. -/
theorem rootCriticalIntensity_eq_sSup_boundaryFlux_lt_one [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    rootCriticalIntensity J o =
      sSup ((↑) '' {β : ℝ≥0 | ∃ S : Finset V, o ∈ S ∧
        boundaryFlux (intensityProfile J β) S o < 1}) :=
  le_antisymm (rootCriticalIntensity_le_sSup_boundaryFlux_lt_one J hJ o)
    (sSup_boundaryFlux_lt_one_le_rootCriticalIntensity J hT hJ o)

/-- **Sharpness (item 1).** Under transitivity and summable rows, the susceptibility is
finite at every intensity below the threshold. -/
theorem chi_lt_top_of_lt_rootCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) {o : V} {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < rootCriticalIntensity J o) :
    chi (intensityProfile J β) o < ⊤ := by
  rw [rootCriticalIntensity_eq_sSup_boundaryFlux_lt_one J hT hJ o, lt_sSup_iff] at hβ
  obtain ⟨_, ⟨β', ⟨S, hoS, hΦ⟩, rfl⟩, hlt⟩ := hβ
  obtain ⟨ε, -, hchi⟩ := exists_chi_lt_top_of_boundaryFlux_lt_one J hT
    (offDiag_rowSum_lt_top_of_summable J hJ) S hoS β' hΦ
  have hle : β ≤ β' + ε := (ENNReal.coe_lt_coe.1 hlt).le.trans le_self_add
  exact (chi_mono (fun e => intensityProfile_mono J hle e) o).trans_lt (hchi o)

/-- **Sharpness at every vertex.** -/
theorem chi_lt_top_of_lt_rootCriticalIntensity' [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) {o : V} {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < rootCriticalIntensity J o) (x : V) :
    chi (intensityProfile J β) x < ⊤ := by
  rw [chi_eq_of_transitive J hT β x o]
  exact chi_lt_top_of_lt_rootCriticalIntensity J hT hJ hβ

/-- Finite susceptibility at `β` gives `β ≤ β_c`. -/
theorem le_rootCriticalIntensity_of_chi_ne_top [Countable V] (J : Sym2 V → ℝ≥0) {o : V}
    {β : ℝ≥0} (h : chi (intensityProfile J β) o ≠ ⊤) :
    (β : ℝ≥0∞) ≤ rootCriticalIntensity J o := by
  have h0 := law_cluster_infinite_eq_zero_of_chi_ne_top _ o h
  refine le_sInf ?_
  rintro b ⟨β', rfl, hpos⟩
  by_contra hlt
  rw [not_le, ENNReal.coe_lt_coe] at hlt
  have := law_intensityProfile_mono (isUpperSet_cluster_infinite o)
    (measurableSet_cluster_infinite o) J hlt.le
  rw [h0] at this
  exact lt_irrefl _ (hpos.trans_le this)

/-- **Item 2, the susceptibility threshold.** Under transitivity and summable rows,
`β_c = sup {β | χ(q_β, o) < ⊤}`. -/
theorem rootCriticalIntensity_eq_sSup_chi_lt_top [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    rootCriticalIntensity J o =
      sSup ((↑) '' {β : ℝ≥0 | chi (intensityProfile J β) o < ⊤}) := by
  refine le_antisymm (ENNReal.le_of_forall_nnreal_lt fun r hr => ?_) (sSup_le ?_)
  · exact le_sSup ⟨r, chi_lt_top_of_lt_rootCriticalIntensity J hT hJ hr, rfl⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact le_rootCriticalIntensity_of_chi_ne_top J hβ.ne

open Classical in
/-- **Item 2, global form.** The global threshold equals the flux threshold. -/
theorem globalCriticalIntensity_eq_sSup_boundaryFlux_lt_one [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    globalCriticalIntensity J =
      sSup ((↑) '' {β : ℝ≥0 | ∃ S : Finset V, o ∈ S ∧
        boundaryFlux (intensityProfile J β) S o < 1}) := by
  rw [← rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive J hT o]
  exact rootCriticalIntensity_eq_sSup_boundaryFlux_lt_one J hT hJ o

/-- **Item 2, global form.** The global threshold equals the susceptibility threshold. -/
theorem globalCriticalIntensity_eq_sSup_chi_lt_top [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    globalCriticalIntensity J =
      sSup ((↑) '' {β : ℝ≥0 | chi (intensityProfile J β) o < ⊤}) := by
  rw [← rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive J hT o]
  exact rootCriticalIntensity_eq_sSup_chi_lt_top J hT hJ o

open Classical in
/-- At or above `β_c` every boundary functional is at least one. -/
theorem one_le_boundaryFlux_of_rootCriticalIntensity_le [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) {o : V} {β : ℝ≥0}
    (hβ : rootCriticalIntensity J o ≤ β) (T : Finset V) (hoT : o ∈ T) :
    1 ≤ boundaryFlux (intensityProfile J β) T o := by
  by_contra h
  rw [not_le] at h
  exact absurd hβ (not_le.2 (lt_rootCriticalIntensity_of_boundaryFlux_lt_one J hT
    (offDiag_rowSum_lt_top_of_summable J hJ) T hoT β h))

/-- **Mean-field lower bound (item 3).** Under transitivity and summable rows, for
every `β > β_c`, `P_β(|K_o| = ∞) ≥ 1 - β_c/β`. (The hypothesis `β_c < β` forces
`β_c < ⊤`.) -/
theorem one_sub_div_le_law_cluster_infinite [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) {o : V} {β : ℝ≥0}
    (hβ : rootCriticalIntensity J o < β) :
    1 - rootCriticalIntensity J o / β ≤
      law (intensityProfile J β) {ω | (cluster ω o).Infinite} := by
  have hc : rootCriticalIntensity J o ≠ ⊤ := ne_top_of_lt hβ
  have hβ' : (rootCriticalIntensity J o).toReal < β := by
    have := ENNReal.toReal_strict_mono ENNReal.coe_ne_top hβ
    rwa [ENNReal.coe_toReal] at this
  have hβ0 : 0 < (β : ℝ) := ENNReal.toReal_nonneg.trans_lt hβ'
  have h := law_cluster_infinite_ge_of_escape_deriv J o ENNReal.toReal_nonneg _
    (escape_deriv_of_one_le_boundaryFlux J hJ o ENNReal.toReal_nonneg fun β' hβ'' T hoT =>
      one_le_boundaryFlux_of_rootCriticalIntensity_le J hT hJ (by
        rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hβ''.le) T hoT) β hβ'
  rwa [ENNReal.ofReal_sub _ (div_nonneg ENNReal.toReal_nonneg hβ0.le), ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos hβ0, ENNReal.ofReal_toReal hc, ENNReal.ofReal_coe_nnreal] at h

/-! ### Non-vacuity witnesses -/

/-- The zero kernel on `ℤ`: transitive with summable rows, `β_c = ⊤`, so item 1 holds at every
`β`; item 3 is vacuous there. -/
example (β : ℝ≥0) : chi (intensityProfile (fun _ : Sym2 ℤ => (0 : ℝ≥0)) β) 0 < ⊤ :=
  chi_lt_top_of_lt_rootCriticalIntensity _ transitive_zero (fun _ => by simp) (by
    rw [rootCriticalIntensity_eq_top_of_rowSum_zero _ (fun _ => by simp)]
    exact ENNReal.coe_lt_top)

/-- The zero kernel on `ℤ`: both threshold identifications hold, with value `⊤`. -/
example :
    rootCriticalIntensity (fun _ : Sym2 ℤ => (0 : ℝ≥0)) 0 =
        sSup ((↑) '' {β : ℝ≥0 | chi (intensityProfile (fun _ : Sym2 ℤ => (0 : ℝ≥0)) β) 0 < ⊤})
      ∧ rootCriticalIntensity (fun _ : Sym2 ℤ => (0 : ℝ≥0)) 0 = ⊤ :=
  ⟨rootCriticalIntensity_eq_sSup_chi_lt_top _ transitive_zero (fun _ => by simp) 0,
    rootCriticalIntensity_eq_top_of_rowSum_zero _ (fun _ => by simp) 0⟩

/-- The constant kernel on `ZMod 2` (finite `V`, `β_c = ⊤`): the hypotheses of items 1 to 3
hold, and the flux and susceptibility thresholds agree with `β_c`. -/
example :
    rootCriticalIntensity (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) 0 =
      sSup ((↑) '' {β : ℝ≥0 | chi (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ≥0)) β) 0
        < ⊤}) :=
  rootCriticalIntensity_eq_sSup_chi_lt_top _ transitive_const_zmod_two
    (fun _ => Summable.of_finite) 0

open PercLib.Models in
open Classical in
/-- The free-group tree (the 4-regular tree, `Models/FreeGroupTree.lean`): its kernel is
transitive with summable rows and has a finite threshold `β_c ≤ 1`, so this is a
finite-threshold witness of the mean-field bound `one_sub_div_le_law_cluster_infinite`
applied at `β = 2`. -/
example :
    rootCriticalIntensity (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) 1 ≤ 1 ∧
    1 - rootCriticalIntensity (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) 1 / (2 : ℝ≥0) ≤
      law (intensityProfile (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) 2) {ω | (cluster ω 1).Infinite} := by
  set J : Sym2 (FreeGroup (Fin 2)) → ℝ≥0 := fun e =>
    if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
    then (1 : ℝ≥0) else 0 with hJe
  have hT : ∀ x y : FreeGroup (Fin 2), ∃ σ : FreeGroup (Fin 2) ≃ FreeGroup (Fin 2),
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := freeGroupTree_transitive
  have h11 : J s(1, 1) = 0 := by
    simp only [J, mem_ofPred_eq]
    rw [ite_eq_right]
    rintro ⟨g, i, h⟩
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      exact FreeGroup.of_ne_one i (by simpa using h2.symm)
    · subst h2
      exact FreeGroup.of_ne_one i (by simpa using h1.symm)
  have hrow1 : ∑' v, (J s(1, v) : ℝ≥0∞) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (tsum_congr fun v => ?_)) freeGroupTree_rowSum_lt_top
    split_ifs with hv
    · rw [hv, h11, ENNReal.coe_zero]
    · rfl
  have hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ) := by
    intro u
    have hshift : ∀ v, (J s(u, v) : ℝ≥0∞) = J s(1, u⁻¹ * v) := by
      intro v
      have h := freeGroupTree_map_mulLeft_mem_iff u⁻¹ s(u, v)
      simp only [Sym2.map_mk, inv_mul_cancel] at h
      simp only [J, h]
    have hs : ∑' v, (J s(u, v) : ℝ≥0∞) < ⊤ := by
      simp_rw [hshift]
      have := (Equiv.mulLeft u⁻¹).tsum_eq (fun w => (J s(1, w) : ℝ≥0∞))
      simp only [Equiv.coe_mulLeft] at this
      rw [this]
      exact hrow1
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hs.ne)
  have hc : rootCriticalIntensity J 1 ≤ 1 := by
    rw [rootCriticalIntensity_eq_sSup_chi_lt_top J hT hJ 1]
    refine sSup_le ?_
    rintro _ ⟨β, hβ, rfl⟩
    by_contra h
    rw [not_le, ENNReal.one_lt_coe_iff] at h
    exact absurd (freeGroupTree_chi_eq_top h.le) hβ.ne
  exact ⟨hc, one_sub_div_le_law_cluster_infinite J hT hJ (hc.trans_lt (by norm_num))⟩

end PercLib.Percolation.Bond
