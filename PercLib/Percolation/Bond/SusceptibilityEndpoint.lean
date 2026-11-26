/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Endpoint theorems for the susceptibility, restored on 2026-11-16. The proofs were written earlier in
this repository (`chi_intensity_sSup_eq_top`, removed in commit bf0b5ba;
`exists_chi_gt_of_chi_eq_top` and `one_div_le_chi_of_chi_eq_top`, removed in commit 77f2eef) and are
restored unchanged; they were cut only for want of a non-vacuity witness, now supplied by
`PercLib/Models/FreeGroupTree.lean`. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.IntensityForm
public import PercLib.Percolation.Bond.SusceptibilityDerivative

/-!
# Endpoints of finite susceptibility

* `chi_intensity_sSup_eq_top`: for a transitive intensity with finite row
  sum `L`, if `b_χ = sSup {β | χ_β < ⊤}` is finite then `χ_{b_χ} = ⊤`.
* `one_div_le_chi_of_chi_eq_top` (blow-up): for a transitive kernel with
  off-diagonal row sum `0 < R < ∞`, if `χ` is finite on `(a,b)`, `0 ≤ a`, and `χ(b) = ∞`,
  then `χ(β) ≥ 1/(R (b - β))` for `a < β < b`.
* `tendsto_chi_intensity_nhdsLT_sSup`: for a transitive intensity with `0 < L < ∞`, if `b_χ`
  is finite then `χ_β → ∞` as `β ↑ b_χ`.

The non-vacuity witnesses are in `PercLib/Models/FreeGroupTree.lean`. This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Right-openness.** If `b_χ = sSup {β | χ_β < ⊤}` is finite, then `χ_{b_χ} = ⊤`. -/
theorem chi_intensity_sSup_eq_top [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    (hb : sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤) :
    chi (intensityProfile J
      (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤})).toNNReal)
      o = ⊤ := by
  set b := sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤})
  by_contra hne
  have hχ : chi (intensityProfile J b.toNNReal) o < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨ε, hε0, hmem⟩ := exists_pos_chi_intensity_add_lt_top hJ hL hχ
  have hle : ((b.toNNReal + ε : ℝ≥0) : ℝ≥0∞) ≤ b := le_sSup ⟨_, hmem, rfl⟩
  rw [ENNReal.coe_add, ENNReal.coe_toNNReal hb.ne] at hle
  have : b + 0 < b + ε := ENNReal.add_lt_add_left hb.ne (by exact_mod_cast hε0)
  rw [add_zero] at this
  exact absurd hle (not_le.2 this)


section MXGM

variable [Countable V] (J : Sym2 V → ℝ≥0)
  (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)

omit [Countable V] in
/-- If `χ(b) = ∞` and `χ` is finite on `(a,b)`, then `χ(t)` is arbitrarily large for
`t < b` close to `b`: the susceptibility is a supremum of continuous finite-volume
susceptibilities. -/
theorem exists_chi_gt_of_chi_eq_top [Countable V] (o : V) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤)
    (hb : chi (intensityProfile J b.toNNReal) o = ⊤) {s : ℝ} (hs : a < s) (hsb : s < b)
    (M : ℝ) :
    ∃ t, s ≤ t ∧ t < b ∧ M < (chi (intensityProfile J t.toNNReal) o).toReal := by
  obtain ⟨S, hoS, hsup⟩ := exists_chi_eq_iSup_finiteChi (intensityProfile J b.toNNReal) o
  rw [hsup] at hb
  have hlt : ENNReal.ofReal (|M| + 1) < ⨆ n, ∑ y : (S n : Set V),
      law (intensityProfile J b.toNNReal) {ω : Config V |
        ((openGraph ω).induce (S n : Set V)).Reachable ⟨o, Finset.mem_coe.2 (hoS n)⟩ y} := by
    rw [hb]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  set o' : (S n : Set V) := ⟨o, Finset.mem_coe.2 (hoS n)⟩
  set g : ℝ → ℝ := fun β => ∑ y : (S n : Set V), (law (intensityProfile J β.toNNReal)).real
    {ω : Config V | ((openGraph ω).induce (S n : Set V)).Reachable o' y}
  have hgb : |M| + 1 < g b := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity)
      (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _),
      ENNReal.toReal_sum fun _ _ => measure_ne_top _ _] at hn
    exact hn
  have hb0 : 0 < b := (ha.trans_lt hs).trans hsb
  have hcont : ContinuousAt g b :=
    (sum_law_localConn_hasDerivWithinAt J (S n) o' hb0.le).continuousWithinAt.continuousAt
      (Ici_mem_nhds hb0)
  have hev : ∀ᶠ t in nhdsWithin b (Iio b), M < g t ∧ t ∈ Ioo s b :=
    ((hcont.eventually (lt_mem_nhds (show M < g b by linarith [le_abs_self M]))).filter_mono
      nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hsb)
  obtain ⟨t, hgt, hts⟩ := hev.exists
  refine ⟨t, hts.1.le, hts.2, hgt.trans_le ?_⟩
  simp only [g, measureReal_def]
  rw [← ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
  exact ENNReal.toReal_mono (hfin t ⟨hs.trans hts.1, hts.2⟩) (finiteChi_le_chi _ (S n) o')

include hJ in
/-- **Blow-up.** For a transitive kernel with off-diagonal row sum `0 < R < ∞`, if
`χ(β) = chi q_β o` is finite on `(a,b)`, `0 ≤ a`, and `χ(b) = ∞`, then
`χ(β) ≥ 1/(R (b - β))` for `a < β < b`. -/
theorem one_div_le_chi_of_chi_eq_top (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤)
    (hR0 : 0 < rowSum (fun e => (J e : ℝ≥0∞)) o) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤)
    (hb : chi (intensityProfile J b.toNNReal) o = ⊤) {β : ℝ} (hβ : β ∈ Ioo a b) :
    1 / ((rowSum (fun e => (J e : ℝ≥0∞)) o).toReal * (b - β)) ≤
      (chi (intensityProfile J β.toNNReal) o).toReal := by
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal
  set χ : ℝ → ℝ := fun u => (chi (intensityProfile J u.toNNReal) o).toReal
  have hRpos : 0 < R := ENNReal.toReal_pos hR0.ne' hR
  have hχ1 : 1 ≤ χ β := by
    have := ENNReal.toReal_mono (hfin β hβ) (one_le_chi (intensityProfile J β.toNNReal) o)
    simpa using this
  have hpos : 0 < R * (b - β) := mul_pos hRpos (sub_pos.2 hβ.2)
  rw [one_div_le hpos (by linarith)]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨t, hβt, htb, ht⟩ := exists_chi_gt_of_chi_eq_top J o ha hfin hb hβ.1 hβ.2 (1 / ε)
  have hcmp := inv_chi_sub_le J hJ o hR ha hfin hβ.1 hβt htb
  have hχt : 0 < χ t := (one_div_pos.2 hε).trans ht
  have hinv : 1 / χ t < ε := by
    rw [div_lt_iff₀ hχt]
    rw [div_lt_iff₀ hε] at ht
    linarith
  have : R * (t - β) ≤ R * (b - β) := mul_le_mul_of_nonneg_left (by linarith) hRpos.le
  change 1 / χ β < R * (b - β) + ε
  linarith


end MXGM

/-- **Transitivity about one root gives transitivity between all pairs:** compose
`φ_y ∘ φ_x⁻¹`. -/
theorem forall_exists_equiv_apply_eq_of_root {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e) :
    ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := by
  intro x y
  obtain ⟨φ, rfl, hφ⟩ := hJ x
  obtain ⟨ψ, rfl, hψ⟩ := hJ y
  refine ⟨φ.symm.trans ψ, by simp, fun e => ?_⟩
  rw [Equiv.coe_trans, ← Sym2.map_map, hψ, map_symm_preserves hφ]

/-- **Divergence at the endpoint.** For a transitive intensity with off-diagonal row sum
`0 < L < ⊤`, if `b_χ = sSup {β | χ_β < ⊤}` is finite then `χ_β → ⊤` as `β ↑ b_χ`. -/
theorem tendsto_chi_intensity_nhdsLT_sSup [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hR0 : 0 < rowSum (fun e => (J e : ℝ≥0∞)) o)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    (hb : sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤) :
    Filter.Tendsto (fun β : ℝ≥0 => chi (intensityProfile J β) o)
      (𝓝[<] (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) ''
        {β | chi (intensityProfile J β) o < ⊤})).toNNReal) (𝓝 ⊤) := by
  set b := sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤})
    with hbdef
  have hJ2 := forall_exists_equiv_apply_eq_of_root hJ
  have hfin : ∀ β ∈ Ioo (0 : ℝ) b.toReal, chi (intensityProfile J β.toNNReal) o ≠ ⊤ := by
    intro β hβ
    have hlt : ((β.toNNReal : ℝ≥0) : ℝ≥0∞) < b :=
      (ENNReal.ofReal_lt_iff_lt_toReal hβ.1.le hb.ne).2 hβ.2
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγlt⟩ := lt_sSup_iff.1 hlt
    exact ne_top_of_le_ne_top hγ.ne
      (chi_mono (fun e => intensityProfile_mono J (ENNReal.coe_le_coe.1 hγlt.le) e) o)
  have hbtop : chi (intensityProfile J b.toReal.toNNReal) o = ⊤ := by
    change chi (intensityProfile J ((b.toNNReal : ℝ)).toNNReal) o = ⊤
    rw [Real.toNNReal_coe]
    exact chi_intensity_sSup_eq_top hJ hL hb
  have hbpos : 0 < b.toReal := by
    refine ENNReal.toReal_pos (lt_of_lt_of_le ?_ (inv_le_chiCriticalIntensity hJ hL)).ne' hb.ne
    exact ENNReal.inv_pos.2 hL.ne
  set R := (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal with hRdef
  have hRpos : 0 < R := ENNReal.toReal_pos hR0.ne' hL.ne
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  set δ : ℝ := 1 / (R * ((M : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := div_pos one_pos (mul_pos hRpos (by positivity))
  have hc : max (b.toReal - δ) 0 < ((b.toNNReal : ℝ≥0) : ℝ) :=
    max_lt (by change b.toReal - δ < b.toReal; linarith) hbpos
  have hev : ∀ᶠ β : ℝ≥0 in nhds b.toNNReal, max (b.toReal - δ) 0 < (β : ℝ) :=
    NNReal.continuous_coe.continuousAt.eventually (lt_mem_nhds hc)
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with β hβc hβb
  have hβ0 : 0 < (β : ℝ) := (le_max_right _ _).trans_lt hβc
  have hβδ : b.toReal - δ < (β : ℝ) := (le_max_left _ _).trans_lt hβc
  have hβlt : (β : ℝ) < b.toReal := by
    change (β : ℝ) < (b.toNNReal : ℝ)
    exact_mod_cast hβb
  have hmem : (β : ℝ) ∈ Ioo (0 : ℝ) b.toReal := ⟨hβ0, hβlt⟩
  have key := one_div_le_chi_of_chi_eq_top J hJ2 o hL.ne hR0 le_rfl hfin hbtop hmem
  rw [Real.toNNReal_coe] at key
  have hfinβ := hfin β hmem
  rw [Real.toNNReal_coe] at hfinβ
  rw [← ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hfinβ, ENNReal.coe_toReal]
  refine lt_of_lt_of_le ?_ key
  have hd : 0 < b.toReal - β := sub_pos.2 hβlt
  have hRd : 0 < R * (b.toReal - β) := mul_pos hRpos hd
  have h1 : R * (b.toReal - β) < R * δ := mul_lt_mul_of_pos_left (by linarith) hRpos
  have h2 : R * δ = 1 / ((M : ℝ) + 1) := by
    rw [hδ]; field_simp
  have h3 : (M : ℝ) + 1 < 1 / (R * (b.toReal - β)) :=
    (lt_one_div (by positivity) hRd).2 (h2 ▸ h1)
  linarith

end PercLib.Percolation.Bond

end
