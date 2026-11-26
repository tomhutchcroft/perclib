/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer
public import PercLib.Percolation.Bond.Embedding
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.IntensityMonotone

/-!
# Right-openness of finite susceptibility for transitive intensities (5LNL)

Let `J : Sym2 V → ℝ≥0` be **transitive** about `o`: for every `x` some bijection `φ` of `V`
with `φ o = x` preserves `J`. Write `q_β = intensityProfile J β`,
`L = ∑'_{y ≠ o} J s(o, y)` and `χ_β = chi q_β o`.

1. `chi_intensity_add_le`. If `L < ⊤`, `χ_β < ⊤` and `ε < 1/(L χ_β)`, then
   `χ_{β+ε} ≤ χ_β / (1 - ε L χ_β)`.
   The proof writes `q_{β+ε}` as the union of `q_β` and an independent layer
   `q_ε = 1 - e^{-εJ}` (`intensityProfile_add`). That layer has off-diagonal row sums at
   most `εL` (`intensity_rowSum_le`). Transitivity makes `χ_β` constant in the vertex, so
   MLLO (`chi_union_le_of_bounds`) applies with `δ = εL` and `M = χ_β`.
2. `inv_le_chiCriticalIntensity`. `b_χ = sSup {β | χ_β < ⊤} ≥ 1/L`.
3. `exists_pos_chi_intensity_add_lt_top`: if `χ_β < ⊤`, then `χ_{β+ε} < ⊤` for some `ε > 0`
   (finite susceptibility is right-open). The endpoint form "`b_χ < ⊤` implies
   `χ_{b_χ} = ⊤`" needs a compiled example with `b_χ < ⊤` and is left to a follow-up.

The threshold `b_χ` is written out as a supremum of a set of finite parameters; no
definition is added.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A bijection preserving `J` preserves every intensity profile. -/
theorem intensityProfile_map_eq {J : Sym2 V → ℝ≥0} {φ : V ≃ V}
    (hφ : ∀ e, J (Sym2.map φ e) = J e) (β : ℝ≥0) (e : Sym2 V) :
    intensityProfile J β (Sym2.map φ e) = intensityProfile J β e := by
  simp only [intensityProfile, hφ]

/-- The inverse of a bijection preserving `J` preserves `J`. -/
theorem map_symm_preserves {J : Sym2 V → ℝ≥0} {φ : V ≃ V}
    (hφ : ∀ e, J (Sym2.map φ e) = J e) (e : Sym2 V) : J (Sym2.map φ.symm e) = J e := by
  have := hφ (Sym2.map φ.symm e)
  rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id, id] at this
  exact this.symm

/-- Under transitivity every susceptibility is at most the one at `o`. -/
theorem chi_intensity_le_root [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e) (β : ℝ≥0) (x : V) :
    chi (intensityProfile J β) x ≤ chi (intensityProfile J β) o := by
  obtain ⟨φ, rfl, hφ⟩ := hJ x
  have h := chi_le_of_embedding φ.symm.toEmbedding (q := intensityProfile J β)
    (q' := intensityProfile J β)
    (fun e _ => (intensityProfile_map_eq (map_symm_preserves hφ) β e).ge) (φ o)
  simpa using h

open Classical in
/-- Under transitivity every off-diagonal row sum of `J` equals the one at `o`. -/
theorem rowSum_eq_root {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e) (u : V) :
    rowSum (fun e => (J e : ℝ≥0∞)) u =
      rowSum (fun e => (J e : ℝ≥0∞)) o := by
  obtain ⟨φ, rfl, hφ⟩ := hJ u
  rw [rowSum_def, rowSum_def, ← φ.tsum_eq]
  refine tsum_congr fun y => ?_
  simp only [φ.injective.eq_iff]
  congr 2
  rw [← hφ s(o, y), Sym2.map_mk]

/-- **Step.** For a transitive intensity with `L < ⊤`, if `χ_β < ⊤` and
`ε < 1/(L χ_β)`, then `χ_{β+ε} ≤ χ_β / (1 - ε L χ_β)`. -/
theorem chi_intensity_add_le [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤) {β ε : ℝ≥0}
    (hχ : chi (intensityProfile J β) o < ⊤)
    (hε : (ε : ℝ≥0∞) <
      (rowSum (fun e => (J e : ℝ≥0∞)) o * chi (intensityProfile J β) o)⁻¹) :
    chi (intensityProfile J (β + ε)) o ≤ chi (intensityProfile J β) o /
      (1 - (ε : ℝ≥0∞) * rowSum (fun e => (J e : ℝ≥0∞)) o *
        chi (intensityProfile J β) o) := by
  set L := rowSum (fun e => (J e : ℝ≥0∞)) o with hLdef
  have hprof : intensityProfile J (β + ε) =
      fun e => σ (σ (intensityProfile J β e) * σ (intensityProfile J ε e)) :=
    funext (intensityProfile_add J β ε)
  have hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ (L.toNNReal : ℝ≥0∞) := by
    intro u
    rw [rowSum_eq_root hJ u, ENNReal.coe_toNNReal hL.ne]
  have hδ := intensity_rowSum_le J L.toNNReal hrow ε
  rw [ENNReal.coe_toNNReal hL.ne] at hδ
  have hεLχ : (ε : ℝ≥0∞) * L * chi (intensityProfile J β) o < 1 := by
    rw [mul_assoc]
    exact ENNReal.mul_lt_of_lt_div (by rwa [one_div])
  rw [hprof]
  exact chi_union_le_of_bounds (intensityProfile J β) (intensityProfile J ε) hδ
    (chi_intensity_le_root hJ β) hχ hεLχ o

/-- The susceptibility at `β + ε` stays finite for small `ε`. -/
theorem chi_intensity_add_lt_top [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤) {β ε : ℝ≥0}
    (hχ : chi (intensityProfile J β) o < ⊤)
    (hε : (ε : ℝ≥0∞) <
      (rowSum (fun e => (J e : ℝ≥0∞)) o * chi (intensityProfile J β) o)⁻¹) :
    chi (intensityProfile J (β + ε)) o < ⊤ := by
  refine (chi_intensity_add_le hJ hL hχ hε).trans_lt (ENNReal.div_lt_top hχ.ne ?_)
  have : (ε : ℝ≥0∞) * rowSum (fun e => (J e : ℝ≥0∞)) o *
      chi (intensityProfile J β) o < 1 := by
    rw [mul_assoc]
    exact ENNReal.mul_lt_of_lt_div (by rwa [one_div])
  exact (tsub_pos_of_lt this).ne'

/-- **Right-openness.** If `χ_β < ⊤`, then `χ_{β+ε} < ⊤` for some `ε > 0`. -/
theorem exists_pos_chi_intensity_add_lt_top [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤) {β : ℝ≥0}
    (hχ : chi (intensityProfile J β) o < ⊤) :
    ∃ ε : ℝ≥0, 0 < ε ∧ chi (intensityProfile J (β + ε)) o < ⊤ := by
  have hpos : (0 : ℝ≥0∞) <
      (rowSum (fun e => (J e : ℝ≥0∞)) o * chi (intensityProfile J β) o)⁻¹ :=
    ENNReal.inv_pos.2 (ENNReal.mul_ne_top hL.ne hχ.ne)
  obtain ⟨ε, hε0, hε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  exact ⟨ε, by exact_mod_cast hε0, chi_intensity_add_lt_top hJ hL hχ hε⟩

/-- **Lower bound.** `b_χ = sSup {β | χ_β < ⊤} ≥ 1/L` for a transitive intensity. -/
theorem inv_le_chiCriticalIntensity [Countable V] {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤) :
    (rowSum (fun e => (J e : ℝ≥0∞)) o)⁻¹ ≤
      sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) := by
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨ε, hcε, hεL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  refine hcε.trans_le (le_sSup ⟨ε, ?_, rfl⟩)
  have h0 : chi (intensityProfile J 0) o = 1 := chi_intensity_zero J o
  have := chi_intensity_add_lt_top hJ hL (β := 0) (ε := ε) (by rw [h0]; exact ENNReal.one_lt_top)
    (by rwa [h0, mul_one])
  rwa [zero_add] at this

/-! ### Non-vacuity -/

open Classical in
/-- The constant intensity on `Sym2 ℤ` restricted to nearest neighbours is transitive about
`0`: translations preserve it. -/
example : ∀ x : ℤ, ∃ φ : ℤ ≃ ℤ, φ 0 = x ∧ ∀ e,
    (fun e : Sym2 ℤ => if e ∈ {f : Sym2 ℤ | ∃ a, f = s(a, a + 1)} then (1 : ℝ≥0) else 0)
        (Sym2.map φ e) =
      (fun e : Sym2 ℤ => if e ∈ {f : Sym2 ℤ | ∃ a, f = s(a, a + 1)} then (1 : ℝ≥0) else 0) e := by
  intro x
  refine ⟨Equiv.addRight x, by simp, fun e => ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, Equiv.coe_addRight, mem_ofPred_eq]
    congr 1
    apply propext
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c - x, ?_⟩
      rcases Sym2.eq_iff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Sym2.eq_iff]; left; constructor <;> omega
      · rw [Sym2.eq_iff]; right; constructor <;> omega
    · rintro ⟨c, hc⟩
      refine ⟨c + x, ?_⟩
      rcases Sym2.eq_iff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Sym2.eq_iff]; left; constructor <;> omega
      · rw [Sym2.eq_iff]; right; constructor <;> omega

/-- For `J = 0` on `ℤ` every hypothesis of `chi_intensity_add_le` holds: translations are
transitive, `L = 0` and `χ_β = 1`. -/
example (ε : ℝ≥0) :=
  chi_intensity_add_le (J := fun _ : Sym2 ℤ => (0 : ℝ≥0)) (o := (0 : ℤ)) (β := 0) (ε := ε)
    (fun x => ⟨Equiv.addRight x, by simp, fun _ => rfl⟩) (by simp)
    (by rw [chi_intensity_zero]; exact ENNReal.one_lt_top) (by simp)

/-- Right-openness at `β = 0` for the same intensity. -/
example := exists_pos_chi_intensity_add_lt_top (J := fun _ : Sym2 ℤ => (0 : ℝ≥0)) (o := (0 : ℤ))
  (β := 0) (fun x => ⟨Equiv.addRight x, by simp, fun _ => rfl⟩) (by simp)
  (by rw [chi_intensity_zero]; exact ENNReal.one_lt_top)

/-- The same intensity has `b_χ = ⊤`, so the lower bound `1/L = ⊤` is attained. -/
example := inv_le_chiCriticalIntensity (J := fun _ : Sym2 ℤ => (0 : ℝ≥0)) (o := (0 : ℤ))
  (fun x => ⟨Equiv.addRight x, by simp, fun _ => rfl⟩) (by simp)

end PercLib.Percolation.Bond

end
