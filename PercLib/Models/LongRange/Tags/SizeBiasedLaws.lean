/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the soft power-law cutoff comparison of the size-biased-laws
article. All mathematical inputs are proved in the imported modules; the ghost comparison
is the two-layer comparison `lintegral_ghost_le_layer` (BEJT).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.SoftCutoff
public import PercLib.Models.LongRange.OmittedLayer
public import PercLib.Models.LongRange.FiniteSusceptibility
public import PercLib.Percolation.Bond.IndependentLayer.Conditional

/-!
# Soft power-law cutoff: correspondence

Wiki correspondence for the soft power-law cutoff and its ghost comparison.

## Main results

* `softCutoff_rows_and_ghost_comparison`
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Percolation.Bond
open scoped ENNReal NNReal unitInterval

namespace PercLib.Models.LongRange

/-- **Soft power-law cutoff.** Let `j` be nonnegative and nonincreasing on `[1, ∞)` with
`j t ≤ A t^{-d-α}`, `J(u,v) = j ‖v-u‖₂` and, for `r ≥ 1`,
`J_r(u,v) = 1{‖v-u‖₂ ≤ r}(j ‖v-u‖₂ - j r)` off the diagonal (`Kfull`, `Kr`: the
off-diagonal bond kernels, both zero on the diagonal). Then `0 ≤ J_r ≤ J`; the rows of
`J - J_r` and of the added layer `1 - e^{-β(J - J_r)}` are at most `C r^{-α}` and
`β C r^{-α}`, `C = A 3^d (1 + 2^d/(1 - 2^{-α}))`; and if the cutoff root cluster is a.s.
finite, the ghost transforms satisfy `M_r(h) ≤ M(h) ≤ M_r(h) + β C r^{-α} E_r[X e^{-hX}] M(h)`
(via the two-layer comparison `lintegral_ghost_le_layer` and transitivity). -/
@[tag "C4E9"]
theorem softCutoff_rows_and_ghost_comparison {d : ℕ} {j : ℝ → ℝ} {α A : ℝ}
    (_hd : 1 ≤ d) (hα : 0 < α) (hA : 0 < A)
    (hj0 : ∀ t, 1 ≤ t → 0 ≤ j t) (hjm : AntitoneOn j (Set.Ici 1))
    (hjA : ∀ t, 1 ≤ t → j t ≤ A * t ^ (-(d : ℝ) - α)) {r : ℝ} (hr : 1 ≤ r)
    (Kfull Kr : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hKfull : ∀ u v, Kfull s(u, v) =
      if u = v then 0 else (j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2)).toNNReal)
    (hKr : ∀ u v, Kr s(u, v) =
      if u = v then 0 else
        (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0).toNNReal) :
    (∀ u v : Fin d → ℤ, u ≠ v →
      0 ≤ (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0) ∧
      (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0) ≤
        j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2)) ∧
    (∀ u : Fin d → ℤ, (∑' v, if v = u then 0 else ENNReal.ofReal
        (j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) -
        (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0))) ≤
      ENNReal.ofReal (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α))) ∧
    (∀ β : ℝ, 0 ≤ β → ∀ u : Fin d → ℤ,
      (∑' v, if v = u then 0 else ENNReal.ofReal (1 - Real.exp (-β *
        (j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) -
          (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
            j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0))))) ≤
      ENNReal.ofReal (β * (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α)))) ∧
    (∀ (β : ℝ≥0) {h : ℝ}, 0 < h →
      (∀ᵐ ω ∂law (intensityProfile Kr β), (cluster ω 0).Finite) →
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
          ∂law (intensityProfile Kr β) ≤
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
          ∂law (intensityProfile Kfull β) ∧
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
          ∂law (intensityProfile Kfull β) ≤
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
          ∂law (intensityProfile Kr β) +
          ENNReal.ofReal (β * (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α))) *
            (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) *
              EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal)))
                ∂law (intensityProfile Kr β)) *
            ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
              ∂law (intensityProfile Kfull β)) := by
  have hC1 : ∀ u v : Fin d → ℤ, u ≠ v →
      0 ≤ (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0) ∧
      (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0) ≤
        j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) :=
    fun u v huv => cutoff_bounds hj0 hjm hr huv
  refine ⟨hC1, fun u => tsum_cutoff_sub_le hα hA.le hjA hr u,
    fun β hβ u => tsum_added_layer_le hα hA.le hjA hr hβ u, ?_⟩
  intro β h hh hfin
  -- `J_r ≤ J` as bond kernels, so `J = J_r + (J - J_r)`.
  have hle : ∀ e, Kr e ≤ Kfull e := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      rw [hKr, hKfull]
      by_cases huv : u = v
      · simp only [huv, ite_true, le_rfl]
      · simp only [huv, ite_false]
        exact Real.toNNReal_le_toNNReal (hC1 u v huv).2
  have hsum : Kr + (Kfull - Kr) = Kfull := by
    funext e
    exact add_tsub_cancel_of_le (hle e)
  set s := intensityProfile (Kfull - Kr) β with hs
  have hlaw : (fun e => σ (σ (intensityProfile Kr β e) * σ (s e))) =
      intensityProfile Kfull β := by
    funext e
    rw [hs, ← intensityProfile_add_kernel, hsum]
  obtain ⟨h1, h2⟩ := lintegral_ghost_le_layer (intensityProfile Kr β) s 0 hh hfin
  rw [hlaw] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  -- The rows of the added layer.
  have hrow : (⨆ u, rowSum (fun e => unitInterval.toENNReal (s e)) u) ≤
      ENNReal.ofReal ((β : ℝ) * (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α))) := by
    refine iSup_le fun u => le_trans (le_of_eq (tsum_congr fun w => ?_))
      (tsum_added_layer_le hα hA.le hjA hr β.2 u)
    rcases eq_or_ne w u with hwu | hwu
    · simp only [hwu, ite_true]
    · simp only [hwu, ite_false]
      have huw : u ≠ w := fun h => hwu h.symm
      have hj : 0 ≤ j √(∑ i, (((w - u) i : ℤ) : ℝ) ^ 2) :=
        hj0 _ (one_le_euclid (sub_ne_zero.2 hwu))
      rw [unitInterval.toENNReal_apply,
        show (unitInterval.toNNReal (s s(u, w)) : ℝ≥0∞) = ENNReal.ofReal (s s(u, w)) from
        (ENNReal.ofReal_eq_coe_nnreal (s s(u, w)).2.1).symm]
      congr 1
      change 1 - Real.exp (-(β : ℝ) * ((Kfull s(u, w) - Kr s(u, w) : ℝ≥0) : ℝ)) = _
      rw [NNReal.coe_sub (hle _), hKfull, hKr]
      simp only [huw, ite_false]
      rw [Real.coe_toNNReal _ hj, Real.coe_toNNReal _ (hC1 u w huw).1]
      congr
  -- Transitivity of the full profile.
  have hT : ∀ x y : Fin d → ℤ, ∃ τ : (Fin d → ℤ) ≃ (Fin d → ℤ), τ x = y ∧
      ∀ e, intensityProfile Kfull β (Sym2.map τ e) = intensityProfile Kfull β e := by
    have hk : ∀ x y : Fin d → ℤ, Kfull s(x, y) =
        (fun z : Fin d → ℤ => if z = 0 then 0 else
          (j √(∑ i, ((z i : ℤ) : ℝ) ^ 2)).toNNReal) (y - x) := by
      intro x y
      rw [hKfull]
      simp only [sub_eq_zero, eq_comm]
    intro x y
    obtain ⟨τ, hτx, hτ⟩ := PercLib.Models.transitive_of_translationInvariant Kfull
      (fun z : Fin d → ℤ => if z = 0 then 0 else (j √(∑ i, ((z i : ℤ) : ℝ) ^ 2)).toNNReal) hk x y
    exact ⟨τ, hτx, fun e => by simp only [intensityProfile, hτ e]⟩
  have hsup : (⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂law (intensityProfile Kfull β)) =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
        ∂law (intensityProfile Kfull β) :=
    le_antisymm (iSup_le fun v => (lintegral_ghost_eq_of_transitive _ hT h 0 v).le)
      (le_iSup (fun v => ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂law (intensityProfile Kfull β)) 0)
  rw [hsup]
  gcongr

end PercLib.Models.LongRange
