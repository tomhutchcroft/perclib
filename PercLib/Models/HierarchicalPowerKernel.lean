/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Power-law kernel bounds on the hierarchical lattice. New proofs from this library's
hierarchical geometry and exact geometric rows (`tsum_level_gt_eq`), its threshold,
transport and truncated-mean theorems, and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied and no definition is
added.
-/
module

public import PercLib.Models.HierarchicalCutoff
public import PercLib.Models.HierarchicalAmplificationStep
public import PercLib.Models.LongRange.RootIndependence
public import PercLib.Percolation.Bond.Tightness.TruncatedMean

/-! # Power-law kernels on the hierarchical lattice

The lattice is `V = ℕ →₀ (Fin d → ZMod L)` and `h z = z.support.sup Nat.succ` is the level.
The kernel `J` is translation invariant (`J s(u + x, v + x) = J s(u, v)`) and satisfies the
upper bound `J s(u, v) ≤ C L^{-(d+α) h(v-u)}` for `u ≠ v`, with `L ≥ 2` and `α > 0`.
Write `K = C (1 - L^{-d}) / (L^α - 1)`.

* `tsum_level_sub_gt_le_of_powerLaw`: the kernel mass of the pairs of displacement level
  above `n` is at most `K L^{-αn}` (comparison with the exact geometric kernel of
  `tsum_level_gt_eq`).
* `rowSum_le_of_powerLaw`, `summable_of_powerLaw`: the off-diagonal row is at most `K`, and
  real rows are summable.
* `tsum_level_gt_le_of_powerLaw`: for `h u ≤ n`, the row from `u` to the exterior of the
  level-`n` ball is at most `K L^{-αn}`.
* `ofReal_le_rootCriticalIntensity_of_powerLaw`: `K⁻¹ ≤ β_c(x)` for every `x` (the row-sum
  half of Prop. 2.12(i) of the hierarchical source); `rootCriticalIntensity_eq_top_of_powerLaw`:
  `C ≤ 0` gives `β_c = ⊤`.
* `transitive_of_powerLaw_translationInvariant`: translations give the transitivity
  hypothesis `hT` of the sharpness and finite-set criterion theorems.
* `blockTransitive_levelBall`: translations by points of the level-`n` ball give the block
  transitivity hypothesis of `le_card_mul_lintegral_clusterIntersection_of_transitive` for the
  profile restricted to that ball; `le_card_mul_lintegral_clusterIntersection_levelBall` is the
  resulting bound `M_n² / (4e) ≤ L^{dn} E|K_0 ∩ Λ_n|`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

/-- The real identity behind the closed form of the power-law tail. -/
theorem powerLaw_tail_real_identity (hL : 2 ≤ L) (α C : ℝ) (hα : 0 < α) (n : ℕ) :
    C * ((L : ℝ) ^ d - 1) * (L : ℝ) ^ (-((d : ℝ) + α)) / (1 - (L : ℝ) ^ (-α)) *
        ((L : ℝ) ^ (-α)) ^ n =
      C * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) / ((L : ℝ) ^ α - 1) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have ha1 : 1 < (L : ℝ) ^ α := Real.one_lt_rpow hL1 hα
  have hb : (0 : ℝ) < (L : ℝ) ^ d := pow_pos hLpos d
  rw [Real.rpow_neg hLpos.le, Real.rpow_neg hLpos.le, Real.rpow_neg hLpos.le,
    Real.rpow_neg hLpos.le, Real.rpow_add hLpos, Real.rpow_natCast,
    Real.rpow_mul_natCast hLpos.le]
  have ha0 : (L : ℝ) ^ α ≠ 0 := by positivity
  have ha1' : (L : ℝ) ^ α - 1 ≠ 0 := by linarith
  have h1a : 1 - ((L : ℝ) ^ α)⁻¹ = ((L : ℝ) ^ α - 1) / (L : ℝ) ^ α := by
    field_simp
  rw [h1a, inv_pow]
  field_simp

/-- **Power-law tail.** The kernel mass from `u` over the pairs of displacement level above
`n` is at most `C (1 - L^{-d}) L^{-αn} / (L^α - 1)`. Proved by comparison with the exact
geometric kernel `C⁺ (L^{-(d+α)})^{h}` and its tail `tsum_level_gt_eq`. No sign condition on
`C` and no translation invariance is needed. -/
theorem tsum_level_sub_gt_le_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ} (hα : 0 < α)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (n : ℕ) (u : ℕ →₀ (Fin d → ZMod L)) :
    (∑' v, if n < (v - u).support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal (C * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) /
        ((L : ℝ) ^ α - 1)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  let ρ : ℝ≥0 := ⟨(L : ℝ) ^ (-((d : ℝ) + α)), (Real.rpow_pos_of_pos hLpos _).le⟩
  have hρ : (ρ : ℝ) = (L : ℝ) ^ (-((d : ℝ) + α)) := rfl
  obtain ⟨J', hJ'⟩ := exists_hierarchical_kernel (d := d) (L := L) C.toNNReal ρ
  have hle : ∀ v, (if n < (v - u).support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0) ≤
      if n < (v - u).support.sup Nat.succ then (J' s(u, v) : ℝ≥0∞) else 0 := by
    intro v
    split_ifs with hv
    · have huv : u ≠ v := by
        rintro rfl
        simp at hv
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hJ', NNReal.coe_mul, NNReal.coe_pow, hρ,
        Real.coe_toNNReal', ← Real.rpow_mul_natCast hLpos.le]
      refine (hJ u v huv).trans ?_
      rw [neg_mul]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hLpos.le _)
    · exact le_rfl
  refine (ENNReal.tsum_le_tsum hle).trans (le_of_eq ?_)
  rw [tsum_level_gt_eq J' C.toNNReal ρ hJ' n u]
  have hNr : (L : ℝ≥0∞) ^ d * ρ = ENNReal.ofReal ((L : ℝ) ^ (-α)) := by
    rw [← ENNReal.ofReal_coe_nnreal, hρ, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
    congr 1
    ring
  have hlt : (L : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have hden : 1 - ENNReal.ofReal ((L : ℝ) ^ (-α)) = ENNReal.ofReal (1 - (L : ℝ) ^ (-α)) := by
    rw [ENNReal.ofReal_sub _ (Real.rpow_nonneg hLpos.le _), ENNReal.ofReal_one]
  have hN1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL1.le
  have hN : ((L ^ d - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((L : ℝ) ^ d - 1) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow,
      Nat.cast_one]
  have hC : ((C.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal C := rfl
  rw [hNr, hden, hN, hC, ← ENNReal.ofReal_coe_nnreal (p := ρ), hρ,
    ← ENNReal.ofReal_pow (Real.rpow_nonneg hLpos.le _),
    ← ENNReal.ofReal_mul' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ d - 1),
    ← ENNReal.ofReal_mul' (Real.rpow_nonneg hLpos.le _),
    ← ENNReal.ofReal_div_of_pos (by linarith : (0 : ℝ) < 1 - (L : ℝ) ^ (-α)),
    ← ENNReal.ofReal_mul' (pow_nonneg (Real.rpow_nonneg hLpos.le _) _)]
  congr 1
  exact powerLaw_tail_real_identity hL α C hα n

/-- **Off-diagonal row bound.** The off-diagonal row of a power-law kernel is at most
`C (1 - L^{-d}) / (L^α - 1)`. It feeds `inv_le_rootCriticalIntensity` and its relatives
(after `convert`, which only changes the decidability instance of `w = v`). -/
theorem rowSum_le_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ} (hα : 0 < α)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (u : ℕ →₀ (Fin d → ZMod L)) :
    rowSum (fun e => (J e : ℝ≥0∞)) u ≤
      ENNReal.ofReal (C * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1)) := by
  have h := tsum_level_sub_gt_le_of_powerLaw hL hα J hJ 0 u
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one] at h
  refine le_of_eq_of_le (tsum_congr fun v => ?_) h
  by_cases hv : v = u
  · simp [hv]
  · have : 0 < (v - u).support.sup Nat.succ :=
      Nat.pos_of_ne_zero fun h0 => hv ((level_sub_eq_zero_iff u v).1 h0).symm
    simp [hv, this]

/-- **Summable rows.** Real rows of a power-law kernel are summable: the `hJ` hypothesis of
`chi_lt_top_of_lt_rootCriticalIntensity`. -/
theorem summable_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ} (hα : 0 < α)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) :
    ∀ u, Summable fun v => (J s(u, v) : ℝ) := by
  intro u
  refine NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)
  have hsplit : (∑' v, (J s(u, v) : ℝ≥0∞)) =
      (J s(u, u) : ℝ≥0∞) + rowSum (fun e => (J e : ℝ≥0∞)) u := by
    calc (∑' v, (J s(u, v) : ℝ≥0∞))
        = ∑' v, ((if v = u then (J s(u, u) : ℝ≥0∞) else 0) +
            if v = u then 0 else (J s(u, v) : ℝ≥0∞)) :=
          tsum_congr fun v => by by_cases hv : v = u <;> simp [hv]
      _ = _ := by rw [ENNReal.tsum_add, tsum_ite_eq, rowSum_def]
  rw [hsplit]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rowSum_le_of_powerLaw hL hα J hJ u)⟩

/-- **Exterior row bound.** For `h u ≤ n`, the kernel mass from `u` to the exterior
`{h > n}` of the level-`n` ball is at most `C (1 - L^{-d}) L^{-αn} / (L^α - 1)`. Here
`h (v - u) = h v` on the exterior, by the strong triangle inequality. -/
theorem tsum_level_gt_le_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ} (hα : 0 < α)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (n : ℕ) {u : ℕ →₀ (Fin d → ZMod L)} (hu : u.support.sup Nat.succ ≤ n) :
    (∑' v, if n < v.support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal (C * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) /
        ((L : ℝ) ^ α - 1)) := by
  refine le_of_eq_of_le (tsum_congr fun v => ?_) (tsum_level_sub_gt_le_of_powerLaw hL hα J hJ n u)
  have hiff : n < v.support.sup Nat.succ ↔ n < (v - u).support.sup Nat.succ := by
    constructor
    · intro hv
      by_contra hvu
      have h := level_add_le_max (v - u) u
      rw [sub_add_cancel] at h
      rcases le_max_iff.1 h with h | h <;> omega
    · intro hvu
      by_contra hv
      have h := level_sub_le_max u 0 v
      rw [zero_sub, sub_zero, Finsupp.support_neg] at h
      rcases le_max_iff.1 h with h | h <;> omega
  simp only [hiff]

/-- **Threshold lower bound** (row-sum half of Prop. 2.12(i) of the hierarchical source):
`(L^α - 1) / (C (1 - L^{-d})) ≤ β_c(x)` at every root. No sign condition on `C` is needed:
when `C (1 - L^{-d}) ≤ 0` the left side is `0`. -/
theorem ofReal_le_rootCriticalIntensity_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ}
    (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (x : ℕ →₀ (Fin d → ZMod L)) :
    ENNReal.ofReal (((L : ℝ) ^ α - 1) / (C * (1 - (L : ℝ) ^ (-(d : ℝ))))) ≤
      rootCriticalIntensity J x := by
  set K : ℝ := C * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1) with hK_def
  have hinv : ((L : ℝ) ^ α - 1) / (C * (1 - (L : ℝ) ^ (-(d : ℝ)))) = K⁻¹ := by
    rw [hK_def, inv_div]
  rw [hinv]
  rcases le_or_gt K 0 with hK | hK
  · rw [ENNReal.ofReal_of_nonpos (inv_nonpos.2 hK)]
    exact zero_le
  · have hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤
        ((K.toNNReal : ℝ≥0) : ℝ≥0∞) := fun v => rowSum_le_of_powerLaw hL hα J hJ v
    have h := inv_le_rootCriticalIntensity J K.toNNReal (fun v => by convert hrow v) x
    rwa [show ((K.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal K from rfl,
      ← ENNReal.ofReal_inv_of_pos hK] at h

/-- **Degenerate constant.** With `C ≤ 0` the power-law bound forces every off-diagonal
pair to vanish, so every root threshold is `⊤`. -/
theorem rootCriticalIntensity_eq_top_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ}
    (hα : 0 < α) (hC : C ≤ 0) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (x : ℕ →₀ (Fin d → ZMod L)) :
    rootCriticalIntensity J x = ⊤ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hK : C * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg hC
        (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by simp)))
    · exact sub_nonneg.2 (Real.one_le_rpow hL1 hα.le)
  refine rootCriticalIntensity_eq_top_of_rowSum_zero J (fun v => ?_) x
  have h := rowSum_le_of_powerLaw hL hα J hJ v
  rw [ENNReal.ofReal_of_nonpos hK] at h
  convert h

/-- **Transitivity.** For a translation-invariant kernel, the translation by `y - x` is an
automorphism carrying `x` to `y`: the hypothesis `hT` of `chi_lt_top_of_lt_rootCriticalIntensity`
and of the finite-set criterion. -/
theorem transitive_of_powerLaw_translationInvariant
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)) :
    ∀ x y : ℕ →₀ (Fin d → ZMod L),
      ∃ σ : (ℕ →₀ (Fin d → ZMod L)) ≃ (ℕ →₀ (Fin d → ZMod L)),
        σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e :=
  LongRange.transitive_of_map_add_invariant J fun a e => by
    induction e using Sym2.ind with
    | _ u v => exact hJt a u v

open Classical in
/-- **Block transitivity.** For the profile `q_β` restricted to the pairs inside the level-`n`
ball `Λ_n` (spelled as in `tightnessScale_hierarchical_amplification`), the translation by any
`v ∈ Λ_n` carries `0` to `v`, preserves the law and preserves `Λ_n`: the hypothesis `hT` of
`le_card_mul_lintegral_clusterIntersection_of_transitive` with `o = 0`. -/
theorem blockTransitive_levelBall [NeZero L] (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)) (β : ℝ≥0) (n : ℕ) :
    ∀ v ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
      ∃ σ : (ℕ →₀ (Fin d → ZMod L)) ≃ (ℕ →₀ (Fin d → ZMod L)), σ 0 = v ∧
        (law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)).map
            (fun ω => Sym2.map σ '' ω) =
          law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0) ∧
        ∀ w, σ w ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset ↔
          w ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset := by
  intro v hv
  rw [Set.Finite.mem_toFinset] at hv
  change v.support.sup Nat.succ ≤ n at hv
  have hball : ∀ w : ℕ →₀ (Fin d → ZMod L),
      (w + v).support.sup Nat.succ ≤ n ↔ w.support.sup Nat.succ ≤ n := by
    intro w
    constructor
    · intro h
      have h' := level_add_le_max (w + v) (-v)
      rw [add_neg_cancel_right, Finsupp.support_neg] at h'
      exact h'.trans (max_le h hv)
    · intro h
      exact (level_add_le_max w v).trans (max_le h hv)
  have hJσ : ∀ e, J (Sym2.map (Equiv.addRight v) e) = J e := fun e => by
    induction e using Sym2.ind with
    | _ a b => exact hJt v a b
  refine ⟨Equiv.addRight v, zero_add v, ?_, fun w => ?_⟩
  · refine PercLib.Probability.prodBernoulli_map_image_sym2_invariant _ _ fun e => ?_
    induction e using Sym2.ind with
    | _ a b =>
      have hmem : s(a + v, b + v) ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 ↔
          s(a, b) ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2 := by
        simp only [Set.mk_mem_sym2_iff, Set.mem_ofPred_eq, hball]
      have hq : intensityProfile J β s(a + v, b + v) = intensityProfile J β s(a, b) := by
        apply Subtype.ext
        simp only [intensityProfile, hJt]
      simp only [Sym2.map_mk, Equiv.coe_addRight, hmem, hq]
  · simp only [Set.Finite.mem_toFinset, Equiv.coe_addRight, Set.mem_ofPred_eq, hball]

open Classical in
/-- **Block-quantile bound under block transitivity** ((2.2) of the hierarchical source):
for the profile restricted to the level-`n` ball, `M_n² / (4e) ≤ L^{dn} E|K_0 ∩ Λ_n|`. -/
theorem le_card_mul_lintegral_clusterIntersection_levelBall [NeZero L]
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)) (β : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal ((tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 / (4 * Real.exp 1)) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞) *
        ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂(law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)) := by
  have hne : ((finite_level_ball (A := Fin d → ZMod L) n).toFinset).Nonempty :=
    ⟨0, by rw [Set.Finite.mem_toFinset]; simp⟩
  have h := le_card_mul_lintegral_clusterIntersection_of_transitive _ hne 0
    (blockTransitive_levelBall J hJt β n)
  rwa [card_toFinset_level_ball] at h

end PercLib.Models

/-! ### Non-vacuity -/
section Witnesses

open PercLib.Models

/-- `L = 2`, `d = 1`, `α = 1`, `C = 1` and the exact kernel `J = (1/4)^h`: it is translation
invariant and satisfies the power-law bound with equality, so its rows are summable and every
root threshold is at least `(2 - 1) / (1 - 1/2) = 2`. -/
example (x : ℕ →₀ (Fin 1 → ZMod 2)) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
      (∀ a u v, J s(u + a, v + a) = J s(u, v)) ∧
      ENNReal.ofReal 2 ≤ rootCriticalIntensity J x ∧
      ∀ u, Summable fun v => (J s(u, v) : ℝ) := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  have hpow : ∀ u v : ℕ →₀ (Fin 1 → ZMod 2), u ≠ v → (J s(u, v) : ℝ) ≤
      1 * ((2 : ℕ) : ℝ) ^ (-((((1 : ℕ) : ℝ) + 1) *
        (((v - u).support.sup Nat.succ : ℕ) : ℝ))) := by
    intro u v _
    rw [hJ, ← neg_mul, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    norm_num
  refine ⟨J, fun a u v => by rw [hJ, hJ]; simp, ?_,
    summable_of_powerLaw (by norm_num) one_pos J hpow⟩
  have h := ofReal_le_rootCriticalIntensity_of_powerLaw (by norm_num) one_pos J hpow x
  convert h using 2
  norm_num

end Witnesses
