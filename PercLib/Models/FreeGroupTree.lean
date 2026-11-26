/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied. The model is the Cayley graph of the
free group of rank two (the 4-regular tree).
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.SetTheory.Cardinal.Free
public import PercLib.Models.BinaryTree
public import PercLib.Percolation.Bond.IndependentLayer.IntensityForm
public import PercLib.Percolation.Bond.PathLowerBounds
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Percolation.Bond.SusceptibilityEndpoint

/-!
# A transitive intensity with infinite susceptibility at a finite parameter

Let `V = FreeGroup (Fin 2)` and let `J e = 1` when `e = s(g, g * FreeGroup.of i)` for some
`g` and `i`, and `J e = 0` otherwise: the right Cayley graph of the free group, the
4-regular tree. Write `q_β = intensityProfile J β`, `L = ∑'_{y ≠ 1} J s(1, y)` and
`b_χ = sSup {β | χ_β(1) < ⊤}` (in `ℝ≥0∞`), exactly as in
`PercLib/Percolation/Bond/IndependentLayer/IntensityForm.lean`.

* `J` is invariant under left multiplication, so it is transitive in both spellings used
  in the library (`freeGroupTree_transitive_one`, `freeGroupTree_transitive`).
* `0 < L < ⊤` (`freeGroupTree_rowSum_pos`, `freeGroupTree_rowSum_lt_top`).
* `χ_β(1) = ⊤` for every `β ≥ 1` (`freeGroupTree_chi_eq_top`): the `2ⁿ` positive words of
  length `n` are distinct vertices, each joined to `1` by an open path with probability
  at least `(1 - e^{-β})ⁿ ≥ 2⁻ⁿ`.
* Hence `b_χ` is finite and positive, `χ` is finite below it and infinite at it
  (`freeGroupTree_chi_endpoint`, and the real-parameter form `freeGroupTree_chi_endpoint_real`).
  These are the non-vacuity witnesses for the endpoint statements of
  `PercLib/Percolation/Bond/SusceptibilityEndpoint.lean`.

This file adds no definition: the kernel is written out in each statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal unitInterval

namespace PercLib.Models

/-- Left multiplication preserves the right Cayley edges of the free group. -/
theorem freeGroupTree_map_mulLeft_mem_iff (x : FreeGroup (Fin 2)) (e : Sym2 (FreeGroup (Fin 2))) :
    Sym2.map (x * ·) e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} ↔
      e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} := by
  have key : ∀ (y : FreeGroup (Fin 2)) (e : Sym2 (FreeGroup (Fin 2))),
      e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} →
        Sym2.map (y * ·) e ∈
          {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} := by
    rintro y _ ⟨g, i, rfl⟩
    exact ⟨y * g, i, by simp [Sym2.map_mk, mul_assoc]⟩
  refine ⟨fun h => ?_, key x e⟩
  have := key x⁻¹ _ h
  rwa [Sym2.map_map, show ((x⁻¹ * ·) ∘ (x * ·) : FreeGroup (Fin 2) → FreeGroup (Fin 2)) = id
    from funext fun g => by simp, Sym2.map_id, id] at this

open Classical in
/-- **Transitivity, rooted form** (as in `IntensityForm.lean`). -/
theorem freeGroupTree_transitive_one :
    ∀ x : FreeGroup (Fin 2), ∃ φ : FreeGroup (Fin 2) ≃ FreeGroup (Fin 2), φ 1 = x ∧ ∀ e,
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) (Sym2.map φ e) =
        (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) e := by
  intro x
  refine ⟨Equiv.mulLeft x, by simp, fun e => ?_⟩
  simp only
  rw [show (⇑(Equiv.mulLeft x) : FreeGroup (Fin 2) → FreeGroup (Fin 2)) = (x * ·) from rfl,
    if_congr (freeGroupTree_map_mulLeft_mem_iff x e) rfl rfl]

open Classical in
/-- **Transitivity, two-point form** (as in `SusceptibilityDerivative.lean`). -/
theorem freeGroupTree_transitive :
    ∀ x y : FreeGroup (Fin 2), ∃ ψ : FreeGroup (Fin 2) ≃ FreeGroup (Fin 2), ψ x = y ∧ ∀ e,
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) (Sym2.map ψ e) =
        (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) e := by
  intro x y
  refine ⟨Equiv.mulLeft (y * x⁻¹), by simp, fun e => ?_⟩
  simp only
  rw [show (⇑(Equiv.mulLeft (y * x⁻¹)) : FreeGroup (Fin 2) → FreeGroup (Fin 2)) =
      ((y * x⁻¹) * ·) from rfl,
    if_congr (freeGroupTree_map_mulLeft_mem_iff (y * x⁻¹) e) rfl rfl]

open Classical in
/-- The off-diagonal row sum of the Cayley kernel at `1` is finite. -/
theorem freeGroupTree_rowSum_lt_top :
    rowSum (fun e' => (((fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) e' : ℝ≥0) : ℝ≥0∞)) 1 < ⊤ := by
  rw [rowSum_def]
  set T : Finset (FreeGroup (Fin 2)) :=
    (Finset.univ : Finset (Fin 2 × Bool)).image
      fun ib => if ib.2 then FreeGroup.of ib.1 else (FreeGroup.of ib.1)⁻¹
  rw [tsum_eq_sum (s := T)]
  · exact ENNReal.sum_lt_top.2 fun y _ => by split_ifs <;> simp
  · intro y hy
    have hmem : s(1, y) ∉ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} := by
      rintro ⟨g, i, hg⟩
      apply hy
      simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
      rcases Sym2.eq_iff.1 hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(i, true), by simp [← h1, h2]⟩
      · refine ⟨(i, false), ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [h2]
        exact (eq_inv_of_mul_eq_one_left h1.symm).symm
    simp only [ite_eq_right_iff.2 (fun h => absurd h hmem), ENNReal.coe_zero, ite_self]

open Classical in
/-- The off-diagonal row sum of the Cayley kernel at `1` is positive. -/
theorem freeGroupTree_rowSum_pos :
    0 < rowSum (fun e' => (((fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) e' : ℝ≥0) : ℝ≥0∞)) 1 := by
  rw [rowSum_def]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (FreeGroup.of (0 : Fin 2)))
  have hmem : s(1, FreeGroup.of (0 : Fin 2)) ∈
      {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} :=
    ⟨1, 0, by simp⟩
  simp only [ite_eq_left_iff.2 (fun h => absurd hmem h),
      ite_eq_right_iff.2 (fun h => absurd h (FreeGroup.of_ne_one _))]
  simp

/-- The vertex reached from `1` by reading a positive word from the left. -/
theorem freeGroupTree_mk_reverse_cons (i : Fin 2) (w : List (Fin 2)) :
    FreeGroup.mk (((i :: w).map fun j => (j, true)).reverse) =
      FreeGroup.mk ((w.map fun j => (j, true)).reverse) * FreeGroup.of i := by
  rw [List.map_cons, List.reverse_cons, ← FreeGroup.mul_mk]
  rfl

/-- Distinct positive words give distinct elements of the free group. -/
theorem freeGroupTree_mk_reverse_injective :
    Function.Injective fun w : List (Fin 2) =>
      FreeGroup.mk ((w.map fun j => (j, true)).reverse) := by
  have hred : ∀ w : List (Fin 2), FreeGroup.IsReduced ((w.map fun j => (j, true)).reverse) := by
    intro w
    rw [← List.map_reverse]
    induction w.reverse with
    | nil => exact FreeGroup.IsReduced.nil
    | cons a l ih =>
      cases l with
      | nil => exact FreeGroup.IsReduced.singleton
      | cons b l =>
        simp only [List.map_cons] at ih ⊢
        exact FreeGroup.isReduced_cons_cons.2 ⟨fun _ => rfl, ih⟩
  intro w w' h
  have h' := congrArg FreeGroup.toWord h
  simp only [FreeGroup.toWord_mk, (hred _).reduce_eq] at h'
  have := List.reverse_injective h'
  exact List.map_injective_iff.2 (fun a b hab => (Prod.ext_iff.1 hab).1) this

/-- Every positive word is reached from `1` by a walk of the same length along Cayley edges. -/
theorem freeGroupTree_exists_walk (w : List (Fin 2)) :
    ∃ p : (⊤ : SimpleGraph (FreeGroup (Fin 2))).Walk 1
        (FreeGroup.mk ((w.map fun j => (j, true)).reverse)),
      p.edges.length = w.length ∧ ∀ e ∈ p.edges,
        e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)} := by
  induction w with
  | nil => exact ⟨.nil, rfl, fun e he => by cases he⟩
  | cons i w ih =>
    obtain ⟨p, hlen, hp⟩ := ih
    have hadj : (⊤ : SimpleGraph (FreeGroup (Fin 2))).Adj
        (FreeGroup.mk ((w.map fun j => (j, true)).reverse))
        (FreeGroup.mk ((w.map fun j => (j, true)).reverse) * FreeGroup.of i) := by
      simp [FreeGroup.of_ne_one]
    rw [freeGroupTree_mk_reverse_cons]
    refine ⟨p.concat hadj, ?_, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.length_append, hlen]
      simp
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
    rcases he with he | he
    · exact hp e he
    · rw [List.mem_singleton] at he
      exact ⟨_, i, he⟩

open Classical in
/-- At `β ≥ 1` each Cayley edge is open with probability at least `1/2`. -/
theorem freeGroupTree_half_le {β : ℝ≥0} (hβ : 1 ≤ β) (e : Sym2 (FreeGroup (Fin 2)))
    (he : e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}) :
    (2⁻¹ : ℝ≥0∞) ≤ (unitInterval.toNNReal (intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) β e) : ℝ≥0∞) := by
  have hreal : (2⁻¹ : ℝ) ≤ 1 - Real.exp (-(β : ℝ) * 1) := by
    have h1 : Real.exp (-(β : ℝ) * 1) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (by have : (1 : ℝ) ≤ β := by exact_mod_cast hβ
                            linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp (-1) ≤ 2⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by norm_num) h2
    linarith
  have hval : ((unitInterval.toNNReal (intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) β e) : ℝ≥0) : ℝ) = 1 - Real.exp (-(β : ℝ) * 1) := by
    have hJe : (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) e = 1 := ite_eq_left_iff.2 (fun h => absurd he h)
    change 1 - Real.exp (-(β : ℝ) * (((fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) e : ℝ≥0) : ℝ)) = _
    rw [hJe, NNReal.coe_one]
  rw [← ENNReal.ofReal_coe_nnreal, hval, show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
  exact ENNReal.ofReal_le_ofReal (by simpa using hreal)

open Classical in
/-- **Infinite susceptibility.** On the free-group tree, `χ_β(1) = ⊤` for every `β ≥ 1`. -/
theorem freeGroupTree_chi_eq_top {β : ℝ≥0} (hβ : 1 ≤ β) :
    chi (intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) β) 1 = ⊤ := by
  set q := intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) β
  have hword : ∀ w : List (Fin 2),
      (2⁻¹ : ℝ≥0∞) ^ w.length ≤ tau q 1 (FreeGroup.mk ((w.map fun j => (j, true)).reverse)) := by
    intro w
    obtain ⟨p, hlen, hp⟩ := freeGroupTree_exists_walk w
    refine le_trans ?_ (prod_le_tau_of_walk q p)
    calc (2⁻¹ : ℝ≥0∞) ^ w.length ≤ (2⁻¹ : ℝ≥0∞) ^ p.edges.toFinset.card := by
          rw [← hlen]
          exact pow_le_pow_right_of_le_one' (by norm_num) (List.toFinset_card_le _)
      _ = ∏ _e ∈ p.edges.toFinset, (2⁻¹ : ℝ≥0∞) := (Finset.prod_const _).symm
      _ ≤ ∏ e ∈ p.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) :=
          Finset.prod_le_prod fun e he =>
            freeGroupTree_half_le hβ e (hp e (List.mem_toFinset.1 he))
  rw [chi_eq_tsum_tau, eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ∑' w : List (Fin 2), (2⁻¹ : ℝ≥0∞) ^ w.length := by
        rw [tsum_pow_length, show ((2 : ℕ) : ℝ≥0∞) * 2⁻¹ = 1 by
          rw [Nat.cast_ofNat, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]]
        simp
    _ ≤ ∑' w : List (Fin 2), tau q 1 (FreeGroup.mk ((w.map fun j => (j, true)).reverse)) :=
        ENNReal.tsum_le_tsum hword
    _ ≤ ∑' y, tau q 1 y :=
        ENNReal.tsum_comp_le_tsum_of_injective freeGroupTree_mk_reverse_injective _

open Classical in
/-- **The endpoint witness.** On the free-group tree, `b_χ = sSup {β | χ_β(1) < ⊤}` is a
finite positive parameter `b ≤ 1`, `χ_β(1) < ⊤` for `β < b`, and `χ_b(1) = ⊤`. -/
theorem freeGroupTree_chi_endpoint :
    ∃ b : ℝ≥0, (b : ℝ≥0∞) = sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) ''
        {β | chi (intensityProfile
          (fun e : Sym2 (FreeGroup (Fin 2)) =>
            if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
            then (1 : ℝ≥0) else 0) β) 1 < ⊤}) ∧
      0 < b ∧ b ≤ 1 ∧
      (∀ β < b, chi (intensityProfile
          (fun e : Sym2 (FreeGroup (Fin 2)) =>
            if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
            then (1 : ℝ≥0) else 0) β) 1 < ⊤) ∧
      chi (intensityProfile
          (fun e : Sym2 (FreeGroup (Fin 2)) =>
            if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
            then (1 : ℝ≥0) else 0) b) 1 = ⊤ := by
  have htr := freeGroupTree_transitive_one
  have hL := freeGroupTree_rowSum_lt_top
  have htop : ∀ β : ℝ≥0, 1 ≤ β → _ := fun β hβ => freeGroupTree_chi_eq_top (β := β) hβ
  generalize (fun e : Sym2 (FreeGroup (Fin 2)) =>
    if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
    then (1 : ℝ≥0) else 0) = J at htr hL htop ⊢
  set A := {β : ℝ≥0 | chi (intensityProfile J β) 1 < ⊤}
  set B := sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' A)
  have hA : ∀ β ∈ A, β < 1 := fun β hβ => by
    by_contra h
    exact (ne_of_lt hβ) (htop β (not_lt.1 h))
  have hB1 : B ≤ 1 := sSup_le fun _ ⟨β, hβ, hβe⟩ => by
    rw [← hβe]
    exact ENNReal.coe_le_one_iff.2 (hA β hβ).le
  have hBtop : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hB1
  have hBpos : 0 < B := lt_of_lt_of_le
    (ENNReal.inv_pos.2 hL.ne) (inv_le_chiCriticalIntensity htr hL)
  have hmono : ∀ {β β' : ℝ≥0}, β ≤ β' →
      chi (intensityProfile J β) 1 ≤ chi (intensityProfile J β') 1 := fun h =>
    chi_mono (fun e => intensityProfile_mono J h e) 1
  refine ⟨B.toNNReal, ENNReal.coe_toNNReal hBtop, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.toNNReal_pos hBpos.ne' hBtop
  · exact_mod_cast (ENNReal.coe_toNNReal hBtop ▸ hB1 : ((B.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ 1)
  · intro β hβ
    have : (β : ℝ≥0∞) < B := by
      rw [← ENNReal.coe_toNNReal hBtop]; exact_mod_cast hβ
    obtain ⟨_, ⟨β', hβ', rfl⟩, hlt⟩ := lt_sSup_iff.1 this
    exact (hmono (ENNReal.coe_le_coe.1 hlt.le)).trans_lt hβ'
  · by_contra h
    obtain ⟨ε, hε, hfin⟩ := exists_pos_chi_intensity_add_lt_top htr hL
      (lt_top_iff_ne_top.2 h)
    have hle : ((B.toNNReal + ε : ℝ≥0) : ℝ≥0∞) ≤ B := le_sSup ⟨_, hfin, rfl⟩
    have hle' : ((B.toNNReal + ε : ℝ≥0) : ℝ≥0∞) ≤ (B.toNNReal : ℝ≥0∞) := by
      rwa [ENNReal.coe_toNNReal hBtop]
    exact absurd ((add_le_iff_nonpos_right _).1 (ENNReal.coe_le_coe.1 hle')) (not_le.2 hε)

open Classical in
/-- **The endpoint witness, real parameter** (the form of `SusceptibilityDerivative.lean`):
some `b > 0` has `χ_β(1) ≠ ⊤` on `(0, b)` and `χ_b(1) = ⊤`. -/
theorem freeGroupTree_chi_endpoint_real :
    ∃ b : ℝ, 0 < b ∧
      (∀ β ∈ Ioo (0 : ℝ) b, chi (intensityProfile
          (fun e : Sym2 (FreeGroup (Fin 2)) =>
            if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
            then (1 : ℝ≥0) else 0) β.toNNReal) 1 ≠ ⊤) ∧
      chi (intensityProfile
          (fun e : Sym2 (FreeGroup (Fin 2)) =>
            if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
            then (1 : ℝ≥0) else 0) b.toNNReal) 1 = ⊤ := by
  obtain ⟨b, -, hb0, -, hlt, htop⟩ := freeGroupTree_chi_endpoint
  refine ⟨b, by exact_mod_cast hb0, fun β hβ => (hlt _ ?_).ne, by simpa using htop⟩
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hβ.1.le]
  exact hβ.2

/-! ### Non-vacuity of the blow-up hypotheses of `SusceptibilityDerivative.lean` -/

open Classical in
/-- The free-group tree satisfies every hypothesis of `inv_chi_sub_le` on `(0, b)` with
`χ_b(1) = ⊤` at the finite endpoint `b`. -/
example : ∃ b : ℝ, 0 < b ∧
    chi (intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) b.toNNReal) 1 = ⊤ ∧
    ∃ R : ℝ, 0 < R ∧ ∀ s t : ℝ, 0 < s → s ≤ t → t < b →
      1 / (chi (intensityProfile
        (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) s.toNNReal) 1).toReal -
        1 / (chi (intensityProfile
        (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) t.toNNReal) 1).toReal ≤ R * (t - s) := by
  obtain ⟨b, hb, hfin, htop⟩ := freeGroupTree_chi_endpoint_real
  have hR := freeGroupTree_rowSum_lt_top
  have hR0 := freeGroupTree_rowSum_pos
  refine ⟨b, hb, htop, _, ENNReal.toReal_pos hR0.ne' hR.ne, fun s t hs hst ht => ?_⟩
  convert inv_chi_sub_le _ freeGroupTree_transitive 1 (by convert hR.ne) le_rfl hfin hs hst ht
    using 3

/-! ### Witnesses for the endpoint theorems of `SusceptibilityEndpoint.lean` -/

open Classical in
/-- **Endpoint of finite susceptibility.** Every hypothesis of `chi_intensity_sSup_eq_top` holds on
the free-group tree, so `χ_{b_χ}(1) = ⊤` there. -/
example : chi (intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0)
      (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile
        (fun e : Sym2 (FreeGroup (Fin 2)) =>
          if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
          then (1 : ℝ≥0) else 0) β) 1 < ⊤})).toNNReal) 1 = ⊤ := by
  obtain ⟨b, hb, -⟩ := freeGroupTree_chi_endpoint
  refine chi_intensity_sSup_eq_top freeGroupTree_transitive_one
    (by convert freeGroupTree_rowSum_lt_top) ?_
  rw [← hb]
  exact ENNReal.coe_lt_top

open Classical in
/-- **Blow-up of the susceptibility.** Every hypothesis of `one_div_le_chi_of_chi_eq_top` holds on
`(0, b)` for the free-group tree, with `R > 0`. -/
example : ∃ b : ℝ, 0 < b ∧ ∃ R : ℝ, 0 < R ∧ ∀ β ∈ Ioo (0 : ℝ) b,
    1 / (R * (b - β)) ≤ (chi (intensityProfile
      (fun e : Sym2 (FreeGroup (Fin 2)) =>
        if e ∈ {f : Sym2 (FreeGroup (Fin 2)) | ∃ g i, f = s(g, g * FreeGroup.of i)}
        then (1 : ℝ≥0) else 0) β.toNNReal) 1).toReal := by
  obtain ⟨b, hb, hfin, htop⟩ := freeGroupTree_chi_endpoint_real
  have hR := freeGroupTree_rowSum_lt_top
  have hR0 := freeGroupTree_rowSum_pos
  refine ⟨b, hb, _, ENNReal.toReal_pos hR0.ne' hR.ne, fun β hβ => ?_⟩
  convert one_div_le_chi_of_chi_eq_top _ freeGroupTree_transitive 1 (by convert hR.ne)
    (by convert hR0) le_rfl hfin htop hβ using 4

end PercLib.Models

end
