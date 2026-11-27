/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
H. Duminil-Copin and V. Tassion, "A new proof of the sharpness of the phase transition for
Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016).
-/
module

public import PercLib.Percolation.Bond.BoundaryContraction
public import PercLib.Percolation.Bond.DegreeGenerating
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Models.Lattice

/-!
# Arm contraction on `ℤ^d` from one finite set

Bond percolation on `ℤ^d` with a translation-invariant profile `q` of range one in the
sup-norm. For a finite set `S ∋ 0` inside `Λ_{L - 1} = {x : ‖x‖ ≤ L - 1}`, the first-exit
inequality from `S`, translation invariance and `‖y‖ ≤ L` for every vertex `y` reached by one
step out of `S` give the contraction of the probability of reaching sup-norm distance `r`:
`P(0 ↔ {‖b‖ ≥ (k+1)L}) ≤ Φ_q(0,S) P(0 ↔ {‖b‖ ≥ kL})`.

For homogeneous nearest-neighbour percolation with `0 < p < 1`, writing
`a_N = P_p(0 ↔ ∂Λ_N)` and `φ = Φ_p(0,S) ∈ (0,1)`, this gives `a_N ≤ φ^⌊N/L⌋` for every `N`,
and `a_N ≤ e^{-cN}` for `N ≥ 1` with
`c = (2L)⁻¹ min(-log φ, -log(1 - (1-p)^{2d})) > 0`.

## Main results

* `law_exists_conn_norm_ge_le_of_translation`: translation invariance of far connections.
* `law_exists_conn_norm_ge_le_boundaryFlux_mul`: one contraction step.
* `law_exists_conn_norm_ge_le_pow`, `law_exists_conn_norm_eq_le_pow`: iteration.
* `law_exists_conn_norm_ge_one_le`: `P(0 ↔ {‖b‖ ≥ 1}) ≤ 1 - (1-p)^{2d}`.
* `toReal_law_arm_le_pow`, `exp_constant_pos`, `toReal_law_arm_le_exp`: the homogeneous
  nearest-neighbour statements.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-- One nearest-neighbour step moves at most one in the sup-norm. -/
theorem norm_sub_le_one_of_zdGraph_adj {x y : Fin d → ℤ} (h : (zdGraph d).Adj x y) :
    ‖y - x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  obtain ⟨i, hi, hj⟩ := (zdGraph_adj_iff_exists x y).1 h
  have key : |y j - x j| ≤ 1 := by
    by_cases hji : j = i
    · subst hji
      exact abs_le.2 ⟨by omega, by omega⟩
    · rw [hj j hji]
      simp
  rw [Pi.sub_apply, Int.norm_eq_abs]
  exact_mod_cast key

/-- **Translation of far connections.** For a translation-invariant profile on `ℤ^d`,
the probability that `y` is joined to some `b` with `‖b - y‖ ≥ r` is at most the probability
that `0` is joined to some `b` with `‖b‖ ≥ r` (in fact they are equal). -/
theorem law_exists_conn_norm_ge_le_of_translation (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ g e, q (Sym2.map (· + g) e) = q e) (y : Fin d → ℤ) (r : ℝ) :
    law q {ω | ∃ b, r ≤ ‖b - y‖ ∧ ω ∈ conn y b} ≤
      law q {ω | ∃ b, r ≤ ‖b‖ ∧ ω ∈ conn 0 b} := by
  have hσ : ∀ e, q (Sym2.map (Equiv.addRight y) e) = q e := fun e => hq y e
  conv_lhs => rw [← law_map_image_of_invariant (Equiv.addRight y) hσ, map_image_sym2Map_apply]
  refine measure_mono ?_
  rintro ω ⟨b, hb, hconn⟩
  refine ⟨b - y, hb, ?_⟩
  have h : Sym2.map (Equiv.addRight y) '' ω ∈
      localConn univ (Equiv.addRight y 0) (Equiv.addRight y (b - y)) := by
    rw [localConn_univ]
    simpa using hconn
  have := localConn_of_image (Equiv.addRight y) ω (S := univ) (T := univ)
    (fun _ _ => mem_univ _) h
  rwa [localConn_univ] at this

/-- **One contraction step.** Let `q` be a translation-invariant profile on `ℤ^d` whose
pairs at sup-distance more than one are closed, and let `S ∋ 0` be a finite set with
`‖x‖ ≤ L - 1` on `S`. Then
`P(0 ↔ {‖b‖ ≥ (k+1)L}) ≤ Φ_q(0,S) P(0 ↔ {‖b‖ ≥ kL})`. -/
theorem law_exists_conn_norm_ge_le_boundaryFlux_mul (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ g e, q (Sym2.map (· + g) e) = q e)
    (hrange : ∀ x y, 1 < ‖y - x‖ → q s(x, y) = 0)
    {S : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ S) {L : ℕ}
    (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1) (k : ℕ) :
    law q {ω | ∃ b, (((k + 1) * L : ℕ) : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} ≤
      boundaryFlux q S 0 * law q {ω | ∃ b, ((k * L : ℕ) : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} := by
  set B : Set (Fin d → ℤ) := {b | (((k + 1) * L : ℕ) : ℝ) ≤ ‖b‖} with hBdef
  have hB : B ⊆ univ \ (S : Set (Fin d → ℤ)) := by
    intro b hb
    refine ⟨mem_univ _, fun hbS => ?_⟩
    have h1 := hS b hbS
    have : (L : ℝ) ≤ (((k + 1) * L : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left L k.succ_pos
    simp only [hBdef, mem_ofPred_eq] at hb
    linarith
  have hfe := law_reach_le_firstExit q (S := (S : Set (Fin d → ℤ))) (A := univ) (u := 0)
    (Finset.mem_coe.2 h0) hB
  have hset : {ω : Config (Fin d → ℤ) | ∃ b, (((k + 1) * L : ℕ) : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} =
      {ω | ∃ b ∈ B, ω ∈ localConn univ 0 b} := by
    ext ω
    simp [hBdef, localConn_univ]
  rw [hset]
  refine hfe.trans ?_
  set a := law q {ω | ∃ b, ((k * L : ℕ) : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b}
  have hterm : ∀ x y, (if y ∈ (S : Set (Fin d → ℤ)) then 0 else
      law q (localConn (S : Set (Fin d → ℤ)) 0 x) * (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) *
        law q {ω | ∃ b ∈ B, ω ∈ localConn univ y b}) ≤
      (if y ∈ (S : Set (Fin d → ℤ)) then 0 else
        law q (localConn (S : Set (Fin d → ℤ)) 0 x) *
          (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) * a := by
    intro x y
    split_ifs with hy
    · simp
    by_cases hx : x ∈ S
    swap
    · rw [localConn_of_notMem_right (by simpa using hx)]
      simp
    by_cases hqxy : q s(x, y) = 0
    · simp [hqxy]
    refine mul_le_mul_right ?_ _
    have hxy : ‖y - x‖ ≤ 1 := not_lt.1 fun h => hqxy (hrange x y h)
    have hyL : ‖y‖ ≤ L := by
      have := norm_add_le (y - x) x
      rw [sub_add_cancel] at this
      linarith [hS x hx]
    refine le_trans (measure_mono ?_) (law_exists_conn_norm_ge_le_of_translation q hq y _)
    rintro ω ⟨b, hb, hω⟩
    refine ⟨b, ?_, by rwa [localConn_univ] at hω⟩
    have := norm_sub_norm_le b y
    simp only [hBdef, mem_ofPred_eq] at hb
    push_cast at hb ⊢
    linarith
  calc _ ≤ ∑' x, ∑' y, (if y ∈ (S : Set (Fin d → ℤ)) then 0 else
          law q (localConn (S : Set (Fin d → ℤ)) 0 x) *
            (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) * a :=
        ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y => by convert hterm x y
    _ = (∑' x, ∑' y, if y ∈ (S : Set (Fin d → ℤ)) then 0 else
          law q (localConn (S : Set (Fin d → ℤ)) 0 x) *
            (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) * a := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun x => ENNReal.tsum_mul_right
    _ = boundaryFlux q S 0 * a := by
        congr 1
        rw [boundaryFlux_eq, tsum_eq_sum (s := S)]
        · refine Finset.sum_congr rfl fun u _ => tsum_congr fun v => ?_
          simp only [Finset.mem_coe]
        · intro x hx
          rw [localConn_of_notMem_right (by simpa using hx)]
          simp

/-- **Iterated contraction.** Under the hypotheses of
`law_exists_conn_norm_ge_le_boundaryFlux_mul`, `P(0 ↔ {‖b‖ ≥ kL}) ≤ Φ_q(0,S)^k`. -/
theorem law_exists_conn_norm_ge_le_pow (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ g e, q (Sym2.map (· + g) e) = q e)
    (hrange : ∀ x y, 1 < ‖y - x‖ → q s(x, y) = 0)
    {S : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ S) {L : ℕ}
    (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1) (k : ℕ) :
    law q {ω | ∃ b, ((k * L : ℕ) : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} ≤ boundaryFlux q S 0 ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    rw [pow_succ']
    exact (law_exists_conn_norm_ge_le_boundaryFlux_mul q hq hrange h0 hS k).trans
      (mul_le_mul_right ih _)

/-- **Arm bound at every radius.** Under the hypotheses of
`law_exists_conn_norm_ge_le_boundaryFlux_mul`, `P(0 ↔ {‖b‖ = N}) ≤ Φ_q(0,S)^⌊N/L⌋`. -/
theorem law_exists_conn_norm_eq_le_pow (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ g e, q (Sym2.map (· + g) e) = q e)
    (hrange : ∀ x y, 1 < ‖y - x‖ → q s(x, y) = 0)
    {S : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ S) {L : ℕ}
    (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1) (N : ℕ) :
    law q {ω | ∃ b, ‖b‖ = N ∧ ω ∈ conn 0 b} ≤ boundaryFlux q S 0 ^ (N / L) := by
  refine (measure_mono fun ω hω => ?_).trans (law_exists_conn_norm_ge_le_pow q hq hrange h0 hS _)
  obtain ⟨b, hb, h⟩ := hω
  exact ⟨b, by rw [hb]; exact_mod_cast Nat.div_mul_le_self N L, h⟩

/-- **One step out of the origin.** If the pairs at `0` are open with probability at most
`p` on the nearest-neighbour bonds and are closed to every other vertex `w ≠ 0`, then
`P(0 ↔ {‖b‖ ≥ 1}) ≤ 1 - (1-p)^{2d}`. -/
theorem law_exists_conn_norm_ge_one_le (q : Sym2 (Fin d → ℤ) → unitInterval) (p : unitInterval)
    (hp : ∀ w, (zdGraph d).Adj 0 w → q s(0, w) ≤ p)
    (hq0 : ∀ w, w ≠ 0 → ¬ (zdGraph d).Adj 0 w → q s(0, w) = 0) :
    law q {ω | ∃ b, (1 : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} ≤
      1 - (1 - (unitInterval.toNNReal p : ℝ≥0∞)) ^ (2 * d) := by
  set D : Set (Config (Fin d → ℤ)) := {ω | {w | (openGraph ω).Adj 0 w}.encard = 0} with hDdef
  have hsub : {ω : Config (Fin d → ℤ) | ∃ b, (1 : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} ⊆ Dᶜ := by
    rintro ω ⟨b, hb, hconn⟩ hD
    have hb0 : b ≠ 0 := by
      rintro rfl
      norm_num at hb
    obtain ⟨w⟩ := hconn
    cases w with
    | nil => exact hb0 rfl
    | @cons _ c _ hadj _ =>
      simp only [hDdef, mem_ofPred_eq, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem] at hD
      exact hD c hadj
  have hDm : MeasurableSet D := by
    rw [hDdef, setOf_degree_eq_zero]
    have : {ω : Config (Fin d → ℤ) | ∀ w : {w // w ≠ (0 : Fin d → ℤ)}, s(0, w.1) ∉ ω} =
        ⋂ w : {w // w ≠ (0 : Fin d → ℤ)}, {ω : Config (Fin d → ℤ) | s(0, w.1) ∈ ω}ᶜ := by
      ext ω
      simp
    rw [this]
    exact MeasurableSet.iInter fun w => (measurableSet_mem _).compl
  refine (measure_mono hsub).trans ?_
  rw [prob_compl_eq_one_sub hDm]
  refine tsub_le_tsub_left ?_ _
  rw [hDdef, law_degree_eq_zero_eq_tprod]
  -- the neighbours of `0`, as a finset of the subtype
  set step : Fin d × Bool → Fin d → ℤ := fun p =>
    Function.update 0 p.1 ((0 : Fin d → ℤ) p.1 + if p.2 then 1 else -1) with hstep
  have hstep0 : ∀ p, step p ≠ 0 := by
    rintro ⟨i, b⟩ h
    have := congrFun h i
    cases b <;> simp [hstep] at this
  set F : Finset {w // w ≠ (0 : Fin d → ℤ)} :=
    Finset.univ.image fun p => ⟨step p, hstep0 p⟩ with hF
  have hFcard : F.card = 2 * d := by
    rw [hF, Finset.card_image_of_injective]
    · simp [mul_comm]
    · intro p p' h
      exact injective_update_step 0 (congrArg Subtype.val h)
  have hadjF : ∀ w : {w // w ≠ (0 : Fin d → ℤ)}, (zdGraph d).Adj 0 w.1 → w ∈ F := by
    intro w hw
    have hmem : w.1 ∈ (zdGraph d).neighborSet 0 := hw
    rw [zdGraph_neighborSet_eq] at hmem
    obtain ⟨p, hp⟩ := hmem
    exact Finset.mem_image.2 ⟨p, Finset.mem_univ _, Subtype.ext hp⟩
  rw [tprod_eq_prod (s := F)]
  · rw [← hFcard]
    refine Finset.pow_card_le_prod _ _ _ fun w hw => ?_
    have hw' : (zdGraph d).Adj 0 w.1 := by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
      rw [← SimpleGraph.mem_neighborSet, zdGraph_neighborSet_eq]
      exact ⟨p, rfl⟩
    refine tsub_le_tsub_left ?_ _
    refine ENNReal.coe_le_coe.2 ?_
    rw [← NNReal.coe_le_coe, unitInterval.coe_toNNReal, unitInterval.coe_toNNReal]
    exact hp w.1 hw'
  · intro w hw
    rw [hq0 w.1 w.2 fun h => hw (hadjF w h)]
    simp

/-! ## Homogeneous nearest-neighbour percolation -/

section Homogeneous

variable (p : unitInterval)

open Classical in
/-- The homogeneous nearest-neighbour profile is translation invariant. -/
theorem nearestNeighbour_profile_map_add (g : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    (if Sym2.map (· + g) e ∈ (zdGraph d).edgeSet then p else 0) =
      if e ∈ (zdGraph d).edgeSet then p else 0 := by
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := d) g
  have : (fun x : Fin d → ℤ => x + g) = φ := funext fun x => (hφ x).symm
  simp only [this, φ.map_mem_edgeSet_iff]

open Classical in
/-- The homogeneous nearest-neighbour profile closes every pair at sup-distance more than
one. -/
theorem nearestNeighbour_profile_eq_zero {x y : Fin d → ℤ} (h : 1 < ‖y - x‖) :
    (if s(x, y) ∈ (zdGraph d).edgeSet then p else 0) = 0 := by
  split_ifs with he
  · exact absurd h (not_lt.2 (norm_sub_le_one_of_zdGraph_adj ((SimpleGraph.mem_edgeSet _).1 he)))
  · rfl

open Classical in
/-- A positive boundary flux of `S ⊆ Λ_{L-1}` at `0` forces `0 ∈ S`, `L ≥ 1` and `d ≥ 1`. -/
theorem mem_and_one_le_of_boundaryFlux_pos {L : ℕ} {S : Finset (Fin d → ℤ)}
    (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1)
    (hφ : 0 < (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal) :
    (0 : Fin d → ℤ) ∈ S ∧ 1 ≤ L ∧ 1 ≤ d := by
  have h0 : (0 : Fin d → ℤ) ∈ S := by
    by_contra h
    rw [boundaryFlux_of_notMem _ h] at hφ
    simp at hφ
  refine ⟨h0, ?_, ?_⟩
  · have := hS 0 h0
    rw [norm_zero] at this
    exact_mod_cast (by linarith : (1 : ℝ) ≤ L)
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine absurd hφ (not_lt.2 (le_of_eq ?_))
      rw [boundaryFlux_eq, ENNReal.toReal_eq_zero_iff]
      left
      refine Finset.sum_eq_zero fun u _ => ENNReal.tsum_eq_zero.2 fun v => ?_
      have hv : v = 0 := Subsingleton.elim v 0
      simp [hv]
    · exact hd

open Classical in
/-- **Arm bound, homogeneous form.** For homogeneous nearest-neighbour percolation on `ℤ^d`
and a finite `S ⊆ Λ_{L-1}` with `φ = Φ_p(0,S) > 0`,
`a_N = P_p(0 ↔ ∂Λ_N) ≤ φ^⌊N/L⌋` for every `N`. -/
theorem toReal_law_arm_le_pow {L : ℕ} {S : Finset (Fin d → ℤ)}
    (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1)
    (hφ : 0 < (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal)
    (N : ℕ) :
    (law (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
        {ω | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b}).toReal ≤
      (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal ^ (N / L) := by
  obtain ⟨h0, -, -⟩ := mem_and_one_le_of_boundaryFlux_pos p hS hφ
  rw [← ENNReal.toReal_pow]
  refine ENNReal.toReal_mono (ENNReal.pow_ne_top (ENNReal.toReal_pos_iff.1 hφ).2.ne) ?_
  exact law_exists_conn_norm_eq_le_pow _ (nearestNeighbour_profile_map_add p)
    (fun x y h => nearestNeighbour_profile_eq_zero p h) h0 hS N

open Classical in
/-- For `N ≥ 1`, `a_N ≤ 1 - (1-p)^{2d}`. -/
theorem toReal_law_arm_le_one_sub_pow {N : ℕ} (hN : 1 ≤ N) :
    (law (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
        {ω | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b}).toReal ≤
      1 - (1 - (p : ℝ)) ^ (2 * d) := by
  have hle_p : ∀ w : Fin d → ℤ, (zdGraph d).Adj 0 w →
      (if s(0, w) ∈ (zdGraph d).edgeSet then p else 0) ≤ p := by
    intro w _
    split_ifs
    exacts [le_rfl, unitInterval.nonneg']
  have hzero : ∀ w : Fin d → ℤ, w ≠ 0 → ¬ (zdGraph d).Adj 0 w →
      (if s(0, w) ∈ (zdGraph d).edgeSet then p else 0) = 0 := by
    intro w _ hw
    split_ifs with he
    · exact absurd ((SimpleGraph.mem_edgeSet _).1 he) hw
    · rfl
  have h := law_exists_conn_norm_ge_one_le
    (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) p hle_p hzero
  have hsub : {ω : Config (Fin d → ℤ) | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b} ⊆
      {ω | ∃ b, (1 : ℝ) ≤ ‖b‖ ∧ ω ∈ conn 0 b} := fun ω ⟨b, hb, hω⟩ =>
    ⟨b, by rw [hb]; exact_mod_cast hN, hω⟩
  rw [← PercLib.Probability.coe_toNNReal_symm_eq_one_sub] at h
  have hle : ((unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞)) ^ (2 * d) ≤ 1 :=
    pow_le_one₀ zero_le (ENNReal.coe_le_one_iff.2 (by
      rw [← NNReal.coe_le_coe, unitInterval.coe_toNNReal]; exact unitInterval.le_one'))
  refine (ENNReal.toReal_mono (by simp) ((measure_mono hsub).trans h)).trans_eq ?_
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_pow]
  simp [unitInterval.coe_symm_eq]

open Classical in
/-- The exponential rate `c = (2L)⁻¹ min(-log φ, -log(1-(1-p)^{2d}))` is positive when
`0 < p < 1`, `d ≥ 1`, `L ≥ 1` and `0 < φ < 1`. -/
theorem arm_exponent_pos (hp0 : 0 < p) (hp1 : p < 1) {L : ℕ} (hL : 1 ≤ L) (hd : 1 ≤ d)
    {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    0 < 1 / (2 * (L : ℝ)) * min (-Real.log φ) (-Real.log (1 - (1 - (p : ℝ)) ^ (2 * d))) := by
  have hp0' : (0 : ℝ) < p := hp0
  have hp1' : (p : ℝ) < 1 := hp1
  have ht0 : 0 < 1 - (1 - (p : ℝ)) ^ (2 * d) := by
    have : (1 - (p : ℝ)) ^ (2 * d) < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
    linarith
  have ht1 : 1 - (1 - (p : ℝ)) ^ (2 * d) < 1 := by
    have : 0 < (1 - (p : ℝ)) ^ (2 * d) := pow_pos (by linarith) _
    linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  refine mul_pos (div_pos one_pos (by linarith)) (lt_min ?_ ?_)
  · linarith [Real.log_neg hφ0 hφ1]
  · linarith [Real.log_neg ht0 ht1]

open Classical in
/-- **Exponential arm decay at every radius.** For homogeneous nearest-neighbour percolation
on `ℤ^d` with `0 < p < 1` and a finite `S ⊆ Λ_{L-1}` with `0 < φ = Φ_p(0,S) < 1`, every
`N ≥ 1` has `a_N ≤ e^{-cN}` with `c = (2L)⁻¹ min(-log φ, -log(1-(1-p)^{2d}))`. -/
theorem toReal_law_arm_le_exp (hp0 : 0 < p) (hp1 : p < 1) {L : ℕ} {S : Finset (Fin d → ℤ)}
    (hS : ∀ x ∈ S, ‖x‖ ≤ (L : ℝ) - 1)
    (hφ0 : 0 < (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal)
    (hφ1 : (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    (law (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
        {ω | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b}).toReal ≤
      Real.exp (-(1 / (2 * (L : ℝ)) *
        min
          (-Real.log (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal)
          (-Real.log (1 - (1 - (p : ℝ)) ^ (2 * d))) * N)) := by
  obtain ⟨-, hL, hd⟩ := mem_and_one_le_of_boundaryFlux_pos p hS hφ0
  have hpow := toReal_law_arm_le_pow p hS hφ0 N
  have hone := toReal_law_arm_le_one_sub_pow (d := d) p hN
  have hc := arm_exponent_pos p hp0 hp1 hL hd hφ0 hφ1
  set φ := (boundaryFlux (fun e => if e ∈ (zdGraph d).edgeSet then p else 0) S 0).toReal
  set a := (law (fun e => if e ∈ (zdGraph d).edgeSet then p else 0)
    {ω | ∃ b : Fin d → ℤ, ‖b‖ = N ∧ ω ∈ conn 0 b}).toReal
  set t := 1 - (1 - (p : ℝ)) ^ (2 * d)
  set m := min (-Real.log φ) (-Real.log t)
  set c := 1 / (2 * (L : ℝ)) * m
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have ht0 : 0 < t := by
    have hp0' : (0 : ℝ) < p := hp0
    have : (1 - (p : ℝ)) ^ (2 * d) < 1 :=
      pow_lt_one₀ (by linarith [unitInterval.le_one p]) (by linarith) (by omega)
    simp only [t]
    linarith
  have hc2L : c * (2 * L) = m := by
    simp only [c]
    field_simp
  rcases le_or_gt (2 * L) N with hNL | hNL
  · have hk : (N : ℝ) / (2 * L) ≤ ((N / L : ℕ) : ℝ) := by
      have h1 : N < N / L * L + L := Nat.lt_div_mul_add (by omega)
      have h1' : (N : ℝ) < ((N / L : ℕ) : ℝ) * L + L := by exact_mod_cast h1
      have h2 : (2 * L : ℝ) ≤ N := by exact_mod_cast hNL
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc a ≤ φ ^ (N / L) := hpow
      _ = Real.exp (((N / L : ℕ) : ℝ) * Real.log φ) := by rw [Real.exp_nat_mul, Real.exp_log hφ0]
      _ ≤ Real.exp (-(c * N)) := by
        apply Real.exp_le_exp.2
        have hlφ : Real.log φ < 0 := Real.log_neg hφ0 hφ1
        have e1 : ((N / L : ℕ) : ℝ) * Real.log φ ≤ (N / (2 * L)) * Real.log φ :=
          mul_le_mul_of_nonpos_right hk hlφ.le
        have e2 : c ≤ (-Real.log φ) / (2 * L) := by
          simp only [c]
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
        have e3 : c * N ≤ (-Real.log φ) / (2 * L) * N :=
          mul_le_mul_of_nonneg_right e2 (Nat.cast_nonneg N)
        have e4 : (-Real.log φ) / (2 * L) * N = -((N / (2 * L)) * Real.log φ) := by ring
        linarith
  · calc a ≤ t := hone
      _ = Real.exp (Real.log t) := (Real.exp_log ht0).symm
      _ ≤ Real.exp (-(c * N)) := by
        apply Real.exp_le_exp.2
        have e1 : c * N ≤ c * (2 * L) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hNL.le) hc.le
        have e2 : c * (2 * L) ≤ -Real.log t := by
          rw [hc2L]
          exact min_le_right _ _
        linarith

end Homogeneous

end PercLib.Percolation.Bond
