/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof that one-dimensional long-range percolation with a kernel of finite first
moment has only finite clusters (wiki integrated-susceptibility, tag JK7V). No
upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Models.LongRange.CutPoints
public import PercLib.Percolation.Bond.Diagonal.Probability
public import PercLib.Percolation.Bond.Ergodic
public import PercLib.Percolation.Bond.Intensity.Defs
public import Mathlib.Analysis.PSeries

/-! # Long-range percolation on `ℤ` with finite crossing intensity

Let `J : ℕ → ℝ≥0` with `∑ r J(r) < ∞` and let `K s(a,b) = J |b - a|`. At every finite
intensity `β`, the gap-cut events `{no open pair crosses k}` have the same positive
probability for every `k`. The events "there are cuts at arbitrarily large `k`" and
"there are cuts at arbitrarily small `k`" are translation invariant and have probability
at least that of one cut, so by the ergodic zero-one law they are almost sure. Two cuts
bracket every cluster, so almost surely every cluster is finite, and both critical
intensities are `⊤`.

The same holds for a profile that equals a distance profile `p` only off the diagonal,
with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞` (`ae_cluster_finite_of_offDiagonal`).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- A translated configuration contains `s(a,b)` exactly when the original contains the
translated-back pair. -/
theorem mem_image_sym2Map_add_iff (ω : Config ℤ) (g a b : ℤ) :
    s(a, b) ∈ Sym2.map (· + g) '' ω ↔ s(a - g, b - g) ∈ ω := by
  constructor
  · rintro ⟨e, he, hmap⟩
    induction e using Sym2.ind with
    | _ c d =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
      rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa using he
      · simpa [Sym2.eq_swap] using he
  · intro h
    exact ⟨s(a - g, b - g), h, by simp⟩

/-- A cut of the translated configuration is a translated cut. -/
theorem cut_image_sym2Map_add_iff (ω : Config ℤ) (g k : ℤ) :
    (IsCut (Sym2.map (· + g) '' ω) k) ↔
      IsCut ω (k - g) := by
  constructor
  · intro h a b ha hb
    have := h (a + g) (b + g) (by omega) (by omega)
    rwa [mem_image_sym2Map_add_iff, add_sub_cancel_right, add_sub_cancel_right] at this
  · intro h a b ha hb
    rw [mem_image_sym2Map_add_iff]
    exact h (a - g) (b - g) (by omega) (by omega)

/-- Cuts at arbitrarily large positions form a measurable event. -/
theorem measurableSet_cuts_atTop :
    MeasurableSet {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} := by
  have : {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} =
      ⋂ N : ℤ, ⋃ k : ℤ, ⋃ (_ : N ≤ k),
        {ω : Config ℤ | IsCut ω k} := by
    ext ω
    simp
  rw [this]
  exact .iInter fun N => .iUnion fun k => .iUnion fun _ => measurableSet_setOf_isCut k

/-- Cuts at arbitrarily small positions form a measurable event. -/
theorem measurableSet_cuts_atBot :
    MeasurableSet {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} := by
  have : {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} =
      ⋂ N : ℤ, ⋃ k : ℤ, ⋃ (_ : k ≤ N),
        {ω : Config ℤ | IsCut ω k} := by
    ext ω
    simp
  rw [this]
  exact .iInter fun N => .iUnion fun k => .iUnion fun _ => measurableSet_setOf_isCut k

/-- **Cuts recur to the right.** For a translation-invariant profile on `ℤ` whose cut
probabilities are bounded below by a positive constant, almost surely there are cuts at
arbitrarily large positions. -/
theorem law_cuts_atTop_eq_one (q : Sym2 ℤ → unitInterval)
    (hq : ∀ x y g : ℤ, q s(x + g, y + g) = q s(x, y)) {c : ℝ≥0∞} (hc0 : 0 < c)
    (hc : ∀ k : ℤ, c ≤ law q {ω | IsCut ω k}) :
    law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} = 1 := by
  have hinv : ∀ g : ℤ, (fun ω : Config ℤ => Sym2.map (· + g) '' ω) ⁻¹'
      {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} =
      {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} := by
    intro g
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, cut_image_sym2Map_add_iff]
    constructor
    · intro h N
      obtain ⟨k, hk, hcut⟩ := h (N + g)
      exact ⟨k - g, by omega, hcut⟩
    · intro h N
      obtain ⟨k, hk, hcut⟩ := h (N - g)
      exact ⟨k + g, by omega, by rwa [add_sub_cancel_right]⟩
  have hlow : c ≤ law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} := by
    have heq : {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} =
        ⋂ N : ℤ, ⋃ k : ℤ, ⋃ (_ : N ≤ k),
          {ω : Config ℤ | IsCut ω k} := by
      ext ω
      simp
    have hdir : Directed (· ⊇ ·) fun N : ℤ => ⋃ k : ℤ, ⋃ (_ : N ≤ k),
        {ω : Config ℤ | IsCut ω k} := by
      intro M N
      refine ⟨max M N, ?_, ?_⟩ <;>
      · exact iUnion₂_mono' fun k hk => ⟨k, by omega, subset_rfl⟩
    rw [heq, hdir.measure_iInter (fun N => (MeasurableSet.iUnion fun k => .iUnion fun _ =>
      measurableSet_setOf_isCut k).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun N => (hc N).trans (measure_mono
      (subset_iUnion₂_of_subset N le_rfl subset_rfl))
  rcases law_eq_zero_or_one_of_translation_invariant q hq measurableSet_cuts_atTop hinv with
    h | h
  · rw [h] at hlow
    exact absurd hlow (not_le.mpr hc0)
  · exact h

/-- **Cuts recur to the left.** -/
theorem law_cuts_atBot_eq_one (q : Sym2 ℤ → unitInterval)
    (hq : ∀ x y g : ℤ, q s(x + g, y + g) = q s(x, y)) {c : ℝ≥0∞} (hc0 : 0 < c)
    (hc : ∀ k : ℤ, c ≤ law q {ω | IsCut ω k}) :
    law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} = 1 := by
  have hinv : ∀ g : ℤ, (fun ω : Config ℤ => Sym2.map (· + g) '' ω) ⁻¹'
      {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} =
      {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} := by
    intro g
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, cut_image_sym2Map_add_iff]
    constructor
    · intro h N
      obtain ⟨k, hk, hcut⟩ := h (N + g)
      exact ⟨k - g, by omega, hcut⟩
    · intro h N
      obtain ⟨k, hk, hcut⟩ := h (N - g)
      exact ⟨k + g, by omega, by rwa [add_sub_cancel_right]⟩
  have hlow : c ≤ law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} := by
    have heq : {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} =
        ⋂ N : ℤ, ⋃ k : ℤ, ⋃ (_ : k ≤ N),
          {ω : Config ℤ | IsCut ω k} := by
      ext ω
      simp
    have hdir : Directed (· ⊇ ·) fun N : ℤ => ⋃ k : ℤ, ⋃ (_ : k ≤ N),
        {ω : Config ℤ | IsCut ω k} := by
      intro M N
      refine ⟨min M N, ?_, ?_⟩ <;>
      · exact iUnion₂_mono' fun k hk => ⟨k, by omega, subset_rfl⟩
    rw [heq, hdir.measure_iInter (fun N => (MeasurableSet.iUnion fun k => .iUnion fun _ =>
      measurableSet_setOf_isCut k).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun N => (hc N).trans (measure_mono
      (subset_iUnion₂_of_subset N le_rfl subset_rfl))
  rcases law_eq_zero_or_one_of_translation_invariant q hq measurableSet_cuts_atBot hinv with
    h | h
  · rw [h] at hlow
    exact absurd hlow (not_le.mpr hc0)
  · exact h

/-- A cut at `k₁ < x` and a cut at `k₂ ≥ x` confine the cluster of `x` to `(k₁, k₂]`. -/
theorem cluster_subset_Ioc_of_cuts (ω : Config ℤ) {x k₁ k₂ : ℤ} (h₁ : k₁ < x) (h₂ : x ≤ k₂)
    (hc₁ : IsCut ω k₁) (hc₂ : IsCut ω k₂) :
    cluster ω x ⊆ Set.Ioc k₁ k₂ := by
  intro y hy
  have hleft := le_cut_iff_of_reachable ω k₁ hc₁ hy
  have hright := le_cut_iff_of_reachable ω k₂ hc₂ hy
  exact ⟨lt_of_not_ge fun h => (not_le.mpr h₁) (hleft.mpr h), hright.mp h₂⟩

/-- **Finite first moment forces finite clusters.** For a radial kernel `J` on `ℤ` with
`∑ r J(r) < ∞` and every finite intensity `β`, almost surely every open cluster is
finite. -/
theorem ae_cluster_finite_of_summable (J : ℕ → ℝ≥0) (K : Sym2 ℤ → ℝ≥0)
    (hK : ∀ a b, K s(a, b) = J (Int.natAbs (b - a)))
    (hJ : Summable fun r : ℕ => (r : ℝ) * (J r : ℝ)) (β : ℝ≥0) :
    ∀ᵐ ω ∂law (intensityProfile K β), ∀ x, (cluster ω x).Finite := by
  set q := intensityProfile K β with hqdef
  set p : ℕ → unitInterval := fun n => intensityProfile K β s(0, (n : ℤ)) with hpdef
  have hpval : ∀ n, (p n : ℝ) = 1 - Real.exp (-(β : ℝ) * (J n : ℝ)) := by
    intro n
    simp only [hpdef, intensityProfile, hK, sub_zero, Int.natAbs_natCast]
  have hqp : ∀ a b, q s(a, b) = p (Int.natAbs (b - a)) := by
    intro a b
    apply Subtype.ext
    rw [hpval]
    simp only [hqdef, intensityProfile, hK]
  have hinv : ∀ x y g : ℤ, q s(x + g, y + g) = q s(x, y) := by
    intro x y g
    rw [hqp, hqp, add_sub_add_right_eq_sub]
  have hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (p n).2.1)
      (fun n => ?_) (hJ.mul_left (β : ℝ))
    rw [hpval]
    have h := Real.add_one_le_exp (-(β : ℝ) * (J n : ℝ))
    have : (n : ℝ) * (1 - Real.exp (-(β : ℝ) * (J n : ℝ))) ≤ (n : ℝ) * ((β : ℝ) * J n) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
    linarith
  have hlt : ∀ n, 1 ≤ n → p n < 1 := by
    intro n _
    rw [← Subtype.coe_lt_coe, hpval, Set.Icc.coe_one]
    linarith [Real.exp_pos (-(β : ℝ) * (J n : ℝ))]
  have hc0 := law_cut_pos p q hqp hsum hlt 0
  have hc : ∀ k : ℤ, law q {ω | IsCut ω 0} ≤ law q {ω | IsCut ω k} := by
    intro k
    rw [law_cut_eq_tprod p q hqp 0, law_cut_eq_tprod p q hqp k]
  have hup := law_cuts_atTop_eq_one q hinv hc0 hc
  have hdown := law_cuts_atBot_eq_one q hinv hc0 hc
  have hupae : ∀ᵐ ω ∂law q, ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k :=
    (ae_iff_measure_eq measurableSet_cuts_atTop.nullMeasurableSet).mpr
      (by rw [hup, measure_univ])
  have hdownae : ∀ᵐ ω ∂law q, ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k :=
    (ae_iff_measure_eq measurableSet_cuts_atBot.nullMeasurableSet).mpr
      (by rw [hdown, measure_univ])
  filter_upwards [hupae, hdownae] with ω hu hd x
  obtain ⟨k₂, hk₂, hc₂⟩ := hu x
  obtain ⟨k₁, hk₁, hc₁⟩ := hd (x - 1)
  exact (Set.finite_Ioc k₁ k₂).subset
    (cluster_subset_Ioc_of_cuts ω (by omega) hk₂ hc₁ hc₂)

/-- **The root critical intensity is infinite** for a radial kernel on `ℤ` with
`∑ r J(r) < ∞`, at every root. -/
theorem rootCriticalIntensity_eq_top_of_summable (J : ℕ → ℝ≥0) (K : Sym2 ℤ → ℝ≥0)
    (hK : ∀ a b, K s(a, b) = J (Int.natAbs (b - a)))
    (hJ : Summable fun r : ℕ => (r : ℝ) * (J r : ℝ)) (x : ℤ) :
    rootCriticalIntensity K x = ⊤ := by
  rw [rootCriticalIntensity, sInf_eq_top]
  rintro b ⟨β, -, hpos⟩
  have h0 : law (intensityProfile K β) {ω | (cluster ω x).Infinite} = 0 := by
    have h := ae_cluster_finite_of_summable J K hK hJ β
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro ω hω hall
    exact hω (hall x)
  rw [h0] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **The global critical intensity is infinite** for a radial kernel on `ℤ` with
`∑ r J(r) < ∞`. -/
theorem globalCriticalIntensity_eq_top_of_summable (J : ℕ → ℝ≥0) (K : Sym2 ℤ → ℝ≥0)
    (hK : ∀ a b, K s(a, b) = J (Int.natAbs (b - a)))
    (hJ : Summable fun r : ℕ => (r : ℝ) * (J r : ℝ)) :
    globalCriticalIntensity K = ⊤ := by
  rw [globalCriticalIntensity, sInf_eq_top]
  rintro b ⟨β, -, hpos⟩
  have h0 : law (intensityProfile K β) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
    have h := ae_cluster_finite_of_summable J K hK hJ β
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    rintro ω ⟨y, hy⟩ hall
    exact hy (hall y)
  rw [h0] at hpos
  exact absurd hpos (lt_irrefl 0)

-- Non-vacuity: the power-law kernel `J(r) = r⁻³`, whose first moment `∑ r⁻²` is finite.
example (β : ℝ≥0) :
    ∀ᵐ ω ∂law (intensityProfile (Sym2.lift ⟨fun a b : ℤ =>
      (((Int.natAbs (b - a) : ℕ) : ℝ≥0) ^ 3)⁻¹, fun a b => by
        dsimp only
        rw [← Int.natAbs_neg, neg_sub]⟩) β), ∀ x, (cluster ω x).Finite := by
  refine ae_cluster_finite_of_summable (fun r => ((r : ℝ≥0) ^ 3)⁻¹) _ (fun a b => rfl) ?_ β
  have h2 : Summable fun r : ℕ => ((r : ℝ) ^ 2)⁻¹ := Real.summable_nat_pow_inv.mpr one_lt_two
  refine h2.congr fun r => ?_
  push_cast
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have : (r : ℝ) ≠ 0 := by positivity
    field_simp

-- Non-vacuity: the nearest-neighbour kernel, with both critical intensities infinite.
example (x : ℤ) :
    rootCriticalIntensity (Sym2.lift ⟨fun a b : ℤ =>
      (if Int.natAbs (b - a) = 1 then 1 else 0 : ℝ≥0), fun a b => by
        dsimp only
        rw [← Int.natAbs_neg, neg_sub]⟩) x = ⊤ ∧
    globalCriticalIntensity (Sym2.lift ⟨fun a b : ℤ =>
      (if Int.natAbs (b - a) = 1 then 1 else 0 : ℝ≥0), fun a b => by
        dsimp only
        rw [← Int.natAbs_neg, neg_sub]⟩) = ⊤ := by
  have hJ : Summable fun r : ℕ => (r : ℝ) * ((if r = 1 then 1 else 0 : ℝ≥0) : ℝ) := by
    refine summable_of_ne_finset_zero (s := {1}) fun r hr => ?_
    simp only [Finset.mem_singleton] at hr
    simp [hr]
  exact ⟨rootCriticalIntensity_eq_top_of_summable (fun r => if r = 1 then 1 else 0) _
      (fun a b => rfl) hJ x,
    globalCriticalIntensity_eq_top_of_summable (fun r => if r = 1 then 1 else 0) _
      (fun a b => rfl) hJ⟩

/-! ### Profiles given by a distance profile off the diagonal

The diagonal values of a profile do not affect the cut events, so the results above extend
to profiles that equal a distance profile only off the diagonal. -/

/-- Gap cuts only involve non-diagonal pairs, so configurations agreeing off the diagonal
have the same cuts. -/
theorem cut_iff_of_sdiff_diagSet_eq {ω ω' : Config ℤ}
    (h : ω \ Sym2.diagSet = ω' \ Sym2.diagSet) (k : ℤ) :
    IsCut ω k ↔ IsCut ω' k := by
  have key : ∀ a b : ℤ, a ≤ k → k < b → (s(a, b) ∈ ω ↔ s(a, b) ∈ ω') := by
    intro a b ha hb
    have hnd : ¬ (s(a, b) : Sym2 ℤ).IsDiag := by
      rw [Sym2.mk_isDiag_iff]; omega
    have h1 : s(a, b) ∈ ω \ Sym2.diagSet ↔ s(a, b) ∈ ω' \ Sym2.diagSet := by rw [h]
    simpa [Set.mem_sdiff, Sym2.mem_diagSet, hnd] using h1
  exact ⟨fun H a b ha hb hm => H a b ha hb ((key a b ha hb).2 hm),
    fun H a b ha hb hm => H a b ha hb ((key a b ha hb).1 hm)⟩

/-- A profile given by a distance profile off the diagonal agrees off the diagonal with
one given by that distance profile everywhere. -/
theorem exists_eq_distance_of_offDiagonal (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a))) :
    ∃ q' : Sym2 ℤ → unitInterval, (∀ a b, q' s(a, b) = p (Int.natAbs (b - a))) ∧
      ∀ e, ¬ e.IsDiag → q e = q' e := by
  classical
  refine ⟨fun e => if e.IsDiag then p 0 else q e, fun a b => ?_, fun e he => by simp [he]⟩
  by_cases hab : a = b
  · subst hab; simp
  · simp only [Sym2.mk_isDiag_iff, hab, ite_false]
    exact hq a b hab

/-- **Cuts recur to the right** for a distance profile off the diagonal (diagonal
arbitrary) with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞`. -/
theorem law_cuts_atTop_eq_one_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k} = 1 := by
  obtain ⟨q', hq', hqq'⟩ := exists_eq_distance_of_offDiagonal p q hq
  have hinv : ∀ x y g : ℤ, q' s(x + g, y + g) = q' s(x, y) := fun x y g => by
    rw [hq', hq', add_sub_add_right_eq_sub]
  rw [law_event_eq_of_offDiagonal q q' hqq' measurableSet_cuts_atTop (fun ω ω' h => by
    simp only [Set.mem_ofPred_eq, cut_iff_of_sdiff_diagSet_eq h])]
  exact law_cuts_atTop_eq_one q' hinv (law_cut_pos p q' hq' hsum hlt 0)
    fun k => by rw [law_cut_eq_tprod p q' hq' 0, law_cut_eq_tprod p q' hq' k]

/-- **Cuts recur to the left** for a distance profile off the diagonal (diagonal
arbitrary) with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞`. -/
theorem law_cuts_atBot_eq_one_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k} = 1 := by
  obtain ⟨q', hq', hqq'⟩ := exists_eq_distance_of_offDiagonal p q hq
  have hinv : ∀ x y g : ℤ, q' s(x + g, y + g) = q' s(x, y) := fun x y g => by
    rw [hq', hq', add_sub_add_right_eq_sub]
  rw [law_event_eq_of_offDiagonal q q' hqq' measurableSet_cuts_atBot (fun ω ω' h => by
    simp only [Set.mem_ofPred_eq, cut_iff_of_sdiff_diagSet_eq h])]
  exact law_cuts_atBot_eq_one q' hinv (law_cut_pos p q' hq' hsum hlt 0)
    fun k => by rw [law_cut_eq_tprod p q' hq' 0, law_cut_eq_tprod p q' hq' k]

/-- Almost surely closed gaps occur arbitrarily far to the right. -/
theorem ae_cuts_atTop_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k :=
  (ae_iff_measure_eq measurableSet_cuts_atTop.nullMeasurableSet).mpr
    (by rw [law_cuts_atTop_eq_one_of_offDiagonal p q hq hlt hsum, measure_univ])

/-- Almost surely closed gaps occur arbitrarily far to the left. -/
theorem ae_cuts_atBot_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k :=
  (ae_iff_measure_eq measurableSet_cuts_atBot.nullMeasurableSet).mpr
    (by rw [law_cuts_atBot_eq_one_of_offDiagonal p q hq hlt hsum, measure_univ])

/-- Closed gaps arbitrarily far in both directions make every cluster finite. -/
theorem cluster_finite_of_cuts_unbounded (ω : Config ℤ)
    (hu : ∀ N : ℤ, ∃ k, N ≤ k ∧ IsCut ω k)
    (hd : ∀ N : ℤ, ∃ k, k ≤ N ∧ IsCut ω k) (x : ℤ) :
    (cluster ω x).Finite := by
  obtain ⟨k₂, hk₂, hc₂⟩ := hu x
  obtain ⟨k₁, hk₁, hc₁⟩ := hd (x - 1)
  exact (Set.finite_Ioc k₁ k₂).subset (cluster_subset_Ioc_of_cuts ω (by omega) hk₂ hc₁ hc₂)

/-- Almost surely every open cluster is finite, for a distance profile off the diagonal
(diagonal arbitrary) with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞`. -/
theorem ae_cluster_finite_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite := by
  filter_upwards [ae_cuts_atTop_of_offDiagonal p q hq hlt hsum,
    ae_cuts_atBot_of_offDiagonal p q hq hlt hsum] with ω hu hd
  exact cluster_finite_of_cuts_unbounded ω hu hd

end PercLib.Models.LongRange
