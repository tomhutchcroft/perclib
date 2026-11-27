/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Moment determinacy of finite laws and of the block-size multiset of a random finite partition.
New for this project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no
upstream code is copied.
Mathematical reference: the finite multiplicative coalescent, T. Hutchcroft, *On the volume of
clusters in hierarchical percolation* (2022), Section 2 (discussion after (2.4)).
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Mixed power-sum moments and the block-size law of a random partition

For a finite multiset of positive integers bounded by `n`, the power sums of orders `1, …, n`
determine the multiset (a Vandermonde argument). For laws on a finite type, functions that
separate points determine the law through the expectations of all their monomials (each point
indicator is a product of affine functions of the separating family). Together: for a random
partition of a finite set with `N` points, the expectations of all products of the power sums
`S_p = ∑_{blocks b} |b|^p`, `2 ≤ p ≤ N`, determine the law of the multiset of block sizes, but
not the law of the labelled partition.

## Main results

* `Multiset.eq_of_sum_map_pow_eq`: power sums of orders `1, …, n` determine a multiset with
  elements in `[1, n]`.
* `PMF.map_eq_map_of_sum_prod_pow_eq`: if a finite family of functions separates the values of
  `φ`, equal monomial moments give equal laws of `φ`.
* `Finpartition.map_parts_card_eq_of_sum_prod_pow_eq`: mixed moments of `S_2, …, S_N` determine
  the law of the block-size multiset.
* `Finpartition.exists_pmf_ne_of_sum_prod_pow_eq`: they do not determine the labelled law.
-/

@[expose] public section
noncomputable section

open Finset

namespace Multiset

/-- A power sum of a multiset with elements in `[1, n]`, written over the counts of the values
`1, …, n`. -/
theorem cast_sum_map_pow_eq_sum_fin {n : ℕ} {s : Multiset ℕ} (hs : ∀ a ∈ s, a ∈ Finset.Icc 1 n)
    (p : ℕ) :
    (((s.map (· ^ p)).sum : ℕ) : ℝ) =
      ∑ i : Fin n, ((i : ℝ) + 1) ^ p * (s.count ((i : ℕ) + 1) : ℝ) := by
  classical
  rw [Finset.sum_multiset_map_count]
  push_cast
  rw [Finset.sum_subset (s₂ := Finset.Icc 1 n) (fun a ha => hs a (Multiset.mem_toFinset.1 ha))
    (fun a _ ha => by simp [Multiset.count_eq_zero.2 (fun h => ha (Multiset.mem_toFinset.2 h))])]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) ^ p * (s.count (i + 1) : ℝ)),
    show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by ext; simp,
    Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun i _ => ?_
  rw [nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, add_comm 1 i]
  push_cast
  ring

/-- Power sums of orders `1, …, n` determine a multiset of natural numbers with elements in
`[1, n]`. -/
theorem eq_of_sum_map_pow_eq {n : ℕ} {s t : Multiset ℕ} (hs : ∀ a ∈ s, a ∈ Finset.Icc 1 n)
    (ht : ∀ a ∈ t, a ∈ Finset.Icc 1 n)
    (h : ∀ p ∈ Finset.Icc 1 n, (s.map (· ^ p)).sum = (t.map (· ^ p)).sum) : s = t := by
  classical
  set v : Fin n → ℝ := fun i => (i : ℝ) + 1 with hv
  set d : Fin n → ℝ := fun i =>
    v i * ((s.count ((i : ℕ) + 1) : ℝ) - (t.count ((i : ℕ) + 1) : ℝ)) with hd
  have hinj : Function.Injective v := by
    intro i j hij
    simp only [hv, add_left_inj, Nat.cast_inj] at hij
    exact Fin.ext hij
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hinj
  have hzero : Matrix.vecMul d (Matrix.vandermonde v) = 0 := by
    funext j
    have hp : (j : ℕ) + 1 ∈ Finset.Icc 1 n := by simp [Nat.succ_le_of_lt j.isLt]
    have hsum := congrArg (fun m : ℕ => (m : ℝ)) (h _ hp)
    simp only [cast_sum_map_pow_eq_sum_fin hs, cast_sum_map_pow_eq_sum_fin ht] at hsum
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, hd, hv]
    rw [← sub_eq_zero] at hsum
    rw [← hsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hd0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hzero
  refine Multiset.ext.2 fun a => ?_
  by_cases ha : a ∈ Finset.Icc 1 n
  · obtain ⟨ha1, han⟩ := Finset.mem_Icc.1 ha
    have hi := congrFun hd0 ⟨a - 1, by omega⟩
    simp only [hd, hv, Pi.zero_apply, mul_eq_zero, sub_eq_zero] at hi
    have ha' : a - 1 + 1 = a := by omega
    rcases hi with hi | hi
    · exact absurd hi (by positivity)
    · simpa [ha'] using hi
  · rw [Multiset.count_eq_zero.2 (fun h => ha (hs a h)),
      Multiset.count_eq_zero.2 (fun h => ha (ht a h))]

end Multiset

namespace PMF

variable {β γ ι : Type*} [Fintype β]

/-- Equal monomial moments of a finite family `g` of functions on `γ` (evaluated along `φ`) give
equal expectations of `m_k · F` for an `F` that is one at `c₀`, zero on a finite set `Y` of
values separated from `c₀`, and a product of affine functions of the family. -/
theorem exists_indicator_of_sum_prod_pow_eq (μ ν : PMF β) (φ : β → γ) (I : Finset ι)
    (g : ι → γ → ℝ)
    (h : ∀ k : ι → ℕ, ∑ b, (μ b).toReal * ∏ i ∈ I, g i (φ b) ^ k i =
      ∑ b, (ν b).toReal * ∏ i ∈ I, g i (φ b) ^ k i)
    (c₀ : γ) (Y : Finset γ) (hY : ∀ y ∈ Y, ∃ i ∈ I, g i y ≠ g i c₀) :
    ∃ F : γ → ℝ, (∀ k : ι → ℕ, ∑ b, (μ b).toReal * ((∏ i ∈ I, g i (φ b) ^ k i) * F (φ b)) =
      ∑ b, (ν b).toReal * ((∏ i ∈ I, g i (φ b) ^ k i) * F (φ b))) ∧ F c₀ = 1 ∧
      ∀ y ∈ Y, F y = 0 := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun k => by simpa using h k, rfl, by simp⟩
  | insert y Y _ ih =>
    obtain ⟨F, hF, hF1, hF0⟩ := ih fun z hz => hY z (Finset.mem_insert_of_mem hz)
    obtain ⟨i, hi, hne⟩ := hY y (Finset.mem_insert_self y Y)
    have hden : g i c₀ - g i y ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    refine ⟨fun z => F z * ((g i z - g i y) / (g i c₀ - g i y)), fun k => ?_, ?_, ?_⟩
    · have hmono : ∀ x : γ, ∏ j ∈ I, g j x ^ (k + Pi.single i 1 : ι → ℕ) j =
          (∏ j ∈ I, g j x ^ k j) * g i x := by
        intro x
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj])
          (fun h' => absurd hi h')]
        simp
      have key : ∀ ρ : PMF β, ∑ b, (ρ b).toReal * ((∏ j ∈ I, g j (φ b) ^ k j) *
          (F (φ b) * ((g i (φ b) - g i y) / (g i c₀ - g i y)))) =
          ((∑ b, (ρ b).toReal * ((∏ j ∈ I, g j (φ b) ^ (k + Pi.single i 1 : ι → ℕ) j) * F (φ b))) -
            g i y * ∑ b, (ρ b).toReal * ((∏ j ∈ I, g j (φ b) ^ k j) * F (φ b))) /
            (g i c₀ - g i y) := by
        intro ρ
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hmono]
        field_simp
      rw [key μ, key ν, hF, hF]
    · simp [hF1, hden]
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · simp
      · simp [hF0 z hz]

/-- **Moment determinacy of finite laws.** Let `φ : β → γ` on a finite type and let `g i`,
`i ∈ I`, be finitely many real functions on `γ` that separate the values of `φ`. If two laws on
`β` give the same expectation to every monomial `∏_{i ∈ I} g i (φ ·) ^ k i`, then the laws of
`φ` agree. -/
theorem map_eq_map_of_sum_prod_pow_eq (μ ν : PMF β) (φ : β → γ) (I : Finset ι)
    (g : ι → γ → ℝ) (hsep : ∀ x y : β, φ x ≠ φ y → ∃ i ∈ I, g i (φ x) ≠ g i (φ y))
    (h : ∀ k : ι → ℕ, ∑ b, (μ b).toReal * ∏ i ∈ I, g i (φ b) ^ k i =
      ∑ b, (ν b).toReal * ∏ i ∈ I, g i (φ b) ^ k i) :
    μ.map φ = ν.map φ := by
  classical
  ext c₀
  by_cases hc : ∃ b₀, φ b₀ = c₀
  swap
  · push Not at hc
    simp [PMF.map_apply, fun b => (hc b).symm]
  obtain ⟨b₀, rfl⟩ := hc
  set Y : Finset γ := (Finset.univ.image φ).erase (φ b₀)
  have hY : ∀ y ∈ Y, ∃ i ∈ I, g i y ≠ g i (φ b₀) := by
    intro y hy
    obtain ⟨hyc, hy⟩ := Finset.mem_erase.1 hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
    exact hsep b b₀ hyc
  obtain ⟨F, hF, hF1, hF0⟩ := exists_indicator_of_sum_prod_pow_eq μ ν φ I g h (φ b₀) Y hY
  have hFb : ∀ b, F (φ b) = if φ b₀ = φ b then 1 else 0 := by
    intro b
    split_ifs with hb
    · rw [← hb, hF1]
    · exact hF0 _ (Finset.mem_erase.2 ⟨Ne.symm hb, Finset.mem_image_of_mem φ (by simp)⟩)
  have hval : ∀ ρ : PMF β, ((ρ.map φ) (φ b₀)).toReal =
      ∑ b, (ρ b).toReal * ((∏ i ∈ I, g i (φ b) ^ (0 : ι → ℕ) i) * F (φ b)) := by
    intro ρ
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun b _ => by
      split_ifs <;> simp [ρ.apply_ne_top])]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hFb]
    split_ifs <;> simp
  have hreal := (hval μ).trans ((hF 0).trans (hval ν).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 hreal

end PMF

namespace Finpartition

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The block-size multiset of a partition of a finite set has elements in `[1, |α|]`. -/
theorem mem_Icc_of_mem_map_parts_card (P : Finpartition (univ : Finset α)) {a : ℕ}
    (ha : a ∈ P.parts.val.map Finset.card) : a ∈ Icc 1 (Fintype.card α) := by
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
  refine Finset.mem_Icc.2 ⟨Finset.card_pos.2 (P.nonempty_of_mem_parts hb), ?_⟩
  exact Finset.card_le_univ b

/-- The power sum `S_p = ∑_b |b|^p` of a partition is the power sum of its block-size
multiset. -/
theorem sum_parts_card_pow_eq (P : Finpartition (univ : Finset α)) (p : ℕ) :
    ∑ b ∈ P.parts, b.card ^ p = ((P.parts.val.map Finset.card).map (· ^ p)).sum := by
  rw [Multiset.map_map]
  rfl

/-- The power sums `S_p = ∑_b |b|^p`, `2 ≤ p ≤ |α|`, determine the block-size multiset of a
partition of a finite set `α`. -/
theorem map_parts_card_eq_of_sum_pow_eq {P Q : Finpartition (univ : Finset α)}
    (h : ∀ p ∈ Icc 2 (Fintype.card α), ∑ b ∈ P.parts, b.card ^ p = ∑ b ∈ Q.parts, b.card ^ p) :
    P.parts.val.map Finset.card = Q.parts.val.map Finset.card := by
  refine Multiset.eq_of_sum_map_pow_eq (fun _ ha => P.mem_Icc_of_mem_map_parts_card ha)
    (fun _ ha => Q.mem_Icc_of_mem_map_parts_card ha) fun p hp => ?_
  rw [← sum_parts_card_pow_eq, ← sum_parts_card_pow_eq]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp only [pow_one, P.sum_card_parts, Q.sum_card_parts]
  · exact h p (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hp).1; omega,
      (Finset.mem_Icc.1 hp).2⟩)

/-- **Mixed mass moments determine the block-size law.** For two laws of a random partition of
a finite set `α` with `N = |α|` points, if all products of the power sums
`S_p = ∑_b |b|^p`, `2 ≤ p ≤ N`, have the same expectation, then the laws of the multiset of
block sizes agree. -/
theorem map_parts_card_eq_of_sum_prod_pow_eq (μ ν : PMF (Finpartition (univ : Finset α)))
    (h : ∀ k : ℕ → ℕ,
      ∑ P, (μ P).toReal *
          ∏ p ∈ Icc 2 (Fintype.card α), ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p =
        ∑ P, (ν P).toReal *
          ∏ p ∈ Icc 2 (Fintype.card α), ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p) :
    μ.map (fun P => P.parts.val.map Finset.card) =
      ν.map (fun P => P.parts.val.map Finset.card) := by
  refine PMF.map_eq_map_of_sum_prod_pow_eq μ ν _ (Icc 2 (Fintype.card α))
    (fun p s => (((s.map (· ^ p)).sum : ℕ) : ℝ)) (fun P Q hPQ => ?_) ?_
  · by_contra hcon
    push Not at hcon
    refine hPQ (map_parts_card_eq_of_sum_pow_eq fun p hp => ?_)
    rw [sum_parts_card_pow_eq, sum_parts_card_pow_eq]
    exact_mod_cast hcon p hp
  · intro k
    simpa only [sum_parts_card_pow_eq] using h k

/-- The two partitions `{{0, 1}, {2}}` and `{{0, 2}, {1}}` of `Fin 3`, as partitions given by
the fibres of `![0, 0, 1]` and of `![0, 1, 0]`. -/
theorem exists_ne_map_parts_card_eq :
    ∃ P Q : Finpartition (univ : Finset (Fin 3)), P ≠ Q ∧
      P.parts.val.map Finset.card = Q.parts.val.map Finset.card := by
  let P := @ofSetoid _ _ _ (Setoid.ker ![(0 : Fin 2), 0, 1])
    (fun a b => inferInstanceAs (Decidable (_ = _)))
  let Q := @ofSetoid _ _ _ (Setoid.ker ![(0 : Fin 2), 1, 0])
    (fun a b => inferInstanceAs (Decidable (_ = _)))
  exact ⟨P, Q, by decide, by decide⟩

/-- **Mixed moments do not determine the labelled law.** There are two different laws of a
random partition of `Fin 3` with the same expectation of every product of the power sums
`S_p = ∑_b |b|^p`, `2 ≤ p ≤ 3`. -/
theorem exists_pmf_ne_of_sum_prod_pow_eq :
    ∃ μ ν : PMF (Finpartition (univ : Finset (Fin 3))), μ ≠ ν ∧ ∀ k : ℕ → ℕ,
      ∑ P, (μ P).toReal * ∏ p ∈ Icc 2 3, ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p =
      ∑ P, (ν P).toReal * ∏ p ∈ Icc 2 3, ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p := by
  classical
  obtain ⟨P, Q, hPQ, hmap⟩ := exists_ne_map_parts_card_eq
  refine ⟨PMF.pure P, PMF.pure Q, fun h => hPQ (by simpa using congrArg PMF.support h), ?_⟩
  intro k
  have hpure : ∀ (R : Finpartition (univ : Finset (Fin 3))) (f : Finpartition univ → ℝ),
      ∑ P', ((PMF.pure R) P').toReal * f P' = f R := by
    intro R f
    rw [Finset.sum_eq_single R (fun b _ hb => by simp [PMF.pure_apply, hb]) (by simp)]
    simp [PMF.pure_apply]
  rw [hpure, hpure]
  simp only [sum_parts_card_pow_eq, hmap]

end Finpartition
