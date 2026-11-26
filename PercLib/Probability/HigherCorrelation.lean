/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The insertion recursion for higher-order correlations and the correlation of nested events.
New for this project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no
upstream code is copied. Mathematical reference: E. H. Lieb and S. Sahi, *On the extension of
the FKG inequality to n functions*, J. Math. Phys. 63 (2022), Section 2.
-/
module

public import PercLib.Probability.HigherCorrelation.Defs
public import PercLib.Combinatorics.Finpartition.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The insertion recursion for higher correlations

Adding one function `f a` to a family `f i`, `i ∈ s` (`s` nonempty, `a ∉ s`) changes the higher
correlation by
`E_{s ∪ {a}}(f) = ∑_{i ∈ s} E_s(f with f i replaced by f i * f a) - (∫ f a) E_s(f)`.
The proof is the insertion of `a` into a partition of `s`, either as a new block or into an
existing block. No integrability is needed: the identity holds term by term.

For nested events `A_1 ⊆ ⋯ ⊆ A_n` of probabilities `a_1 ≤ ⋯ ≤ a_n`, the recursion gives
`E_n(1_{A_1}, …, 1_{A_n}) = a_1 ∏_{j=2}^n (j - 1 - a_j) ≥ 0`.

## Main results

* `PercLib.sum_finpartition_insert_moments`: the combinatorial recursion for an arbitrary
  moment function.
* `PercLib.higherCorrelation_insert`: the insertion recursion.
* `PercLib.higherCorrelation_pair`, `PercLib.higherCorrelation_fin_three`: the explicit forms
  for two and three functions.
* `PercLib.higherCorrelation_insert_of_eq_one`: inserting the constant function one multiplies
  the correlation by `|s| - 1` under a probability measure.
* `PercLib.higherCorrelation_indicator_of_monotoneOn`: the product formula for a nested family of
  events indexed by a finset of a linear order.
* `PercLib.higherCorrelation_indicator_fin_of_monotone`: the same for `A : Fin n → Set Ω`,
  together with its nonnegativity.
-/

@[expose] public section

open MeasureTheory Finset

namespace PercLib

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

/-- **Partition sums under insertion of a point.** For a moment function `m` on finsets,
`a ∉ s` and `s` nonempty, the signed partition sum `∑_π (-1)^{|π|-1} ∏_{B ∈ π} (|B|-1)! m B`
over `insert a s` equals the sum over partitions `P` of `s` of `(-1)^{|P|-1}` times
`∑_{t ∈ P} |t|! m (insert a t) ∏_{B ∈ P, B ≠ t} (|B|-1)! m B - m {a} ∏_{B ∈ P} (|B|-1)! m B`. -/
theorem sum_finpartition_insert_moments (m : Finset ι → ℝ) {a : ι} {s : Finset ι}
    (ha : a ∉ s) (hs : s.Nonempty) :
    ∑ Q : Finpartition (insert a s), (-1 : ℝ) ^ (#Q.parts - 1) *
        ∏ B ∈ Q.parts, (((#B - 1).factorial : ℝ) * m B) =
      ∑ P : Finpartition s, (-1 : ℝ) ^ (#P.parts - 1) *
        (∑ t ∈ P.parts, ((#t).factorial : ℝ) * m (insert a t) *
            ∏ B ∈ P.parts.erase t, (((#B - 1).factorial : ℝ) * m B) -
          m {a} * ∏ B ∈ P.parts, (((#B - 1).factorial : ℝ) * m B)) := by
  rw [Finpartition.sum_insert_eq_sum_add_sum ha]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  have hpos : 0 < #P.parts := card_pos.2 (P.parts_nonempty hs.ne_empty)
  have hins : ∀ t (ht : t ∈ P.parts), (-1 : ℝ) ^ (#(P.insertIntoPart ha t ht).parts - 1) *
      ∏ B ∈ (P.insertIntoPart ha t ht).parts, (((#B - 1).factorial : ℝ) * m B) =
      (-1 : ℝ) ^ (#P.parts - 1) * (((#t).factorial : ℝ) * m (insert a t) *
        ∏ B ∈ P.parts.erase t, (((#B - 1).factorial : ℝ) * m B)) := by
    intro t ht
    have hat : a ∉ t := P.notMem_of_mem_parts ha ht
    rw [Finpartition.card_parts_insertIntoPart, Finpartition.parts_insertIntoPart,
      prod_insert, card_insert_of_notMem hat, Nat.add_sub_cancel]
    exact fun h ↦ P.notMem_of_mem_parts ha (mem_of_mem_erase h) (mem_insert_self a t)
  rw [Finset.sum_congr rfl fun t _ ↦ hins t.1 t.2,
    Finset.sum_attach P.parts (fun t ↦ (-1 : ℝ) ^ (#P.parts - 1) *
      (((#t).factorial : ℝ) * m (insert a t) *
        ∏ B ∈ P.parts.erase t, (((#B - 1).factorial : ℝ) * m B))),
    Finpartition.card_parts_extendSingleton, Finpartition.parts_extendSingleton,
    prod_insert (P.singleton_notMem_parts ha), ← mul_sum]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hpos
  rw [hk]
  simp only [Nat.add_sub_cancel, card_singleton, Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, one_mul, zero_add, pow_succ]
  ring

/-- The factor of a block in the partition sum after the function `f i` is replaced by
`f i * f a`, for `i` in that block. -/
private theorem integral_prod_update_of_mem (μ : Measure Ω) (f : ι → Ω → ℝ) {a i : ι}
    {t : Finset ι} (hat : a ∉ t) (hi : i ∈ t) :
    ∫ ω, ∏ j ∈ t, Function.update f i (f i * f a) j ω ∂μ =
      ∫ ω, ∏ j ∈ insert a t, f j ω ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only
  rw [prod_insert hat, ← mul_prod_erase t _ hi, ← mul_prod_erase t (fun j ↦ f j ω) hi,
    Function.update_self,
    prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_erase hj)], Pi.mul_apply]
  ring

/-- The factor of a block not containing `i` is unchanged when `f i` is replaced. -/
private theorem integral_prod_update_of_notMem (μ : Measure Ω) (f : ι → Ω → ℝ) {i : ι}
    (g : Ω → ℝ) {t : Finset ι} (hi : i ∉ t) :
    ∫ ω, ∏ j ∈ t, Function.update f i g j ω ∂μ = ∫ ω, ∏ j ∈ t, f j ω ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  exact prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (by rintro rfl; exact hi hj)]

/-- **Insertion recursion for higher correlations.** For `a ∉ s` with `s` nonempty,
`E_{s ∪ {a}}(f) = ∑_{i ∈ s} E_s(f with f i replaced by f i * f a) - (∫ f a) E_s(f)`.
No integrability is needed. -/
theorem higherCorrelation_insert (μ : Measure Ω) {a : ι} {s : Finset ι} (ha : a ∉ s)
    (hs : s.Nonempty) (f : ι → Ω → ℝ) :
    higherCorrelation μ (insert a s) f =
      ∑ i ∈ s, higherCorrelation μ s (Function.update f i (f i * f a)) -
        (∫ ω, f a ω ∂μ) * higherCorrelation μ s f := by
  set m : Finset ι → ℝ := fun B ↦ ∫ ω, ∏ i ∈ B, f i ω ∂μ with hm
  rw [higherCorrelation, sum_finpartition_insert_moments m ha hs]
  simp only [higherCorrelation]
  rw [Finset.sum_comm, mul_sum, ← sum_sub_distrib]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  have hma : m {a} = ∫ ω, f a ω ∂μ := by simp [hm]
  suffices key : ∑ t ∈ P.parts, ((#t).factorial : ℝ) * m (insert a t) *
      ∏ B ∈ P.parts.erase t, (((#B - 1).factorial : ℝ) * m B) =
      ∑ i ∈ s, ∏ B ∈ P.parts, (((#B - 1).factorial : ℝ) *
        ∫ ω, ∏ j ∈ B, Function.update f i (f i * f a) j ω ∂μ) by
    rw [hma, ← mul_sum, ← key]
    ring
  -- Group the indices `i ∈ s` by the part of `P` containing them.
  have hsplit : ∀ F : ι → ℝ, ∑ i ∈ s, F i = ∑ t ∈ P.parts, ∑ i ∈ t, F i := fun F ↦ by
    have : ∑ i ∈ s, F i = ∑ i ∈ P.parts.biUnion id, F i := by rw [P.biUnion_parts]
    rw [this, sum_biUnion P.disjoint]
    rfl
  rw [hsplit]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  symm
  have hat : a ∉ t := P.notMem_of_mem_parts ha ht
  have hterm : ∀ i ∈ t, ∏ B ∈ P.parts, (((#B - 1).factorial : ℝ) *
      ∫ ω, ∏ j ∈ B, Function.update f i (f i * f a) j ω ∂μ) =
      ((#t - 1).factorial : ℝ) * m (insert a t) *
        ∏ B ∈ P.parts.erase t, (((#B - 1).factorial : ℝ) * m B) := by
    intro i hi
    rw [← mul_prod_erase P.parts _ ht, integral_prod_update_of_mem μ f hat hi]
    congr 1
    refine prod_congr rfl fun B hB ↦ ?_
    have hiB : i ∉ B := fun h ↦ ne_of_mem_erase hB
      (P.eq_of_mem_parts (mem_of_mem_erase hB) ht h hi)
    rw [integral_prod_update_of_notMem μ f _ hiB]
  rw [Finset.sum_congr rfl hterm, sum_const, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
  congr 2
  have hne : #t ≠ 0 := (card_pos.2 (P.nonempty_of_mem_parts ht)).ne'
  exact_mod_cast Nat.mul_factorial_pred hne

/-- For two functions the higher correlation is the covariance `∫ f i f j - ∫ f i ∫ f j`. -/
theorem higherCorrelation_pair (μ : Measure Ω) {i j : ι} (hij : i ≠ j) (f : ι → Ω → ℝ) :
    higherCorrelation μ {i, j} f =
      ∫ ω, f i ω * f j ω ∂μ - (∫ ω, f i ω ∂μ) * ∫ ω, f j ω ∂μ := by
  rw [higherCorrelation_insert μ (by simpa using hij) (singleton_nonempty j)]
  simp only [sum_singleton, higherCorrelation_singleton, Function.update_self, Pi.mul_apply]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)

/-- For three functions, `E_3(f_0, f_1, f_2) = 2 ∫ f_0 f_1 f_2 - ∫ f_0 f_1 ∫ f_2 - ∫ f_0 f_2 ∫ f_1
- ∫ f_1 f_2 ∫ f_0 + ∫ f_0 ∫ f_1 ∫ f_2`. -/
theorem higherCorrelation_fin_three (μ : Measure Ω) (f : Fin 3 → Ω → ℝ) :
    higherCorrelation μ univ f =
      2 * ∫ ω, f 0 ω * f 1 ω * f 2 ω ∂μ - (∫ ω, f 0 ω * f 1 ω ∂μ) * ∫ ω, f 2 ω ∂μ -
        (∫ ω, f 0 ω * f 2 ω ∂μ) * ∫ ω, f 1 ω ∂μ - (∫ ω, f 1 ω * f 2 ω ∂μ) * ∫ ω, f 0 ω ∂μ +
        (∫ ω, f 0 ω ∂μ) * (∫ ω, f 1 ω ∂μ) * ∫ ω, f 2 ω ∂μ := by
  have hu : (univ : Finset (Fin 3)) = insert 0 {1, 2} := by decide
  rw [hu, higherCorrelation_insert μ (by decide) (insert_nonempty 1 {2}),
    sum_insert (by decide), sum_singleton, higherCorrelation_pair μ (by decide),
    higherCorrelation_pair μ (by decide), higherCorrelation_pair μ (by decide)]
  simp only [Function.update_apply]
  simp only [show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte, Pi.mul_apply]
  have h1 : ∫ ω, f 1 ω * f 0 ω * f 2 ω ∂μ = ∫ ω, f 0 ω * f 1 ω * f 2 ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
  have h2 : ∫ ω, f 1 ω * (f 2 ω * f 0 ω) ∂μ = ∫ ω, f 0 ω * f 1 ω * f 2 ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
  have h3 : ∫ ω, f 1 ω * f 0 ω ∂μ = ∫ ω, f 0 ω * f 1 ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
  have h4 : ∫ ω, f 2 ω * f 0 ω ∂μ = ∫ ω, f 0 ω * f 2 ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
  rw [h1, h2, h3, h4]
  ring

/-- **Inserting the constant function one.** Under a probability measure, for `a ∉ s` with `s`
nonempty and `f a = 1`, `E_{s ∪ {a}}(f) = (|s| - 1) E_s(f)`. -/
theorem higherCorrelation_insert_of_eq_one (μ : Measure Ω) [IsProbabilityMeasure μ] {a : ι}
    {s : Finset ι} (ha : a ∉ s) (hs : s.Nonempty) (f : ι → Ω → ℝ) (h1 : f a = 1) :
    higherCorrelation μ (insert a s) f = ((#s : ℝ) - 1) * higherCorrelation μ s f := by
  rw [higherCorrelation_insert μ ha hs]
  have hupd : ∀ i, Function.update f i (f i * f a) = f := fun i ↦ by
    rw [h1, mul_one, Function.update_eq_self]
  simp_rw [hupd]
  simp only [sum_const, nsmul_eq_mul, h1, Pi.one_apply, integral_const, probReal_univ,
    smul_eq_mul, mul_one]
  ring

/-- **Correlation of nested events, indexed by a finset of a linear order.** If the events
`A j`, `j ∈ s`, are measurable and increase along `s`, then under a probability measure
`E_s(1_{A j}) = P(A j₀) ∏_{j ∈ s, j ≠ j₀} (#{k ∈ s : k < j} - P(A j))`, where `j₀` is the least
element of `s`. -/
theorem higherCorrelation_indicator_of_monotoneOn {ι : Type*} [LinearOrder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (hs : s.Nonempty) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hmono : MonotoneOn A s) :
    higherCorrelation μ s (fun i ↦ (A i).indicator 1) =
      μ.real (A (s.min' hs)) *
        ∏ j ∈ s.erase (s.min' hs), ((#(s.filter (· < j)) : ℝ) - μ.real (A j)) := by
  induction s using Finset.induction_on_max with
  | empty => exact absurd hs (by simp)
  | insert b s hlt ih =>
    have hbs : b ∉ s := fun h ↦ lt_irrefl b (hlt b h)
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp [integral_indicator_one (hA b (mem_insert_self b ∅))]
    have hA' : ∀ i ∈ s, MeasurableSet (A i) := fun i hi ↦ hA i (mem_insert_of_mem hi)
    have hmono' : MonotoneOn A s := hmono.mono (subset_insert b s)
    have hmin : (insert b s).min' hs = s.min' hs' := by
      refine le_antisymm (min'_le _ _ (mem_insert_of_mem (min'_mem s hs'))) ?_
      refine le_min' _ _ _ fun y hy ↦ ?_
      rcases mem_insert.1 hy with rfl | hy
      · exact (hlt _ (min'_mem s hs')).le
      · exact min'_le s y hy
    rw [higherCorrelation_insert μ hbs hs', ih hs' hA' hmono', hmin]
    have hupd : ∀ i ∈ s, (A i).indicator (1 : Ω → ℝ) * (A b).indicator 1 =
        (A i).indicator 1 := fun i hi ↦ by
      have hsub : A i ⊆ A b := hmono (mem_insert_of_mem hi) (mem_insert_self b s) (hlt i hi).le
      ext ω
      by_cases hω : ω ∈ A i
      · simp [hω, hsub hω]
      · simp [hω]
    have hcongr : ∀ i ∈ s, higherCorrelation μ s
        (Function.update (fun j ↦ (A j).indicator 1) i
          ((A i).indicator 1 * (A b).indicator 1)) =
        higherCorrelation μ s (fun j ↦ (A j).indicator 1) := fun i hi ↦ by
      rw [hupd i hi, Function.update_eq_self]
    rw [Finset.sum_congr rfl hcongr, ih hs' hA' hmono', sum_const, nsmul_eq_mul,
      integral_indicator_one (hA b (mem_insert_self b s))]
    have hmb : s.min' hs' ≠ b := (hlt _ (min'_mem s hs')).ne
    rw [erase_insert_of_ne hmb.symm, prod_insert (fun h ↦ hbs (mem_of_mem_erase h))]
    have hcard : (insert b s).filter (· < b) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxb⟩
        · exact absurd hxb (lt_irrefl _)
        · exact hx
      · exact fun hx ↦ ⟨Or.inr hx, hlt x hx⟩
    have hfilt : ∀ j ∈ s.erase (s.min' hs'), (insert b s).filter (· < j) = s.filter (· < j) :=
      fun j hj ↦ by
        rw [filter_insert]
        simp [not_lt.2 (hlt j (mem_of_mem_erase hj)).le]
    rw [hcard, prod_congr rfl fun j hj ↦
      congrArg (fun x : Finset ι ↦ (#x : ℝ) - μ.real (A j)) (hfilt j hj).symm]
    ring

/-- **Correlation of nested events.** If `A 0 ⊆ A 1 ⊆ ⋯ ⊆ A (n-1)` are measurable events
of a probability space with probabilities `a_j = P(A j)`, then
`E_n(1_{A 0}, …, 1_{A (n-1)}) = a_0 ∏_{j=1}^{n-1} (j - a_j)`, and this is nonnegative. In the
one-based indexing `A_1 ⊆ ⋯ ⊆ A_n` this reads `a_1 ∏_{j=2}^n (j - 1 - a_j) ≥ 0`. -/
theorem higherCorrelation_indicator_fin_of_monotone (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A) :
    higherCorrelation μ univ (fun i ↦ (A i).indicator 1) =
        μ.real (A ⟨0, hn⟩) *
          ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j)) ∧
      0 ≤ μ.real (A ⟨0, hn⟩) *
          ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j)) := by
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have hmin : (univ : Finset (Fin n)).min' hne = ⟨0, hn⟩ :=
    le_antisymm (min'_le _ _ (mem_univ _)) (le_min' _ _ _ fun y _ ↦ Fin.le_def.2 (Nat.zero_le _))
  have hcard : ∀ j : Fin n, (#((univ : Finset (Fin n)).filter (· < j)) : ℝ) = (j : ℕ) :=
    fun j ↦ by rw [filter_gt_eq_Iio, Fin.card_Iio]
  refine ⟨?_, ?_⟩
  · rw [higherCorrelation_indicator_of_monotoneOn μ univ hne A (fun i _ ↦ hA i)
      (hmono.monotoneOn _), hmin]
    simp only [hcard]
  · refine mul_nonneg measureReal_nonneg (prod_nonneg fun j hj ↦ ?_)
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.2 fun h ↦ (ne_of_mem_erase hj) (Fin.ext h)
    have : μ.real (A j) ≤ 1 := measureReal_le_one
    have : (1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast hj1
    linarith

/-- The correlation of nested events is `a_0 ∏_{j ≥ 1} (j - a_j)`. -/
theorem higherCorrelation_indicator_fin_eq_of_monotone (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A) :
    higherCorrelation μ univ (fun i ↦ (A i).indicator 1) =
      μ.real (A ⟨0, hn⟩) *
        ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j)) :=
  (higherCorrelation_indicator_fin_of_monotone μ hn A hA hmono).1

/-- The nested-event product `a_0 ∏_{j ≥ 1} (j - a_j)` is nonnegative. -/
theorem measureReal_mul_prod_sub_measureReal_nonneg_of_monotone (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (A : Fin n → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A) :
    0 ≤ μ.real (A ⟨0, hn⟩) *
        ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j)) :=
  (higherCorrelation_indicator_fin_of_monotone μ hn A hA hmono).2

end PercLib
