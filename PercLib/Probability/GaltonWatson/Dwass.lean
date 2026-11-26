/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-26. Reference: M. Dwass, *The total progeny in a branching
process and a related random walk*, J. Appl. Probab. 6 (1969) 682–686; the generation-by-
generation induction follows R. van der Hofstad and M. Keane, *An elementary proof of the
hitting time theorem*, Amer. Math. Monthly 115 (2008) 753–756. No upstream code is copied.
-/
module

public import PercLib.Probability.GaltonWatson
public import Mathlib.RingTheory.PowerSeries.Derivative

/-! # Dwass's formula for the total progeny

Let `T_k` be the total progeny of a Galton–Watson process with offspring law `p` started from
`k ≥ 1` ancestors, and let `S_n` be a sum of `n` independent offspring variables. Then

`n · P(T_k = n) = k · P(S_n = n - k)` for `k ≤ n`,

which for one ancestor is Dwass's formula `P(T = n) = n⁻¹ P(S_n = n - 1)`.

The proof is an induction on `n` over the first generation. The first generation of `k`
ancestors has `S_k` individuals, independent of the later generations, which form a process
started from `S_k` ancestors with the same law. Writing `φ` for the generating series of `p`,
`P(S_k = m)` is the coefficient of `X^m` in `φ^k`, and the inductive step is the identity
`(k + r) · X (φ^k)' φ^r = k · X (φ^(k+r))'` of formal power series.

## Main results

* `measure_sum_range_eq_coeff_pow`: the law of a sum of `k` independent copies of `p` is the
  coefficient sequence of `φ^k`.
* `measurePreserving_shift_galtonWatsonMeasure`, `measure_preimage_eval_zero_inter_shift`:
  the later generations are a copy of the process, independent of the first generation.
* `totalProgenyFrom_eq_add_shift`: the first-generation decomposition of the total progeny.
* `natCast_mul_galtonWatsonMeasure_totalProgenyFrom`: the hitting-time identity for `k`
  ancestors.
* `galtonWatsonMeasure_totalProgeny_eq`: Dwass's formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory PowerSeries
open scoped ENNReal

namespace PercLib.Probability

/-! ### Formal power series -/

theorem PowerSeries.coeff_X_mul_derivative {R : Type*} [CommSemiring R] (f : R⟦X⟧) (m : ℕ) :
    coeff m (X * d⁄dX f) = m * coeff m f := by
  cases m with
  | zero => simp
  | succ m => rw [coeff_succ_X_mul, coeff_derivative, mul_comm]; push_cast; ring

/-- The power-series identity behind the inductive step of the hitting-time theorem:
`(k + r) · X (f^k)' f^r = k · X (f^(k+r))'` for `k ≥ 1`. -/
theorem PowerSeries.natCast_mul_X_mul_derivative_pow_mul_pow {R : Type*} [CommSemiring R]
    (f : R⟦X⟧) {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    ((k + r : ℕ) : R⟦X⟧) * (X * d⁄dX (f ^ k) * f ^ r) = (k : R⟦X⟧) * (X * d⁄dX (f ^ (k + r))) := by
  rw [derivative_pow, derivative_pow]
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show k + 1 + r - 1 = k + r by omega, Nat.add_sub_cancel, pow_add]
  push_cast
  ring

/-! ### Sums of independent offspring variables -/

section Sums

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : PMF ℕ} {ξ : ℕ → Ω → ℕ}

/-- **The law of a sum of independent offspring variables.** If `ξ₀, ξ₁, …` are independent
with law `p`, then `P(ξ₀ + ⋯ + ξ_{k-1} = m)` is the coefficient of `X^m` in `φ^k`, where
`φ = ∑ⱼ p(j) Xʲ`. -/
theorem measure_sum_range_eq_coeff_pow [IsProbabilityMeasure P] (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p.toMeasure) (k m : ℕ) :
    P {ω | ∑ i ∈ Finset.range k, ξ i ω = m} = coeff m (PowerSeries.mk (fun j => p j) ^ k) := by
  classical
  induction k generalizing m with
  | zero =>
    by_cases hm : m = 0
    · subst hm; simp
    · simp [hm, Ne.symm hm, coeff_one]
  | succ k ih =>
    have hset : {ω | ∑ i ∈ Finset.range (k + 1), ξ i ω = m} =
        ⋃ q ∈ Finset.antidiagonal m, ((fun ω => ∑ i ∈ Finset.range k, ξ i ω) ⁻¹' {q.1} ∩
          ξ k ⁻¹' {q.2}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Finset.mem_antidiagonal, Finset.sum_range_succ, exists_prop]
      constructor
      · intro h; exact ⟨(_, _), h, rfl, rfl⟩
      · rintro ⟨q, hq, h1, h2⟩; rw [h1, h2]; exact hq
    have hS : Measurable fun ω => ∑ i ∈ Finset.range k, ξ i ω :=
      Finset.measurable_sum _ fun i _ => hξ i
    have hindk : IndepFun (fun ω => ∑ i ∈ Finset.range k, ξ i ω) (ξ k) P := by
      have := hind.indepFun_finsetSum_of_notMem hξ (s := Finset.range k) (i := k) (by simp)
      convert this using 1
      ext ω; simp
    rw [hset, measure_biUnion_finset]
    · rw [pow_succ, coeff_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hindk.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
        (measurableSet_singleton _), coeff_mk, ← Measure.map_apply (hξ k)
        (measurableSet_singleton _), hlaw, PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton _)]
      exact congrArg (· * p q.2) (ih q.1)
    · intro q _ q' _ hne
      exact Set.disjoint_left.2 fun ω h1 h2 =>
        hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
    · exact fun q _ => (hS (measurableSet_singleton _)).inter (hξ k (measurableSet_singleton _))

end Sums

variable (p : PMF ℕ)

/-- The first generation of `k` ancestors in law: the sum of `k` offspring variables. -/
theorem infinitePi_sum_range_eq_coeff_pow (k m : ℕ) :
    Measure.infinitePi (fun _ : ℕ => p.toMeasure) {x : ℕ → ℕ | ∑ j ∈ Finset.range k, x j = m} =
      coeff m (PowerSeries.mk (fun j => p j) ^ k) :=
  measure_sum_range_eq_coeff_pow (ξ := fun i (x : ℕ → ℕ) => x i) (fun i => measurable_pi_apply i)
    (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi _ i).map_eq) k m

/-! ### The first-generation decomposition -/

/-- The process started from `k` ancestors, after one generation, is the process started from
the `S_k = ∑_{j<k} ξ_{0,j}` children, driven by the later offspring variables. -/
theorem generationSizeFrom_succ_eq_shift (k n : ℕ) (ω : ℕ → ℕ → ℕ) :
    generationSizeFrom k (n + 1) ω =
      generationSizeFrom (∑ j ∈ Finset.range k, ω 0 j) n fun i => ω (i + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [generationSizeFrom_succ k (n + 1), ih]; rfl

/-- **First-generation decomposition of the total progeny**: `T_k = k + T_{S_k} ∘ shift`. -/
theorem totalProgenyFrom_eq_add_shift (k : ℕ) (ω : ℕ → ℕ → ℕ) :
    totalProgenyFrom k ω =
      k + totalProgenyFrom (∑ j ∈ Finset.range k, ω 0 j) fun i => ω (i + 1) := by
  rw [totalProgenyFrom, tsum_eq_zero_add' ENNReal.summable, generationSizeFrom_zero]
  simp only [generationSizeFrom_succ_eq_shift]
  rfl

/-- The later generations of offspring variables have the Galton–Watson law. -/
theorem measurePreserving_shift_galtonWatsonMeasure :
    MeasurePreserving (fun (ω : ℕ → ℕ → ℕ) (i : ℕ) => ω (i + 1)) (galtonWatsonMeasure p)
      (galtonWatsonMeasure p) := by
  refine ⟨by fun_prop, ?_⟩
  rw [galtonWatsonMeasure]
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have : (fun (ω : ℕ → ℕ → ℕ) (i : ℕ) => ω (i + 1)) ⁻¹' Set.pi (↑s) t =
      Set.pi ↑(s.map ⟨Nat.succ, Nat.succ_injective⟩) fun i => t (i - 1) := by
    ext ω; simp
  rw [this]
  refine (Measure.infinitePi_pi (μ := fun _ : ℕ => Measure.infinitePi fun _ : ℕ => p.toMeasure)
    (s := s.map ⟨Nat.succ, Nat.succ_injective⟩) (t := fun i => t (i - 1))
    fun i _ => ht _).trans ?_
  rw [Finset.prod_map]
  simp

/-- The first generation of offspring variables is independent of the later ones. -/
theorem measure_preimage_eval_zero_inter_shift {A : Set (ℕ → ℕ)} {B : Set (ℕ → ℕ → ℕ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    galtonWatsonMeasure p ((fun ω : ℕ → ℕ → ℕ => ω 0) ⁻¹' A ∩
        (fun (ω : ℕ → ℕ → ℕ) (i : ℕ) => ω (i + 1)) ⁻¹' B) =
      galtonWatsonMeasure p ((fun ω : ℕ → ℕ → ℕ => ω 0) ⁻¹' A) *
        galtonWatsonMeasure p ((fun (ω : ℕ → ℕ → ℕ) (i : ℕ) => ω (i + 1)) ⁻¹' B) := by
  let m : ℕ → MeasurableSpace (ℕ → ℕ → ℕ) := fun i =>
    MeasurableSpace.comap (fun ω : ℕ → ℕ → ℕ => ω i) inferInstance
  have hiI : iIndep m (galtonWatsonMeasure p) :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_eval_galtonWatsonMeasure p)
  have hI := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hiI
    (S := {0}) (T := {i | 1 ≤ i}) (by simp)
  refine (Indep_iff _ _ _).1 hI _ _ ?_ ?_
  · exact (le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) => m i) 0 rfl) _ ⟨A, hA, rfl⟩
  · have hle : MeasurableSpace.comap (fun (ω : ℕ → ℕ → ℕ) (i : ℕ) => ω (i + 1))
        MeasurableSpace.pi ≤ ⨆ i ∈ {i : ℕ | 1 ≤ i}, m i := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun n => ?_
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | 1 ≤ i}) => m i) (n + 1) (by simp)
    exact hle _ ⟨B, hB, rfl⟩

theorem natCast_add_eq_natCast_iff {k n : ℕ} {T : ℝ≥0∞} :
    (k : ℝ≥0∞) + T = n ↔ k ≤ n ∧ T = ((n - k : ℕ) : ℝ≥0∞) := by
  constructor
  · intro h
    have hkn : k ≤ n := by exact_mod_cast (le_self_add.trans_eq h : (k : ℝ≥0∞) ≤ n)
    refine ⟨hkn, (ENNReal.add_right_inj (ENNReal.natCast_ne_top k)).1 ?_⟩
    rw [h, ← Nat.cast_add, Nat.add_sub_cancel' hkn]
  · rintro ⟨hkn, rfl⟩
    rw [← Nat.cast_add, Nat.add_sub_cancel' hkn]

/-- **First-generation recursion for the law of the total progeny.** -/
theorem galtonWatsonMeasure_totalProgenyFrom_eq_tsum (k n : ℕ) :
    galtonWatsonMeasure p {ω | totalProgenyFrom k ω = n} =
      ∑' m, coeff m (PowerSeries.mk (fun j => p j) ^ k) *
        if k ≤ n then galtonWatsonMeasure p {ω | totalProgenyFrom m ω = (n - k : ℕ)} else 0 := by
  have hA : ∀ m : ℕ, MeasurableSet {x : ℕ → ℕ | ∑ j ∈ Finset.range k, x j = m} := fun m =>
    measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
      measurable_const
  have hB : ∀ m : ℕ, MeasurableSet {y : ℕ → ℕ → ℕ | (k : ℝ≥0∞) + totalProgenyFrom m y = n} :=
    fun m => measurableSet_eq_fun (by fun_prop) measurable_const
  have hset : {ω | totalProgenyFrom k ω = n} = ⋃ m : ℕ,
      ((fun ω : ℕ → ℕ → ℕ => ω 0) ⁻¹' {x : ℕ → ℕ | ∑ j ∈ Finset.range k, x j = m} ∩
        (fun (ω : ℕ → ℕ → ℕ) (i : ℕ) => ω (i + 1)) ⁻¹'
          {y : ℕ → ℕ → ℕ | (k : ℝ≥0∞) + totalProgenyFrom m y = n}) := by
    ext ω; simp [totalProgenyFrom_eq_add_shift k ω]
  rw [hset, measure_iUnion]
  · refine tsum_congr fun m => ?_
    rw [measure_preimage_eval_zero_inter_shift p (hA m) (hB m),
      (measurePreserving_eval_galtonWatsonMeasure p 0).measure_preimage
        (hA m).nullMeasurableSet,
      (measurePreserving_shift_galtonWatsonMeasure p).measure_preimage
        (hB m).nullMeasurableSet, infinitePi_sum_range_eq_coeff_pow]
    congr 1
    split_ifs with hkn
    · congr 1; ext y; simp [natCast_add_eq_natCast_iff, hkn]
    · convert measure_empty (μ := galtonWatsonMeasure p)
      ext y; simp [natCast_add_eq_natCast_iff, hkn]
  · intro m m' hne
    exact Set.disjoint_left.2 fun ω h1 h2 => hne (h1.1.symm.trans h2.1)
  · exact fun m => (measurable_pi_apply 0 (hA m)).inter
      ((measurePreserving_shift_galtonWatsonMeasure p).measurable (hB m))

theorem galtonWatsonMeasure_totalProgenyFrom_zero_left (r : ℕ) :
    galtonWatsonMeasure p {ω | totalProgenyFrom 0 ω = r} = if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst hr; simp
  · simp [hr, eq_comm (a := (0 : ℝ≥0∞))]

theorem galtonWatsonMeasure_totalProgenyFrom_of_lt {m r : ℕ} (h : r < m) :
    galtonWatsonMeasure p {ω | totalProgenyFrom m ω = r} = 0 := by
  convert measure_empty (μ := galtonWatsonMeasure p)
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hω
  have := le_totalProgenyFrom m ω
  rw [hω] at this
  exact absurd (by exact_mod_cast this : m ≤ r) (by omega)

/-- **The hitting-time theorem for the total progeny.** For `1 ≤ k ≤ n`, the total progeny
`T_k` from `k` ancestors satisfies `n P(T_k = n) = k [X^{n-k}] φ^n`, that is,
`n P(T_k = n) = k P(S_n = n - k)`. -/
theorem natCast_mul_galtonWatsonMeasure_totalProgenyFrom (n : ℕ) :
    ∀ k, 1 ≤ k → k ≤ n → (n : ℝ≥0∞) * galtonWatsonMeasure p {ω | totalProgenyFrom k ω = n} =
      k * coeff (n - k) (PowerSeries.mk (fun j => p j) ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hk hkn
  rw [galtonWatsonMeasure_totalProgenyFrom_eq_tsum]
  simp only [hkn, ↓reduceIte]
  set φ : ℝ≥0∞⟦X⟧ := PowerSeries.mk fun j => p j
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [tsum_eq_single 0 fun m hm => by
      rw [galtonWatsonMeasure_totalProgenyFrom_of_lt p (by omega), mul_zero]]
    simp
  · have key : ∀ m, (r : ℝ≥0∞) * galtonWatsonMeasure p {ω | totalProgenyFrom m ω = r} =
        if m ≤ r then m * coeff (r - m) (φ ^ r) else 0 := by
      intro m
      split_ifs with hm
      · rcases Nat.eq_zero_or_pos m with rfl | hm0
        · rw [galtonWatsonMeasure_totalProgenyFrom_zero_left]; simp [hr.ne']
        · exact ih r (by omega) m hm0 hm
      · rw [galtonWatsonMeasure_totalProgenyFrom_of_lt p (by omega), mul_zero]
    have hsum : (r : ℝ≥0∞) * ∑' m, coeff m (φ ^ k) *
        galtonWatsonMeasure p {ω | totalProgenyFrom m ω = r} =
          coeff r (X * d⁄dX (φ ^ k) * φ ^ r) := by
      rw [← ENNReal.tsum_mul_left]
      simp_rw [mul_left_comm (r : ℝ≥0∞), key]
      rw [tsum_eq_sum (s := Finset.range (r + 1)) fun m hm => by
        simp only [Finset.mem_range, not_lt] at hm
        simp only [show ¬ m ≤ r by omega, ↓reduceIte, mul_zero]]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      simp only [show m ≤ r by omega, ↓reduceIte]
      rw [PowerSeries.coeff_X_mul_derivative]
      ring
    have hps := congrArg (coeff r) (PowerSeries.natCast_mul_X_mul_derivative_pow_mul_pow φ hk r)
    rw [coeff_natCast_mul, coeff_natCast_mul, PowerSeries.coeff_X_mul_derivative] at hps
    have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hr.ne'
    refine (ENNReal.mul_right_inj hr0 (ENNReal.natCast_ne_top r)).1 ?_
    rw [mul_left_comm, hsum, hps]
    ring

/-- **Dwass's formula.** For independent offspring variables `ξ₀, ξ₁, …` with law `p` and
every `n ≥ 1`, the total progeny `T` of the Galton–Watson process satisfies
`P(T = n) = n⁻¹ P(ξ₀ + ⋯ + ξ_{n-1} = n - 1)`. -/
theorem galtonWatsonMeasure_totalProgeny_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p.toMeasure) {n : ℕ} (hn : 1 ≤ n) :
    galtonWatsonMeasure p {ω | totalProgeny ω = n} =
      (n : ℝ≥0∞)⁻¹ * P {ω | ∑ i ∈ Finset.range n, ξ i ω = n - 1} := by
  have h := natCast_mul_galtonWatsonMeasure_totalProgenyFrom p n 1 le_rfl hn
  simp only [totalProgenyFrom_one, Nat.cast_one, one_mul] at h
  rw [measure_sum_range_eq_coeff_pow hξ hind hlaw, ← h, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : n ≠ 0)) (ENNReal.natCast_ne_top n),
    one_mul]

end PercLib.Probability
