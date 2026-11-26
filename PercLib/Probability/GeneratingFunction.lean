/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the probability generating function of an offspring law on `ℕ`,
the iteration from `0` and the extinction criterion (wiki branching-processes, tags 8TFY and BFM4,
analytic content). The argument follows the binomial case of `PercLib/Models/TreeRecursion.lean`; no
upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.GeomSum

/-! # Generating functions of offspring laws

For an offspring law `p : PMF ℕ` write `φ(s) = ∑ₖ p(k) sᵏ` (a real function, used on `[0,1]`)
and `m = ∑ₖ k p(k) ∈ [0, ∞]`.

1. `φ` is continuous, monotone and convex on `[0,1]`, with `φ(1) = 1`
   (`continuousOn_genFun`, `monotoneOn_genFun`, `convexOn_genFun`, `genFun_one`).
2. The iterates `φⁿ(0)` increase (`monotone_iterate_genFun`) and converge
   (`tendsto_iterate_genFun`) to `⨆ₙ φⁿ(0)`, the least fixed point of `φ` in `[0,1]`
   (`isLeast_iSup_iterate_genFun`).
3. For the least fixed point `q`: `q = 1 ↔ m ≤ 1 ∧ p(1) ≠ 1`
   (`genFun_least_fixedPoint_eq_one_iff`); if `p(1) = 1` then `φ = id` and `q = 0`
   (`genFun_eq_id_of_apply_one`, `genFun_least_fixedPoint_eq_zero_of_apply_one`); if `m > 1`
   then `q < 1` (`genFun_least_fixedPoint_lt_one`). The case `m = ⊤` is included.

No process is defined; this file is about `PMF ℕ` and real functions only.
-/

@[expose] public section
noncomputable section

open Set Filter Topology Finset
open scoped ENNReal

namespace PercLib.Probability

variable (p : PMF ℕ)

/-! ### Basic properties -/

/-- The real masses of an offspring law are summable. -/
theorem summable_pmf_toReal : Summable fun k => (p k).toReal :=
  ENNReal.summable_toReal (p.tsum_coe ▸ ENNReal.one_ne_top)

/-- The real masses of an offspring law sum to one. -/
theorem tsum_pmf_toReal : ∑' k, (p k).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

/-- The series of `φ(s)` converges on `[0,1]`. -/
theorem summable_genFun {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Summable fun k => (p k).toReal * s ^ k :=
  (summable_pmf_toReal p).of_nonneg_of_le
    (fun k => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs.1 k))
    (fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs.1 hs.2))

/-- **`φ(1) = 1`.** -/
theorem genFun_one : ∑' k, (p k).toReal * (1 : ℝ) ^ k = 1 := by
  simpa using tsum_pmf_toReal p

/-- `φ` is nonnegative on `[0, ∞)`. -/
theorem genFun_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ ∑' k, (p k).toReal * s ^ k :=
  tsum_nonneg fun k => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs k)

/-- **`φ` is monotone on `[0,1]`.** -/
theorem monotoneOn_genFun :
    MonotoneOn (fun s : ℝ => ∑' k, (p k).toReal * s ^ k) (Icc 0 1) :=
  fun _ ha _ hb hab => (summable_genFun p ha).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1 hab k) ENNReal.toReal_nonneg)
    (summable_genFun p hb)

/-- `φ` maps `[0,1]` into `[0,1]`. -/
theorem genFun_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑' k, (p k).toReal * s ^ k ∈ Icc (0 : ℝ) 1 :=
  ⟨genFun_nonneg p hs.1, (genFun_one p) ▸
    monotoneOn_genFun p hs (right_mem_Icc.2 zero_le_one) hs.2⟩

/-- **`φ` is continuous on `[0,1]`.** -/
theorem continuousOn_genFun :
    ContinuousOn (fun s : ℝ => ∑' k, (p k).toReal * s ^ k) (Icc 0 1) := by
  refine continuousOn_tsum (fun k => (continuous_const.mul (continuous_pow k)).continuousOn)
    (summable_pmf_toReal p) fun k s hs => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs.1 k))]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs.1 hs.2)

/-- **`φ` is convex on `[0,1]`.** -/
theorem convexOn_genFun :
    ConvexOn ℝ (Icc 0 1) (fun s : ℝ => ∑' k, (p k).toReal * s ^ k) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ Icc (0 : ℝ) 1 := (convex_Icc 0 1) hx hy ha hb hab
  simp only [smul_eq_mul] at hxy ⊢
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_genFun p hx).mul_left a).tsum_add ((summable_genFun p hy).mul_left b)]
  refine (summable_genFun p hxy).tsum_le_tsum (fun k => ?_)
    (((summable_genFun p hx).mul_left a).add ((summable_genFun p hy).mul_left b))
  have h := ((convexOn_pow k).2 (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) ha hb hab)
  simp only [smul_eq_mul] at h
  have hp : 0 ≤ (p k).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h hp]

/-! ### Iteration from zero -/

/-- The iterates `φⁿ(0)` stay in `[0,1]`. -/
theorem iterate_genFun_mem_Icc (n : ℕ) :
    (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0 ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => exact left_mem_Icc.2 zero_le_one
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact genFun_mem_Icc p ih

/-- **The iterates `φⁿ(0)` increase.** -/
theorem monotone_iterate_genFun :
    Monotone fun n => (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0 := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact (genFun_mem_Icc p (left_mem_Icc.2 zero_le_one)).1
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (n + 1)]
    exact monotoneOn_genFun p (iterate_genFun_mem_Icc p n) (iterate_genFun_mem_Icc p (n + 1)) ih

/-- **The iterates converge** to their supremum. -/
theorem tendsto_iterate_genFun :
    Tendsto (fun n => (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0) atTop
      (𝓝 (⨆ n, (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0)) :=
  tendsto_atTop_ciSup (monotone_iterate_genFun p)
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (iterate_genFun_mem_Icc p n).2⟩

/-- **The limit of the iterates is the least fixed point of `φ` in `[0,1]`.** -/
theorem isLeast_iSup_iterate_genFun :
    IsLeast {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r}
      (⨆ n, (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0) := by
  set φ : ℝ → ℝ := fun s => ∑' k, (p k).toReal * s ^ k with hφ
  set q := ⨆ n, φ^[n] 0
  have hbdd : BddAbove (range fun n => φ^[n] 0) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (iterate_genFun_mem_Icc p n).2⟩
  have hq : q ∈ Icc (0 : ℝ) 1 :=
    ⟨(iterate_genFun_mem_Icc p 0).1.trans (le_ciSup hbdd 0),
      ciSup_le fun n => (iterate_genFun_mem_Icc p n).2⟩
  have ht := tendsto_iterate_genFun p
  refine ⟨⟨hq, ?_⟩, fun r ⟨hr, hfix⟩ => ?_⟩
  · have h1 : Tendsto (fun n => φ (φ^[n] 0)) atTop (𝓝 (φ q)) :=
      ((continuousOn_genFun p) q hq).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨ht, Eventually.of_forall (iterate_genFun_mem_Icc p)⟩)
    have h2 : Tendsto (fun n => φ (φ^[n] 0)) atTop (𝓝 q) := by
      have := ht.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [Function.iterate_succ_apply']
    exact tendsto_nhds_unique h1 h2
  · have hle : ∀ n, φ^[n] 0 ≤ r := by
      intro n
      induction n with
      | zero => exact hr.1
      | succ n ih =>
        rw [Function.iterate_succ_apply', ← hfix]
        exact monotoneOn_genFun p (iterate_genFun_mem_Icc p n) hr ih
    exact ciSup_le hle

/-! ### The extinction criterion -/

/-- If `p(1) = 1`, every other mass vanishes. -/
theorem pmf_apply_eq_zero_of_apply_one (h : p 1 = 1) {k : ℕ} (hk : k ≠ 1) : p k = 0 := by
  rw [PMF.apply_eq_zero_iff, (PMF.apply_eq_one_iff p 1).1 h]
  exact hk

/-- **The degenerate law.** If `p(1) = 1` then `φ` is the identity. -/
theorem genFun_eq_id_of_apply_one (h : p 1 = 1) (s : ℝ) :
    ∑' k, (p k).toReal * s ^ k = s := by
  rw [tsum_eq_single 1 fun k hk => by simp [pmf_apply_eq_zero_of_apply_one p h hk], h]
  simp

/-- **The degenerate law.** If `p(1) = 1` the least fixed point is `0`. -/
theorem genFun_least_fixedPoint_eq_zero_of_apply_one (h : p 1 = 1) {q : ℝ}
    (hq : IsLeast {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r} q) : q = 0 :=
  le_antisymm (hq.2 ⟨left_mem_Icc.2 zero_le_one, genFun_eq_id_of_apply_one p h 0⟩) hq.1.1.1

/-- The real mean: if `m < ⊤`, the real series `∑ k p(k)` converges to `m`. -/
theorem hasSum_mean_toReal (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k ≠ ⊤) :
    HasSum (fun k : ℕ => (k : ℝ) * (p k).toReal) (∑' k : ℕ, (k : ℝ≥0∞) * p k).toReal := by
  have hne : ∀ k : ℕ, (k : ℝ≥0∞) * p k ≠ ⊤ := fun k =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (p.apply_ne_top k)
  have hs := ENNReal.summable_toReal hm
  rw [ENNReal.tsum_toReal_eq hne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hs ⊢
  exact hs.hasSum

/-- Bernoulli's inequality in the form used below:
`sᵏ - s ≥ -(k - 1)(1 - s)s` on `[0,1]`, with the excess `(1 - s)²` at `k = 0`. -/
theorem pow_sub_self_ge {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    -(((k : ℝ) - 1) * (1 - s) * s) + (if k = 0 then (1 - s) ^ 2 else 0) ≤ s ^ k - s := by
  rcases k with _ | j
  · simp only [Nat.cast_zero, pow_zero, ite_true]
    nlinarith
  · simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.add_one_ne_zero,
      ite_false, add_zero]
    have hb := one_add_mul_le_pow (a := s - 1) (by linarith [hs.1]) j
    have : s * (1 + j * (s - 1)) ≤ s * (1 + (s - 1)) ^ j :=
      mul_le_mul_of_nonneg_left hb hs.1
    rw [add_sub_cancel] at this
    rw [pow_succ]
    nlinarith

/-- **Subcritical and critical laws.** If `m ≤ 1` and `p(0) > 0`, then `φ(s) > s` on
`[0,1)`. -/
theorem genFun_gt_self (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k ≤ 1) (h0 : 0 < (p 0).toReal) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) : s < ∑' k, (p k).toReal * s ^ k := by
  have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
  have hmean := hasSum_mean_toReal p (ne_top_of_le_ne_top ENNReal.one_ne_top hm)
  set m := (∑' k : ℕ, (k : ℝ≥0∞) * p k).toReal
  have hm1 : m ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hm)
  have hφ := (summable_genFun p hs').hasSum
  have hp := (summable_pmf_toReal p).hasSum
  rw [tsum_pmf_toReal] at hp
  -- `h k = p k (sᵏ - s) + (k - 1) p k (1 - s) s ≥ 0`, with `h 0 ≥ p 0 (1 - s)²`
  set h : ℕ → ℝ := fun k => (p k).toReal * s ^ k - (p k).toReal * s +
    ((k : ℝ) * (p k).toReal - (p k).toReal) * ((1 - s) * s)
  have hh : HasSum h ((∑' k, (p k).toReal * s ^ k) - 1 * s + (m - 1) * ((1 - s) * s)) :=
    ((hφ.sub (hp.mul_right s)).add ((hmean.sub hp).mul_right ((1 - s) * s)))
  have hnn : ∀ k, (p k).toReal * (if k = 0 then (1 - s) ^ 2 else 0) ≤ h k := by
    intro k
    have := mul_le_mul_of_nonneg_left (pow_sub_self_ge hs' k)
      (ENNReal.toReal_nonneg : 0 ≤ (p k).toReal)
    simp only [h]
    nlinarith
  have h0le : (p 0).toReal * (1 - s) ^ 2 ≤ ∑' k, h k := by
    have := hh.summable.le_tsum 0 fun k hk => by
      have := hnn k
      simp only [hk, ite_false, mul_zero] at this
      exact this
    have h0 := hnn 0
    simp only [ite_true] at h0
    linarith
  rw [hh.tsum_eq] at h0le
  have hpos : 0 < (p 0).toReal * (1 - s) ^ 2 :=
    mul_pos h0 (pow_pos (by linarith [hs.2]) 2)
  have hneg : (m - 1) * ((1 - s) * s) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg (by linarith [hs.2]) hs.1)
  linarith

/-- If `m ≤ 1` and `p(1) ≠ 1` then `p(0) > 0`. -/
theorem pmf_zero_pos_of_mean_le_one (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k ≤ 1) (h1 : p 1 ≠ 1) :
    0 < (p 0).toReal := by
  by_contra h0
  have h0 : (p 0).toReal = 0 := le_antisymm (not_lt.1 h0) ENNReal.toReal_nonneg
  have hmean := hasSum_mean_toReal p (ne_top_of_le_ne_top ENNReal.one_ne_top hm)
  have hm1 : (∑' k : ℕ, (k : ℝ≥0∞) * p k).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hm)
  have hp := (summable_pmf_toReal p).hasSum
  rw [tsum_pmf_toReal] at hp
  have hd := hmean.sub hp
  have hnn : ∀ k : ℕ, 0 ≤ (k : ℝ) * (p k).toReal - (p k).toReal := by
    intro k
    rcases k with _ | k
    · simp [h0]
    · have : (0 : ℝ) ≤ k * (p (k + 1)).toReal := mul_nonneg k.cast_nonneg ENNReal.toReal_nonneg
      push_cast
      linarith
  have hzero : ∀ k : ℕ, (k : ℝ) * (p k).toReal - (p k).toReal = 0 := by
    have hsum0 : ∑' k : ℕ, ((k : ℝ) * (p k).toReal - (p k).toReal) = 0 :=
      le_antisymm (by rw [hd.tsum_eq]; linarith) (tsum_nonneg hnn)
    have h := (hasSum_zero_iff_of_nonneg hnn).1 (hsum0 ▸ hd.summable.hasSum)
    exact fun k => congrFun h k
  have hk : ∀ k, k ≠ 1 → (p k).toReal = 0 := by
    intro k hk
    rcases k with _ | k
    · exact h0
    · have := hzero (k + 1)
      have hk0 : (k : ℝ) ≠ 0 := by
        intro h
        exact hk (by rw [Nat.cast_eq_zero.1 h])
      push_cast at this
      have : (k : ℝ) * (p (k + 1)).toReal = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hk0
  have h1' : (p 1).toReal = 1 := by
    rw [← tsum_pmf_toReal p, tsum_eq_single 1 hk]
  exact h1 ((ENNReal.toReal_eq_one_iff _).1 h1')

/-- **Supercritical laws.** If `m > 1` then `φ(s) < s` for some `s ∈ [0,1)`. -/
theorem exists_genFun_lt_self (hm : 1 < ∑' k : ℕ, (k : ℝ≥0∞) * p k) :
    ∃ s ∈ Ico (0 : ℝ) 1, ∑' k, (p k).toReal * s ^ k < s := by
  -- a finite truncation of the mean already exceeds one
  rw [ENNReal.tsum_eq_iSup_nat] at hm
  obtain ⟨N, hN⟩ := lt_iSup_iff.1 hm
  have hN' : 1 < ∑ k ∈ range N, (k : ℝ) * (p k).toReal := by
    have hfin : ∑ k ∈ range N, (k : ℝ≥0∞) * p k ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top k)
        (p.apply_ne_top k)
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hfin).2 hN
    rw [ENNReal.toReal_sum fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top k)
      (p.apply_ne_top k)] at this
    simpa [ENNReal.toReal_mul] using this
  -- the polynomial `g(s) = ∑_{k<N} p(k) (1 + s + ⋯ + s^{k-1})` exceeds one near `1`
  set g : ℝ → ℝ := fun s => ∑ k ∈ range N, (p k).toReal * ∑ i ∈ range k, s ^ i
  have hg1 : g 1 = ∑ k ∈ range N, (k : ℝ) * (p k).toReal := by
    simp only [g, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hgc : Continuous g := by fun_prop
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), 1 < g s ∧ 0 < s := by
    refine (((hgc.tendsto 1).eventually (lt_mem_nhds (hg1 ▸ hN'))).and
      (lt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, ⟨hgs, hs0⟩, hs1⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨s, ⟨hs0.le, hs1⟩, ?_⟩
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, hs1.le⟩
  -- `1 - φ(s) = ∑ p(k) (1 - sᵏ) ≥ ∑_{k<N} p(k)(1 - sᵏ) = (1 - s) g(s) > 1 - s`
  have hφ := (summable_genFun p hs').hasSum
  have hp := (summable_pmf_toReal p).hasSum
  rw [tsum_pmf_toReal] at hp
  have hd := hp.sub hφ
  have hnn : ∀ k, 0 ≤ (p k).toReal - (p k).toReal * s ^ k := fun k => by
    have : (p k).toReal * s ^ k ≤ (p k).toReal :=
      mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs'.1 hs'.2)
    linarith
  have hle := hd.summable.sum_le_tsum (range N) (fun k _ => hnn k)
  rw [hd.tsum_eq] at hle
  have hgeom : ∑ k ∈ range N, ((p k).toReal - (p k).toReal * s ^ k) = (1 - s) * g s := by
    simp only [g]
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, mul_neg_geom_sum]
    ring
  rw [hgeom] at hle
  have : (1 - s) * 1 < (1 - s) * g s := mul_lt_mul_of_pos_left hgs (by linarith)
  linarith

/-- **Supercritical laws survive.** If `m > 1` (possibly `m = ⊤`) the least fixed point of `φ`
in `[0,1]` is less than `1`. -/
theorem genFun_least_fixedPoint_lt_one (hm : 1 < ∑' k : ℕ, (k : ℝ≥0∞) * p k) {q : ℝ}
    (hq : IsLeast {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r} q) : q < 1 := by
  obtain ⟨s, hs, hlt⟩ := exists_genFun_lt_self p hm
  have hcont : ContinuousOn (fun r : ℝ => ∑' k, (p k).toReal * r ^ k - r) (Icc 0 s) :=
    ((continuousOn_genFun p).mono (Icc_subset_Icc_right hs.2.le)).sub continuousOn_id
  have hivt := intermediate_value_Icc' hs.1 hcont
  obtain ⟨r, hr, hr0⟩ := hivt ⟨sub_nonpos.2 hlt.le, by simpa using genFun_nonneg p le_rfl⟩
  have hfix : r ∈ {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r} :=
    ⟨⟨hr.1, hr.2.trans hs.2.le⟩, sub_eq_zero.1 hr0⟩
  exact (hq.2 hfix).trans_lt (hr.2.trans_lt hs.2)

/-- **The extinction criterion.** The least fixed point of `φ` in `[0,1]` is `1` exactly when
`m ≤ 1` and `p(1) ≠ 1`. -/
theorem genFun_least_fixedPoint_eq_one_iff {q : ℝ}
    (hq : IsLeast {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r} q) :
    q = 1 ↔ ∑' k : ℕ, (k : ℝ≥0∞) * p k ≤ 1 ∧ p 1 ≠ 1 := by
  constructor
  · intro h1
    refine ⟨not_lt.1 fun hm => (genFun_least_fixedPoint_lt_one p hm hq).ne h1, fun hp1 => ?_⟩
    rw [genFun_least_fixedPoint_eq_zero_of_apply_one p hp1 hq] at h1
    exact zero_ne_one h1
  · rintro ⟨hm, h1⟩
    by_contra hne
    have hlt : q < 1 := lt_of_le_of_ne hq.1.1.2 hne
    have := genFun_gt_self p hm (pmf_zero_pos_of_mean_le_one p hm h1) ⟨hq.1.1.1, hlt⟩
    rw [hq.1.2] at this
    exact lt_irrefl q this

/-! ### Non-vacuity -/

/-- The degenerate law `p(1) = 1`: `φ = id`, and the iterates from `0` stay at `0`. -/
example : (⨆ n, (fun s : ℝ => ∑' k, ((PMF.pure 1 : PMF ℕ) k).toReal * s ^ k)^[n] 0) = 0 :=
  genFun_least_fixedPoint_eq_zero_of_apply_one _ (PMF.pure_apply_self 1)
    (isLeast_iSup_iterate_genFun _)

/-- `Bin(2, 3/4)` offspring: masses `1/16, 6/16, 9/16` on `0, 1, 2`. The mean is `3/2 > 1`
and the least fixed point is `1/9`. -/
example : ∃ p : PMF ℕ, 1 < ∑' k : ℕ, (k : ℝ≥0∞) * p k ∧
    (⨆ n, (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0) = 1 / 9 := by
  let r : ℕ → ℝ := fun k => if k = 0 then 1 / 16 else if k = 1 then 6 / 16 else
    if k = 2 then 9 / 16 else 0
  have hr : ∀ k, 0 ≤ r k := fun k => by
    simp only [r]
    split_ifs <;> norm_num
  have hr0 : ∀ k ∉ range 3, r k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [r]
    split_ifs <;> first | rfl | omega
  have hf : ∑ k ∈ range 3, ENNReal.ofReal (r k) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hr k]
    simp [Finset.sum_range_succ, r]
    norm_num
  let p : PMF ℕ := PMF.ofFinset (fun k => ENNReal.ofReal (r k)) (range 3) hf
    (fun k hk => by simp [hr0 k hk])
  have hp : ∀ k, (p k).toReal = r k := fun k => ENNReal.toReal_ofReal (hr k)
  have hφ : ∀ s : ℝ, ∑' k, (p k).toReal * s ^ k = 1 / 16 + 6 / 16 * s + 9 / 16 * s ^ 2 := by
    intro s
    simp_rw [hp]
    rw [tsum_eq_sum (s := range 3) fun k hk => by simp [hr0 k hk]]
    simp [Finset.sum_range_succ, r]
  refine ⟨p, ?_, ?_⟩
  · have hm : ∀ k : ℕ, (k : ℝ≥0∞) * p k = ENNReal.ofReal (k * r k) := fun k => by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      rfl
    simp_rw [hm]
    rw [tsum_eq_sum (s := range 3) fun k hk => by simp [hr0 k hk],
      ← ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (hr k),
      ENNReal.one_lt_ofReal]
    simp [Finset.sum_range_succ, r]
    norm_num
  · have hmem : (1 / 9 : ℝ) ∈ {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r} :=
      ⟨⟨by norm_num, by norm_num⟩, by rw [hφ]; norm_num⟩
    have hlow : (1 / 9 : ℝ) ∈
        lowerBounds {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r} := by
      rintro r ⟨hr, hfix⟩
      rw [hφ] at hfix
      by_contra hlt
      push Not at hlt
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 / 9 - r) (by linarith : (0 : ℝ) < 1 - r)]
    exact (isLeast_iSup_iterate_genFun p).unique ⟨hmem, hlow⟩

end PercLib.Probability
