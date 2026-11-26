/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Probability.DiscreteLayerCake
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Tail-sum identities for `ℕ∞`-valued random variables

Let `T : Ω → ℕ∞` be measurable under a measure `μ`.

* `lintegral_toENNReal_eq_tsum` (CSY8 in general form): `∫⁻ T = ∑_{n ≥ 0} μ {n + 1 ≤ T}`.
* `lintegral_min_eq_sum`: `∫⁻ min(T, N) = ∑_{n < N} μ {n + 1 ≤ T}`.
* `lintegral_rpow_eq_tsum`: for real `p > 0`,
  `∫⁻ T^p = ∑_{n ≥ 0} ((n+1)^p - n^p) μ {n + 1 ≤ T}` (with `⊤^p = ⊤`).
* `lintegral_indicator_lt_eq`: for a real `X ≥ 0` and `t ≥ 0`,
  `∫⁻ X 1{X > t} = t μ{X > t} + ∫_t^∞ μ{X > s} ds`, from mathlib's layer cake.

The ghost identity
`∫⁻ (1 - e^{-hT}) = (1 - e^{-h}) ∑_{n ≥ 1} e^{-h(n-1)} μ {n ≤ T}`, is
`PercLib.Probability.lintegral_ghost_eq_tsum` (`GhostTransform.lean`) and is not repeated.
The cluster case of the first identity is `chi_eq_tsum_law_le_encard`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

theorem measurableSet_natCast_le (hT : Measurable T) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) ≤ T ω} :=
  hT (Set.to_countable _).measurableSet

/-! ### First moments -/

/-- **Tail sum.** `∫⁻ T = ∑_{n ≥ 0} μ {n + 1 ≤ T}`. -/
@[tag "CSY8"]
theorem lintegral_toENNReal_eq_tsum (hT : Measurable T) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} := by
  have hpt : ∀ ω, (T ω : ℝ≥0∞) = ∑' n : ℕ,
      {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [PercLib.Percolation.Bond.toENNReal_eq_tsum_ite_le]
    congr 1
    funext n
    simp [Set.indicator]
  simp_rw [hpt]
  rw [lintegral_tsum fun n => (measurable_const.indicator
    (measurableSet_natCast_le hT _)).aemeasurable]
  congr 1
  funext n
  exact lintegral_indicator_one (measurableSet_natCast_le hT _)

/-- **Truncated tail sum.** `∫⁻ min(T, N) = ∑_{n < N} μ {n + 1 ≤ T}`. -/
theorem lintegral_min_eq_sum (hT : Measurable T) (N : ℕ) :
    ∫⁻ ω, ((min (T ω) N : ℕ∞) : ℝ≥0∞) ∂μ =
      ∑ n ∈ Finset.range N, μ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} := by
  have hpt : ∀ ω, ((min (T ω) N : ℕ∞) : ℝ≥0∞) = ∑ n ∈ Finset.range N,
      {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    have hint : ((T ω : ℕ∞) : ℝ≥0∞) = ⊤ ∨ ∃ m : ℕ, ((T ω : ℕ∞) : ℝ≥0∞) = (m : ℝ≥0∞) := by
      induction T ω using ENat.recTopCoe with
      | top => exact Or.inl (by simp)
      | coe m => exact Or.inr ⟨m, by simp⟩
    rw [ENat.toENNReal_min, ENat.toENNReal_coe, min_eq_sum_ite hint N]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hiff : ((n : ℝ≥0∞) + 1 ≤ ((T ω : ℕ∞) : ℝ≥0∞)) ↔ ((n + 1 : ℕ) : ℕ∞) ≤ T ω := by
      rw [show (n : ℝ≥0∞) + 1 = (((n + 1 : ℕ) : ℕ∞) : ℝ≥0∞) by push_cast; ring,
        ENat.toENNReal_le]
    by_cases h : ((n + 1 : ℕ) : ℕ∞) ≤ T ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} from h),
        ite_eq_left (hiff.2 h)]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} from h),
        ite_eq_right (mt hiff.1 h)]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun n _ => measurable_const.indicator
    (measurableSet_natCast_le hT _)]
  exact Finset.sum_congr rfl fun n _ => lintegral_indicator_one (measurableSet_natCast_le hT _)

/-! ### Real moments -/

/-- `n ↦ n^p` is monotone on `ℕ` for `p ≥ 0`, in `ℝ≥0∞`. -/
theorem monotone_natCast_rpow {p : ℝ} (hp : 0 ≤ p) :
    Monotone fun n : ℕ => (n : ℝ≥0∞) ^ p := fun _ _ hab =>
  ENNReal.rpow_le_rpow (by exact_mod_cast hab) hp

/-- **Pointwise telescoping.** For `x : ℕ∞` and `p > 0`,
`x^p = ∑_{n ≥ 0} ((n+1)^p - n^p) 1{n + 1 ≤ x}`. -/
theorem rpow_eq_tsum_ite {p : ℝ} (hp : 0 < p) (x : ℕ∞) :
    ((x : ℝ≥0∞)) ^ p = ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      (if ((n + 1 : ℕ) : ℕ∞) ≤ x then 1 else 0) := by
  have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N, (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) =
      (N : ℝ≥0∞) ^ p := by
    intro N
    induction N with
    | zero => simp [ENNReal.zero_rpow_of_pos hp]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, add_tsub_cancel_of_le
        (ENNReal.rpow_le_rpow (le_add_right le_rfl) hp.le)]
      push_cast
      rfl
  induction x using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENNReal.top_rpow_of_pos hp, le_top, ↓reduceIte, mul_one]
    rw [ENNReal.tsum_eq_iSup_nat]
    simp_rw [htel]
    refine ((iSup_eq_top (f := fun N : ℕ => (N : ℝ≥0∞) ^ p)).2 fun b hb => ?_).symm
    obtain ⟨N, hN⟩ := exists_nat_gt (b.toReal ^ (1 / p))
    refine ⟨N, ?_⟩
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [← ENNReal.ofReal_toReal hb.ne, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_rpow_of_nonneg hN0 hp.le]
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hNpos p)).2 ?_
    calc b.toReal = (b.toReal ^ (1 / p)) ^ p := by
          rw [← Real.rpow_mul ENNReal.toReal_nonneg, one_div_mul_cancel hp.ne', Real.rpow_one]
      _ < (N : ℝ) ^ p := Real.rpow_lt_rpow (by positivity) hN hp
  | coe m =>
    rw [tsum_eq_sum (s := Finset.range m) fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      have : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by rw [Nat.cast_le]; omega
      rw [ite_eq_right this, mul_zero]]
    rw [show ((m : ℕ∞) : ℝ≥0∞) = (m : ℝ≥0∞) by simp, ← htel m]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : ((n + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
      rw [Nat.cast_le]; have := Finset.mem_range.1 hn; omega
    rw [ite_eq_left this, mul_one]

/-- **Real moments.** For `p > 0`, `∫⁻ T^p = ∑_{n ≥ 0} ((n+1)^p - n^p) μ {n + 1 ≤ T}`. -/
theorem lintegral_rpow_eq_tsum (hT : Measurable T) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ((T ω : ℝ≥0∞)) ^ p ∂μ = ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      μ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} := by
  simp_rw [rpow_eq_tsum_ite hp]
  have hm : ∀ n : ℕ, Measurable fun ω => (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      (if ((n + 1 : ℕ) : ℕ∞) ≤ T ω then (1 : ℝ≥0∞) else 0) := fun n =>
    (measurable_of_countable (fun t : ℕ∞ => (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      (if ((n + 1 : ℕ) : ℕ∞) ≤ t then (1 : ℝ≥0∞) else 0))).comp hT
  rw [lintegral_tsum fun n => (hm n).aemeasurable]
  congr 1
  funext n
  have hc : ∀ ω, (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      (if ((n + 1 : ℕ) : ℕ∞) ≤ T ω then (1 : ℝ≥0∞) else 0) =
      (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
        {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω}.indicator 1 ω := fun ω => by
    by_cases h : ((n + 1 : ℕ) : ℕ∞) ≤ T ω
    · rw [ite_eq_left h, Set.indicator_of_mem (show ω ∈ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} from h)]
      rfl
    · rw [ite_eq_right h,
        Set.indicator_of_notMem (show ω ∉ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} from h)]
  rw [lintegral_congr hc, lintegral_const_mul _ (measurable_one.indicator
    (measurableSet_natCast_le hT _)), lintegral_indicator_one (measurableSet_natCast_le hT _)]

/-! ### Real variables -/

/-- **Truncated layer cake.** For a real `X ≥ 0` and `t ≥ 0`,
`∫⁻ X 1{X > t} = t μ{X > t} + ∫_t^∞ μ{X > s} ds`. -/
theorem lintegral_indicator_lt_eq {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, {ω | t < X ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω ∂μ =
      ENNReal.ofReal t * μ {ω | t < X ω} + ∫⁻ s in Ioi t, μ {ω | s < X ω} := by
  set g : Ω → ℝ := {ω | t < X ω}.indicator X with hg
  have hS : MeasurableSet {ω | t < X ω} := measurableSet_lt measurable_const hX
  have hgm : Measurable g := hX.indicator hS
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by
    simp only [hg, Set.indicator]; split_ifs
    · exact hX0 ω
    · exact le_rfl
  have hlhs : ∀ ω, {ω | t < X ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω =
      ENNReal.ofReal (g ω) := fun ω => by
    simp only [hg, Set.indicator]; split_ifs <;> simp
  simp_rw [hlhs]
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hgm.aemeasurable]
  -- Split `(0, ∞) = (0, t] ∪ (t, ∞)`.
  have hsplit : Ioi (0 : ℝ) = Ioc 0 t ∪ Ioi t := (Ioc_union_Ioi_eq_Ioi ht).symm
  rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi_same)]
  congr 1
  · -- On `(0, t]`, `{s < g} = {t < X}`.
    have hset : ∀ s ∈ Ioc (0 : ℝ) t, μ {ω | s < g ω} = μ {ω | t < X ω} := by
      intro s hs
      congr 1
      ext ω
      simp only [hg, Set.mem_ofPred_eq, Set.indicator]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => lt_of_le_of_lt hs.2 h⟩
      · exact ⟨fun h' => absurd hs.1 (not_lt.2 h'.le), fun h' => absurd h' h⟩
    rw [setLIntegral_congr_fun measurableSet_Ioc (fun s hs => hset s hs), setLIntegral_const,
      Real.volume_Ioc, sub_zero, mul_comm]
  · -- On `(t, ∞)`, `{s < g} = {s < X}`.
    refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : t < s) => ?_
    congr 1
    ext ω
    simp only [hg, Set.mem_ofPred_eq, Set.indicator]
    split_ifs with h
    · rfl
    · exact ⟨fun h' => absurd h' (by linarith [ht]), fun h' => absurd (hs.trans h') h⟩

/-! ### Non-vacuity witnesses -/

/-- `T ≡ k`: the tail sum is `k`. -/
example (k : ℕ) : ∑' n : ℕ, (Measure.dirac ()) {_ω : Unit | ((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)} =
    (k : ℝ≥0∞) := by
  have := lintegral_toENNReal_eq_tsum (μ := Measure.dirac ()) (T := fun _ : Unit => (k : ℕ∞))
    measurable_const
  simpa using this.symm

/-- `T ≡ ⊤`: the tail sum is `⊤`. -/
example : ∑' n : ℕ, (Measure.dirac ()) {_ω : Unit | ((n + 1 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞)} = ⊤ := by
  have := lintegral_toENNReal_eq_tsum (μ := Measure.dirac ()) (T := fun _ : Unit => (⊤ : ℕ∞))
    measurable_const
  simp only [lintegral_const, measure_univ, mul_one, ENat.toENNReal_top] at this
  exact this.symm

/-- `T ≡ k`, item 2: the moment series is `k^p`. -/
example (k : ℕ) {p : ℝ} (hp : 0 < p) :
    ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      (Measure.dirac ()) {_ω : Unit | ((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)} = (k : ℝ≥0∞) ^ p := by
  have := lintegral_rpow_eq_tsum (μ := Measure.dirac ()) (T := fun _ : Unit => (k : ℕ∞))
    measurable_const hp
  simpa using this.symm

/-- `T ≡ ⊤`, item 2: the moment series is `⊤`. -/
example {p : ℝ} (hp : 0 < p) :
    ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p) *
      (Measure.dirac ()) {_ω : Unit | ((n + 1 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞)} = ⊤ := by
  have := lintegral_rpow_eq_tsum (μ := Measure.dirac ()) (T := fun _ : Unit => (⊤ : ℕ∞))
    measurable_const hp
  simp only [lintegral_const, measure_univ, mul_one, ENat.toENNReal_top,
    ENNReal.top_rpow_of_pos hp] at this
  exact this.symm

/-- Item 4 for `X ≡ 2` and `t = 1`: both sides are `2`. -/
example : ∫⁻ _ω, {_ω : Unit | (1 : ℝ) < 2}.indicator (fun _ => ENNReal.ofReal 2)
    () ∂(Measure.dirac ()) =
    ENNReal.ofReal 1 * (Measure.dirac ()) {_ω : Unit | (1 : ℝ) < 2} +
      ∫⁻ s in Ioi (1 : ℝ), (Measure.dirac ()) {_ω : Unit | s < 2} :=
  lintegral_indicator_lt_eq (X := fun _ => (2 : ℝ)) measurable_const (fun _ => by norm_num)
    zero_le_one

end PercLib.Probability
