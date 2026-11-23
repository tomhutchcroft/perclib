/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1 (paper.txt lines 1727--1795), read against the repository model of
`PercLib/Models/LongRange/Defs.lean` (Definitions I.1.3 and I.1.5).

The transparent definitions for this model are in `LongRange/Corner/Defs.lean`.
-/
module

public import PercLib.Models.LongRange.Corner.Defs

/-!
# The corner at the positive integer radius `r₀ = 1`

The cut-off profile of Definition I.1.5 is `J_r(s) = K s - K r` for `s ≤ r` and `0` for `s > r`.
For `K s = s ^ (-(d+α))` and the sup norm on `ℤ^d` every value of `‖·‖` is a natural number, so at
a positive integer scale `r₀` an entire norm sphere `‖y‖ = r₀` sits exactly at the corner of every
one of its edge probabilities. `PercLib/Models/LongRange/CutoffCorner.lean` proves the pointwise
corner of a single edge. This file proves the consequence for the paper's moment

  `F r = ∫ ‖K_o‖^p dμ_r`,  `μ_r = law (intensityProfile (cutoffKernel N K r) β)`.

Main results:

* `moment_eq_one_of_le_one` — `F` is the constant `1` on `(-∞, 1]`;
* `hasDerivWithinAt_moment_zero_Iic_one` — the left derivative of `F` at `1` exists and is `0`;
* `eventually_le_slope_moment` — the right difference quotients are eventually at least
  `(2^p - 1) β (d+α) / 2`;
* `not_hasDerivAt_moment_one` — consequently `F` is **not** differentiable at `1` for `β > 0`.

The model, the carrier, the quantifier order and the cut-off convention are production's; the only
hypotheses are `1 ≤ d`, `0 < α`, `1 ≤ p`, `0 < β` and the high-temperature row-sum condition
`β ∑_z ‖z‖^(-(d+α)) < 1` that production itself uses. Nothing is assumed about the derivative or
its value, and no moment is assumed finite: finiteness is *derived* from the high-temperature
restoration bound `exists_powerLaw_root_succ_moment_bound`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange.Corner

variable {d : ℕ}

theorem moment_def (α : ℝ) (β : ℝ≥0) (p : ℕ) (r : ℝ) :
    moment d α β p r =
      ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal ∂(mu d α β r) := rfl

/-! ## The kernel vanishes below scale one -/

/-- **The power-law cut-off kernel vanishes at every scale `r ≤ 1`.** Every nonzero integer
displacement has sup-norm at least `1`, so at such a scale no pair is inside the cut-off. -/
theorem prof_cutoffKernel_eq_zero_of_le_one {α : ℝ} {r : ℝ} (hr : r ≤ 1)
    (e : Sym2 (Fin d → ℤ)) :
    PercLib.Models.LongRange.cutoffKernel (d := d) (snorm d) (prof d α) r e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · rw [PercLib.Models.LongRange.cutoffKernel_def, h]
      simp
    · rw [PercLib.Models.LongRange.cutoffKernel_def,
        PercLib.Models.LongRange.radialKernel_of_ne h]
      show (PercLib.Models.LongRange.cutoffProfile (prof d α) r
        (snorm d (Int.cast ∘ (x - y)))).toNNReal = 0
      have h1 : (1 : ℝ) ≤ snorm d (Int.cast ∘ (x - y)) :=
        PercLib.Models.LongRange.one_le_normSeminorm_intCast (d := d) (sub_ne_zero.2 h)
      by_cases hlt : snorm d (Int.cast ∘ (x - y)) ≤ r
      · rw [PercLib.Models.LongRange.cutoffProfile_of_le hlt, Real.toNNReal_eq_zero]
        have hN : snorm d (Int.cast ∘ (x - y)) = 1 := by linarith
        have hr1 : r = 1 := by linarith
        rw [hN, hr1]
        simp
      · rw [PercLib.Models.LongRange.cutoffProfile_of_lt (not_le.1 hlt), Real.toNNReal_zero]

/-- Consequently the intensity profile is identically zero at every scale `r ≤ 1`. -/
theorem prof_intensityProfile_eq_zero_of_le_one {α : ℝ} {β : ℝ≥0} {r : ℝ} (hr : r ≤ 1) :
    intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) (snorm d) (prof d α) r) β =
      fun _ => (0 : unitInterval) := by
  have hker : PercLib.Models.LongRange.cutoffKernel (d := d) (snorm d) (prof d α) r =
      fun _ => 0 := funext (prof_cutoffKernel_eq_zero_of_le_one hr)
  rw [hker]
  funext e
  apply Subtype.ext
  simp [intensityProfile]

/-- **The law is the Dirac mass at the empty configuration at every scale `r ≤ 1`.** -/
theorem mu_eq_dirac_empty_of_le_one {α : ℝ} {β : ℝ≥0} {r : ℝ} (hr : r ≤ 1) :
    mu d α β r = Measure.dirac (∅ : Config (Fin d → ℤ)) := by
  rw [mu, prof_intensityProfile_eq_zero_of_le_one (d := d) hr, law]
  simpa only [Set.mem_empty_iff_false, ite_false, Bool.false_eq_true, reduceIte] using
    (PercLib.Probability.prodBernoulli_deterministic (E := Sym2 (Fin d → ℤ))
      (∅ : Set (Sym2 (Fin d → ℤ))))

/-- **The moment is `1` at every scale `r ≤ 1`**: the configuration is empty, so the cluster of the
root is the singleton `{0}`. -/
theorem moment_eq_one_of_le_one {α : ℝ} {β : ℝ≥0} {p : ℕ} {r : ℝ} (hr : r ≤ 1) :
    moment d α β p r = 1 := by
  rw [moment, mu_eq_dirac_empty_of_le_one (d := d) hr,
    MeasureTheory.integral_dirac
      (fun ω => (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal)
      (∅ : Config (Fin d → ℤ)), cluster_empty, Set.encard_singleton]
  simp

/-- **The left derivative of the moment at `1` exists and equals `0`.** -/
theorem hasDerivWithinAt_moment_zero_Iic_one {α : ℝ} {β : ℝ≥0} {p : ℕ} :
    HasDerivWithinAt (moment d α β p) 0 (Iic (1 : ℝ)) 1 := by
  refine (hasDerivWithinAt_const (x := (1 : ℝ)) (s := Iic (1 : ℝ)) (c := (1 : ℝ))).congr
    ?_ ?_
  · intro r hr
    exact moment_eq_one_of_le_one (d := d) hr
  · exact moment_eq_one_of_le_one (d := d) le_rfl

/-! ## Lower bound on the moment above scale one -/

/-- The pair `{0, x}` is open only if the root is not isolated. -/
theorem cluster_ne_singleton_of_mem {x : Fin d → ℤ} (hx : x ≠ 0)
    {ω : Config (Fin d → ℤ)} (h : s(0, x) ∈ ω) :
    cluster ω (0 : Fin d → ℤ) ≠ {0} := by
  intro hcl
  have hmem : x ∈ cluster ω (0 : Fin d → ℤ) := by
    rw [mem_cluster_iff]
    exact ((openGraph_adj_iff ω 0 x).2 ⟨h, fun h0 => hx h0.symm⟩).reachable
  rw [hcl] at hmem
  exact hx (Set.mem_singleton_iff.1 hmem)

/-- Pointwise: the `p`-th power of the cluster volume is at least `2 ^ p` on the event that the
pair `{0, x}` is open, and at least `1` everywhere. -/
theorem indicator_add_le_pow_encard (p : ℕ) {x : Fin d → ℤ} (hx : x ≠ 0)
    (ω : Config (Fin d → ℤ)) :
    (1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) *
        (({ω' : Config (Fin d → ℤ) | s(0, x) ∈ ω'} : Set (Config (Fin d → ℤ))).indicator
          (fun _ => (1 : ℝ≥0∞))) ω
      ≤ ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p := by
  have hbase : (1 : ℝ≥0∞) ≤ ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) := by
    simpa using ENat.toENNReal_mono (one_le_encard_cluster ω (0 : Fin d → ℤ))
  rcases Classical.em (s(0, x) ∈ ω) with h | h
  · have hind : (({ω' : Config (Fin d → ℤ) | s(0, x) ∈ ω'} :
        Set (Config (Fin d → ℤ))).indicator (fun _ => (1 : ℝ≥0∞))) ω = 1 := by
      simp [h]
    rw [hind, mul_one]
    have hsub : ({0, x} : Set (Fin d → ℤ)) ⊆ cluster ω (0 : Fin d → ℤ) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h0 | hx'
      · rw [h0]
        exact mem_cluster_self ω 0
      · rw [hx']
        rw [mem_cluster_iff]
        exact ((openGraph_adj_iff ω 0 x).2 ⟨h, fun h0 => hx h0.symm⟩).reachable
    have h2 : (2 : ℕ∞) ≤ (cluster ω (0 : Fin d → ℤ)).encard := by
      have hpair : ({0, x} : Set (Fin d → ℤ)).encard = 2 :=
        Set.encard_pair (fun h0 => hx h0.symm)
      rw [← hpair]
      exact Set.encard_le_encard hsub
    have h2' : (2 : ℝ≥0∞) ≤ ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) :=
      ENat.toENNReal_mono h2
    calc (1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) = (2 : ℝ≥0∞) ^ p := by
          rw [add_comm, tsub_add_cancel_of_le (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
      _ ≤ _ := pow_le_pow_left' h2' p
  · have hind : (({ω' : Config (Fin d → ℤ) | s(0, x) ∈ ω'} :
        Set (Config (Fin d → ℤ))).indicator (fun _ => (1 : ℝ≥0∞))) ω = 0 := by
      simp [h]
    rw [hind, mul_zero, add_zero]
    simpa only [one_pow] using pow_le_pow_left' hbase p

/-- **The strict radial indicator, i.e. the flux weight of the paper's derivative formula, vanishes
at every scale `r ≤ 1`.** Hence the flux series with the *open* ball `‖y‖ < 1` is identically zero
at `r₀ = 1`, consistently with `hasDerivWithinAt_moment_zero_Iic_one`. -/
theorem radialKernel_indicator_eq_zero_of_le_one {r : ℝ} (hr : r ≤ 1)
    (e : Sym2 (Fin d → ℤ)) :
    (PercLib.Models.LongRange.radialKernel (snorm d) (fun s => if s < r then 1 else 0) e : ℝ)
      = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · rw [h]
      simp
    · have h1 : (1 : ℝ) ≤ snorm d (Int.cast ∘ (x - y)) :=
        PercLib.Models.LongRange.one_le_normSeminorm_intCast (d := d) (sub_ne_zero.2 h)
      rw [PercLib.Models.LongRange.radialKernel_of_ne h]
      rw [ite_eq_right (by linarith : ¬ snorm d (Int.cast ∘ (x - y)) < r), Real.toNNReal_zero]
      rfl


/-! ## The `p`-th moment dominates `1 + (2^p - 1) μ{pair open}` -/

/-- The event that the pair `{0, x}` is open is measurable. -/
theorem measurableSet_pair_open (x : Fin d → ℤ) :
    MeasurableSet {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω} :=
  measurableSet_mem (s(0, x))

/-- **The `p`-th moment is at least `1 + (2^p - 1) μ{pair `{0,x}` open}`**, in `ℝ≥0∞`. -/
theorem one_add_mul_measure_le_lintegral {α : ℝ} {β : ℝ≥0} {p : ℕ} {x : Fin d → ℤ} (hx : x ≠ 0)
    {r : ℝ} :
    (1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) *
        (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω})
      ≤ ∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r) := by
  have hAmeas : MeasurableSet {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω} :=
    measurableSet_pair_open x
  have hkey : ∫⁻ ω, ((1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) *
        ({ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}.indicator (fun _ => (1 : ℝ≥0∞))) ω)
        ∂(mu d α β r)
      = (1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) *
        (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}) := by
    rw [lintegral_add_left measurable_const,
      lintegral_const_mul _ (measurable_const.indicator hAmeas),
      lintegral_indicator hAmeas, setLIntegral_const, lintegral_const, measure_univ]
    simp
  rw [← hkey]
  exact lintegral_mono fun ω => indicator_add_le_pow_encard p hx ω

/-- **The `p`-th moment is at least `1 + (2^p - 1) μ{pair `{0,x}` open}`**, in `ℝ`. -/
theorem one_add_mul_toReal_le {α : ℝ} {β : ℝ≥0} {p : ℕ} {x : Fin d → ℤ} (hx : x ≠ 0) {r : ℝ}
    (hfin : (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r)) ≠ ⊤) :
    1 + ((2 : ℝ) ^ p - 1) * (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}).toReal
      ≤ (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r)).toReal := by
  have hM1 : mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω} ≤ 1 := by
    rw [← measure_univ (μ := mu d α β r)]
    exact measure_mono (subset_univ _)
  have hAM : ((2 : ℝ≥0∞) ^ p - 1) *
      (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}) ≠ ⊤ := by
    have h : ((2 : ℝ≥0∞) ^ p - 1) *
        (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}) ≤ ((2 : ℝ≥0∞) ^ p - 1) * 1 := by
      gcongr
    refine ne_top_of_le_ne_top ?_ h
    simp
  have htop : ((1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) *
      (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω})) ≠ ⊤ := by
    have hfin : ((2 : ℝ≥0∞) ^ p - 1) *
        (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}) ≤ ((2 : ℝ≥0∞) ^ p - 1) * 1 := by
      gcongr
    refine ne_top_of_le_ne_top ?_ (add_le_add_right hfin 1)
    simp
  calc 1 + ((2 : ℝ) ^ p - 1) * (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω}).toReal
      = ((1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ p - 1) *
          (mu d α β r {ω : Config (Fin d → ℤ) | s(0, x) ∈ ω})).toReal := by
        rw [ENNReal.toReal_add (by simp) hAM, ENNReal.toReal_mul,
          ENNReal.toReal_sub_of_le (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2))
            (ENNReal.pow_ne_top (by simp)),
          ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    _ ≤ _ := ENNReal.toReal_mono hfin (one_add_mul_measure_le_lintegral (x := x) hx (r := r))

/-! ## Finiteness of the moment and the value of the two-point function -/

/-- **The `p`-th moment is finite in the high-temperature regime** (the restoration bound of
production), for every scale `r > 1`. -/
theorem lintegral_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) {r : ℝ} (hr : 1 < r) :
    (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r)) ≠ ⊤ := by
  obtain ⟨M, hM, hroot⟩ := PercLib.Models.LongRange.exists_powerLaw_root_succ_moment_bound
    (d := d) hd hα (β := β) hβ (0 : Fin d → ℤ) p (u := 1 / 2) (v := r + 1) (R := r + 1)
    (by norm_num) (by linarith)
  refine ne_top_of_le_ne_top hM ?_
  refine le_trans (PercLib.Percolation.Bond.rootMoment_le_of_le (mu d α β r) (0 : Fin d → ℤ)
    (Nat.le_succ p)) ?_
  exact hroot r (Or.inl ⟨by linarith, by linarith⟩)

/-- **The moment as the `toReal` of the extended integral**, on the finite range. -/
theorem moment_eq_lintegral_toReal {α : ℝ} {β : ℝ≥0} {p : ℕ} {r : ℝ}
    (hfin : (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r)) ≠ ⊤) :
    moment d α β p r =
      (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r)).toReal := by
  rw [moment_def]
  exact PercLib.Models.LongRange.integral_toReal_encard_pow_eq (0 : Fin d → ℤ) p hfin

/-- The sup norm of the displacement from the root to a unit coordinate vector is `1`. -/
theorem snorm_sub_single (i : Fin d) :
    snorm d (Int.cast ∘ ((0 : Fin d → ℤ) - Pi.single i (1 : ℤ))) = 1 := by
  have hsub : (Int.cast ∘ ((0 : Fin d → ℤ) - Pi.single i (1 : ℤ)) : Fin d → ℝ) =
      -(Int.cast ∘ Pi.single i (1 : ℤ)) := by
    rw [PercLib.Models.LongRange.intCast_comp_sub]
    simp
  rw [hsub, map_neg_eq_map]
  change normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ Pi.single i (1 : ℤ)) = 1
  rw [PercLib.Models.LongRange.normSeminorm_intCast, Pi.norm_single]
  norm_num

theorem ne_zero_single (i : Fin d) : (0 : Fin d → ℤ) ≠ Pi.single i (1 : ℤ) := by
  intro h
  have := congrFun h i
  simp at this

theorem prof_one {α : ℝ} : prof d α 1 = 1 := by
  rw [prof, PercLib.Models.LongRange.powerLawProfile, Real.one_rpow, mul_one]

theorem prof_apply {α : ℝ} (r : ℝ) : prof d α r = r ^ (-((d : ℝ) + α)) := by
  rw [prof, PercLib.Models.LongRange.powerLawProfile, one_mul]

/-- The profile is at most `1` on `[1, ∞)` when the exponent is nonnegative. -/
theorem prof_le_one_of_one_le {α : ℝ} {r : ℝ} (ha : (0 : ℝ) ≤ (d : ℝ) + α) (hr : 1 ≤ r) :
    prof d α r ≤ 1 := by
  have h : r ^ (-((d : ℝ) + α)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith : -((d : ℝ) + α) ≤ 0)
  simpa only [prof_apply, prof_one] using h

/-- The profile at a unit displacement exceeds the profile at any scale `r > 1`. -/
theorem prof_unit_sub_prof_nonneg {α : ℝ} {r : ℝ} (ha : (0 : ℝ) ≤ (d : ℝ) + α) (hr : 1 < r) :
    (0 : ℝ) ≤ prof d α 1 - prof d α r := by
  have h := prof_le_one_of_one_le (d := d) (α := α) ha hr.le
  rw [prof_one]
  linarith

/-- The cut-off kernel of a unit coordinate pair, `J_r(‖e₁‖) = 1 - r ^ (-(d+α))`. -/
theorem cutoffKernel_unit_pair {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 1 < r) (i : Fin d) :
    (PercLib.Models.LongRange.cutoffKernel (d := d) (snorm d) (prof d α) r
      s(0, Pi.single i (1 : ℤ)) : ℝ) = 1 - r ^ (-((d : ℝ) + α)) := by
  have hne := ne_zero_single (d := d) i
  have hval : PercLib.Models.LongRange.cutoffProfile (prof d α) r
      (snorm d (Int.cast ∘ ((0 : Fin d → ℤ) - Pi.single i (1 : ℤ)))) =
      1 - r ^ (-((d : ℝ) + α)) := by
    rw [snorm_sub_single, PercLib.Models.LongRange.cutoffProfile_of_le hr.le, prof_one,
      prof_apply]
  have hnn : (0 : ℝ) ≤ 1 - r ^ (-((d : ℝ) + α)) := by
    have h := prof_unit_sub_prof_nonneg (d := d) (α := α) (by positivity : (0:ℝ) ≤ (d:ℝ) + α) hr
    rwa [prof_one, prof_apply] at h
  rw [PercLib.Models.LongRange.cutoffKernel_def,
    PercLib.Models.LongRange.radialKernel_of_ne hne, hval, Real.toNNReal_of_nonneg hnn]
  exact NNReal.coe_mk _ _

/-- **The two-point function at the unit pair is at least the cut-off edge probability.** -/
theorem one_sub_exp_le_measure_pair {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {r : ℝ} (hr : 1 < r)
    (i : Fin d) :
    1 - Real.exp (-(β : ℝ) * (1 - r ^ (-((d : ℝ) + α))))
      ≤ (mu d α β r {ω : Config (Fin d → ℤ) | s(0, Pi.single i (1 : ℤ)) ∈ ω}).toReal := by
  have heq : mu d α β r {ω : Config (Fin d → ℤ) | s(0, Pi.single i (1 : ℤ)) ∈ ω}
      = (unitInterval.toNNReal (intensityProfile (PercLib.Models.LongRange.cutoffKernel
          (d := d) (snorm d) (prof d α) r) β s(0, Pi.single i (1 : ℤ))) : ℝ≥0∞) := by
    rw [mu]
    exact PercLib.Probability.prodBernoulli_setOf_mem _ _
  rw [heq, ENNReal.coe_toReal, unitInterval.coe_toNNReal,
    PercLib.Models.LongRange.coe_intensityProfile_eq, cutoffKernel_unit_pair hα hr i]

/-! ## The corner factor `δ ↦ 1 - exp (-β (1 - (1+δ)^(-(d+α))))` -/

/-- **The derivative of the corner factor at `0`** is `β (d+α)`: at `δ = 0` the profile
difference vanishes and the rate of the cut-off kernel is `|J'(1)| = d + α`. -/
theorem hasDerivAt_cornerFactor {α : ℝ} {β : ℝ≥0} :
    HasDerivAt (fun δ : ℝ => 1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α)))))
      ((β : ℝ) * ((d : ℝ) + α)) 0 := by
  have hinner : HasDerivAt (fun δ : ℝ => (1 + δ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hrpow : HasDerivAt (fun t : ℝ => t ^ (-((d : ℝ) + α)))
      (-((d : ℝ) + α) * (1 : ℝ) ^ (-((d : ℝ) + α) - 1)) (1 + 0) := by
    simpa using Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := -((d : ℝ) + α))
      (Or.inl one_ne_zero)
  have hA : HasDerivAt (fun δ : ℝ => (1 + δ) ^ (-((d : ℝ) + α))) (-((d : ℝ) + α)) 0 := by
    have h := hrpow.comp (0 : ℝ) hinner
    have h' : HasDerivAt (fun δ : ℝ => (1 + δ) ^ (-((d : ℝ) + α)))
        ((-((d : ℝ) + α) * (1 : ℝ) ^ (-((d : ℝ) + α) - 1)) * 1) 0 := h
    rw [Real.one_rpow, mul_one, mul_one] at h'
    exact h'
  have hB : HasDerivAt (fun δ : ℝ => 1 - (1 + δ) ^ (-((d : ℝ) + α))) ((d : ℝ) + α) 0 := by
    have h := hA.const_sub 1
    simpa using h
  have hC : HasDerivAt (fun δ : ℝ => -(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))
      (-(β : ℝ) * ((d : ℝ) + α)) 0 := hB.const_mul (-(β : ℝ))
  have hD : HasDerivAt (fun δ : ℝ => Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α)))))
      (Real.exp 0 * (-(β : ℝ) * ((d : ℝ) + α))) 0 := by
    have h := hC.exp
    simpa using h
  have hE : HasDerivAt
      (fun δ : ℝ => 1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α)))))
      (-(Real.exp 0 * (-(β : ℝ) * ((d : ℝ) + α)))) 0 := hD.const_sub 1
  convert hE using 1
  rw [Real.exp_zero]
  ring

/-- **Right difference quotients of the corner factor tend to `β (d+α)`.** -/
theorem tendsto_slope_cornerFactor {α : ℝ} {β : ℝ≥0} :
    Tendsto (fun δ : ℝ =>
        (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((β : ℝ) * ((d : ℝ) + α))) := by
  have hslope := (hasDerivAt_cornerFactor (d := d) (α := α) (β := β)).tendsto_slope
  have hpt : ∀ δ : ℝ,
      slope (fun ε : ℝ => 1 - Real.exp (-(β : ℝ) * (1 - (1 + ε) ^ (-((d : ℝ) + α))))) 0 δ
        = (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ := by
    intro δ
    have h0 : (1 - Real.exp (-(β : ℝ) * (1 - (1 + (0 : ℝ)) ^ (-((d : ℝ) + α))))) = 0 := by
      norm_num
    simp only [slope, vsub_eq_sub, h0, sub_zero, smul_eq_mul, div_eq_inv_mul]
  refine (Tendsto.congr hpt hslope).mono_left ?_
  exact nhdsWithin_mono (0 : ℝ) (fun x hx => ne_of_gt hx)

/-- Eventually the right difference quotients of the corner factor exceed `β (d+α) / 2`. -/
theorem eventually_le_cornerFactor_slope {α : ℝ} (hα : 0 < α) {β : ℝ≥0} (hβ : 0 < β) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (β : ℝ) * ((d : ℝ) + α) / 2
        ≤ (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ := by
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have ha : (0 : ℝ) < (d : ℝ) + α := by positivity
  have hc : (0 : ℝ) < (β : ℝ) * ((d : ℝ) + α) := mul_pos hβ' ha
  refine ((tendsto_order.1 (tendsto_slope_cornerFactor (d := d) (α := α) (β := β))).1
    ((β : ℝ) * ((d : ℝ) + α) / 2) (by linarith)).mono ?_
  intro δ hδ
  exact le_of_lt hδ


/-! ## The moment increases at least linearly away from scale one -/

/-- **The moment at scale `r > 1` exceeds `1` by at least `(2^p - 1)` times the cut-off edge
probability of a unit pair.** -/
theorem moment_sub_one_ge {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) {r : ℝ} (hr : 1 < r) (i : Fin d) :
    ((2 : ℝ) ^ p - 1) * (1 - Real.exp (-(β : ℝ) * (1 - r ^ (-((d : ℝ) + α)))))
      ≤ moment d α β p r - moment d α β p 1 := by
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ p - 1 := by
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hp
    norm_num at h2 ⊢
    linarith
  have hfin := lintegral_pow_ne_top (d := d) hd hα hβ p hr
  have h1 : 1 + ((2 : ℝ) ^ p - 1) *
      (mu d α β r {ω : Config (Fin d → ℤ) | s(0, Pi.single i (1 : ℤ)) ∈ ω}).toReal
      ≤ (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(mu d α β r)).toReal :=
    one_add_mul_toReal_le (x := Pi.single i (1 : ℤ)) (ne_zero_single i).symm hfin
  have h2 := one_sub_exp_le_measure_pair (d := d) hα (β := β) hr i
  have hm := moment_eq_lintegral_toReal (d := d) (α := α) (β := β) (p := p) (r := r) hfin
  have h0 := moment_eq_one_of_le_one (d := d) (α := α) (β := β) (p := p) (r := (1 : ℝ)) le_rfl
  rw [h0, hm]
  have := mul_le_mul_of_nonneg_left h2 hc
  linarith

/-- **Right difference quotients of the moment are bounded below.** -/
theorem eventually_le_slope_moment {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβpos : 0 < β)
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (i : Fin d) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((2 : ℝ) ^ p - 1) * ((β : ℝ) * ((d : ℝ) + α)) / 2
        ≤ (moment d α β p (1 + δ) - moment d α β p 1) / δ := by
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ p - 1 := by
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hp
    norm_num at h2 ⊢
    linarith
  have hfac := eventually_le_cornerFactor_slope (d := d) hα hβpos
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 := by
    have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    exact this
  filter_upwards [hfac, hsmall, self_mem_nhdsWithin] with δ hδ hδ1 hδpos
  have hδ0 : (0 : ℝ) < δ := hδpos
  have hr : (1 : ℝ) < 1 + δ := by linarith
  have hmain := moment_sub_one_ge (d := d) hd hα hβ p hp hr i
  have hge : ((2 : ℝ) ^ p - 1) * (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α)))))
      ≤ moment d α β p (1 + δ) - moment d α β p 1 := hmain
  have hdiv : ((2 : ℝ) ^ p - 1) *
        (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ
      ≤ (moment d α β p (1 + δ) - moment d α β p 1) / δ :=
    div_le_div_of_nonneg_right hge hδ0.le
  have hsplit : ((2 : ℝ) ^ p - 1) *
        (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ
      = ((2 : ℝ) ^ p - 1) *
        ((1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ) := by
    ring
  rw [hsplit] at hdiv
  have := mul_le_mul_of_nonneg_left hδ hc
  linarith [hdiv, this]

/-! ## The moment is not differentiable at scale one -/

/-- **The paper's `p`-th cut-off root moment is not differentiable at the integer scale `1`**, in
the infinite-lattice high-temperature regime `β ∑_z ‖z‖^(-(d+α)) < 1` with `β > 0`, `d ≥ 1`,
`α > 0` and `p ≥ 1`.  Its left derivative at `1` is `0`
(`hasDerivWithinAt_moment_zero_Iic_one`), while the right difference quotients are eventually at
least `(2^p - 1) β (d+α) / 2 > 0` (`eventually_le_slope_moment`).  Hence Lemma I.4.1 of the
source cannot be read with the two-sided derivative at an integer scale. -/
theorem not_hasDerivAt_moment_one {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβpos : 0 < β)
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (i : Fin d) (L : ℝ) :
    ¬ HasDerivAt (moment d α β p) L 1 := by
  intro h
  have hleft : HasDerivWithinAt (moment d α β p) L (Iic (1 : ℝ)) 1 := h.hasDerivWithinAt
  have e1 : derivWithin (moment d α β p) (Iic (1 : ℝ)) 1 = L :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic 1)
  have e0 : derivWithin (moment d α β p) (Iic (1 : ℝ)) 1 = 0 :=
    (hasDerivWithinAt_moment_zero_Iic_one (d := d) (α := α) (β := β) (p := p)).derivWithin
      (uniqueDiffWithinAt_Iic 1)
  have hL : L = 0 := by rw [← e1, e0]
  subst hL
  have hslope1 : Tendsto (slope (moment d α β p) (1 : ℝ)) (𝓝[≠] (1 : ℝ)) (𝓝 0) :=
    h.tendsto_slope
  have hin : Tendsto (fun δ : ℝ => 1 + δ) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hbase : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hbase.const_add 1
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ' : (0 : ℝ) < δ := hδ
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      linarith
  have hcomp := hslope1.comp hin
  have hpt : ∀ δ : ℝ, slope (moment d α β p) (1 : ℝ) (1 + δ)
      = (moment d α β p (1 + δ) - moment d α β p 1) / δ := by
    intro δ
    have hd : (1 + δ) - 1 = δ := by ring
    simp only [slope, vsub_eq_sub, hd, smul_eq_mul, div_eq_inv_mul]
  have hslope : Tendsto (fun δ : ℝ => (moment d α β p (1 + δ) - moment d α β p 1) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := Tendsto.congr hpt hcomp
  have hev := eventually_le_slope_moment (d := d) hd hα hβpos hβ p hp i
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβpos
  have ha : (0 : ℝ) < (d : ℝ) + α := by positivity
  have h2p : (1 : ℝ) < (2 : ℝ) ^ p := by
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hp
    norm_num at h2 ⊢
    linarith
  have hmul : (0 : ℝ) < ((2 : ℝ) ^ p - 1) * ((β : ℝ) * ((d : ℝ) + α)) :=
    mul_pos (by linarith) (mul_pos hβ' ha)
  have hbound := le_of_tendsto_of_tendsto tendsto_const_nhds hslope hev
  linarith

/-- The same statement with the scale written as a positive integer corner: the moment is not
differentiable at `1` in any dimension, any exponent and any positive high-temperature intensity. -/
theorem not_differentiableAt_moment_one {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβpos : 0 < β)
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (i : Fin d) :
    ¬ DifferentiableAt ℝ (moment d α β p) 1 := by
  intro hd'
  exact not_hasDerivAt_moment_one hd hα hβpos hβ p hp i (deriv (moment d α β p) 1)
    (DifferentiableAt.hasDerivAt hd')

end PercLib.Models.LongRange.Corner
