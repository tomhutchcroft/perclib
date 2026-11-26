/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: a logarithmic fourth-moment bound from a weighted exponential
moment (wiki exponential-moments, tag IXEZ), and box exits force large clusters for finite-range
bonds on `ℤ^d` (tag YVJT, deterministic and conditional parts). No upstream proof is copied, no
definition is added and no Input is introduced.
-/
module

public import PercLib.Models.Site.Basic
public import PercLib.Percolation.Bond.Forest
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PercLib.Probability.ExponentialMoments
public import PercLib.Percolation.Bond.TreeGraph.Moments
public import PercLib.Percolation.Bond.UniformVolumeTail

/-! # Exponential comparisons for cluster volumes

* `integral_pow_four_le` (IXEZ): if `X ≥ 0`, `χ = E X ≥ 1` and `E[X e^{X/(4χ²)}] ≤ √2 χ`, then
  `X⁴` is integrable and `E X⁴ ≤ 1152 χ⁴ (log 2χ)² E X²`. With `T = 24 χ² log(2χ)` and
  `s = 1/(4χ²)`, pointwise `X⁴ ≤ T² X² + T³ e^{-sT} X e^{sX}`, because `x³ e^{-sx}` is
  decreasing on `[T, ∞)`; then `E X² ≥ χ²` absorbs the second term.
* `integral_encard_cluster_pow_four_le` (IXEZ for percolation): the same bound for the root
  cluster volume of a model with finite susceptibility that is the same at every vertex.
* `ae_encard_cluster_ge_of_exit` (YVJT, geometric step): for a profile on `ℤ^d` vanishing on
  pairs at sup distance `> R`, almost surely a connection from `o` to a vertex at sup distance
  `> r` forces `|K_o| ≥ ⌊r/R⌋ + 1`.
* `law_exit_le` (YVJT, conditional): under the volume tail bound
  `P(|K_o| ≥ n) ≤ (√2 χ_o / n) e^{-n/(4M²)}` (an ordinary hypothesis here), the exit
  probability is at most `√2 χ_o e^{-r/(4RM²)}`.
* `law_exit_le_of_iSup_chi_ne_top` (YVJT): the same exit bound with `χ_o = χ(o)` and
  `M = ⨆ x, χ(x) < ∞`, the volume tail now supplied by
  `PercLib.Percolation.Bond.law_encard_cluster_ge_le_sqrt_two_mul`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Real

namespace PercLib.Models

/-! ### IXEZ -/

/-- For `x ≥ T > 0` and `s T ≥ 3`, `x³ ≤ T³ e^{s(x - T)}`. -/
theorem pow_three_le_mul_exp {x T s : ℝ} (hT : 0 < T) (hsT : 3 ≤ s * T) (hx : T ≤ x) :
    x ^ 3 ≤ T ^ 3 * exp (s * (x - T)) := by
  set u := x / T with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hT]; linarith
  have hxu : x = T * u := by rw [hu]; field_simp
  have h1 : u ≤ exp (u - 1) := by linarith [add_one_le_exp (u - 1)]
  have h2 : u ^ 3 ≤ exp (u - 1) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
  have h3 : exp (u - 1) ^ 3 ≤ exp (s * (x - T)) := by
    rw [← exp_nat_mul]
    refine exp_le_exp.2 ?_
    rw [hxu, show s * (T * u - T) = s * T * (u - 1) by ring]
    push_cast
    exact mul_le_mul_of_nonneg_right hsT (by linarith)
  have hx3 : x ^ 3 = T ^ 3 * u ^ 3 := by rw [hxu, mul_pow]
  rw [hx3]
  exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)

/-- The pointwise comparison `x⁴ ≤ T² x² + T³ e^{-sT} x e^{sx}` for `x ≥ 0`, `T > 0`,
`s T ≥ 3`. -/
theorem pow_four_le_of_nonneg {x T s : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hsT : 3 ≤ s * T) :
    x ^ 4 ≤ T ^ 2 * x ^ 2 + T ^ 3 * exp (-(s * T)) * (x * exp (s * x)) := by
  have hb : 0 ≤ T ^ 3 * exp (-(s * T)) * (x * exp (s * x)) := by positivity
  rcases le_or_gt x T with hxT | hxT
  · have : x ^ 4 ≤ T ^ 2 * x ^ 2 := by
      have h2 : x ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hx hxT 2
      nlinarith [sq_nonneg x]
    linarith
  · have h3 := pow_three_le_mul_exp hT hsT hxT.le
    have : x ^ 4 ≤ T ^ 3 * exp (-(s * T)) * (x * exp (s * x)) := by
      have e : T ^ 3 * exp (-(s * T)) * (x * exp (s * x)) = x * (T ^ 3 * exp (s * (x - T))) := by
        rw [mul_sub, sub_eq_add_neg, exp_add]
        ring
      rw [e, show x ^ 4 = x * x ^ 3 by ring]
      exact mul_le_mul_of_nonneg_left h3 hx
    nlinarith [sq_nonneg x, sq_nonneg T]

/-- **Fourth moment from an exponential moment.** Let `X ≥ 0` be measurable and integrable on a
probability space, with `χ = E X ≥ 1`, `X e^{X/(4χ²)}` integrable and `E[X e^{X/(4χ²)}] ≤ √2 χ`.
Then `X⁴` and `X²` are integrable and `E X⁴ ≤ 1152 χ⁴ (log 2χ)² E X²`. -/
theorem integral_pow_four_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hXm : AEStronglyMeasurable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXi : Integrable X P) (hχ : 1 ≤ ∫ ω, X ω ∂P)
    (hexpi : Integrable (fun ω => X ω * exp (X ω / (4 * (∫ ω, X ω ∂P) ^ 2))) P)
    (hexp : ∫ ω, X ω * exp (X ω / (4 * (∫ ω, X ω ∂P) ^ 2)) ∂P ≤
      √2 * ∫ ω, X ω ∂P) :
    Integrable (fun ω => X ω ^ 4) P ∧ Integrable (fun ω => X ω ^ 2) P ∧
      ∫ ω, X ω ^ 4 ∂P ≤
        1152 * (∫ ω, X ω ∂P) ^ 4 * Real.log (2 * ∫ ω, X ω ∂P) ^ 2 * ∫ ω, X ω ^ 2 ∂P := by
  set χ := ∫ ω, X ω ∂P with hχeq
  have hχ0 : 0 < χ := zero_lt_one.trans_le hχ
  set s := 1 / (4 * χ ^ 2) with hs
  have hs0 : 0 < s := by positivity
  set L := Real.log (2 * χ) with hL
  have hL2 : 1 / 2 ≤ L := by
    rw [hL]
    have h2 : (2 : ℝ) ≤ 2 * χ := by linarith
    have hlog2 : 1 / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact hlog2.trans (Real.log_le_log (by norm_num) h2)
  have hLχ : L ≤ χ := by
    rw [hL]
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * χ by positivity)
    have h' : Real.log (2 * χ) = Real.log 2 + Real.log χ := Real.log_mul (by norm_num) hχ0.ne'
    have h1 := Real.log_le_sub_one_of_pos hχ0
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  set T := 24 * χ ^ 2 * L with hT
  have hT0 : 0 < T := by positivity
  have hsT : s * T = 6 * L := by rw [hs, hT]; field_simp; norm_num
  have hsT3 : 3 ≤ s * T := by rw [hsT]; linarith
  have hexpX : (fun ω => X ω * exp (X ω / (4 * χ ^ 2))) = fun ω => X ω * exp (s * X ω) := by
    funext ω
    rw [hs, one_div_mul_eq_div]
  rw [hexpX] at hexpi hexp
  -- integrability of `X²` and `X⁴`
  have hX2le : ∀ ω, X ω ^ 2 ≤ (1 / s) * (X ω * exp (s * X ω)) := fun ω => by
    have h := add_one_le_exp (s * X ω)
    have : X ω ≤ exp (s * X ω) / s := by rw [le_div_iff₀ hs0]; nlinarith [hX0 ω]
    have e : 1 / s * (X ω * exp (s * X ω)) = X ω * (exp (s * X ω) / s) := by ring
    rw [e, sq]
    exact mul_le_mul_of_nonneg_left this (hX0 ω)
  have hX2 : Integrable (fun ω => X ω ^ 2) P := by
    refine (hexpi.const_mul (1 / s)).mono' (hXm.pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hX2le ω
  have hpt := fun ω => pow_four_le_of_nonneg (hX0 ω) hT0 hsT3
  have hdom : Integrable (fun ω => T ^ 2 * X ω ^ 2 +
      T ^ 3 * exp (-(s * T)) * (X ω * exp (s * X ω))) P :=
    (hX2.const_mul _).add (hexpi.const_mul _)
  have hX4 : Integrable (fun ω => X ω ^ 4) P := by
    refine hdom.mono' (hXm.pow 4) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hX0 ω; positivity)]
    exact hpt ω
  refine ⟨hX4, hX2, ?_⟩
  -- Jensen: `χ² ≤ E X²`
  have hjensen : χ ^ 2 ≤ ∫ ω, X ω ^ 2 ∂P := by
    have h0 : 0 ≤ ∫ ω, (X ω - χ) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have e : ∫ ω, (X ω - χ) ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P - 2 * χ * χ + χ ^ 2 := by
      have hexp' : (fun ω => (X ω - χ) ^ 2) =
          fun ω => (X ω ^ 2 - 2 * χ * X ω) + χ ^ 2 := by
        funext ω
        ring
      have i1 : Integrable (fun ω => X ω ^ 2 - 2 * χ * X ω) P := hX2.sub (hXi.const_mul _)
      rw [hexp', integral_add (f := fun ω => X ω ^ 2 - 2 * χ * X ω) i1 (integrable_const _),
        integral_sub (f := fun ω => X ω ^ 2) (g := fun ω => 2 * χ * X ω) hX2
          (hXi.const_mul _), integral_const_mul, integral_const, probReal_univ,
        smul_eq_mul, one_mul]
    linarith
  -- integrate the pointwise bound
  have hint : ∫ ω, X ω ^ 4 ∂P ≤
      T ^ 2 * ∫ ω, X ω ^ 2 ∂P + T ^ 3 * exp (-(s * T)) * (√2 * χ) := by
    calc ∫ ω, X ω ^ 4 ∂P
        ≤ ∫ ω, (T ^ 2 * X ω ^ 2 + T ^ 3 * exp (-(s * T)) * (X ω * exp (s * X ω))) ∂P :=
          integral_mono hX4 hdom hpt
      _ = T ^ 2 * ∫ ω, X ω ^ 2 ∂P +
            T ^ 3 * exp (-(s * T)) * ∫ ω, X ω * exp (s * X ω) ∂P := by
          rw [integral_add (hX2.const_mul _) (hexpi.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ T ^ 2 * ∫ ω, X ω ^ 2 ∂P + T ^ 3 * exp (-(s * T)) * (√2 * χ) := by
          gcongr
  -- the second term is at most `T² E X²`
  have hexpsT : exp (s * T) = (2 * χ) ^ 6 := by
    rw [hsT, hL, ← Real.exp_log (show 0 < 2 * χ by positivity), ← exp_nat_mul,
      Real.exp_log (show 0 < 2 * χ by positivity)]
    push_cast
    ring_nf
  have hsmall : T ^ 3 * exp (-(s * T)) * (√2 * χ) ≤ T ^ 2 * ∫ ω, X ω ^ 2 ∂P := by
    rw [exp_neg, hexpsT]
    have hsq2 : √2 ≤ 3 / 2 := by
      rw [sqrt_le_left (by norm_num)]
      norm_num
    have hχ5 : χ ≤ χ ^ 5 := by
      calc χ = χ ^ 1 := (pow_one χ).symm
        _ ≤ χ ^ 5 := pow_le_pow_right₀ hχ (by norm_num)
    -- `T √2 χ / (2χ)^6 ≤ χ²`
    have key : T * √2 * χ ≤ (2 * χ) ^ 6 * χ ^ 2 := by
      rw [hT]
      have hL0 : 0 ≤ L := by linarith
      have h1 : 24 * χ ^ 2 * L * √2 * χ ≤ 24 * χ ^ 2 * χ ^ 5 * (3 / 2) * χ := by
        have h' : L * √2 ≤ χ ^ 5 * (3 / 2) :=
          (mul_le_mul (hLχ.trans hχ5) hsq2 (sqrt_nonneg 2) (by positivity))
        calc 24 * χ ^ 2 * L * √2 * χ = (24 * χ ^ 2 * χ) * (L * √2) := by ring
          _ ≤ (24 * χ ^ 2 * χ) * (χ ^ 5 * (3 / 2)) :=
            mul_le_mul_of_nonneg_left h' (by positivity)
          _ = 24 * χ ^ 2 * χ ^ 5 * (3 / 2) * χ := by ring
      have h2 : 24 * χ ^ 2 * χ ^ 5 * (3 / 2) * χ ≤ (2 * χ) ^ 6 * χ ^ 2 := by
        have : (2 * χ) ^ 6 * χ ^ 2 = 64 * χ ^ 8 := by ring
        rw [this]
        nlinarith [pow_pos hχ0 8]
      linarith
    have hpos6 : 0 < (2 * χ) ^ 6 := by positivity
    calc T ^ 3 * ((2 * χ) ^ 6)⁻¹ * (√2 * χ) = T ^ 2 * ((T * √2 * χ) / (2 * χ) ^ 6) := by
          field_simp
      _ ≤ T ^ 2 * χ ^ 2 := by
          gcongr
          rw [div_le_iff₀ hpos6]
          linarith
      _ ≤ T ^ 2 * ∫ ω, X ω ^ 2 ∂P := by gcongr
  calc ∫ ω, X ω ^ 4 ∂P ≤ 2 * T ^ 2 * ∫ ω, X ω ^ 2 ∂P := by linarith
    _ = 1152 * χ ^ 4 * L ^ 2 * ∫ ω, X ω ^ 2 ∂P := by rw [hT]; ring

/-- **Non-vacuity witness for `integral_pow_four_le`:** `X ≡ 1` under any probability measure
(`χ = 1`). -/
theorem integral_pow_four_le_const_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    ∫ _ω, (1 : ℝ) ^ 4 ∂P ≤
      1152 * (∫ _ω, (1 : ℝ) ∂P) ^ 4 * Real.log (2 * ∫ _ω, (1 : ℝ) ∂P) ^ 2 *
        ∫ _ω, (1 : ℝ) ^ 2 ∂P := by
  have hχ : ∫ _ω, (1 : ℝ) ∂P = 1 := by simp
  refine (integral_pow_four_le (X := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (fun _ => zero_le_one) (integrable_const _) hχ.ge (integrable_const _) ?_).2.2
  rw [hχ]
  simp only [one_mul, one_pow, mul_one, integral_const, probReal_univ, smul_eq_mul]
  -- `e^{1/4} ≤ √2`
  have h1 : exp (1 / 4) ≤ √2 := by
    rw [le_sqrt (exp_pos _).le (by norm_num), ← exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (1 / 4) = 1 / 2 := by norm_num
    rw [this]
    have := Real.log_two_gt_d9
    exact (exp_le_exp.2 (by linarith : (1 / 2 : ℝ) ≤ Real.log 2)).trans_eq
      (Real.exp_log (by norm_num))
  linarith

/-! ### IXEZ for cluster volumes -/

section ClusterVolume

open PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

/-- **Fourth moment of the cluster volume.** For an independent bond model on a countable vertex set
whose susceptibility is finite and the same at every vertex, the root cluster volume `X = |K_o|`
(read in `ℕ`; it is a.s. finite) satisfies `E X⁴ ≤ 1152 χ⁴ log²(2χ) E X²`. The exponential-moment
hypothesis of `integral_pow_four_le` comes from the tree-graph moment bounds
(`lintegral_encard_pow_le`) and `lintegral_mul_exp_le` at `r = 1/(4χ²)`. -/
theorem integral_encard_cluster_pow_four_le {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (hconst : ∀ x, chi q x = chi q o)
    (hfin : chi q o < ⊤) :
    Integrable (fun ω => ((cluster ω o).encard.toNat : ℝ) ^ 4) (law q) ∧
      Integrable (fun ω => ((cluster ω o).encard.toNat : ℝ) ^ 2) (law q) ∧
      ∫ ω, ((cluster ω o).encard.toNat : ℝ) ^ 4 ∂law q ≤
        1152 * (chi q o).toReal ^ 4 * Real.log (2 * (chi q o).toReal) ^ 2 *
          ∫ ω, ((cluster ω o).encard.toNat : ℝ) ^ 2 ∂law q := by
  set χ := (chi q o).toReal with hχdef
  set X : Config V → ℝ := fun ω => ((cluster ω o).encard.toNat : ℝ) with hXdef
  have hXm : Measurable X := measurable_encard_toNat_cluster o
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => Nat.cast_nonneg _
  have hχtop : chi q o ≠ ⊤ := hfin.ne
  have hχ1 : 1 ≤ chi q o := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂law q := by simp
      _ ≤ chi q o := lintegral_mono fun ω => by
        have h : (1 : ℕ∞) ≤ (cluster ω o).encard :=
          Set.one_le_encard_iff_nonempty.2 ⟨o, SimpleGraph.Reachable.refl o⟩
        have h' := ENat.toENNReal_le.2 h
        simpa using h'
  have hχ : 1 ≤ χ := by
    have := ENNReal.toReal_mono hχtop hχ1
    simpa using this
  have hχ0 : 0 < χ := zero_lt_one.trans_le hχ
  -- `ofReal X ≤ |K_o|` everywhere, with equality where the cluster is finite.
  have hle : ∀ ω, ENNReal.ofReal (X ω) ≤ ((cluster ω o).encard : ℝ≥0∞) := by
    intro ω
    rcases eq_or_ne (cluster ω o).encard ⊤ with h | h
    · simp [h]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
      simp [hXdef, ← hm]
  have hae : ∀ᵐ ω ∂law q, ENNReal.ofReal (X ω) = ((cluster ω o).encard : ℝ≥0∞) :=
    ae_ofReal_encard_toNat_cluster_eq q o hχtop
  have hlint : ∫⁻ ω, ENNReal.ofReal (X ω) ∂law q = chi q o := lintegral_congr_ae hae
  have hXi : Integrable X (law q) :=
    (lintegral_ofReal_ne_top_iff_integrable hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall hX0)).1 (by rw [hlint]; exact hχtop)
  have hint : ∫ ω, X ω ∂law q = χ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hX0)
      hXm.aestronglyMeasurable, hlint]
  -- Moment bounds from the tree-graph inequality (Y84V).
  have hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂law q ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)) := by
    intro m hm
    have hY := lintegral_encard_pow_le q (M := chi q o) (fun x => (hconst x).le) m hm o
    calc ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂law q
        ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q := lintegral_mono fun ω => by
          rw [ENNReal.ofReal_pow (hX0 ω)]
          exact pow_le_pow_left₀ zero_le (hle ω) m
      _ ≤ _ := hY
      _ = ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)) := by
        rw [← ENNReal.ofReal_toReal hχtop, ← hχdef,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_pow hχ0.le,
          show 2 * m - 1 = (2 * m - 2) + 1 by omega, pow_succ,
          ENNReal.ofReal_mul (by positivity)]
        ring
  -- The exponential moment (0BQB).
  set r : ℝ := 1 / (4 * χ ^ 2) with hrdef
  have hr : 0 ≤ r := by positivity
  have hr1 : r < (2 * χ ^ 2)⁻¹ := by
    rw [hrdef, one_div]
    exact inv_strictAnti₀ (by positivity) (by nlinarith [sq_pos_of_pos hχ0])
  have hexpL := lintegral_mul_exp_le (P := law q) hXm hX0 hχ0 hmom hr hr1
  have hval : χ / √(1 - 2 * r * χ ^ 2) = √2 * χ := by
    have h1 : 1 - 2 * r * χ ^ 2 = 2⁻¹ := by
      rw [hrdef]
      field_simp
      norm_num
    rw [h1, Real.sqrt_inv, div_inv_eq_mul, mul_comm]
  rw [hval] at hexpL
  have hEm' : Measurable fun ω => X ω * exp (r * X ω) :=
    hXm.mul (measurable_exp.comp (hXm.const_mul r))
  have hE0 : ∀ ω, 0 ≤ X ω * exp (r * X ω) := fun ω => mul_nonneg (hX0 ω) (exp_pos _).le
  have hexpi : Integrable (fun ω => X ω * exp (r * X ω)) (law q) :=
    (lintegral_ofReal_ne_top_iff_integrable hEm'.aestronglyMeasurable
      (Filter.Eventually.of_forall hE0)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hexpL)
  have hexp : ∫ ω, X ω * exp (r * X ω) ∂law q ≤ √2 * χ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hE0)
      hEm'.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hexpL
  have hfun : (fun ω => X ω * exp (X ω / (4 * (∫ ω, X ω ∂law q) ^ 2))) =
      fun ω => X ω * exp (r * X ω) := by
    funext ω
    rw [hint, hrdef]
    ring_nf
  have main := integral_pow_four_le (P := law q) (X := X) hXm.aestronglyMeasurable hX0 hXi
    (by rw [hint]; exact hχ) (by rw [hfun]; exact hexpi)
    (by rw [hfun, hint]; exact hexp)
  rw [hint] at main
  exact main

end ClusterVolume

/-! ### YVJT -/

section YVJT

open PercLib.Percolation.Bond PercLib.Models.Site

variable {d : ℕ}

/-- Along an open walk whose steps have sup-length at most `R`, the displacement is at most
`length * R`. -/
theorem norm_sub_le_length_mul {ω : Config (LatticeSite d)} {R : ℝ}
    (hω : ∀ x y, (openGraph ω).Adj x y → ‖x - y‖ ≤ R) {x y : LatticeSite d}
    (p : (openGraph ω).Walk x y) : ‖y - x‖ ≤ p.length * R := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    calc ‖c - a‖ ≤ ‖c - b‖ + ‖b - a‖ := norm_sub_le_norm_sub_add_norm_sub c b a
      _ ≤ p.length * R + R := by
          have := hω a b h
          rw [norm_sub_rev] at this
          linarith
      _ = (p.length + 1) * R := by ring

/-- **Geometric step.** Let `q` vanish on pairs at sup distance `> R`, with `R > 0`.
Almost surely, if `o` is joined to a vertex `y` with `‖y - o‖ > r`, then
`|K_o| ≥ ⌊r/R⌋ + 1`. -/
theorem ae_encard_cluster_ge_of_exit (q : Sym2 (LatticeSite d) → unitInterval) {R r : ℝ}
    (hR : 0 < R) (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0)
    (o : LatticeSite d) :
    ∀ᵐ ω ∂law q, (∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖) →
      ((⌊r / R⌋₊ + 1 : ℕ) : ℕ∞) ≤ (cluster ω o).encard := by
  filter_upwards [ae_config_subset_positive q] with ω hω ⟨y, hy, hry⟩
  have hadj : ∀ x y, (openGraph ω).Adj x y → ‖x - y‖ ≤ R := by
    intro x y h
    obtain ⟨he, -⟩ := (openGraph_adj_iff ω x y).1 h
    by_contra hlt
    have h0 := hq x y (not_le.1 hlt)
    have hpos : 0 < q s(x, y) := hω he
    rw [h0] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨p, hp⟩ := hy.exists_isPath
  have hlen := norm_sub_le_length_mul hadj p
  have hfloor : ⌊r / R⌋₊ ≤ p.length := by
    have : r / R ≤ p.length := by
      rw [div_le_iff₀ hR]
      linarith
    calc ⌊r / R⌋₊ ≤ ⌊(p.length : ℝ)⌋₊ := Nat.floor_le_floor this
      _ = p.length := Nat.floor_natCast _
  have hsub : (p.support.toFinset : Set (LatticeSite d)) ⊆ cluster ω o := by
    intro v hv
    have hv' : v ∈ p.support := by simpa using hv
    exact ⟨p.takeUntil v hv'⟩
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support]
  calc ((⌊r / R⌋₊ + 1 : ℕ) : ℕ∞) ≤ ((p.length + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.add_le_add_right hfloor 1
    _ = (p.support.toFinset : Set (LatticeSite d)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, hcard]
    _ ≤ (cluster ω o).encard := Set.encard_le_encard hsub

/-- **Conditional.** Under the hypotheses of `ae_encard_cluster_ge_of_exit` with any real `r`, if
`P(|K_o| ≥ n) ≤ (√2 χ / n) e^{-n/(4M²)}` for every `n ≥ 1` (a volume tail bound, here an ordinary
hypothesis), then `P(o ↔ a vertex outside o + [-r,r]^d) ≤ √2 χ e^{-r/(4RM²)}`. -/
theorem law_exit_le (q : Sym2 (LatticeSite d) → unitInterval) {R r χ M : ℝ} (hR : 0 < R)
    (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0) (o : LatticeSite d)
    (hχ : 0 ≤ χ)
    (htail : ∀ n : ℕ, 1 ≤ n → law q {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
      ENNReal.ofReal (√2 * χ / n * exp (-(n / (4 * M ^ 2))))) :
    law q {ω | ∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖} ≤
      ENNReal.ofReal (√2 * χ * exp (-(r / (4 * R * M ^ 2)))) := by
  set n : ℕ := ⌊r / R⌋₊ + 1 with hn
  have hn1 : 1 ≤ n := Nat.le_add_left 1 _
  have hle : law q {ω | ∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖} ≤
      law q {ω | (n : ℕ∞) ≤ (cluster ω o).encard} :=
    measure_mono_ae ((ae_encard_cluster_ge_of_exit q hR hq o).mono fun ω h hω => h hω)
  refine (hle.trans (htail n hn1)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hnR : r / R ≤ n := by
    rw [hn]
    push_cast
    exact (Nat.lt_floor_add_one (r / R)).le
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 : √2 * χ / n ≤ √2 * χ := div_le_self (by positivity) hn0
  have h2 : exp (-(n / (4 * M ^ 2))) ≤ exp (-(r / (4 * R * M ^ 2))) := by
    refine exp_le_exp.2 (neg_le_neg ?_)
    rw [show r / (4 * R * M ^ 2) = (r / R) / (4 * M ^ 2) by field_simp]
    exact div_le_div_of_nonneg_right hnR (by positivity)
  exact mul_le_mul h1 h2 (exp_pos _).le (by positivity)

/-! ### Non-vacuity for YVJT -/

/-- **Non-vacuity witness for the geometric step:** `d = 1`, `R = 1`, open probability `p` on
nearest-neighbour pairs of `ℤ` and `0` otherwise. -/
theorem ae_encard_cluster_ge_of_exit_nn (p : unitInterval) (r : ℝ) :
    ∀ᵐ ω ∂law (Sym2.lift ⟨fun x y : LatticeSite 1 => if ‖x - y‖ ≤ 1 then p else 0,
      fun x y => by simp only [norm_sub_rev]⟩),
      (∃ y, (openGraph ω).Reachable 0 y ∧ r < ‖y - 0‖) →
        ((⌊r / 1⌋₊ + 1 : ℕ) : ℕ∞) ≤ (cluster ω 0).encard :=
  ae_encard_cluster_ge_of_exit _ one_pos (fun x y h => by simp [not_le.2 h]) 0

/-- **Non-vacuity witness for the conditional bound:** with the zero profile the cluster of `o` is
`{o}` almost surely, so the volume tail hypothesis holds with `χ = 2` and `M = 1`. -/
theorem law_exit_le_zero (o : LatticeSite d) (r : ℝ) :
    law (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval))
        {ω | ∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖} ≤
      ENNReal.ofReal (√2 * 2 * exp (-(r / (4 * 1 * 1 ^ 2)))) := by
  refine law_exit_le _ one_pos (fun _ _ _ => rfl) o (by norm_num) fun n hn => ?_
  have hsingle : ∀ᵐ ω ∂law (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval)),
      cluster ω o = {o} := by
    filter_upwards [ae_config_subset_positive (fun _ : Sym2 (LatticeSite d) =>
      (0 : unitInterval))] with ω hω
    have hω0 : ω = ∅ := eq_empty_of_forall_notMem fun e he => lt_irrefl (0 : unitInterval) (hω he)
    ext y
    simp only [cluster, mem_ofPred_eq, mem_singleton_iff, hω0]
    constructor
    · rintro ⟨w⟩
      cases w with
      | nil => rfl
      | cons h _ =>
        exact absurd ((openGraph_adj_iff ∅ _ _).1 h).1 (notMem_empty _)
    · rintro rfl
      exact SimpleGraph.Reachable.refl _
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    -- `1 ≤ 2 √2 e^{-1/4}` since `e^{1/4} ≤ 2 ≤ 2 √2`
    have he : exp (1 / 4) ≤ 2 := by
      have := Real.log_two_gt_d9
      exact (exp_le_exp.2 (by linarith : (1 / 4 : ℝ) ≤ Real.log 2)).trans_eq
        (Real.exp_log (by norm_num))
    have hs : 1 ≤ √2 := by rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hx : exp (-((1 : ℕ) / (4 * (1 : ℝ) ^ 2))) = (exp (1 / 4))⁻¹ := by
      rw [← exp_neg]
      norm_num
    rw [hx, Nat.cast_one, div_one, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
    nlinarith
  · have h0 : law (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval))
        {ω | (n : ℕ∞) ≤ (cluster ω o).encard} = 0 := by
      refine measure_mono_null (t := {ω | ¬ cluster ω o = {o}}) ?_ (ae_iff.1 hsingle)
      intro ω hω hc
      simp only [mem_ofPred_eq, hc, encard_singleton] at hω
      have : (n : ℕ∞) ≤ 1 := hω
      norm_cast at this
      omega
    rw [h0]
    exact zero_le

end YVJT

/-! ### YVJT with the volume tail discharged -/

section UniformSusceptibility

open PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

variable {d : ℕ}

/-- **Spatial exponential decay for finite-range bonds.** Let `q` vanish on pairs at sup
distance `> R`, with `R > 0`, and let `M = ⨆ x, χ(x) < ∞`. Then for every real `r`,
`P(o ↔ a vertex outside o + [-r,r]^d) ≤ √2 χ(o) e^{-r/(4RM²)}`. -/
theorem law_exit_le_of_iSup_chi_ne_top (q : Sym2 (LatticeSite d) → unitInterval) {R : ℝ}
    (hR : 0 < R) (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0)
    (hM : (⨆ x, chi q x) ≠ ⊤) (o : LatticeSite d) (r : ℝ) :
    law q {ω | ∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖} ≤
      ENNReal.ofReal (√2 * (chi q o).toReal *
        exp (-(r / (4 * R * (⨆ x, chi q x).toReal ^ 2)))) := by
  refine law_exit_le q hR hq o ENNReal.toReal_nonneg fun n hn => ?_
  have hset : {ω : Config (LatticeSite d) | (n : ℕ∞) ≤ (cluster ω o).encard} =
      {ω | ENNReal.ofReal (n : ℝ) ≤ ((cluster ω o).encard : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq, ENNReal.ofReal_natCast]
    rw [← ENat.toENNReal_le, ENat.toENNReal_coe]
  rw [hset]
  exact law_encard_cluster_ge_le_sqrt_two_mul q o hM (by exact_mod_cast hn)

/-! ### Non-vacuity -/

/-- The zero profile on `ℤ^d` has range `R = 1` and `χ ≡ 1`, so it meets every hypothesis of
`law_exit_le_of_iSup_chi_ne_top`. -/
example (o : LatticeSite d) (r : ℝ) :
    law (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval))
        {ω | ∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖} ≤
      ENNReal.ofReal (√2 * (chi (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval)) o).toReal *
        exp (-(r / (4 * 1 *
          (⨆ x, chi (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval)) x).toReal ^ 2)))) := by
  have h1 : ∀ x, chi (fun _ : Sym2 (LatticeSite d) => (0 : unitInterval)) x = 1 :=
    chi_eq_one_of_offDiagonal_zero _ fun _ _ _ => rfl
  exact law_exit_le_of_iSup_chi_ne_top _ one_pos (fun _ _ _ => rfl)
    (by simp [h1]) o r

end UniformSusceptibility

end PercLib.Models
