/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. Statements from the wiki article `cutoff-localization` (tags
32GP, 0WAE) and `spatial-cutoff-moments`; source T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, §I.4.1. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.SpatialMoments.Defs
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Analysis.GoodScales

/-!
# Spatial moments localise the volume (32GP, 0WAE)

For a countable vertex group `V`, a profile `q`, a root `o` and a weight `N : V → ℝ` (a norm,
for instance the sup norm on `ℤ^d`; no sign condition is needed), write
`B(o, R) = {x | N(x - o) ≤ R}`.

* **Algebra of spatial moments**: `spatialMoment_add`, `spatialMoment_const_mul`,
  `spatialMoment_one` (`= χ`), `spatialMoment_add_right_of_invariant` (translation
  invariance), `spatialMoment_sq_eq_tsum` (the second moment along an additive functional).
* **32GP** (`lintegral_encard_diff_ball_le`): if `E[∑_{x ∈ K_o} N(x - o)^p] ≤ (C_p r)^p χ`,
  then `E|K_o \ B(o, C r)| ≤ (C_p / C)^p χ` for every `C > 0`; and
  (`exists_chi_le_mul_ball`) for every `ε > 0` one `C`, depending only on `p`, `C_p`, `ε`,
  gives `χ ≤ (1 + ε) E|K_o ∩ B(o, C r)|` for every `q` and `r` satisfying the hypothesis with
  `χ < ∞`.
* **Markov form** (`law_not_subset_ball_le`): `P(K_o ⊄ B(o, C r)) ≤ (C_p / C)^p χ`.
* **0WAE** (`exists_moment_ratio_bounds`): for random variables `0 ≤ Y ≤ X` with
  `P(Y ≥ tQ) ≤ A e^{-bt} P(Y ≥ Q)` for `t ≥ 1` and `E X^j ≤ L E Y^j` for `j = 2, 3, 4`, there
  is `D` depending only on `A, b, L` with `m₂ ≤ D Q m₁`, `m₃ ≤ D Q² m₁`, `m₃ ≤ D Q m₂` and
  `m₄ ≤ D Q² m₂`, `m_j = E X^j`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [AddGroup V]

/-! ### Algebra of spatial moments -/

/-- Additivity in the weight. -/
theorem spatialMoment_add [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (w w' : V → ℝ≥0∞) :
    spatialMoment q o (w + w') = spatialMoment q o w + spatialMoment q o w' := by
  simp only [spatialMoment_eq_tsum, Pi.add_apply, add_mul]
  exact ENNReal.tsum_add

/-- Homogeneity in the weight. -/
theorem spatialMoment_const_mul [Countable V] (q : Sym2 V → unitInterval) (o : V) (c : ℝ≥0∞)
    (w : V → ℝ≥0∞) :
    spatialMoment q o (fun z => c * w z) = c * spatialMoment q o w := by
  simp only [spatialMoment_eq_tsum, mul_assoc]
  exact ENNReal.tsum_mul_left

/-- The constant weight `1` gives the susceptibility. -/
theorem spatialMoment_one [Countable V] (q : Sym2 V → unitInterval) (o : V) :
    spatialMoment q o (fun _ => 1) = chi q o := by
  simp only [spatialMoment_eq_tsum, one_mul]
  exact (chi_eq_tsum_tau q o).symm

/-- **Translation invariance.** For a profile invariant under the translation `x ↦ x + g`,
the spatial moment does not depend on the root. -/
theorem spatialMoment_add_right_of_invariant [Countable V] {q : Sym2 V → unitInterval} (g : V)
    (hq : ∀ e, q (Sym2.map (Equiv.addRight g) e) = q e) (o : V) (w : V → ℝ≥0∞) :
    spatialMoment q (o + g) w = spatialMoment q o w := by
  have hlaw := law_map_image_of_invariant (Equiv.addRight g) hq
  rw [spatialMoment_eq_tsum, spatialMoment_eq_tsum,
    ← (Equiv.addRight g).tsum_eq (fun x => w (x - (o + g)) * tau q (o + g) x)]
  refine tsum_congr fun x => ?_
  have ht := tau_eq_of_map_law (Equiv.addRight g) hlaw o x
  simp only [Equiv.coe_addRight] at ht ⊢
  rw [ht, add_sub_add_right_eq_sub]

/-- **The second moment along an additive functional.** For `ℓ : V →+ ℝ`,
`E[∑_{x ∈ K_o} ℓ(x - o)²] = ∑_x ℓ(x - o)² τ(o, x)`. -/
theorem spatialMoment_sq_eq_tsum [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (ℓ : V →+ ℝ) :
    spatialMoment q o (fun z => ENNReal.ofReal (ℓ z ^ 2)) =
      ∑' x, ENNReal.ofReal (ℓ (x - o) ^ 2) * tau q o x :=
  spatialMoment_eq_tsum q o _

/-! ### 32GP: the volume outside a ball -/

/-- The expected volume of `K_o` outside `B(o, R)` is the spatial moment of the indicator of
`N > R`. -/
theorem lintegral_encard_diff_ball_eq (q : Sym2 V → unitInterval) (o : V) (N : V → ℝ)
    (R : ℝ) :
    ∫⁻ ω, ((cluster ω o \ {x | N (x - o) ≤ R}).encard : ℝ≥0∞) ∂law q =
      spatialMoment q o (fun z => if R < N z then 1 else 0) := by
  rw [spatialMoment_def]
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.tsum_set_one, tsum_subtype (cluster ω o \ {x | N (x - o) ≤ R})
    (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ cluster ω o
  · by_cases hN : R < N (x - o)
    · rw [indicator_of_mem (show x ∈ cluster ω o \ {x | N (x - o) ≤ R} from
        ⟨hx, fun h => absurd h (not_le.2 hN)⟩), indicator_of_mem hx]
      simp [hN]
    · rw [indicator_of_notMem (show x ∉ cluster ω o \ {x | N (x - o) ≤ R} from
        fun h => h.2 (not_lt.1 hN)), indicator_of_mem hx]
      simp [hN]
  · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem hx]

/-- **Localization from the spatial moment.** Let `p, r, C > 0` and `C_p ≥ 0`. If
`E[∑_{x ∈ K_o} N(x - o)^p] ≤ (C_p r)^p χ`, then `E|K_o \ B(o, C r)| ≤ (C_p / C)^p χ`. -/
theorem lintegral_encard_diff_ball_le [Countable V] (q : Sym2 V → unitInterval) (o : V)
    {N : V → ℝ} {p r C Cp : ℝ} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C)
    (hCp : 0 ≤ Cp)
    (hS : spatialMoment q o (fun z => ENNReal.ofReal (N z ^ p)) ≤
      ENNReal.ofReal ((Cp * r) ^ p) * chi q o) :
    ∫⁻ ω, ((cluster ω o \ {x | N (x - o) ≤ C * r}).encard : ℝ≥0∞) ∂law q ≤
      ENNReal.ofReal ((Cp / C) ^ p) * chi q o := by
  have hCr : 0 < C * r := mul_pos hC hr
  have hCrp : 0 < (C * r) ^ p := Real.rpow_pos_of_pos hCr p
  rw [lintegral_encard_diff_ball_eq]
  -- the indicator is at most `N^p / (C r)^p`
  have hw : (fun z => if C * r < N z then (1 : ℝ≥0∞) else 0) ≤
      fun z => ENNReal.ofReal (((C * r) ^ p)⁻¹) * ENNReal.ofReal (N z ^ p) := by
    intro z
    by_cases hz : C * r < N z
    · simp only [hz, ite_true]
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hCrp.le), ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_mul_eq_div, one_le_div hCrp]
      exact Real.rpow_le_rpow hCr.le hz.le hp.le
    · simp [hz]
  calc spatialMoment q o (fun z => if C * r < N z then 1 else 0)
      ≤ spatialMoment q o (fun z => ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          ENNReal.ofReal (N z ^ p)) := spatialMoment_mono q o hw
    _ = ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          spatialMoment q o (fun z => ENNReal.ofReal (N z ^ p)) :=
        spatialMoment_const_mul q o _ _
    _ ≤ ENNReal.ofReal (((C * r) ^ p)⁻¹) * (ENNReal.ofReal ((Cp * r) ^ p) * chi q o) := by
        gcongr
    _ = ENNReal.ofReal ((Cp / C) ^ p) * chi q o := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hCrp.le)]
        congr 2
        rw [Real.mul_rpow hCp hr.le, Real.mul_rpow hC.le hr.le, Real.div_rpow hCp hC.le]
        have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
        have hCp' : 0 < C ^ p := Real.rpow_pos_of_pos hC p
        field_simp

/-- The expected volume of `K_o` is the expected volume inside `B(o, R)` plus that outside. -/
theorem chi_eq_lintegral_inter_add_diff [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (N : V → ℝ) (R : ℝ) :
    chi q o = ∫⁻ ω, ((cluster ω o ∩ {x | N (x - o) ≤ R}).encard : ℝ≥0∞) ∂law q +
      ∫⁻ ω, ((cluster ω o \ {x | N (x - o) ≤ R}).encard : ℝ≥0∞) ∂law q := by
  have hm : ∀ A : Set V, Measurable fun ω : Config V => ((cluster ω o ∩ A).encard : ℝ≥0∞) :=
    fun A => (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard.comp (Measurable.of_mem fun x => by
        by_cases hx : x ∈ A
        · simp only [mem_inter_iff, hx, and_true]
          exact (measurableSet_conn o x).mem
        · simp only [mem_inter_iff, hx, and_false]
          exact measurable_const))
  rw [chi, ← lintegral_add_left (hm _)]
  refine lintegral_congr fun ω => ?_
  have h := Set.encard_union_eq (s := cluster ω o ∩ {x | N (x - o) ≤ R})
    (t := cluster ω o \ {x | N (x - o) ≤ R}) (Set.disjoint_left.2 fun x h1 h2 => h2.2 h1.2)
  rw [Set.inter_union_sdiff] at h
  rw [h, ENat.toENNReal_add]

/-- **Consequence.** For every `ε > 0` there is `C > 0`, depending only on `p`, `C_p`
and `ε`, such that every profile and scale `r > 0` with
`E[∑_{x ∈ K_o} N(x - o)^p] ≤ (C_p r)^p χ < ∞` satisfy `χ ≤ (1 + ε) E|K_o ∩ B(o, C r)|`. -/
theorem exists_chi_le_mul_ball [Countable V] {N : V → ℝ} {p Cp : ℝ}
    (hp : 0 < p) (hCp : 0 ≤ Cp) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Sym2 V → unitInterval) (o : V) (r : ℝ), 0 < r →
      spatialMoment q o (fun z => ENNReal.ofReal (N z ^ p)) ≤
        ENNReal.ofReal ((Cp * r) ^ p) * chi q o →
      chi q o < ⊤ →
      chi q o ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((cluster ω o ∩ {x | N (x - o) ≤ C * r}).encard : ℝ≥0∞) ∂law q := by
  -- choose `C` with `(C_p / C)^p ≤ ε / (1 + ε)`
  set δ : ℝ := ε / (1 + ε) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hδ1 : δ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set C : ℝ := (Cp + 1) / δ ^ p⁻¹ with hC_def
  have hδp : 0 < δ ^ p⁻¹ := Real.rpow_pos_of_pos hδ0 _
  have hC : 0 < C := div_pos (by linarith) hδp
  have hratio : (Cp / C) ^ p ≤ δ := by
    have h1 : Cp / C ≤ δ ^ p⁻¹ := by
      rw [hC_def, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc (Cp / C) ^ p ≤ (δ ^ p⁻¹) ^ p :=
          Real.rpow_le_rpow (div_nonneg hCp hC.le) h1 hp.le
      _ = δ := by rw [← Real.rpow_mul hδ0.le, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  refine ⟨C, hC, fun q o r hr hS hfin => ?_⟩
  have hout := lintegral_encard_diff_ball_le q o hp hr hC hCp hS
  set I := ∫⁻ ω, ((cluster ω o ∩ {x | N (x - o) ≤ C * r}).encard : ℝ≥0∞) ∂law q
  have hsplit := chi_eq_lintegral_inter_add_diff q o N (C * r)
  -- `χ ≤ I + δ χ`
  have h1 : chi q o ≤ I + ENNReal.ofReal δ * chi q o := by
    calc chi q o = I + _ := hsplit
      _ ≤ I + ENNReal.ofReal ((Cp / C) ^ p) * chi q o := add_le_add le_rfl hout
      _ ≤ I + ENNReal.ofReal δ * chi q o := by gcongr
  -- pass to real numbers
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (by rw [hsplit]; exact le_self_add)
  have hχ := ENNReal.toReal_mono (by
    exact ENNReal.add_ne_top.2 ⟨hItop, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne⟩) h1
  rw [ENNReal.toReal_add hItop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0.le] at hχ
  rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_toReal hItop,
    ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hχ0 : 0 ≤ (chi q o).toReal := ENNReal.toReal_nonneg
  -- `(1 - δ) χ ≤ I` and `1 / (1 - δ) = 1 + ε`
  have hkey : (chi q o).toReal * (1 - δ) ≤ I.toReal := by nlinarith
  have hone : (1 + ε) * (1 - δ) = 1 := by
    rw [hδ]; field_simp; ring
  nlinarith

/-- **Markov form.** Under the hypothesis of `lintegral_encard_diff_ball_le`,
`P(K_o ⊄ B(o, C r)) ≤ (C_p / C)^p χ`. -/
theorem law_not_subset_ball_le [Countable V] (q : Sym2 V → unitInterval) (o : V)
    {N : V → ℝ} {p r C Cp : ℝ} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C)
    (hCp : 0 ≤ Cp)
    (hS : spatialMoment q o (fun z => ENNReal.ofReal (N z ^ p)) ≤
      ENNReal.ofReal ((Cp * r) ^ p) * chi q o) :
    law q {ω | ¬ cluster ω o ⊆ {x | N (x - o) ≤ C * r}} ≤
      ENNReal.ofReal ((Cp / C) ^ p) * chi q o := by
  refine le_trans ?_ (lintegral_encard_diff_ball_le q o hp hr hC hCp hS)
  calc law q {ω | ¬ cluster ω o ⊆ {x | N (x - o) ≤ C * r}}
      = ∫⁻ ω, {ω | ¬ cluster ω o ⊆ {x | N (x - o) ≤ C * r}}.indicator 1 ω ∂law q := by
        rw [lintegral_indicator_one₀]
        refine (MeasurableSet.nullMeasurableSet ?_)
        have : {ω : Config V | ¬ cluster ω o ⊆ {x | N (x - o) ≤ C * r}} =
            ⋃ x ∈ {x | ¬ N (x - o) ≤ C * r}, conn o x := by
          ext ω
          simp only [mem_ofPred_eq, not_subset, mem_iUnion, exists_prop]
          exact ⟨fun ⟨x, hx, h⟩ => ⟨x, h, hx⟩, fun ⟨x, h, hx⟩ => ⟨x, hx, h⟩⟩
        rw [this]
        exact MeasurableSet.biUnion (to_countable _) fun x _ => measurableSet_conn o x
    _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        by_cases h : ω ∈ {ω | ¬ cluster ω o ⊆ {x | N (x - o) ≤ C * r}}
        · rw [indicator_of_mem h, Pi.one_apply]
          obtain ⟨x, hx, hxB⟩ := not_subset.1 h
          have : (cluster ω o \ {x | N (x - o) ≤ C * r}).Nonempty := ⟨x, hx, hxB⟩
          have h1 := Set.one_le_encard_iff_nonempty.2 this
          calc (1 : ℝ≥0∞) = ((1 : ℕ∞) : ℝ≥0∞) := by simp
            _ ≤ _ := ENat.toENNReal_le.2 h1
        · rw [indicator_of_notMem h]
          exact zero_le

/-! ### Non-vacuity witness -/

/-- **Non-vacuity witness for `lintegral_encard_diff_ball_le`.** On `ℤ` with every pair closed
(`q = 0`), `N = |·|`, `p = 1`, `C_p = r = 1`: the spatial moment is `N(0) = 0`, so the hypothesis
holds and the volume outside `B(0, C)` has expectation at most `C⁻¹ χ`. -/
example (C : ℝ) (hC : 0 < C) :
    ∫⁻ ω, ((cluster ω (0 : ℤ) \ {x | |((x - 0 : ℤ) : ℝ)| ≤ C * 1}).encard : ℝ≥0∞)
        ∂law (fun _ : Sym2 ℤ => (0 : unitInterval)) ≤
      ENNReal.ofReal ((1 / C) ^ (1 : ℝ)) * chi (fun _ : Sym2 ℤ => (0 : unitInterval)) 0 := by
  refine lintegral_encard_diff_ball_le (N := fun z : ℤ => |(z : ℝ)|) _ 0 one_pos one_pos hC
    zero_le_one ?_
  rw [spatialMoment_zero]
  simp

end PercLib.Percolation.Bond

/-! ### 0WAE: localized exponential damping controls the moment ratios -/

namespace PercLib.Analysis

/-- **0WAE.** There is a constant `D`, depending only on `A, b, L > 0`, such that for random
variables `0 ≤ Y ≤ X` on a probability space with finite first four moments of `X`,
`P(Y ≥ tQ) ≤ A e^{-bt} P(Y ≥ Q)` for `t ≥ 1` and `E X^j ≤ L E Y^j` for `j = 2, 3, 4`
(`Q > 0`), the moments `m_j = E X^j` satisfy
`m₂ ≤ D Q m₁`, `m₃ ≤ D Q² m₁`, `m₃ ≤ D Q m₂` and `m₄ ≤ D Q² m₂`. -/
@[tag "0WAE"]
theorem exists_moment_ratio_bounds {A b L : ℝ} (hA : 0 < A) (hb : 0 < b) (hL : 0 < L) :
    ∃ D : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X Y : Ω → ℝ) (Q : ℝ), Measurable X → Measurable Y → (∀ ω, 0 ≤ Y ω) →
      (∀ ω, Y ω ≤ X ω) → 0 < Q →
      (∀ j : ℕ, j ≤ 4 → Integrable (fun ω => X ω ^ j) μ) →
      (∀ t, 1 ≤ t → μ.real {ω | t * Q ≤ Y ω} ≤ A * Real.exp (-b * t) * μ.real {ω | Q ≤ Y ω}) →
      (∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∫ ω, X ω ^ j ∂μ ≤ L * ∫ ω, Y ω ^ j ∂μ) →
      ∫ ω, X ω ^ 2 ∂μ ≤ D * Q * ∫ ω, X ω ∂μ ∧
      ∫ ω, X ω ^ 3 ∂μ ≤ D * Q ^ 2 * ∫ ω, X ω ∂μ ∧
      ∫ ω, X ω ^ 3 ∂μ ≤ D * Q * ∫ ω, X ω ^ 2 ∂μ ∧
      ∫ ω, X ω ^ 4 ∂μ ≤ D * Q ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by
  set K : ℝ → ℝ := fun r => 1 + A * Real.exp (-b) + A * r *
    ∫ t in Ioi 1, t ^ (r - 1) * Real.exp (-b * t) with hK
  have hK0 : ∀ r, 0 < r → 0 ≤ K r := by
    intro r hr
    have hI : 0 ≤ ∫ t in Ioi (1 : ℝ), t ^ (r - 1) * Real.exp (-b * t) :=
      setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _) (Real.exp_pos _).le
    have := Real.exp_pos (-b)
    positivity
  refine ⟨L * (K 2 + K 3 + K 4), fun {Ω} _ μ _ X Y Q hX hY hY0 hYX hQ hint htail hloc => ?_⟩
  -- moments of `Y` are integrable
  have hYint : ∀ j : ℕ, j ≤ 4 → Integrable (fun ω => Y ω ^ j) μ := by
    intro j hj
    refine (hint j hj).mono' (hY.pow_const j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hY0 ω) j)]
    exact pow_le_pow_left₀ (hY0 ω) (hYX ω) j
  -- BZDZ for `(p, q)`, in natural powers
  have hB : ∀ p r : ℕ, 0 < p → 0 < r → p + r ≤ 4 →
      ∫ ω, Y ω ^ (p + r) ∂μ ≤ K ((p + r : ℕ) : ℝ) * Q ^ r * ∫ ω, Y ω ^ p ∂μ := by
    intro p r hp hr hpr
    have h := (PercLib.Analysis.integral_rpow_add_le_of_tail hY hY0 hQ hA hb
      (Nat.cast_pos.2 hp) (Nat.cast_pos.2 hr) htail (by
        simpa only [Real.rpow_natCast] using hYint p (by omega))).2.2
    simp only [Real.rpow_natCast, ← Nat.cast_add] at h
    exact h
  have hYX1 : ∫ ω, Y ω ∂μ ≤ ∫ ω, X ω ∂μ :=
    integral_mono (by simpa using hYint 1 (by norm_num)) (by simpa using hint 1 (by norm_num))
      hYX
  have hYX2 : ∫ ω, Y ω ^ 2 ∂μ ≤ ∫ ω, X ω ^ 2 ∂μ :=
    integral_mono (hYint 2 (by norm_num)) (hint 2 (by norm_num))
      fun ω => pow_le_pow_left₀ (hY0 ω) (hYX ω) 2
  have hY1 : 0 ≤ ∫ ω, Y ω ∂μ := integral_nonneg hY0
  have hY2 : 0 ≤ ∫ ω, Y ω ^ 2 ∂μ := integral_nonneg fun ω => pow_nonneg (hY0 ω) 2
  have hX1 : 0 ≤ ∫ ω, X ω ∂μ := hY1.trans hYX1
  have hX2 : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := hY2.trans hYX2
  have hK2 := hK0 2 (by norm_num)
  have hK3 := hK0 3 (by norm_num)
  have hK4 := hK0 4 (by norm_num)
  have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg Q
  have b11 := hB 1 1 one_pos one_pos (by norm_num)
  have b12 := hB 1 2 one_pos two_pos (by norm_num)
  have b21 := hB 2 1 two_pos one_pos (by norm_num)
  have b22 := hB 2 2 two_pos two_pos (by norm_num)
  norm_num at b11 b12 b21 b22
  have l2 := hloc 2 le_rfl (by norm_num)
  have l3 := hloc 3 (by norm_num) (by norm_num)
  have l4 := hloc 4 (by norm_num) le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc ∫ ω, X ω ^ 2 ∂μ ≤ L * ∫ ω, Y ω ^ 2 ∂μ := l2
      _ ≤ L * (K 2 * Q * ∫ ω, Y ω ∂μ) := by gcongr
      _ ≤ L * (K 2 * Q * ∫ ω, X ω ∂μ) := by gcongr
      _ ≤ L * ((K 2 + K 3 + K 4) * Q * ∫ ω, X ω ∂μ) := by gcongr; linarith
      _ = L * (K 2 + K 3 + K 4) * Q * ∫ ω, X ω ∂μ := by ring
  · calc ∫ ω, X ω ^ 3 ∂μ ≤ L * ∫ ω, Y ω ^ 3 ∂μ := l3
      _ ≤ L * (K 3 * Q ^ 2 * ∫ ω, Y ω ∂μ) := by gcongr
      _ ≤ L * (K 3 * Q ^ 2 * ∫ ω, X ω ∂μ) := by gcongr
      _ ≤ L * ((K 2 + K 3 + K 4) * Q ^ 2 * ∫ ω, X ω ∂μ) := by gcongr; linarith
      _ = L * (K 2 + K 3 + K 4) * Q ^ 2 * ∫ ω, X ω ∂μ := by ring
  · calc ∫ ω, X ω ^ 3 ∂μ ≤ L * ∫ ω, Y ω ^ 3 ∂μ := l3
      _ ≤ L * (K 3 * Q * ∫ ω, Y ω ^ 2 ∂μ) := by gcongr
      _ ≤ L * (K 3 * Q * ∫ ω, X ω ^ 2 ∂μ) := by gcongr
      _ ≤ L * ((K 2 + K 3 + K 4) * Q * ∫ ω, X ω ^ 2 ∂μ) := by gcongr; linarith
      _ = L * (K 2 + K 3 + K 4) * Q * ∫ ω, X ω ^ 2 ∂μ := by ring
  · calc ∫ ω, X ω ^ 4 ∂μ ≤ L * ∫ ω, Y ω ^ 4 ∂μ := l4
      _ ≤ L * (K 4 * Q ^ 2 * ∫ ω, Y ω ^ 2 ∂μ) := by gcongr
      _ ≤ L * (K 4 * Q ^ 2 * ∫ ω, X ω ^ 2 ∂μ) := by gcongr
      _ ≤ L * ((K 2 + K 3 + K 4) * Q ^ 2 * ∫ ω, X ω ^ 2 ∂μ) := by gcongr; linarith
      _ = L * (K 2 + K 3 + K 4) * Q ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by ring

/-- **Non-vacuity witness for `exists_moment_ratio_bounds`.** `X = Y = 1` under a point mass,
`Q = 1`, `A = e`, `b = 1`, `L = 1`: the tail hypothesis holds (`P(Y ≥ t) = 0` for `t > 1`) and so
does localization. -/
example : ∃ D : ℝ, ∫ ω, (fun _ : Unit => (1 : ℝ)) ω ^ 2 ∂(Measure.dirac ()) ≤
    D * 1 * ∫ ω, (fun _ : Unit => (1 : ℝ)) ω ∂(Measure.dirac ()) := by
  obtain ⟨D, hD⟩ := exists_moment_ratio_bounds (Real.exp_pos 1) one_pos one_pos
  refine ⟨D, (hD (Measure.dirac ()) (fun _ => 1) (fun _ => 1) 1 measurable_const
    measurable_const (fun _ => zero_le_one) (fun _ => le_rfl) one_pos
    (fun j _ => integrable_const _) ?_ (fun j _ _ => by simp)).1⟩
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp [← Real.exp_add]
  · have : {ω : Unit | t * 1 ≤ (fun _ : Unit => (1 : ℝ)) ω} = ∅ := by
      ext ω
      simp only [mul_one, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact ht'
    rw [this, measureReal_empty]
    positivity

end PercLib.Analysis
