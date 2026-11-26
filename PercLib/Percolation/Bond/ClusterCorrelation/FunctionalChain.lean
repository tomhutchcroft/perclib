/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Mathematical reference: the restoration-map argument for
functionals of two distinct clusters in a countable independent product model,
extending Lemma I.2.1 of T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.ClusterCorrelation.Inequalities
public import Mathlib.Probability.Moments.Covariance

/-! # Product and covariance chains for functionals of two clusters

For `F G : Set V → ℝ≥0∞` with measurable cluster evaluations, under `law q` on a countable
vertex set:

* `lintegral_indicator_compl_conn_mul_le_mul`: for `G` increasing and `F` arbitrary,
  `E[F(K_x) G(K_y) 1{x ↮ y}] ≤ E[F(K_x) 1{x ↮ y}] E G(K_y)`. The proof is the restoration
  map (`map_restoreMap`, `cluster_restoreMap`, `cluster_restoreMap_subset_snd`).
* `lintegral_indicator_compl_conn_mul_le_mul_le`: the first chain, ending in
  `E F(K_x) E G(K_y)`.
* `lintegral_mul_lintegral_le_lintegral_mul_le_add`: for `F`, `G` increasing,
  `E F E G ≤ E[F G] ≤ E F E G + E[F G 1{x ↔ y}]`.
* `covariance_cluster_nonneg_and_le`: with finite expectations,
  `0 ≤ Cov(F(K_x), G(K_y)) ≤ E[F G 1{x ↔ y}]`, with mathlib's `covariance`.

Two general facts are proved on the way: `covariance_eq_sub_of_integrable_mul` (the
`E[XY] - E X E Y` formula from integrability of `X`, `Y`, `X Y`, without square integrability)
and its `ℝ≥0∞` form `covariance_toReal_eq_sub`.

## Main results

* `lintegral_indicator_compl_conn_mul_le_mul_le`
* `lintegral_mul_lintegral_le_lintegral_mul_le_add`
* `covariance_cluster_nonneg_and_le`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-! ### Covariance from first moments -/

section Covariance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Cov(X, Y) = E[X Y] - E X E Y` when `X`, `Y` and `X Y` are integrable (no square
integrability needed). -/
theorem covariance_eq_sub_of_integrable_mul [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (hXY : Integrable (X * Y) μ) :
    cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
  have hXY' : Integrable (fun ω => X ω * Y ω) μ := hXY
  have h1 : Integrable (fun ω => X ω * μ[Y]) μ := hX.mul_const _
  have h2 : Integrable (fun ω => μ[X] * Y ω) μ := hY.const_mul _
  have e : (fun ω => (X ω - μ[X]) * (Y ω - μ[Y])) =
      fun ω => (X ω * Y ω - X ω * μ[Y]) - (μ[X] * Y ω - μ[X] * μ[Y]) := by
    ext ω; ring
  have h3 : Integrable (fun ω => X ω * Y ω - X ω * μ[Y]) μ := hXY'.sub h1
  have h4 : Integrable (fun ω => μ[X] * Y ω - μ[X] * μ[Y]) μ := h2.sub (integrable_const _)
  rw [covariance, e, integral_sub h3 h4,
    integral_sub hXY' h1, integral_sub h2 (integrable_const _)]
  simp only [integral_mul_const, integral_const_mul, integral_const, probReal_univ, one_smul,
    Pi.mul_apply]
  ring

/-- **Covariance of `ℝ≥0∞`-valued variables.** For a.e.-measurable `X Y : Ω → ℝ≥0∞` with
finite `E X`, `E Y`, `E[X Y]`, the covariance of the real parts is
`E[X Y] - E X E Y`. -/
theorem covariance_toReal_eq_sub [IsProbabilityMeasure μ] {X Y : Ω → ℝ≥0∞}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ) (hX : ∫⁻ ω, X ω ∂μ ≠ ⊤)
    (hY : ∫⁻ ω, Y ω ∂μ ≠ ⊤) (hXY : ∫⁻ ω, X ω * Y ω ∂μ ≠ ⊤) :
    cov[fun ω => (X ω).toReal, fun ω => (Y ω).toReal; μ] =
      (∫⁻ ω, X ω * Y ω ∂μ).toReal - (∫⁻ ω, X ω ∂μ).toReal * (∫⁻ ω, Y ω ∂μ).toReal := by
  have hprod : (fun ω => (X ω).toReal) * (fun ω => (Y ω).toReal) =
      fun ω => (X ω * Y ω).toReal := by
    ext ω; simp [ENNReal.toReal_mul]
  have e1 : ∫ ω, (X ω * Y ω).toReal ∂μ = (∫⁻ ω, X ω * Y ω ∂μ).toReal :=
    integral_toReal (hXm.mul hYm) (ae_lt_top' (hXm.mul hYm) hXY)
  rw [covariance_eq_sub_of_integrable_mul (integrable_toReal_of_lintegral_ne_top hXm hX)
    (integrable_toReal_of_lintegral_ne_top hYm hY)
    (hprod ▸ integrable_toReal_of_lintegral_ne_top (hXm.mul hYm) hXY), hprod]
  beta_reduce
  rw [e1, integral_toReal hXm (ae_lt_top' hXm hX), integral_toReal hYm (ae_lt_top' hYm hY)]

end Covariance

/-! ### Two distinct clusters -/

variable {V : Type*} [Countable V]

/-- **Distinct clusters, one increasing functional.** For `G` increasing and `F` arbitrary,
`E[F(K_x) G(K_y) 1{x ↮ y}] ≤ E[F(K_x) 1{x ↮ y}] E G(K_y)`, with infinite values allowed. -/
theorem lintegral_indicator_compl_conn_mul_le_mul (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y)) :
    ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q ≤
      (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
        ∫⁻ ω, G (cluster ω y) ∂law q := by
  have hc := (measurableSet_conn (V := V) x y).compl
  have hm : Measurable fun ω : Config V =>
      (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω :=
    (hFm.mul hGm).indicator hc
  calc ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q
      = ∫⁻ p, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y))
          (restoreMap x p) ∂((law q).prod (law q)) := by
        conv_lhs => rw [← map_restoreMap q x]
        exact lintegral_map hm (measurable_restoreMap x)
    _ ≤ ∫⁻ p, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) p.1 * G (cluster p.2 y)
          ∂((law q).prod (law q)) := by
        refine lintegral_mono fun p => ?_
        by_cases hr : restoreMap x p ∈ conn x y
        · rw [indicator_of_notMem (Set.notMem_compl_iff.2 hr)]
          exact zero_le
        · have hy : y ∉ cluster p.1 x := by
            rw [← cluster_restoreMap x p]; exact hr
          have hp : p.1 ∈ (conn x y)ᶜ := hy
          rw [indicator_of_mem hr, indicator_of_mem hp, cluster_restoreMap]
          exact mul_le_mul' le_rfl (hG fun w hw => (cluster_restoreMap_subset_snd hy hw).1)
    _ = (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
          ∫⁻ ω, G (cluster ω y) ∂law q :=
        lintegral_prod_mul (hFm.indicator hc).aemeasurable hGm.aemeasurable

/-- **The first chain.** For `G` increasing and `F` arbitrary,
`E[F(K_x) G(K_y) 1{x ↮ y}] ≤ E[F(K_x) 1{x ↮ y}] E G(K_y) ≤ E F(K_x) E G(K_y)`. -/
theorem lintegral_indicator_compl_conn_mul_le_mul_le (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y)) :
    ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q ≤
        (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
          ∫⁻ ω, G (cluster ω y) ∂law q ∧
      (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
          ∫⁻ ω, G (cluster ω y) ∂law q ≤
        (∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q :=
  ⟨lintegral_indicator_compl_conn_mul_le_mul q x y F G hG hFm hGm,
    mul_le_mul' (lintegral_mono fun ω => indicator_le_self _ _ ω) le_rfl⟩

omit [Countable V] in
/-- `E[F(K_x) 1{x ↮ y}] E G(K_y) ≤ E F(K_x) E G(K_y)`, the second step of the first chain. -/
theorem lintegral_indicator_compl_conn_mul_lintegral_le (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) :
    (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
        ∫⁻ ω, G (cluster ω y) ∂law q ≤
      (∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q :=
  mul_le_mul' (lintegral_mono fun ω => indicator_le_self _ _ ω) le_rfl

/-- **The second chain.** For `F`, `G` increasing,
`E F(K_x) E G(K_y) ≤ E[F(K_x) G(K_y)] ≤ E F(K_x) E G(K_y) + E[F(K_x) G(K_y) 1{x ↔ y}]`. -/
theorem lintegral_mul_lintegral_le_lintegral_mul_le_add (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) (hF : Monotone F) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y)) :
    (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) ≤
        ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ∧
      ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≤
        (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) +
          ∫⁻ ω, (conn x y).indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q :=
  ⟨clusterFunctionalHarris q x y F G hF hG hFm hGm,
    clusterCovarianceUpper q x y F G hF hG hFm hGm⟩

/-- **The covariance form.** For `F`, `G` increasing with `E[F(K_x) G(K_y)]`, `E F(K_x)` and
`E G(K_y)` finite, `0 ≤ Cov(F(K_x), G(K_y)) ≤ E[F(K_x) G(K_y) 1{x ↔ y}]`. -/
theorem covariance_cluster_nonneg_and_le (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) (hF : Monotone F) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y))
    (hFG : ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≠ ⊤)
    (hEF : ∫⁻ ω, F (cluster ω x) ∂law q ≠ ⊤) (hEG : ∫⁻ ω, G (cluster ω y) ∂law q ≠ ⊤) :
    0 ≤ cov[fun ω => (F (cluster ω x)).toReal, fun ω => (G (cluster ω y)).toReal; law q] ∧
      cov[fun ω => (F (cluster ω x)).toReal, fun ω => (G (cluster ω y)).toReal; law q] ≤
        (∫⁻ ω, (conn x y).indicator
          (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q).toReal := by
  rw [covariance_toReal_eq_sub hFm.aemeasurable hGm.aemeasurable hEF hEG hFG,
    ← ENNReal.toReal_mul]
  obtain ⟨hH, hU⟩ := lintegral_mul_lintegral_le_lintegral_mul_le_add q x y F G hF hG hFm hGm
  have hprod : (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) ≠ ⊤ :=
    ENNReal.mul_ne_top hEF hEG
  have hI : (∫⁻ ω, (conn x y).indicator
      (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q) ≠ ⊤ :=
    ne_top_of_le_ne_top hFG (lintegral_mono fun ω => indicator_le_self _ _ ω)
  constructor
  · exact sub_nonneg.mpr (ENNReal.toReal_mono hFG hH)
  · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hprod, hI⟩) hU
    rw [ENNReal.toReal_add hprod hI] at h
    linarith

/-- For `F`, `G` increasing with finite expectations, `0 ≤ Cov(F(K_x), G(K_y))`. -/
theorem covariance_cluster_nonneg (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) (hF : Monotone F) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y))
    (hFG : ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≠ ⊤)
    (hEF : ∫⁻ ω, F (cluster ω x) ∂law q ≠ ⊤) (hEG : ∫⁻ ω, G (cluster ω y) ∂law q ≠ ⊤) :
    0 ≤ cov[fun ω => (F (cluster ω x)).toReal, fun ω => (G (cluster ω y)).toReal; law q] :=
  (covariance_cluster_nonneg_and_le q x y F G hF hG hFm hGm hFG hEF hEG).1

/-- For `F`, `G` increasing with finite expectations,
`Cov(F(K_x), G(K_y)) ≤ E[F(K_x) G(K_y) 1{x ↔ y}]`. -/
theorem covariance_cluster_le (q : Sym2 V → unitInterval) (x y : V)
    (F G : Set V → ℝ≥0∞) (hF : Monotone F) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y))
    (hFG : ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≠ ⊤)
    (hEF : ∫⁻ ω, F (cluster ω x) ∂law q ≠ ⊤) (hEG : ∫⁻ ω, G (cluster ω y) ∂law q ≠ ⊤) :
    cov[fun ω => (F (cluster ω x)).toReal, fun ω => (G (cluster ω y)).toReal; law q] ≤
      (∫⁻ ω, (conn x y).indicator
        (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q).toReal :=
  (covariance_cluster_nonneg_and_le q x y F G hF hG hFm hGm hFG hEF hEG).2

end PercLib.Percolation.Bond
