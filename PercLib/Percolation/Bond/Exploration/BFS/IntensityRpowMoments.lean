/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof-only module; there is no counterpart in the source repository `yujinhkim/lrp`
(branch `work/yujinhkim-critical-lrp-orchestration`, head commit
`1a4906a25965de1bf9440b0af188deb0420c03a6`, Apache-2.0 licence): its
`PercLib/CriticalLRP/IntensityMoments.lean` (source revision
`95248147f2fcfeb9c2666c706089d86ee17887a6`) and
`PercLib/CriticalLRP/PowerLawHighTemp/Tail.lean` (source revision
`4a8819bfb7779ac3ff9bf079a8f8edc0a6b19536`) state the natural-exponent moments only, so the real-
exponent statements below are new mathematics, not a migration.

The scalar technique is the real-exponent analogue of the migrated scalar transfer in
`PercLib/Probability/Exploration/MomentBound.lean` (source revision
`d5e0763c9187ea85e4877ae4f6a19ab0b58c1c4d`, Apache-2.0); it is proved here from
`Real.log_le_sub_one_of_pos` and the calculus of `Real.rpow`. Production base
`2471b808cd0f1b79dc8a1ba514d43e63b9b9595c`, Lean 4.35.0, canonical namespace prefix
`PercLib.Percolation.Bond.Exploration.BFS` (scalar part:
`PercLib.Probability.ExplorationEnvelope`).

This module introduces no definition and no alternative configuration model: it is a
proof-only extension of the existing high-temperature cluster-moment API. Intended production
location `PercLib/Percolation/Bond/Exploration/BFS/IntensityRpowMoments.lean`.

Mathematical reference: M. Aizenman and C. M. Newman, *Tree graph inequalities and critical
behavior in percolation models*, J. Statist. Phys. 36 (1984), the exponential cluster tail at high
temperature, together with T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Definition I.1.3 and §I.1.2, whose long-range law this library
presents as `intensityProfile J β`.  The moment transfer itself (`x ^ q ≤ C λ ^ x` with
`C = (q / (e log λ))^q`) is elementary and carries no external input.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.IntensityMoments
public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Real-exponent cluster moments at high temperature

The exponential cluster moment `E[λ^{|K_o|}] ≤ 1/m` at `β M < 1` is converted into *every* real
moment `E[|K_o|^q]`, `q ≥ 0`, of the genuine (possibly infinite) cluster volume, with the
explicit constant `(q / (e log λ))^q / m` obtained from the maximization of `t ↦ t^q λ^{-t}`.
Nothing is restricted to natural exponents: the headline statements quantify over `q : ℝ`,
`0 ≤ q`, and the exponent is `ENNReal.rpow` on the extended cardinality
`((cluster ω o).encard : ℝ≥0∞)`, so that an infinite cluster contributes `⊤` rather than a
junk finite value. `q = 0` is included: then the constant is `1/m ≥ 1` and the moment is
`(prodBernoulli p) univ = 1`.

The two ingredients are, in order,

* a pointwise real-power comparison `x ^ q ≤ (q / (e log λ))^q * λ ^ x` for `x ≥ 0`, `q ≥ 0`,
  `λ > 1` (`rpow_le_mul_rpow_of_one_lt`) and its integrated form against an arbitrary measure;
* the identification, on the almost-sure finiteness event supplied by the exponential moment,
  of `((cluster ω o).encard : ℝ≥0∞) ^ q` with `ENNReal.ofReal ((encard.toNat : ℝ) ^ q)`
  (`ofReal_encard_toNat_rpow`), which is where the finite-cardinality conversion is made — it is
  never assumed, only derived a.e. from `∫⁻ λ^{|K_o|} < ∞`.

## Main results

* `rpow_le_mul_rpow_of_one_lt`, `lintegral_rpow_le_mul_lintegral_rpow`: the scalar and integrated
  real-power transfers;
* `lintegral_rpow_encard_cluster_le_of_epow`, `..._le_of_epow_toNat`, `..._le_inv_mul`,
  `..._le_zero`, `..._le_inv_mul_rowSum`, `exists_lam_forall_lintegral_rpow_encard_cluster_le`:
  explicit moment bounds from an exponential cluster moment, uniformly in the root;
* `lintegral_rpow_encard_cluster_ne_top`, `forall_lintegral_rpow_encard_cluster_ne_top`: every
  real moment of order `q ≥ 0` is finite;
* `lintegral_rpow_zero_encard_cluster`: the exponent `q = 0` is the total mass `1`;
* `lintegral_clusterVol_intensityProfile_rpow_le`, `..._ne_top`,
  `exists_lam_forall_lintegral_clusterVol_intensityProfile_rpow_le`: the intensity-profile forms at
  `β M < 1`, valid also at `(β M).toReal = 0`;
* `power_lintegral_encard_cluster_rpow_ne_top`, `power_forall_lintegral_encard_cluster_rpow_ne_top`,
  `exists_beta_interval_powerLaw_encard_cluster_rpow_ne_top`,
  `exists_lam_power_lintegral_encard_cluster_rpow_le`: the concrete summability power law on
  `Fin d → ℤ` for every real exponent `q ≥ 0`, every root, in the explicit region `β M < 1`, with
  a positive interval of such parameters.

## What is not claimed

No statement is made at `β M = 1` or above, at the critical parameter, or about sharpness. No
finite-volume, finite-box or `ncard` substitute is used. Nothing here is a cutoff statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability PercLib.Probability.ExplorationEnvelope
open scoped ENNReal NNReal BigOperators

namespace PercLib.Probability.ExplorationEnvelope

/-- **The real-exponent scalar transfer.**  For `λ > 1`, `q ≥ 0` and `x ≥ 0`,
`x ^ q ≤ (q / (e log λ))^q * λ ^ x`.  The constant is optimal: it is the value of
`x ↦ x^q λ^{-x}` at its maximum `x = q / log λ`.  For `q = 0` both sides are `1` and `λ ^ x ≥ 1`.

This is the real-exponent counterpart of `pow_le_factorial_div_log_mul_rpow`, which covers
natural `q` with the weaker constant `q! / (log λ)^q`. -/
theorem rpow_le_mul_rpow_of_one_lt {lam q x : ℝ} (hlam : 1 < lam) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    x ^ q ≤ (q / (Real.exp 1 * Real.log lam)) ^ q * lam ^ x := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hl : 0 < Real.log lam := Real.log_pos hlam
  have hden : 0 < Real.exp 1 * Real.log lam := mul_pos (Real.exp_pos 1) hl
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · rw [← hq0, Real.rpow_zero, Real.rpow_zero, one_mul]
    exact Real.one_le_rpow hlam.le hx
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0, Real.zero_rpow hqpos.ne', Real.rpow_zero, mul_one]
    exact (Real.rpow_pos_of_pos (div_pos hqpos hden) q).le
  have hbase : 0 < q / (Real.exp 1 * Real.log lam) := div_pos hqpos hden
  have hCpos : 0 < (q / (Real.exp 1 * Real.log lam)) ^ q := Real.rpow_pos_of_pos hbase q
  have ht : 0 < q / Real.log lam := div_pos hqpos hl
  -- `log x ≤ x / t - 1 + log t` at `t = q / log λ`, multiplied by `q > 0`
  have hlogineq : Real.log x ≤ x / (q / Real.log lam) - 1 + Real.log (q / Real.log lam) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hxpos ht)
    rw [Real.log_div hxpos.ne' ht.ne'] at h
    linarith
  have hmul : q * Real.log x
      ≤ q * (x / (q / Real.log lam) - 1 + Real.log (q / Real.log lam)) :=
    mul_le_mul_of_nonneg_left hlogineq hqpos.le
  have hxt : q * (x / (q / Real.log lam) - 1 + Real.log (q / Real.log lam))
      = x * Real.log lam + q * (Real.log (q / Real.log lam) - 1) := by
    field_simp
    ring
  have hlogC : Real.log ((q / (Real.exp 1 * Real.log lam)) ^ q)
      = q * (Real.log (q / Real.log lam) - 1) := by
    rw [Real.log_rpow hbase q, Real.log_div hqpos.ne' hden.ne',
      Real.log_mul (Real.exp_pos 1).ne' hl.ne', Real.log_exp,
      Real.log_div hqpos.ne' hl.ne']
    ring
  have hmain : q * Real.log x
      ≤ Real.log ((q / (Real.exp 1 * Real.log lam)) ^ q) + x * Real.log lam := by
    rw [hlogC]
    have h1 := hmul
    rw [hxt] at h1
    linarith
  calc x ^ q = Real.exp (q * Real.log x) := by
        rw [Real.rpow_def_of_pos hxpos, mul_comm]
    _ ≤ Real.exp (Real.log ((q / (Real.exp 1 * Real.log lam)) ^ q) + x * Real.log lam) :=
        Real.exp_le_exp.mpr hmain
    _ = (q / (Real.exp 1 * Real.log lam)) ^ q * lam ^ x := by
        rw [Real.exp_add, Real.exp_log hCpos, Real.rpow_def_of_pos hlam0,
          mul_comm (Real.log lam) x]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The real-exponent transfer, integrated.**  For `λ > 1`, `q ≥ 0` and a nonnegative real
random variable `N`, `∫⁻ N^q ≤ (q / (e log λ))^q * ∫⁻ λ^N`.

As in `lintegral_pow_le_mul_lintegral_rpow` neither measurability of `N` nor any condition on `m`
is needed: `ENNReal` lower integrals are monotone for arbitrary functions and the constant is
finite. -/
theorem lintegral_rpow_le_mul_lintegral_rpow {lam : ℝ} (hlam : 1 < lam) {q : ℝ} (hq : 0 ≤ q)
    {N : Ω → ℝ} (hN : ∀ ω, 0 ≤ N ω) :
    ∫⁻ ω, ENNReal.ofReal ((N ω) ^ q) ∂μ
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) *
          ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ := by
  have hC : (0 : ℝ) ≤ (q / (Real.exp 1 * Real.log lam)) ^ q :=
    Real.rpow_nonneg (div_nonneg hq (le_of_lt (mul_pos (Real.exp_pos 1) (Real.log_pos hlam)))) q
  calc ∫⁻ ω, ENNReal.ofReal ((N ω) ^ q) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) *
            ENNReal.ofReal (lam ^ N ω) ∂μ := by
        refine lintegral_mono (fun ω => ?_)
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (rpow_le_mul_rpow_of_one_lt hlam hq (hN ω))
    _ = ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) *
          ∫⁻ ω, ENNReal.ofReal (lam ^ N ω) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PercLib.Probability.ExplorationEnvelope

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- On an a.s. finite cluster, the real power of `encard.toNat` is the real power of the
extended cardinality.  This is the `q : ℝ` counterpart of `ofReal_encard_toNat_pow`; the
converse direction fails for `q < 0` at `encard = 0`, hence the hypothesis `0 ≤ q`. -/
theorem ofReal_encard_toNat_rpow (s : Set V) (hfin : s.encard ≠ ⊤) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((s.encard.toNat : ℝ) ^ q) = ((s.encard : ℝ≥0∞) ^ q) := by
  have hbase : ENNReal.ofReal (s.encard.toNat : ℝ) = (s.encard : ℝ≥0∞) := by
    calc ENNReal.ofReal (s.encard.toNat : ℝ) = (s.encard.toNat : ℝ≥0∞) :=
          ENNReal.ofReal_natCast _
      _ = (s.encard : ℝ≥0∞) := congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) (ENat.natCast_toNat hfin)
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq, hbase]

/-- **The a.e. form of `ofReal_encard_toNat_rpow`.** On configurations where the cluster is finite,
the extended real moment is the integral of `ENNReal.ofReal ((encard.toNat : ℝ) ^ q)`; this is the
step that lets a finite-cardinality computation be transported to the true `ENNReal.rpow` moment,
and it is valid only on the a.e.-finite event. -/
theorem lintegral_rpow_encard_cluster_eq_ofReal_toNat {p : Sym2 V → unitInterval} (o : V) {q : ℝ}
    (hq : 0 ≤ q) (hfin : ∀ᵐ ω ∂(prodBernoulli p), (cluster ω o).encard ≠ ⊤) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      = ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ q) ∂(prodBernoulli p) := by
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with ω hω
  exact (ofReal_encard_toNat_rpow (cluster ω o) hω hq).symm

/-- **The exponent `q = 0` is the total mass.**  With the convention `a ^ (0 : ℝ) = 1` of
`ENNReal.rpow`, the zeroth moment of the whole cluster is the total mass of the law, i.e. `1`; in
particular it is finite and independent of the cluster.  This is the one end of the exponent range
that is checked by the convention itself rather than by the transfer, and it needs no countability
of the vertex set. -/
theorem lintegral_rpow_zero_encard_cluster (p : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (0 : ℝ) ∂(prodBernoulli p) = 1 := by
  simp

variable [Countable V]

/-- **Every real moment of order `q ≥ 0` from an exponential cluster moment.**  If
`E[λ^{|K_o|}] ≤ C` for some `λ > 1` and finite `C`, then
`E[|K_o|^q] ≤ (q / (e log λ))^q * C` for every real `q ≥ 0`, where the moment is the
`ℝ≥0∞`-valued `ENNReal.rpow` moment of the genuine cluster cardinality.

The a.s. finiteness of the cluster is derived from the exponential moment
(`ae_encard_cluster_ne_top_of_epow_le`), not assumed: an infinite cluster on a set of positive
measure would make both the exponential moment and every `q > 0` moment infinite. -/
theorem lintegral_rpow_encard_cluster_le_of_epow {p : Sym2 V → unitInterval} (o : V)
    {lam C q : ℝ} (hlam : 1 < lam)
    (hint : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal C) (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * C) := by
  have hC0 : 0 ≤ (q / (Real.exp 1 * Real.log lam)) ^ q :=
    Real.rpow_nonneg (div_nonneg hq (le_of_lt (mul_pos (Real.exp_pos 1) (Real.log_pos hlam)))) q
  have hfin : ∀ᵐ ω ∂(prodBernoulli p), (cluster ω o).encard ≠ ⊤ :=
    ae_encard_cluster_ne_top_of_epow_le hlam hint
  have hpt : ∀ᵐ ω ∂(prodBernoulli p), ((cluster ω o).encard : ℝ≥0∞) ^ q
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) *
          epow (ENNReal.ofReal lam) ((cluster ω o).encard) := by
    filter_upwards [hfin] with ω hω
    have hx : (0 : ℝ) ≤ ((cluster ω o).encard.toNat : ℝ) := by positivity
    have h1 := rpow_le_mul_rpow_of_one_lt hlam hq hx
    have hpow : epow (ENNReal.ofReal lam) ((cluster ω o).encard)
        = ENNReal.ofReal (lam ^ ((cluster ω o).encard.toNat : ℝ)) := by
      conv_lhs => rw [← ENat.natCast_toNat hω]
      rw [epow_ofReal_pow hlam.le, Real.rpow_natCast]
    rw [← ofReal_encard_toNat_rpow (cluster ω o) hω hq, hpow, ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal h1
  calc ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      ≤ ∫⁻ ω, ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) *
          epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) *
          ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q) * ENNReal.ofReal C := by
        gcongr
    _ = ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * C) :=
        (ENNReal.ofReal_mul hC0).symm

/-- **The real moments with the explicit envelope constant `1 / m`.**  Hypothesis shape of
`lintegral_pow_encard_cluster_le_inv_mul`, with an arbitrary real exponent `q ≥ 0`. -/
theorem lintegral_rpow_encard_cluster_le_inv_mul {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * (1 / m)) :=
  lintegral_rpow_encard_cluster_le_of_epow o hlam
    (lintegral_epow_encard_cluster_le_inv_mul hrow o hlam.le hm hm1 hcond) hq

/-- The `m = 0` case of `lintegral_rpow_encard_cluster_le_inv_mul`: the envelope is identically
`1`, and the real moment is at most `(q / (e log λ))^q * λ`. -/
theorem lintegral_rpow_encard_cluster_le_zero {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : m = 0) (o : V) {lam : ℝ} (hlam : 1 < lam) {q : ℝ}
    (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * lam) :=
  lintegral_rpow_encard_cluster_le_of_epow o hlam
    (lintegral_epow_encard_cluster_le_zero hrow hm o hlam.le) hq

/-- **Bridge from the `encard.toNat` exponential moment.**  The hypothesis shape of the
production lemma `lintegral_rpow_encard_cluster_le`, i.e. an exponential moment written at the
finite cardinality `encard.toNat` as `E[λ^{|K_o|}] ≤ C`, already yields every real moment of order
`q ≥ 0`.  The almost-sure finiteness needed to read `encard` as `encard.toNat` is supplied by the
high-temperature row hypotheses (`ae_encard_cluster_ne_top`): the `toNat` form alone does not
exclude an infinite cluster, because `⊤.toNat = 0` contributes the junk value `λ ^ 0 = 1`. -/
theorem lintegral_rpow_encard_cluster_le_of_epow_toNat {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) {lam C q : ℝ}
    (hlam : 1 < lam)
    (hmom : ∫⁻ ω, ENNReal.ofReal (lam ^ ((cluster ω o).encard.toNat : ℝ)) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal C) (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * C) := by
  have hfin : ∀ᵐ ω ∂(prodBernoulli p), (cluster ω o).encard ≠ ⊤ :=
    ae_encard_cluster_ne_top hrow hm hm1 o
  have hint : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal C := by
    refine (lintegral_congr_ae ?_).trans_le hmom
    filter_upwards [hfin] with ω hω
    conv_lhs => rw [← ENat.natCast_toNat hω]
    rw [epow_ofReal_pow hlam.le, Real.rpow_natCast]
  exact lintegral_rpow_encard_cluster_le_of_epow o hlam hint hq

/-- `RowSum`-flavoured real moments (row sums including the diagonal), the `ℝ`-exponent
counterpart of `lintegral_pow_encard_cluster_le_inv_mul_rowSum`. -/
theorem lintegral_rpow_encard_cluster_le_inv_mul_rowSum {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : RowSum p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * (1 / m)) :=
  lintegral_rpow_encard_cluster_le_of_epow o hlam
    (lintegral_epow_encard_cluster_le_inv_mul_rowSum hrow o hlam.le hm hm1 hcond) hq

/-- **One admissible `λ` bounds every real moment at every root.**  The real-exponent
counterpart of `exists_lam_forall_lintegral_pow_encard_cluster_le`, with the same single `λ` for
all roots and all exponents. -/
theorem exists_lam_forall_lintegral_rpow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ (o : V) (q : ℝ), 0 ≤ q →
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p)
        ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * (1 / m)) := by
  obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, fun o q hq =>
    lintegral_rpow_encard_cluster_le_inv_mul hrow o hlam hm hm1.le hcond hq⟩

/-- **Every real cluster moment is finite at high temperature.**  For `0 < m < 1` the extended
moment `E[|K_o|^q]` is finite for every real `q ≥ 0` and every root `o`; the cluster is a.s.
finite as well. -/
theorem lintegral_rpow_encard_cluster_ne_top {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p) ≠ ⊤ := by
  obtain ⟨lam, hlam, h⟩ := exists_lam_forall_lintegral_rpow_encard_cluster_le hrow hm hm1
  exact ne_of_lt ((h o q hq).trans_lt ENNReal.ofReal_lt_top)

/-- The simultaneous form of `lintegral_rpow_encard_cluster_ne_top`: all real moments of order
`q ≥ 0` at a fixed root are finite at once, with a single `λ`. -/
theorem forall_lintegral_rpow_encard_cluster_ne_top {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) :
    ∀ q : ℝ, 0 ≤ q → ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(prodBernoulli p) ≠ ⊤ :=
  fun _ hq => lintegral_rpow_encard_cluster_ne_top hrow hm hm1 o hq

/-! ### The intensity-profile interface -/

/-- **Real moments under an intensity profile, with an explicit envelope constant.**  For an
`ℝ≥0`-valued intensity profile `J` whose off-diagonal rows are at most `M`, the `q`-th real
moment of the true cluster under the actual law `law (intensityProfile J β)` is at most
`(q / (e log λ))^q * C` for one admissible `λ > 1` and the envelope constant `C` of
`exists_lam_envelope_intensityProfile`.  This covers `(β M).toReal = 0`, where `C = 2`. -/
theorem lintegral_clusterVol_intensityProfile_rpow_le (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (o : V) {q : ℝ} (hq : 0 ≤ q) :
    ∃ lam C : ℝ, 1 < lam ∧
      (∀ n : ℕ, lam * envelope (((β : ℝ≥0∞) * M).toReal) lam n ≤ C) ∧
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(law (intensityProfile J β))
        ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * C) := by
  obtain ⟨lam, C, hlam, hC⟩ := exists_lam_envelope_intensityProfile J M hJ β hβ
  have hrow : UniformRowBound (intensityProfile J β) ((β : ℝ≥0∞) * M).toReal :=
    uniformRowBound_intensityProfile J M hJ β hβ
  exact ⟨lam, C, hlam, hC,
    lintegral_rpow_encard_cluster_le_of_epow o hlam
      (lintegral_epow_cluster_le_of_envelope_bound hrow o hlam.le hC) hq⟩

/-- **Every real cluster moment is finite for an intensity profile at `β M < 1`.**  This is the
real-exponent upgrade of `lintegral_clusterVol_intensity_pow_ne_top`. -/
theorem lintegral_clusterVol_intensityProfile_rpow_ne_top (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (o : V) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(law (intensityProfile J β)) ≠ ⊤ := by
  obtain ⟨lam, C, hlam, hC, hle⟩ := lintegral_clusterVol_intensityProfile_rpow_le J M hJ β hβ o hq
  exact ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)

/-- The simultaneous real-moment form for an intensity profile. -/
theorem forall_lintegral_clusterVol_intensityProfile_rpow_ne_top (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (o : V) :
    ∀ q : ℝ, 0 ≤ q →
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(law (intensityProfile J β)) ≠ ⊤ :=
  fun _ hq => lintegral_clusterVol_intensityProfile_rpow_ne_top J M hJ β hβ o hq

/-- **Root-uniform real moments for an intensity profile.**  A single admissible `λ > 1` and a
single envelope constant `C` bound the `q`-th real moment at *every* root and for *every* exponent
`q ≥ 0` simultaneously.  This is the real-exponent counterpart of
`exists_lam_envelope_intensityProfile` together with the natural-moment theorem; the profile's
off-diagonal rows are at most `M` and `β M < 1`. -/
theorem exists_lam_forall_lintegral_clusterVol_intensityProfile_rpow_le (J : Sym2 V → ℝ≥0)
    (M : ℝ≥0) (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    ∃ lam C : ℝ, 1 < lam ∧
      (∀ n : ℕ, lam * envelope (((β : ℝ≥0∞) * M).toReal) lam n ≤ C) ∧
      ∀ (o : V) (q : ℝ), 0 ≤ q →
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂(law (intensityProfile J β))
          ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q * C) := by
  obtain ⟨lam, C, hlam, hC⟩ := exists_lam_envelope_intensityProfile J M hJ β hβ
  have hrow : UniformRowBound (intensityProfile J β) ((β : ℝ≥0∞) * M).toReal :=
    uniformRowBound_intensityProfile J M hJ β hβ
  exact ⟨lam, C, hlam, hC, fun o q hq =>
    lintegral_rpow_encard_cluster_le_of_epow o hlam
      (lintegral_epow_cluster_le_of_envelope_bound hrow o hlam.le hC) hq⟩

end PercLib.Percolation.Bond.Exploration.BFS

namespace PercLib.Percolation.Bond.Exploration.BFS

/-! ### The concrete power law: every real moment at high temperature -/

/-- **Every real cluster moment of the power-law model is finite** at every lattice vertex, in the
explicit high-temperature region `β M < 1` with `M = ∑_z ‖z‖_∞^{-d-α}`, for every real exponent
`q ≥ 0`.  This is the real-exponent upgrade of `power_lintegral_encard_cluster_pow_ne_top`; the
moment is the extended one, `ENNReal.rpow` applied to the genuine cluster cardinality, so an
infinite cluster contributes `⊤`.  No statement is made at or above `β M = 1`. -/
theorem power_lintegral_encard_cluster_rpow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ q ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  classical
  have hrows : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, if w = v then 0 else
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(v, w) : ℝ≥0∞)) ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (power_rowSum_le hd (by linarith) (radialKernel_powerLaw_mk hα) v)
  have hJ : ∀ v : Fin d → ℤ,
      rowSum (fun e => (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) e : ℝ≥0∞)) v ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    rw [rowSum_def]
    refine le_of_eq_of_le ?_ (hrows v)
    exact tsum_congr fun w => by by_cases h : w = v <;> simp [h]
  exact lintegral_clusterVol_intensityProfile_rpow_ne_top
    (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)))
    (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ β hβ x hq

/-- Simultaneous form: all real moments of every order `q ≥ 0` are finite at once at a vertex. -/
theorem power_forall_lintegral_encard_cluster_rpow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∀ q : ℝ, 0 ≤ q →
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ q ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ :=
  fun _ hq => power_lintegral_encard_cluster_rpow_ne_top hd hα hβ x hq

/-- **An explicit moment bound for the power law.**  On the positive part of the high-temperature
region, one admissible `λ > 1` bounds *every* real moment of order `q ≥ 0` at every lattice
vertex by the explicit constant `(q / (e log λ))^q / (β M)`. -/
theorem exists_lam_power_lintegral_encard_cluster_rpow_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hm : 0 < ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ (x : Fin d → ℤ) (q : ℝ), 0 ≤ q →
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ q ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q *
            (1 / ((β : ℝ≥0∞) * (Real.toNNReal
              (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal)) := by
  classical
  have hrows : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, if w = v then 0 else
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) s(v, w) : ℝ≥0∞)) ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (power_rowSum_le hd (by linarith) (radialKernel_powerLaw_mk hα) v)
  have hJ : ∀ v : Fin d → ℤ,
      rowSum (fun e => (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) e : ℝ≥0∞)) v ≤
        (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) := by
    intro v
    rw [rowSum_def]
    refine le_of_eq_of_le ?_ (hrows v)
    exact tsum_congr fun w => by by_cases h : w = v <;> simp [h]
  have hrow : UniformRowBound (intensityProfile
      (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)
      ((β : ℝ≥0∞) * (Real.toNNReal
        (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal :=
    uniformRowBound_intensityProfile _ _ hJ β hβ
  have hm1 : ((β : ℝ≥0∞) * (Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal < 1 :=
    intensity_toReal_mul_lt_one _ hβ
  obtain ⟨lam, hlam, hcond⟩ :=
    PercLib.Probability.ExplorationEnvelope.exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, fun x q hq =>
    lintegral_rpow_encard_cluster_le_inv_mul hrow x hlam hm hm1.le hcond hq⟩

/-- **A positive interval of parameters on which every real cluster moment of the power-law
model is finite.**  The endpoint is `β₀ = (M + 1)⁻¹` with `M = ∑_z ‖z‖_∞^{-d-α}`; the statement
produces it, so the high-temperature region is not a single point.  Nothing is claimed at `β₀`
or beyond. -/
theorem exists_beta_interval_powerLaw_encard_cluster_rpow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (x : Fin d → ℤ) (q : ℝ), 0 ≤ q →
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ q ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  refine ⟨((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) + 1)⁻¹,
    inv_pos.mpr (by positivity), fun β hβ x q hq => ?_⟩
  exact power_lintegral_encard_cluster_rpow_ne_top hd hα
    (mul_coe_lt_one_of_lt_inv_add_one hβ) x hq

/-! ### Consistency and non-vacuity checks -/

/-- The real statement at `q = 1` is the first-moment statement (its `ENNReal.rpow` form). -/
example {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  simpa only [ENNReal.rpow_one] using power_lintegral_encard_cluster_rpow_ne_top hd hα hβ x
    (zero_le_one' ℝ)

/-- The statement is not restricted to natural exponents: order `1/2`. -/
example {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ ((1 : ℝ) / 2) ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ :=
  power_lintegral_encard_cluster_rpow_ne_top hd hα hβ x (by norm_num)

/-- The exponent `q = 0` is included: the moment is then `(law …) univ = 1`. -/
example {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ (0 : ℝ) ∂
      (law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ :=
  power_lintegral_encard_cluster_rpow_ne_top hd hα hβ x (le_refl 0)

/-- Non-vacuity: a **positive** parameter at which every real moment is finite, at every vertex. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ q : ℝ, 0 ≤ q →
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ q ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  obtain ⟨β, hβ, hβM, _⟩ := exists_beta_positive_powerLaw hd hα
  exact ⟨β, hβ, fun q hq => power_lintegral_encard_cluster_rpow_ne_top hd hα hβM x hq⟩

/-- Non-vacuity of the explicit-bound form: at a positive parameter, some `λ > 1` bounds every
real moment of the power-law model by the stated explicit constant. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧ ∃ lam : ℝ, 1 < lam ∧ ∀ q : ℝ, 0 ≤ q →
      ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ q ∂
        (law (intensityProfile
          (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β))
        ≤ ENNReal.ofReal ((q / (Real.exp 1 * Real.log lam)) ^ q *
            (1 / ((β : ℝ≥0∞) * (Real.toNNReal
              (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)).toReal)) := by
  obtain ⟨β, hβ, hβM, hm⟩ := exists_beta_positive_powerLaw hd hα
  obtain ⟨lam, hlam, h⟩ := exists_lam_power_lintegral_encard_cluster_rpow_le hd hα hβM hm
  exact ⟨β, hβ, lam, hlam, h x⟩

end PercLib.Percolation.Bond.Exploration.BFS
