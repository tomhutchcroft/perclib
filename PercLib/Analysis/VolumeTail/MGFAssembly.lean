/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The moving-scale cut-off limit (I.3.7) and the ghost-restoration assembly of the Laplace
asymptotic (I.3.2) in the proof of Proposition I.3.2 of T. Hutchcroft, *Critical long-range
percolation I: High effective dimension*, arXiv:2508.18807v1, §I.3.2.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/MGFAssembly.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the structure `RVPosData` is unbundled into the hypotheses of
`PercLib/Analysis/RegularVariation/GeneralInverse.lean` and `RVPosData.genInv` is
`genInv f x₀`; the source's `mean`, `sbMean` and `sizeBiasedLaw` are written out as
`∫ x, x ∂μ`, `(∫ x, x ^ 2 ∂μ) / ∫ x, x ∂μ` and the size-biased law of
`PercLib/Analysis/VolumeTail/SizeBiasMGF.lean`; the kernel `kern` (value `0` at `0`) is the
kernel `f_λ` of `PercLib/Probability/SizeBiasLimits.lean` (value `λ` at `0`), so the no-atom and
support hypotheses on `Q∞` are removed where the proofs no longer use them; the definitions
`lapDefect` and `FullLawGhostRatio` are written out; the ε-arguments of
`mgf_of_fullLawGhostRatio` are proved once for abstract families
(`tendsto_div_of_forall_tendsto_of_comparison`); `const_eq` is replaced by
`div_mul_rpow_div_rpow_eq_mul_rpow_neg`; hypotheses the proofs do not use are removed;
declarations are renamed; `import Mathlib`, `autoImplicit`, disabled linters and `#print` lines
are removed.
-/
module

public import PercLib.Analysis.VolumeTail.Normalizer
public import PercLib.Probability.WeakKernels

/-! # The cut-off limit and the ghost-restoration assembly for Proposition I.3.2

Let `μ_r` be laws on `[0, ∞)` with `E_r X ~ A₁ r^α`, size-biased mean
`Ê_r X = E_r X² / E_r X ~ A₂ f(r)` for `f` regularly varying of index `a α`, and size-biased
laws `Q_r` of `X / Ê_r X` converging weakly to `Q∞`. With the generalized inverse
`g = genInv f x₀`, the cut-off `r_λ(h) = g(λ / (A₂ h))` fills the level `h Ê_{r_λ(h)} X → λ`,
and the cut-off Laplace defect satisfies (I.3.7):

  `E_{r_λ(h)}[1 - e^{-hX}] / (g(1/h)^α h) → (A₁ / A₂^{1/a}) λ^{-(a-1)/a} ∫ f_λ dQ∞`.

A uniform comparison of the uncut law `μ∞` with the cut-off laws (the ratio form of (I.3.5),
(I.3.6), hypothesis `hG` below) transfers this to the uncut law, giving (I.3.2).

## Main results

* `tendsto_div_of_forall_tendsto_of_comparison`: the transfer for abstract families.
* `forall_le_one_add_mul_of_comparison`, `exists_tendsto_atTop_of_forall_le_one_add_mul`,
  `eventually_le_of_comparison`: the comparison makes the candidate constants relatively
  Cauchy, hence convergent, with limit above them.
* `tendsto_laplace_div_genInv_rpow_mul`, `tendsto_laplace_div_genInv_rpow_mul_rpow_neg`: the
  cut-off limit (I.3.7) at the moving scale.
* `tendsto_laplace_div_genInv_of_comparison`: (I.3.2) from the comparison and the `λ → ∞`
  limit of the constants.
* `comparison_of_restoration`: the comparison from the restoration inequality (I.3.5).

These are analytic steps of the proof of Proposition I.3.2, not that proposition.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory Real
open scoped Topology ENNReal

namespace PercLib.Analysis

open PercLib.Probability

/-! ### The comparison argument for abstract families -/

/-- `(1 - η)⁻¹ ≤ 1 + 2η` for `0 ≤ η ≤ 1/2`. -/
theorem inv_one_sub_le_one_add_two_mul {η : ℝ} (hη : 0 ≤ η) (hη2 : η ≤ 1 / 2) :
    (1 - η)⁻¹ ≤ 1 + 2 * η := by
  rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- A uniform comparison `L ≤ U ≤ L (1 - η)⁻¹` with `η > 0` forces `L ≥ 0`. -/
theorem nonneg_of_le_of_le_mul_inv_one_sub {L U η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (h1 : L ≤ U) (h2 : U ≤ L * (1 - η)⁻¹) : 0 ≤ L := by
  by_contra hL
  push Not at hL
  have hk : 1 < (1 - η)⁻¹ := by
    rw [lt_inv_comm₀ one_pos (by linarith), inv_one]
    linarith
  nlinarith

/-- **Transfer of cut-off limits through a uniform comparison.** Let `L λ h / N h → c λ` along
`l` for every `λ > 0`, with `N > 0` eventually, and `c λ → A` as `λ → ∞`. If for every
`η ∈ (0, 1/2]` there is `Λ` such that for every `λ ≥ Λ`, eventually along `l`,
`L λ h ≤ U h ≤ L λ h (1 - η)⁻¹`, then `U h / N h → A`. -/
theorem tendsto_div_of_forall_tendsto_of_comparison {ι : Type*} {l : Filter ι}
    {L : ℝ → ι → ℝ} {U N : ι → ℝ} {c : ℝ → ℝ} {A : ℝ} (hN : ∀ᶠ h in l, 0 < N h)
    (hL : ∀ lam, 0 < lam → Tendsto (fun h => L lam h / N h) l (𝓝 (c lam)))
    (hc : Tendsto c atTop (𝓝 A))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, ∀ lam, Λ ≤ lam →
      ∀ᶠ h in l, L lam h ≤ U h ∧ U h ≤ L lam h * (1 - η)⁻¹) :
    Tendsto (fun h => U h / N h) l (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := min (1 / 2) (ε / (4 * (|A| + ε))) with hηdef
  have hAε : 0 < |A| + ε := by positivity
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη2 : η ≤ 1 / 2 := min_le_left _ _
  have hηε : 2 * η * (|A| + ε / 2) ≤ ε / 2 := by
    have h1 : η ≤ ε / (4 * (|A| + ε)) := min_le_right _ _
    have h2 : 2 * η * (|A| + ε / 2) ≤ 2 * (ε / (4 * (|A| + ε))) * (|A| + ε) := by
      have : |A| + ε / 2 ≤ |A| + ε := by linarith
      have h0 : 0 ≤ 2 * η := by linarith
      calc 2 * η * (|A| + ε / 2) ≤ 2 * η * (|A| + ε) := mul_le_mul_of_nonneg_left this h0
        _ ≤ 2 * (ε / (4 * (|A| + ε))) * (|A| + ε) := by gcongr
    have h3 : 2 * (ε / (4 * (|A| + ε))) * (|A| + ε) = ε / 2 := by
      field_simp
      ring
    linarith
  obtain ⟨Λ, hΛ⟩ := hG η hη0 hη2
  obtain ⟨lam, hlamc, hlamΛ, hlam0⟩ :=
    ((hc.eventually (Metric.ball_mem_nhds A (by positivity : 0 < ε / 4))).and
      ((eventually_ge_atTop Λ).and (eventually_gt_atTop (0 : ℝ)))).exists
  rw [Real.dist_eq] at hlamc
  have hk := inv_one_sub_le_one_add_two_mul hη0.le hη2
  filter_upwards [(hL lam hlam0).eventually (Metric.ball_mem_nhds (c lam)
    (by positivity : 0 < ε / 4)), hΛ lam hlamΛ, hN] with h hY hcomp hNh
  rw [Real.dist_eq] at hY
  rw [Real.dist_eq]
  have hL0 : 0 ≤ L lam h := nonneg_of_le_of_le_mul_inv_one_sub hη0 hη2 hcomp.1 hcomp.2
  set Y := L lam h / N h with hYdef
  have hY0 : 0 ≤ Y := div_nonneg hL0 hNh.le
  have hlow : Y ≤ U h / N h := div_le_div_of_nonneg_right hcomp.1 hNh.le
  have hupp : U h / N h ≤ Y * (1 + 2 * η) := by
    calc U h / N h ≤ L lam h * (1 - η)⁻¹ / N h := div_le_div_of_nonneg_right hcomp.2 hNh.le
      _ = Y * (1 - η)⁻¹ := by rw [hYdef]; ring
      _ ≤ Y * (1 + 2 * η) := mul_le_mul_of_nonneg_left hk hY0
  have hYA : |Y - A| < ε / 2 := by
    calc |Y - A| ≤ |Y - c lam| + |c lam - A| := abs_sub_le _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add hY hlamc
      _ = ε / 2 := by ring
  have hYle : Y ≤ |A| + ε / 2 := by
    have := (abs_lt.1 hYA).2
    linarith [le_abs_self A]
  have hcorr : Y * (2 * η) ≤ ε / 2 := by
    calc Y * (2 * η) ≤ (|A| + ε / 2) * (2 * η) := mul_le_mul_of_nonneg_right hYle (by linarith)
      _ = 2 * η * (|A| + ε / 2) := by ring
      _ ≤ ε / 2 := hηε
  rw [abs_lt]
  constructor
  · linarith [(abs_lt.1 hYA).1]
  · nlinarith [(abs_lt.1 hYA).2]

/-- **The comparison makes the candidate constants relatively Cauchy.** Under the hypotheses of
`tendsto_div_of_forall_tendsto_of_comparison` (without the limit of `c`), along a nontrivial
filter: for every `ε > 0` there is `Λ` with `c x ≤ (1 + ε) c y` for all `x, y ≥ Λ`. -/
theorem forall_le_one_add_mul_of_comparison {ι : Type*} {l : Filter ι} [l.NeBot]
    {L : ℝ → ι → ℝ} {U N : ι → ℝ} {c : ℝ → ℝ} (hN : ∀ᶠ h in l, 0 < N h)
    (hL : ∀ lam, 0 < lam → Tendsto (fun h => L lam h / N h) l (𝓝 (c lam)))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, ∀ lam, Λ ≤ lam →
      ∀ᶠ h in l, L lam h ≤ U h ∧ U h ≤ L lam h * (1 - η)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ Λ : ℝ, ∀ x, Λ ≤ x → ∀ y, Λ ≤ y → c x ≤ (1 + ε) * c y := by
  intro ε hε
  set η : ℝ := min (1 / 2) (ε / 2)
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hη2 : η ≤ 1 / 2 := min_le_left _ _
  have hk : (1 - η)⁻¹ ≤ 1 + ε := by
    have := inv_one_sub_le_one_add_two_mul hη0.le hη2
    have : η ≤ ε / 2 := min_le_right _ _
    linarith
  obtain ⟨Λ, hΛ⟩ := hG η hη0 hη2
  refine ⟨max Λ 1, fun x hx y hy => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hy)
  have hxΛ : Λ ≤ x := le_trans (le_max_left _ _) hx
  have hyΛ : Λ ≤ y := le_trans (le_max_left _ _) hy
  have hev : ∀ᶠ h in l, L x h / N h ≤ L y h / N h * (1 - η)⁻¹ := by
    filter_upwards [hΛ x hxΛ, hΛ y hyΛ, hN] with h hxh hyh hNh
    calc L x h / N h ≤ L y h * (1 - η)⁻¹ / N h :=
          div_le_div_of_nonneg_right (hxh.1.trans hyh.2) hNh.le
      _ = L y h / N h * (1 - η)⁻¹ := by ring
  have hcy : 0 ≤ c y := by
    refine ge_of_tendsto (hL y hy0) ?_
    filter_upwards [hΛ y hyΛ, hN] with h hyh hNh
    exact div_nonneg (nonneg_of_le_of_le_mul_inv_one_sub hη0 hη2 hyh.1 hyh.2) hNh.le
  have hle := le_of_tendsto_of_tendsto (hL x hx0) ((hL y hy0).mul_const _) hev
  calc c x ≤ c y * (1 - η)⁻¹ := hle
    _ ≤ c y * (1 + ε) := mul_le_mul_of_nonneg_left hk hcy
    _ = (1 + ε) * c y := mul_comm _ _

/-- **Relatively Cauchy functions converge.** If `c ≥ 0` eventually and for every `ε > 0` there
is `Λ` with `c x ≤ (1 + ε) c y` for all `x, y ≥ Λ`, then `c` converges along `atTop`. No
monotonicity is used. -/
theorem exists_tendsto_atTop_of_forall_le_one_add_mul {α : Type*} [SemilatticeSup α]
    [Nonempty α] {c : α → ℝ} (hnn : ∀ᶠ x in atTop, 0 ≤ c x)
    (hrel : ∀ ε : ℝ, 0 < ε → ∃ Λ, ∀ x, Λ ≤ x → ∀ y, Λ ≤ y → c x ≤ (1 + ε) * c y) :
    ∃ A, Tendsto c atTop (𝓝 A) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 hnn
  obtain ⟨Λ₁, hΛ₁⟩ := hrel 1 one_pos
  set M := Λ₀ ⊔ Λ₁
  have hB : ∀ x, M ≤ x → c x ≤ 2 * c M := fun x hx => by
    have := hΛ₁ x (le_trans le_sup_right hx) M le_sup_right
    linarith
  have hM0 : 0 ≤ c M := hΛ₀ M le_sup_left
  set δ := ε / (2 * c M + 1)
  have hδ : 0 < δ := by positivity
  have hδB : δ * (2 * c M) < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨Λ₂, hΛ₂⟩ := hrel δ hδ
  refine ⟨M ⊔ Λ₂, fun n hn => ?_⟩
  have hnM : M ≤ n := le_trans le_sup_left hn
  have hN2 : Λ₂ ≤ M ⊔ Λ₂ := le_sup_right
  have hn2 : Λ₂ ≤ n := le_trans hN2 hn
  have h1 := hΛ₂ n hn2 (M ⊔ Λ₂) hN2
  have h2 := hΛ₂ (M ⊔ Λ₂) hN2 n hn2
  have hcn := hB n hnM
  have hcN := hB (M ⊔ Λ₂) le_sup_left
  have hcn0 : 0 ≤ c n := hΛ₀ n (le_trans le_sup_left hnM)
  have hcN0 : 0 ≤ c (M ⊔ Λ₂) := hΛ₀ _ (le_trans le_sup_left le_sup_left)
  rw [Real.dist_eq, abs_lt]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hcn hδ.le]
  · nlinarith [mul_le_mul_of_nonneg_left hcN hδ.le]

/-- **The limit lies above the candidate constants.** If `L λ h / N h → c λ` for `λ > 0`,
`L λ h ≤ U h` eventually for every `λ ≥ Λ`, and `U h / N h → A` along a nontrivial filter, then
`c λ ≤ A` for all large `λ`. -/
theorem eventually_le_of_comparison {ι : Type*} {l : Filter ι} [l.NeBot] {L : ℝ → ι → ℝ}
    {U N : ι → ℝ} {c : ℝ → ℝ} {A Λ : ℝ} (hN : ∀ᶠ h in l, 0 < N h)
    (hL : ∀ lam, 0 < lam → Tendsto (fun h => L lam h / N h) l (𝓝 (c lam)))
    (hG : ∀ lam, Λ ≤ lam → ∀ᶠ h in l, L lam h ≤ U h)
    (hU : Tendsto (fun h => U h / N h) l (𝓝 A)) :
    ∀ᶠ lam in atTop, c lam ≤ A := by
  filter_upwards [eventually_ge_atTop Λ, eventually_gt_atTop (0 : ℝ)] with lam hlΛ hl0
  refine le_of_tendsto_of_tendsto (hL lam hl0) hU ?_
  filter_upwards [hG lam hlΛ, hN] with h hh hNh
  exact div_le_div_of_nonneg_right hh hNh.le

/-- **The comparison produces the limit constant.** Under the hypotheses of
`forall_le_one_add_mul_of_comparison`, the candidate constants converge to some `A ≥ 0`,
`U h / N h → A`, and `c λ ≤ A` for all large `λ`; in particular `A > 0` when `c λ > 0` for all
`λ > 0`. -/
theorem exists_tendsto_of_comparison {ι : Type*} {l : Filter ι} [l.NeBot]
    {L : ℝ → ι → ℝ} {U N : ι → ℝ} {c : ℝ → ℝ} (hN : ∀ᶠ h in l, 0 < N h)
    (hL : ∀ lam, 0 < lam → Tendsto (fun h => L lam h / N h) l (𝓝 (c lam)))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, ∀ lam, Λ ≤ lam →
      ∀ᶠ h in l, L lam h ≤ U h ∧ U h ≤ L lam h * (1 - η)⁻¹) :
    ∃ A, 0 ≤ A ∧ Tendsto c atTop (𝓝 A) ∧ Tendsto (fun h => U h / N h) l (𝓝 A) ∧
      ∀ᶠ lam in atTop, c lam ≤ A := by
  obtain ⟨Λ, hΛ⟩ := hG (1 / 2) (by norm_num) le_rfl
  have hcnn : ∀ᶠ lam in atTop, 0 ≤ c lam := by
    filter_upwards [eventually_ge_atTop Λ, eventually_gt_atTop (0 : ℝ)] with lam hlΛ hl0
    refine ge_of_tendsto (hL lam hl0) ?_
    filter_upwards [hΛ lam hlΛ, hN] with h hh hNh
    exact div_nonneg (nonneg_of_le_of_le_mul_inv_one_sub (by norm_num) le_rfl hh.1 hh.2)
      hNh.le
  obtain ⟨A, hA⟩ := exists_tendsto_atTop_of_forall_le_one_add_mul hcnn
    (forall_le_one_add_mul_of_comparison hN hL hG)
  have hU := tendsto_div_of_forall_tendsto_of_comparison hN hL hA hG
  exact ⟨A, ge_of_tendsto hA hcnn, hA, hU,
    eventually_le_of_comparison hN hL (fun lam hl => (hΛ lam hl).mono fun _ h => h.1) hU⟩

/-! ### Laplace defects -/

/-- The Laplace defect `E[1 - e^{-hX}]` of a law on `[0, ∞)` is nonnegative for `h ≥ 0`. -/
theorem integral_one_sub_exp_neg_mul_nonneg {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) {h : ℝ}
    (hh : 0 ≤ h) : 0 ≤ ∫ x, (1 - exp (-(h * x))) ∂μ := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [(ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) hμ) :
    ∀ᵐ x ∂μ, 0 ≤ x)] with x hx
  exact sub_nonneg.2 (exp_le_one_iff.2 (by nlinarith))

/-! ### The cut-off limit at the moving scale -/

/-- **The cut-off limit (I.3.7) at the moving scale**, for a fixed rate `λ > 0`. Let `μ_r` be
laws on `[0, ∞)` with `m_r = E_r X > 0`, `s_r = E_r X² / m_r > 0`, `m_r / (A₁ r^α) → 1` and
`s_r / f(r) → A₂ > 0`, where `f` is measurable and regularly varying of index `a α` with a
threshold `x₀`, and let the size-biased laws `Q_r` of `X / s_r` converge weakly to `Q∞`. With
`g = genInv f x₀` and `r_λ(h) = g(λ / (A₂ h))`,
`E_{r_λ(h)}[1 - e^{-hX}] / (g(1/h)^α h) → (A₁ ∫ f_λ dQ∞ / λ) (λ / A₂)^{1/a}` as `h ↓ 0`. -/
theorem tendsto_laplace_div_genInv_rpow_mul (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ} (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ a α : ℝ} (hA₂ : 0 < A₂) (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) /
        (genInv f x₀ (1 / h) ^ α * h)) (𝓝[>] 0)
      (𝓝 (A₁ * (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf) / lam *
        (lam / A₂) ^ (1 / a))) := by
  have hρ : 0 < ρ := hρα ▸ mul_pos ha hα
  have hA₁ : A₁ ≠ 0 := by
    rintro rfl
    simp at hE
  have hrfun : Tendsto (fun h : ℝ => genInv f x₀ (lam / (A₂ * h))) (𝓝[>] 0) atTop :=
    (hf.tendsto_genInv_atTop hρ hmeas hbdd).comp (tendsto_level_arg hA₂ hlam)
  have hrate : Tendsto (fun h : ℝ => h * ((∫ x, x ^ 2 ∂mu (genInv f x₀ (lam / (A₂ * h)))) /
      ∫ x, x ∂mu (genInv f x₀ (lam / (A₂ * h))))) (𝓝[>] 0) (𝓝 lam) :=
    hf.tendsto_level_filled_of_tendsto_div hρ hmeas hx₀ hpos hbdd
      (ψ := fun r => (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r) hA₂ hlam hS
  have hX0 : ∀ r, 0 ≤ᵐ[mu r] fun x => x := fun r =>
    ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) (hmu r))
  have hker := tendsto_integral_laplaceKernel_comp hconv
    (fun r => map_withDensity_ofReal_div_Iio_zero (mu r) (X := fun x => x) measurable_id (hX0 r)
      _ (hSpos r)) hrfun hrate hlam
  simp only [Measure.coe_toProbabilityMeasure] at hker
  have hscale := hf.tendsto_level_normalization hρ hmeas hx₀ hpos hbdd ha hα hρα hA₂ hlam
  have hE1 := hE.comp hrfun
  have hA2c : Tendsto (fun h : ℝ => A₁ / (h * ((∫ x, x ^ 2 ∂mu (genInv f x₀ (lam / (A₂ * h)))) /
      ∫ x, x ∂mu (genInv f x₀ (lam / (A₂ * h)))))) (𝓝[>] 0) (𝓝 (A₁ / lam)) :=
    tendsto_const_nhds.div hrate hlam.ne'
  have hprod := ((hE1.mul hA2c).mul hker).mul hscale
  rw [show 1 * (A₁ / lam) * (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf) *
      (lam / A₂) ^ (1 / a) = A₁ * (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y)
        ∂Qinf) / lam * (lam / A₂) ^ (1 / a) by ring] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (0 : ℝ) < h := hh
  have hr : 0 < genInv f x₀ (lam / (A₂ * h)) := hf.genInv_pos hρ hmeas hx₀ _
  have hτ : 0 < genInv f x₀ (1 / h) := hf.genInv_pos hρ hmeas hx₀ _
  have key : ∀ m s J R T : ℝ, m ≠ 0 → s ≠ 0 → R ≠ 0 → T ≠ 0 →
      m / (A₁ * R) * (A₁ / (h * s)) * J * (R / T) = m / s * J / (T * h) := by
    intro m s J R T hm hs hR hT
    field_simp
  rw [integral_one_sub_exp_eq_mul_integral_laplaceKernel (mu (genInv f x₀ (lam / (A₂ * h))))
    (X := fun x => x) measurable_id (hX0 _) (hSpos _) (hEpos _) h]
  exact key _ _ _ _ _ (hEpos _).ne' (hSpos _).ne' (Real.rpow_pos_of_pos hr α).ne'
    (Real.rpow_pos_of_pos hτ α).ne'

/-- **The cut-off limit (I.3.7) in the paper's constant form**:
`E_{r_λ(h)}[1 - e^{-hX}] / (g(1/h)^α h) → (A₁ / A₂^{1/a}) λ^{-(a-1)/a} ∫ f_λ dQ∞`, the bracket
of (I.3.7). -/
theorem tendsto_laplace_div_genInv_rpow_mul_rpow_neg (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ} (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ a α : ℝ} (hA₂ : 0 < A₂) (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) /
        (genInv f x₀ (1 / h) ^ α * h)) (𝓝[>] 0)
      (𝓝 (A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
        ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf)) := by
  have h := tendsto_laplace_div_genInv_rpow_mul mu Qinf hmeas hf hx₀ hpos hbdd hmu hEpos hSpos
    hprob hconv hA₂ ha hα hρα hE hS hlam
  have e : ∀ J : ℝ, A₁ * J / lam * (lam / A₂) ^ (1 / a) =
      A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) * J := fun J => by
    rw [Real.div_rpow hlam.le hA₂.le, ← div_mul_rpow_div_rpow_eq_mul_rpow_neg hA₂ hlam ha.ne']
    ring
  rwa [e] at h

/-! ### The uncut Laplace asymptotic (I.3.2) -/

/-- **The Laplace asymptotic (I.3.2) from the ghost comparison.** Under the hypotheses of
`tendsto_laplace_div_genInv_rpow_mul_rpow_neg`, let `μ∞` be a law such that for every
`η ∈ (0, 1/2]` there is `Λ > 0` such that for every `λ ≥ Λ`, for all small `h > 0`, the uncut
and cut-off Laplace defects at the cut-off `r_λ(h)` compare within the factor `(1 - η)⁻¹` (the
ratio form of (I.3.5), (I.3.6)). If the constants
`(A₁ / A₂^{1/a}) λ^{-(a-1)/a} ∫ f_λ dQ∞` tend to `A₃` as `λ → ∞`, then
`E_∞[1 - e^{-hX}] / (g(1/h)^α h) → A₃` as `h ↓ 0`. -/
theorem tendsto_laplace_div_genInv_of_comparison (mu : ℝ → Measure ℝ) (muinf : Measure ℝ)
    (Qinf : Measure ℝ) [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ}
    (hmeas : Measurable f) (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < f x) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂mu r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ a α A₃ : ℝ} (hA₂ : 0 < A₂) (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    (hJ : Tendsto (fun lam => A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) *
      ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Qinf) atTop (𝓝 A₃))
    (hG : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam, Λ ≤ lam →
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h))) ≤
          ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
        ∫ x, (1 - exp (-(h * x))) ∂muinf ≤
          (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) * (1 - η)⁻¹) :
    Tendsto (fun h : ℝ => (∫ x, (1 - exp (-(h * x))) ∂muinf) / (genInv f x₀ (1 / h) ^ α * h))
      (𝓝[>] 0) (𝓝 A₃) := by
  have hρ : 0 < ρ := hρα ▸ mul_pos ha hα
  refine tendsto_div_of_forall_tendsto_of_comparison
    (L := fun lam h => ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h))))
    ?_ (fun lam hlam => tendsto_laplace_div_genInv_rpow_mul_rpow_neg mu Qinf hmeas hf hx₀ hpos
      hbdd hmu hEpos hSpos hprob hconv hA₂ ha hα hρα hE hS hlam) hJ
    (fun η hη hη2 => (hG η hη hη2).imp fun _ h => h.2)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact mul_pos (Real.rpow_pos_of_pos (hf.genInv_pos hρ hmeas hx₀ _) α) hh

/-! ### The comparison from the restoration inequality -/

/-- **The ghost comparison from the restoration inequality (I.3.5).** Let `μ_r`, `Q_r`, `Q∞`,
`f`, `x₀` be as in `tendsto_laplace_div_genInv_rpow_mul`, with `ρ > 0` and `Q∞ {0} = 0`, and let
`μ∞` be a law on `[0, ∞)` such that for all large `r` and all `h > 0`,
`E_r[1 - e^{-hX}] ≤ E_∞[1 - e^{-hX}] ≤ E_r[1 - e^{-hX}] + C r^{-α} E_r[X e^{-hX}] E_∞[1 - e^{-hX}]`.
Then for every `η ∈ (0, 1/2]` there is `Λ > 0` such that for every `λ ≥ Λ`, for all small
`h > 0`, the uncut and cut-off Laplace defects at `r_λ(h) = genInv f x₀ (λ / (A₂ h))` compare
within the factor `(1 - η)⁻¹`. -/
theorem comparison_of_restoration (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    [IsProbabilityMeasure Qinf] {f : ℝ → ℝ} {ρ x₀ : ℝ} (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C)
    (hmu : ∀ r, mu r (Iio 0) = 0) (hmuinf : muinf (Iio 0) = 0)
    (hEpos : ∀ r, 0 < ∫ x, x ∂mu r) (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)
    (hprob : ∀ r, IsProbabilityMeasure (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)))
    (hQinf0 : Qinf {0} = 0)
    (hconv : Tendsto (fun r => (((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x =>
        x / ((∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r)).toProbabilityMeasure) atTop
      (𝓝 Qinf.toProbabilityMeasure))
    {A₁ A₂ α C : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hC : 0 < C)
    (hE : Tendsto (fun r => (∫ x, x ∂mu r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hS : Tendsto (fun r => (∫ x, x ^ 2 ∂mu r) / (∫ x, x ∂mu r) / f r) atTop (𝓝 A₂))
    (hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      ∫ x, (1 - exp (-(h * x))) ∂mu r ≤ ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
      ∫ x, (1 - exp (-(h * x))) ∂muinf ≤ ∫ x, (1 - exp (-(h * x))) ∂mu r +
        C * r ^ (-α) * (∫ x, x * exp (-(h * x)) ∂mu r) * ∫ x, (1 - exp (-(h * x))) ∂muinf) :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam, Λ ≤ lam →
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h))) ≤
          ∫ x, (1 - exp (-(h * x))) ∂muinf ∧
        ∫ x, (1 - exp (-(h * x))) ∂muinf ≤
          (∫ x, (1 - exp (-(h * x))) ∂mu (genInv f x₀ (lam / (A₂ * h)))) * (1 - η)⁻¹ := by
  intro η hη hη2
  set T : ℝ := η / (8 * (C * A₁)) with hTdef
  have hT0 : 0 < T := by positivity
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 ((tendsto_integral_exp_neg_mul_abs_atTop hQinf0).eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < T / 2)))
  refine ⟨max Λ₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun lam hlam => ?_⟩
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hlam)
  have hJs0 : ∫ y, exp (-(lam * |y|)) ∂Qinf < T / 2 := hΛ₀ lam (le_trans (le_max_left _ _) hlam)
  have hrfun : Tendsto (fun h : ℝ => genInv f x₀ (lam / (A₂ * h))) (𝓝[>] 0) atTop :=
    (hf.tendsto_genInv_atTop hρ hmeas hbdd).comp (tendsto_level_arg hA₂ hlam0)
  have hrate : Tendsto (fun h : ℝ => h * ((∫ x, x ^ 2 ∂mu (genInv f x₀ (lam / (A₂ * h)))) /
      ∫ x, x ∂mu (genInv f x₀ (lam / (A₂ * h))))) (𝓝[>] 0) (𝓝 lam) :=
    hf.tendsto_level_filled_of_tendsto_div hρ hmeas hx₀ hpos hbdd
      (ψ := fun r => (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r) hA₂ hlam0 hS
  have hX0 : ∀ r, 0 ≤ᵐ[mu r] fun x => x := fun r =>
    ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) (hmu r))
  have hexpbase := tendsto_integral_exp_neg_mul_abs_of_tendsto_rate (hconv.comp hrfun) hrate hlam0
  simp only [Function.comp_apply, Measure.coe_toProbabilityMeasure] at hexpbase
  have hexpconv := hexpbase.eventually (eventually_lt_nhds (by linarith : _ < T))
  have hEbd : ∀ᶠ h : ℝ in 𝓝[>] 0, (∫ x, x ∂mu (genInv f x₀ (lam / (A₂ * h)))) /
      (A₁ * genInv f x₀ (lam / (A₂ * h)) ^ α) ≤ 2 :=
    hrfun.eventually (hE.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)))
  filter_upwards [hrfun.eventually hI35, hEbd, hexpconv, self_mem_nhdsWithin] with
    h hrest hEr hJ hh
  have hh0 : (0 : ℝ) < h := hh
  set r := genInv f x₀ (lam / (A₂ * h))
  set m := ∫ x, x ∂mu r
  set s := (∫ x, x ^ 2 ∂mu r) / ∫ x, x ∂mu r
  set D := ∫ x, (1 - exp (-(h * x))) ∂muinf
  set Dr := ∫ x, (1 - exp (-(h * x))) ∂mu r
  set J := ∫ y, exp (-(h * s * y)) ∂(((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / s)
  have hr : 0 < r := hf.genInv_pos hρ hmeas hx₀ _
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have hm_le : m * r ^ (-α) ≤ 2 * A₁ := by
    rw [div_le_iff₀ (mul_pos hA₁ hrα)] at hEr
    rw [Real.rpow_neg hr.le, ← div_eq_mul_inv, div_le_iff₀ hrα]
    linarith
  have hJT : J ≤ T := by
    refine le_trans (le_of_eq ?_) hJ.le
    refine integral_congr_ae ?_
    filter_upwards [(ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy)
      (map_withDensity_ofReal_div_Iio_zero (mu r) (X := fun x => x) measurable_id (hX0 r) _
        (hSpos r))) : ∀ᵐ y ∂(((mu r).withDensity fun x =>
      ENNReal.ofReal (x / ∫ x, x ∂mu r)).map fun x => x / s), 0 ≤ y)] with y hy
    rw [abs_of_nonneg hy]
  have hJ0 : 0 ≤ J := integral_nonneg fun y => (exp_pos _).le
  have hD0 : 0 ≤ D := integral_one_sub_exp_neg_mul_nonneg hmuinf hh0.le
  have hDr0 : 0 ≤ Dr := integral_one_sub_exp_neg_mul_nonneg (hmu r) hh0.le
  have hstep := (hrest h hh0).2
  rw [integral_mul_exp_neg_eq_mul_integral (mu r) (X := fun x => x) measurable_id (hX0 r)
    (hSpos r).ne' (hEpos r) h] at hstep
  have hcorr : C * r ^ (-α) * (m * J) ≤ η / 4 := by
    have hm0 : 0 ≤ m * r ^ (-α) := (mul_pos (hEpos r) (Real.rpow_pos_of_pos hr _)).le
    calc C * r ^ (-α) * (m * J) = C * (m * r ^ (-α)) * J := by ring
      _ ≤ C * (2 * A₁) * T := by gcongr
      _ = η / 4 := by rw [hTdef]; field_simp; ring
  have hkey : D * (1 - η) ≤ Dr := by
    have h1 : C * r ^ (-α) * (m * J) * D ≤ η / 4 * D := mul_le_mul_of_nonneg_right hcorr hD0
    have h2 : D ≤ Dr + C * r ^ (-α) * (m * J) * D := hstep
    nlinarith
  refine ⟨(hrest h hh0).1, ?_⟩
  have hη1 : 0 < 1 - η := by linarith
  calc D = D * (1 - η) * (1 - η)⁻¹ := by field_simp
    _ ≤ Dr * (1 - η)⁻¹ := mul_le_mul_of_nonneg_right hkey (inv_nonneg.2 hη1.le)

end PercLib.Analysis
