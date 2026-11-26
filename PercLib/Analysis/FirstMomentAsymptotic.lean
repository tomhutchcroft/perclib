/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from contributor yujinhkim, repository `yujinhkim/lrp`, branch `critical-lrp-1`,
commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/VolumeMoments/FirstMoment/Asymptotic.lean`,
`PercLib/CriticalLRP/VolumeMoments/FirstMoment/Bootstrap.lean` and
`PercLib/CriticalLRP/VolumeMoments/FirstMoment/Main.lean`. Licence: Apache-2.0 as declared in
that revision's file headers and `third_party/critical-lrp/NOTICE.md`. Upstream origin:
`yujinhkim/Critical-Long-range-percolation`, revision
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified).
Changes: `LogarithmicallyIntegrable` is the notion of
`PercLib/Analysis/RegularVariation/Defs.lean`; the source's `tendsto_rpow_mul_integral_Ioi` and
`first_moment_asymptotic` are replaced by the existing
`tendsto_rpow_mul_integral_Ioi_mul_rpow_neg` and `isEquivalent_rpow_of_hasDerivWithinAt_riccati`;
the source's `rpow_cube_of_pos` by mathlib's `Real.rpow_mul_natCast`; the source definition
`bootstrapThreshold` is written out in the statement; the lower bound is derived from
`lemma_I_4_5_two_nocont` without the measurability and boundedness hypotheses; the measurability
hypothesis on the relative error in the log-integrability statement is dropped (it follows from
continuity); theorems are renamed after their conclusions; namespace `PercLib.Analysis`; no
disabled linters or `autoImplicit`.

Mathematical reference: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Section I.4.1: Proposition I.4.2 (p. 34), Corollary I.4.8
(p. 36), the proof of Lemma I.4.9 (pp. 37–38) and Lemma I.4.13 (p. 39).
-/
module

public import PercLib.Analysis.HardyMajorant
public import PercLib.Analysis.RiccatiComparison

/-! # The first-moment asymptotic of Proposition I.4.2

This file collects the analytic steps that turn the first-moment ODE (I.4.6),
`f' = A (1 - h) r^{-α-1} f²`, into the mean-field asymptotic `f r ~ (α/A) r^α`.

* The relative error `𝓗_r = (A/α) r^{-α} f r - 1` has the closed form
  `1 + 𝓗_r = (1 - α r^α ∫_r^∞ h s s^{-α-1} ds)⁻¹`, and is logarithmically integrable when the
  error `h` is a logarithmically integrable error function (Lemma I.4.13 applied to (I.4.7)).
* A nonnegative error gives the lower bound `(α/A) r^α ≤ f r` (Corollary I.4.8).
* The bootstrap of Lemma I.4.9 is run with the multiplicative error
  `Ē = 1 - (1 - 𝓔₀)(1 - 𝓔₁)` perturbed additively by `|𝓔₀| ≤ 1/8`, uniformly in
  `β ∈ [β_c/2, β_c)`, and passed to `β ↑ β_c`.
* With `𝓔₀ → 0` and `0 ≤ 𝓔₁ ≤ c r^{3α-d}`, `d > 3α`, the first moment at `β_c` satisfies
  `f r / ((α/β_c) r^α) → 1`.

Nothing probabilistic is asserted. The inputs that the paper obtains from sharpness of the
phase transition (the minimal threshold `r₀ β` and the a-priori bound `F β r ≤ (2α/β) r^α`),
from the tree-graph inequality and Lemma I.4.7 (the error bound) and from monotone convergence
in `β` (the left limit at `β_c`) are explicit hypotheses. Proposition I.4.2 and Corollary I.4.8
of the paper are therefore not proved here for the percolation model.

## Main results

* `abs_one_sub_mul_one_sub_le`, `abs_one_sub_mul_one_sub_le_of_le`: the error `Ē` in terms of
  `𝓔₀, 𝓔₁`;
* `le_mul_rpow_mul_div_pow_three_of_le_div`: the algebra of (I.4.8);
* `bootstrap_perturbed`: the bootstrapping engine of Lemma I.4.9 with the `𝓔₀` perturbation;
* `exists_forall_le_of_bootstrap_perturbed`: the a-priori bound at `β_c`;
* `div_mul_rpow_le_of_riccati_of_nonneg`: the lower bound of Corollary I.4.8;
* `one_add_div_mul_rpow_neg_mul_sub_one_eq_inv`: the closed form of `1 + 𝓗_r`;
* `logarithmicallyIntegrable_div_mul_rpow_neg_mul_sub_one`: `𝓗` is logarithmically integrable;
* `tendsto_div_rpow_of_one_sub_mul_one_sub_error`: the first-moment asymptotic at `β_c`.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### The error `Ē` of (I.4.6) in terms of `𝓔₀` and `𝓔₁` -/

/-- `Ē = 1 - (1 - 𝓔₀)(1 - 𝓔₁) = 𝓔₀ + 𝓔₁ (1 - 𝓔₀)`: if `|𝓔₀| ≤ 1/8` and `0 ≤ 𝓔₁` then
`|Ē| ≤ |𝓔₀| + (9/8) 𝓔₁`. -/
theorem abs_one_sub_mul_one_sub_le {E0 E1 : ℝ} (hE0 : |E0| ≤ 1 / 8) (hE1 : 0 ≤ E1) :
    |1 - (1 - E0) * (1 - E1)| ≤ |E0| + (9 / 8) * E1 := by
  have h1 : |1 - E0| ≤ 9 / 8 := by
    rw [abs_le] at hE0 ⊢
    constructor <;> linarith [hE0.1, hE0.2]
  have h3 : |E1 * (1 - E0)| ≤ (9 / 8) * E1 := by
    rw [abs_mul, abs_of_nonneg hE1, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 hE1
  calc |1 - (1 - E0) * (1 - E1)| = |E0 + E1 * (1 - E0)| := by ring_nf
    _ ≤ |E0| + |E1 * (1 - E0)| := abs_add_le _ _
    _ ≤ |E0| + (9 / 8) * E1 := by linarith [h3]

/-- If `|𝓔₀| ≤ 1/8` and `0 ≤ 𝓔₁ ≤ C r^{3α-d} (A/((α/β) r^α))³`, then
`|Ē| ≤ 1/8 + (9/8) C r^{3α-d} (A/((α/β) r^α))³`. -/
theorem abs_one_sub_mul_one_sub_le_of_le {α β d C E0 E1 A r : ℝ} (hE0 : |E0| ≤ 1 / 8)
    (hE1nn : 0 ≤ E1) (hE1 : E1 ≤ C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3) :
    |1 - (1 - E0) * (1 - E1)|
      ≤ 1 / 8 + (9 / 8) * C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3 := by
  have h := abs_one_sub_mul_one_sub_le hE0 hE1nn
  nlinarith [h, hE0, hE1]

/-- **The algebra of (I.4.8).** If `|B_r| ≥ c r^d` and `𝓔₁ ≤ 3A³/|B_r|`, then
`𝓔₁ ≤ (3/c)(α/β)³ r^{3α-d} (A/((α/β) r^α))³`. -/
theorem le_mul_rpow_mul_div_pow_three_of_le_div {α β d c A b E1 r : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hc : 0 < c) (hr : 0 < r) (hA : 0 < A) (hb : c * r ^ d ≤ b)
    (hE1 : E1 ≤ 3 * A ^ 3 / b) :
    E1 ≤ (3 / c) * (α / β) ^ 3 * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3 := by
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have hcrd : 0 < c * r ^ d := by positivity
  have h1 : 3 * A ^ 3 / b ≤ 3 * A ^ 3 / (c * r ^ d) :=
    div_le_div_of_nonneg_left (by positivity) hcrd hb
  have hcube : (r ^ α) ^ 3 = r ^ (3 * α) := by
    rw [← Real.rpow_mul_natCast hr.le, mul_comm]
    norm_num
  have hsplit : r ^ (3 * α - d) = r ^ (3 * α) * r ^ (-d) := by
    rw [← Real.rpow_add hr]
    ring_nf
  have h2 : (3 / c) * (α / β) ^ 3 * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3
      = 3 * A ^ 3 / (c * r ^ d) := by
    rw [div_pow A, mul_pow (α / β), hcube, hsplit, Real.rpow_neg hr.le]
    have : 0 < r ^ (3 * α) := Real.rpow_pos_of_pos hr _
    have : 0 < r ^ d := Real.rpow_pos_of_pos hr _
    field_simp
  linarith [hE1, h1, le_of_eq h2]

/-! ### Threshold arithmetic for the bootstrap -/

private theorem rpow_div_pow {P r₀ α d : ℝ} (hP : 0 < P) (hr₀ : 0 < r₀) (hd : 0 < d) :
    (P ^ (1 / d) * r₀ ^ (3 * α / d)) ^ d = P * r₀ ^ (3 * α) := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hP.le,
    ← Real.rpow_mul hr₀.le, show (1 / d) * d = 1 by field_simp,
    show (3 * α / d) * d = 3 * α by field_simp, Real.rpow_one]

private theorem one_le_threshold {P r₀ α d : ℝ} (hP : 0 < P) (hα : 0 < α) (hd : 0 < d)
    (hr₀ : P ^ (-(1 / (3 * α))) < r₀) :
    1 ≤ P ^ (1 / d) * r₀ ^ (3 * α / d) := by
  have hstep : P ^ (-(1 / d)) ≤ r₀ ^ (3 * α / d) := by
    have h1 : (P ^ (-(1 / (3 * α)))) ^ (3 * α / d) ≤ r₀ ^ (3 * α / d) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hP.le _) hr₀.le (by positivity)
    have h2 : (P ^ (-(1 / (3 * α)))) ^ (3 * α / d) = P ^ (-(1 / d)) := by
      rw [← Real.rpow_mul hP.le]
      congr 1
      field_simp
    rwa [h2] at h1
  calc (1 : ℝ) = P ^ (1 / d) * P ^ (-(1 / d)) := by
        rw [← Real.rpow_add hP]; norm_num
    _ ≤ P ^ (1 / d) * r₀ ^ (3 * α / d) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_pos_of_pos hP _).le

private theorem le_threshold {P r₀ R₁ α d : ℝ} (hP : 0 < P) (hα : 0 < α) (hd : 0 < d)
    (hR₁ : 0 ≤ R₁) (hr₀ : R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α))) < r₀) :
    R₁ ≤ P ^ (1 / d) * r₀ ^ (3 * α / d) := by
  have hbase : 0 ≤ R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α))) := by positivity
  have h1 : (R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α)))) ^ (3 * α / d)
      ≤ r₀ ^ (3 * α / d) :=
    Real.rpow_le_rpow hbase hr₀.le (by positivity)
  have h2 : (R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α)))) ^ (3 * α / d)
      = R₁ * P ^ (-(1 / d)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hR₁ _) (Real.rpow_nonneg hP.le _),
      ← Real.rpow_mul hR₁, ← Real.rpow_mul hP.le,
      show d / (3 * α) * (3 * α / d) = 1 by field_simp,
      show -(1 / (3 * α)) * (3 * α / d) = -(1 / d) by field_simp, Real.rpow_one]
  rw [h2] at h1
  have key : R₁ * P ^ (-(1 / d)) * P ^ (1 / d) ≤ r₀ ^ (3 * α / d) * P ^ (1 / d) :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hP.le _)
  have hPprod : P ^ (-(1 / d)) * P ^ (1 / d) = 1 := by
    rw [← Real.rpow_add hP]
    norm_num
  calc R₁ = R₁ * (P ^ (-(1 / d)) * P ^ (1 / d)) := by rw [hPprod, mul_one]
    _ = R₁ * P ^ (-(1 / d)) * P ^ (1 / d) := by ring
    _ ≤ r₀ ^ (3 * α / d) * P ^ (1 / d) := key
    _ = P ^ (1 / d) * r₀ ^ (3 * α / d) := by ring

private theorem threshold_lt_self {P r₀ α d : ℝ} (hP : 0 < P) (hr₀ : 0 < r₀)
    (hα : 0 < α) (hg : 0 < d - 3 * α) (hr : P ^ (1 / (d - 3 * α)) < r₀) :
    P ^ (1 / d) * r₀ ^ (3 * α / d) < r₀ := by
  have hd : 0 < d := by linarith
  have h1 : P ^ (1 / d) < r₀ ^ ((d - 3 * α) / d) := by
    have h2 : (P ^ (1 / (d - 3 * α))) ^ ((d - 3 * α) / d) < r₀ ^ ((d - 3 * α) / d) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hP.le _) hr (by positivity)
    have h3 : (P ^ (1 / (d - 3 * α))) ^ ((d - 3 * α) / d) = P ^ (1 / d) := by
      rw [← Real.rpow_mul hP.le]
      congr 1
      field_simp
    rwa [h3] at h2
  have h5 : P ^ (1 / d) * r₀ ^ (3 * α / d) < r₀ ^ ((d - 3 * α) / d) * r₀ ^ (3 * α / d) :=
    mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hr₀ _)
  rwa [← Real.rpow_add hr₀, show (d - 3 * α) / d + 3 * α / d = 1 by field_simp; ring,
    Real.rpow_one] at h5

/-! ### The bootstrapping engine of Lemma I.4.9 with the `𝓔₀` perturbation -/

/-- **The bootstrapping engine of Lemma I.4.9, with the perturbation `1/8` coming from `𝓔₀`.**
Let `d > 3α`, let `F > 0` be monotone with `F' = (1 - e) β r^{-α-1} F²` on `[1, ∞)`, let the
error obey `|e r| ≤ 1/8 + C r^{3α-d} (F r/((α/β) r^α))³` for `r ≥ R₁`, and let `r₀ ≥ 1` be
minimal with `F r ≤ (2α/β) r^α` for `r ≥ r₀`. Then `r₀` is at most
`max 1 (max (R₁^{d/(3α)} P^{-1/(3α)}) (max (P^{1/(d-3α)}) (P^{-1/(3α)})))` with `P = 128 C`.

The paper's display `Ē ≤ C r^{3α-d}(…)³` drops `𝓔₀`; the additive form is the correct one,
which is why the threshold differs from `bootstrap_high_dim`. -/
theorem bootstrap_perturbed
    {α β d C R₁ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hC : 0 < C) (hγ : 0 < d - 3 * α)
    (hR₁ : 0 ≤ R₁)
    {F F' e : ℝ → ℝ}
    (hderiv : ∀ r, 1 ≤ r → HasDerivAt F (F' r) r)
    (hODE : ∀ r, 1 ≤ r → F' r = (1 - e r) * β * r ^ (-α - 1) * (F r) ^ 2)
    (hpos : ∀ r, 1 ≤ r → 0 < F r)
    (hmono : ∀ r s, 1 ≤ r → r ≤ s → F r ≤ F s)
    (herr : ∀ r, R₁ ≤ r → |e r| ≤ 1 / 8 + C * r ^ (3 * α - d) * (F r / (α / β * r ^ α)) ^ 3)
    {r₀ : ℝ} (hr₀ : 1 ≤ r₀) (hbdd : ∀ r, r₀ ≤ r → F r ≤ 2 * α / β * r ^ α)
    (hmin : ∀ b, 1 ≤ b → (∀ r, b ≤ r → F r ≤ 2 * α / β * r ^ α) → r₀ ≤ b) :
    r₀ ≤ max 1 (max (R₁ ^ (d / (3 * α)) * (128 * C) ^ (-(1 / (3 * α))))
      (max ((128 * C) ^ (1 / (d - 3 * α))) ((128 * C) ^ (-(1 / (3 * α)))))) := by
  set P : ℝ := 128 * C with hPdef
  have hdpos : 0 < d := by linarith
  have hPpos : 0 < P := by positivity
  by_contra hcon
  rw [not_le, max_lt_iff, max_lt_iff, max_lt_iff] at hcon
  obtain ⟨-, hR3, hR4, hR1⟩ := hcon
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  set r : ℝ := P ^ (1 / d) * r₀ ^ (3 * α / d) with hrdef
  have hr1 : 1 ≤ r := one_le_threshold hPpos hα hdpos hR1
  have hrR₁ : R₁ ≤ r := le_threshold hPpos hα hdpos hR₁ hR3
  have hrlt : r < r₀ := threshold_lt_self hPpos hr₀pos hα hγ hR4
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrd : r ^ d = P * r₀ ^ (3 * α) := rpow_div_pow hPpos hr₀pos hdpos
  -- the a priori bound with `max s r₀`
  have hFa : ∀ s, 1 ≤ s → F s ≤ (2 * α / β) * (max s r₀) ^ α := by
    intro s hs
    rcases le_total r₀ s with h | h
    · rw [max_eq_left h]; exact hbdd s h
    · rw [max_eq_right h]
      exact (hmono s r₀ hs h).trans (hbdd r₀ le_rfl)
  -- the smallness of the error on `[r, ∞)`
  have herr14 : ∀ s, r ≤ s → |e s| ≤ 1 / 4 := by
    intro s hrs
    have hs1 : 1 ≤ s := le_trans hr1 hrs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hmaxpos : 0 < max s r₀ := lt_of_lt_of_le hs0 (le_max_left _ _)
    have hcube : (F s / (α / β * s ^ α)) ^ 3 ≤ 8 * (((max s r₀) / s) ^ (3 * α)) := by
      have hspos : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
      have hratio : F s / (α / β * s ^ α) ≤ 2 * (((max s r₀) / s) ^ α) := by
        rw [div_le_iff₀ (by positivity)]
        calc F s ≤ (2 * α / β) * ((max s r₀) ^ α) := hFa s hs1
          _ = 2 * (((max s r₀) / s) ^ α) * (α / β * s ^ α) := by
              rw [Real.div_rpow hmaxpos.le hs0.le]
              field_simp
      have hnonneg : 0 ≤ F s / (α / β * s ^ α) :=
        le_of_lt (div_pos (hpos s hs1) (by positivity))
      calc (F s / (α / β * s ^ α)) ^ 3 ≤ (2 * (((max s r₀) / s) ^ α)) ^ 3 :=
            pow_le_pow_left₀ hnonneg hratio 3
        _ = 8 * (((max s r₀) / s) ^ (3 * α)) := by
            rw [mul_pow, ← Real.rpow_mul_natCast (div_pos hmaxpos hs0).le, mul_comm α]
            norm_num
    have hstep : C * s ^ (3 * α - d) * (F s / (α / β * s ^ α)) ^ 3
        ≤ 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by
      have h1 : C * s ^ (3 * α - d) * (F s / (α / β * s ^ α)) ^ 3
          ≤ C * s ^ (3 * α - d) * (8 * (((max s r₀) / s) ^ (3 * α))) :=
        mul_le_mul_of_nonneg_left hcube (mul_nonneg hC.le (Real.rpow_nonneg hs0.le _))
      have h2 : C * s ^ (3 * α - d) * (8 * (((max s r₀) / s) ^ (3 * α)))
          = 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by
        have h3 : s ^ (3 * α - d) = s ^ (3 * α) * s ^ (-d) := by
          rw [← Real.rpow_add hs0]; ring_nf
        have h4 : 0 < s ^ (3 * α) := Real.rpow_pos_of_pos hs0 _
        rw [Real.div_rpow hmaxpos.le hs0.le, h3]
        field_simp
      linarith [h1, le_of_eq h2]
    have hmax : ((max s r₀) ^ (3 * α)) * s ^ (-d) ≤ (r₀ ^ (3 * α)) * r ^ (-d) := by
      rcases le_total r₀ s with h | h
      · rw [max_eq_left h]
        have h1 : s ^ (3 * α - d) ≤ r₀ ^ (3 * α - d) :=
          Real.rpow_le_rpow_of_nonpos hr₀pos h (by linarith)
        have h2 : s ^ (3 * α - d) = s ^ (3 * α) * s ^ (-d) := by
          rw [← Real.rpow_add hs0]; ring_nf
        have hratio : 1 ≤ r₀ ^ d * r ^ (-d) := by
          rw [Real.rpow_neg hrpos.le, ← div_eq_mul_inv, ← Real.div_rpow hr₀pos.le hrpos.le,
            ← Real.one_rpow d]
          exact Real.rpow_le_rpow zero_le_one (le_of_lt ((one_lt_div hrpos).2 hrlt)) hdpos.le
        have h3 : r₀ ^ (3 * α - d) ≤ r₀ ^ (3 * α) * r ^ (-d) := by
          calc r₀ ^ (3 * α - d) = r₀ ^ (3 * α - d) * 1 := by ring
            _ ≤ r₀ ^ (3 * α - d) * (r₀ ^ d * r ^ (-d)) :=
                mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hr₀pos.le _)
            _ = r₀ ^ (3 * α) * r ^ (-d) := by
                rw [← mul_assoc, ← Real.rpow_add hr₀pos, show 3 * α - d + d = 3 * α by ring]
        linarith [h1, h2, h3]
      · rw [max_eq_right h]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hrpos hrs (by linarith)) (Real.rpow_nonneg hr₀pos.le _)
    have hfinal : 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d)
        ≤ 8 * C * (r₀ ^ (3 * α)) * r ^ (-d) := by
      have h8 : 0 ≤ 8 * C := by positivity
      nlinarith [hmax, h8]
    have hrpow2 : 8 * C * (r₀ ^ (3 * α)) * r ^ (-d) = 1 / 16 := by
      rw [Real.rpow_neg hrpos.le, hrd, hPdef]
      have : 0 < r₀ ^ (3 * α) := Real.rpow_pos_of_pos hr₀pos _
      field_simp
      ring
    linarith [herr s (le_trans hrR₁ hrs), hstep, hfinal, hrpow2]
  have hadm : ∀ s, r ≤ s → F s ≤ (2 * α / β) * s ^ α := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hrpos hs
    have hineq : ∀ x, r ≤ x → (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2 ≤ F' x := by
      intro x hx
      have hx1 : 1 ≤ x := le_trans hr1 hx
      rw [hODE x hx1]
      have hge : (3 / 4 : ℝ) ≤ 1 - e x := by
        linarith [(abs_le.1 (herr14 x hx)).2]
      have hnn : 0 ≤ β * x ^ (-α - 1) * (F x) ^ 2 := by
        have := hpos x hx1
        have : 0 < x := lt_of_lt_of_le zero_lt_one hx1
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hge hnn]
    have hfin := lemma_I_4_5_one_nocont (f := F) (f' := F') (A := 3 / 4 * β) (r₀ := r)
      (by positivity) hα hrpos (fun x hx => hderiv x (le_trans hr1 hx))
      (fun x hx => hpos x (le_trans hr1 hx)) hineq s hs
    have hle2 : α / (3 / 4 * β) ≤ 2 * α / β := by
      rw [div_le_div_iff₀ (by positivity) hβ]
      nlinarith
    have hspos : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
    nlinarith [hfin, hle2, hspos]
  linarith [hmin r hr1 hadm]

/-- **The a-priori bound of Lemma I.4.9 at `β_c`.** Suppose that for every
`β ∈ [β_c/2, β_c)` the hypotheses of `bootstrap_perturbed` hold for `F β`, with a constant `C`
and a threshold `R₁` independent of `β` (the error bound is required for
`β ∈ [β_c/2, β_c]`), where `r₀ β` is the minimal threshold given by sharpness of the phase
transition, and that `F β r → F β_c r` as `β ↑ β_c` for every `r`. Then
`F β_c r ≤ (2α/β_c) r^α` for all `r ≥ R`, for some `R ≥ 1` depending only on `α, d, C, R₁`. -/
theorem exists_forall_le_of_bootstrap_perturbed
    {α d C βc R₁ : ℝ} (hα : 0 < α) (hβc : 0 < βc) (hC : 0 < C) (hγ : 0 < d - 3 * α)
    (hR₁ : 0 ≤ R₁)
    {F F' e : ℝ → ℝ → ℝ} {r₀ : ℝ → ℝ}
    (hderiv : ∀ β r, 1 ≤ r → HasDerivAt (F β) (F' β r) r)
    (hODE : ∀ β r, 1 ≤ r → F' β r = (1 - e β r) * β * r ^ (-α - 1) * (F β r) ^ 2)
    (hpos : ∀ β r, 1 ≤ r → 0 < F β r)
    (hmono : ∀ β r s, 1 ≤ r → r ≤ s → F β r ≤ F β s)
    (herr : ∀ β r, βc / 2 ≤ β → β ≤ βc → R₁ ≤ r →
      |e β r| ≤ 1 / 8 + C * r ^ (3 * α - d) * (F β r / (α / β * r ^ α)) ^ 3)
    (hr₀1 : ∀ β, βc / 2 ≤ β → β < βc → 1 ≤ r₀ β)
    (hbdd : ∀ β r, βc / 2 ≤ β → β < βc → r₀ β ≤ r → F β r ≤ 2 * α / β * r ^ α)
    (hmin : ∀ β b, βc / 2 ≤ β → β < βc → 1 ≤ b →
      (∀ r, b ≤ r → F β r ≤ 2 * α / β * r ^ α) → r₀ β ≤ b)
    (hmeet : ∀ r, Tendsto (fun β => F β r) (𝓝[<] βc) (𝓝 (F βc r))) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r, R ≤ r → F βc r ≤ 2 * α / βc * r ^ α := by
  set T : ℝ := max 1 (max (R₁ ^ (d / (3 * α)) * (128 * C) ^ (-(1 / (3 * α))))
    (max ((128 * C) ^ (1 / (d - 3 * α))) ((128 * C) ^ (-(1 / (3 * α)))))) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  refine ⟨T, hT1, fun r hr => ?_⟩
  have hstep : ∀ β, βc / 2 ≤ β → β < βc → F β r ≤ 2 * α / β * r ^ α := by
    intro β h1β h2β
    have hβpos : 0 < β := lt_of_lt_of_le (by linarith) h1β
    have hτ := bootstrap_perturbed (F := F β) (F' := F' β) (e := e β) (R₁ := R₁)
      hα hβpos hC hγ hR₁ (hderiv β) (hODE β) (hpos β) (hmono β)
      (fun s hs => herr β s h1β h2β.le hs) (hr₀1 β h1β h2β)
      (fun s hs => hbdd β s h1β h2β hs)
      (fun b hb1 hb2 => hmin β b h1β h2β hb1 hb2)
    exact hbdd β r h1β h2β (le_trans hτ hr)
  have hlimR : Tendsto (fun β : ℝ => 2 * α / β * r ^ α) (𝓝[<] βc)
      (𝓝 (2 * α / βc * r ^ α)) :=
    (((tendsto_const_nhds (x := 2 * α)).div tendsto_id hβc.ne').mul_const _).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto (hmeet r) hlimR ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds (show βc / 2 < βc by linarith))] with β hβlt hβgt
  exact hstep β hβgt.le hβlt

/-! ### The relative error of the first moment -/

section RelativeError

variable {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}

/-- **Corollary I.4.8, analytic form.** If the error `h` of the first-moment ODE
`f' = A (1 - h) r^{-α-1} f²` is nonnegative and `f → ∞`, then `(α/A) r^α ≤ f r`. No
dimensional hypothesis is needed. -/
theorem div_mul_rpow_le_of_riccati_of_nonneg (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hnn : ∀ t, r₀ ≤ t → 0 ≤ h t) :
    ∀ r, r₀ ≤ r → α / A * r ^ α ≤ f r := by
  refine lemma_I_4_5_two_nocont hA hα hr₀ hderiv hpos hinf fun t ht => ?_
  have ht0 : 0 < t := hr₀.trans_le ht
  have : 0 ≤ A * t ^ (-α - 1) * (f t) ^ 2 := by positivity
  rw [hode t ht]
  nlinarith [hnn t ht]

/-- **The closed form of the relative error.** On `[r₀, ∞)`, the relative error
`𝓗_r = (A/α) r^{-α} f r - 1` satisfies `1 + 𝓗_r = (1 - α r^α ∫_r^∞ h s s^{-α-1} ds)⁻¹`
(formula (I.4.7)). -/
theorem one_add_div_mul_rpow_neg_mul_sub_one_eq_inv (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivWithinAt f (f' t) (Ici r₀) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r →
      1 + (A / α * r ^ (-α) * f r - 1)
        = (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))⁻¹ := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  obtain ⟨hden, hform⟩ := one_sub_mul_integral_Ioi_pos_and_eq_div_of_hasDerivWithinAt hA hα hr₀
    hderiv hpos hinf hode hmeas hC r hr
  have hrr : r ^ (-α) * r ^ α = 1 := by
    rw [← Real.rpow_add hr0]
    norm_num
  rw [hform, add_sub_cancel]
  have : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  field_simp
  linear_combination hrr

/-- **Lemma I.4.13 (first clause) for the relative error of the first moment.** If the error
`h` of the first-moment ODE is measurable, bounded on `[r₀, ∞)`, tends to `0` and is
logarithmically integrable, then so is the relative error `𝓗_r = (A/α) r^{-α} f r - 1`. -/
theorem logarithmicallyIntegrable_div_mul_rpow_neg_mul_sub_one (hA : 0 < A) (hα : 0 < α)
    (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) (hlint : LogarithmicallyIntegrable h) :
    LogarithmicallyIntegrable (fun r => A / α * r ^ (-α) * f r - 1) := by
  obtain ⟨-, r₁, hr₁, hint⟩ := hlint
  have hmaj := integrableOn_rpow_mul_integral_Ioi_rpow_mul_abs hα hr₁ hmeas hint
  have hsmall : ∀ᶠ r : ℝ in atTop,
      |α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)| ≤ 1 / 2 :=
    (tendsto_rpow_mul_integral_Ioi_mul_rpow_neg hα h0).abs.eventually
      (eventually_le_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
  obtain ⟨r₂, hr₂⟩ := eventually_atTop.1 hsmall
  set R : ℝ := max r₀ (max r₁ (max r₂ 1)) with hRdef
  have hr₀R : r₀ ≤ R := le_max_left _ _
  have hr₁R : r₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hr₂R : r₂ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hRpos : 0 < R := lt_of_lt_of_le hr₀ hr₀R
  -- continuity of the relative error on `[r₀, ∞)`
  have hcont : ContinuousOn (fun r => A / α * r ^ (-α) * f r - 1) (Ici r₀) := by
    intro t ht
    have ht0 : 0 < t := hr₀.trans_le ht
    exact ((((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).const_mul _).mul
      (hderiv t ht).continuousAt).sub continuousAt_const).continuousWithinAt
  refine ⟨⟨r₀, (continuousOn_iff_continuous_domRestrict.1 hcont).measurable⟩, R, hRpos, ?_⟩
  have hmaj2 : IntegrableOn
      (fun r => 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)) (Ioi R) :=
    (hmaj.mono_set (Ioi_subset_Ioi hr₁R)).const_mul (2 * α)
  have hcontR : ContinuousOn (fun r => |A / α * r ^ (-α) * f r - 1| / r) (Ioi R) := by
    refine ((hcont.mono fun t ht => mem_Ici.2 (hr₀R.trans (le_of_lt ht))).abs.div
      continuousOn_id fun t ht => ?_)
    exact (hRpos.trans ht).ne'
  refine Integrable.mono hmaj2 (hcontR.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hrR : R ≤ r := le_of_lt hr
  have hr0 : r₀ ≤ r := hr₀R.trans hrR
  have hrpos : 0 < r := hRpos.trans_le hrR
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hI
  set M : ℝ := ∫ s in Ioi r, s ^ (-α - 1) * |h s| with hM
  have hy : A / α * r ^ (-α) * f r - 1 = (1 - α * r ^ α * I)⁻¹ - 1 := by
    have := one_add_div_mul_rpow_neg_mul_sub_one_eq_inv hA hα hr₀
      (fun t ht => (hderiv t ht).hasDerivWithinAt) hpos hinf hode
      (hmeas.comp measurable_subtype_coe) hC r hr0
    linarith
  have hsmallJ : |α * r ^ α * I| ≤ 1 / 2 := hr₂ r (hr₂R.trans hrR)
  have hden_lb : 1 / 2 ≤ |1 - α * r ^ α * I| := by
    have h3 := abs_sub_abs_le_abs_sub (1 : ℝ) (α * r ^ α * I)
    rw [abs_one] at h3
    linarith
  have hdenpos : 0 < |1 - α * r ^ α * I| := by linarith
  have hHs : A / α * r ^ (-α) * f r - 1 = α * r ^ α * I / (1 - α * r ^ α * I) := by
    rw [hy]
    have hne : 1 - α * r ^ α * I ≠ 0 := abs_pos.1 hdenpos
    field_simp
    ring
  have hIbound : |I| ≤ M := by
    refine (abs_integral_le_integral_abs).trans_eq (integral_congr_ae ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hrpos.trans hs).le _), mul_comm]
  have hMnn : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (Real.rpow_nonneg (hrpos.trans hs).le _) (abs_nonneg _)
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hrpos α
  have hnum : |α * r ^ α * I / (1 - α * r ^ α * I)| ≤ 2 * α * (r ^ α * M) := by
    rw [abs_div, div_le_iff₀ hdenpos, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hrα]
    have : α * r ^ α * |I| ≤ α * r ^ α * M := mul_le_mul_of_nonneg_left hIbound (by positivity)
    have h2 : 0 ≤ 2 * α * (r ^ α * M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hden_lb h2]
  have hrr : r ^ α / r = r ^ (α - 1) := (Real.rpow_sub_one hrpos.ne' α).symm
  have hrhs_nn : 0 ≤ 2 * α * (r ^ (α - 1) * M) := by
    have : 0 ≤ r ^ (α - 1) := Real.rpow_nonneg hrpos.le _
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrhs_nn, abs_div, abs_abs,
    abs_of_pos hrpos, hHs, div_le_iff₀ hrpos]
  calc |α * r ^ α * I / (1 - α * r ^ α * I)| ≤ 2 * α * (r ^ α * M) := hnum
    _ = 2 * α * (r ^ α / r * M) * r := by field_simp
    _ = 2 * α * (r ^ (α - 1) * M) * r := by rw [hrr]

end RelativeError

/-! ### The first-moment asymptotic at `β_c` -/

/-- **The first-moment asymptotic of Proposition I.4.2, Case 1, from the error bounds.** Let
`d > 3α` and let `F > 0`, `F → ∞`, satisfy the first-moment ODE (I.4.6) at `β_c`,
`F' = (1 - Ē) β_c r^{-α-1} F²` with `Ē = 1 - (1 - 𝓔₀)(1 - 𝓔₁)` measurable, where
`|𝓔₀| ≤ 1/8`, `𝓔₀ → 0` and `0 ≤ 𝓔₁ r ≤ c r^{3α-d}` on `[r₀, ∞)`. Then
`F r / ((α/β_c) r^α) → 1`.

In the paper the bound on `𝓔₁` comes from Lemma I.4.7, the tree-graph inequality and the
a-priori estimate of Lemma I.4.9; here it is a hypothesis. -/
theorem tendsto_div_rpow_of_one_sub_mul_one_sub_error
    {F F' E0 E1 : ℝ → ℝ} {α βc d c r₀ : ℝ}
    (hα : 0 < α) (hβc : 0 < βc) (hγ : 0 < d - 3 * α) (hc : 0 ≤ c)
    (hr₀pos : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hODE : ∀ t, r₀ ≤ t →
      F' t = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * βc * t ^ (-α - 1) * (F t) ^ 2)
    (hE0 : Tendsto E0 atTop (𝓝 0)) (hE0b : ∀ t, r₀ ≤ t → |E0 t| ≤ 1 / 8)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t ∧ E1 t ≤ c * t ^ (3 * α - d))
    (hmeas : Measurable (fun t => 1 - (1 - E0 t) * (1 - E1 t))) :
    Tendsto (fun r => F r / (α / βc * r ^ α)) atTop (𝓝 1) := by
  have hE1tend : Tendsto E1 atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => c * t ^ (3 * α - d)) atTop (𝓝 0) := by
      simpa [neg_sub] using (tendsto_rpow_neg_atTop hγ).const_mul c
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_ge_atTop r₀] with t ht using (hE1 t ht).1
    · filter_upwards [eventually_ge_atTop r₀] with t ht using (hE1 t ht).2
  have he0 : Tendsto (fun t => 1 - (1 - E0 t) * (1 - E1 t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => (1 - E0 t) * (1 - E1 t)) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hE0).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hE1tend)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  have hbnd : ∀ t, r₀ ≤ t →
      |1 - (1 - E0 t) * (1 - E1 t)| ≤ 1 / 8 + (9 / 8) * (c * r₀ ^ (3 * α - d)) := by
    intro t ht
    have h1 := abs_one_sub_mul_one_sub_le (hE0b t ht) (hE1 t ht).1
    have h3 : t ^ (3 * α - d) ≤ r₀ ^ (3 * α - d) :=
      Real.rpow_le_rpow_of_nonpos hr₀pos ht (by linarith)
    have h2 : E1 t ≤ c * r₀ ^ (3 * α - d) :=
      (hE1 t ht).2.trans (mul_le_mul_of_nonneg_left h3 hc)
    linarith [hE0b t ht]
  have hequiv := isEquivalent_rpow_of_hasDerivWithinAt_riccati
    (h := fun t => 1 - (1 - E0 t) * (1 - E1 t)) hβc hα hr₀pos
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hpos hinf
    (fun t ht => by rw [hODE t ht]; ring) (hmeas.comp measurable_subtype_coe) hbnd he0
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).1 hequiv
  filter_upwards [eventually_gt_atTop 0] with r hr
  have : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  positivity

end PercLib.Analysis
