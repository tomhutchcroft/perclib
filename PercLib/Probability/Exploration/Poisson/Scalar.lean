/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Poisson/Scalar.lean`; added at source revision
`a1dd3fd7178264bb1dfc2c71abc2cdca25da9d48`, supplied under its Apache-2.0 header. This is a
proof-only module. Its reviewed
interfaces contain all the corresponding definitions. The canonical BFS namespace prefix is
`PercLib.Percolation.Bond.Exploration.BFS`. Forbidden build-option and source task-label commands
were not imported.
-/
module

public import PercLib.Probability.Exploration.Poisson.Defs
public import PercLib.Probability.Exploration.PGF

/-!
# Scalar Bernoulli-Poisson estimates

Arithmetic of the one-coordinate `ℝ≥0∞` Bernoulli PGF factor and the finite-product
Poisson-exponential estimate lives here. The finiteness assumption on `t` governs `toReal`;
truncated subtraction is handled with separate hypotheses, not by replacing infinity by zero.
The product estimate applies to an explicit finite `Finset`, not automatically to an infinite
fresh frontier or cluster.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace PercLib.Probability.ExplorationPoisson

/-! ### The one-coordinate factor `t * p + (1 - p)` -/

/-- **The factor identity.** For `1 ≤ t` finite and `p ≤ 1`, the truncated-subtraction
form `t * p + (1 - p)` coincides with `1 + p * (t - 1)`.

The two truncations are handled separately: `1 - p` is exact because `p ≤ 1`, and
`t - 1` is exact because `1 ≤ t` and `t ≠ ⊤`.  No `ring` is used on a truncated
subtraction. -/
theorem pgfFactor_eq_one_add_tsub (t p : ℝ≥0∞) (hp : p ≤ 1) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) :
    pgfFactor t p = 1 + p * (t - 1) := by
  have hp_top : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have htp_top : t * p ≠ ⊤ := ENNReal.mul_ne_top ht_top hp_top
  have h1p_top : 1 - p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hX_top : t * p + (1 - p) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨htp_top, h1p_top⟩
  have ht1_top : t - 1 ≠ ⊤ := ne_top_of_le_ne_top ht_top tsub_le_self
  have hmul_top : p * (t - 1) ≠ ⊤ := ENNReal.mul_ne_top hp_top ht1_top
  have hY_top : 1 + p * (t - 1) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hmul_top⟩
  have hX : (t * p + (1 - p)).toReal = t.toReal * p.toReal + (1 - p.toReal) := by
    rw [ENNReal.toReal_add htp_top h1p_top, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top, ENNReal.toReal_one]
  have hY : (1 + p * (t - 1)).toReal = 1 + p.toReal * (t.toReal - 1) := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top hmul_top, ENNReal.toReal_one, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le ht ht_top, ENNReal.toReal_one]
  have hkey : t.toReal * p.toReal + (1 - p.toReal) = 1 + p.toReal * (t.toReal - 1) := by ring
  exact (ENNReal.toReal_eq_toReal_iff' hX_top hY_top).mp (by rw [hX, hY]; exact hkey)

/-- **Positivity of the factor.** Under `1 ≤ t` finite and `p ≤ 1` the factor is at least `1`;
in particular it never degenerates to `0`, including at `p = 1` where it equals `t`. -/
theorem one_le_pgfFactor (t p : ℝ≥0∞) (hp : p ≤ 1) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) :
    1 ≤ pgfFactor t p := by
  rw [pgfFactor_eq_one_add_tsub t p hp ht ht_top]
  exact le_add_right le_rfl

/-- The factor is non-zero: the pgf of a Bernoulli coordinate at `t ≥ 1` never vanishes. -/
theorem pgfFactor_ne_zero (t p : ℝ≥0∞) (hp : p ≤ 1) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) :
    pgfFactor t p ≠ 0 :=
  ne_bot_of_le_ne_bot (by simp) (one_le_pgfFactor t p hp ht ht_top)

/-- At `p = 1` the factor is exactly `t`: the non-vacuous case of the identity. -/
theorem pgfFactor_one (t : ℝ≥0∞) : pgfFactor t 1 = t := by
  rw [pgfFactor_def]
  simp


/-- **The factor identity in `ofReal` form**, with the real parameters explicit.
`ofReal τ * ofReal q + (1 - ofReal q) = ofReal (1 + q (τ - 1))` for `0 ≤ q ≤ 1` and `τ ≥ 1`.
The truncated subtraction `1 - ofReal q` is identified with `ofReal (1 - q)` using `q ≤ 1`,
so no `ring` touches a `tsub`. -/
theorem ofReal_pgfFactor (q τ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 1 ≤ τ) :
    ENNReal.ofReal τ * ENNReal.ofReal q + (1 - ENNReal.ofReal q)
      = ENNReal.ofReal (1 + q * (τ - 1)) := by
  have hτ0 : 0 ≤ τ := le_trans zero_le_one hτ
  have hsub1 : (1 : ℝ≥0∞) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
    rw [ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one]
  have h1 : 0 ≤ q * (τ - 1) := mul_nonneg hq0 (by linarith)
  rw [hsub1, ← ENNReal.ofReal_mul hτ0, ← ENNReal.ofReal_add (mul_nonneg hτ0 hq0)
    (by linarith)]
  congr 1
  ring

/-- **The factor identity in `ofReal` form at a `ℝ≥0∞` parameter.** For finite `1 ≤ t` and
`p ≤ 1`, the factor is the `ofReal` of the real Bernoulli pgf at `t.toReal`. -/
theorem pgfFactor_eq_ofReal (t p : ℝ≥0∞) (hp : p ≤ 1) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) :
    pgfFactor t p = ENNReal.ofReal (1 + p.toReal * (t.toReal - 1)) := by
  have hp_top : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hp1 : p.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hp
  have ht1 : 1 ≤ t.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ht_top ht
  conv_lhs =>
    rw [← ENNReal.ofReal_toReal hp_top, ← ENNReal.ofReal_toReal ht_top]
  exact ofReal_pgfFactor p.toReal t.toReal (by positivity) hp1 ht1

/-! ### The finite product bound -/

/-- **Finite-product Poisson bound.** For `0 ≤ q_e ≤ 1`, `τ ≥ 1` and a finite set `S` of
coordinates whose intensities sum to at most `m`, the product of the Bernoulli pgf factors is
at most `ofReal (exp ((τ - 1) m))`.

This is the `ℝ≥0∞` form of `PROOF.md` Lemma 4.3 with the truncated-subtraction factors of
`AdaptedReveal.PGF`, and it is a *finite-set* statement: it says nothing about an infinite
product or an infinite cluster. -/
theorem prod_pgfFactor_le_exp {ι : Type*} (q : ι → ℝ) (hq0 : ∀ e, 0 ≤ q e)
    (hq1 : ∀ e, q e ≤ 1) (τ : ℝ) (hτ : 1 ≤ τ) (S : Finset ι) {m : ℝ}
    (hm : ∑ e ∈ S, q e ≤ m) :
    ∏ e ∈ S, (ENNReal.ofReal τ * ENNReal.ofReal (q e) + (1 - ENNReal.ofReal (q e)))
      ≤ ENNReal.ofReal (Real.exp ((τ - 1) * m)) := by
  classical
  have hfac : ∀ e ∈ S, ENNReal.ofReal τ * ENNReal.ofReal (q e) + (1 - ENNReal.ofReal (q e))
      = ENNReal.ofReal (1 + q e * (τ - 1)) :=
    fun e _ => ofReal_pgfFactor (q e) τ (hq0 e) (hq1 e) hτ
  rw [Finset.prod_congr rfl hfac]
  have hnn : ∀ e ∈ S, (0:ℝ) ≤ 1 + q e * (τ - 1) := by
    intro e _
    have : 0 ≤ q e * (τ - 1) := mul_nonneg (hq0 e) (by linarith)
    linarith
  rw [← ENNReal.ofReal_prod_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real finite-product bound, taken from the committed Poisson lemma
  have hcoe : ∏ e ∈ S, (1 + q e * (τ - 1))
      = ∏ i : ↥S, (1 + q (i : ι) * (τ - 1)) := (Finset.prod_coe_sort S _).symm
  rw [hcoe]
  have hprod := PercLib.Probability.ExplorationEnvelope.sum_tiltedWeight_eq_prod
    (fun i : ↥S => q (i : ι)) τ (Finset.univ : Finset ↥S)
  have hbound := PercLib.Probability.ExplorationEnvelope.sum_tiltedWeight_le_exp
    (fun i : ↥S => q (i : ι)) τ (Finset.univ : Finset ↥S)
    (fun i => hq0 (i : ι)) hτ (m := m) ?_
  · rw [← hprod]
    exact hbound
  · rwa [Finset.sum_coe_sort]

end PercLib.Probability.ExplorationPoisson
