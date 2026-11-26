/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Defs
public import PercLib.Percolation.Bond.Lace.Expansion.Finite
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The infinite signed lace expansion

Absolute summability of all coefficient row masses and a finite continuation
bound justify the infinite convolution. The identity follows by taking limits
in the proved finite expansion; its remainder tends to zero.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem summable_signed_of_ennreal_sum_ne_top {ι : Type*}
    (k : ι → ℕ) (f : ι → ℝ≥0∞) (h : (∑' i, f i) ≠ ⊤) :
    Summable (fun i => (-1 : ℝ) ^ k i * (f i).toReal) := by
  apply (ENNReal.summable_toReal h).of_norm_bounded
  intro i
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, le_refl]

/-- Finite total coefficient mass implies absolute summability of the signed
coefficient series at every endpoint. -/
theorem summable_signed_laceCoefficient (q : Sym2 V → unitInterval) (x y : V)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal) := by
  apply summable_signed_of_ennreal_sum_ne_top id
  exact ne_top_of_le_ne_top hmass (ENNReal.tsum_le_tsum fun _ => ENNReal.le_tsum y)

/-- The signed infinite lace kernel has a summable row whenever the total
nonnegative coefficient row masses are summable. -/
theorem summable_laceSum (q : Sym2 V → unitInterval) (x : V)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    Summable (laceSum q x) := by
  have htotal : (∑' z : ℕ × V, laceCoefficient q z.1 x z.2) ≠ ⊤ := by
    rw [ENNReal.tsum_prod']
    exact hmass
  have hs : Summable (fun z : ℕ × V =>
      (-1 : ℝ) ^ z.1 * (laceCoefficient q z.1 x z.2).toReal) :=
    summable_signed_of_ennreal_sum_ne_top Prod.fst
      (fun z : ℕ × V => laceCoefficient q z.1 x z.2) htotal
  exact hs.prod_symm.prod

/-- The canonical finite alternating kernels converge to the infinite kernel. -/
theorem tendsto_partialLaceSum (q : Sym2 V → unitInterval) (x y : V)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    Tendsto (fun N => partialLaceSum q N x y) atTop (𝓝 (laceSum q x y)) :=
  (summable_signed_laceCoefficient q x y hmass).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

/-- The total nonnegative continuation series is finite under the same
coefficient-mass and continuation assumptions. -/
theorem tsum_laceCoefficient_step_ne_top (q : Sym2 V → unitInterval)
    (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    (∑' n : ℕ, ∑' u, ∑' v, laceCoefficient q n x u *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hmass hCfinite) ?_
  calc
    _ ≤ ∑' n : ℕ, (∑' u, laceCoefficient q n x u) * C :=
      ENNReal.tsum_le_tsum fun n => laceCoefficient_step_le_mass_mul q n x y C hC
    _ = _ := ENNReal.tsum_mul_right

set_option maxHeartbeats 800000 in
/-- Infinite convolution commutes with the absolutely summable signed
coefficient series. -/
theorem laceSum_step_eq_tsum (q : Sym2 V → unitInterval)
    (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    (∑' n : ℕ, (-1 : ℝ) ^ n *
      (∑' u, ∑' v, laceCoefficient q n x u *
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y).toReal) =
      ∑' u, ∑' v, laceSum q x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  let F : ℕ → V × V → ℝ≥0∞ := fun n p =>
    laceCoefficient q n x p.1 * J p.1 p.2 * tau q p.2 y
  have htotal : (∑' z : ℕ × (V × V), F z.1 z.2) ≠ ⊤ := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_prod']
    exact tsum_laceCoefficient_step_ne_top q x y C hCfinite hC hmass
  have hrows : (∑' n : ℕ, ∑' p, F n p) ≠ ⊤ := by
    simpa only [ENNReal.tsum_prod'] using htotal
  have hFn (n : ℕ) : (∑' p, F n p) ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hrows n
  have hs : Summable (fun z : ℕ × (V × V) => (-1 : ℝ) ^ z.1 * (F z.1 z.2).toReal) :=
    summable_signed_of_ennreal_sum_ne_top Prod.fst (fun z => F z.1 z.2) htotal
  have hinner (p : V × V) :
      (∑' n : ℕ, (-1 : ℝ) ^ n * (F n p).toReal) =
        laceSum q x p.1 * (J p.1 p.2).toReal * (tau q p.2 y).toReal := by
    simp only [F, ENNReal.toReal_mul]
    simp_rw [← mul_assoc, tsum_mul_right]
    rfl
  have hsInner : Summable (fun p : V × V =>
      ∑' n : ℕ, (-1 : ℝ) ^ n * (F n p).toReal) := hs.prod_symm.prod
  have hsp : Summable (fun p : V × V =>
      laceSum q x p.1 * (J p.1 p.2).toReal * (tau q p.2 y).toReal) :=
    hsInner.congr hinner
  calc
    _ = ∑' n : ℕ, ∑' p : V × V, (-1 : ℝ) ^ n * (F n p).toReal := by
      apply tsum_congr
      intro n
      change (-1 : ℝ) ^ n * (∑' u, ∑' v, F n (u, v)).toReal = _
      rw [← ENNReal.tsum_prod', ENNReal.tsum_toReal_eq
        (ENNReal.ne_top_of_tsum_ne_top (hFn n)), tsum_mul_left]
    _ = ∑' p : V × V, ∑' n : ℕ, (-1 : ℝ) ^ n * (F n p).toReal := hs.tsum_comm.symm
    _ = ∑' p : V × V, laceSum q x p.1 * (J p.1 p.2).toReal * (tau q p.2 y).toReal :=
      tsum_congr hinner
    _ = _ := hsp.tsum_prod

/-- The convolutions of the finite alternating kernels converge to the
convolution of the infinite signed kernel. -/
theorem tendsto_partialLaceSum_step (q : Sym2 V → unitInterval)
    (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    Tendsto (fun N => ∑' u, ∑' v, partialLaceSum q N x u *
      (offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal)
      atTop (𝓝 (∑' u, ∑' v, laceSum q x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal)) := by
  have hs := summable_signed_of_ennreal_sum_ne_top id
    (fun n => ∑' u, ∑' v, laceCoefficient q n x u *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) (tsum_laceCoefficient_step_ne_top q x y C hCfinite hC hmass)
  have h := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, id_eq] at h
  rw [laceSum_step_eq_tsum q x y C hCfinite hC hmass] at h
  have hfinite (N : ℕ) := partialLaceSum_step_eq_tsum q N x y C hCfinite hC
    (fun n _ => ENNReal.ne_top_of_tsum_ne_top hmass n)
  simpa only [hfinite] using h

/-- Under total coefficient-mass summability the actual signed remainder
vanishes. The continuation bound is uniform in both vertices. -/
theorem tendsto_signedLaceRemainder_zero [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u z, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v z) ≤ C)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    Tendsto (fun N => signedLaceRemainder q N x y) atTop (𝓝 0) := by
  have hpos : (∑' n : ℕ, ∑' u, laceCoefficient q (n + 1) x u) ≠ ⊤ :=
    ne_top_of_le_ne_top hmass
      (ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
        (fun n => ∑' u, laceCoefficient q n x u))
  have hr : Tendsto (fun n => laceRemainder q n x y) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_iSup_laceRemainder_zero q x C hCfinite hC hpos)
      (fun _ => bot_le) (fun n => le_iSup (fun z => laceRemainder q n x z) y)
  have hrreal : Tendsto (fun n => (laceRemainder q n x y).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [signedLaceRemainder, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hrreal

/-- The infinite signed lace expansion with the canonical lace kernel. The
finite-cluster and absolute-summability hypotheses justify every cutting step,
real conversion, convolution interchange, and passage to the limit. -/
theorem infinite_lace_expansion [Countable V]
    (q : Sym2 V → unitInterval) (x y : V)
    (hfin : ∀ a u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u z, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v z) ≤ C)
    (hmass : (∑' n : ℕ, ∑' u, laceCoefficient q n x u) ≠ ⊤) :
    (tau q x y).toReal = (if x = y then 1 else 0) + laceSum q x y +
      (∑' v, (offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
      (∑' u, ∑' v, laceSum q x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal) := by
  have hp := tendsto_partialLaceSum q x y hmass
  have hc := tendsto_partialLaceSum_step q x y C hCfinite (fun u => hC u y) hmass
  have hr := tendsto_signedLaceRemainder_zero q x y C hCfinite hC hmass
  have hlimit : Tendsto (fun N =>
      (if x = y then (1 : ℝ) else 0) + partialLaceSum q N x y +
        (∑' v, (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
        (∑' u, ∑' v, partialLaceSum q N x u *
          (offDiagonal (fun a b : V =>
            (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal) +
        signedLaceRemainder q N x y) atTop
      (𝓝 ((if x = y then (1 : ℝ) else 0) + laceSum q x y +
        (∑' v, (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
        (∑' u, ∑' v, laceSum q x u *
          (offDiagonal (fun a b : V =>
            (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal))) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds.add hp).add tendsto_const_nhds).add hc).add hr
  have hconst := hlimit.congr' (Filter.Eventually.of_forall fun N =>
    (finite_lace_expansion q N x y hfin C hCfinite (fun u => hC u y)
      (fun n _ => ENNReal.ne_top_of_tsum_ne_top hmass n)).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end PercLib.Percolation.Bond.Lace
