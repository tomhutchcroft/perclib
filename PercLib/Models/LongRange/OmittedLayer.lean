/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Discharge of the premise `hD` that the formalisation of contributor yujinhkim cited below adds to
Propositions I.3.1 and I.3.2 of T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1. The premise is read from the repository `yujinhkim/lrp`, branch
`critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/VolumeTailAllN.lean`,
`PercLib/CriticalLRP/Analysis/VolumeTailUpper.lean` (hypothesis `hD`) and
`PercLib/CriticalLRP/CountableProduct/GhostCoupling.lean` (`shiftProb`, written out here); licence
Apache-2.0 as declared in those file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not
independently verified). Contributor: yujinhkim. No code is copied: the proofs are new, from the
ball counts and power-law tail bounds of `PowerLaw.lean`.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Models.LongRange.SoftCutoff
public import PercLib.Percolation.Bond.IntensityMonotone

/-! # The omitted layer of the cut-off family

For a norm `N` on `ℝ^d` (evaluated on `ℤ^d`), a profile `K` and a scale `r`, the full kernel is
`J = radialKernel N K` and the cut-off kernel `J_r = cutoffKernel N K r`. The omitted kernel
is `J - J_r` (pointwise truncated subtraction in `ℝ≥0`, which is exact since `J_r ≤ J`).

* `law_intensityProfile_eq_map_union_omitted` (item 1): the full law is the
  law of `ω ∪ ξ` for independent `ω ~ law (intensityProfile J_r β)` and
  `ξ ~ law (intensityProfile (J - J_r) β)`;
* `coe_omittedKernel_of_ne` (item 2): `(J - J_r)(x,y) = K r` if `N(x-y) ≤ r` and
  `K (N(x-y))` otherwise;
* `tsum_omittedKernel_le` and `tsum_omittedLayer_le` (item 3): for the power law
  `K = powerLawProfile c (d + α)` and any norm with `κ ‖z‖ ≤ N (Int.cast ∘ z)`, the omitted rows are
  at most `C r^{-α}` and the omitted-layer probability rows at most `β C r^{-α}` for `r ≥ 1`,
  with `C = c ((1 + 2/κ)^d + κ^{-d} · 2d 3^{d-1} (1 + 1/α))`;
* `tsum_shiftProb_le` (item 4): the same row bound in the fork's spelling of `hD`, with
  `shiftProb(q_∞, q_r) = min 1 (max 0 ((q_∞ - q_r)/(1 - q_r)))` written out and shown
  equal to `1 - e^{-β (J - J_r)}`.

The premise `hD` therefore holds for the power-law cut-off family under the paper's
hypotheses, with no extra assumption on the norm beyond its comparability with the sup
norm (true of every norm coming from a norm on `ℝ^d`).
-/

@[expose] public section
noncomputable section

open Set
open scoped ENNReal NNReal unitInterval
open PercLib.Percolation.Bond PercLib.Probability

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K : ℝ → ℝ} {r : ℝ}

/-! ### Kernel additivity of the intensity profile -/

section Additivity

variable {V : Type*}

/-- The intensity profile of a sum of kernels is the superposition of the two profiles. -/
theorem intensityProfile_add_kernel (J₁ J₂ : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V) :
    intensityProfile (J₁ + J₂) β e =
      σ (σ (intensityProfile J₁ β e) * σ (intensityProfile J₂ β e)) := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, Set.Icc.coe_mul, unitInterval.coe_symm_eq,
    unitInterval.coe_symm_eq]
  simp only [intensityProfile, Pi.add_apply, NNReal.coe_add, sub_sub_cancel, ← Real.exp_add]
  congr 2
  ring

/-- The law of a sum of kernels is the law of the union of independent configurations. -/
theorem law_intensityProfile_add_kernel (J₁ J₂ : Sym2 V → ℝ≥0) (β : ℝ≥0) :
    law (intensityProfile (J₁ + J₂) β) =
      ((law (intensityProfile J₁ β)).prod (law (intensityProfile J₂ β))).map
        (fun ω => ω.1 ∪ ω.2) := by
  simp only [law]
  rw [prodBernoulli_prod_map_union]
  congr 1
  funext e
  exact intensityProfile_add_kernel J₁ J₂ β e

end Additivity

/-! ### The omitted kernel -/

/-- The omitted kernel vanishes on the diagonal. -/
@[simp] theorem omittedKernel_diag (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (r : ℝ)
    (x : Fin d → ℤ) : (radialKernel N K - cutoffKernel N K r) s(x, x) = 0 := by
  simp [cutoffKernel_def]

/-- **Item 1.** For a profile nonnegative on `(0, ∞)` and `r > 0`, the full law
is the law of the union of the cut-off configuration and an independent omitted layer. -/
theorem law_intensityProfile_eq_map_union_omitted {N : ModelNorm (Fin d → ℝ)}
    (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r) (β : ℝ≥0) :
    law (intensityProfile (radialKernel N K) β) =
      ((law (intensityProfile (cutoffKernel N K r) β)).prod
        (law (intensityProfile
          (radialKernel N.toSeminorm K - cutoffKernel N.toSeminorm K r) β))).map
        (fun ω => ω.1 ∪ ω.2) := by
  rw [← law_intensityProfile_add_kernel]
  congr 2
  funext e
  exact (add_tsub_cancel_of_le (cutoffKernel_le_radialKernel hK hr e)).symm

/-- **Item 2.** For a profile nonnegative and decreasing on `(0, ∞)` and
`r > 0`, off the diagonal the omitted kernel is `K r` inside the cut-off and the full kernel
outside it. -/
theorem coe_omittedKernel_of_ne {N : ModelNorm (Fin d → ℝ)} (hK : ∀ t, 0 < t → 0 ≤ K t)
    (hKa : AntitoneOn K (Ioi 0)) (hr : 0 < r) {x y : Fin d → ℤ} (hxy : x ≠ y) :
    ((radialKernel N.toSeminorm K - cutoffKernel N.toSeminorm K r) s(x, y) : ℝ) =
      if N (Int.cast ∘ (x - y)) ≤ r then K r else K (N (Int.cast ∘ (x - y))) := by
  have hs := N.intCast_comp_sub_pos hxy
  rw [Pi.sub_apply, NNReal.coe_sub (cutoffKernel_le_radialKernel hK hr _),
    coe_radialKernel_of_ne hxy (hK _ hs), cutoffKernel_def, radialKernel_of_ne hxy,
    ModelNorm.coe_toSeminorm]
  split_ifs with h
  · rw [cutoffProfile_of_le h, Real.coe_toNNReal _ (sub_nonneg.2 (hKa hs hr h))]
    ring
  · rw [cutoffProfile_of_lt (not_le.1 h)]
    simp

/-! ### Counting lattice points in a norm ball -/

/-- If `κ ‖z‖ ≤ N (Int.cast ∘ z)`, a ball of radius `r ≥ 1` has at most `(1 + 2/κ)^d r^d` points of
the sup-norm ball `κ ‖z‖ ≤ r`. -/
theorem encard_mul_norm_le {κ : ℝ} (hκ : 0 < κ) (hr : 1 ≤ r) :
    (({z : Fin d → ℤ | κ * ‖z‖ ≤ r}.encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((1 + 2 / κ) ^ d * r ^ d) := by
  set n := ⌊r / κ⌋₊
  have hsub : {z : Fin d → ℤ | κ * ‖z‖ ≤ r} ⊆ {z | ‖z‖ ≤ n} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [← natCast_floor_norm]
    exact_mod_cast Nat.floor_mono (le_div_iff₀' hκ |>.2 hz)
  have hcard : ({z : Fin d → ℤ | ‖z‖ ≤ n}.encard : ℝ≥0∞) = ((2 * n + 1) ^ d : ℕ) := by
    rw [← (finite_norm_le n).cast_ncard_eq, ← Nat.card_coe_set_eq]
    erw [card_norm_le]
    simp
  calc (({z : Fin d → ℤ | κ * ‖z‖ ≤ r}.encard : ℕ∞) : ℝ≥0∞)
      ≤ ({z : Fin d → ℤ | ‖z‖ ≤ n}.encard : ℝ≥0∞) := by
        exact_mod_cast Set.encard_le_encard hsub
    _ = ENNReal.ofReal ((2 * n + 1 : ℝ) ^ d) := by
        rw [hcard, ← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_pow]
        have hn : (n : ℝ) ≤ r / κ := Nat.floor_le (by positivity)
        refine pow_le_pow_left₀ (by positivity) ?_ d
        have : 2 * (r / κ) = 2 / κ * r := by ring
        nlinarith

/-! ### The row bound for the power law -/

/-- The constant of the row bound: `c ((1 + 2/κ)^d + κ^{-d} · 2d 3^{d-1} (1 + 1/α))`. -/
theorem omitted_const_nonneg {c κ α : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) (hα : 0 < α) :
    0 ≤ c * ((1 + 2 / κ) ^ d +
      κ ^ (-(d : ℝ)) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) := by
  positivity

/-- **Item 3, the omitted kernel.** For the power law `c s^{-(d+α)}` with
`c ≥ 0`, `α > 0`, `d ≥ 1`, and a norm with `κ ‖z‖ ≤ N (Int.cast ∘ z)`, every off-diagonal row of
`J - J_r` is at most `C r^{-α}` for `r ≥ 1`, with
`C = c ((1 + 2/κ)^d + κ^{-d} · 2d 3^{d-1} (1 + 1/α))`. -/
theorem tsum_omittedKernel_le (hd : 1 ≤ d) {α c κ : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    {N : ModelNorm (Fin d → ℝ)} (hκ : 0 < κ) (hN : ∀ z, κ * ‖z‖ ≤ N (Int.cast ∘ z))
    (hr : 1 ≤ r) (x : Fin d → ℤ) :
    rowSum (fun e => (((radialKernel N.toSeminorm (powerLawProfile c (d + α)) -
      cutoffKernel N.toSeminorm (powerLawProfile c (d + α)) r) e : ℝ≥0) : ℝ≥0∞)) x ≤
      ENNReal.ofReal (c * ((1 + 2 / κ) ^ d +
        κ ^ (-(d : ℝ)) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) * r ^ (-α)) := by
  have hr0 : 0 < r := one_pos.trans_le hr
  set a : ℝ := d + α with ha_def
  have ha : 0 ≤ a := by positivity
  set K := powerLawProfile c a
  have hK : ∀ t, 0 < t → 0 ≤ K t := fun t ht => mul_nonneg hc (Real.rpow_nonneg ht.le _)
  have hKa : AntitoneOn K (Ioi 0) := antitoneOn_powerLawProfile hc ha
  set C0 : ℝ := ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) with hC0
  have hC0n : 0 ≤ C0 := by positivity
  set t : ℝ := max (r / κ) 1
  have ht1 : 1 ≤ t := le_max_right _ _
  -- shift to the origin: `y = z + x`
  simp only [rowSum_def]
  rw [← (Equiv.addRight x).tsum_eq]
  simp only [Equiv.coe_addRight, add_eq_right]
  -- pointwise domination
  let A : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
    if κ * ‖z‖ ≤ r then ENNReal.ofReal (c * r ^ (-a)) else 0
  let B : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (c * κ ^ (-a)) * ENNReal.ofReal (if t ≤ ‖z‖ then ‖z‖ ^ (-a) else 0)
  have hpt : ∀ z : Fin d → ℤ, (if z = 0 then 0 else
      (((radialKernel N.toSeminorm K - cutoffKernel N.toSeminorm K r) s(x, z + x) : ℝ≥0) :
        ℝ≥0∞)) ≤ A z + B z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    simp only [hz, ite_false]
    have hne : x ≠ z + x := by simpa [eq_comm] using hz
    rw [← ENNReal.ofReal_coe_nnreal, coe_omittedKernel_of_ne hK hKa hr0 hne,
      show x - (z + x) = -z by abel, intCast_comp_neg, map_neg_eq_map]
    have hz1 : 1 ≤ ‖z‖ := one_le_norm_of_ne_zero hz
    have hNz : κ * ‖z‖ ≤ N (Int.cast ∘ z) := hN z
    have hκz : 0 < κ * ‖z‖ := by positivity
    by_cases h1 : N (Int.cast ∘ z) ≤ r
    · simp only [h1, ite_true, A, K, powerLawProfile, hNz.trans h1]
      exact le_self_add
    · simp only [h1, ite_false, K, powerLawProfile]
      have hNr : r < N (Int.cast ∘ z) := not_le.1 h1
      by_cases h2 : κ * ‖z‖ ≤ r
      · simp only [h2, ite_true, A]
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr0 hNr.le (by linarith)) hc
      · have h2' : r < κ * ‖z‖ := not_le.1 h2
        have htz : t ≤ ‖z‖ := max_le ((div_le_iff₀' hκ).2 h2'.le) hz1
        simp only [h2, ite_false, A, zero_add, B, htz, ite_true]
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc, ← Real.mul_rpow hκ.le (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hκz hNz (by linarith)) hc
  -- the two sums
  have hAsum : ∑' z, A z ≤ ENNReal.ofReal (c * (1 + 2 / κ) ^ d * r ^ (-α)) := by
    simp only [A]
    rw [tsum_ite_const_eq]
    calc (({z : Fin d → ℤ | κ * ‖z‖ ≤ r}.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (c * r ^ (-a))
        ≤ ENNReal.ofReal ((1 + 2 / κ) ^ d * r ^ d) * ENNReal.ofReal (c * r ^ (-a)) := by
          gcongr
          exact encard_mul_norm_le hκ hr
      _ = ENNReal.ofReal (c * (1 + 2 / κ) ^ d * r ^ (-α)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [ha_def, Real.rpow_neg hr0.le, Real.rpow_add hr0, Real.rpow_natCast,
            Real.rpow_neg hr0.le]
          have : (0 : ℝ) < r ^ α := by positivity
          have : (0 : ℝ) < r ^ d := by positivity
          field_simp
  have hBsum : ∑' z, B z ≤ ENNReal.ofReal (c * (κ ^ (-(d : ℝ)) * C0) * r ^ (-α)) := by
    simp only [B]
    rw [ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (c * κ ^ (-a)) *
          ∑' z : Fin d → ℤ, ENNReal.ofReal (if t ≤ ‖z‖ then ‖z‖ ^ (-a) else 0)
        ≤ ENNReal.ofReal (c * κ ^ (-a)) * ENNReal.ofReal (C0 * t ^ (-α)) := by
          gcongr
          have := tsum_ofReal_powerLaw_tail_le hd hα ht1
          rw [hC0, mul_assoc]
          simpa [ha_def] using this
      _ ≤ ENNReal.ofReal (c * κ ^ (-a)) * ENNReal.ofReal (C0 * (κ ^ α * r ^ (-α))) := by
          gcongr
          have hle : r / κ ≤ t := le_max_left _ _
          calc t ^ (-α) ≤ (r / κ) ^ (-α) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
            _ = κ ^ α * r ^ (-α) := by
                rw [Real.div_rpow hr0.le hκ.le, Real.rpow_neg hκ.le, div_inv_eq_mul, mul_comm]
      _ = ENNReal.ofReal (c * (κ ^ (-(d : ℝ)) * C0) * r ^ (-α)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : κ ^ (-a) * κ ^ α = κ ^ (-(d : ℝ)) := by
            rw [← Real.rpow_add hκ, ha_def]
            ring_nf
          calc c * κ ^ (-a) * (C0 * (κ ^ α * r ^ (-α)))
              = c * (κ ^ (-a) * κ ^ α) * C0 * r ^ (-α) := by ring
            _ = _ := by rw [this]; ring
  calc ∑' z : Fin d → ℤ, (if z = 0 then 0 else
        (((radialKernel N.toSeminorm K - cutoffKernel N.toSeminorm K r) s(x, z + x) : ℝ≥0) : ℝ≥0∞))
      ≤ ∑' z, (A z + B z) := ENNReal.tsum_le_tsum hpt
    _ = ∑' z, A z + ∑' z, B z := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (c * (1 + 2 / κ) ^ d * r ^ (-α)) +
          ENNReal.ofReal (c * (κ ^ (-(d : ℝ)) * C0) * r ^ (-α)) := add_le_add hAsum hBsum
    _ = ENNReal.ofReal (c * ((1 + 2 / κ) ^ d + κ ^ (-(d : ℝ)) * C0) * r ^ (-α)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- `1 - e^{-β X} ≤ β X` for `β ≥ 0`. -/
theorem one_sub_exp_neg_mul_le (β X : ℝ) : 1 - Real.exp (-β * X) ≤ β * X := by
  have := Real.add_one_le_exp (-β * X)
  linarith

/-- **Item 3, the omitted layer.** Under the hypotheses of
`tsum_omittedKernel_le`, at every intensity `β ≥ 0`, every off-diagonal probability row of
the omitted layer `1 - e^{-β (J - J_r)}` is at most `β C r^{-α}` for `r ≥ 1`. -/
theorem tsum_omittedLayer_le (hd : 1 ≤ d) {α c κ : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    {N : ModelNorm (Fin d → ℝ)} (hκ : 0 < κ) (hN : ∀ z, κ * ‖z‖ ≤ N (Int.cast ∘ z))
    (hr : 1 ≤ r) (β : ℝ≥0) (x : Fin d → ℤ) :
    rowSum (fun e => ENNReal.ofReal (intensityProfile
      (radialKernel N.toSeminorm (powerLawProfile c (d + α)) -
        cutoffKernel N.toSeminorm (powerLawProfile c (d + α)) r) β e : ℝ)) x ≤
      ENNReal.ofReal (β * (c * ((1 + 2 / κ) ^ d +
        κ ^ (-(d : ℝ)) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) * r ^ (-α))) := by
  rw [ENNReal.ofReal_mul β.coe_nonneg]
  refine le_trans ?_ (mul_le_mul' le_rfl (tsum_omittedKernel_le hd hα hc hκ hN hr x))
  simp only [rowSum_def]
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs
  · simp
  · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul β.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (one_sub_exp_neg_mul_le _ _)

/-- **Item 3, existential form.** -/
theorem exists_tsum_omittedLayer_le (hd : 1 ≤ d) {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (N : ModelNorm (Fin d → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ (β : ℝ≥0) (x : Fin d → ℤ),
      rowSum (fun e => (((radialKernel N.toSeminorm (powerLawProfile c (d + α)) -
        cutoffKernel N.toSeminorm (powerLawProfile c (d + α)) r) e : ℝ≥0) : ℝ≥0∞)) x ≤
        ENNReal.ofReal (C * r ^ (-α)) ∧
      rowSum (fun e => ENNReal.ofReal (intensityProfile
        (radialKernel N.toSeminorm (powerLawProfile c (d + α)) -
          cutoffKernel N.toSeminorm (powerLawProfile c (d + α)) r) β e : ℝ)) x ≤
        ENNReal.ofReal (β * (C * r ^ (-α))) :=
  let ⟨_, hκ, hN⟩ := exists_pos_mul_norm_le_intCast N
  ⟨_, omitted_const_nonneg hc hκ hα, fun _ hr β x =>
    ⟨tsum_omittedKernel_le hd hα hc hκ hN hr x,
      tsum_omittedLayer_le hd hα hc hκ hN hr β x⟩⟩

/-! ### The fork's spelling of `hD` (item 4) -/

/-- The fork's shift probability `(q_∞ - q_r)/(1 - q_r)`, clamped to `[0, 1]`, of the
intensity profiles of `J` and of `J' ≤ J` is the omitted-layer probability
`1 - e^{-β (J - J')}`. -/
theorem shiftProb_intensityProfile_eq {V : Type*} {J J' : Sym2 V → ℝ≥0} (hJ : J' ≤ J)
    (β : ℝ≥0) (e : Sym2 V) :
    min 1 (max 0 (((intensityProfile J β e : ℝ) - (intensityProfile J' β e : ℝ)) /
        (1 - (intensityProfile J' β e : ℝ)))) =
      (intensityProfile (J - J') β e : ℝ) := by
  have hval : ((intensityProfile J β e : ℝ) - (intensityProfile J' β e : ℝ)) /
      (1 - (intensityProfile J' β e : ℝ)) = 1 - Real.exp (-(β : ℝ) * ((J - J') e : ℝ)) := by
    simp only [intensityProfile, Pi.sub_apply, NNReal.coe_sub (hJ e)]
    rw [sub_sub_sub_cancel_left, sub_sub_cancel, div_eq_iff (Real.exp_pos _).ne', sub_mul,
      one_mul, ← Real.exp_add]
    ring_nf
  rw [hval]
  have h0 := (intensityProfile (J - J') β e).2
  simp only [intensityProfile] at h0
  rw [max_eq_right h0.1, min_eq_right h0.2]
  rfl

/-- **Item 4: `hD` in the fork's spelling.** Under the hypotheses of
`tsum_omittedKernel_le`, for every `r ≥ 1` and `x`, the full row (diagonal included) of the
shift probability `min 1 (max 0 ((q_∞ - q_r)/(1 - q_r)))` from the cut-off law `q_r` to the
full law `q_∞` at intensity `β` is at most `β C r^{-α}`. -/
theorem tsum_shiftProb_le (hd : 1 ≤ d) {α c κ : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    {N : ModelNorm (Fin d → ℝ)} (hκ : 0 < κ) (hN : ∀ z, κ * ‖z‖ ≤ N (Int.cast ∘ z))
    (β : ℝ≥0) :
    ∀ r : ℝ, 1 ≤ r → ∀ x : Fin d → ℤ,
      (∑' y, ENNReal.ofReal (min 1 (max 0
        (((intensityProfile (radialKernel N (powerLawProfile c (d + α))) β s(x, y) : ℝ) -
            (intensityProfile (cutoffKernel N (powerLawProfile c (d + α)) r) β s(x, y) : ℝ)) /
          (1 - (intensityProfile (cutoffKernel N (powerLawProfile c (d + α)) r) β
            s(x, y) : ℝ)))))) ≤
        ENNReal.ofReal (β * (c * ((1 + 2 / κ) ^ d +
          κ ^ (-(d : ℝ)) * (((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α))) * r ^ (-α))) := by
  intro r hr x
  have hK : ∀ t, 0 < t → 0 ≤ powerLawProfile c (d + α) t :=
    fun t ht => mul_nonneg hc (Real.rpow_nonneg ht.le _)
  refine le_trans (le_of_eq ?_) (tsum_omittedLayer_le hd hα hc hκ hN hr β x)
  refine tsum_congr fun y => ?_
  rw [shiftProb_intensityProfile_eq
    (cutoffKernel_le_radialKernel hK (one_pos.trans_le hr)) β s(x, y)]
  split_ifs with h
  · subst h
    simp [intensityProfile]
  · rfl

/-! ### Witnesses -/

/-- At `d = 1`, the sup norm (`κ = 1`), `α = 1`, `c = 1` and `r = 1`, the omitted kernel is
the whole kernel off distance `1` and has value `1` at distance `1`. -/
example {x y : Fin 1 → ℤ} (hxy : x ≠ y) :
    ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2) -
        cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2) 1) s(x, y) : ℝ) =
      if ‖x - y‖ ≤ 1 then 1 else ‖x - y‖ ^ (-(2 : ℝ)) := by
  rw [← ModelNorm.toSeminorm_ofNorm, coe_omittedKernel_of_ne
    (fun t ht => (powerLawProfile_pos one_pos ht).le)
    (antitoneOn_powerLawProfile zero_le_one zero_le_two) one_pos hxy]
  simp [powerLawProfile, norm_intCast_comp]

/-- At `d = 1`, the sup norm (`κ = 1`), `α = 1`, `c = 1`, `r = 1`: the constant evaluates to
`C = 7`, and every omitted row is at most `7`. -/
example (x : Fin 1 → ℤ) :
    rowSum (fun e => (((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (powerLawProfile 1 ((1 : ℕ) + 1)) - cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (powerLawProfile 1 ((1 : ℕ) + 1)) 1) e : ℝ≥0) :
        ℝ≥0∞)) x ≤ ENNReal.ofReal 7 := by
  refine (tsum_omittedKernel_le le_rfl one_pos zero_le_one (N := ModelNorm.ofNorm (Fin 1 → ℝ))
    one_pos (fun z => by rw [one_mul, ModelNorm.coe_ofNorm, norm_intCast_comp]) le_rfl
    x).trans_eq ?_
  norm_num

end PercLib.Models.LongRange
