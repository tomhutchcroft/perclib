/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Cap (bounded truncation) approximation of extended moments: monotone convergence in the cap and a
quantitative higher-moment error bound. Extended values are kept in `ℝ≥0∞`, so infinite clusters
are preserved as `⊤`.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Basic.Real.ENatENNReal

/-!
# Cap approximation of extended moments

Let `X` be a measurable space with a measure `μ`, let `g : X → ℕ∞` be measurable and let
`B : ℕ`. The *capped `p`-th moment* is

`∫⁻ x, ((g x ⊓ B).toNat : ℝ≥0∞) ^ p ∂μ`,

the `p`-th moment of `g` truncated at `B`. The truncation is the `ℝ≥0∞`-valued cap
`(g x : ℝ≥0∞) ⊓ B` (this identity is `capToNat_eq_inf`; note that the naive reading
`(g x).toNat` would send `⊤` to `0`, so the cap must be taken in `ℕ∞` before `toNat`).

## Main results

* `tendsto_capToNat_atTop`: `((n ⊓ B).toNat : ℝ≥0∞) → n` as `B → ∞`, for every `n : ℕ∞`
  including `n = ⊤`.
* `tendsto_lintegral_capToNat_pow`, `iSup_lintegral_capToNat_pow`: the capped moments increase to
  the full extended moment `∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ`. No finiteness hypothesis: the limit is
  `⊤` when the moment is infinite.
* `lintegral_pow_le_lintegral_capToNat_pow_add`: for `p ≤ q` and `1 ≤ B`, the pointwise bound
  `n ^ p ≤ (n ⊓ B) ^ p + B ^ -(q - p) * n ^ q` integrates to
  `∫⁻ g ^ p ≤ ∫⁻ (g ⊓ B) ^ p + B ^ -(q - p) * ∫⁻ g ^ q`, i.e. the cap error is controlled by the
  higher moment `∫⁻ g ^ q` at rate `B ^ -(q - p)`. With `q = p + 1` the rate is `1 / B`.
* `tendsto_integral_capToNat_pow`: when the extended `p`-th moment is finite, the ordinary
  integrals of the bounded capped integrands converge to its `toReal`. If the moment is infinite
  the `ℝ≥0∞` statement is the only one available, since `⊤.toReal = 0` in `ℝ≥0∞` would be
  meaningless as a real moment.
* `capMoment_error_le`: the quantitative `O(1/B)` error bound for the real-valued capped moments,
  uniform in all parameters other than the higher moment bound.

No derivative, no continuity in any parameter and no interchange of the cap limit with
differentiation is asserted here.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

variable {X : Type*} [MeasurableSpace X]

/-! ### The cap as an `ℝ≥0∞`-valued truncation -/

/-- The cap `n ⊓ B` read through `toNat` is the `ℝ≥0∞`-valued truncation of `n` at `B`. This is
the bridge between the `ℕ∞`-valued cap used in the cluster-moment statements and the `ℝ≥0∞`
moment. -/
theorem capToNat_eq_inf (n : ℕ∞) (B : ℕ) :
    ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) = (n : ℝ≥0∞) ⊓ (B : ℝ≥0∞) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe m =>
      rcases le_total m B with hle | hle
      · rw [inf_eq_left.mpr (by exact_mod_cast hle), ENat.toNat_natCast,
          inf_eq_left.mpr (by exact_mod_cast hle)]
        rfl
      · rw [inf_eq_right.mpr (by exact_mod_cast hle), ENat.toNat_natCast,
          inf_eq_right.mpr (by exact_mod_cast hle)]

/-- The capped value is monotone in the cap. -/
theorem monotone_capToNat (n : ℕ∞) :
    Monotone fun B : ℕ => ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) := by
  intro B B' hBB
  have hle : n ⊓ (B : ℕ∞) ≤ n ⊓ (B' : ℕ∞) := inf_le_inf_left n (by exact_mod_cast hBB)
  have hne : n ⊓ (B' : ℕ∞) ≠ ⊤ := ne_top_of_le_ne_top (by simp) inf_le_right
  have h := ENat.toNat_le_toNat hle hne
  change ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ≤ ((n ⊓ (B' : ℕ∞)).toNat : ℝ≥0∞)
  exact_mod_cast h

/-- The capped value is bounded by the cap. -/
theorem capToNat_le (n : ℕ∞) (B : ℕ) :
    ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ≤ (B : ℝ≥0∞) := by
  rw [capToNat_eq_inf]
  exact inf_le_right

/-- **The cap converges to the value**, including at `n = ⊤` where the cap itself runs to `⊤`. -/
theorem tendsto_capToNat_atTop (n : ℕ∞) :
    Tendsto (fun B : ℕ => ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞)) atTop (𝓝 (n : ℝ≥0∞)) := by
  induction n using ENat.recTopCoe with
  | top =>
      have h : (fun B : ℕ => ((⊤ ⊓ (B : ℕ∞)).toNat : ℝ≥0∞)) = fun B : ℕ => (B : ℝ≥0∞) := by
        funext B
        simp
      rw [h]
      change Tendsto (fun B : ℕ => (B : ℝ≥0∞)) atTop (𝓝 ⊤)
      rw [← ENNReal.iSup_natCast]
      exact tendsto_atTop_iSup fun _ _ hBB => by exact_mod_cast hBB
  | coe m =>
      have hev : (fun B : ℕ => ((↑m ⊓ (B : ℕ∞)).toNat : ℝ≥0∞)) =ᶠ[atTop] fun _ => (m : ℝ≥0∞) := by
        filter_upwards [eventually_ge_atTop m] with B hB
        rw [inf_eq_left.mpr (by exact_mod_cast hB), ENat.toNat_natCast]
      exact (Filter.tendsto_congr' hev).2 tendsto_const_nhds

/-- The supremum of the capped values is the value itself. -/
theorem iSup_capToNat (n : ℕ∞) :
    (⨆ B : ℕ, ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞)) = (n : ℝ≥0∞) :=
  tendsto_nhds_unique (tendsto_atTop_iSup (monotone_capToNat n)) (tendsto_capToNat_atTop n)

/-! ### Monotone convergence of the capped moments -/

/-- The capped moments are monotone in the cap. -/
theorem monotone_lintegral_capToNat_pow (μ : Measure X) (g : X → ℕ∞) (p : ℕ) :
    Monotone fun B : ℕ => ∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ :=
  fun _ _ hBB =>
    lintegral_mono fun x => pow_le_pow_left₀ zero_le (monotone_capToNat (g x) hBB) p

/-- **Monotone convergence of capped moments to the full extended moment.** No finiteness is
assumed: if the extended moment is infinite the capped moments tend to `⊤`. -/
theorem tendsto_lintegral_capToNat_pow (μ : Measure X) {g : X → ℕ∞} (hg : Measurable g) (p : ℕ) :
    Tendsto (fun B : ℕ => ∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ) atTop
      (𝓝 (∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun B x => ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p)
    (F := fun x => (g x : ℝ≥0∞) ^ p) ?_ ?_ ?_
  · intro B
    exact (((measurable_of_countable
      (fun n : ℕ∞ => ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞))).comp hg).pow_const p).aemeasurable
  · exact Eventually.of_forall fun x =>
      fun _ _ hBB => pow_le_pow_left₀ zero_le (monotone_capToNat (g x) hBB) p
  · exact Eventually.of_forall fun x =>
      ((ENNReal.continuous_pow p).tendsto (g x : ℝ≥0∞)).comp (tendsto_capToNat_atTop (g x))

/-- The supremum form of monotone convergence of capped moments. -/
theorem iSup_lintegral_capToNat_pow (μ : Measure X) {g : X → ℕ∞} (hg : Measurable g) (p : ℕ) :
    (⨆ B : ℕ, ∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ) =
      ∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ :=
  tendsto_nhds_unique (tendsto_atTop_iSup (monotone_lintegral_capToNat_pow μ g p))
    (tendsto_lintegral_capToNat_pow μ hg p)

/-! ### The quantitative higher-moment bound -/

/-- **Pointwise cap error bound.** For `p ≤ q` and `1 ≤ B`,
`n ^ p ≤ (n ⊓ B) ^ p + B ^ -(q - p) * n ^ q`; on `{n ≤ B}` the first term already dominates and
on `{n > B}` the loss `n ^ p - B ^ p` is paid for by the higher power at rate `B ^ -(q - p)`. -/
theorem pow_le_capToNat_pow_add_inv_mul_pow {p q : ℕ} (hpq : p ≤ q) {B : ℕ} (hB : 1 ≤ B)
    (n : ℕ∞) :
    (n : ℝ≥0∞) ^ p ≤ ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p +
      ((B : ℝ≥0∞) ^ (q - p))⁻¹ * (n : ℝ≥0∞) ^ q := by
  rw [capToNat_eq_inf]
  rcases le_or_gt (n : ℝ≥0∞) (B : ℝ≥0∞) with h | h
  · rw [inf_eq_left.mpr h]
    exact le_add_right le_rfl
  · rw [inf_eq_right.mpr h.le]
    have hB0 : (B : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hBt : (B : ℝ≥0∞) ≠ ⊤ := by simp
    have hx0 : (B : ℝ≥0∞) ^ (q - p) ≠ 0 := pow_ne_zero _ hB0
    have hxt : (B : ℝ≥0∞) ^ (q - p) ≠ ⊤ := ENNReal.pow_ne_top hBt
    have hmain : (B : ℝ≥0∞) ^ (q - p) * (n : ℝ≥0∞) ^ p ≤ (n : ℝ≥0∞) ^ q := by
      calc (B : ℝ≥0∞) ^ (q - p) * (n : ℝ≥0∞) ^ p
          ≤ (n : ℝ≥0∞) ^ (q - p) * (n : ℝ≥0∞) ^ p :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le h.le _) zero_le
        _ = (n : ℝ≥0∞) ^ ((q - p) + p) := (pow_add _ _ _).symm
        _ = (n : ℝ≥0∞) ^ q := by rw [Nat.sub_add_cancel hpq]
    calc (n : ℝ≥0∞) ^ p
        = ((B : ℝ≥0∞) ^ (q - p))⁻¹ * ((B : ℝ≥0∞) ^ (q - p) * (n : ℝ≥0∞) ^ p) := by
          rw [ENNReal.inv_mul_cancel_left hx0 hxt]
      _ ≤ ((B : ℝ≥0∞) ^ (q - p))⁻¹ * (n : ℝ≥0∞) ^ q :=
          mul_le_mul_of_nonneg_left hmain zero_le
      _ ≤ (B : ℝ≥0∞) ^ p + ((B : ℝ≥0∞) ^ (q - p))⁻¹ * (n : ℝ≥0∞) ^ q :=
          le_add_left le_rfl

/-- **The integrated quantitative cap error bound**, in `ℝ≥0∞`. -/
theorem lintegral_pow_le_lintegral_capToNat_pow_add (μ : Measure X) {g : X → ℕ∞}
    (hg : Measurable g) {p q : ℕ} (hpq : p ≤ q) {B : ℕ} (hB : 1 ≤ B) :
    ∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ ≤
      ∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ +
        ((B : ℝ≥0∞) ^ (q - p))⁻¹ * ∫⁻ x, (g x : ℝ≥0∞) ^ q ∂μ := by
  have hcap : Measurable fun x => ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p :=
    ((measurable_of_countable
      (fun n : ℕ∞ => ((n ⊓ (B : ℕ∞)).toNat : ℝ≥0∞))).comp hg).pow_const p
  have hq : Measurable fun x => (g x : ℝ≥0∞) ^ q :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp hg |>.pow_const q
  calc ∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ
      ≤ ∫⁻ x, (((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p +
          ((B : ℝ≥0∞) ^ (q - p))⁻¹ * (g x : ℝ≥0∞) ^ q) ∂μ :=
        lintegral_mono fun x => pow_le_capToNat_pow_add_inv_mul_pow hpq hB (g x)
    _ = ∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ +
          ((B : ℝ≥0∞) ^ (q - p))⁻¹ * ∫⁻ x, (g x : ℝ≥0∞) ^ q ∂μ := by
        rw [lintegral_add_left hcap, lintegral_const_mul _ hq]

/-! ### The real-valued capped moments -/

/-- The capped moment is bounded by the cap, so it is finite for every finite measure. -/
theorem lintegral_capToNat_pow_ne_top (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℕ∞)
    (p B : ℕ) :
    (∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ := by
  have hle : (∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ) ≤
      (B : ℝ≥0∞) ^ p * μ Set.univ := by
    calc ∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ
        ≤ ∫⁻ _x, (B : ℝ≥0∞) ^ p ∂μ :=
          lintegral_mono fun x => pow_le_pow_left₀ zero_le (capToNat_le (g x) B) p
      _ = (B : ℝ≥0∞) ^ p * μ Set.univ := lintegral_const _
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (measure_ne_top μ _)) hle

/-- **The real-valued capped moment is the `toReal` of the extended one.** The cap makes the
integrand bounded, so the ordinary integral is finite. -/
theorem integral_capToNat_pow_eq_toReal (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℕ∞}
    (hg : Measurable g) (p B : ℕ) :
    ∫ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p ∂μ =
      (∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ).toReal := by
  have hmeas : Measurable fun x => ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p :=
    ((measurable_of_countable (fun n : ℕ∞ => ((n ⊓ (B : ℕ∞)).toNat : ℝ))).comp hg).pow_const p
  have hbdd : ∀ x, ‖((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p‖ ≤ (B : ℝ) ^ p := by
    intro x
    have hle : ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ≤ B := by
      have h := ENat.toNat_le_toNat (inf_le_right : g x ⊓ (B : ℕ∞) ≤ (B : ℕ∞)) (by simp)
      exact_mod_cast h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hle p
  have hint : Integrable (fun x => ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p) μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable _ (Eventually.of_forall hbdd)
  have hnn : 0 ≤ᵐ[μ] fun x => ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p :=
    Eventually.of_forall fun x => by positivity
  have hkey := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
  have hfun : (fun x => ENNReal.ofReal (((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p)) =
      fun x => ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p := by
    funext x
    rw [ENNReal.ofReal_pow (by positivity)]
    norm_cast
  rw [hfun] at hkey
  have h := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity)] at h
  exact h

/-- **Convergence of real-valued capped moments**, under finiteness of the extended `p`-th
moment. The limit `(∫⁻ (g x) ^ p).toReal` is the honest real moment; without the finiteness
hypothesis only the `ℝ≥0∞` statement holds. -/
theorem tendsto_integral_capToNat_pow (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℕ∞}
    (hg : Measurable g) (p : ℕ) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ ≠ ⊤) :
    Tendsto (fun B : ℕ => ∫ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p ∂μ) atTop
      (𝓝 ((∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ).toReal)) := by
  have h : Tendsto
      (fun B : ℕ => (∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ).toReal) atTop
      (𝓝 ((∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp (tendsto_lintegral_capToNat_pow μ hg p)
  simpa only [integral_capToNat_pow_eq_toReal μ hg p] using h

/-- **Quantitative error bound for the real-valued capped moment.** If the `(p+1)`-st extended
moment is finite, the cap error of the `p`-th moment is at most `B⁻¹` times that higher moment. -/
theorem capMoment_error_le (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℕ∞} (hg : Measurable g)
    (p : ℕ) {B : ℕ} (hB : 1 ≤ B) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ^ (p + 1) ∂μ ≠ ⊤) :
    (∫⁻ x, (g x : ℝ≥0∞) ^ p ∂μ).toReal -
        ∫ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ) ^ p ∂μ ≤
      (B : ℝ)⁻¹ * (∫⁻ x, (g x : ℝ≥0∞) ^ (p + 1) ∂μ).toReal := by
  rw [integral_capToNat_pow_eq_toReal μ hg p]
  have h := lintegral_pow_le_lintegral_capToNat_pow_add μ hg (Nat.le_succ p) hB (q := p + 1)
  rw [show p + 1 - p = 1 from by omega, pow_one] at h
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hcapfin := lintegral_capToNat_pow_ne_top μ g p B
  have hx : (B : ℝ≥0∞)⁻¹ * (∫⁻ x, (g x : ℝ≥0∞) ^ (p + 1) ∂μ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hB0) hfin
  have htop : (∫⁻ x, ((g x ⊓ (B : ℕ∞)).toNat : ℝ≥0∞) ^ p ∂μ) +
      (B : ℝ≥0∞)⁻¹ * (∫⁻ x, (g x : ℝ≥0∞) ^ (p + 1) ∂μ) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hcapfin, hx⟩
  have ht := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_add hcapfin hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at ht
  linarith

end PercLib.Probability
