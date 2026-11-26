/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: escaping point masses converge vaguely to zero but have no weakly
convergent subsequence (wiki size-biased-laws, tag WGQ7), and the Laplace limit of a size-biased
weak limit (tag 7W00). No upstream proof is copied, no definition is added and no Input is
introduced.
-/
module

public import PercLib.Meta.Tag
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Support

/-! # Limits of size-biased laws: escape of mass

On `EuclideanSpace ℝ (Fin d)` with `d ≥ 1`, let `e₁` be the first unit vector.

* `not_tendsto_dirac_smul` (WGQ7, first part): the point masses at `n e₁`, as finite measures,
  have no weakly convergent subsequence. A weak limit would have total mass `1`, but a bounded
  continuous bump equal to `1` on the ball of radius `R` has integral `0` against the point masses
  eventually, so the limit gives every ball, hence the whole space, measure `0`.
* `tendsto_integral_dirac_smul_of_hasCompactSupport` (WGQ7, second part): they converge
  vaguely to `0`: the integral of every compactly supported function tends to `0`.
* `tendsto_laplace_of_sizeBias_tendsto` (7W00, Laplace part): if the laws `Q_r` of `X_r/a_r`
  under the size-biased measures converge weakly to `Q` on `[0,∞)` and `h_r a_r → λ > 0`, then
  `(a_r/m_r) E[1 - e^{-h_r X_r}] → ∫ f_λ dQ`, `f_λ(y) = (1 - e^{-λy})/y`, `f_λ(0) = λ`. The
  sequence is `∫ f_{h_r a_r} dQ_r` exactly, and `|f_λ - f_μ| ≤ |λ - μ|` uniformly on `[0,∞)`.
* `tendsto_tail_of_sizeBias_tendsto` (7W00, tail part): if moreover `t > 0` and `Q{t} = 0`,
  then `(a_r/m_r) P(X_r ≥ t a_r) → ∫_{[t,∞)} y⁻¹ dQ`. The sequence is `∫ 1_{y ≥ t} y⁻¹ dQ_r`
  exactly; that integrand is squeezed between bounded continuous functions that differ from
  it only on a small window around the non-atom `t`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology Metric BoundedContinuousFunction

namespace PercLib.Probability

variable {d : ℕ}

/-- The norm of `t e₁` is `|t|`. -/
theorem norm_smul_single (hd : 0 < d) (t : ℝ) :
    ‖t • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)‖ = |t| := by
  rw [norm_smul, (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).1 ⟨0, hd⟩, mul_one,
    Real.norm_eq_abs]

/-- A bounded continuous bump: `1` on `closedBall 0 R`, `0` outside `closedBall 0 (R+1)`,
between `0` and `1`. -/
theorem exists_bump (R : ℝ) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ᵇ ℝ, (∀ x, 0 ≤ f x) ∧ (∀ x, ‖x‖ ≤ R → 1 ≤ f x) ∧
      ∀ x, R + 1 ≤ ‖x‖ → f x = 0 := by
  let g : C(EuclideanSpace ℝ (Fin d), ℝ) :=
    ⟨fun x => max 0 (min 1 (R + 1 - ‖x‖)), by fun_prop⟩
  refine ⟨BoundedContinuousFunction.mkOfBound g 1 fun x y => ?_, fun x => le_max_left _ _,
    fun x hx => ?_, fun x hx => ?_⟩
  · simp only [g, ContinuousMap.coe_mk, Real.dist_eq]
    have h1 : 0 ≤ max 0 (min 1 (R + 1 - ‖x‖)) := le_max_left _ _
    have h2 : max 0 (min 1 (R + 1 - ‖x‖)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have h3 : 0 ≤ max 0 (min 1 (R + 1 - ‖y‖)) := le_max_left _ _
    have h4 : max 0 (min 1 (R + 1 - ‖y‖)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    rw [abs_le]
    constructor <;> linarith
  · simp only [BoundedContinuousFunction.mkOfBound_coe, g, ContinuousMap.coe_mk]
    rw [min_eq_left (by linarith)]
    exact le_max_right _ _
  · simp only [BoundedContinuousFunction.mkOfBound_coe, g, ContinuousMap.coe_mk]
    rw [max_eq_left (min_le_of_right_le (by linarith))]

/-- **WGQ7, no weak limit.** On `EuclideanSpace ℝ (Fin d)` with `d ≥ 1`, the point masses at
`n e₁` (as finite measures) have no weakly convergent subsequence. -/
@[tag "WGQ7"]
theorem not_tendsto_dirac_smul (hd : 0 < d) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d))) :
    ¬ Tendsto (β := FiniteMeasure (EuclideanSpace ℝ (Fin d))) (fun n => ⟨Measure.dirac
        ((φ n : ℝ) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)), inferInstance⟩)
        atTop (𝓝 μ) := by
  intro h0
  have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 h0
  -- total mass one
  have hmass : (μ : Measure (EuclideanSpace ℝ (Fin d))) univ = 1 := by
    have h1 := h (BoundedContinuousFunction.const _ 1)
    have e1 : ∀ n, ∫ x, (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin d)) (1 : ℝ)) x
        ∂(Measure.dirac ((φ n : ℝ) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ))) = 1 :=
      fun n => by simp
    have e2 : ∫ x, (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin d)) (1 : ℝ)) x
        ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) =
          (μ : Measure (EuclideanSpace ℝ (Fin d))).real univ := by simp
    have h1' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (𝓝 ((μ : Measure (EuclideanSpace ℝ (Fin d))).real univ)) := by
      rw [← e2]
      exact h1.congr fun n => e1 n
    have hval := tendsto_nhds_unique h1' tendsto_const_nhds
    rw [measureReal_def] at hval
    have hfin : (μ : Measure (EuclideanSpace ℝ (Fin d))) univ ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin, hval, ENNReal.ofReal_one]
  -- every ball is null
  have hball : ∀ R : ℕ, (μ : Measure (EuclideanSpace ℝ (Fin d))) (closedBall 0 R) = 0 := by
    intro R
    obtain ⟨f, hf0, hf1, hfz⟩ := exists_bump (d := d) (R : ℝ)
    have hlim := h f
    have hev : ∀ᶠ n in atTop, ∫ x, f x ∂(Measure.dirac ((φ n : ℝ) •
        EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ))) = 0 := by
      filter_upwards [eventually_ge_atTop (R + 1)] with n hn
      rw [integral_dirac]
      refine hfz _ ?_
      rw [norm_smul_single hd, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hn.trans (hφ.id_le n)
    have hzero : ∫ x, f x ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) = 0 :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))
    have hle : (μ : Measure (EuclideanSpace ℝ (Fin d))).real (closedBall 0 R) ≤
        ∫ x, f x ∂(μ : Measure (EuclideanSpace ℝ (Fin d))) := by
      rw [← integral_indicator_one measurableSet_closedBall]
      refine integral_mono ((integrable_const 1).indicator measurableSet_closedBall)
        (f.integrable _) fun x => ?_
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) R
      · rw [indicator_of_mem hx]
        exact hf1 x (by simpa using hx)
      · rw [indicator_of_notMem hx]
        exact hf0 x
    rw [hzero] at hle
    have h0 : (μ : Measure (EuclideanSpace ℝ (Fin d))).real (closedBall 0 R) = 0 :=
      le_antisymm hle measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0
  have huniv : (μ : Measure (EuclideanSpace ℝ (Fin d))) univ = 0 := by
    rw [← iUnion_closedBall_nat (0 : EuclideanSpace ℝ (Fin d))]
    exact measure_iUnion_null hball
  rw [hmass] at huniv
  exact one_ne_zero huniv

/-- **Vague limit.** The point masses at `n e₁` converge vaguely to `0`: for every
compactly supported `f`, `∫ f d δ_{n e₁} → 0`. -/
theorem tendsto_integral_dirac_smul_of_hasCompactSupport (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : HasCompactSupport f) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(Measure.dirac ((n : ℝ) •
      EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)))) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hf.isBounded.subset_closedBall 0
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop ⌈R⌉₊] with n hn
  rw [integral_dirac]
  symm
  by_contra hne
  have hmem := hR (subset_tsupport f (Function.mem_support.2 hne))
  rw [mem_closedBall, dist_zero_right, norm_smul_single hd, abs_of_nonneg (Nat.cast_nonneg _)]
    at hmem
  have : (⌈R⌉₊ : ℝ) < n := by exact_mod_cast hn
  linarith [Nat.le_ceil R]

/-- In particular the vague limit `0` is the zero measure: the limit of the integrals is
`∫ f d0`. -/
theorem tendsto_integral_dirac_smul_zero (hd : 0 < d) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : HasCompactSupport f) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(Measure.dirac ((n : ℝ) •
      EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)))) atTop
      (𝓝 (∫ x, f x ∂(0 : Measure (EuclideanSpace ℝ (Fin d))))) := by
  rw [integral_zero_measure]
  exact tendsto_integral_dirac_smul_of_hasCompactSupport hd hf

/-! ### 7W00: the Laplace transform of a size-biased limit -/

section Laplace

open Real

/-- The kernel `f_λ(y) = (1 - e^{-λy})/y`, `f_λ(0) = λ`, is the difference quotient of
`y ↦ 1 - e^{-λy}` at `0`. -/
theorem laplaceKernel_eq_dslope (lam y : ℝ) :
    (if y = 0 then lam else (1 - exp (-(lam * y))) / y) =
      dslope (fun y => 1 - exp (-(lam * y))) 0 y := by
  have hd : HasDerivAt (fun y => 1 - exp (-(lam * y))) lam 0 := by
    have h1 : HasDerivAt (fun y : ℝ => -(lam * y)) (-lam) 0 := by
      have h0 := (hasDerivAt_id (0 : ℝ)).const_mul (-lam)
      simp only [id, mul_one] at h0
      convert h0 using 1
      funext y
      ring
    have h2 := (h1.exp).const_sub 1
    simpa using h2
  split_ifs with hy
  · rw [hy, dslope_same, hd.deriv]
  · rw [dslope_of_ne _ hy, slope_def_field]
    simp

/-- `f_λ` is continuous. -/
theorem continuous_laplaceKernel (lam : ℝ) :
    Continuous fun y : ℝ => if y = 0 then lam else (1 - exp (-(lam * y))) / y := by
  have h : (fun y : ℝ => if y = 0 then lam else (1 - exp (-(lam * y))) / y) =
      dslope (fun y => 1 - exp (-(lam * y))) 0 := funext (laplaceKernel_eq_dslope lam)
  rw [h]
  refine continuousOn_univ.1 ((continuousOn_dslope Filter.univ_mem).2 ⟨by fun_prop, ?_⟩)
  fun_prop

/-- For `λ ≥ 0` and `y ≥ 0`, `0 ≤ f_λ(y) ≤ λ`. -/
theorem laplaceKernel_mem_Icc {lam y : ℝ} (hlam : 0 ≤ lam) (hy : 0 ≤ y) :
    0 ≤ (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∧
      (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ≤ lam := by
  split_ifs with h0
  · exact ⟨hlam, le_rfl⟩
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm h0)
    have h1 : exp (-(lam * y)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    have h2 : 1 - lam * y ≤ exp (-(lam * y)) := by linarith [add_one_le_exp (-(lam * y))]
    refine ⟨div_nonneg (by linarith) hy'.le, ?_⟩
    rw [div_le_iff₀ hy']
    linarith

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |exp (-a) - exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have h1 : exp (-b) ≤ exp (-a) := exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonpos (by linarith)]
  have h2 : exp (-a) - exp (-b) = exp (-a) * (1 - exp (-(b - a))) := by
    rw [mul_sub, mul_one, ← exp_add]
    ring_nf
  rw [h2]
  have h3 : 1 - exp (-(b - a)) ≤ b - a := by linarith [add_one_le_exp (-(b - a))]
  have h4 : 0 ≤ 1 - exp (-(b - a)) := by
    have : exp (-(b - a)) ≤ 1 := exp_le_one_iff.2 (by linarith)
    linarith
  have h5 : exp (-a) ≤ 1 := exp_le_one_iff.2 (by linarith)
  nlinarith [exp_pos (-a)]

/-- **Uniform Lipschitz bound.** For `λ, μ ≥ 0` and `y ≥ 0`, `|f_λ(y) - f_μ(y)| ≤ |λ - μ|`. -/
theorem abs_laplaceKernel_sub_le {lam mu y : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hy : 0 ≤ y) :
    |(if y = 0 then lam else (1 - exp (-(lam * y))) / y) -
        (if y = 0 then mu else (1 - exp (-(mu * y))) / y)| ≤ |lam - mu| := by
  split_ifs with h0
  · exact le_rfl
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm h0)
    rw [div_sub_div_same, show 1 - exp (-(lam * y)) - (1 - exp (-(mu * y))) =
      exp (-(mu * y)) - exp (-(lam * y)) by ring, abs_div, abs_of_pos hy', div_le_iff₀ hy']
    calc |exp (-(mu * y)) - exp (-(lam * y))| ≤ |mu * y - lam * y| :=
          abs_exp_neg_sub_exp_neg_le (by positivity) (by positivity)
      _ = |lam - mu| * y := by
          rw [← sub_mul, abs_mul, abs_of_pos hy', abs_sub_comm]

/-- The bounded continuous version `y ↦ f_λ(max y 0)` of the kernel, for `λ ≥ 0`. -/
theorem exists_bcf_laplaceKernel {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ G : ℝ →ᵇ ℝ, ∀ y, G y = (fun y => if y = 0 then lam else (1 - exp (-(lam * y))) / y)
      (max y 0) := by
  let g : C(ℝ, ℝ) := ⟨fun y => (fun y => if y = 0 then lam else (1 - exp (-(lam * y))) / y)
    (max y 0), (continuous_laplaceKernel lam).comp (continuous_id.max continuous_const)⟩
  refine ⟨BoundedContinuousFunction.mkOfBound g lam fun x y => ?_, fun y => rfl⟩
  have hx := laplaceKernel_mem_Icc hlam (le_max_right x 0)
  have hy := laplaceKernel_mem_Icc hlam (le_max_right y 0)
  simp only [g, ContinuousMap.coe_mk, Real.dist_eq]
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- **The size-biased Laplace identity.** With `Q` the law of `X/a` under the size-biased
measure `(X/m) P`, `(a/m) E[1 - e^{-hX}] = ∫ f_{ha}(max y 0) dQ(y)`. -/
theorem integral_laplaceKernel_sizeBias {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {a h : ℝ} (ha : 0 < a) :
    ∫ y, (fun y => if y = 0 then h * a else (1 - exp (-(h * a * y))) / y) (max y 0)
        ∂(((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map fun ω => X ω / a)) =
      a / (∫ ω, X ω ∂P) * ∫ ω, (1 - exp (-(h * X ω))) ∂P := by
  set m := ∫ ω, X ω ∂P
  have hc : Continuous fun y : ℝ =>
      (fun y => if y = 0 then h * a else (1 - exp (-(h * a * y))) / y) (max y 0) :=
    (continuous_laplaceKernel (h * a)).comp (continuous_id.max continuous_const)
  rw [integral_map (hXm.div_const a).aemeasurable hc.aestronglyMeasurable]
  change ∫ ω, _ ∂(P.withDensity fun ω => ((Real.toNNReal (X ω / m) : NNReal) : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul (hXm.div_const m).real_toNNReal, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]
  have hXa : max (X ω / a) 0 = X ω / a := max_eq_left (div_nonneg (hX0 ω) ha.le)
  rw [hXa]
  rcases (hX0 ω).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · have hne : X ω / a ≠ 0 := (div_pos hpos ha).ne'
    simp only [hne, ↓reduceIte]
    rw [max_eq_left (div_nonneg (hX0 ω) (integral_nonneg hX0)),
      show h * a * (X ω / a) = h * X ω by field_simp]
    field_simp
    rfl

/-- **Laplace part.** Let `X_r ≥ 0` with `0 < m_r = E X_r`, scales `a_r > 0`, and let `Q_r`
be the law of `X_r/a_r` under the size-biased measure `(X_r/m_r) P_r`. If `Q_r → Q` weakly, with
`Q(-∞,0) = 0`, and `h_r > 0` with `h_r a_r → λ > 0`, then
`(a_r/m_r) E[1 - e^{-h_r X_r}] → ∫ f_λ dQ`, `f_λ(y) = (1 - e^{-λy})/y`, `f_λ(0) = λ`. -/
theorem tendsto_laplace_of_sizeBias_tendsto {ι : Type*} {l : Filter ι} {Ω : Type*}
    [MeasurableSpace Ω] (P : ι → Measure Ω) (X : ι → Ω → ℝ) (hXm : ∀ r, Measurable (X r))
    (hX0 : ∀ r ω, 0 ≤ X r ω) (a : ι → ℝ) (ha : ∀ r, 0 < a r) (Q : ι → ProbabilityMeasure ℝ)
    (hQ : ∀ r, (Q r : Measure ℝ) =
      ((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / a r)
    (Q₀ : ProbabilityMeasure ℝ) (hQ₀ : (Q₀ : Measure ℝ) (Iio 0) = 0)
    (hconv : Tendsto Q l (𝓝 Q₀)) (h : ι → ℝ) (hh : ∀ r, 0 < h r) {lam : ℝ} (hlam : 0 < lam)
    (hlim : Tendsto (fun r => h r * a r) l (𝓝 lam)) :
    Tendsto (fun r => a r / (∫ ω, X r ω ∂P r) * ∫ ω, (1 - exp (-(h r * X r ω))) ∂P r) l
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ))) := by
  obtain ⟨G, hG⟩ := exists_bcf_laplaceKernel hlam.le
  -- the target integral only sees `y ≥ 0`
  have htarget : ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ) =
      ∫ y, G y ∂(Q₀ : Measure ℝ) := by
    refine integral_congr_ae ?_
    have hae : ∀ᵐ y ∂(Q₀ : Measure ℝ), 0 ≤ y := by
      have e : {y : ℝ | ¬ 0 ≤ y} = Iio 0 := by
        ext y
        simp
      rw [ae_iff, e]
      exact hQ₀
    filter_upwards [hae] with y hy
    rw [hG y, max_eq_left hy]
  rw [htarget]
  -- the sequence is `∫ G_{λ_r} dQ_r`
  have hseq : ∀ r, a r / (∫ ω, X r ω ∂P r) * ∫ ω, (1 - exp (-(h r * X r ω))) ∂P r =
      ∫ y, (fun y => if y = 0 then h r * a r else (1 - exp (-(h r * a r * y))) / y) (max y 0)
        ∂(Q r : Measure ℝ) := fun r => by
    rw [hQ r, integral_laplaceKernel_sizeBias (P r) (hXm r) (hX0 r) (ha r)]
  simp_rw [hseq]
  -- weak convergence for the fixed kernel
  have hweak : Tendsto (fun r => ∫ y, G y ∂(Q r : Measure ℝ)) l
      (𝓝 (∫ y, G y ∂(Q₀ : Measure ℝ))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv G
  -- the kernels are uniformly close
  have hclose : ∀ r, |∫ y, (fun y => if y = 0 then h r * a r else
      (1 - exp (-(h r * a r * y))) / y) (max y 0) ∂(Q r : Measure ℝ) -
        ∫ y, G y ∂(Q r : Measure ℝ)| ≤ |h r * a r - lam| := fun r => by
    have hlr : 0 ≤ h r * a r := (mul_pos (hh r) (ha r)).le
    obtain ⟨Gr, hGr⟩ := exists_bcf_laplaceKernel hlr
    have e : ∀ y, (fun y => if y = 0 then h r * a r else (1 - exp (-(h r * a r * y))) / y)
        (max y 0) = Gr y := fun y => (hGr y).symm
    simp_rw [e]
    rw [← integral_sub (Gr.integrable _) (G.integrable _)]
    calc |∫ y, (Gr y - G y) ∂(Q r : Measure ℝ)| ≤ ∫ y, |Gr y - G y| ∂(Q r : Measure ℝ) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _y, |h r * a r - lam| ∂(Q r : Measure ℝ) := by
          refine integral_mono ((Gr.integrable _).sub (G.integrable _)).abs
            (integrable_const _) fun y => ?_
          rw [hGr y, hG y]
          exact abs_laplaceKernel_sub_le hlr hlam.le (le_max_right y 0)
      _ = |h r * a r - lam| := by simp
  have hdiff : Tendsto (fun r => |h r * a r - lam|) l (𝓝 0) := by
    have := (hlim.sub_const lam).abs
    simpa using this
  have hsq : Tendsto (fun r => ∫ y, (fun y => if y = 0 then h r * a r else
      (1 - exp (-(h r * a r * y))) / y) (max y 0) ∂(Q r : Measure ℝ) -
        ∫ y, G y ∂(Q r : Measure ℝ)) l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun r => abs_nonneg _) hclose hdiff
  simpa using hsq.add hweak

/-- **Non-vacuity witness for the Laplace limit.** If `X_r ≡ a_r` then `Q_r = δ₁` for every `r`, and
the limit `Q = δ₁` is supported on `[0, ∞)`; the Laplace limit is `1 - e^{-λ}`. -/
theorem sizeBias_law_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {a : ℝ} (ha : 0 < a) :
    ((P.withDensity fun _ => ENNReal.ofReal (a / ∫ _ω, a ∂P)).map fun _ => a / a) =
      Measure.dirac 1 ∧
      (Measure.dirac (1 : ℝ)) (Iio 0) = 0 := by
  constructor
  · have hint : ∫ _ω, a ∂P = a := by simp
    rw [hint, div_self ha.ne', ENNReal.ofReal_one,
      show (fun _ : Ω => (1 : ENNReal)) = 1 from rfl, withDensity_one, Measure.map_const,
      measure_univ, one_smul]
  · simp

/-- **Non-vacuity witness for the Laplace limit, instantiated.** With `X_r ≡ a_r = 1` on a point,
`h_r = λ`, the hypotheses hold with `Q_r = Q = δ₁`, and the theorem gives the constant sequence
`1 - e^{-λ}`. -/
theorem tendsto_laplace_const {ι : Type*} (l : Filter ι) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun _ : ι => (1 : ℝ) / (∫ _ω, (1 : ℝ) ∂(Measure.dirac ())) *
        ∫ _ω, (1 - exp (-(lam * 1))) ∂(Measure.dirac ())) l
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y)
        ∂((⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ))) := by
  refine tendsto_laplace_of_sizeBias_tendsto (l := l) (fun _ => Measure.dirac ())
    (fun _ _ => (1 : ℝ)) (fun _ => measurable_const) (fun _ _ => zero_le_one) (fun _ => 1)
    (fun _ => one_pos) (fun _ => ⟨Measure.dirac 1, inferInstance⟩) (fun _ => ?_)
    ⟨Measure.dirac 1, inferInstance⟩ (by simp) tendsto_const_nhds (fun _ => lam)
    (fun _ => hlam) hlam (by simpa using tendsto_const_nhds)
  exact (sizeBias_law_const (Measure.dirac ()) one_pos).1.symm

end Laplace

/-! ### 7W00: the tail of a size-biased limit -/

section Tail

open Real

/-- A window around a non-atom is eventually small. -/
theorem exists_small_window (Q : Measure ℝ) [IsFiniteMeasure Q] {t ε : ℝ} (ht : 0 < t)
    (hQt : Q {t} = 0) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ ≤ t / 2 ∧ Q.real (Icc (t - δ) (t + δ)) < ε := by
  have hlim := tendsto_measure_biInter_gt (μ := Q) (a := (0 : ℝ))
    (s := fun δ => Icc (t - δ) (t + δ)) (fun _ _ => measurableSet_Icc.nullMeasurableSet)
    (fun i j _ hij => Icc_subset_Icc (by linarith) (by linarith))
    ⟨1, one_pos, measure_ne_top _ _⟩
  have hinter : (⋂ r > (0 : ℝ), Icc (t - r) (t + r)) = {t} := by
    ext y
    simp only [mem_iInter, mem_Icc, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < |y - t| := abs_pos.2 (sub_ne_zero.2 hne)
      have := h (|y - t| / 2) (by positivity)
      rcases le_or_gt 0 (y - t) with h0 | h0
      · rw [abs_of_nonneg h0] at this hpos
        linarith [this.2]
      · rw [abs_of_neg h0] at this hpos
        linarith [this.1]
    · rintro rfl r hr
      constructor <;> linarith
  rw [hinter, hQt] at hlim
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Q (Icc (t - δ) (t + δ)) < ENNReal.ofReal ε :=
    hlim (Iio_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨δ, hδε, hδt⟩ := (hev.and (Ioo_mem_nhdsGT (half_pos ht))).exists
  refine ⟨δ, hδt.1, hδt.2.le, ?_⟩
  rw [measureReal_def]
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hδε |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

/-- **Continuous sandwich of `g(y) = 1_{y ≥ t} / y`.** For `0 < δ ≤ t/2` there are bounded
continuous `L ≤ g ≤ U` with `U - g` and `g - L` at most `(2/t) 1_{[t-δ, t+δ]}`. -/
theorem exists_bcf_sandwich {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hδt : δ ≤ t / 2) :
    ∃ U L : ℝ →ᵇ ℝ, ∀ y,
      L y ≤ (Ici t).indicator (fun y => y⁻¹) y ∧ (Ici t).indicator (fun y => y⁻¹) y ≤ U y ∧
      U y - (Ici t).indicator (fun y => y⁻¹) y ≤
        2 / t * (Icc (t - δ) (t + δ)).indicator 1 y ∧
      (Ici t).indicator (fun y => y⁻¹) y - L y ≤
        2 / t * (Icc (t - δ) (t + δ)).indicator 1 y := by
  have htd : 0 < t - δ := by linarith
  have h2t : 1 / (t - δ) ≤ 2 / t := by
    rw [div_le_div_iff₀ htd ht]
    linarith
  let u : C(ℝ, ℝ) := ⟨fun y => min 1 (max 0 ((y - (t - δ)) / δ)) / max y (t - δ), by
    refine Continuous.div (by fun_prop) (by fun_prop) fun y => ?_
    exact (htd.trans_le (le_max_right _ _)).ne'⟩
  let w : C(ℝ, ℝ) := ⟨fun y => min 1 (max 0 ((y - t) / δ)) / max y t, by
    refine Continuous.div (by fun_prop) (by fun_prop) fun y => ?_
    exact (ht.trans_le (le_max_right _ _)).ne'⟩
  have hclamp : ∀ z : ℝ, 0 ≤ min 1 (max 0 z) ∧ min 1 (max 0 z) ≤ 1 := fun z =>
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hu : ∀ y, 0 ≤ u y ∧ u y ≤ 1 / (t - δ) := fun y => by
    simp only [u, ContinuousMap.coe_mk]
    have hm : t - δ ≤ max y (t - δ) := le_max_right _ _
    have hm0 : 0 < max y (t - δ) := htd.trans_le hm
    refine ⟨div_nonneg (hclamp _).1 hm0.le, ?_⟩
    calc min 1 (max 0 ((y - (t - δ)) / δ)) / max y (t - δ) ≤ 1 / max y (t - δ) :=
          div_le_div_of_nonneg_right (hclamp _).2 hm0.le
      _ ≤ 1 / (t - δ) := one_div_le_one_div_of_le htd hm
  have hw : ∀ y, 0 ≤ w y ∧ w y ≤ 1 / t := fun y => by
    simp only [w, ContinuousMap.coe_mk]
    have hm : t ≤ max y t := le_max_right _ _
    have hm0 : 0 < max y t := ht.trans_le hm
    refine ⟨div_nonneg (hclamp _).1 hm0.le, ?_⟩
    calc min 1 (max 0 ((y - t) / δ)) / max y t ≤ 1 / max y t :=
          div_le_div_of_nonneg_right (hclamp _).2 hm0.le
      _ ≤ 1 / t := one_div_le_one_div_of_le ht hm
  refine ⟨BoundedContinuousFunction.mkOfBound u (1 / (t - δ)) fun x y => ?_,
    BoundedContinuousFunction.mkOfBound w (1 / t) fun x y => ?_, fun y => ?_⟩
  · rw [Real.dist_eq, abs_le]
    constructor <;> linarith [(hu x).1, (hu x).2, (hu y).1, (hu y).2]
  · rw [Real.dist_eq, abs_le]
    constructor <;> linarith [(hw x).1, (hw x).2, (hw y).1, (hw y).2]
  simp only [BoundedContinuousFunction.mkOfBound_coe]
  have hu' := hu y
  have hw' := hw y
  simp only [u, w, ContinuousMap.coe_mk] at hu' hw' ⊢
  by_cases hyt : t ≤ y
  · have hy0 : 0 < y := ht.trans_le hyt
    rw [indicator_of_mem (show y ∈ Ici t from hyt)]
    have hmu : max y (t - δ) = y := max_eq_left (by linarith)
    have hmw : max y t = y := max_eq_left hyt
    have hcu : min 1 (max 0 ((y - (t - δ)) / δ)) = 1 := by
      rw [min_eq_left]
      rw [le_max_iff]
      right
      rw [le_div_iff₀ hδ]
      linarith
    rw [hmu, hcu, hmw]
    refine ⟨?_, by rw [one_div], ?_, ?_⟩
    · calc min 1 (max 0 ((y - t) / δ)) / y ≤ 1 / y :=
            div_le_div_of_nonneg_right (hclamp _).2 hy0.le
        _ = y⁻¹ := one_div y
    · rw [one_div, sub_self]
      exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
    · by_cases hyδ : y ≤ t + δ
      · rw [indicator_of_mem (show y ∈ Icc (t - δ) (t + δ) from ⟨by linarith, hyδ⟩),
          Pi.one_apply, mul_one]
        have : y⁻¹ ≤ 2 / t := by
          rw [inv_eq_one_div]
          exact (one_div_le_one_div_of_le ht hyt).trans (by
            rw [div_le_div_iff₀ ht ht]; linarith)
        linarith [div_nonneg (hclamp ((y - t) / δ)).1 hy0.le]
      · have hc : min 1 (max 0 ((y - t) / δ)) = 1 := by
          rw [min_eq_left]
          rw [le_max_iff]
          right
          rw [le_div_iff₀ hδ]
          linarith
        rw [hc, one_div, sub_self]
        exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
  · rw [indicator_of_notMem (show y ∉ Ici t from hyt)]
    have hw0 : min 1 (max 0 ((y - t) / δ)) = 0 := by
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
      exact min_eq_right zero_le_one
    rw [hw0, zero_div]
    refine ⟨le_rfl, hu'.1, ?_, ?_⟩
    swap
    · rw [sub_zero]
      exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
    rw [sub_zero]
    by_cases hyδ : t - δ ≤ y
    · rw [indicator_of_mem (show y ∈ Icc (t - δ) (t + δ) from ⟨hyδ, by linarith⟩),
        Pi.one_apply, mul_one]
      exact hu'.2.trans h2t
    · have hc : min 1 (max 0 ((y - (t - δ)) / δ)) = 0 := by
        rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
        exact min_eq_right zero_le_one
      rw [hc, zero_div]
      exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `g(y) = 1_{y ≥ t}/y` is integrable for every finite measure. -/
theorem integrable_indicator_inv (Q : Measure ℝ) [IsFiniteMeasure Q] {t : ℝ} (ht : 0 < t) :
    Integrable ((Ici t).indicator fun y : ℝ => y⁻¹) Q := by
  refine Integrable.of_bound ((measurable_inv.indicator measurableSet_Ici).aestronglyMeasurable)
    (1 / t) (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : t ≤ y
  · rw [indicator_of_mem (show y ∈ Ici t from hy), norm_inv, Real.norm_eq_abs,
      abs_of_pos (ht.trans_le hy), ← one_div]
    exact one_div_le_one_div_of_le ht hy
  · rw [indicator_of_notMem (show y ∉ Ici t from hy), norm_zero]
    positivity

/-- **Portmanteau for `1_{y ≥ t}/y`.** If `Q_r → Q` weakly and `Q{t} = 0` with `t > 0`, then
`∫ 1_{y ≥ t} y⁻¹ dQ_r → ∫ 1_{y ≥ t} y⁻¹ dQ`. -/
theorem tendsto_integral_indicator_inv {ι : Type*} {l : Filter ι} (Q : ι → ProbabilityMeasure ℝ)
    (Q₀ : ProbabilityMeasure ℝ) (hconv : Tendsto Q l (𝓝 Q₀)) {t : ℝ} (ht : 0 < t)
    (hQt : (Q₀ : Measure ℝ) {t} = 0) :
    Tendsto (fun r => ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q r : Measure ℝ)) l
      (𝓝 (∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q₀ : Measure ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδt, hwin⟩ := exists_small_window (Q₀ : Measure ℝ) ht hQt
    (show 0 < ε * t / 8 by positivity)
  obtain ⟨U, L, hUL⟩ := exists_bcf_sandwich ht hδ hδt
  have hU := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv U
  have hL := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv L
  have hint := fun (μ : ProbabilityMeasure ℝ) => integrable_indicator_inv (μ : Measure ℝ) ht
  have hwinI : ∀ μ : ProbabilityMeasure ℝ,
      ∫ y, 2 / t * (Icc (t - δ) (t + δ)).indicator 1 y ∂(μ : Measure ℝ) =
        2 / t * (μ : Measure ℝ).real (Icc (t - δ) (t + δ)) := fun μ => by
    rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
  have hwI : ∀ μ : ProbabilityMeasure ℝ,
      Integrable (fun y => 2 / t * (Icc (t - δ) (t + δ)).indicator 1 y) (μ : Measure ℝ) :=
    fun μ => ((integrable_const 1).indicator measurableSet_Icc).const_mul _
  -- the sandwich errors under `Q₀`
  have herrU : ∫ y, U y ∂(Q₀ : Measure ℝ) ≤
      ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q₀ : Measure ℝ) + ε / 4 := by
    have h1 : ∫ y, U y ∂(Q₀ : Measure ℝ) -
        ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q₀ : Measure ℝ) ≤
          2 / t * (Q₀ : Measure ℝ).real (Icc (t - δ) (t + δ)) := by
      rw [← integral_sub (U.integrable _) (hint Q₀), ← hwinI Q₀]
      exact integral_mono ((U.integrable _).sub (hint Q₀)) (hwI Q₀) fun y => (hUL y).2.2.1
    have h2 : 2 / t * (Q₀ : Measure ℝ).real (Icc (t - δ) (t + δ)) ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ht]
      nlinarith
    linarith
  have herrL : ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q₀ : Measure ℝ) - ε / 4 ≤
      ∫ y, L y ∂(Q₀ : Measure ℝ) := by
    have h1 : ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q₀ : Measure ℝ) -
        ∫ y, L y ∂(Q₀ : Measure ℝ) ≤ 2 / t * (Q₀ : Measure ℝ).real (Icc (t - δ) (t + δ)) := by
      rw [← integral_sub (hint Q₀) (L.integrable _), ← hwinI Q₀]
      exact integral_mono ((hint Q₀).sub (L.integrable _)) (hwI Q₀) fun y => (hUL y).2.2.2
    have h2 : 2 / t * (Q₀ : Measure ℝ).real (Icc (t - δ) (t + δ)) ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ht]
      nlinarith
    linarith
  filter_upwards [(Metric.tendsto_nhds.1 hU) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.1 hL) (ε / 4) (by positivity)] with r hUr hLr
  rw [Real.dist_eq] at hUr hLr ⊢
  have hle : ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q r : Measure ℝ) ≤
      ∫ y, U y ∂(Q r : Measure ℝ) :=
    integral_mono (hint (Q r)) (U.integrable _) fun y => (hUL y).2.1
  have hge : ∫ y, L y ∂(Q r : Measure ℝ) ≤
      ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q r : Measure ℝ) :=
    integral_mono (L.integrable _) (hint (Q r)) fun y => (hUL y).1
  rw [abs_lt] at hUr hLr ⊢
  constructor <;> linarith [hUr.1, hUr.2, hLr.1, hLr.2]

/-- **The size-biased tail identity.** With `Q` the law of `X/a` under `(X/m) P`,
`(a/m) P(X ≥ t a) = ∫ 1_{y ≥ t} y⁻¹ dQ(y)` for `t, a > 0`. -/
theorem integral_indicator_inv_sizeBias {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ∫ y, (Ici t).indicator (fun y => y⁻¹) y
        ∂(((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map fun ω => X ω / a)) =
      a / (∫ ω, X ω ∂P) * P.real {ω | t * a ≤ X ω} := by
  set m := ∫ ω, X ω ∂P
  rw [integral_map (hXm.div_const a).aemeasurable
    (measurable_inv.indicator measurableSet_Ici).aestronglyMeasurable]
  change ∫ ω, _ ∂(P.withDensity fun ω => ((Real.toNNReal (X ω / m) : NNReal) : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul (hXm.div_const m).real_toNNReal,
    ← integral_indicator_one (measurableSet_le measurable_const hXm), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]
  rw [max_eq_left (div_nonneg (hX0 ω) (integral_nonneg hX0))]
  by_cases hω : t * a ≤ X ω
  · have hX : 0 < X ω := (mul_pos ht ha).trans_le hω
    rw [indicator_of_mem (show X ω / a ∈ Ici t from (le_div_iff₀ ha).2 hω),
      indicator_of_mem (show ω ∈ {ω | t * a ≤ X ω} from hω), Pi.one_apply, mul_one]
    field_simp
    rfl
  · rw [indicator_of_notMem (show X ω / a ∉ Ici t from fun h => hω ((le_div_iff₀ ha).1 h)),
      indicator_of_notMem (show ω ∉ {ω | t * a ≤ X ω} from hω), mul_zero, mul_zero]

/-- **Tail part.** Let `X_r ≥ 0`, scales `a_r > 0`, and let `Q_r` be the law of `X_r/a_r`
under the size-biased measure `(X_r/m_r) P_r`, `m_r = E X_r`. If `Q_r → Q` weakly and `t > 0`
with `Q{t} = 0`, then `(a_r/m_r) P(X_r ≥ t a_r) → ∫_{[t,∞)} y⁻¹ dQ`. -/
theorem tendsto_tail_of_sizeBias_tendsto {ι : Type*} {l : Filter ι} {Ω : Type*}
    [MeasurableSpace Ω] (P : ι → Measure Ω) (X : ι → Ω → ℝ) (hXm : ∀ r, Measurable (X r))
    (hX0 : ∀ r ω, 0 ≤ X r ω) (a : ι → ℝ) (ha : ∀ r, 0 < a r) (Q : ι → ProbabilityMeasure ℝ)
    (hQ : ∀ r, (Q r : Measure ℝ) =
      ((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / a r)
    (Q₀ : ProbabilityMeasure ℝ) (hconv : Tendsto Q l (𝓝 Q₀)) {t : ℝ} (ht : 0 < t)
    (hQt : (Q₀ : Measure ℝ) {t} = 0) :
    Tendsto (fun r => a r / (∫ ω, X r ω ∂P r) * (P r).real {ω | t * a r ≤ X r ω}) l
      (𝓝 (∫ y in Ici t, y⁻¹ ∂(Q₀ : Measure ℝ))) := by
  rw [← integral_indicator measurableSet_Ici]
  have hseq : ∀ r, a r / (∫ ω, X r ω ∂P r) * (P r).real {ω | t * a r ≤ X r ω} =
      ∫ y, (Ici t).indicator (fun y => y⁻¹) y ∂(Q r : Measure ℝ) := fun r => by
    rw [hQ r, integral_indicator_inv_sizeBias (P r) (hXm r) (hX0 r) (ha r) ht]
  simp_rw [hseq]
  exact tendsto_integral_indicator_inv Q Q₀ hconv ht hQt

/-- **Non-vacuity witness for the tail part.** With `X_r ≡ a_r = 1` on a point, `Q_r = Q = δ₁` and
`t = 1/2` (not an atom of `δ₁`), the theorem applies. -/
theorem tendsto_tail_const {ι : Type*} (l : Filter ι) :
    Tendsto (fun _ : ι => (1 : ℝ) / (∫ _ω, (1 : ℝ) ∂(Measure.dirac ())) *
        (Measure.dirac ()).real {_ω : Unit | 1 / 2 * 1 ≤ (1 : ℝ)}) l
      (𝓝 (∫ y in Ici (1 / 2), y⁻¹
        ∂((⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ))) := by
  refine tendsto_tail_of_sizeBias_tendsto (l := l) (fun _ => Measure.dirac ())
    (fun _ _ => (1 : ℝ)) (fun _ => measurable_const) (fun _ _ => zero_le_one) (fun _ => 1)
    (fun _ => one_pos) (fun _ => ⟨Measure.dirac 1, inferInstance⟩) (fun _ => ?_)
    ⟨Measure.dirac 1, inferInstance⟩ tendsto_const_nhds (by norm_num) ?_
  · exact (sizeBias_law_const (Measure.dirac ()) one_pos).1.symm
  · simp

end Tail

end PercLib.Probability
