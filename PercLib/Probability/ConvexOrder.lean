/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22, against pinned mathlib. No upstream proof is copied.
Mathematical reference: M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer
(2007), Section 3.A (convex order, closure under weak limits with uniform integrability).
The identification of the limit law is proved here through characteristic functions:
`x ↦ t²x²/2 ± cos (t x)` and `x ↦ t²x²/2 ± sin (t x)` are convex.
-/
module

public import PercLib.Probability.ConvexComparison
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Convex order of laws on `ℝ` and weak limits

For laws `μ, ν` on `ℝ` with a first moment, `ConvexOrder μ ν` (written `μ ≤cx ν` in the
literature) says that `∫ φ dμ ≤ ∫ φ dν` for every convex `φ : ℝ → ℝ`, as extended
expectations in `(-∞, ∞]`. `UnifIntegrableAlong f ν` says that `f` is uniformly integrable
along a family of measures `ν i` (possibly not living on a common probability space).

## Main results

* `ConvexOrder.unifIntegrableAlong`: if `μ i ≤cx ν i` and `|f|` is convex, uniform
  integrability of `f` along `ν` transfers to `μ`.
* `integrable_of_tendsto_of_unifIntegrableAlong`,
  `tendsto_integral_of_unifIntegrableAlong`: under weak convergence and uniform
  integrability of `g`, the limit integrates `g`, and integrals of continuous functions
  dominated by `A + B |g|` converge.
* `ConvexOrder.of_tendsto`: convex order passes to weak limits when the larger laws have
  uniformly integrable first moments.
* `ConvexOrder.integral_id_eq_of_tendsto`: the limit laws then have equal means.
* `ConvexOrder.eq_of_integral_sq_eq`: convex order with equal finite second moments forces
  equality of the laws.
* `ConvexOrder.eq_of_tendsto_of_tendsto_sub`: a vanishing gap of second moments along
  convergent sequences identifies the limit laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace PercLib.Probability

/-! ### Definitions -/

/-- Convex order `μ ≤cx ν` of two laws on `ℝ`: both have a first moment, and for every convex
`φ`, `∫ φ dμ ≤ ∫ φ dν` as extended expectations in `(-∞, ∞]`. Since `φ` lies above an affine
function, its negative parts are integrable, so the extended comparison says exactly: if `φ`
is `ν`-integrable then it is `μ`-integrable and the integrals compare. -/
def ConvexOrder (μ ν : Measure ℝ) : Prop :=
  Integrable (fun x => x) μ ∧ Integrable (fun x => x) ν ∧
    ∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ → Integrable φ ν →
      Integrable φ μ ∧ ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν

/-- Uniform integrability of `f` along a family of measures `ν i`: `f` is integrable for every
`ν i`, and the tail integrals `∫_{K < |f|} |f| dν i` are small uniformly in `i` for large
`K`. For the laws `ν i` of random variables `Y i` this is uniform integrability of `f (Y i)`,
the variables possibly living on different probability spaces. -/
def UnifIntegrableAlong {α ι : Type*} [MeasurableSpace α] (f : α → ℝ) (ν : ι → Measure α) :
    Prop :=
  (∀ i, Integrable f (ν i)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ i, ∫ x in {x | K < |f x|}, |f x| ∂ν i ≤ ε

namespace ConvexOrder

variable {μ ν : Measure ℝ}

theorem integrable_left (h : ConvexOrder μ ν) : Integrable (fun x => x) μ := h.1

theorem integrable_right (h : ConvexOrder μ ν) : Integrable (fun x => x) ν := h.2.1

theorem integrable_of_integrable (h : ConvexOrder μ ν) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hφν : Integrable φ ν) : Integrable φ μ :=
  (h.2.2 φ hφ hφν).1

theorem integral_le (h : ConvexOrder μ ν) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hφν : Integrable φ ν) : ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν :=
  (h.2.2 φ hφ hφν).2

/-- Laws in convex order have equal means. -/
theorem integral_id_eq (h : ConvexOrder μ ν) : ∫ x, x ∂μ = ∫ x, x ∂ν := by
  refine le_antisymm (h.integral_le (convexOn_id convex_univ) h.integrable_right) ?_
  have := h.integral_le (concaveOn_id convex_univ).neg h.integrable_right.neg
  simp only [Pi.neg_apply, id] at this
  rw [integral_neg, integral_neg] at this
  linarith

theorem refl (hμ : Integrable (fun x => x) μ) : ConvexOrder μ μ :=
  ⟨hμ, hμ, fun _ _ hφ => ⟨hφ, le_rfl⟩⟩

end ConvexOrder

/-! ### Uniform integrability along a family of measures -/

section UnifIntegrableAlong

variable {α ι : Type*} [MeasurableSpace α] {f : α → ℝ} {ν : ι → Measure α}

theorem UnifIntegrableAlong.integrable (h : UnifIntegrableAlong f ν) (i : ι) :
    Integrable f (ν i) :=
  h.1 i

/-- Uniform integrability in hinge form: `∫ (|f| - K)₊ dν i` is small for all large `K`,
uniformly in `i`. -/
theorem UnifIntegrableAlong.exists_integral_max_sub_le (hf : Measurable f)
    (h : UnifIntegrableAlong f ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ K' ≥ K, ∀ i, ∫ x, max (|f x| - K') 0 ∂ν i ≤ ε := by
  obtain ⟨K, hK⟩ := h.2 ε hε
  refine ⟨max K 0, fun K' hK' i => le_trans ?_ (hK i)⟩
  have hs : MeasurableSet {x | K < |f x|} := 
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)
  rw [← integral_indicator hs]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => le_max_right _ _)
    ((h.1 i).abs.indicator hs) (ae_of_all _ fun x => ?_)
  by_cases hx : K < |f x|
  · rw [indicator_of_mem (show x ∈ {x | K < |f x|} from hx)]
    exact max_le (by linarith [le_max_right K 0]) (abs_nonneg _)
  · rw [indicator_of_notMem (show x ∉ {x | K < |f x|} from hx)]
    exact max_le (by linarith [le_max_left K 0]) le_rfl

/-- Conversely, the hinge form gives uniform integrability. -/
theorem unifIntegrableAlong_of_integral_max_sub_le [∀ i, IsFiniteMeasure (ν i)]
    (hf : Measurable f) (hint : ∀ i, Integrable f (ν i))
    (h : ∀ ε : ℝ, 0 < ε → ∃ K, ∀ i, ∫ x, max (|f x| - K) 0 ∂ν i ≤ ε) :
    UnifIntegrableAlong f ν := by
  refine ⟨hint, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := h (ε / 2) (by positivity)
  refine ⟨2 * max K 0, fun i => ?_⟩
  have hs : MeasurableSet {x | 2 * max K 0 < |f x|} := 
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)
  rw [← integral_indicator hs]
  calc ∫ x, {x | 2 * max K 0 < |f x|}.indicator (fun x => |f x|) x ∂ν i
      ≤ ∫ x, 2 * max (|f x| - K) 0 ∂ν i := by
        refine integral_mono_of_nonneg
          (ae_of_all _ fun x => indicator_nonneg (fun _ _ => abs_nonneg _) x)
          ((((hint i).abs.sub (integrable_const K)).pos_part).const_mul 2)
          (ae_of_all _ fun x => ?_)
        by_cases hx : 2 * max K 0 < |f x|
        · rw [indicator_of_mem (show x ∈ {x | 2 * max K 0 < |f x|} from hx)]
          have := le_max_left (|f x| - K) 0
          linarith [le_max_left K 0]
        · rw [indicator_of_notMem (show x ∉ {x | 2 * max K 0 < |f x|} from hx)]
          exact mul_nonneg two_pos.le (le_max_right _ _)
    _ = 2 * ∫ x, max (|f x| - K) 0 ∂ν i := integral_const_mul _ _
    _ ≤ ε := by linarith [hK i]

end UnifIntegrableAlong

/-- If `μ i ≤cx ν i` for every `i` and `|f|` is convex, then uniform integrability of `f`
along `ν` gives uniform integrability of `f` along `μ`. -/
theorem ConvexOrder.unifIntegrableAlong {ι : Type*} {μ ν : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (h : ∀ i, ConvexOrder (μ i) (ν i)) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ConvexOn ℝ univ fun x => |f x|) (hUI : UnifIntegrableAlong f ν) :
    UnifIntegrableAlong f μ := by
  have hint : ∀ i, Integrable f (μ i) := fun i =>
    (integrable_norm_iff hfm.aestronglyMeasurable).1 (by
      simpa only [Real.norm_eq_abs] using (h i).integrable_of_integrable hf (hUI.1 i).abs)
  refine unifIntegrableAlong_of_integral_max_sub_le hfm hint fun ε hε => ?_
  obtain ⟨K, hK⟩ := hUI.exists_integral_max_sub_le hfm hε
  have hcK : ConvexOn ℝ univ fun x => max (|f x| - K) 0 :=
    (hf.sub (concaveOn_const K convex_univ)).sup (convexOn_const 0 convex_univ)
  exact ⟨K, fun i => le_trans ((h i).integral_le hcK
    ((hUI.1 i).abs.sub (integrable_const K)).pos_part) (hK K le_rfl i)⟩

/-! ### Weak limits under uniform integrability -/

section WeakLimit

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- Truncation of a real number to `[-M, M]` moves it by at most `(|a| - M)₊`. -/
theorem abs_sub_max_neg_min_le (a : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    |a - max (-M) (min a M)| ≤ max (|a| - M) 0 := by
  rcases min_cases a M with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases max_cases (-M) (min a M) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
  rcases abs_cases a with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
  rcases abs_cases (a - max (-M) (min a M)) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
  rcases max_cases (|a| - M) 0 with ⟨h5, h5'⟩ | ⟨h5, h5'⟩ <;>
  linarith

/-- Under weak convergence of probability measures, uniform integrability of a continuous `g`
along the sequence makes `g` integrable for the limit. -/
theorem integrable_of_tendsto_of_unifIntegrableAlong {μs : ℕ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ)) {g : Ω → ℝ} (hg : Continuous g)
    (hUI : UnifIntegrableAlong g fun n => (μs n : Measure Ω)) : Integrable g μ := by
  obtain ⟨K, hK⟩ := hUI.exists_integral_max_sub_le hg.measurable one_pos
  set K0 := max K 0 with hK0
  have hbd : ∀ n, ∫ x, |g x| ∂(μs n : Measure Ω) ≤ K0 + 1 := fun n => by
    have hi : Integrable (fun x => max (|g x| - K0) 0) (μs n : Measure Ω) :=
      ((hUI.1 n).abs.sub (integrable_const K0)).pos_part
    calc ∫ x, |g x| ∂(μs n : Measure Ω) ≤ ∫ x, (K0 + max (|g x| - K0) 0) ∂(μs n : Measure Ω) :=
          integral_mono (hUI.1 n).abs ((integrable_const _).add hi)
            fun x => by linarith [le_max_left (|g x| - K0) 0]
      _ = K0 + ∫ x, max (|g x| - K0) 0 ∂(μs n : Measure Ω) := by
          rw [integral_add (integrable_const _) hi]; simp
      _ ≤ K0 + 1 := by linarith [hK K0 (le_max_left _ _) n]
  have htr : ∀ M : ℕ, ∫ x, min |g x| (M : ℝ) ∂(μ : Measure Ω) ≤ K0 + 1 := fun M => by
    let T : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
      ⟨fun x => min |g x| (M : ℝ), by fun_prop⟩ M fun x y => by
        change dist (min |g x| (M : ℝ)) (min |g y| (M : ℝ)) ≤ M
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [min_le_right |g x| (M : ℝ), min_le_right |g y| (M : ℝ),
          le_min (abs_nonneg (g x)) (Nat.cast_nonneg (α := ℝ) M),
          le_min (abs_nonneg (g y)) (Nat.cast_nonneg (α := ℝ) M)]
    have hT := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ T
    change Tendsto (fun n => ∫ x, min |g x| (M : ℝ) ∂(μs n : Measure Ω)) atTop
      (𝓝 (∫ x, min |g x| (M : ℝ) ∂(μ : Measure Ω))) at hT
    exact le_of_tendsto' hT fun n =>
      (integral_mono (T.integrable _) (hUI.1 n).abs fun x => min_le_left _ _).trans (hbd n)
  have hlim : Tendsto (fun M : ℕ => ∫⁻ x, ENNReal.ofReal (min |g x| (M : ℝ)) ∂(μ : Measure Ω))
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal |g x| ∂(μ : Measure Ω))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun M => by fun_prop)
      (ae_of_all _ fun x M M' hMM' => ENNReal.ofReal_le_ofReal
        (min_le_min le_rfl (Nat.cast_le.2 hMM'))) (ae_of_all _ fun x => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|g x|⌉₊] with M hM
    rw [min_eq_left (Nat.ceil_le.1 hM)]
  have hle : ∫⁻ x, ENNReal.ofReal |g x| ∂(μ : Measure Ω) ≤ ENNReal.ofReal (K0 + 1) :=
    le_of_tendsto' hlim fun M => by
      have hi : Integrable (fun x => min |g x| (M : ℝ)) (μ : Measure Ω) :=
        (integrable_const (M : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg M))]
          exact min_le_right _ _)
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun x => le_min (abs_nonneg _) (Nat.cast_nonneg M))]
      exact ENNReal.ofReal_le_ofReal (htr M)
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- Under weak convergence of probability measures and uniform integrability of a continuous
`g`, integrals of every continuous `h` with `|h| ≤ A + B |g|` converge. -/
theorem tendsto_integral_of_unifIntegrableAlong {μs : ℕ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ)) {g h : Ω → ℝ} (hg : Continuous g)
    (hh : Continuous h) {A B : ℝ} (hhg : ∀ x, |h x| ≤ A + B * |g x|)
    (hUI : UnifIntegrableAlong g fun n => (μs n : Measure Ω)) :
    Tendsto (fun n => ∫ x, h x ∂(μs n : Measure Ω)) atTop (𝓝 (∫ x, h x ∂(μ : Measure Ω))) := by
  have hgμ : Integrable g μ := integrable_of_tendsto_of_unifIntegrableAlong hμ hg hUI
  set C := |B| + 1 with hC
  have hCpos : 0 < C := by positivity
  have hhg' : ∀ x, |h x| ≤ A + C * |g x| := fun x => by
    have := mul_nonneg (by linarith [le_abs_self B] : 0 ≤ C - B) (abs_nonneg (g x))
    nlinarith [hhg x]
  have hint : ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ], Integrable g ρ → Integrable h ρ :=
    fun ρ _ hgρ => ((integrable_const A).add (hgρ.abs.const_mul C)).mono'
      hh.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hhg' x)
  have htail : Tendsto (fun K => ∫ x, max (|g x| - K) 0 ∂(μ : Measure Ω)) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := (μ : Measure Ω))
      (l := (atTop : Filter ℝ)) (F := fun K x => max (|g x| - K) 0) (f := fun _ => (0 : ℝ))
      (fun x => |g x|) (Eventually.of_forall fun K => by fun_prop)
      (by
        filter_upwards [eventually_ge_atTop 0] with K hK
        refine ae_of_all _ fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (abs_nonneg _))
      hgμ.abs
      (ae_of_all _ fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop |g x|] with K hK
        exact (max_eq_right (by linarith)).symm)
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (3 * C) := by positivity
  obtain ⟨K0, hK0⟩ := hUI.exists_integral_max_sub_le hg.measurable hε'
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 ((tendsto_order.1 htail).2 _ hε')
  set K := max K0 K1 with hK
  set M := max (A + C * K) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  let T : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => max (-M) (min (h x) M), by fun_prop⟩ (2 * M) fun x y => by
      change dist (max (-M) (min (h x) M)) (max (-M) (min (h y) M)) ≤ 2 * M
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [le_max_left (-M) (min (h x) M), le_max_left (-M) (min (h y) M),
        max_le (by linarith : -M ≤ M) (min_le_right (h x) M),
        max_le (by linarith : -M ≤ M) (min_le_right (h y) M)]
  have hpt : ∀ x, |h x - T x| ≤ C * max (|g x| - K) 0 := fun x => by
    refine (abs_sub_max_neg_min_le (h x) hM0).trans ?_
    rw [mul_max_of_nonneg _ _ hCpos.le, mul_zero]
    exact max_le_max (by nlinarith [hhg' x, le_max_left (A + C * K) 0]) le_rfl
  have herr : ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ], Integrable g ρ →
      |∫ x, h x ∂ρ - ∫ x, T x ∂ρ| ≤ C * ∫ x, max (|g x| - K) 0 ∂ρ := fun ρ _ hgρ => by
    rw [← integral_sub (hint ρ hgρ) (T.integrable ρ), ← integral_const_mul]
    exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun x => abs_nonneg _)
      ((hgρ.abs.sub (integrable_const K)).pos_part.const_mul C) (ae_of_all _ hpt))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ T) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have e1 := herr (μs n : Measure Ω) (hUI.1 n)
  have e2 := herr (μ : Measure Ω) hgμ
  have t1 : C * ∫ x, max (|g x| - K) 0 ∂(μs n : Measure Ω) ≤ ε / 3 := by
    refine (mul_le_mul_of_nonneg_left (hK0 K (le_max_left _ _) n) hCpos.le).trans (le_of_eq ?_)
    field_simp
  have t2 : C * ∫ x, max (|g x| - K) 0 ∂(μ : Measure Ω) ≤ ε / 3 := by
    refine (mul_le_mul_of_nonneg_left (hK1 K (le_max_right _ _)).le hCpos.le).trans (le_of_eq ?_)
    field_simp
  have e3 := hN n hn
  rw [Real.dist_eq] at e3 ⊢
  rw [abs_le] at e1 e2
  rw [abs_lt] at e3 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

end WeakLimit

/-! ### Convex order of weak limits -/

theorem convexOn_abs_id : ConvexOn ℝ univ fun x : ℝ => |x| :=
  ((convexOn_id convex_univ).sup (concaveOn_id convex_univ).neg).congr fun x _ => by
    simp [abs_eq_max_neg]

theorem convexOn_abs_sq : ConvexOn ℝ univ fun x : ℝ => |x ^ 2| := by
  simpa only [abs_sq] using (even_two.convexOn_pow : ConvexOn ℝ univ fun x : ℝ => x ^ 2)

/-- **Convex order passes to weak limits.** If `μs n ≤cx νs n`, `μs n → μ`, `νs n → ν` weakly
and the first moments are uniformly integrable along `νs`, then `μ ≤cx ν`. -/
theorem ConvexOrder.of_tendsto {μs νs : ℕ → ProbabilityMeasure ℝ} {μ ν : ProbabilityMeasure ℝ}
    (hcx : ∀ n, ConvexOrder (μs n) (νs n)) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν))
    (hUI : UnifIntegrableAlong (fun x => x) fun n => (νs n : Measure ℝ)) :
    ConvexOrder μ ν := by
  have hUIμ : UnifIntegrableAlong (fun x => x) fun n => (μs n : Measure ℝ) :=
    ConvexOrder.unifIntegrableAlong hcx measurable_id' convexOn_abs_id hUI
  have hμi := integrable_of_tendsto_of_unifIntegrableAlong hμ continuous_id' hUIμ
  have hνi := integrable_of_tendsto_of_unifIntegrableAlong hν continuous_id' hUI
  have hlip : ∀ (ψ : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ univ ψ → LipschitzWith K ψ →
      ∫ x, ψ x ∂(μ : Measure ℝ) ≤ ∫ x, ψ x ∂(ν : Measure ℝ) := by
    intro ψ K hψ hK
    have hb : ∀ x, |ψ x| ≤ |ψ 0| + K * |x| := LipschitzWith.abs_le_abs_zero_add hK
    exact le_of_tendsto_of_tendsto'
      (tendsto_integral_of_unifIntegrableAlong hμ continuous_id' hK.continuous hb hUIμ)
      (tendsto_integral_of_unifIntegrableAlong hν continuous_id' hK.continuous hb hUI)
      fun n => (hcx n).integral_le hψ (integrable_comp_of_lipschitzWith (hcx n).2.1 hK)
  refine ⟨hμi, hνi, fun φ hφ hφi => ?_⟩
  exact (convex_comparison_of_lipschitzWith_comparison (X := fun x => x) (X' := fun x => x)
    measurable_id'.aemeasurable measurable_id'.aemeasurable hμi hνi hlip hφ).2.2 hφi

/-- Under the hypotheses of `ConvexOrder.of_tendsto`, the limit laws have equal means. -/
theorem ConvexOrder.integral_id_eq_of_tendsto {μs νs : ℕ → ProbabilityMeasure ℝ}
    {μ ν : ProbabilityMeasure ℝ} (hcx : ∀ n, ConvexOrder (μs n) (νs n))
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hUI : UnifIntegrableAlong (fun x => x) fun n => (νs n : Measure ℝ)) :
    ∫ x, x ∂(μ : Measure ℝ) = ∫ x, x ∂(ν : Measure ℝ) :=
  (ConvexOrder.of_tendsto hcx hμ hν hUI).integral_id_eq

/-! ### Identification of the law by second moments -/

/-- `u ↦ u² / 2 + c u` is convex when `c'' ≥ -1`. -/
theorem convexOn_sq_div_two_add {c c' c'' : ℝ → ℝ} (h1 : ∀ u, HasDerivAt c (c' u) u)
    (h2 : ∀ u, HasDerivAt c' (c'' u) u) (h3 : ∀ u, -1 ≤ c'' u) :
    ConvexOn ℝ univ fun u => u ^ 2 / 2 + c u := by
  have hd : ∀ u, HasDerivAt (fun u => u ^ 2 / 2 + c u) (u + c' u) u := fun u => by
    have := ((hasDerivAt_pow 2 u).div_const 2).add (h1 u)
    convert this using 1
    simp
  have hd' : deriv (fun u => u ^ 2 / 2 + c u) = fun u => u + c' u :=
    funext fun u => (hd u).deriv
  have hd2 : ∀ u, HasDerivAt (fun u => u + c' u) (1 + c'' u) u := fun u =>
    (hasDerivAt_id u).add (h2 u)
  refine convexOn_univ_of_deriv2_nonneg (fun u => (hd u).differentiableAt) ?_ fun u => ?_
  · rw [hd']; exact fun u => (hd2 u).differentiableAt
  · change 0 ≤ deriv (deriv fun u => u ^ 2 / 2 + c u) u
    rw [hd', (hd2 u).deriv]
    linarith [h3 u]

/-- `x ↦ (t x)² / 2 + c (t x)` is convex when `c'' ≥ -1`. -/
theorem convexOn_mul_sq_div_two_add {c c' c'' : ℝ → ℝ} (h1 : ∀ u, HasDerivAt c (c' u) u)
    (h2 : ∀ u, HasDerivAt c' (c'' u) u) (h3 : ∀ u, -1 ≤ c'' u) (t : ℝ) :
    ConvexOn ℝ univ fun x => (t * x) ^ 2 / 2 + c (t * x) := by
  have := (convexOn_sq_div_two_add h1 h2 h3).comp_linearMap (t • LinearMap.id)
  simpa [Function.comp_def] using this

/-- If `μ ≤cx ν`, and `q ± ψ` are convex with `q, ψ` integrable for both laws and `q` of equal
integrals, then `ψ` has equal integrals. -/
theorem ConvexOrder.integral_eq_of_convexOn_add_sub {μ ν : Measure ℝ} (h : ConvexOrder μ ν)
    {q ψ : ℝ → ℝ} (hqμ : Integrable q μ) (hqν : Integrable q ν) (hq : ∫ x, q x ∂μ = ∫ x, q x ∂ν)
    (hψμ : Integrable ψ μ) (hψν : Integrable ψ ν) (h1 : ConvexOn ℝ univ fun x => q x + ψ x)
    (h2 : ConvexOn ℝ univ fun x => q x - ψ x) : ∫ x, ψ x ∂μ = ∫ x, ψ x ∂ν := by
  have a := h.integral_le h1 (hqν.add hψν)
  have b := h.integral_le h2 (hqν.sub hψν)
  rw [integral_add hqμ hψμ, integral_add hqν hψν] at a
  rw [integral_sub hqμ hψμ, integral_sub hqν hψν] at b
  linarith

/-- **Convex order with equal second moments forces equal laws.** -/
theorem ConvexOrder.eq_of_integral_sq_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ConvexOrder μ ν) (h2 : Integrable (fun x => x ^ 2) ν)
    (heq : ∫ x, x ^ 2 ∂μ = ∫ x, x ^ 2 ∂ν) : μ = ν := by
  have h2μ : Integrable (fun x => x ^ 2) μ :=
    h.integrable_of_integrable (even_two.convexOn_pow) h2
  have hbdd : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (ψ : ℝ → ℝ), Continuous ψ →
      (∀ x, |ψ x| ≤ 1) → Integrable ψ ρ := fun ρ _ ψ hψ hb =>
    (integrable_const (1 : ℝ)).mono' hψ.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have key : ∀ (t : ℝ) (ψ c' c'' d' d'' : ℝ → ℝ), Continuous ψ → (∀ x, |ψ x| ≤ 1) →
      (∀ u, HasDerivAt ψ (c' u) u) → (∀ u, HasDerivAt c' (c'' u) u) → (∀ u, -1 ≤ c'' u) →
      (∀ u, HasDerivAt (fun u => -ψ u) (d' u) u) → (∀ u, HasDerivAt d' (d'' u) u) →
      (∀ u, -1 ≤ d'' u) →
      ∫ x, ψ (t * x) ∂μ = ∫ x, ψ (t * x) ∂ν := by
    intro t ψ c' c'' d' d'' hψ hb h1 h2' h3 g1 g2 g3
    have hq : ∀ ρ : Measure ℝ, Integrable (fun x => x ^ 2) ρ →
        Integrable (fun x => (t * x) ^ 2 / 2) ρ := fun ρ hρ =>
      (hρ.const_mul (t ^ 2 / 2)).congr (ae_of_all _ fun x => by ring)
    have hqe : ∀ ρ : Measure ℝ, ∫ x, (t * x) ^ 2 / 2 ∂ρ = t ^ 2 / 2 * ∫ x, x ^ 2 ∂ρ := fun ρ => by
      rw [← integral_const_mul]; congr 1; funext x; ring
    refine h.integral_eq_of_convexOn_add_sub (hq μ h2μ) (hq ν h2) (by rw [hqe, hqe, heq])
      (hbdd μ _ (by fun_prop) fun x => hb _) (hbdd ν _ (by fun_prop) fun x => hb _)
      (convexOn_mul_sq_div_two_add h1 h2' h3 t) ?_
    simpa only [sub_eq_add_neg] using convexOn_mul_sq_div_two_add g1 g2 g3 t
  have hcos : ∀ t, ∫ x, Real.cos (t * x) ∂μ = ∫ x, Real.cos (t * x) ∂ν := fun t =>
    key t Real.cos (fun u => -Real.sin u) (fun u => -Real.cos u) Real.sin Real.cos
      Real.continuous_cos (fun x => Real.abs_cos_le_one x) Real.hasDerivAt_cos
      (fun u => (Real.hasDerivAt_sin u).neg) (fun u => by linarith [Real.cos_le_one u])
      (fun u => by convert (Real.hasDerivAt_cos u).neg using 1; simp) Real.hasDerivAt_sin
      (fun u => Real.neg_one_le_cos u)
  have hsin : ∀ t, ∫ x, Real.sin (t * x) ∂μ = ∫ x, Real.sin (t * x) ∂ν := fun t =>
    key t Real.sin Real.cos (fun u => -Real.sin u) (fun u => -Real.cos u) Real.sin
      Real.continuous_sin (fun x => Real.abs_sin_le_one x) Real.hasDerivAt_sin
      Real.hasDerivAt_cos (fun u => by linarith [Real.sin_le_one u])
      (fun u => (Real.hasDerivAt_sin u).neg)
      (fun u => by convert (Real.hasDerivAt_cos u).neg using 1; simp)
      (fun u => Real.neg_one_le_sin u)
  have hexp : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (t : ℝ),
      ∫ x, Complex.exp (↑t * ↑x * Complex.I) ∂ρ =
        ↑(∫ x, Real.cos (t * x) ∂ρ) + ↑(∫ x, Real.sin (t * x) ∂ρ) * Complex.I := by
    intro ρ _ t
    have hc := hbdd ρ (fun x => Real.cos (t * x)) (by fun_prop) fun x => Real.abs_cos_le_one _
    have hs := hbdd ρ (fun x => Real.sin (t * x)) (by fun_prop) fun x => Real.abs_sin_le_one _
    have he : ∀ x : ℝ, Complex.exp (↑t * ↑x * Complex.I) =
        ↑(Real.cos (t * x)) + ↑(Real.sin (t * x)) * Complex.I := fun x => by
      rw [← Complex.ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp_rw [he]
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply_real, charFun_apply_real, hexp μ t, hexp ν t, hcos t, hsin t]

/-- **Identification of the limit law.** Under the hypotheses of `ConvexOrder.of_tendsto`, if
moreover the squares are uniformly integrable along `νs` and the second-moment gap
`∫ x² dνs n - ∫ x² dμs n` tends to zero, then the squares are uniformly integrable along `μs`
and the limit laws coincide. -/
theorem ConvexOrder.eq_of_tendsto_of_tendsto_sub {μs νs : ℕ → ProbabilityMeasure ℝ}
    {μ ν : ProbabilityMeasure ℝ} (hcx : ∀ n, ConvexOrder (μs n) (νs n))
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hUI : UnifIntegrableAlong (fun x => x) fun n => (νs n : Measure ℝ))
    (hUI2 : UnifIntegrableAlong (fun x => x ^ 2) fun n => (νs n : Measure ℝ))
    (hgap : Tendsto (fun n => ∫ x, x ^ 2 ∂(νs n : Measure ℝ) - ∫ x, x ^ 2 ∂(μs n : Measure ℝ))
      atTop (𝓝 0)) :
    UnifIntegrableAlong (fun x => x ^ 2) (fun n => (μs n : Measure ℝ)) ∧ μ = ν := by
  have hUI2μ : UnifIntegrableAlong (fun x => x ^ 2) fun n => (μs n : Measure ℝ) :=
    ConvexOrder.unifIntegrableAlong hcx (by fun_prop) convexOn_abs_sq hUI2
  refine ⟨hUI2μ, ?_⟩
  have hc : Continuous fun x : ℝ => x ^ 2 := by fun_prop
  have hb : ∀ x : ℝ, |x ^ 2| ≤ 0 + 1 * |x ^ 2| := fun x => by simp
  have tμ := tendsto_integral_of_unifIntegrableAlong hμ hc hc hb hUI2μ
  have tν := tendsto_integral_of_unifIntegrableAlong hν hc hc hb hUI2
  have heq : ∫ x, x ^ 2 ∂(μ : Measure ℝ) = ∫ x, x ^ 2 ∂(ν : Measure ℝ) := by
    have := tendsto_nhds_unique (tν.sub tμ) hgap
    linarith
  exact ProbabilityMeasure.toMeasure_injective
    ((ConvexOrder.of_tendsto hcx hμ hν hUI).eq_of_integral_sq_eq
      (integrable_of_tendsto_of_unifIntegrableAlong hν hc hUI2) heq)

end PercLib.Probability
