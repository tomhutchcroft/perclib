/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Discharge of the premise `hunif` that the formalisation of contributor yujinhkim cited below adds to
Lemma I.4.1 of T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1. The argument
is read from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files `PercLib/CriticalLRP/RussoInf/DominatedFlux.lean`,
`PercLib/CriticalLRP/RussoInf/Exchange.lean`, `PercLib/CriticalLRP/RussoInf/FluxMain.lean`,
`PercLib/CriticalLRP/RussoInf/CutoffFlux.lean` and `PercLib/CriticalLRP/RussoInf/Capstone.lean`;
licence Apache-2.0 as declared in those file headers and `third_party/critical-lrp/NOTICE.md`;
upstream `yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`
(not independently verified). Contributor: yujinhkim. No code is copied: the fork's definitions
(`cutConfig`, `cutFun`, `cappedClusterVol`, `pivotalFlux`, `cutoffEdgeDeriv`) are written out as
expressions on the bond interface, and the proofs are new, from the finite Russo formula
of this library and the dominated limit-of-derivatives theorem of
`PercLib/Analysis/DominatedDerivative.lean`.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Models.LongRange.SoftCutoff
public import PercLib.Models.TranslationInvariant
public import PercLib.Percolation.Bond.ClusterTails
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.ZeroOne
public import PercLib.Probability.Coordinate
public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.ProductExpectation
public import PercLib.Probability.Russo
public import PercLib.Probability.Superposition
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Infinite-volume Russo formula from a dominator (part 1: the window argument)

Let `V` be countable, `o : V`, and `F : ℕ∞ → ℝ` bounded by `m` and constant from some
`n₀` on (for instance `F n = min ((min n n')^p) m'`, the fork's `cappedClusterVol`). For a
family of profiles `p r` write `ψ(r) = ∫ F |K_o| d(law (p r))` and, for a pair `e`,
`Δ_e(r) = ∫ (F |K_o(ω ∪ {e})| - F |K_o(ω \ {e})|) d(law (p r))`.

* `window_tendsto`: for every increasing exhaustion `S_k` of the pairs, the window
  functional `F |K_o(ω ∩ S_k)|` is eventually equal to `F |K_o(ω)|`;
* `hasDerivAt_integral_window`: the finite-window Russo formula;
* `abs_integral_pivotal_le`: `|Δ_e| ≤ 2 m P(e touches K_o)`, also for every window;
* `integral_sub_eq_integral_flux` (the integrated form of item 3): if
  `r ↦ p r e` is continuous and differentiable with derivative `c r e` off a countable set
  of `r` for each `e`, and `∑_{e ∈ S} |c r e| P_r(e touches K_o) ≤ M` for every finite `S`
  (the dominator), then `ψ t - ψ s = ∫_s^t ∑' e, c r e Δ_e(r) dr`, and the flux is bounded
  by `2 m M`. No locally uniform convergence (`hunif`) is assumed.

For the cut-off family on `ℤ^d` (a norm `N` on `ℝ^d`, `K` decreasing with continuous
derivative `K'` on `(0, ∞)`, finite `E_{μ_R}|K_o|`):

* `cutoff_dominator` (item 1) and `integral_sub_eq_integral_flux_cutoff` (item 3, integrated);
* `continuousOn_flux_cutoff` (item 2): the flux is continuous on every interval free of the
  values `N (Int.cast ∘ z)`;
* `hasDerivAt_integral_cutoff` (item 3): `ψ` is differentiable with derivative the infinite
  pivotal flux at every `r₀ ∈ (0, R)` that is not a value `N (Int.cast ∘ z)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal unitInterval
open PercLib.Percolation.Bond PercLib.Probability

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {V : Type*}

/-! ### Clusters and windows -/

/-- Opening a pair with no endpoint in the cluster of `o` does not change that cluster. -/
theorem cluster_insert_eq_of_forall_not_mem {ω : Config V} {o : V} {e : Sym2 V}
    (he : ∀ x ∈ e, x ∉ cluster ω o) : cluster (insert e ω) o = cluster ω o := by
  refine Subset.antisymm ?_ (cluster_mono (subset_insert e ω) o)
  intro y hy
  change (openGraph (insert e ω)).Reachable o y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact mem_cluster_self ω o
  | @tail z w _ hadj ih =>
    rw [openGraph_adj_iff, mem_insert_iff] at hadj
    obtain ⟨hzw | hzw, hne⟩ := hadj
    · exact absurd ih (he z (hzw ▸ Sym2.mem_mk_left z w))
    · exact (show (openGraph ω).Reachable o z from ih).trans
        (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω z w).2 ⟨hzw, hne⟩))

/-- In any window `S`, opening or closing a pair with no endpoint in the cluster of `o`
leaves the window cluster unchanged. -/
theorem cluster_insert_inter_eq {ω : Config V} {o : V} {e : Sym2 V} (S : Set (Sym2 V))
    (he : ∀ x ∈ e, x ∉ cluster ω o) :
    cluster (insert e ω ∩ S) o = cluster ((ω \ {e}) ∩ S) o := by
  by_cases heS : e ∈ S
  · have h : insert e ω ∩ S = insert e ((ω \ {e}) ∩ S) := by
      ext f
      by_cases hf : f = e
      · subst hf; simp [heS]
      · simp [hf]
    rw [h]
    exact cluster_insert_eq_of_forall_not_mem fun x hx hx' =>
      he x hx (cluster_mono (inter_subset_left.trans sdiff_subset) o hx')
  · have h : insert e ω ∩ S = (ω \ {e}) ∩ S := by
      ext f
      by_cases hf : f = e
      · subst hf; simp [heS]
      · simp [hf]
    rw [h]

/-- The event that the pair `e` touches the cluster of `o`. -/
theorem measurableSet_touch [Countable V] (o : V) (e : Sym2 V) :
    MeasurableSet {ω : Config V | ∃ x ∈ e, x ∈ cluster ω o} := by
  induction e using Sym2.ind with
  | _ a b =>
    have h : {ω : Config V | ∃ x ∈ s(a, b), x ∈ cluster ω o} = conn o a ∪ conn o b := by
      ext ω
      simp only [Sym2.mem_iff, mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨x, rfl | rfl, hx⟩
        · exact Or.inl hx
        · exact Or.inr hx
      · rintro (h | h)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨b, Or.inr rfl, h⟩
    rw [h]
    exact (measurableSet_conn o a).union (measurableSet_conn o b)

theorem measurable_inter_const (S : Set (Sym2 V)) :
    Measurable fun ω : Config V => ω ∩ S :=
  Measurable.of_mem fun f => by
    by_cases hf : f ∈ S
    · simpa [hf] using measurable_set_mem f
    · simp [hf]

/-- Every window functional is measurable. -/
theorem measurable_window [Countable V] (F : ℕ∞ → ℝ) (o : V) (S : Set (Sym2 V)) :
    Measurable fun ω : Config V => F (cluster (ω ∩ S) o).encard :=
  (measurable_of_countable F).comp ((measurable_encard_cluster o).comp (measurable_inter_const S))

/-- A pivotal difference of a window functional is bounded by `2 m` on the event that the
pair touches the full cluster of `o`, and vanishes off it. -/
theorem abs_window_pivotal_le {F : ℕ∞ → ℝ} {m : ℝ} (hF : ∀ n, |F n| ≤ m) (o : V)
    (S : Set (Sym2 V)) (e : Sym2 V) (ω : Config V) :
    |F (cluster (insert e ω ∩ S) o).encard - F (cluster ((ω \ {e}) ∩ S) o).encard| ≤
      {ω : Config V | ∃ x ∈ e, x ∈ cluster ω o}.indicator (fun _ => 2 * m) ω := by
  by_cases h : ∃ x ∈ e, x ∈ cluster ω o
  · rw [indicator_of_mem (show ω ∈ {ω : Config V | ∃ x ∈ e, x ∈ cluster ω o} from h)]
    refine (abs_sub _ _).trans ?_
    linarith [hF (cluster (insert e ω ∩ S) o).encard, hF (cluster ((ω \ {e}) ∩ S) o).encard]
  · rw [indicator_of_notMem (show ω ∉ {ω : Config V | ∃ x ∈ e, x ∈ cluster ω o} from h),
      cluster_insert_inter_eq S (by simpa using h), sub_self, abs_zero]

/-- **The pivotal bound.** `|∫ Δ_e| ≤ 2 m P(e touches K_o)` in every window. -/
theorem abs_integral_pivotal_le [Countable V] {F : ℕ∞ → ℝ} {m : ℝ} (hF : ∀ n, |F n| ≤ m)
    (o : V) (S : Set (Sym2 V)) (e : Sym2 V) (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    |∫ ω, (F (cluster (insert e ω ∩ S) o).encard - F (cluster ((ω \ {e}) ∩ S) o).encard) ∂μ| ≤
      2 * m * μ.real {ω : Config V | ∃ x ∈ e, x ∈ cluster ω o} := by
  have hA := measurableSet_touch o e
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_const (2 * m)).indicator hA)
    (Eventually.of_forall fun ω => abs_window_pivotal_le hF o S e ω)).trans_eq ?_
  rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]

/-! ### Windows converge -/

/-- **Window convergence.** Along an increasing exhaustion, the window functional is
eventually equal to the full functional, provided `F` is constant from some `n₀` on. -/
theorem window_eventually_eq {F : ℕ∞ → ℝ} (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤)
    (o : V) {S : ℕ → Finset (Sym2 V)} (hSm : Monotone S) (hS : ∀ e, ∃ k, e ∈ S k)
    (ω : Config V) :
    ∀ᶠ k in atTop, F (cluster (ω ∩ S k) o).encard = F (cluster ω o).encard := by
  classical
  obtain ⟨n₀, hn₀⟩ := hF
  -- a finite part `T` of the cluster that determines the value of `F`
  obtain ⟨T, hTC, hT⟩ : ∃ T : Finset V, (T : Set V) ⊆ cluster ω o ∧
      (∀ C : Set V, (T : Set V) ⊆ C → C ⊆ cluster ω o → F C.encard = F (cluster ω o).encard) := by
    by_cases hfin : (cluster ω o).Finite
    · refine ⟨hfin.toFinset, by simp, fun C hTC hC => ?_⟩
      rw [Subset.antisymm hC (by simpa using hTC)]
    · have hinf : (cluster ω o).Infinite := hfin
      obtain ⟨T, hT, hcard⟩ := hinf.exists_subset_card_eq n₀
      refine ⟨T, hT, fun C hTC _ => ?_⟩
      rw [hinf.encard_eq, hn₀ _ (by
        rw [← hcard, ← Set.encard_coe_eq_coe_finsetCard]
        exact Set.encard_le_encard hTC)]
  obtain ⟨E₀, hE₀ω, hE₀⟩ := exists_finset_of_forall_conn o T fun x hx => hTC hx
  have hev : ∀ᶠ k in atTop, ∀ f ∈ E₀, f ∈ S k := by
    rw [eventually_all_finset]
    intro f _
    obtain ⟨k, hk⟩ := hS f
    exact eventually_atTop.2 ⟨k, fun k' hk' => hSm hk' hk⟩
  filter_upwards [hev] with k hk
  refine hT _ (fun x hx => ?_) (cluster_mono inter_subset_left o)
  have hsub : ((E₀ : Set (Sym2 V)) : Config V) ⊆ ω ∩ (S k : Set (Sym2 V)) :=
    fun f hf => ⟨hE₀ω hf, hk f hf⟩
  exact conn_mono hsub (hE₀ x hx)

/-- Window integrals of a transformed configuration converge. -/
theorem tendsto_integral_window [Countable V] {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : V) {S : ℕ → Finset (Sym2 V)}
    (hSm : Monotone S) (hS : ∀ e, ∃ k, e ∈ S k) (T : Config V → Config V) (hT : Measurable T)
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    Tendsto (fun k => ∫ ω, F (cluster (T ω ∩ S k) o).encard ∂μ) atTop
      (𝓝 (∫ ω, F (cluster (T ω) o).encard ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => m) (fun k => ?_)
    (integrable_const m) (fun k => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => ?_)
  · exact ((measurable_window F o (S k : Set (Sym2 V))).comp hT).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hFm _
  · exact tendsto_const_nhds.congr' ((window_eventually_eq hF o hSm hS (T ω)).mono
      fun k hk => hk.symm)

/-- Window pivotal differences converge. -/
theorem tendsto_integral_window_pivotal [Countable V] {F : ℕ∞ → ℝ} {m : ℝ}
    (hFm : ∀ n, |F n| ≤ m) (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : V)
    {S : ℕ → Finset (Sym2 V)} (hSm : Monotone S) (hS : ∀ e, ∃ k, e ∈ S k) (e : Sym2 V)
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    Tendsto (fun k => ∫ ω, (F (cluster (insert e ω ∩ S k) o).encard -
        F (cluster ((ω \ {e}) ∩ S k) o).encard) ∂μ) atTop
      (𝓝 (∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard) ∂μ)) := by
  have hint : ∀ (T : Config V → Config V), Measurable T → ∀ W : Set (Sym2 V),
      Integrable (fun ω => F (cluster (T ω ∩ W) o).encard) μ := fun T hT W =>
    Integrable.of_bound (C := m) ((measurable_window F o W).comp hT).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFm _)
  have hint' : ∀ (T : Config V → Config V), Measurable T →
      Integrable (fun ω => F (cluster (T ω) o).encard) μ := fun T hT => by
    simpa using hint T hT univ
  have hi := measurable_insert (ι := Sym2 V) e
  have hd := measurable_diff_singleton (ι := Sym2 V) e
  simp_rw [fun k => integral_sub (hint _ hi (S k : Set (Sym2 V))) (hint _ hd (S k : Set (Sym2 V))),
    integral_sub (hint' _ hi) (hint' _ hd)]
  exact (tendsto_integral_window hFm hF o hSm hS _ hi μ).sub
    (tendsto_integral_window hFm hF o hSm hS _ hd μ)

/-! ### The finite-window Russo formula -/

/-- The window integral of a transformed configuration is an integral against the restricted
product law. -/
theorem integral_window_eq_restrict (S : Finset (Sym2 V)) (h : Set S → ℝ)
    (q : Sym2 V → unitInterval) :
    ∫ ω, h (Subtype.val ⁻¹' ω : Set S) ∂(law q) =
      ∫ η, h η ∂(prodBernoulli fun i : S => q i) := by
  have hm : Measurable (fun ω : Set (Sym2 V) => (Subtype.val ⁻¹' ω : Set S)) :=
    Measurable.of_mem fun i => measurable_set_mem (i : Sym2 V)
  rw [← prodBernoulli_map_restrict, integral_map hm.aemeasurable
    (measurable_of_finite h).aestronglyMeasurable]
  rfl

theorem image_val_preimage_val (S : Finset (Sym2 V)) (ω : Config V) :
    (Subtype.val '' (Subtype.val ⁻¹' ω : Set S) : Config V) = ω ∩ S := by
  ext f
  simp only [mem_image, mem_preimage, mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hg, g.2⟩
  · rintro ⟨hf, hfS⟩
    exact ⟨⟨f, hfS⟩, hf, rfl⟩

theorem image_val_insert_preimage_val (S : Finset (Sym2 V)) (e : S) (ω : Config V) :
    (Subtype.val '' insert e (Subtype.val ⁻¹' ω : Set S) : Config V) =
        insert (e : Sym2 V) ω ∩ S := by
  rw [image_insert_eq, image_val_preimage_val]
  ext f
  by_cases hf : f = e
  · subst hf; simp
  · simp [hf]

theorem image_val_diff_preimage_val (S : Finset (Sym2 V)) (e : S) (ω : Config V) :
    (Subtype.val '' ((Subtype.val ⁻¹' ω : Set S) \ {e}) : Config V) = (ω \ {(e : Sym2 V)}) ∩ S := by
  rw [image_sdiff Subtype.val_injective, image_singleton, image_val_preimage_val]
  ext f
  simp only [Set.mem_sdiff, mem_inter_iff, mem_singleton_iff]
  tauto

/-- **The finite-window Russo formula.** If every pair of the finite window `S` has a
differentiable probability at `r₀`, the window functional is differentiable at `r₀` with
derivative the window pivotal flux. -/
theorem hasDerivAt_integral_window (F : ℕ∞ → ℝ) (o : V) (S : Finset (Sym2 V))
    (p : ℝ → Sym2 V → unitInterval) (c : Sym2 V → ℝ) (r₀ : ℝ)
    (hp : ∀ e ∈ S, HasDerivAt (fun r => (p r e : ℝ)) (c e) r₀) :
    HasDerivAt (fun r => ∫ ω, F (cluster (ω ∩ S) o).encard ∂(law (p r)))
      (∑ e ∈ S, c e * ∫ ω, (F (cluster (insert e ω ∩ S) o).encard -
        F (cluster ((ω \ {e}) ∩ S) o).encard) ∂(law (p r₀))) r₀ := by
  classical
  set f : Set S → ℝ := fun η => F (cluster (Subtype.val '' η) o).encard
  have h := FiniteProfile.integral_hasDerivWithinAt (E := S) (fun e r => (p r e : ℝ))
    (fun e => c e) r₀ (fun e => hp e e.2) (fun r (e : S) => p r e) univ (fun _ => rfl)
    (fun _ _ _ => rfl) f
  rw [hasDerivWithinAt_univ] at h
  have hfun : (fun r => ∫ ω, F (cluster (ω ∩ S) o).encard ∂(law (p r))) =
      fun r => ∫ η, f η ∂(prodBernoulli fun e : S => p r e) := by
    funext r
    rw [← integral_window_eq_restrict]
    simp only [f, image_val_preimage_val]
  have hder : (∑ e ∈ S, c e * ∫ ω, (F (cluster (insert e ω ∩ S) o).encard -
        F (cluster ((ω \ {e}) ∩ S) o).encard) ∂(law (p r₀))) =
      ∑ e : S, c e * ∫ η, (f (insert e η) - f (η \ {e})) ∂(prodBernoulli fun e : S => p r₀ e) := by
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← integral_window_eq_restrict S (fun η : Set S => f (insert e η) - f (η \ {e}))]
    simp only [f, image_val_insert_preimage_val, image_val_diff_preimage_val]
  rw [hfun, hder]
  exact h

/-- The window functional is continuous wherever the probabilities of the window are. -/
theorem continuousOn_integral_window (F : ℕ∞ → ℝ) (o : V) (S : Finset (Sym2 V))
    (p : ℝ → Sym2 V → unitInterval) {U : Set ℝ}
    (hp : ∀ e ∈ S, ContinuousOn (fun r => (p r e : ℝ)) U) :
    ContinuousOn (fun r => ∫ ω, F (cluster (ω ∩ S) o).encard ∂(law (p r))) U := by
  classical
  have hfun : (fun r => ∫ ω, F (cluster (ω ∩ S) o).encard ∂(law (p r))) =
      fun r => ∑ η : Set S, F (cluster (Subtype.val '' η) o).encard *
        ∏ i : S, if i ∈ η then (p r i : ℝ) else 1 - (p r i : ℝ) := by
    funext r
    rw [← integral_prodBernoulli, ← integral_window_eq_restrict S
      (fun η : Set S => F (cluster (Subtype.val '' η) o).encard)]
    simp only [image_val_preimage_val]
  rw [hfun]
  refine continuousOn_finsetSum _ fun η _ => continuousOn_const.mul ?_
  refine continuousOn_finsetProd _ fun i _ => ?_
  by_cases hi : i ∈ η
  · simpa only [hi, ite_true] using hp i i.2
  · simp only [hi, ite_false]
    exact continuousOn_const.sub (hp i i.2)

/-! ### The integrated infinite-volume Russo formula -/

/-- **Integrated infinite-volume Russo formula (item 3, integrated form).**

Let `r ↦ p r e` be continuous on `(u, v)` and differentiable with derivative `c r e` off a
countable set `C e`, for every pair `e`, and let the dominator
`∑_{e ∈ S} |c r e| P_r(e touches K_o) ≤ M` hold for every finite `S` and `r ∈ (u, v)`.
Then for `u < s ≤ t < v`,
`ψ t - ψ s = ∫_s^t ∑' e, c r e ∫ (F |K_o(ω ∪ {e})| - F |K_o(ω \ {e})|) d(law (p r)) dr`. -/
theorem integral_sub_eq_integral_flux [Countable V] {F : ℕ∞ → ℝ} {m : ℝ}
    (hFm : ∀ n, |F n| ≤ m) (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : V)
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {u v : ℝ} (C : Sym2 V → Set ℝ)
    (hC : ∀ e, (C e).Countable) (hcont : ∀ e, ContinuousOn (fun r => (p r e : ℝ)) (Ioo u v))
    (hderiv : ∀ e, ∀ r ∈ Ioo u v, r ∉ C e → HasDerivAt (fun r => (p r e : ℝ)) (c r e) r)
    {M : ℝ} (hdom : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ M)
    {s t : ℝ} (hus : u < s) (hst : s ≤ t) (htv : t < v) :
    ∫ ω, F (cluster ω o).encard ∂(law (p t)) - ∫ ω, F (cluster ω o).encard ∂(law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω, (F (cluster (insert e ω) o).encard -
        F (cluster (ω \ {e}) o).encard) ∂(law (p r)) := by
  classical
  obtain ⟨S, hSm, hS⟩ := exists_finset_exhaustion (V := Sym2 V)
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hFm 0)
  set B : Set ℝ := ⋃ e, C e
  have hB : B.Countable := countable_iUnion hC
  set ψk : ℕ → ℝ → ℝ := fun k r => ∫ ω, F (cluster (ω ∩ S k) o).encard ∂(law (p r))
  set Φk : ℕ → ℝ → ℝ := fun k r => ∑ e ∈ S k, c r e * ∫ ω,
    (F (cluster (insert e ω ∩ S k) o).encard - F (cluster ((ω \ {e}) ∩ S k) o).encard)
      ∂(law (p r))
  set Φ : ℝ → ℝ := fun r => ∑' e, c r e * ∫ ω, (F (cluster (insert e ω) o).encard -
    F (cluster (ω \ {e}) o).encard) ∂(law (p r))
  have hIcc : Icc s t ⊆ Ioo u v := Icc_subset_Ioo hus htv
  -- step 1: window derivatives off the bad set
  have h1 : ∀ k, ∀ r ∈ Ioo u v, r ∉ B → HasDerivAt (ψk k) (Φk k r) r := fun k r hr hrB =>
    hasDerivAt_integral_window F o (S k) p (c r) r fun e _ =>
      hderiv e r hr fun h => hrB (mem_iUnion.2 ⟨e, h⟩)
  -- step 2: the window fluxes are bounded by `2 m M`
  have h2 : ∀ k, ∀ r ∈ Ioo u v, |Φk k r| ≤ 2 * m * M := by
    intro k r hr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ S k, |c r e * ∫ ω, (F (cluster (insert e ω ∩ S k) o).encard -
          F (cluster ((ω \ {e}) ∩ S k) o).encard) ∂(law (p r))|
        ≤ ∑ e ∈ S k, |c r e| *
            (2 * m * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o}) := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_integral_pivotal_le hFm o _ e _) (abs_nonneg _)
      _ = 2 * m * ∑ e ∈ S k, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ 2 * m * M := mul_le_mul_of_nonneg_left (hdom r hr (S k)) (by positivity)
  -- step 3: the window fluxes converge to the infinite flux off the bad set
  have h3 : ∀ r ∈ Ioo u v, Tendsto (fun k => Φk k r) atTop (𝓝 (Φ r)) := by
    intro r hr
    have hsum : Summable fun e => |c r e| *
        (2 * m * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o}) := by
      refine summable_of_sum_le (c := 2 * m * M) (fun e => by positivity) fun T => ?_
      calc ∑ e ∈ T, |c r e| * (2 * m * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o})
          = 2 * m * ∑ e ∈ T, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ ≤ 2 * m * M := mul_le_mul_of_nonneg_left (hdom r hr T) (by positivity)
    have heq : ∀ k, Φk k r = ∑' e, (if e ∈ S k then c r e * ∫ ω,
        (F (cluster (insert e ω ∩ S k) o).encard - F (cluster ((ω \ {e}) ∩ S k) o).encard)
          ∂(law (p r)) else 0) := fun k => by
      rw [tsum_eq_sum (s := S k) fun e he => ite_eq_right_iff.2 fun h => absurd h he]
      exact Finset.sum_congr rfl fun e he => (ite_eq_left_iff.2 fun h => absurd he h).symm
    simp_rw [heq]
    refine tendsto_tsum_of_dominated_convergence hsum (fun e => ?_) (Eventually.of_forall
      fun k e => ?_)
    · obtain ⟨k₀, hk₀⟩ := hS e
      refine Tendsto.congr' (eventually_atTop.2 ⟨k₀,
          fun k hk => (ite_eq_left_iff.2 fun h => absurd (hSm hk hk₀) h).symm⟩) ?_
      exact (tendsto_integral_window_pivotal hFm hF o hSm hS e _).const_mul _
    · split_ifs
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_integral_pivotal_le hFm o _ e _) (abs_nonneg _)
      · rw [norm_zero]
        positivity
  -- step 4: the window identities
  have hBnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ B :=
      measure_eq_zero_iff_ae_notMem.1 (hB.measure_zero volume)
  have h4 : ∀ k, ψk k t - ψk k s = ∫ r in s..t, deriv (ψk k) r := by
    intro k
    refine (integral_eq_of_hasDerivAt_off_countable_of_le (ψk k) (deriv (ψk k)) hst hB
      ((continuousOn_integral_window F o (S k) p fun e _ => hcont e).mono hIcc)
      (fun x hx => (h1 k x (Ioo_subset_Ioo hus.le htv.le ⟨hx.1.1, hx.1.2⟩) hx.2).deriv ▸
        h1 k x (Ioo_subset_Ioo hus.le htv.le ⟨hx.1.1, hx.1.2⟩) hx.2) ?_).symm
    refine (intervalIntegrable_const (c := 2 * m * M)).mono_fun'
      (measurable_deriv _).aestronglyMeasurable ?_
    rw [uIoc_of_le hst]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hBnull] with x hx hxB
    have hxI : x ∈ Ioo u v := hIcc (Ioc_subset_Icc_self hx)
    rw [(h1 k x hxI hxB).deriv, Real.norm_eq_abs]
    exact h2 k x hxI
  -- step 5: dominated convergence of the integrals of the window fluxes
  have h5 : Tendsto (fun k => ∫ r in s..t, deriv (ψk k) r) atTop (𝓝 (∫ r in s..t, Φ r)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * m * M)
      (Eventually.of_forall fun k => (measurable_deriv _).aestronglyMeasurable) ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun k => ?_
      filter_upwards [hBnull] with x hxB hx
      rw [uIoc_of_le hst] at hx
      have hxI : x ∈ Ioo u v := hIcc (Ioc_subset_Icc_self hx)
      rw [(h1 k x hxI hxB).deriv, Real.norm_eq_abs]
      exact h2 k x hxI
    · filter_upwards [hBnull] with x hxB hx
      rw [uIoc_of_le hst] at hx
      have hxI : x ∈ Ioo u v := hIcc (Ioc_subset_Icc_self hx)
      simp_rw [fun k => (h1 k x hxI hxB).deriv]
      exact h3 x hxI
  -- step 6: the window functionals converge
  have h6 : Tendsto (fun k => ψk k t - ψk k s) atTop
      (𝓝 (∫ ω, F (cluster ω o).encard ∂(law (p t)) - ∫ ω, F (cluster ω o).encard ∂(law (p s)))) :=
    (tendsto_integral_window hFm hF o hSm hS id measurable_id _).sub
      (tendsto_integral_window hFm hF o hSm hS id measurable_id _)
  exact tendsto_nhds_unique h6 (h5.congr fun k => (h4 k).symm)

/-! ### The cut-off family

For a norm `N` on `ℝ^d` (evaluated on `ℤ^d`), a profile `K ≥ 0`, decreasing and differentiable
on `(0, ∞)` with derivative `K'`, and an intensity `β`, the cut-off law at scale `r` is
`law (intensityProfile (cutoffKernel N K r) β)`. Its `r`-derivative at a pair `e` is the
fork's `cutoffEdgeDeriv`, written out:
`c_r(e) = 1{e ≠ diagonal, N(e) < r} · β (-K'(r)) e^{-β J_r(e)}`, the indicator being the
radial kernel of the profile `s ↦ 1{s < r}`. -/

section Cutoff

variable {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}

/-- For a profile nonnegative and decreasing on `(0, ∞)` and `r > 0`, the cut-off kernel is
`(K (N(x-y)) - K r)₊` off the diagonal. -/
theorem coe_cutoffKernel_eq_max {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0)) {r : ℝ}
    (hr : 0 < r)
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    (cutoffKernel N K r s(x, y) : ℝ) = max (K (N (Int.cast ∘ (x - y))) - K r) 0 := by
  have hs := N.intCast_comp_sub_pos hxy
  rw [cutoffKernel_def, radialKernel_of_ne hxy, ModelNorm.coe_toSeminorm, Real.coe_toNNReal']
  by_cases h : N (Int.cast ∘ (x - y)) ≤ r
  · rw [cutoffProfile_of_le h]
  · rw [cutoffProfile_of_lt (not_le.1 h), max_self, max_eq_right]
    linarith [hKa hr hs (not_le.1 h).le]

/-- The edge probabilities of the cut-off law are continuous in the scale on `(0, ∞)`. -/
theorem continuousOn_cutoff_prob {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    (hKc : ContinuousOn K (Ioi 0))
    (β : ℝ≥0) (e : Sym2 (Fin d → ℤ)) :
    ContinuousOn (fun r => (intensityProfile (cutoffKernel N K r) β e : ℝ)) (Ioi 0) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      have h0 : ∀ r, (intensityProfile (cutoffKernel N K r) β s(x, x) : ℝ) = 0 := fun r => by
        simp [intensityProfile, cutoffKernel_def]
      simp_rw [h0]
      exact continuousOn_const
    · refine ContinuousOn.congr (f := fun r => 1 - Real.exp (-(β : ℝ) *
        max (K (N (Int.cast ∘ (x - y))) - K r) 0)) ?_ fun r hr => ?_
      · have h1 : ContinuousOn (fun r => K (N (Int.cast ∘ (x - y))) - K r) (Ioi 0) :=
          continuousOn_const.sub hKc
        have h2 : ContinuousOn (fun r => max (K (N (Int.cast ∘ (x - y))) - K r) 0) (Ioi 0) :=
          ContinuousOn.sup h1 continuousOn_const
        exact continuousOn_const.sub (Real.continuous_exp.comp_continuousOn
          (continuousOn_const.mul h2))
      · change 1 - Real.exp (-(β : ℝ) * (cutoffKernel N K r s(x, y) : ℝ)) = _
        rw [coe_cutoffKernel_eq_max hKa hr hxy]

/-- **The `r`-derivative of a cut-off edge probability** away from the corner
`r = N(x - y)`: `c_r(e) = 1{N(e) < r} β (-K'(r)) e^{-β J_r(e)}`. -/
theorem hasDerivAt_cutoff_prob {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t) (β : ℝ≥0) {r : ℝ} (hr : 0 < r)
    (e : Sym2 (Fin d → ℤ)) (hre : ∀ x y, e = s(x, y) → r ≠ N (Int.cast ∘ (x - y))) :
    HasDerivAt (fun r => (intensityProfile (cutoffKernel N K r) β e : ℝ))
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) r := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      have h0 : ∀ r, (intensityProfile (cutoffKernel N K r) β s(x, x) : ℝ) = 0 := fun r => by
        simp [intensityProfile, cutoffKernel_def]
      simp_rw [h0, radialKernel_diag, NNReal.coe_zero, zero_mul]
      exact hasDerivAt_const r (0 : ℝ)
    have hs := N.intCast_comp_sub_pos hxy
    have hne := hre x y rfl
    rw [radialKernel_of_ne hxy, ModelNorm.coe_toSeminorm]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `r < N(x - y)`: the pair is closed near `r`
      have hev : (fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ)) =ᶠ[𝓝 r]
          fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hlt] with r' hr'
        change 1 - Real.exp (-(β : ℝ) * (cutoffKernel N K r' s(x, y) : ℝ)) = 0
        rw [cutoffKernel_def, radialKernel_of_ne hxy, ModelNorm.coe_toSeminorm,
          cutoffProfile_of_lt hr']
        simp
      simp only [not_lt.2 hlt.le, ite_false, Real.toNNReal_zero, NNReal.coe_zero, zero_mul]
      exact (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq hev
    · -- `N(x - y) < r`: the pair has probability `1 - e^{-β (K s - K r)}` near `r`
      have hev : (fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ)) =ᶠ[𝓝 r]
          fun r => 1 - Real.exp (-(β : ℝ) * (K (N (Int.cast ∘ (x - y))) - K r)) := by
        filter_upwards [Ioi_mem_nhds hgt] with r' hr'
        change 1 - Real.exp (-(β : ℝ) * (cutoffKernel N K r' s(x, y) : ℝ)) = _
        rw [coe_cutoffKernel_eq_max hKa (hs.trans hr') hxy,
          max_eq_left (sub_nonneg.2 (hKa hs (hs.trans hr') hr'.le))]
      have hJ : (cutoffKernel N K r s(x, y) : ℝ) = K (N (Int.cast ∘ (x - y))) - K r := by
        rw [coe_cutoffKernel_eq_max hKa hr hxy,
          max_eq_left (sub_nonneg.2 (hKa hs (hs.trans hgt) hgt.le))]
      simp only [hgt, ite_true, Real.toNNReal_one, NNReal.coe_one, one_mul]
      rw [hJ]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev
      have h := (((hK' r hr).const_sub (K (N (Int.cast ∘ (x - y))))).const_mul
          (-(β : ℝ))).exp.const_sub 1
      convert h using 1
      ring

/-- The parameters at which some pair sits at the corner form a countable set. -/
theorem countable_cutoff_corners (e : Sym2 (Fin d → ℤ)) :
    {r : ℝ | ∃ x y, e = s(x, y) ∧ r = N (Int.cast ∘ (x - y))}.Countable :=
  (countable_range fun p : (Fin d → ℤ) × (Fin d → ℤ) => N (Int.cast ∘ (p.1 - p.2))).mono (by
    rintro r ⟨x, y, -, rfl⟩
    exact ⟨(x, y), rfl⟩)

/-- Finitely many lattice points have `N (Int.cast ∘ z) < R`, for a norm `N` on `ℝ^d`. -/
theorem finite_norm_lt (N : ModelNorm (Fin d → ℝ)) (R : ℝ) :
    {z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}.Finite := by
  obtain ⟨κ, hκ, hN⟩ := exists_pos_mul_norm_le_intCast N
  refine (finite_norm_le ⌊R / κ⌋₊).subset fun z hz => ?_
  simp only [mem_ofPred_eq] at hz ⊢
  rw [← natCast_floor_norm]
  have : ‖z‖ ≤ R / κ := (le_div_iff₀' hκ).2 ((hN z).trans hz.2.le)
  exact_mod_cast Nat.floor_mono this

/-- The row count `∑'_y 1{y ≠ x, N(x - y) < R}` is the number of nonzero lattice points with
`N (Int.cast ∘ z) < R`. -/
theorem tsum_row_count (x : Fin d → ℤ) (R : ℝ) :
    ∑' y, (if x ≠ y ∧ N (Int.cast ∘ (x - y)) < R then (1 : ℝ≥0∞) else 0) =
      ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}.encard : ℝ≥0∞) := by
  classical
  rw [← (Equiv.subLeft x).tsum_eq, ← mul_one ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) <
      R}.encard : ℝ≥0∞),
    ← tsum_ite_const_eq (fun z : Fin d → ℤ => z ≠ 0 ∧ N (Int.cast ∘ z) < R)]
  refine tsum_congr fun z => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  by_cases hz : z = 0
  · simp [hz]
  · have hxz : x ≠ x - z := fun h => hz (by simpa using h.symm)
    simp [hz, hxz]

/-- **Item 1, the dominator.** On `(u, R)`, if `|K'| ≤ L` there,
the cut-off family satisfies the dominator of `integral_sub_eq_integral_flux` with
`M = (β L · 2 · #{z ≠ 0 : N (Int.cast ∘ z) < R} · E_{μ_R}|K_o|).toReal`. -/
theorem cutoff_dominator {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    (β : ℝ≥0) {L : ℝ} {u R : ℝ}
    (hL : ∀ r ∈ Ioo u R, |K' r| ≤ L) (o : Fin d → ℤ)
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) :
    ∀ r ∈ Ioo u R, ∀ S : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ S, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))| *
        (law (intensityProfile (cutoffKernel N K r) β)).real
          {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤
      (ENNReal.ofReal (β * L) * 2 * ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}.encard : ℝ≥0∞) *
        chi (intensityProfile (cutoffKernel N K R) β) o).toReal := by
  classical
  intro r hr S
  set q := intensityProfile (cutoffKernel N.toSeminorm K r) β
  set nR : ℝ≥0∞ := ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}.encard : ℝ≥0∞)
  set c : Sym2 (Fin d → ℤ) → ℝ := fun e => (radialKernel N
      (fun s => if s < r then 1 else 0) e : ℝ) *
    ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))
  set w : (Fin d → ℤ) × (Fin d → ℤ) → ℝ≥0∞ := fun p =>
    if p.1 ≠ p.2 ∧ N (Int.cast ∘ (p.1 - p.2)) < R then tau q o p.1 else 0
  have hβL : 0 ≤ (β : ℝ) * L := mul_nonneg β.coe_nonneg ((abs_nonneg _).trans (hL r hr))
  -- the per-pair bound
  have hpair : ∀ e, ENNReal.ofReal |c e| * law q {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤
      ENNReal.ofReal (β * L) * (w (Quot.out e) + w
          (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap) := by
    intro e
    obtain ⟨⟨a, b⟩, hab⟩ : ∃ p, Quot.out e = p := ⟨_, rfl⟩
    have he : e = s(a, b) := by rw [← Quot.out_eq e, hab]
    rw [hab]
    simp only [Prod.swap_prod_mk]
    subst he
    by_cases hdiag : a = b
    · subst hdiag
      simp [c, radialKernel_diag]
    by_cases hlt : N (Int.cast ∘ (a - b)) < r
    · have hab' : N (Int.cast ∘ (a - b)) < R := hlt.trans hr.2
      have hba' : N (Int.cast ∘ (b - a)) < R := by
          rwa [intCast_comp_sub, map_sub_rev, ← intCast_comp_sub]
      simp only [w, Ne, hdiag, not_false_eq_true, true_and, hab', ite_true,
        show ¬ b = a from fun h => hdiag h.symm, hba']
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
      · simp only [c, radialKernel_of_ne hdiag, ModelNorm.coe_toSeminorm, hlt, ite_true,
          Real.toNNReal_one, NNReal.coe_one, one_mul, abs_mul, abs_neg]
        rw [abs_of_nonneg β.coe_nonneg, abs_of_pos (Real.exp_pos _)]
        have hexp : Real.exp (-(β : ℝ) * (cutoffKernel N K r s(a, b) : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 β.coe_nonneg)
            (NNReal.coe_nonneg _))
        calc (β : ℝ) * |K' r| * Real.exp (-(β : ℝ) * (cutoffKernel N K r s(a, b) : ℝ))
            ≤ (β : ℝ) * L * 1 := mul_le_mul (mul_le_mul_of_nonneg_left (hL r hr) β.coe_nonneg)
              hexp (Real.exp_pos _).le hβL
          _ = β * L := mul_one _
      · have h : {ω : Config (Fin d → ℤ) | ∃ x ∈ s(a, b), x ∈ cluster ω o} = conn o a ∪
          conn o b := by
          ext ω
          simp only [Sym2.mem_iff, mem_ofPred_eq, mem_union]
          constructor
          · rintro ⟨x, rfl | rfl, hx⟩
            · exact Or.inl hx
            · exact Or.inr hx
          · rintro (h | h)
            · exact ⟨a, Or.inl rfl, h⟩
            · exact ⟨b, Or.inr rfl, h⟩
        rw [h]
        exact measure_union_le _ _
    · simp only [c, radialKernel_of_ne hdiag, ModelNorm.coe_toSeminorm, hlt, ite_false,
        Real.toNNReal_zero, NNReal.coe_zero, zero_mul, abs_zero, ENNReal.ofReal_zero]
      simp
  -- the sum over ordered pairs
  have hw : ∑' p, w p = nR * chi q o := by
    rw [ENNReal.tsum_prod', chi_eq_tsum_tau, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp only [w]
    simp_rw [ite_and]
    have : ∀ y, (if x ≠ y then (if N (Int.cast ∘ (x - y)) < R then tau q o x else 0) else 0) =
        tau q o x * (if x ≠ y ∧ N (Int.cast ∘ (x - y)) < R then 1 else 0) := fun y => by
      by_cases h1 : x ≠ y <;> by_cases h2 : N (Int.cast ∘ (x - y)) < R <;> simp [h1, h2]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, mul_comm]
    exact congrArg (· * tau q o x) (tsum_row_count (N := N.toSeminorm) x R)
  have hinj : Function.Injective (Quot.out : Sym2 (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ)) :=
    fun e f h => by rw [← Quot.out_eq e, ← Quot.out_eq f, h]
  have hinj' : Function.Injective
      (fun e : Sym2 (Fin d → ℤ) => (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap) :=
    Prod.swap_injective.comp hinj
  have hchi : chi q o ≤ chi (intensityProfile (cutoffKernel N K R) β) o :=
    chi_mono (intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKa e hr.2.le) β) o
  have hsum : ∑ e ∈ S, ENNReal.ofReal |c e| * law q {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤
      ENNReal.ofReal (β * L) * 2 * nR * chi (intensityProfile (cutoffKernel N K R) β) o := by
    calc ∑ e ∈ S, ENNReal.ofReal |c e| * law q {ω | ∃ x ∈ e, x ∈ cluster ω o}
        ≤ ∑' e, ENNReal.ofReal |c e| * law q {ω | ∃ x ∈ e, x ∈ cluster ω o} :=
          ENNReal.sum_le_tsum S
      _ ≤ ∑' e, ENNReal.ofReal (β * L) * (w (Quot.out e) +
          w (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap) :=
          ENNReal.tsum_le_tsum hpair
      _ = ENNReal.ofReal (β * L) * (∑' e, w (Quot.out e) + ∑' e,
          w (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      _ ≤ ENNReal.ofReal (β * L) * (∑' p, w p + ∑' p, w p) := by
          gcongr
          · exact ENNReal.tsum_comp_le_tsum_of_injective hinj w
          · exact ENNReal.tsum_comp_le_tsum_of_injective hinj' w
      _ = ENNReal.ofReal (β * L) * 2 * nR * chi q o := by
          rw [hw, ← two_mul]; ring
      _ ≤ _ := by gcongr
  have hfin : ∀ e ∈ S, ENNReal.ofReal |c e| * law q {ω | ∃ x ∈ e, x ∈ cluster ω o} ≠ ⊤ :=
    fun e _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  calc ∑ e ∈ S, |c e| * (law q).real {ω | ∃ x ∈ e, x ∈ cluster ω o}
      = (∑ e ∈ S, ENNReal.ofReal |c e| * law q {ω | ∃ x ∈ e, x ∈ cluster ω o}).toReal := by
        rw [ENNReal.toReal_sum hfin]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
    _ ≤ _ := by
        refine ENNReal.toReal_mono ?_ hsum
        refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofNat_ne_top) ?_) hχ
        exact ENat.toENNReal_ne_top.2 (finite_norm_lt N R).encard_lt_top.ne

/-- **Item 3, integrated form, for the cut-off family.** Let `N` be a norm on
`ℝ^d`, let `K` be decreasing on `(0, ∞)` with continuous derivative `K'` there, and let
the cut-off law at scale `R` have finite expected cluster volume at `o`. Then for
`0 < s ≤ t < R`, with `c_r(e) = 1{N(e) < r} β (-K'(r)) e^{-β J_r(e)}`,
`ψ t - ψ s = ∫_s^t ∑' e, c_r(e) ∫ (F |K_o(ω ∪ {e})| - F |K_o(ω \ {e})|) dμ_r dr`.
No locally uniform convergence of window fluxes is assumed. -/
theorem integral_sub_eq_integral_flux_cutoff {N : ModelNorm (Fin d → ℝ)}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (htR : t < R) :
    ∫ ω, F (cluster ω o).encard ∂(law (intensityProfile (cutoffKernel N K t) β)) -
        ∫ ω, F (cluster ω o).encard ∂(law (intensityProfile (cutoffKernel N K s) β)) =
      ∫ r in s..t, ∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  have hu : 0 < s / 2 := half_pos hs
  have hKc : ContinuousOn K (Ioi 0) := fun t ht => (hK' t ht).continuousAt.continuousWithinAt
  have hsub : Ioo (s / 2) R ⊆ Ioi 0 := fun r hr => hu.trans hr.1
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := s / 2) (b := R)).exists_bound_of_continuousOn
    (hK'c.mono fun r hr => hu.trans_le hr.1)
  refine integral_sub_eq_integral_flux hFm hF o (fun r => intensityProfile (cutoffKernel N K r) β)
    _ (fun e => {r | ∃ x y, e = s(x, y) ∧ r = N (Int.cast ∘ (x - y))}) countable_cutoff_corners
    (fun e => (continuousOn_cutoff_prob hKa hKc β e).mono hsub)
    (fun e r hr hrC => hasDerivAt_cutoff_prob hKa hK' β (hsub hr) e
      fun x y he h => hrC ⟨x, y, he, h⟩)
    (cutoff_dominator hKa β (fun r hr => hL r (Ioo_subset_Icc_self hr)) o hχ)
    (by linarith) hst htR

end Cutoff

/-! ### Continuity of the flux and the derivative -/

/-- The infinite pivotal flux is bounded by `2 m M` under the dominator. -/
theorem abs_flux_le [Countable V] {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m) (o : V)
    (q : Sym2 V → unitInterval) (c : Sym2 V → ℝ) {M : ℝ}
    (hdom : ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c e| * (law q).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ M) :
    |∑' e, c e * ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
      ∂(law q)| ≤ 2 * m * M := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hFm 0)
  set P : Sym2 V → ℝ := fun e => (law q).real {ω | ∃ x ∈ e, x ∈ cluster ω o}
  have hb : ∀ e, ‖c e * ∫ ω, (F (cluster (insert e ω) o).encard -
      F (cluster (ω \ {e}) o).encard) ∂(law q)‖ ≤ |c e| * (2 * m * P e) := fun e => by
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa only [inter_univ] using abs_integral_pivotal_le hFm o univ e (law q)
  have hle : ∀ S : Finset (Sym2 V), ∑ e ∈ S, |c e| * (2 * m * P e) ≤ 2 * m * M := fun S => by
    calc ∑ e ∈ S, |c e| * (2 * m * P e) = 2 * m * ∑ e ∈ S, |c e| * P e := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ 2 * m * M := mul_le_mul_of_nonneg_left (hdom S) (by positivity)
  have hnn : 0 ≤ fun e => |c e| * (2 * m * P e) := fun e => by
    have : 0 ≤ P e := measureReal_nonneg
    positivity
  have hsum := summable_of_sum_le hnn hle
  rw [← Real.norm_eq_abs]
  exact tsum_of_norm_bounded hsum.hasSum hb |>.trans (Real.tsum_le_of_sum_le hnn hle)

/-- **Continuity from the dominator.** Under the hypotheses of
`integral_sub_eq_integral_flux`, `ψ` is Lipschitz, hence continuous, on `(u, v)`. -/
theorem continuousOn_integral_of_dominator [Countable V] {F : ℕ∞ → ℝ} {m : ℝ}
    (hFm : ∀ n, |F n| ≤ m) (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : V)
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {u v : ℝ} (C : Sym2 V → Set ℝ)
    (hC : ∀ e, (C e).Countable) (hcont : ∀ e, ContinuousOn (fun r => (p r e : ℝ)) (Ioo u v))
    (hderiv : ∀ e, ∀ r ∈ Ioo u v, r ∉ C e → HasDerivAt (fun r => (p r e : ℝ)) (c r e) r)
    {M : ℝ} (hdom : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ M) :
    ContinuousOn (fun r => ∫ ω, F (cluster ω o).encard ∂(law (p r))) (Ioo u v) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := (2 * m * M).toNNReal) fun x hx y hy =>
      ?_).continuousOn
  have key : ∀ x ∈ Ioo u v, ∀ y ∈ Ioo u v, y ≤ x →
      dist (∫ ω, F (cluster ω o).encard ∂(law (p x))) (∫ ω, F (cluster ω o).encard ∂(law (p y)))
        ≤ (2 * m * M).toNNReal * dist x y := by
    intro x hx y hy hyx
    rw [Real.dist_eq, Real.dist_eq, integral_sub_eq_integral_flux hFm hF o p c C hC hcont hderiv
      hdom hy.1 hyx hx.2, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * m * M)
      fun r hr => ?_).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _))
    rw [uIoc_of_le hyx] at hr
    rw [Real.norm_eq_abs]
    exact abs_flux_le hFm o (p r) (c r) (hdom r ⟨hy.1.trans hr.1, hr.2.trans_lt hx.2⟩)
  rcases le_total y x with hyx | hxy
  · exact key x hx y hy hyx
  · rw [dist_comm, dist_comm x]
    exact key y hy x hx hxy

/-- Forcing a pair open is the update of its probability to `1`. -/
theorem integral_insert_eq_update [Countable V] [DecidableEq V] {G : Config V → ℝ}
    (hG : Measurable G)
    (q : Sym2 V → unitInterval) (e : Sym2 V) :
    ∫ ω, G (insert e ω) ∂(law q) = ∫ ω, G ω ∂(law (Function.update q e 1)) := by
  simp only [law]
  rw [← prodBernoulli_map_insert, integral_map (measurable_insert e).aemeasurable
    hG.aestronglyMeasurable]

/-- Forcing a pair closed is the update of its probability to `0`. -/
theorem integral_diff_eq_update [Countable V] [DecidableEq V] {G : Config V → ℝ} (hG : Measurable G)
    (q : Sym2 V → unitInterval) (e : Sym2 V) :
    ∫ ω, G (ω \ {e}) ∂(law q) = ∫ ω, G ω ∂(law (Function.update q e 0)) := by
  simp only [law]
  rw [← prodBernoulli_map_diff_singleton, integral_map (measurable_diff_singleton e).aemeasurable
    hG.aestronglyMeasurable]

section CutoffContinuity

variable {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}

/-- The touching probabilities of the pairs at distance below `R`, summed over all pairs,
are at most `2 #{z ≠ 0 : N (Int.cast ∘ z) < R} E|K_o|`. -/
theorem tsum_touch_le (q : Sym2 (Fin d → ℤ) → unitInterval) (R : ℝ) (o : Fin d → ℤ) :
    ∑' e, (radialKernel N (fun s => if s < R then 1 else 0) e : ℝ≥0∞) *
        law q {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤
      2 * ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}.encard : ℝ≥0∞) * chi q o := by
  classical
  set w : (Fin d → ℤ) × (Fin d → ℤ) → ℝ≥0∞ := fun p =>
    if p.1 ≠ p.2 ∧ N (Int.cast ∘ (p.1 - p.2)) < R then tau q o p.1 else 0
  have hpair : ∀ e, (radialKernel N (fun s => if s < R then 1 else 0) e : ℝ≥0∞) *
      law q {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤
      w (Quot.out e) + w (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap := by
    intro e
    obtain ⟨⟨a, b⟩, hab⟩ : ∃ p, Quot.out e = p := ⟨_, rfl⟩
    have he : e = s(a, b) := by rw [← Quot.out_eq e, hab]
    rw [hab]
    simp only [Prod.swap_prod_mk]
    subst he
    by_cases hdiag : a = b
    · subst hdiag
      simp [radialKernel_diag]
    by_cases hlt : N (Int.cast ∘ (a - b)) < R
    · have hba : N (Int.cast ∘ (b - a)) < R := by rwa [intCast_comp_sub, map_sub_rev,
        ← intCast_comp_sub]
      simp only [w, Ne, hdiag, not_false_eq_true, true_and, hlt, ite_true,
        show ¬ b = a from fun h => hdiag h.symm, hba, radialKernel_of_ne hdiag,
        Real.toNNReal_one, ENNReal.coe_one, one_mul]
      have h : {ω : Config (Fin d → ℤ) | ∃ x ∈ s(a, b), x ∈ cluster ω o} = conn o a ∪ conn o b := by
        ext ω
        simp only [Sym2.mem_iff, mem_ofPred_eq, mem_union]
        constructor
        · rintro ⟨x, rfl | rfl, hx⟩
          · exact Or.inl hx
          · exact Or.inr hx
        · rintro (h | h)
          · exact ⟨a, Or.inl rfl, h⟩
          · exact ⟨b, Or.inr rfl, h⟩
      rw [h]
      exact measure_union_le _ _
    · simp [radialKernel_of_ne hdiag, hlt]
  have hw : ∑' p, w p = ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}.encard : ℝ≥0∞) *
      chi q o := by
    rw [ENNReal.tsum_prod', chi_eq_tsum_tau, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp only [w]
    have : ∀ y, (if x ≠ y ∧ N (Int.cast ∘ (x - y)) < R then tau q o x else 0) =
        tau q o x * (if x ≠ y ∧ N (Int.cast ∘ (x - y)) < R then 1 else 0) := fun y => by
      split_ifs <;> simp
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, tsum_row_count, mul_comm]
  have hinj : Function.Injective (Quot.out : Sym2 (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ)) :=
    fun e f h => by rw [← Quot.out_eq e, ← Quot.out_eq f, h]
  have hinj' : Function.Injective
      (fun e : Sym2 (Fin d → ℤ) => (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap) :=
    Prod.swap_injective.comp hinj
  calc ∑' e, (radialKernel N (fun s => if s < R then 1 else 0) e : ℝ≥0∞) *
        law q {ω | ∃ x ∈ e, x ∈ cluster ω o}
      ≤ ∑' e, (w (Quot.out e) + w (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap) :=
        ENNReal.tsum_le_tsum hpair
    _ = ∑' e, w (Quot.out e) + ∑' e, w (Quot.out e : (Fin d → ℤ) × (Fin d → ℤ)).swap :=
        ENNReal.tsum_add
    _ ≤ ∑' p, w p + ∑' p, w p := add_le_add (ENNReal.tsum_comp_le_tsum_of_injective hinj w)
        (ENNReal.tsum_comp_le_tsum_of_injective hinj' w)
    _ = _ := by rw [hw, ← two_mul, mul_assoc]

/-- The cut-off family is translation invariant, so its susceptibility does not depend on
the root. -/
theorem chi_cutoff_eq (K : ℝ → ℝ) (R : ℝ) (β : ℝ≥0) (x y : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel N K R) β) x =
      chi (intensityProfile (cutoffKernel N K R) β) y := by
  refine chi_eq_of_transitive _ (fun x y => ⟨Equiv.addRight (y - x), by simp, fun e => ?_⟩) β x y
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, Equiv.coe_addRight, cutoffKernel_def, radialKernel_mk, add_left_inj,
      add_sub_add_right_eq_sub]

/-- Under forcing a pair `s(a, b)` open, a pair touches the cluster of `o` only if it touches
the cluster of `o`, `a` or `b`. -/
theorem touch_insert_subset (o a b : Fin d → ℤ) (f : Sym2 (Fin d → ℤ)) :
    {ω : Config (Fin d → ℤ) | insert s(a, b) ω ∈ {ω' : Config (Fin d → ℤ) |
        ∃ x ∈ f, x ∈ cluster ω' o}} ⊆
      ({ω | ∃ x ∈ f, x ∈ cluster ω o} ∪ {ω | ∃ x ∈ f, x ∈ cluster ω a}) ∪
        {ω | ∃ x ∈ f, x ∈ cluster ω b} := by
  rintro ω ⟨x, hxf, hx⟩
  rcases cluster_insert_subset ω a b o hx with (h | h) | h
  · exact Or.inl (Or.inl ⟨x, hxf, h⟩)
  · exact Or.inl (Or.inr ⟨x, hxf, h⟩)
  · exact Or.inr ⟨x, hxf, h⟩

/-- **Continuity of the pivotal terms.** For the cut-off family, `r ↦ Δ_e(r)` is continuous
on `(u, R)` for every pair `e` and every `u > 0`. -/
theorem continuousOn_pivotal_cutoff {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u : ℝ} (hu : 0 < u)
    (e : Sym2 (Fin d → ℤ)) :
    ContinuousOn (fun r => ∫ ω, (F (cluster (insert e ω) o).encard -
      F (cluster (ω \ {e}) o).encard) ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (Ioo u R) := by
  set q : ℝ → Sym2 (Fin d → ℤ) → unitInterval := fun r => intensityProfile (cutoffKernel N K r) β
  set c : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r f =>
    (radialKernel N (fun s => if s < r then 1 else 0) f : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r f : ℝ)))
  set C : Sym2 (Fin d → ℤ) → Set ℝ := fun f => {r | ∃ x y, f = s(x, y) ∧ r = N (Int.cast ∘ (x - y))}
  have hKc : ContinuousOn K (Ioi 0) := fun t ht => (hK' t ht).continuousAt.continuousWithinAt
  have hsub : Ioo u R ⊆ Ioi 0 := fun r hr => hu.trans hr.1
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := u) (b := R)).exists_bound_of_continuousOn
    (hK'c.mono fun r hr => hu.trans_le hr.1)
  have hL' : ∀ r ∈ Ioo u R, |K' r| ≤ L := fun r hr => hL r (Ioo_subset_Icc_self hr)
  have hmeas : Measurable fun ω : Config (Fin d → ℤ) => F (cluster ω o).encard :=
    (measurable_of_countable F).comp (measurable_encard_cluster o)
  have hint : ∀ (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
      (T : Config (Fin d → ℤ) → Config (Fin d → ℤ)), Measurable T →
      Integrable (fun ω => F (cluster (T ω) o).encard) μ := fun μ _ T hT =>
    Integrable.of_bound (C := m) (hmeas.comp hT).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFm _)
  have hcont : ∀ f, ContinuousOn (fun r => (q r f : ℝ)) (Ioo u R) := fun f =>
    (continuousOn_cutoff_prob hKa hKc β f).mono hsub
  have hderiv : ∀ f, ∀ r ∈ Ioo u R, r ∉ C f → HasDerivAt (fun r => (q r f : ℝ)) (c r f) r :=
    fun f r hr hrC => hasDerivAt_cutoff_prob hKa hK' β (hsub hr) f
      fun x y he h => hrC ⟨x, y, he, h⟩
  have hdom : ∀ (x : Fin d → ℤ), ∀ r ∈ Ioo u R, ∀ S : Finset (Sym2 (Fin d → ℤ)),
      ∑ f ∈ S, |c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω x} ≤
        (ENNReal.ofReal (β * L) * 2 * ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) <
            R}.encard : ℝ≥0∞) *
          chi (intensityProfile (cutoffKernel N K R) β) o).toReal := fun x => by
    rw [chi_cutoff_eq K R β o x]
    exact cutoff_dominator hKa β hL' x (by rwa [← chi_cutoff_eq K R β o x])
  set M := (ENNReal.ofReal (β * L) * 2 * ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) <
      R}.encard : ℝ≥0∞) *
    chi (intensityProfile (cutoffKernel N K R) β) o).toReal
  -- the two forced families
  set c' : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r f => if f = e then 0 else c r f
  have hc' : ∀ r f, |c' r f| ≤ |c r f| := fun r f => by
    simp only [c']; split_ifs <;> simp
  have hcont' : ∀ (t : unitInterval) f,
      ContinuousOn (fun r => (Function.update (q r) e t f : ℝ)) (Ioo u R) := fun t f => by
    by_cases hf : f = e
    · subst hf; simp only [Function.update_self]; exact continuousOn_const
    · simp only [Function.update_of_ne hf]; exact hcont f
  have hderiv' : ∀ (t : unitInterval) f, ∀ r ∈ Ioo u R, r ∉ C f →
      HasDerivAt (fun r => (Function.update (q r) e t f : ℝ)) (c' r f) r := fun t f r hr hrC => by
    by_cases hf : f = e
    · subst hf; simp only [Function.update_self, c', ite_true]; exact hasDerivAt_const r _
    · simp only [Function.update_of_ne hf, c', hf, ite_false]; exact hderiv f r hr hrC
  have hψ1 := continuousOn_integral_of_dominator hFm hF o (fun r => Function.update (q r) e 1) c'
    C (fun f => countable_cutoff_corners f) (hcont' 1) (hderiv' 1) (M := 3 * M) (by
      intro r hr S
      induction e using Sym2.ind with
      | _ a b =>
      calc ∑ f ∈ S, |c' r f| * (law (Function.update (q r) s(a, b) 1)).real
            {ω | ∃ y ∈ f, y ∈ cluster ω o}
          ≤ ∑ f ∈ S, (|c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω o} +
              |c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω a} +
              |c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω b}) := by
            refine Finset.sum_le_sum fun f _ => ?_
            rw [← mul_add, ← mul_add]
            refine mul_le_mul (hc' r f) ?_ measureReal_nonneg (abs_nonneg _)
            rw [measureReal_def, law, prodBernoulli_update_one_apply _ _ (measurableSet_touch o f),
              ← law, ← measureReal_def]
            exact (measureReal_mono (touch_insert_subset o a b f)).trans
              ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
        _ = ∑ f ∈ S, |c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω o} +
              ∑ f ∈ S, |c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω a} +
              ∑ f ∈ S, |c r f| * (law (q r)).real {ω | ∃ y ∈ f, y ∈ cluster ω b} := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ M + M + M := add_le_add (add_le_add (hdom o r hr S) (hdom a r hr S)) (hdom b r hr S)
        _ = 3 * M := by ring)
  have hψ0 := continuousOn_integral_of_dominator hFm hF o (fun r => Function.update (q r) e 0) c'
    C (fun f => countable_cutoff_corners f) (hcont' 0) (hderiv' 0) (M := M) (by
      intro r hr S
      refine le_trans (Finset.sum_le_sum fun f _ => ?_) (hdom o r hr S)
      refine mul_le_mul (hc' r f) ?_ measureReal_nonneg (abs_nonneg _)
      rw [measureReal_def, law, prodBernoulli_update_zero_apply _ _ (measurableSet_touch o f),
        ← law, ← measureReal_def]
      exact measureReal_mono fun ω ⟨y, hyf, hy⟩ => ⟨y, hyf, cluster_mono sdiff_subset o hy⟩)
  refine (hψ1.sub hψ0).congr fun r _ => ?_
  rw [integral_sub (hint _ _ (measurable_insert e)) (hint _ _ (measurable_diff_singleton e)),
    integral_insert_eq_update (G := fun ω => F (cluster ω o).encard) hmeas,
    integral_diff_eq_update (G := fun ω => F (cluster ω o).encard) hmeas]
  rfl

/-- The indicator `1{N(e) < r}` increases with `r`. -/
theorem radialKernel_indicator_mono {r r' : ℝ} (h : r ≤ r') (e : Sym2 (Fin d → ℤ)) :
    radialKernel N (fun s => if s < r then 1 else 0) e ≤
      radialKernel N (fun s => if s < r' then 1 else 0) e := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · simp [hxy]
    rw [radialKernel_of_ne hxy, radialKernel_of_ne hxy]
    refine Real.toNNReal_le_toNNReal ?_
    by_cases h1 : N (Int.cast ∘ (x - y)) < r
    · simp [h1, h1.trans_le h]
    · simp only [h1, ite_false]; split_ifs <;> norm_num

/-- **Item 2.** On an interval `(u, v) ⊆ (0, R)` that contains no value `N (Int.cast ∘ z)`,
the infinite pivotal flux of the cut-off family is continuous. -/
theorem continuousOn_flux_cutoff {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u v : ℝ} (hu : 0 < u)
    (hvR : v ≤ R) (hI : ∀ z, N (Int.cast ∘ z) ∉ Ioo u v) :
    ContinuousOn (fun r => ∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v) := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hFm 0)
  have hKc : ContinuousOn K (Ioi 0) := fun t ht => (hK' t ht).continuousAt.continuousWithinAt
  have hsub : Ioo u v ⊆ Ioi 0 := fun r hr => hu.trans hr.1
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := u) (b := v)).exists_bound_of_continuousOn
    (hK'c.mono fun r hr => hu.trans_le hr.1)
  have hL0 : 0 ≤ L ∨ IsEmpty (Ioo u v) := by
    rcases (Ioo u v).eq_empty_or_nonempty with h | ⟨r, hr⟩
    · exact Or.inr (by rw [h]; infer_instance)
    · exact Or.inl ((norm_nonneg _).trans (hL r (Ioo_subset_Icc_self hr)))
  rcases hL0 with hL0 | hempty
  swap
  · intro r hr; exact absurd ⟨r, hr⟩ (not_nonempty_iff.2 hempty)
  set P : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r e =>
    (law (intensityProfile (cutoffKernel N K r) β)).real {ω | ∃ x ∈ e, x ∈ cluster ω o}
  set B : Sym2 (Fin d → ℤ) → ℝ := fun e => 2 * m * ((β : ℝ) * L) *
    ((radialKernel N (fun s => if s < v then 1 else 0) e : ℝ) * P v e)
  -- summability of the bound
  have hχv : chi (intensityProfile (cutoffKernel N K v) β) o ≠ ⊤ :=
    ne_top_of_le_ne_top hχ (chi_mono (intensityProfile_le_of_le
      (fun e => monotone_cutoffKernel hKa e hvR) β) o)
  have hBsum : Summable B := by
    have hfin : ∑' e, (radialKernel N (fun s => if s < v then 1 else 0) e : ℝ≥0∞) *
        law (intensityProfile (cutoffKernel N K v) β) {ω | ∃ x ∈ e, x ∈ cluster ω o} ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENat.toENNReal_ne_top.2 (finite_norm_lt N v).encard_lt_top.ne)) hχv)
        (tsum_touch_le _ v o)
    refine (ENNReal.summable_toReal hfin).mul_left (2 * m * ((β : ℝ) * L)) |>.congr fun e => ?_
    simp only [B, P, ENNReal.toReal_mul, ENNReal.coe_toReal, measureReal_def]
  -- the terms
  refine continuousOn_tsum (u := B) (fun e => ?_) hBsum fun e r hr => ?_
  · -- each term is continuous on the corner-free interval
    refine ContinuousOn.mul ?_ (continuousOn_pivotal_cutoff hKa hK' hK'c β hFm hF o hχ hu e
      |>.mono fun r hr => ⟨hr.1, hr.2.trans_le hvR⟩)
    induction e using Sym2.ind with
    | _ x y =>
    by_cases hxy : x = y
    · subst hxy; simp only [radialKernel_diag, NNReal.coe_zero, zero_mul]; exact continuousOn_const
    have hcst : ∃ a : ℝ, ∀ r ∈ Ioo u v,
        (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) = a := by
      have hz := hI (x - y)
      by_cases hle : N (Int.cast ∘ (x - y)) ≤ u
      · exact ⟨1, fun r hr => by
          rw [radialKernel_of_ne hxy]; simp [hle.trans_lt hr.1]⟩
      · have hge : v ≤ N (Int.cast ∘ (x - y)) := by
          by_contra h'
          exact hz ⟨not_le.1 hle, not_le.1 h'⟩
        exact ⟨0, fun r hr => by
          rw [radialKernel_of_ne hxy]; simp [not_lt.2 (hr.2.le.trans hge)]⟩
    obtain ⟨a, ha⟩ := hcst
    refine ContinuousOn.congr (f := fun r => a * ((β : ℝ) * -K' r *
      Real.exp (-(β : ℝ) * max (K (N (Int.cast ∘ (x - y))) - K r) 0))) ?_ fun r hr => ?_
    · have h1 : ContinuousOn (fun r => K (N (Int.cast ∘ (x - y))) - K r) (Ioo u v) :=
        continuousOn_const.sub (hKc.mono hsub)
      have h2 : ContinuousOn (fun r => max (K (N (Int.cast ∘ (x - y))) - K r) 0) (Ioo u v) :=
        ContinuousOn.sup h1 continuousOn_const
      exact continuousOn_const.mul ((continuousOn_const.mul ((hK'c.mono hsub).neg)).mul
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul h2)))
    · simp only
      rw [ha r hr, coe_cutoffKernel_eq_max hKa (hsub hr) hxy]
  · -- the uniform bound
    have hr' : r ∈ Ioo u R := ⟨hr.1, hr.2.trans_le hvR⟩
    rw [Real.norm_eq_abs, abs_mul]
    have hpiv := abs_integral_pivotal_le hFm o univ e
      (law (intensityProfile (cutoffKernel N K r) β))
    simp only [inter_univ] at hpiv
    have hP : P r e ≤ P v e := by
      simp only [P, measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
      exact prodBernoulli_mono_event _ _ (intensityProfile_le_of_le
        (fun e => monotone_cutoffKernel hKa e hr.2.le) β) (measurableSet_touch o e)
        fun ω ω' h ⟨x, hxe, hx⟩ => ⟨x, hxe, cluster_mono h o hx⟩
    have hc : |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))| ≤
        (radialKernel N (fun s => if s < v then 1 else 0) e : ℝ) * ((β : ℝ) * L) := by
      rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
      refine mul_le_mul (radialKernel_indicator_mono hr.2.le e) ?_ (abs_nonneg _)
        (NNReal.coe_nonneg _)
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg β.coe_nonneg, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 β.coe_nonneg)
          (NNReal.coe_nonneg _))
      calc (β : ℝ) * |K' r| * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))
          ≤ (β : ℝ) * L * 1 := mul_le_mul (mul_le_mul_of_nonneg_left
            (by simpa using hL r (Ioo_subset_Icc_self hr)) β.coe_nonneg) hexp
            (Real.exp_pos _).le (mul_nonneg β.coe_nonneg hL0)
        _ = β * L := mul_one _
    calc _ ≤ (radialKernel N (fun s => if s < v then 1 else 0) e : ℝ) * ((β : ℝ) * L) *
          (2 * m * P r e) := mul_le_mul hc hpiv (abs_nonneg _) (by positivity)
      _ ≤ (radialKernel N (fun s => if s < v then 1 else 0) e : ℝ) * ((β : ℝ) * L) *
          (2 * m * P v e) := by gcongr
      _ = B e := by simp only [B]; ring

/-- Around a parameter `r₀ ∈ (0, R)` that is not a value `N (Int.cast ∘ z)`, there is a corner-free
open interval inside `(0, R)`. -/
theorem exists_corner_free {N : ModelNorm (Fin d → ℝ)} {r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hr₀R : r₀ < R) (hcorner : ∀ z, N (Int.cast ∘ z) ≠ r₀) :
    ∃ δ > 0, 0 < r₀ - δ ∧ r₀ + δ ≤ R ∧ ∀ z, N (Int.cast ∘ z) ∉ Ioo (r₀ - δ) (r₀ + δ) := by
  set D : Set ℝ := (fun z => N (Int.cast ∘ z)) '' {z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < R}
  have hD : D.Finite := (finite_norm_lt N R).image _
  have hr₀D : r₀ ∈ Dᶜ := fun ⟨z, _, hz⟩ => hcorner z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD.isClosed.isOpen_compl r₀ hr₀D
  refine ⟨min ε (min (r₀ / 2) (R - r₀)), lt_min hε (lt_min (half_pos hr₀) (sub_pos.2 hr₀R)),
    by linarith [min_le_right ε (min (r₀ / 2) (R - r₀)), min_le_left (r₀ / 2) (R - r₀)],
    by linarith [min_le_right ε (min (r₀ / 2) (R - r₀)), min_le_right (r₀ / 2) (R - r₀)],
    fun z hz => ?_⟩
  have hδε := min_le_left ε (min (r₀ / 2) (R - r₀))
  have hδ1 := min_le_right ε (min (r₀ / 2) (R - r₀))
  have hδ2 := min_le_left (r₀ / 2) (R - r₀)
  have hδ3 := min_le_right (r₀ / 2) (R - r₀)
  by_cases hz0 : z = 0
  · subst hz0
    rw [show (Int.cast ∘ (0 : Fin d → ℤ) : Fin d → ℝ) = 0 from funext fun _ => by simp,
      map_zero] at hz
    linarith [hz.1]
  · refine hball (show N (Int.cast ∘ z) ∈ Metric.ball r₀ ε from ?_)
      ⟨z, ⟨hz0, by linarith [hz.2]⟩, rfl⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]

/-- **Item 3: Lemma I.4.1 without `hunif`.** For the cut-off family with finite
expected cluster volume at scale `R`, the expectation `ψ(r) = ∫ F |K_o| dμ_r` is
differentiable at every `r₀ ∈ (0, R)` that is not a value `N (Int.cast ∘ z)`, with derivative the
infinite pivotal flux `∑' e, c_{r₀}(e) ∫ (F |K_o(ω ∪ {e})| - F |K_o(ω \ {e})|) dμ_{r₀}`. -/
theorem hasDerivAt_integral_cutoff {N : ModelNorm (Fin d → ℝ)} (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀R : r₀ < R) (hcorner : ∀ z, N (Int.cast ∘ z) ≠ r₀) :
    HasDerivAt (fun r => ∫ ω, F (cluster ω o).encard
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (∑' e, ((radialKernel N (fun s => if s < r₀ then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r₀ * Real.exp (-(β : ℝ) * (cutoffKernel N K r₀ e : ℝ)))) *
        ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
          ∂(law (intensityProfile (cutoffKernel N K r₀) β))) r₀ := by
  obtain ⟨δ, hδ, hδ0, hδR, hI⟩ := exists_corner_free hr₀ hr₀R hcorner
  set ψ : ℝ → ℝ := fun r => ∫ ω, F (cluster ω o).encard
    ∂(law (intensityProfile (cutoffKernel N K r) β))
  set Φ : ℝ → ℝ := fun r => ∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
    ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
      ∂(law (intensityProfile (cutoffKernel N K r) β))
  have hΦ : ContinuousOn Φ (Ioo (r₀ - δ) (r₀ + δ)) :=
    continuousOn_flux_cutoff hKa hK' hK'c β hFm hF o hχ hδ0 hδR hI
  have hmem : Ioo (r₀ - δ) (r₀ + δ) ∈ 𝓝 r₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hident : ψ =ᶠ[𝓝 r₀] fun r => ψ r₀ + ∫ y in r₀..r, Φ y := by
    filter_upwards [hmem] with r hr
    rcases le_total r₀ r with h | h
    · rw [← integral_sub_eq_integral_flux_cutoff hKa hK' hK'c β hFm hF o hχ hr₀ h
        (by linarith [hr.2])]
      ring
    · rw [intervalIntegral.integral_symm, ← integral_sub_eq_integral_flux_cutoff hKa hK'
        hK'c β hFm hF o hχ (by linarith [hr.1]) h hr₀R]
      ring
  have hInt : HasDerivAt (fun r => ψ r₀ + ∫ y in r₀..r, Φ y) (Φ r₀) r₀ :=
    (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hΦ.stronglyMeasurableAtFilter isOpen_Ioo r₀ ⟨by linarith, by linarith⟩)
      (hΦ.continuousAt hmem)).const_add _
  exact hInt.congr_of_eventuallyEq hident

end CutoffContinuity

/-! ### Witnesses -/

/-- Non-vacuity witness for the cut-off family: at `d = 1`, the sup norm, `K(s) = s^{-2}` and
`β = 1/10`, the cut-off law at `R = 5/2` has finite susceptibility (its kernel has total mass at
most `4`). -/
theorem chi_cutoff_example_ne_top :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2)
      (5 / 2)) (1 / 10)) 0 ≠ ⊤ := by
  set N := normSeminorm ℝ (Fin 1 → ℝ)
  set K := powerLawProfile 1 2
  have hK : ∀ t, 0 < t → 0 ≤ K t := fun t ht => (powerLawProfile_pos one_pos ht).le
  set k : (Fin 1 → ℤ) → ℝ≥0 := fun z => cutoffKernel N K (5 / 2) s(0, z)
  have hJ : ∀ x y, cutoffKernel N K (5 / 2) s(x, y) = k (y - x) := fun x y => by
    simp only [k, cutoffKernel_def, radialKernel_mk, zero_sub, neg_sub]
    congr 1
    exact propext ⟨fun h => by rw [h, sub_self], fun h => (sub_eq_zero.1 h.symm).symm⟩
  have hk : ∑' z, (k z : ℝ≥0∞) ≤ ((4 : ℝ≥0) : ℝ≥0∞) := by
    refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) ((tsum_ofReal_powerLaw_tail_le le_rfl
      one_pos le_rfl).trans_eq ?_)
    · by_cases hz : z = 0
      · simp [k, hz, cutoffKernel_def]
      have h1 : 1 ≤ ‖z‖ := one_le_norm_of_ne_zero hz
      have hle := cutoffKernel_le_radialKernel (N := ModelNorm.ofNorm (Fin 1 → ℝ)) hK
          (by norm_num : (0 : ℝ) < 5 / 2)
        s(0, z)
      rw [ModelNorm.toSeminorm_ofNorm, radialKernel_of_ne (Ne.symm hz)] at hle
      refine (ENNReal.coe_le_coe.2 hle).trans_eq ?_
      simp only [h1, ite_true, zero_sub, K, powerLawProfile, one_mul, ENNReal.ofReal]
      norm_num
      rw [intCast_comp_neg, norm_neg, norm_intCast_comp]
    · norm_num
  have hβ : ((1 / 10 : ℝ≥0) : ℝ≥0∞) * ((4 : ℝ≥0) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    norm_num
  refine ne_top_of_le_ne_top ?_ (chi_intensity_le_of_translationInvariant _ k hJ 4 hk _ hβ 0)
  exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hβ).ne'

/-- Non-vacuity witness for item 3 (integrated form): `d = 1`, sup norm, `K(s) = s^{-2}` with
`K'(s) = -2 s^{-3}`, `β = 1/10`, `R = 5/2`, `[s, t] = [3/2, 2]` and `F n = 1{n ≥ 2}`. -/
example := integral_sub_eq_integral_flux_cutoff (d := 1) (N := ModelNorm.ofNorm (Fin 1 → ℝ))
  (K := powerLawProfile 1 2) (K' := fun t => 1 * ((-2) * t ^ ((-2 : ℝ) - 1)))
  (antitoneOn_powerLawProfile zero_le_one zero_le_two)
  (fun t ht => by
    have h := (Real.hasDerivAt_rpow_const (p := -2) (Or.inl ht.ne')).const_mul (1 : ℝ)
    convert h using 1
    funext x
    simp [powerLawProfile])
  (continuousOn_const.mul (continuousOn_const.mul
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))))
  (1 / 10) (F := fun n => if n ≤ 1 then 0 else 1) (m := 1) (fun n => by split_ifs <;> simp)
  ⟨2, fun n hn => by
    have h1 : ¬ n ≤ 1 := fun h => absurd (hn.trans h) (by decide)
    simp [h1]⟩ 0 chi_cutoff_example_ne_top (s := 3 / 2) (t := 2) (by norm_num) (by norm_num)
  (by norm_num)

/-- On `Bool`, with every pair open with probability `r` on `(0, 1)`, derivative `1`, no
exceptional parameters, the functional `F n = 1{n ≥ 2}` and `M = 3` (there are three pairs),
every hypothesis of `integral_sub_eq_integral_flux` holds. -/
example := integral_sub_eq_integral_flux (V := Bool) (F := fun n => if n ≤ 1 then 0 else 1)
  (m := 1) (fun n => by split_ifs <;> simp) ⟨2, fun n hn => by
    have h1 : ¬ n ≤ 1 := fun h => absurd (hn.trans h) (by decide)
    simp [h1]⟩ false (fun r _ => Set.projIcc (0 : ℝ) 1 zero_le_one r) (fun _ _ => 1)
  (u := 0) (v := 1) (fun _ => ∅) (fun _ => countable_empty)
  (fun _ => (continuous_subtype_val.comp continuous_projIcc).continuousOn)
  (fun _ r hr _ => (hasDerivAt_id r).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds hr.1 hr.2) fun x hx => by
      simp [Set.projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hx)]))
  (M := 3) (fun r _ S => by
    calc ∑ e ∈ S, |(1 : ℝ)| * (law _).real {ω | ∃ x ∈ e, x ∈ cluster ω false}
        ≤ ∑ e ∈ S, (1 : ℝ) := Finset.sum_le_sum fun e _ => by
          rw [abs_one, one_mul]; exact measureReal_le_one
      _ ≤ 3 := by
          rw [Finset.sum_const, nsmul_one]
          exact_mod_cast (Finset.card_le_univ S).trans_eq (by decide))
  (s := 1 / 4) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)


/-- For the sup norm no lattice point has norm in `(3/2, 2)`. -/
theorem norm_not_mem_Ioo_three_halves_two (z : Fin 1 → ℤ) :
    ModelNorm.ofNorm (Fin 1 → ℝ) (Int.cast ∘ z) ∉ Ioo (3 / 2 : ℝ) 2 := by
  rw [ModelNorm.coe_ofNorm, norm_intCast_comp, ← natCast_floor_norm]
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_ge ⌊‖z‖⌋₊ 2 with h | h
  · have : (⌊‖z‖⌋₊ : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 h
    linarith
  · have : (2 : ℝ) ≤ ⌊‖z‖⌋₊ := by exact_mod_cast h
    linarith

/-- Non-vacuity witness for items 2 and 3: at `d = 1`, the sup norm, `K(s) = s^{-2}`, `β = 1/10`,
`R = 5/2`, `F n = 1{n ≥ 2}`: the flux is continuous on `(3/2, 2)` and `ψ` is differentiable
at `r₀ = 7/4`. -/
example := hasDerivAt_integral_cutoff (d := 1) (N := ModelNorm.ofNorm (Fin 1 → ℝ))
  (K := powerLawProfile 1 2) (K' := fun t => 1 * ((-2) * t ^ ((-2 : ℝ) - 1)))
  (antitoneOn_powerLawProfile zero_le_one zero_le_two)
  (fun t ht => by
    have h := (Real.hasDerivAt_rpow_const (p := -2) (Or.inl ht.ne')).const_mul (1 : ℝ)
    convert h using 1
    funext x
    simp [powerLawProfile])
  (continuousOn_const.mul (continuousOn_const.mul
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))))
  (1 / 10) (F := fun n => if n ≤ 1 then 0 else 1) (m := 1) (fun n => by split_ifs <;> simp)
  ⟨2, fun n hn => by
    have h1 : ¬ n ≤ 1 := fun h => absurd (hn.trans h) (by decide)
    simp [h1]⟩ 0 chi_cutoff_example_ne_top (r₀ := 7 / 4) (by norm_num) (by norm_num)
  (fun z h => norm_not_mem_Ioo_three_halves_two z ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩)

example := continuousOn_flux_cutoff (d := 1) (N := ModelNorm.ofNorm (Fin 1 → ℝ))
  (K := powerLawProfile 1 2) (K' := fun t => 1 * ((-2) * t ^ ((-2 : ℝ) - 1)))
  (antitoneOn_powerLawProfile zero_le_one zero_le_two)
  (fun t ht => by
    have h := (Real.hasDerivAt_rpow_const (p := -2) (Or.inl ht.ne')).const_mul (1 : ℝ)
    convert h using 1
    funext x
    simp [powerLawProfile])
  (continuousOn_const.mul (continuousOn_const.mul
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))))
  (1 / 10) (F := fun n => if n ≤ 1 then 0 else 1) (m := 1) (fun n => by split_ifs <;> simp)
  ⟨2, fun n hn => by
    have h1 : ¬ n ≤ 1 := fun h => absurd (hn.trans h) (by decide)
    simp [h1]⟩ 0 chi_cutoff_example_ne_top (u := 3 / 2) (v := 2) (by norm_num) (by norm_num)
  norm_not_mem_Ioo_three_halves_two

end PercLib.Models.LongRange
