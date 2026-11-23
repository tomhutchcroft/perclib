/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Finite-window expectation continuity and monotone profile convergence are composed to compare
true extended cluster moments. No finite-window law is substituted for the infinite-volume law.
-/
module

public import PercLib.Percolation.Bond.EdgeWindowMoments
public import PercLib.Percolation.Bond.MomentTransport
public import PercLib.Probability.FiniteContinuity

/-!
# Convergence of cluster moments along monotone bond profiles

For a pointwise-increasing family of Bernoulli bond profiles converging to a limiting profile,
every natural power of a rooted cluster's extended cardinality converges to the limiting moment.
The limit holds in `ℝ≥0∞`, including when the limiting moment is `⊤`. Finite edge windows are used
only as an intermediate exhaustion of the infinite-lattice cluster.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PercLib.Probability
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- The windowed moment as a function of the profile is continuous. -/
theorem continuous_lintegral_encard_cluster_inter_window_pow
    (o : V) (F : Finset (Sym2 V)) (p : ℕ) :
    Continuous fun q : Sym2 V → unitInterval =>
      ∫⁻ ω, ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q := by
  classical
  have hm : Measurable (fun ω : Set (Sym2 V) => (Subtype.val ⁻¹' ω : Set F)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  have himg : ∀ ω : Set (Sym2 V), (Subtype.val '' (Subtype.val ⁻¹' ω : Set F) : Set (Sym2 V))
      = ω ∩ (F : Set (Sym2 V)) := by
    intro ω
    ext e
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨e, h2⟩, h1, rfl⟩
  have hsub : ∀ A : Set F, (Subtype.val '' A : Set (Sym2 V)) ⊆ (F : Set (Sym2 V)) := by
    intro A e he
    obtain ⟨i, -, rfl⟩ := he
    exact i.2
  have hgm : Measurable fun A : Set F =>
      ((cluster ((Subtype.val '' A : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p :=
    measurable_of_countable _
  have hfin : ∀ A : Set F,
      ((cluster ((Subtype.val '' A : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ≠ ⊤ := by
    intro A
    have hle : (cluster (Subtype.val '' A : Set (Sym2 V)) o).encard ≤
        ((insert o (F.biUnion fun e => e.toFinset)).card : ℕ∞) := by
      refine le_trans (encard_le_encard (cluster_mono ?_ o))
        (WindowMoments.encard_cluster_inter_window_le_card
          (ω := (Subtype.val '' A : Set (Sym2 V))) o F)
      exact fun e he => ⟨he, hsub A he⟩
    have hle2 : ((cluster (Subtype.val '' A : Set (Sym2 V)) o).encard : ℝ≥0∞) ≤
        ((insert o (F.biUnion fun e => e.toFinset)).card : ℝ≥0∞) := by
      simpa using ENat.toENNReal_le.2 hle
    exact ENNReal.pow_ne_top (ne_top_of_le_ne_top (by simp) hle2)
  have hkey : ∀ q : Sym2 V → unitInterval,
      ∫⁻ ω, ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q =
        ∑ A : Set F, ((cluster ((Subtype.val '' A : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p *
          prodBernoulli (fun i : F => q i) {A} := by
    intro q
    have h1 : ∫⁻ ω, ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q =
        ∫⁻ ω, ((cluster ((Subtype.val '' (Subtype.val ⁻¹' ω : Set F) : Set (Sym2 V))) o).encard :
            ℝ≥0∞) ^ p ∂law q := by
      refine lintegral_congr fun ω => ?_
      rw [himg]
    rw [h1]
    rw [← lintegral_map hgm hm]
    rw [show law q = prodBernoulli q from rfl, prodBernoulli_map_restrict]
    exact lintegral_fintype _
  rw [funext hkey]
  refine continuous_finsetSum _ fun A _ => ?_
  have hc := continuous_prodBernoulli_cylinder (ι := Sym2 V) F ({A} : Set (Set F))
  have hc' : Continuous fun q : Sym2 V → unitInterval =>
      prodBernoulli (fun i : F => q i) {A} := by
    simpa only [prodBernoulli_cylinder_apply] using hc
  exact (ENNReal.continuous_const_mul (hfin A)).comp hc'

/-- Window moments are measurable in the configuration. -/
theorem measurable_encard_cluster_inter_window_pow (o : V) (F : Finset (Sym2 V)) (p : ℕ) :
    Measurable fun ω : Config V => ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p :=
  (WindowMoments.measurable_encard_cluster_inter_window o (F : Set (Sym2 V))).pow_const p

/-- Window moments are monotone in the profile. -/
theorem monotone_lintegral_encard_cluster_inter_window_pow
    {q q' : Sym2 V → unitInterval} (h : q ≤ q') (o : V) (F : Finset (Sym2 V)) (p : ℕ) :
    (∫⁻ ω, ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q) ≤
      ∫⁻ ω, ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q' :=
  lintegral_prodBernoulli_mono q q' h (measurable_encard_cluster_inter_window_pow o F p)
    fun _ _ hω => pow_le_pow_left'
      (ENat.toENNReal_le.2 (encard_le_encard (cluster_mono (Set.inter_subset_inter_left _ hω) o)))
      p

omit [Countable V] in
/-- Window moments are bounded by the unrestricted moment at the same profile. -/
theorem lintegral_encard_cluster_inter_window_pow_le_cluster
    (q : Sym2 V → unitInterval) (o : V) (F : Finset (Sym2 V)) (p : ℕ) :
    (∫⁻ ω, ((cluster (ω ∩ (F : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q :=
  lintegral_mono fun _ω => pow_le_pow_left'
    (ENat.toENNReal_le.2 (encard_le_encard (cluster_mono Set.inter_subset_left o))) p

variable [Nonempty (Sym2 V)]

/-- **Monotone convergence in the cluster volume along an increasing profile family.** -/
theorem iSup_lintegral_encard_cluster_pow_eq_of_tendsto_profile
    {q : ℝ → Sym2 V → unitInterval} {qinf : Sym2 V → unitInterval}
    (hmono : Monotone q) (hle : ∀ r, q r ≤ qinf)
    (hconv : ∀ e, Tendsto (fun r => q r e) atTop (𝓝 (qinf e))) (o : V) (p : ℕ) :
    (⨆ r : ℝ, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (q r)) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law qinf := by
  classical
  obtain ⟨S, hSmono, hScover⟩ := WindowMoments.exists_monotone_cofinal_window (V := V)
  have hW : ∀ k : ℕ, Tendsto
      (fun r : ℝ => ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p
        ∂law (q r)) atTop
      (𝓝 (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law qinf)) :=
    fun k => ((continuous_lintegral_encard_cluster_inter_window_pow o (S k) p).tendsto qinf).comp
      (tendsto_pi_nhds.mpr hconv)
  have hWmono : ∀ k : ℕ, Monotone fun r : ℝ =>
      ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law (q r) :=
    fun k r r' hrr' => monotone_lintegral_encard_cluster_inter_window_pow (hmono hrr') o (S k) p
  have hWle : ∀ (k : ℕ) (r : ℝ),
      (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law (q r)) ≤
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (q r) :=
    fun k r => lintegral_encard_cluster_inter_window_pow_le_cluster (q r) o (S k) p
  have hMle : ∀ r : ℝ, (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (q r)) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law qinf :=
    fun r => lintegral_encard_cluster_pow_mono (hle r) o p
  refine le_antisymm (iSup_le hMle) ?_
  have hsup : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law qinf) =
      ⨆ k : ℕ, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law qinf :=
    WindowMoments.lintegral_encard_cluster_pow_eq_iSup (law qinf) o hSmono hScover p
  rw [hsup]
  refine iSup_le fun k => ?_
  have hk : (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law qinf) =
      ⨆ r : ℝ, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law (q r) :=
    tendsto_nhds_unique (hW k) (tendsto_atTop_iSup (hWmono k))
  rw [hk]
  exact iSup_le fun r => (hWle k r).trans (le_iSup (fun r : ℝ =>
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (q r)) r)

/-- **Moment convergence along an increasing profile family.** -/
theorem tendsto_lintegral_encard_cluster_pow_of_tendsto_profile
    {q : ℝ → Sym2 V → unitInterval} {qinf : Sym2 V → unitInterval}
    (hmono : Monotone q) (hle : ∀ r, q r ≤ qinf)
    (hconv : ∀ e, Tendsto (fun r => q r e) atTop (𝓝 (qinf e))) (o : V) (p : ℕ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (q r)) atTop
      (𝓝 (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law qinf)) := by
  have hMmono : Monotone fun r : ℝ =>
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (q r) :=
    fun r r' hrr' => lintegral_encard_cluster_pow_mono (hmono hrr') o p
  have h := tendsto_atTop_iSup hMmono
  rwa [iSup_lintegral_encard_cluster_pow_eq_of_tendsto_profile hmono hle hconv o p] at h

end PercLib.Percolation.Bond
