/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/MomentMonotonicity/MomentTransfer.lean`, added at source revision
`be191774d09f8bcded687f6950b5ab667972eb3d` ("Prove all-order moment comparison and window
bounds"), unchanged at branch head `1a4906a25965de1bf9440b0af188deb0420c03a6`; the source file
carries the Apache-2.0 header reproduced above.

The source proves the monotone transport once, for an arbitrary measurable increasing
functional of the configuration, through its `edgeMeasure` and the threshold map
`atParameter`.  On the canonical bond interface that general statement is already the landed
`PercLib.Probability.lintegral_prodBernoulli_mono` (`PercLib/Probability/Coupling/Monotone.lean`,
proof by the three-state coordinate coupling of `exists_prodBernoulli_monotone_coupling`); no
`edgeMeasure`, no threshold map and no `tsum` is recreated here, and the generic theorem is
not restated.

What is added is the part of the source that is not yet on the canonical interface: the
specialization to the genuine (possibly infinite) cluster cardinality `(cluster ω o).encard`,
for every natural exponent and every real exponent `p ≥ 0`, together with the finiteness
transfer that lets a finite moment of the dominating profile bound the dominated one.  The
source's `clusterVol` is the canonical `((cluster ω o).encard : ℝ≥0∞)` (`clusterVol_eq_encard`
in the source is `rfl`), so this is the same functional.

This is a proof-only module: it introduces no definition, no alternative configuration model
and no finite substitute for the true infinite cluster.  It states nothing about a cutoff law
and nothing about the critical parameter.
-/
module

public import PercLib.Probability.Coupling.Monotone
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Percolation.Bond.PathComparison
public import PercLib.Probability.OpenEventHarris
public import PercLib.Percolation.Bond.IntensityScaling

/-!
# All-order transfer of cluster moments along the monotone coupling

For ordered bond profiles `q ≤ q'`, the law `prodBernoulli q` is stochastically dominated by
`prodBernoulli q'`, so every measurable increasing functional has a smaller extended integral
under the smaller profile (`PercLib.Probability.lintegral_prodBernoulli_mono`).  The open
cluster is increasing in the configuration (`cluster_mono`), the cardinality `encard` is
monotone for inclusion, and `x ↦ x ^ p` is monotone on `ℝ≥0∞` for `p ≥ 0`; hence every
cluster moment passes from the smaller to the larger profile, with the value `⊤` allowed on
both sides.

## Main results

* `measurable_encard_cluster_rpow`, `monotone_encard_cluster_rpow`: the real power of the
  cluster cardinality is measurable and increasing in the configuration.
* `lintegral_encard_cluster_mono_of_monotone`: the transfer for an arbitrary monotone
  functional `g` of the genuine cluster cardinality.
* `lintegral_encard_cluster_rpow_mono`: `∫ |K_o|^p dP_q ≤ ∫ |K_o|^p dP_{q'}` for `p ≥ 0`.
* `lintegral_encard_cluster_pow_mono`: the same for a natural exponent `k`.
* `lintegral_encard_cluster_rpow_ne_top_of_le`, `lintegral_encard_cluster_pow_ne_top_of_le`:
  finiteness transfers from the larger profile to the smaller one, at every order;
  `lintegral_encard_cluster_rpow_le_of_le`, `…_pow_le_of_le` are the same transfer in the
  form that consumes an explicit bound.
* `law_encard_cluster_ge_mono`: the event-level face, the volume tail probability is monotone
  in the profile.
* `lintegral_encard_cluster_pow_mono_intensity`, `…_mono_intensity_of_le`: the same transport
  for the intensity interface `intensityProfile J β`, in the kernel and in the parameter.

The exponent `p = 0` is included: `x ^ (0 : ℝ) = 1` for every `x`, also for `x = ⊤`, so the
`p = 0` instance is the constant `1` and no `0 * ∞` convention enters.  The statements are
unconditional in `ℝ≥0∞`: they are not conditional bounds written as identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The functional `ω ↦ |K_o(ω)| ^ p` -/

/-- The real power of the genuine cluster cardinality is measurable, including infinite
cardinality. -/
theorem measurable_encard_cluster_rpow (o : V) (p : ℝ) :
    Measurable fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) ^ p :=
  ((Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp
    (measurable_encard_cluster o)).pow_const p

omit [Countable V] in
/-- The real power of the genuine cluster cardinality is increasing in the configuration,
for a nonnegative exponent.  Infinite cardinality is kept: `⊤ ^ p = ⊤` for `p > 0` and
`⊤ ^ 0 = 1`.  No countability is used, so the vertex type stays general. -/
theorem monotone_encard_cluster_rpow (o : V) {p : ℝ} (hp : 0 ≤ p) :
    Monotone fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) ^ p :=
  fun _ _ hω => ENNReal.rpow_le_rpow
    (ENat.toENNReal_le.2 (Set.encard_le_encard (cluster_mono hω o))) hp

/-! ### Transport of every moment from `q` to `q' ≥ q` -/

/-- **Transport for every monotone functional of the cluster volume.**  For profiles `q ≤ q'`
and every monotone `g : ℕ∞ → ℝ≥0∞`, the integral of `g (|K_o|)` is smaller under `q`.  The
value `⊤` is allowed on both sides; `ℕ∞` is countable, so no measurability of `g` is needed.
The power cases below are the instances `g = (· ^ p)`. -/
theorem lintegral_encard_cluster_mono_of_monotone {q q' : Sym2 V → unitInterval} (h : q ≤ q')
    (o : V) {g : ℕ∞ → ℝ≥0∞} (hg : Monotone g) :
    (∫⁻ ω, g ((cluster ω o).encard) ∂law q)
      ≤ ∫⁻ ω, g ((cluster ω o).encard) ∂law q' :=
  lintegral_prodBernoulli_mono q q' h
    ((measurable_of_countable g).comp (measurable_encard_cluster o))
    fun _ _ hω => hg (Set.encard_le_encard (cluster_mono hω o))

/-- **All-order moment transfer along the monotone coupling.**  For profiles `q ≤ q'` the
`p`-th extended cluster moment at `o` is smaller under `q`, for every real `p ≥ 0`.  Both
sides may be `⊤`. -/
theorem lintegral_encard_cluster_rpow_mono {q q' : Sym2 V → unitInterval} (h : q ≤ q')
    (o : V) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q)
      ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q' :=
  lintegral_prodBernoulli_mono q q' h (measurable_encard_cluster_rpow o p)
    (monotone_encard_cluster_rpow o hp)

/-- **All-order moment transfer, natural exponents.**  The source's `q`-th moment statement
(`lintegral_clusterVol_pow_mono_of_le`), on the canonical bond law and with the true cluster
cardinality. -/
theorem lintegral_encard_cluster_pow_mono {q q' : Sym2 V → unitInterval} (h : q ≤ q')
    (o : V) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law q)
      ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law q' := by
  simpa only [ENNReal.rpow_natCast] using
    lintegral_encard_cluster_rpow_mono h o (p := (k : ℝ)) (Nat.cast_nonneg k)

/-! ### Finiteness transfer -/

/-- **Finiteness transfer, real exponents.**  A finite `p`-th moment of the dominating
profile gives a finite `p`-th moment of the dominated one, for every `p ≥ 0`.  This is the
step that consumes a moment bound for the dominating law; it produces none itself. -/
theorem lintegral_encard_cluster_rpow_ne_top_of_le {q q' : Sym2 V → unitInterval}
    (h : q ≤ q') (o : V) {p : ℝ} (hp : 0 ≤ p)
    (hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q') ≠ ⊤) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (lintegral_encard_cluster_rpow_mono h o hp)

/-- **Finiteness transfer, natural exponents.** -/
theorem lintegral_encard_cluster_pow_ne_top_of_le {q q' : Sym2 V → unitInterval}
    (h : q ≤ q') (o : V) (k : ℕ)
    (hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law q') ≠ ⊤) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law q) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (lintegral_encard_cluster_pow_mono h o k)

/-- **Consumption form, real exponents.**  An explicit bound for the `p`-th moment of the
dominating profile bounds the `p`-th moment of the dominated one. -/
theorem lintegral_encard_cluster_rpow_le_of_le {q q' : Sym2 V → unitInterval} (h : q ≤ q')
    (o : V) {p : ℝ} (hp : 0 ≤ p) {C : ℝ≥0∞}
    (hC : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q') ≤ C) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q) ≤ C :=
  (lintegral_encard_cluster_rpow_mono h o hp).trans hC

/-- **Consumption form, natural exponents.** -/
theorem lintegral_encard_cluster_pow_le_of_le {q q' : Sym2 V → unitInterval} (h : q ≤ q')
    (o : V) (k : ℕ) {C : ℝ≥0∞}
    (hC : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law q') ≤ C) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law q) ≤ C :=
  (lintegral_encard_cluster_pow_mono h o k).trans hC

/-! ### The cluster-volume tail event -/

/-- **Cluster-volume tails are monotone in the profile.**  For profiles `q ≤ q'` and every
threshold `n : ℕ∞`, the probability that the cluster of `o` has at least `n` vertices is
smaller under `q`.  This is the event-level face of the moment transfer. -/
theorem law_encard_cluster_ge_mono {q q' : Sym2 V → unitInterval} (h : q ≤ q') (o : V)
    (n : ℕ∞) :
    law q {ω | n ≤ (cluster ω o).encard} ≤ law q' {ω | n ≤ (cluster ω o).encard} :=
  prodBernoulli_mono_event q q' h (measurableSet_le_encard_cluster o n)
    (isUpperSet_le_encard_cluster o n)

/-! ### The intensity interface -/

/-- A larger kernel has larger cluster moments at every order, at fixed intensity. -/
theorem lintegral_encard_cluster_pow_mono_intensity {J J' : Sym2 V → ℝ≥0} (h : J ≤ J')
    (β : ℝ≥0) (o : V) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile J β))
      ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile J' β) :=
  lintegral_encard_cluster_pow_mono (intensityProfile_le_of_le h β) o k

/-- A larger intensity has larger cluster moments at every order, for a fixed kernel. -/
theorem lintegral_encard_cluster_pow_mono_intensity_of_le {J : Sym2 V → ℝ≥0} {β β' : ℝ≥0}
    (h : β ≤ β') (o : V) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile J β))
      ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile J β') :=
  lintegral_encard_cluster_pow_mono (intensityProfile_mono J h) o k

/-! ### Consistency and non-vacuity -/

-- The exponent `p = 1` is the committed `chi_mono`
-- (`PercLib/Percolation/Bond/ProfileRegularity.lean`), so the new statement generalizes a
-- landed one instead of renaming it.
example {q q' : Sym2 V → unitInterval} (h : q ≤ q') (o : V) : chi q o ≤ chi q' o := by
  simpa only [chi, ENNReal.rpow_one] using lintegral_encard_cluster_rpow_mono h o
    (p := 1) zero_le_one

-- `p = 0` is genuinely allowed by the transport: both sides are the constant moment `1`,
-- even though the cluster may be infinite on a set of positive measure.
example {q : Sym2 V → unitInterval} (o : V) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (0 : ℝ) ∂law q) = 1 := by
  simp

-- The transfer is not vacuous: on `ℕ` the closed profile has cluster volume one at every
-- vertex and the open profile has an infinite cluster, so the `p = 1` instance is strict.
-- (`chi (fun _ => 1) 0 = ⊤` is the committed example in
-- `PercLib/Percolation/Bond/Susceptibility.lean`.)
example : chi (fun _ : Sym2 ℕ => (0 : unitInterval)) 0
    < chi (fun _ : Sym2 ℕ => (1 : unitInterval)) 0 := by
  have h₁ : chi (fun _ : Sym2 ℕ => (0 : unitInterval)) 0 = 1 := by
    simp [chi, law, PercLib.Probability.prodBernoulli_const, cluster_empty]
  have h₂ : chi (fun _ : Sym2 ℕ => (1 : unitInterval)) 0 = ⊤ := by
    have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := by
      ext y
      simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]
    simp [chi, law, PercLib.Probability.prodBernoulli_const, hc]
  rw [h₁, h₂]
  exact ENNReal.one_lt_top

-- The finiteness-transfer hypothesis is satisfiable at `p = 0` for every profile, since the
-- zero-th moment of any cluster is one.
example {q : Sym2 V → unitInterval} (o : V) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (0 : ℝ) ∂law q) ≠ ⊤ := by
  simp

end PercLib.Percolation.Bond
