/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files `PercLib/CriticalLRP/MassTransportI41.lean` and
`PercLib/CriticalLRP/CountableProduct/MassTransport.lean`, contributed by `yujinhkim`. Licence:
Apache-2.0, as declared in those files' headers and in `third_party/critical-lrp/NOTICE.md` of that
commit (upstream origin `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`, not independently verified). Changes: the second model
of the source (`shiftConfig`, `Config`, `Connects`, `clusterVol`, `clusterVolR`, `configIndicator`,
`cutoffSymKernel`, `russoLHS`/`russoRHS`) is replaced by the bond interface of this library
(`Config`, `conn`, `cluster`, `law`, `intensityProfile`, `cutoffKernel`); the state shift
`shiftConfig t ω` is the push-forward `Sym2.map (· + t) '' ω`; the cluster volume is
`(cluster ω x).encard`; every integrand is written out instead of being introduced by a definition;
the source's `linfNorm` becomes `N (Int.cast ∘ z)`;
focused imports; `autoImplicit` off.
Lemma I.2.6 specialization: `PercLib/CriticalLRP/Tightness/LemmaI26Cutoff.lean` is also
ported below. `edianMaxVol` is the existing `tightnessScale`, and `FiniteVolume.box d n` is
`Finset.Icc (-n) n`; its real-integral form takes `ENNReal.toReal` of the cluster cardinality.
The stronger statements below need no `AntitoneOn` or positive-scale premise for Lemma I.2.6,
because `cutoffKernel` already truncates at zero. The balls in the Russo/mass-transport
statements use `N (Int.cast ∘ z)` for the chosen norm `N`, corresponding to the source's
`linfNorm`; the general identities take a `Seminorm`, and the cutoff instances use a `ModelNorm`.

-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Models.LongRange.InfiniteVolumeRusso
public import PercLib.Models.LongRange.QuantileMoments
public import PercLib.Models.LongRange.RootIndependence
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.MassTransportTuple
public import Mathlib.Data.Set.Card

/-!
# Mass transport for cluster volumes on `ℤ^d`

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1 and its
mass-transport step, on the bond model of this library.

For a law `μ` on configurations of `ℤ^d = Fin d → ℤ` that is invariant under the shift
`ω ↦ Sym2.map (· + t) '' ω` and a nonnegative measurable kernel `g` with
`g (x + t) (shift t ω) = g x ω`:

* `lintegral_conn_mul_translate`: the per-site transport
  `∫ 1(0 ↔ x) g x dμ = ∫ 1(-x ↔ 0) g 0 dμ`;
* `lintegral_cluster_massTransport`: `∫ ∑_{x ∈ K_0} g x dμ = ∫ |K_0| g 0 dμ`;
* `lintegral_cluster_ball_massTransport`: the same with `g x = ∑_{w ∈ S} φ x w`, the form in
  which the `x`-anchored ball `B_r(x)` is replaced by the origin-anchored `B_r`.

Everything is `ℝ≥0∞`-valued, so no summability or integrability hypothesis is needed, and the
identities are unconditional in the cluster volume.

## Main results

Provenance: `PercLib/CriticalLRP/CountableProduct/MassTransport.lean` of the source above
(`lintegral_connects_mul_shift`, `lintegral_cluster_massTransport`,
`lintegral_cluster_ball_massTransport`), with the same proof, rewritten on the bond interface.
The cutoff Russo integrands and binomial steps are adapted from `MassTransportI41.lean`;
Lemma I.2.6 is adapted from `Tightness/LemmaI26Cutoff.lean` as described above.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

open PercLib.Analysis
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis

variable {d : ℕ}

/-! ### Translation of configurations -/

/-- The shift of a configuration by `t` is `ω ↦ Sym2.map (· + t) '' ω`. -/
theorem conn_translate_indicator (t a b : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    (conn (a + t) (b + t)).indicator (fun _ => (1 : ℝ≥0∞))
        (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω)
      = (conn a b).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases h : ω ∈ conn a b
  · have h' : Sym2.map (fun x : Fin d → ℤ => x + t) '' ω ∈ conn (a + t) (b + t) :=
      (image_mem_conn_iff (Equiv.addRight t) ω a b).2 h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : Sym2.map (fun x : Fin d → ℤ => x + t) '' ω ∉ conn (a + t) (b + t) :=
      fun hh => h ((image_mem_conn_iff (Equiv.addRight t) ω a b).1 hh)
    rw [ite_eq_right h', ite_eq_right h]

/-- The cluster of `x + t` in the shifted configuration is the translate of the cluster of `x`. -/
theorem cluster_translate (t x : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (x + t) =
      (fun y : Fin d → ℤ => y + t) '' cluster ω x :=
  cluster_image (Equiv.addRight t) ω x

/-- Cluster volumes are preserved by a translation of the configuration. -/
theorem encard_cluster_translate (t x : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    (cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (x + t)).encard =
      (cluster ω x).encard :=
  encard_cluster_image (Equiv.addRight t) ω x

/-- The indicator of a connection event is measurable. -/
theorem measurable_conn_indicator (a b : Fin d → ℤ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      (conn a b).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
  measurable_const.indicator (measurableSet_conn a b)

/-- The `ℝ≥0∞`-valued cluster volume is measurable. -/
theorem measurable_encard_cluster_coe (x : Fin d → ℤ) :
    Measurable fun ω : Config (Fin d → ℤ) => ((cluster ω x).encard : ℝ≥0∞) :=
  measurable_from_top.comp (measurable_encard_cluster x)

/-- Lower integrals against a shifted law. -/
theorem lintegral_map_shift (μ : Measure (Config (Fin d → ℤ))) (t : Fin d → ℤ)
    (f : Config (Fin d → ℤ) → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂(μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω))
      = ∫⁻ ω, f (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) ∂μ :=
  PercLib.Percolation.Bond.lintegral_map_image_sym2Map (Equiv.addRight t) μ f

/-- A profile invariant under every translation has a law invariant under every shift. -/
theorem law_map_translate (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (t : Fin d → ℤ) :
    (law q).map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = law q := by
  simpa [Equiv.coe_addRight] using law_map_addRight_eq q hq t

/-! ### Per-site transport -/

/-- **Per-site transport.** For a shift-invariant law, the `μ`-integral of
`1(0 ↔ x) g x` does not depend on `x`, once `g` is re-indexed at the origin. -/
theorem lintegral_conn_mul_translate (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (g : (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞) (hg : ∀ x, Measurable (g x))
    (hcov : ∀ (x t : Fin d → ℤ) (ω),
      g (x + t) (Sym2.map (fun y : Fin d → ℤ => y + t) '' ω) = g x ω)
    (x : Fin d → ℤ) :
    ∫⁻ ω, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω ∂μ
      = ∫⁻ ω, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω * g 0 ω ∂μ := by
  classical
  have hmeas : Measurable fun ω : Config (Fin d → ℤ) =>
      (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω :=
    (measurable_conn_indicator 0 x).mul (hg x)
  have hind : ∀ ω : Config (Fin d → ℤ),
      (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞))
          (Sym2.map (fun y : Fin d → ℤ => y + x) '' ω)
        = (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    have h := conn_translate_indicator x (-x) 0 ω
    rw [neg_add_cancel, zero_add] at h
    exact h
  have hcovx : ∀ ω : Config (Fin d → ℤ),
      g x (Sym2.map (fun y : Fin d → ℤ => y + x) '' ω) = g 0 ω := by
    intro ω
    have h := hcov 0 x ω
    rw [zero_add] at h
    exact h
  calc ∫⁻ ω, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω ∂μ
      = ∫⁻ ω, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω
          ∂(μ.map (fun ω => Sym2.map (fun y : Fin d → ℤ => y + x) '' ω)) := by
        rw [hμ x]
    _ = ∫⁻ ω, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞))
            (Sym2.map (fun y : Fin d → ℤ => y + x) '' ω) *
            g x (Sym2.map (fun y : Fin d → ℤ => y + x) '' ω) ∂μ :=
        PercLib.Percolation.Bond.lintegral_map_image_sym2Map (Equiv.addRight x) μ _
    _ = ∫⁻ ω, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω * g 0 ω ∂μ :=
        lintegral_congr fun ω => by rw [hind ω, hcovx ω]

/-- **Mass-transport principle for the cluster volume.** For a shift-invariant law `μ` and a
nonnegative measurable shift-covariant kernel `g`,
`∫ ∑_{x ∈ K_0} g x dμ = ∫ |K_0| g 0 dμ`, where `∑_{x ∈ K_0}` is written
`∑' x, 1(0 ↔ x) · g x` and `|K_0|` is `(cluster ω 0).encard`. -/
theorem lintegral_cluster_massTransport (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (g : (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞) (hg : ∀ x, Measurable (g x))
    (hcov : ∀ (x t : Fin d → ℤ) (ω),
      g (x + t) (Sym2.map (fun y : Fin d → ℤ => y + t) '' ω) = g x ω) :
    ∫⁻ ω, (∑' x, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω) ∂μ
      = ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) * g 0 ω ∂μ := by
  classical
  have hterm : ∀ x : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) =>
      (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω :=
    fun x => (measurable_conn_indicator 0 x).mul (hg x)
  have hstep : ∀ x : Fin d → ℤ,
      ∫⁻ ω, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω ∂μ
        = ∫⁻ ω, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω * g 0 ω ∂μ :=
    fun x => lintegral_conn_mul_translate μ hμ g hg hcov x
  have hsum : ∀ ω : Config (Fin d → ℤ),
      (∑' x, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω)
        = ((cluster ω 0).encard : ℝ≥0∞) := by
    intro ω
    rw [encard_cluster_eq_tsum ω 0]
    calc (∑' x, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω)
        = ∑' x, (conn 0 (-x)).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
          tsum_congr fun x => by rw [conn_symm]
      _ = ∑' y, (conn 0 y).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
          Equiv.tsum_eq (Equiv.neg (Fin d → ℤ))
            (fun y => (conn 0 y).indicator (fun _ => (1 : ℝ≥0∞)) ω)
  calc ∫⁻ ω, (∑' x, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω) ∂μ
      = ∑' x, ∫⁻ ω, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * g x ω ∂μ :=
        lintegral_tsum fun x => (hterm x).aemeasurable
    _ = ∑' x, ∫⁻ ω, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω * g 0 ω ∂μ :=
        tsum_congr hstep
    _ = ∫⁻ ω, (∑' x, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω * g 0 ω) ∂μ :=
        (lintegral_tsum fun x =>
          ((measurable_conn_indicator (-x) 0).mul (hg 0)).aemeasurable).symm
    _ = ∫⁻ ω, (∑' x, (conn (-x) 0).indicator (fun _ => (1 : ℝ≥0∞)) ω) * g 0 ω ∂μ :=
        lintegral_congr fun ω => ENNReal.tsum_mul_right
    _ = ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) * g 0 ω ∂μ :=
        lintegral_congr fun ω => by rw [hsum ω]

/-- **Mass transport of the `x`-anchored ball.** With the ball stored as a finite set `S` of
displacements and the integrand written in the relative coordinate `w = y - x`,
`∫ ∑_{x ∈ K_0} ∑_{w ∈ S} φ x w dμ = ∫ |K_0| ∑_{w ∈ S} φ 0 w dμ`. -/
theorem lintegral_cluster_ball_massTransport (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (S : Finset (Fin d → ℤ))
    (φ : (Fin d → ℤ) → (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞)
    (hφ : ∀ (x w : Fin d → ℤ), Measurable (φ x w))
    (hφcov : ∀ (x t w : Fin d → ℤ) (ω),
      φ (x + t) w (Sym2.map (fun y : Fin d → ℤ => y + t) '' ω) = φ x w ω) :
    ∫⁻ ω, (∑' x, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * (∑ w ∈ S, φ x w ω)) ∂μ
      = ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) * (∑ w ∈ S, φ 0 w ω) ∂μ := by
  have hg : ∀ x : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) => ∑ w ∈ S, φ x w ω :=
    fun x => Finset.measurable_sum S fun w _ => hφ x w
  have hcov : ∀ (x t : Fin d → ℤ) (ω : Config (Fin d → ℤ)),
      (∑ w ∈ S, φ (x + t) w (Sym2.map (fun y : Fin d → ℤ => y + t) '' ω))
        = ∑ w ∈ S, φ x w ω := by
    intro x t ω
    exact Finset.sum_congr rfl fun w _ => hφcov x t w ω
  exact lintegral_cluster_massTransport μ hμ (fun x ω => ∑ w ∈ S, φ x w ω) hg hcov

/-! ### The Russo triple weight of Lemma I.4.1

The weight of the proof of Lemma I.4.1 is
`1(a ↔ b) · 1(N (c − b) ≤ r) · 1(b ↮ c) · ((|K_b| + |K_c|)^p − |K_b|^p)`,
written out below at each occurrence (no definition is introduced). -/

/-- A set indicator pulled back along a shift of the configuration. -/
theorem indicator_image_translate {s s' : Set (Config (Fin d → ℤ))} {t : Fin d → ℤ}
    (h : ∀ ω : Config (Fin d → ℤ),
      Sym2.map (fun x : Fin d → ℤ => x + t) '' ω ∈ s' ↔ ω ∈ s)
    (ω : Config (Fin d → ℤ)) :
    s'.indicator (fun _ => (1 : ℝ≥0∞)) (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω)
      = s.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hω : ω ∈ s
  · rw [ite_eq_left ((h ω).2 hω), ite_eq_left hω]
  · rw [ite_eq_right (fun hh => hω ((h ω).1 hh)), ite_eq_right hω]

/-- A connection indicator is shift covariant. -/
theorem compl_conn_translate_indicator (t a b : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    (conn (a + t) (b + t))ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
        (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω)
      = (conn a b)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω :=
  indicator_image_translate (fun ω => not_congr (image_mem_conn_iff (Equiv.addRight t) ω a b)) ω

/-- The cluster-volume increment is shift invariant. -/
theorem russo_volume_translate (p : ℕ) (t b c : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    ((((cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (b + t)).encard : ℝ≥0∞) +
        ((cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (c + t)).encard : ℝ≥0∞)) ^ p -
        ((cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (b + t)).encard : ℝ≥0∞) ^ p)
      = ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
        ((cluster ω b).encard : ℝ≥0∞) ^ p) := by
  rw [encard_cluster_translate, encard_cluster_translate]

/-- **Shift covariance of the Russo triple weight.** The weight of the proof of Lemma I.4.1 is
invariant under a simultaneous shift of the configuration and the three vertices. -/
theorem russo_triple_translate (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) (t a b c : Fin d → ℤ)
    (ω : Config (Fin d → ℤ)) :
    (conn (a + t) (b + t)).indicator (fun _ => (1 : ℝ≥0∞))
          (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) *
        (if N (Int.cast ∘ ((c + t) - (b + t))) ≤ r then 1 else 0) *
        (conn (b + t) (c + t))ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
          (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) *
        ((((cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (b + t)).encard : ℝ≥0∞) +
            ((cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (c + t)).encard : ℝ≥0∞)) ^ p -
            ((cluster (Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) (b + t)).encard : ℝ≥0∞) ^ p)
      = (conn a b).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (if N (Int.cast ∘ (c - b)) ≤ r then 1 else 0) *
        (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
          ((cluster ω b).encard : ℝ≥0∞) ^ p) := by
  have h4 : (c + t) - (b + t) = c - b := by abel
  rw [conn_translate_indicator, h4, compl_conn_translate_indicator, russo_volume_translate]

/-- The Russo triple weight is measurable in the configuration. -/
theorem measurable_russo_triple (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) (a b c : Fin d → ℤ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      (conn a b).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (if N (Int.cast ∘ (c - b)) ≤ r then 1 else 0) *
        (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
          ((cluster ω b).encard : ℝ≥0∞) ^ p) := by
  have hI2 : Measurable fun ω : Config (Fin d → ℤ) =>
      (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    measurable_const.indicator (measurableSet_conn b c).compl
  have hinc : Measurable fun ω : Config (Fin d → ℤ) =>
      (((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
        ((cluster ω b).encard : ℝ≥0∞) ^ p :=
    (((measurable_encard_cluster_coe b).add (measurable_encard_cluster_coe c)).pow_const p).sub
      ((measurable_encard_cluster_coe b).pow_const p)
  exact ((measurable_conn_indicator a b).mul measurable_const).mul hI2 |>.mul hinc

/-! ### The deterministic mass-transport step -/

/-- **Mass-transport principle, three-point form.** For a diagonally invariant
`F : G → G → G → ℝ≥0∞`, the sum over the triples with second coordinate `0` equals the sum
over the triples with first coordinate `0`. -/
theorem tsum_mass_transport_three {G : Type*} [AddCommGroup G] [Countable G]
    (F : G → G → G → ℝ≥0∞)
    (hF : ∀ (a b c t : G), F (a + t) (b + t) (c + t) = F a b c) :
    (∑' b, ∑' c, F 0 b c) = ∑' a, ∑' c, F a 0 c := by
  have h1 : (∑' p : G × G, F 0 p.1 p.2) = ∑' b, ∑' c, F 0 b c := ENNReal.tsum_prod'
  have h2 : (∑' p : G × G, F p.1 0 p.2) = ∑' a, ∑' c, F a 0 c := ENNReal.tsum_prod'
  rw [← h1, ← h2]
  have hstep : ∀ p : G × G, F 0 p.1 p.2 = F (-p.1) 0 (p.2 - p.1) := by
    intro p
    have h := hF (-p.1) 0 (p.2 - p.1) p.1
    simpa using h
  rw [tsum_congr hstep]
  let e : G × G ≃ G × G :=
    { toFun := fun p => (-p.1, p.2 - p.1)
      invFun := fun q => (-q.1, q.2 - q.1)
      left_inv := by
        rintro ⟨b, c⟩
        simp only [Prod.mk.injEq]
        constructor <;> abel
      right_inv := by
        rintro ⟨b, c⟩
        simp only [Prod.mk.injEq]
        constructor <;> abel }
  calc (∑' p : G × G, F (-p.1) 0 (p.2 - p.1))
      = ∑' p : G × G, F (e p).1 0 (e p).2 := by
        refine tsum_congr fun p => ?_
        rw [show (e p).1 = -p.1 from rfl, show (e p).2 = p.2 - p.1 from rfl]
    _ = ∑' q : G × G, F q.1 0 q.2 := Equiv.tsum_eq e (fun q => F q.1 0 q.2)

/-- **The mass-transport step of Lemma I.4.1.** For any shift-invariant law `μ` on
configurations of `ℤ^d`, the triple weight summed with the middle vertex at the origin equals
the same weight summed with the first vertex at the origin. -/
theorem massTransport_russo (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    (∑' b, ∑' c, ∫⁻ ω,
        (conn 0 b).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - b)) ≤ r then 1 else 0) *
          (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω b).encard : ℝ≥0∞) ^ p) ∂μ)
      = ∑' a, ∑' c, ∫⁻ ω,
        (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
          (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p) ∂μ := by
  refine tsum_mass_transport_three
    (fun a b c => ∫⁻ ω,
      (conn a b).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (if N (Int.cast ∘ (c - b)) ≤ r then 1 else 0) *
        (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
          ((cluster ω b).encard : ℝ≥0∞) ^ p) ∂μ) ?_
  intro a b c t
  conv_lhs => rw [← hμ t]
  rw [lintegral_map_shift]
  exact lintegral_congr fun ω => russo_triple_translate p N r t a b c ω

/-- Interchange of the lower integral with the double sum, first-variable form. -/
theorem lintegral_russo_triple_tsum (μ : Measure (Config (Fin d → ℤ))) (p : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    ∫⁻ ω, (∑' b, ∑' c,
        (conn 0 b).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - b)) ≤ r then 1 else 0) *
          (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω b).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∑' b, ∑' c, ∫⁻ ω,
        (conn 0 b).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - b)) ≤ r then 1 else 0) *
          (conn b c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω b).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω b).encard : ℝ≥0∞) ^ p) ∂μ := by
  rw [lintegral_tsum]
  · exact tsum_congr fun b => by
      rw [lintegral_tsum fun c => (measurable_russo_triple p N r 0 b c).aemeasurable]
  · exact fun b => (Measurable.tsum fun c => measurable_russo_triple p N r 0 b c).aemeasurable

/-- Interchange of the lower integral with the double sum, second-variable form. -/
theorem lintegral_russo_triple_tsum' (μ : Measure (Config (Fin d → ℤ))) (p : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    ∫⁻ ω, (∑' a, ∑' c,
        (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
          (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∑' a, ∑' c, ∫⁻ ω,
        (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
          (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p) ∂μ := by
  rw [lintegral_tsum]
  · exact tsum_congr fun a => by
      rw [lintegral_tsum fun c => (measurable_russo_triple p N r a 0 c).aemeasurable]
  · exact fun a => (Measurable.tsum fun c => measurable_russo_triple p N r a 0 c).aemeasurable


/-! ### The paper's Russo integrands -/

/-- Connected vertices have equal cluster volume, using the general bond-model theorem. -/
theorem encard_cluster_eq_of_mem_conn {ω : Config (Fin d → ℤ)} {x y : Fin d → ℤ}
    (h : ω ∈ conn x y) : (cluster ω x).encard = (cluster ω y).encard := by
  rw [cluster_eq_of_mem_conn h]

/-- The volume of the cluster of `v` is the sum of the connection indicators. Reindexed form. -/
theorem tsum_conn_indicator_eq_encard (v : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    (∑' a, (conn a v).indicator (fun _ => (1 : ℝ≥0∞)) ω) = ((cluster ω v).encard : ℝ≥0∞) := by
  rw [encard_cluster_eq_tsum ω v]
  exact tsum_congr fun a => by rw [conn_symm]

/-- On the event `0 ↔ x`, the event `x ↮ y` carries the same indicator at `ω` as `0 ↮ y`. -/
theorem compl_conn_indicator_congr {ω : Config (Fin d → ℤ)} {x : Fin d → ℤ}
    (h : ω ∈ conn 0 x) (y : Fin d → ℤ) :
    (conn x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω
      = (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  have hx0 : ω ∈ conn x 0 := by rwa [conn_symm] at h
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hxy : ω ∈ conn x y
  · have h0y : ω ∈ conn 0 y := conn_trans h hxy
    rw [ite_eq_right (by simp [hxy]), ite_eq_right (by simp [h0y])]
  · have h0y : ω ∉ conn 0 y := fun hh => hxy (conn_trans hx0 hh)
    rw [ite_eq_left (by simp [hxy]), ite_eq_left (by simp [h0y])]

/-- **The left-hand side of the Russo identity, as a triple sum.** -/
theorem russoLHS_eq_triple (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) (ω : Config (Fin d → ℤ)) :
    (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p))
      = ∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω x).encard : ℝ≥0∞) ^ p) := by
  classical
  refine tsum_congr fun x => ?_
  by_cases hx : ω ∈ conn 0 x
  · have hx' : ω ∈ conn x 0 := by rwa [conn_symm] at hx
    have hvol : ((cluster ω x).encard : ℝ≥0∞) = ((cluster ω 0).encard : ℝ≥0∞) := by
      rw [encard_cluster_eq_of_mem_conn hx']
    refine tsum_congr fun y => ?_
    rw [compl_conn_indicator_congr hx y, ← hvol]
  · have h0 : (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
      simp [hx]
    simp [h0]

/-- **The right-hand side of the Russo identity, as a triple sum.** -/
theorem russoRHS_eq_triple (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) (ω : Config (Fin d → ℤ)) :
    (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
      = ∑' a, ∑' c,
        (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
          (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p) := by
  have hfac : ∀ a : Fin d → ℤ,
      (∑' c,
          (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
            (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
        = (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∑' c,
            (if N (Int.cast ∘ c) ≤ r then 1 else 0) *
              (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p) := by
    intro a
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun c => ?_
    rw [sub_zero]
    ac_rfl
  calc (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
      = (∑' a, (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω) *
          ∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p) := by
        rw [tsum_conn_indicator_eq_encard]
    _ = ∑' a, (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∑' c,
            (if N (Int.cast ∘ c) ≤ r then 1 else 0) *
              (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p) := by
        rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' c,
        (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
          (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p) :=
        tsum_congr fun a => (hfac a).symm

/-- **Lemma I.4.1, mass-transport step.** For any shift-invariant law on configurations of
`ℤ^d`, the expectation of the Russo integrand
`∑_{x ∈ K_0} ∑_{y ∈ B_r(x)} 1(y ∉ K_0) ((|K_0| + |K_y|)^p − |K_0|^p)` equals the expectation of
`|K_0| ∑_{y ∈ B_r} 1(y ∉ K_0) ((|K_0| + |K_y|)^p − |K_0|^p)`.

This is the `ℝ≥0∞` form: no summability or finiteness of moments is assumed, and the truncated
subtraction of `ℝ≥0∞` agrees with the real difference on the event that the clusters are finite. -/
theorem i41_massTransport (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    ∫⁻ ω, (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ := by
  calc ∫⁻ ω, (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∫⁻ ω, (∑' x, ∑' y,
          (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
            (conn x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω x).encard : ℝ≥0∞) ^ p)) ∂μ :=
        lintegral_congr fun ω => russoLHS_eq_triple p N r ω
    _ = ∑' x, ∑' y, ∫⁻ ω,
          (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
            (conn x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω x).encard : ℝ≥0∞) ^ p) ∂μ :=
        lintegral_russo_triple_tsum μ p N r
    _ = ∑' a, ∑' c, ∫⁻ ω,
          (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
            (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p) ∂μ :=
        massTransport_russo μ hμ p N r
    _ = ∫⁻ ω, (∑' a, ∑' c,
          (conn a 0).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (if N (Int.cast ∘ (c - 0)) ≤ r then 1 else 0) *
            (conn 0 c)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω c).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ :=
        (lintegral_russo_triple_tsum' μ p N r).symm
    _ = ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ :=
        lintegral_congr fun ω => (russoRHS_eq_triple p N r ω).symm

/-! ### The binomial step of Lemma I.4.1 -/

/-- **The single-site binomial identity in `ℝ≥0∞` form**: for finite `a, b ≥ 0`,
`a ((a + b)^p − a^p) = ∑_{ℓ<p} C(p,ℓ) a^{ℓ+1} b^{p−ℓ}`, read through `ℝ≥0∞`. -/
theorem ofReal_mul_pow_sub_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    ENNReal.ofReal a * ENNReal.ofReal ((a + b) ^ p - a ^ p)
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ENNReal.ofReal a ^ (ℓ + 1) *
          ENNReal.ofReal b ^ (p - ℓ) := by
  have hdiff : 0 ≤ (a + b) ^ p - a ^ p := by
    have hle : a ^ p ≤ (a + b) ^ p := pow_le_pow_left₀ ha (by linarith) p
    linarith
  rw [← ENNReal.ofReal_mul ha,
    PercLib.Probability.mul_pow_sub_pow_eq_sum_choose,
    ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  · intro ℓ _
    positivity

/-- **The single-site binomial identity**, with the volume increments as `ℝ≥0∞` numbers.
Finiteness of the two volumes is all that is needed. -/
theorem mul_pow_sub_pow_eq_sum_choose_ennreal {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (p : ℕ) :
    A * ((A + B) ^ p - A ^ p)
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) * B ^ (p - ℓ) := by
  have ha : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
    ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ A.toReal + B.toReal),
    ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ A.toReal ^ p)]
  exact ofReal_mul_pow_sub_pow A.toReal B.toReal ha hb p

/-- **The pointwise binomial form of (I.4.1)** on the event that every cluster is finite. -/
theorem russoRHS_eq_binomial_of_finite {ω : Config (Fin d → ℤ)}
    (h : ∀ v : Fin d → ℤ, ((cluster ω v).encard : ℝ≥0∞) ≠ ⊤) (p : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          ∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) := by
  have hA0 : ((cluster ω 0).encard : ℝ≥0∞) ≠ ⊤ := h 0
  have hbin : ∀ y : Fin d → ℤ,
      ((cluster ω 0).encard : ℝ≥0∞) *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)
        = ∑ ℓ ∈ Finset.range p,
            (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) :=
    fun y => mul_pow_sub_pow_eq_sum_choose_ennreal hA0 (h y) p
  calc (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
      = ∑' y,
          ((if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
            (((cluster ω 0).encard : ℝ≥0∞) *
              ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p)) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun y => by ac_rfl
    _ = ∑' y,
          ((if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
            ∑ ℓ ∈ Finset.range p,
              (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
                ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) :=
        tsum_congr fun y => by rw [hbin y]
    _ = ∑' y, ∑ ℓ ∈ Finset.range p,
          ((if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
            ((p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) :=
        tsum_congr fun y => Finset.mul_sum ..
    _ = ∑ ℓ ∈ Finset.range p,
          (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
            ∑' y,
              ((if N (Int.cast ∘ y) ≤ r then 1 else 0) *
                (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
                ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) := by
        rw [Summable.tsum_finsetSum (s := Finset.range p) (fun ℓ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun y => by ac_rfl

/-- **Lemma I.4.1 in binomial form.** After the mass-transport step, the expectation of
`|K_0| ∑_{y ∈ B_r} 1(y ∉ K_0) ((|K_0| + |K_y|)^p − |K_0|^p)` is the binomial sum
`∑_{ℓ<p} C(p,ℓ) E[ |K_0|^{ℓ+1} ∑_{y ∈ B_r} 1(y ∉ K_0) |K_y|^{p−ℓ} ]`.

The only hypothesis is that clusters are almost surely finite. No moment finiteness is assumed:
the identity is in `ℝ≥0∞`. -/
theorem i41_binomial (μ : Measure (Config (Fin d → ℤ)))
    (hfin : ∀ v : Fin d → ℤ,
      μ {ω : Config (Fin d → ℤ) | ((cluster ω v).encard : ℝ≥0∞) = ⊤} = 0)
    (p : ℕ) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ := by
  have htsum : ∀ ℓ : ℕ, Measurable fun ω : Config (Fin d → ℤ) =>
      ∑' y,
        (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) := by
    intro ℓ
    refine Measurable.tsum fun y => ?_
    exact (measurable_const.mul
      (measurable_const.indicator (measurableSet_conn 0 y).compl)).mul
      ((measurable_encard_cluster_coe y).pow_const (p - ℓ))
  have hAS : ∀ ℓ : ℕ, Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) :=
    fun ℓ => ((measurable_encard_cluster_coe 0).pow_const (ℓ + 1)).mul (htsum ℓ)
  have hsummand : ∀ ℓ : ℕ, Measurable fun ω : Config (Fin d → ℤ) =>
      ((p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1)) *
        (∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) :=
    fun ℓ => (measurable_const.mul ((measurable_encard_cluster_coe 0).pow_const (ℓ + 1))).mul
      (htsum ℓ)
  have hae : ∀ᵐ ω ∂μ, ∀ v : Fin d → ℤ, ((cluster ω v).encard : ℝ≥0∞) ≠ ⊤ := by
    rw [ae_all_iff]
    intro v
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin v)] with ω h
    exact h
  calc ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∫⁻ ω, (∑ ℓ ∈ Finset.range p,
          (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
            ∑' y,
              (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
                (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
                ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω h
        exact russoRHS_eq_binomial_of_finite h p N r
    _ = ∑ ℓ ∈ Finset.range p, ∫⁻ ω,
          (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
            ∑' y,
              (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
                (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
                ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) ∂μ :=
        lintegral_finsetSum _ fun ℓ _ => hsummand ℓ
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        conv_lhs =>
          enter [2, ω]
          rw [mul_assoc]
        rw [lintegral_const_mul]
        exact hAS ℓ

/-! ### The cut-off family -/

/-- The law of the cut-off kernel is shift invariant, at every norm, profile, scale and
intensity. -/
theorem law_cutoffKernel_map_translate {N : ModelNorm (Fin d → ℝ)} (K : ℝ → ℝ) (r : ℝ)
    (β : ℝ≥0) (t : Fin d → ℤ) :
    (law (intensityProfile (cutoffKernel (d := d) N K r) β)).map
        (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω)
      = law (intensityProfile (cutoffKernel (d := d) N K r) β) :=
  law_map_translate (intensityProfile (cutoffKernel (d := d) N K r) β)
    (intensityProfile_map_add (cutoffKernel_map_add (d := d) N K r) β) t

/-- **The mass-transport step of Lemma I.4.1 for the cut-off model**: for the cut-off kernel of
Definition I.1.5 on `ℤ^d`, any norm, any profile, any scale and any intensity, the expectation of
the Russo integrand equals the expectation of
`|K_0| ∑_{y ∈ B_r} 1(y ∉ K_0) ((|K_0| + |K_y|)^p − |K_0|^p)`.

No finiteness of moments is assumed: the identity is in `ℝ≥0∞`. -/
theorem i41_cutoff_massTransport {N : ModelNorm (Fin d → ℝ)} (K : ℝ → ℝ) (r : ℝ) (β : ℝ≥0)
    (p : ℕ) :
    ∫⁻ ω, (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))
      = ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) :=
  i41_massTransport _ (fun t => law_cutoffKernel_map_translate K r β t) p
    (N : Seminorm ℝ (Fin d → ℝ)) r

/-- **Lemma I.4.1 in binomial form for the cut-off model**, assuming that clusters are almost
surely finite (the only extra input used by the paper, via sharpness of the phase transition). -/
theorem i41_cutoff_binomial {N : ModelNorm (Fin d → ℝ)} (K : ℝ → ℝ) (r : ℝ) (β : ℝ≥0) (p : ℕ)
    (hfin : ∀ v : Fin d → ℤ,
      law (intensityProfile (cutoffKernel (d := d) N K r) β)
        {ω : Config (Fin d → ℤ) | ((cluster ω v).encard : ℝ≥0∞) = ⊤} = 0) :
    ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) :=
  i41_binomial _ hfin p N r


/-! ### Non-vacuity witnesses -/

/-- The empty configuration is fixed by every shift. -/
theorem sym2Map_empty (t : Fin d → ℤ) :
    Sym2.map (fun x : Fin d → ℤ => x + t) '' (∅ : Config (Fin d → ℤ)) = ∅ := by
  simp

/-- Witness for the general cluster mass transport: under the Dirac measure at the empty
configuration, the left-hand side is `∑'_x 1(0 ↔ x) = 1`. -/
example (d : ℕ) :
    ∫⁻ ω, (∑' x, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * 1)
        ∂(Measure.dirac (∅ : Config (Fin d → ℤ))) = 1 := by
  classical
  rw [lintegral_dirac]
  have h : ∀ x : Fin d → ℤ,
      (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) (∅ : Config (Fin d → ℤ)) =
        if x = 0 then 1 else 0 := by
    intro x
    rw [Set.indicator_apply]
    by_cases hx : x = 0
    · subst hx
      simp [conn_self]
    · have hmem : (∅ : Config (Fin d → ℤ)) ∉ conn 0 x := by
        rw [empty_mem_conn_iff]
        exact fun h' => hx h'.symm
      simp [hmem, hx]
  simp only [h, mul_one, tsum_ite_eq]

/-- Witness, right-hand side: under the Dirac measure at the empty configuration the cluster of
the origin is a singleton, so the right-hand side is `1`. -/
example (d : ℕ) :
    ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) * 1
        ∂(Measure.dirac (∅ : Config (Fin d → ℤ))) = 1 := by
  rw [lintegral_dirac, mul_one, cluster_empty]
  simp

/-- Witness for `lintegral_cluster_massTransport`: the identity `1 = 1` at the Dirac measure of
the empty configuration and the constant kernel `g ≡ 1`, so the theorem is not vacuous. -/
example (d : ℕ) :
    ∫⁻ ω, (∑' x, (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω * 1)
        ∂(Measure.dirac (∅ : Config (Fin d → ℤ)))
      = ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) * 1
        ∂(Measure.dirac (∅ : Config (Fin d → ℤ))) :=
  lintegral_cluster_massTransport _ (fun t => by simp)
    (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ => rfl)

/-! ### General translation-invariant intensities -/

/-- **The mass-transport step of Lemma I.4.1 for any translation-invariant intensity.** For any
profile `J` on pairs of `ℤ^d` that is invariant under every translation, the bond law
`law (intensityProfile J β)` satisfies the mass-transport identity of Lemma I.4.1. -/
theorem i41_intensityProfile_massTransport {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ (a : Fin d → ℤ) e, J (Sym2.map (· + a) e) = J e) (β : ℝ≥0) (p : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    ∫⁻ ω, (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂(law (intensityProfile J β))
      = ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂(law (intensityProfile J β)) :=
  i41_massTransport _ (fun t => law_map_translate _ (intensityProfile_map_add hJ β) t) p N r

/-- **Lemma I.4.1 in binomial form for any intensity**, assuming that clusters are almost surely
finite. No translation invariance is needed for this step. -/
theorem i41_intensityProfile_binomial {J : Sym2 (Fin d → ℤ) → ℝ≥0} (β : ℝ≥0) (p : ℕ)
    (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ)
    (hfin : ∀ v : Fin d → ℤ,
      law (intensityProfile J β) {ω : Config (Fin d → ℤ) |
        ((cluster ω v).encard : ℝ≥0∞) = ⊤} = 0) :
    ∫⁻ ω, (((cluster ω 0).encard : ℝ≥0∞) *
        ∑' y,
          (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂(law (intensityProfile J β))
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂(law (intensityProfile J β)) :=
  i41_binomial _ hfin p N r


/-! ### Lemma I.2.6 for the cut-off family -/

/-- **Lemma I.2.6, real-integral form.** If the `p`-th moment of the cluster volume is finite
(automatic for the subcritical laws used in the paper), the lower bound of Lemma I.2.6 holds
for the real-valued expectation `∫ (|K_0|)^p d(law q)`, together with the general-profile
form used by the cut-off instance below. -/
theorem rpow_div_le_integral_encard_cluster (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ a e, q (Sym2.map (· + a) e) = q e) (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hfin : ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law q) ≠ ⊤) :
    ((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ)
        ^ (p + 1) / (Real.exp 1 * ((2 * n + 1) ^ d : ℕ)) ≤
      ∫ ω, ((cluster ω 0).encard : ℝ≥0∞).toReal ^ p ∂(law q) := by
  have hm : Measurable fun ω : Config (Fin d → ℤ) => ((cluster ω 0).encard : ℝ≥0∞) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard_cluster (x := (0 : Fin d → ℤ)))
  have hae : AEMeasurable (fun ω : Config (Fin d → ℤ) => ((cluster ω 0).encard : ℝ≥0∞) ^ p)
      (law q) := (hm.pow_const p).aemeasurable
  have haelt : ∀ᵐ ω ∂(law q), ((cluster ω 0).encard : ℝ≥0∞) ^ p < ⊤ := ae_lt_top' hae hfin
  have h1 : ((tightnessScale q (Finset.Icc (fun _ : Fin d => -(n : ℤ))
        (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) /
        (Real.exp 1 * ((2 * n + 1) ^ d : ℕ)) ≤
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law q)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (rpow_div_le_lintegral_encard_cluster q hq n hp)
  rw [← integral_toReal hae haelt] at h1
  refine h1.trans_eq (integral_congr_ae ?_)
  filter_upwards with ω
  exact (ENNReal.toReal_rpow _ p).symm

/-- **Lemma I.2.6 for the cut-off law `P_{β,r}`**: for a profile `K` that is nonnegative and
antitone on `(0,∞)`, every scale `r > 0`, intensity `β ≥ 0`, `n ∈ ℕ` and real `p > 0`,

  `E_{β,r}|K_0|^p ≥ (M_{β,r} - 1)^{p+1} / (e |B_n|)`,

where `M_{β,r}` is the tightness scale of the largest cluster in `B_n` and `|B_n| = (2n+1)^d`. -/
theorem lemma_I_2_6_cutoff (N : ModelNorm (Fin d → ℝ)) (K : ℝ → ℝ)
    (r : ℝ) (β : NNReal) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((tightnessScale (intensityProfile
          (cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r) β)
        (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) /
          (Real.exp 1 * ((2 * n + 1) ^ d : ℕ))) ≤
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law (intensityProfile
        (cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r) β)) :=
  rpow_div_le_lintegral_encard_cluster_intensity (d := d)
    (J := cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r)
    (cutoffKernel_map_add (d := d) N K r) β n hp

/-- **Lemma I.2.6 for the cut-off law `P_{β,r}` in the paper's real-expectation form**, under
finiteness of the `p`-th moment (automatic for the subcritical cut-off laws used in the
paper). -/
theorem lemma_I_2_6_cutoff_real_integral (N : ModelNorm (Fin d → ℝ)) (K : ℝ → ℝ)
    (r : ℝ) (β : NNReal) (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hfin : ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law (intensityProfile
        (cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r) β)) ≠ ⊤) :
    ((tightnessScale (intensityProfile (cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r) β)
        (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) - 1 : ℕ) : ℝ) ^ (p + 1) /
          (Real.exp 1 * ((2 * n + 1) ^ d : ℕ)) ≤
      ∫ ω, ((cluster ω 0).encard : ℝ≥0∞).toReal ^ p ∂(law (intensityProfile
        (cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r) β)) :=
  rpow_div_le_integral_encard_cluster (d := d)
    (q := intensityProfile (cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) K r) β)
    (intensityProfile_map_add (cutoffKernel_map_add (d := d) N K r) β) n hp hfin

end PercLib.Models.LongRange
