/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
SOURCE MIGRATION + NEW DERIVED, proof-only. The bounded identities of the old module
`PercLib/CriticalLRP/MomentMonotonicity/CutoffMomentAudit.lean`
(source revision `be191774d09f8bcded687f6950b5ab667972eb3d`, supplied under its
Apache-2.0 header), restated on the canonical bond
interface `PercLib.Percolation.Bond` with the finite window taken as a *restriction of the
configuration to a finite set of open pairs*, `ω ↦ ω ∩ S`.  No old code is copied verbatim; the
old proofs are rebuilt from the current production API (`exists_finset_of_mem_conn`,
`encard_iUnion_of_monotone`, `lintegral_iSup`, `measurable_encard_cluster`).
-/
module

public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Probability.OpenEventHarris
public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Models.LongRange.InfiniteVolumeRusso

/-!
# Cluster moments over finite edge windows

This is a proof-only port of the bounded equivalences and expectation identities of the old
module `PercLib.CriticalLRP.MomentMonotonicity.CutoffMomentAudit`.

The finite window is a **restriction of the configuration to a finite set of open pairs**:
for `S : Finset (Sym2 V)` the windowed cluster of `o` is the cluster of `o` in the restricted
configuration `ω ∩ S`.  It is not a finite-volume substitute for the vertex set: the cluster of
the unrestricted configuration is kept with its true cardinality, which is `⊤` on fibres with an
infinite cluster, throughout.

* `iUnion_cluster_inter_window` and `encard_cluster_eq_iSup_encard_inter_window`: along a
  monotone cofinal family of finite edge windows the window clusters increase to the cluster
  (*source migration*, the pointwise core of the old `box` exhaustion).
* `lintegral_encard_cluster_pow_eq_iSup`: the `p`-th cluster moment is the supremum of its
  finite-window moments, for an arbitrary measure on configurations and with `⊤` allowed on both
  sides (*source migration* of the old `cutoff_powMoment_eq_iSup_box`, itself an application of
  `lintegral_clusterVol_pow_eq_iSup_window`).
* `lintegral_encard_cluster_inter_window_pow_ne_top`: for a finite measure each finite-window
  `p`-th moment is finite with the explicit bound `|vertices of the window| ^ p`
  (*source migration* of `window_powMoment_ne_top` / `cutoff_window_powMoment_ne_top`).
* `encard_cluster_pow_ne_top_iff_uniform_window`: the unrestricted `p`-th moment is finite if and
  only if the finite-window moments admit a bound independent of the window (*source migration*
  of `powMoment_ne_top_iff_uniform_window` / `cutoff_powMoment_ne_top_iff_uniform_box`).
* `chi_eq_iSup_lintegral_encard_inter_window`: the susceptibility is the supremum of the
  expected finite-window volumes (*new derived*).
* `cutoffKernel_*`: the same three statements at the cut-off law
  `law (intensityProfile (cutoffKernel N K r) β)` of Definition I.1.5 (*new derived*
  specialisations).

The old module's hypothesis `0 < r` on the cut-off scale is not needed here: `intensityProfile`
is total in `r` on the canonical interface, so the cut-off statements hold at every real `r`, in
particular at every `r > 0`.

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.WindowMoments

open PercLib.Percolation.Bond

variable {V : Type*}

/-! ## Exhaustion by finite edge windows -/

/-- Every finite set of pairs is contained in a member of a monotone cofinal family of finite
edge windows. -/
theorem exists_finset_subset_window {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S)
    (hScover : ∀ e, ∃ k, e ∈ S k) (F : Finset (Sym2 V)) : ∃ k, F ⊆ S k := by
  classical
  induction F using Finset.induction with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | insert a F ha ih =>
      obtain ⟨k₁, h₁⟩ := hScover a
      obtain ⟨k₂, h₂⟩ := ih
      refine ⟨max k₁ k₂, ?_⟩
      intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact hSmono (le_max_left k₁ k₂) h₁
      · exact hSmono (le_max_right k₁ k₂) (h₂ he)

/-- The windowed cluster is monotone in the window. -/
theorem monotone_cluster_inter_window (ω : Config V) (o : V) {S : ℕ → Finset (Sym2 V)}
    (hSmono : Monotone S) :
    Monotone fun k => cluster (ω ∩ (S k : Set (Sym2 V))) o := by
  intro i j hij
  refine cluster_mono ?_ o
  intro e he
  exact ⟨he.1, hSmono hij he.2⟩

/-- **Exhaustion of the cluster by finite edge windows.**  If the finite windows increase and
every pair occurs in some window, the clusters of the restricted configurations increase to the
cluster of the full configuration. -/
theorem iUnion_cluster_inter_window (ω : Config V) (o : V) {S : ℕ → Finset (Sym2 V)}
    (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k) :
    (⋃ k, cluster (ω ∩ (S k : Set (Sym2 V))) o) = cluster ω o := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => cluster_mono Set.inter_subset_left o) ?_
  intro y hy
  rw [mem_cluster_iff] at hy
  obtain ⟨F, hFω, hF⟩ := exists_finset_of_mem_conn hy
  obtain ⟨k, hk⟩ := exists_finset_subset_window hSmono hScover F
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  rw [mem_cluster_iff]
  exact conn_mono (ω := (F : Config V)) (ω' := ω ∩ (S k : Set (Sym2 V)))
    (fun e he => ⟨hFω he, hk he⟩) hF

/-- **The cluster volume is the supremum of its finite-edge-window volumes.** -/
theorem encard_cluster_eq_iSup_encard_inter_window (ω : Config V) (o : V)
    {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k) :
    (cluster ω o).encard = ⨆ k, (cluster (ω ∩ (S k : Set (Sym2 V))) o).encard := by
  rw [← iUnion_cluster_inter_window ω o hSmono hScover]
  exact encard_iUnion_of_monotone (monotone_cluster_inter_window ω o hSmono)

/-! ## The moment identity -/

/-- The windowed cluster volume is measurable. -/
theorem measurable_encard_cluster_inter_window [Countable V] (o : V) (S : Set (Sym2 V)) :
    Measurable fun ω : Config V => ((cluster (ω ∩ S) o).encard : ℝ≥0∞) :=
  (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
    ((measurable_encard_cluster o).comp (PercLib.Models.LongRange.measurable_inter_const S))

/-- Powers commute with the supremum of an increasing sequence in `ℝ≥0∞`. -/
theorem iSup_pow_of_monotone {a : ℕ → ℝ≥0∞} (ha : Monotone a) (p : ℕ) :
    (⨆ k, a k) ^ p = ⨆ k, a k ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [pow_succ, ih]
      refine le_antisymm ?_ ?_
      · rw [ENNReal.iSup_mul]
        refine iSup_le fun k => ?_
        rw [ENNReal.mul_iSup]
        refine iSup_le fun j => ?_
        calc a k ^ p * a j ≤ a (max k j) ^ p * a (max k j) :=
              mul_le_mul' (pow_le_pow_left' (ha (le_max_left k j)) p) (ha (le_max_right k j))
          _ = a (max k j) ^ (p + 1) := (pow_succ _ _).symm
          _ ≤ ⨆ m, a m ^ (p + 1) := le_iSup (fun m => a m ^ (p + 1)) (max k j)
      · refine iSup_le fun m => ?_
        rw [pow_succ]
        exact mul_le_mul' (le_iSup (fun k => a k ^ p) m) (le_iSup a m)

/-- **The `p`-th cluster moment is the supremum of its finite-edge-window moments.**  No
finiteness assumption: `⊤` is allowed on both sides. -/
theorem lintegral_encard_cluster_pow_eq_iSup [Countable V] (μ : Measure (Config V)) (o : V)
    {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k) (p : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) =
      ⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ := by
  have hpt : ∀ ω : Config V, ((cluster ω o).encard : ℝ≥0∞) ^ p =
      ⨆ k, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p := by
    intro ω
    have hmono : Monotone fun k => ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) :=
      fun i j hij => ENat.toENNReal_le.2
        (encard_le_encard (monotone_cluster_inter_window ω o hSmono hij))
    rw [encard_cluster_eq_iSup_encard_inter_window ω o hSmono hScover, ENat.toENNReal_iSup]
    exact iSup_pow_of_monotone hmono p
  rw [funext hpt]
  refine lintegral_iSup (fun k => ?_) (fun i j hij ω => ?_)
  · exact (measurable_encard_cluster_inter_window o (S k)).pow_const p
  · exact pow_le_pow_left'
      (ENat.toENNReal_le.2
        (encard_le_encard (monotone_cluster_inter_window ω o hSmono hij))) p

/-! ## Finite-window finiteness and the uniform-bound equivalence -/

/-- **The windowed cluster lies in the finite vertex set of the window.** -/
theorem cluster_inter_window_subset [DecidableEq V] (ω : Config V) (o : V)
    (S : Finset (Sym2 V)) :
    cluster (ω ∩ (S : Set (Sym2 V))) o ⊆
      ((insert o (S.biUnion fun e => e.toFinset) : Finset V) : Set V) := by
  intro y hy
  change (openGraph (ω ∩ (S : Set (Sym2 V)))).Reachable o y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact Finset.mem_coe.2 (Finset.mem_insert_self o _)
  | @tail z w _ hadj ih =>
      rw [openGraph_adj_iff] at hadj
      obtain ⟨hzw, -⟩ := hadj
      refine Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨s(z, w), hzw.2, ?_⟩))
      rw [Sym2.mem_toFinset]
      exact Sym2.mem_mk_right z w

/-- **The windowed cluster volume is bounded by the number of vertices of the window.** -/
theorem encard_cluster_inter_window_le_card [DecidableEq V] (ω : Config V) (o : V)
    (S : Finset (Sym2 V)) :
    (cluster (ω ∩ (S : Set (Sym2 V))) o).encard ≤
      ((insert o (S.biUnion fun e => e.toFinset)).card : ℕ∞) := by
  calc (cluster (ω ∩ (S : Set (Sym2 V))) o).encard
      ≤ ((insert o (S.biUnion fun e => e.toFinset) : Finset V) : Set V).encard :=
        encard_le_encard (cluster_inter_window_subset ω o S)
    _ = ((insert o (S.biUnion fun e => e.toFinset) : Finset V).card : ℕ∞) :=
        Set.encard_coe_eq_coe_finsetCard _

/-- **Every finite-window `p`-th moment is finite** for a finite measure, with the explicit
bound `|vertices of the window| ^ p`. -/
theorem lintegral_encard_cluster_inter_window_pow_ne_top [Countable V] (μ : Measure (Config V))
    [IsFiniteMeasure μ] (o : V) (S : Finset (Sym2 V)) (p : ℕ) :
    (∫⁻ ω, ((cluster (ω ∩ (S : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ := by
  classical
  set c : ℝ≥0∞ := ((insert o (S.biUnion fun e => e.toFinset) : Finset V).card : ℝ≥0∞) with hc
  have hb : ∀ ω : Config V, ((cluster (ω ∩ (S : Set (Sym2 V))) o).encard : ℝ≥0∞) ≤ c := by
    intro ω
    calc ((cluster (ω ∩ (S : Set (Sym2 V))) o).encard : ℝ≥0∞)
        ≤ (((insert o (S.biUnion fun e => e.toFinset) : Finset V).card : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 (encard_cluster_inter_window_le_card ω o S)
      _ = c := by rw [hc]; simp
  have hle : (∫⁻ ω, ((cluster (ω ∩ (S : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ)
      ≤ (c : ℝ≥0∞) ^ p * μ univ := by
    calc (∫⁻ ω, ((cluster (ω ∩ (S : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ)
        ≤ ∫⁻ _ω : Config V, (c : ℝ≥0∞) ^ p ∂μ := lintegral_mono fun ω => pow_le_pow_left' (hb ω) p
      _ = (c : ℝ≥0∞) ^ p * μ univ := lintegral_const _
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by rw [hc]; simp)) (measure_ne_top μ _)) hle

/-- **The unrestricted `p`-th moment is finite if and only if the finite-window moments admit a
bound independent of the window.**  This is the exact content of the uniform-bound equivalence:
each window moment is finite by the previous lemma, so the content is the uniformity. -/
theorem encard_cluster_pow_ne_top_iff_uniform_window [Countable V] (μ : Measure (Config V))
    (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k)
    (p : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k,
        (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) ≤ C := by
  rw [lintegral_encard_cluster_pow_eq_iSup μ o hSmono hScover p]
  refine ⟨fun h => ⟨_, h, fun k => le_iSup (fun k =>
    ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) k⟩, ?_⟩
  rintro ⟨C, hC, hle⟩
  exact ne_top_of_le_ne_top hC (iSup_le hle)

/-- Each finite-window moment is bounded by the unrestricted moment. -/
theorem lintegral_encard_cluster_inter_window_pow_le [Countable V] (μ : Measure (Config V))
    (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k)
    (p k : ℕ) :
    (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ := by
  rw [lintegral_encard_cluster_pow_eq_iSup μ o hSmono hScover p]
  exact le_iSup (fun k =>
    ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) k

/-- **Under a finite unrestricted `p`-th moment** the supremum of the finite-window moments is
that moment, and is finite.  This is the "iSup of the finite-window moments under a finite
expectation at the unrestricted law" form; without the finiteness hypothesis the identity
`lintegral_encard_cluster_pow_eq_iSup` still holds with `⊤` allowed on both sides. -/
theorem iSup_lintegral_encard_inter_window_eq_of_ne_top [Countable V] (μ : Measure (Config V))
    (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k)
    (p : ℕ) (hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    (⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) =
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ ∧
      (⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ :=
  ⟨(lintegral_encard_cluster_pow_eq_iSup μ o hSmono hScover p).symm,
    by rw [← lintegral_encard_cluster_pow_eq_iSup μ o hSmono hScover p]; exact hfin⟩

/-! ## The independent percolation law -/

/-- **Susceptibility as the supremum of finite-edge-window expectations** (*new derived*). -/
theorem chi_eq_iSup_lintegral_encard_inter_window [Countable V] (q : Sym2 V → unitInterval)
    (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k) :
    chi q o = ⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ∂law q := by
  simpa only [chi, pow_one] using lintegral_encard_cluster_pow_eq_iSup (law q) o hSmono hScover 1

/-- **Under a finite susceptibility** the supremum of the expected finite-window volumes is the
susceptibility and is finite. -/
theorem iSup_lintegral_encard_inter_window_eq_chi_of_ne_top [Countable V]
    (q : Sym2 V → unitInterval) (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S)
    (hScover : ∀ e, ∃ k, e ∈ S k) (hfin : chi q o ≠ ⊤) :
    (⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ∂law q) = chi q o ∧
      (⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ∂law q) ≠ ⊤ := by
  have h := iSup_lintegral_encard_inter_window_eq_of_ne_top (law q) o hSmono hScover 1
    (by simpa only [chi, pow_one] using hfin)
  simpa only [chi, pow_one] using h

/-- The `p`-th moment identity under the independent law. -/
theorem law_lintegral_encard_cluster_pow_eq_iSup [Countable V] (q : Sym2 V → unitInterval)
    (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k)
    (p : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q) =
      ⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q :=
  lintegral_encard_cluster_pow_eq_iSup (law q) o hSmono hScover p

/-- Each finite-window moment is finite under the independent law. -/
theorem law_encard_cluster_inter_window_pow_ne_top [Countable V] (q : Sym2 V → unitInterval)
    (o : V) (S : Finset (Sym2 V)) (p : ℕ) :
    (∫⁻ ω, ((cluster (ω ∩ (S : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q) ≠ ⊤ :=
  lintegral_encard_cluster_inter_window_pow_ne_top (law q) o S p

/-- The uniform-bound equivalence under the independent law. -/
theorem law_encard_cluster_pow_ne_top_iff_uniform_window [Countable V]
    (q : Sym2 V → unitInterval) (o : V) {S : ℕ → Finset (Sym2 V)} (hSmono : Monotone S)
    (hScover : ∀ e, ∃ k, e ∈ S k) (p : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q) ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k,
        (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 V))) o).encard : ℝ≥0∞) ^ p ∂law q) ≤ C :=
  encard_cluster_pow_ne_top_iff_uniform_window (law q) o hSmono hScover p

/-- A countable nonempty pair set admits a monotone cofinal exhaustion by finite edge
windows. -/
theorem exists_monotone_cofinal_window [Nonempty (Sym2 V)] [Countable (Sym2 V)] :
    ∃ S : ℕ → Finset (Sym2 V), Monotone S ∧ ∀ e, ∃ k, e ∈ S k := by
  classical
  obtain ⟨f, hf⟩ := exists_surjective_nat (Sym2 V)
  refine ⟨fun k => (Finset.range k).image f, ?_, fun e => ?_⟩
  · intro i j hij
    exact Finset.image_subset_image (Finset.range_subset_range.2 hij)
  · obtain ⟨k, rfl⟩ := hf e
    exact ⟨k + 1, Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), rfl⟩⟩

/-! ## The cut-off law of Definition I.1.5 -/

open PercLib.Analysis
open PercLib.Models.LongRange

variable {d : ℕ}

/-- **At the cut-off law `P_{β,r}` of Definition I.1.5** the `p`-th cluster moment is the
supremum of its finite-edge-window moments.  Arbitrary norm `N`, profile `K`, real scale `r` and
parameter `β`; no finiteness assumption. -/
theorem cutoffKernel_lintegral_encard_cluster_pow_eq_iSup (N : Seminorm ℝ (Fin d → ℝ))
    (K : ℝ → ℝ) (r : ℝ) (β : ℝ≥0) (o : Fin d → ℤ)
    {S : ℕ → Finset (Sym2 (Fin d → ℤ))} (hSmono : Monotone S)
    (hScover : ∀ e, ∃ k, e ∈ S k) (p : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel N K r) β)) =
      ⨆ k, ∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 (Fin d → ℤ)))) o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel N K r) β) :=
  lintegral_encard_cluster_pow_eq_iSup _ o hSmono hScover p

/-- **Every finite-window moment at the cut-off law is finite** (*source migration* of
`cutoff_window_powMoment_ne_top`, at every real scale `r`, in particular at every `r > 0`). -/
theorem cutoffKernel_encard_cluster_inter_window_pow_ne_top (N : Seminorm ℝ (Fin d → ℝ))
    (K : ℝ → ℝ) (r : ℝ) (β : ℝ≥0) (o : Fin d → ℤ) (S : Finset (Sym2 (Fin d → ℤ)))
    (p : ℕ) :
    (∫⁻ ω, ((cluster (ω ∩ (S : Set (Sym2 (Fin d → ℤ)))) o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel N K r) β)) ≠ ⊤ :=
  law_encard_cluster_inter_window_pow_ne_top _ o S p

/-- **The cut-off `p`-th moment is finite if and only if the finite-window moments are uniformly
bounded** (*source migration* of `cutoff_powMoment_ne_top_iff_uniform_box`). -/
theorem cutoffKernel_encard_cluster_pow_ne_top_iff_uniform_window (N : Seminorm ℝ (Fin d → ℝ))
    (K : ℝ → ℝ) (r : ℝ) (β : ℝ≥0) (o : Fin d → ℤ)
    {S : ℕ → Finset (Sym2 (Fin d → ℤ))} (hSmono : Monotone S)
    (hScover : ∀ e, ∃ k, e ∈ S k) (p : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel N K r) β)) ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k,
        (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 (Fin d → ℤ)))) o).encard : ℝ≥0∞) ^ p
            ∂law (intensityProfile (cutoffKernel N K r) β)) ≤ C :=
  law_encard_cluster_pow_ne_top_iff_uniform_window _ o hSmono hScover p

/-- The pair set of `ℤ^d` admits a monotone cofinal exhaustion by finite edge windows. -/
theorem exists_monotone_cofinal_window_int (d : ℕ) :
    ∃ S : ℕ → Finset (Sym2 (Fin d → ℤ)), Monotone S ∧ ∀ e, ∃ k, e ∈ S k :=
  exists_monotone_cofinal_window

/-- **New derived**: at the concrete power-law cut-off in the high-temperature region `β M < 1`
the finite-edge-window moments are uniformly bounded in the window, at every positive scale.
This is the uniform bound that the old audit isolated as the exact content of the cut-off moment
obligation; here it is derived from the production finiteness of the unrestricted cut-off
moment (`Models.LongRange.lintegral_cutoffKernel_powerLaw_pow_ne_top`) through the
uniform-bound equivalence above. -/
theorem powerLaw_exists_uniform_window_bound (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {r : ℝ} (hr : 0 < r) (o : Fin d → ℤ) {S : ℕ → Finset (Sym2 (Fin d → ℤ))}
    (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k) (p : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k,
      (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 (Fin d → ℤ)))) o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤ C :=
  (cutoffKernel_encard_cluster_pow_ne_top_iff_uniform_window (normSeminorm ℝ (Fin d → ℝ))
    (powerLawProfile 1 ((d : ℝ) + α)) r β o hSmono hScover p).1
    (lintegral_cutoffKernel_powerLaw_pow_ne_top (r := r) hd hα hβ hr o p)

/-- Non-vacuity of the high-temperature hypothesis: at `β = 0` the bound `β M < 1` holds, so the
uniform finite-window bound of `powerLaw_exists_uniform_window_bound` is available. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) (o : Fin d → ℤ)
    {S : ℕ → Finset (Sym2 (Fin d → ℤ))} (hSmono : Monotone S) (hScover : ∀ e, ∃ k, e ∈ S k)
    (p : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k,
      (∫⁻ ω, ((cluster (ω ∩ (S k : Set (Sym2 (Fin d → ℤ)))) o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) (0 : ℝ≥0))) ≤ C :=
  powerLaw_exists_uniform_window_bound hd hα (β := 0) (by simp) hr o hSmono hScover p

end PercLib.Percolation.Bond.WindowMoments
