/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written 2026-11-22 for the truncation/moment prerequisites of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1.
No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.UniformVolumeTail
public import PercLib.Models.LongRange.InfiniteVolumeRusso
public import PercLib.Models.LongRange.MassTransportI41
public import PercLib.Probability.Coordinate
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Probability.MassTransportTuple
public import PercLib.Percolation.Bond.MomentDerivativeTruncated
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Models.HierarchicalCutoff
public import PercLib.Models.LongRange.CutoffCorner
public import PercLib.Percolation.Bond.Forest
public import PercLib.Probability.Cylinder
public import PercLib.Analysis.DominatedDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Tail sums of cluster volumes

The paper's volume moment `E|K|^p` is unbounded; the formalised Russo formula
(`PercLib.Models.LongRange.hasDerivAt_integral_cutoff`) takes a bounded, eventually constant
observable `F : ℕ∞ → ℝ`. The passage between the unbounded moment and the bounded truncations
is a tail-sum (layer cake) identity, which this file proves on the existing bond model.

* `lintegral_iSup_sum_mul_indicator_enat_lt`: weighted layer cake for a measurable
  `f : α → ℕ∞`: if `g x = ⨆ N, ∑_{n < N} c n * 1(n < x)` then
  `∫⁻ g (f a) ∂μ = ∑' n, c n * μ {a | n < f a}`. No finiteness of `μ` beyond the statement.
* `enat_coe_eq_iSup_sum_ite_lt`: the `p = 1` instance, `x = ⨆ N, ∑_{n<N} 1(n < x)`;
* `enat_coe_pow_eq_iSup_sum_ite_lt`: the `p ≥ 1` instance,
  `x^p = ⨆ N, ∑_{n<N} ((n+1)^p - n^p) 1(n < x)` (telescoping);
* `lintegral_encard_cluster_eq_tsum_tail`: `E|K_o| = ∑_n P(n < |K_o|)` for the cluster volume
  `(cluster ω o).encard` under `law q`;
* `lintegral_encard_cluster_pow_eq_tsum_tail`: `E|K_o|^p = ∑_n ((n+1)^p - n^p) P(n < |K_o|)`.
Both are exact in `ℝ≥0∞`, so infinite cluster volume contributes `∞` on both sides: no
finiteness of the cluster is assumed, and the truncation step for the Russo formula needs no
dominator (only the derivative limit does).

Non-vacuity: the zero profile on `ℤ` has `|K_o| = 1` a.e., and the left side of the `p = 1`
identity evaluates to `1`.

Scope: these are tail-sum identities for any bond profile on a countable vertex set. They do
not assert differentiability or the limit of truncated derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Analysis

/-- **Weighted layer cake for `ℕ∞`-valued functions.** If `g` is the supremum of the partial
sums `∑_{n < N} c n * 1(n < x)`, then integrating `g ∘ f` against `μ` gives
`∑' n, c n * μ {a | n < f a}`. -/
theorem lintegral_iSup_sum_mul_indicator_enat_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℕ∞} (hf : Measurable f) (c : ℕ → ℝ≥0∞) {g : ℕ∞ → ℝ≥0∞}
    (hg : ∀ x : ℕ∞, g x = ⨆ N : ℕ, ∑ n ∈ Finset.range N,
      c n * (if (n : ℕ∞) < x then 1 else 0)) :
    ∫⁻ a, g (f a) ∂μ = ∑' n : ℕ, c n * μ {a | (n : ℕ∞) < f a} := by
  have hset : ∀ n : ℕ, MeasurableSet {a : α | (n : ℕ∞) < f a} :=
    fun n => hf (show MeasurableSet (Set.Ioi (n : ℕ∞)) from trivial)
  have hterm : ∀ n : ℕ, ∫⁻ a, c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) ∂μ =
      c n * μ {a : α | (n : ℕ∞) < f a} := by
    intro n
    have hfun : (fun a => c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0)) =
        {a : α | (n : ℕ∞) < f a}.indicator (fun _ => c n) := by
      funext a
      by_cases h : (n : ℕ∞) < f a <;> simp [Set.indicator, h]
    rw [hfun, lintegral_indicator (hset n), setLIntegral_const]
  have hmeas : ∀ n : ℕ, Measurable fun a : α =>
      c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) := by
    intro n
    have hfun : (fun a : α => c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0)) =
        {a : α | (n : ℕ∞) < f a}.indicator (fun _ => c n) := by
      funext a
      by_cases h : (n : ℕ∞) < f a <;> simp [Set.indicator, h]
    rw [hfun]
    exact measurable_const.indicator (hset n)
  have hsup : (fun a => g (f a)) = fun a => ⨆ N : ℕ, ∑ n ∈ Finset.range N,
      c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) := funext fun a => hg (f a)
  rw [hsup, lintegral_iSup]
  · rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_congr fun N => ?_
    rw [lintegral_finsetSum (s := Finset.range N) (fun n _ => hmeas n)]
    exact Finset.sum_congr rfl fun n _ => hterm n
  · exact fun N => Finset.measurable_sum _ fun n _ => hmeas n
  · exact fun N M hNM a => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      fun i _ _ => by positivity

end PercLib.Analysis

namespace PercLib.Analysis

/-- The partial sums of the `p = 1` layer cake, for a finite value `k`. -/
theorem sum_range_ite_enat_lt_cast (N k : ℕ) :
    ∑ n ∈ Finset.range N, (if (n : ℕ∞) < (k : ℕ∞) then (1 : ℝ≥0∞) else 0) =
      ((min N k : ℕ) : ℝ≥0∞) := by
  rw [← Finset.sum_filter (p := fun n : ℕ => (n : ℕ∞) < (k : ℕ∞))]
  have hfilt : (Finset.range N).filter (fun n : ℕ => (n : ℕ∞) < (k : ℕ∞)) =
      Finset.range (min N k) := by
    ext n
    simp [Finset.mem_filter, Finset.mem_range]
  rw [hfilt]
  simp

/-- **`p = 1` layer cake for `ℕ∞`.** `x` is the supremum of its partial counting sums. -/
theorem enat_coe_eq_iSup_sum_ite_lt (x : ℕ∞) :
    (x : ℝ≥0∞) = ⨆ N : ℕ,
      ∑ n ∈ Finset.range N, (if (n : ℕ∞) < x then (1 : ℝ≥0∞) else 0) := by
  rcases eq_or_ne x ⊤ with hx | hx
  · subst hx
    have hpt : ∀ N : ℕ,
        ∑ n ∈ Finset.range N, (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) =
          (N : ℝ≥0∞) := by
      intro N
      simp
    simp only [hpt]
    exact ENNReal.iSup_natCast.symm
  · obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hx
    simp only [sum_range_ite_enat_lt_cast]
    refine le_antisymm ?_ (iSup_le fun N => ?_)
    · calc (((k : ℕ∞)) : ℝ≥0∞) = (((min k k : ℕ)) : ℝ≥0∞) := by simp
      _ ≤ ⨆ N, (((min N k : ℕ)) : ℝ≥0∞) := le_iSup (fun N => (((min N k : ℕ)) : ℝ≥0∞)) k
    · exact_mod_cast Nat.min_le_right N k

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- **Tail sum of the cluster volume.** Under `law q`, the expected cluster volume equals the
sum of the tails of `(cluster ω o).encard`. Both sides are in `ℝ≥0∞`: infinite cluster volume
contributes `∞` to both, so no finiteness hypothesis is needed. -/
theorem lintegral_encard_cluster_eq_tsum_tail (q : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂law q =
      ∑' n : ℕ, law q {ω | (n : ℕ∞) < (cluster ω o).encard} := by
  have h := PercLib.Analysis.lintegral_iSup_sum_mul_indicator_enat_lt (μ := law q)
    (f := fun ω => (cluster ω o).encard) (measurable_encard_cluster o) (fun _ => 1)
    (g := fun x => (x : ℝ≥0∞)) fun x => by
      rw [PercLib.Analysis.enat_coe_eq_iSup_sum_ite_lt x]
      exact iSup_congr fun N => Finset.sum_congr rfl fun n _ => by rw [one_mul]
  simpa using h

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-- **Non-vacuity.** Under the zero profile on `ℤ` every cluster is a singleton
(`ae_cluster_eq_singleton_of_offDiagonal`), so `|K_o| = 1` almost surely and the left side of
`lintegral_encard_cluster_eq_tsum_tail` is the probability `1`. -/
example (o : ℤ) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂law (fun _ : Sym2 ℤ => (0 : unitInterval)) = 1 := by
  have hae : ∀ᵐ ω ∂law (fun _ : Sym2 ℤ => (0 : unitInterval)),
      ((cluster ω o).encard : ℝ≥0∞) = 1 :=
    (ae_cluster_eq_singleton_of_offDiagonal _ fun x y _ => rfl).mono fun ω h => by
      rw [h o, Set.encard_singleton]
      simp
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

end PercLib.Percolation.Bond

namespace PercLib.Analysis

theorem sum_range_ofReal_pow_sub (p k : ℕ) (hp : 1 ≤ p) :
    ∑ n ∈ Finset.range k, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) =
      (k : ℝ≥0∞) ^ p := by
  have hnn : ∀ n ∈ Finset.range k, 0 ≤ ((n : ℝ) + 1) ^ p - (n : ℝ) ^ p := by
    intro n _
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h3 := pow_le_pow_left₀ h1 h2 p
    linarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  rw [show (k : ℝ≥0∞) ^ p = ENNReal.ofReal ((k : ℝ) ^ p) by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]]
  congr 1
  have htel := Finset.sum_range_sub (fun i : ℕ => ((i : ℝ)) ^ p) k
  simpa [Nat.cast_zero, zero_pow (by omega : p ≠ 0)] using htel

theorem one_le_ofReal_pow_sub (p n : ℕ) (hp : 1 ≤ p) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) := by
  rw [ENNReal.one_le_ofReal]
  have hlt : n ^ p < (n + 1) ^ p := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by omega)
  have h1 : ((n ^ p : ℕ) : ℝ) + 1 ≤ (((n + 1) ^ p : ℕ) : ℝ) := by exact_mod_cast hlt
  push_cast at h1 ⊢
  linarith

theorem enat_coe_pow_eq_iSup_sum_ite_lt (p : ℕ) (hp : 1 ≤ p) (x : ℕ∞) :
    (x : ℝ≥0∞) ^ p = ⨆ N : ℕ, ∑ n ∈ Finset.range N,
      ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) * (if (n : ℕ∞) < x then 1 else 0) := by
  have hc : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ p - (n : ℝ) ^ p := by
    intro n
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h3 := pow_le_pow_left₀ h1 h2 p
    linarith
  rcases eq_or_ne x ⊤ with hx | hx
  · subst hx
    rw [show ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ from rfl, ENNReal.top_pow (by omega : p ≠ 0)]
    refine le_antisymm ?_ le_top
    rw [← ENNReal.iSup_natCast]
    refine iSup_le fun N => ?_
    have hpt : ∑ n ∈ Finset.range N, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
        (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) =
        ∑ n ∈ Finset.range N, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp
    calc (N : ℝ≥0∞) = ∑ n ∈ Finset.range N, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) :=
          Finset.sum_le_sum fun n _ => one_le_ofReal_pow_sub p n hp
      _ = _ := hpt.symm
      _ ≤ ⨆ N, ∑ n ∈ Finset.range N,
            ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
              (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) :=
          le_iSup (fun N => ∑ n ∈ Finset.range N,
            ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
              (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0)) N
  · obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hx
    have hfilt : ∀ N : ℕ, (Finset.range N).filter (fun n : ℕ => (n : ℕ∞) < (k : ℕ∞)) =
        Finset.range (min N k) := by
      intro N
      ext n
      simp [Finset.mem_filter, Finset.mem_range]
    have hterm : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
          (if (n : ℕ∞) < ((k : ℕ∞)) then 1 else 0) =
        ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p) := by
      intro N
      have hstep : ∀ n ∈ Finset.range N,
          ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
            (if (n : ℕ∞) < ((k : ℕ∞)) then 1 else 0) =
          (if (n : ℕ∞) < ((k : ℕ∞)) then ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p)
            else 0) := by
        intro n _
        by_cases h : (n : ℕ∞) < ((k : ℕ∞)) <;> simp [h]
      rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter (p := fun n : ℕ => (n : ℕ∞) < (k : ℕ∞)),
        hfilt N]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => hc m)]
      rw [show (∑ n ∈ Finset.range (min N k), (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p)) =
          ((min N k : ℕ) : ℝ) ^ p by
        have htel := Finset.sum_range_sub (fun i : ℕ => ((i : ℝ)) ^ p) (min N k)
        simpa [Nat.cast_zero, zero_pow (by omega : p ≠ 0)] using htel]
    rw [show ((↑k : ℕ∞) : ℝ≥0∞) ^ p = ENNReal.ofReal (((k : ℕ) : ℝ) ^ p) by
      rw [show ((↑k : ℕ∞) : ℝ≥0∞) = (k : ℝ≥0∞) from rfl, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (Nat.cast_nonneg k)]]
    simp only [hterm]
    have hupper : ∀ N : ℕ, ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p) ≤
        ENNReal.ofReal (((k : ℕ) : ℝ) ^ p) := by
      intro N
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : (min N k : ℕ) ≤ k := Nat.min_le_right N k
      have hcast : ((min N k : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hle
      have := pow_le_pow_left₀ (Nat.cast_nonneg (min N k)) hcast p
      simpa using this
    refine le_antisymm ?_ (iSup_le hupper)
    calc ENNReal.ofReal (((k : ℕ) : ℝ) ^ p) = ENNReal.ofReal (((min k k : ℕ) : ℝ) ^ p) := by
          simp
      _ ≤ ⨆ N, ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p) :=
          le_iSup (fun N => ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p)) k


end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- **Tail sum of a cluster-volume power.** The `p`-th moment of the cluster volume is the
sum of the jumps `(n+1)^p - n^p` weighted by the tails of `(cluster ω o).encard`, exactly in
`ℝ≥0∞`; no finiteness hypothesis is used, and the exponent `p ≥ 1` is needed for the
telescoping weights `1^p - 0^p = 1`. -/
theorem lintegral_encard_cluster_pow_eq_tsum_tail (q : Sym2 V → unitInterval) (o : V)
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q =
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
        law q {ω | (n : ℕ∞) < (cluster ω o).encard} :=
  PercLib.Analysis.lintegral_iSup_sum_mul_indicator_enat_lt (μ := law q)
    (f := fun ω => (cluster ω o).encard) (measurable_encard_cluster o)
    (c := fun n => ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p))
    (g := fun x => (x : ℝ≥0∞) ^ p)
    (fun x => PercLib.Analysis.enat_coe_pow_eq_iSup_sum_ite_lt p hp x)

end PercLib.Percolation.Bond

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

/-! ### The arithmetic of the cap -/

open PercLib.Probability

variable {V : Type*} [Countable V]

/-! ### Monotonicity of the cluster in the pair -/

omit [Countable V] in
/-- Closing (or rather restricting to) the pair `e` can only shrink the cluster of `o`: the
configuration `ω \ {e}` is a subconfiguration of `insert e ω`. -/
theorem encard_cluster_sdiff_le_insert (ω : Config V) (e : Sym2 V) (o : V) :
    (cluster (ω \ {e}) o).encard ≤ (cluster (insert e ω) o).encard :=
  Set.encard_mono (cluster_mono (Set.sdiff_subset.trans (Set.subset_insert e ω)) o)

omit [Countable V] in
/-- The cast form used below: the `ℝ≥0∞` cluster volumes are ordered the same way. -/
theorem encard_cluster_sdiff_le_insert_coe (ω : Config V) (e : Sym2 V) (o : V) :
    ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
  by exact_mod_cast encard_cluster_sdiff_le_insert ω e o

/-- **The cap in additive form.** For `y ≤ x` and any cap `c`,
`min c x - min c y = min c x - y` in `ℝ≥0∞` (truncated subtraction). Consequently the capped
increment is monotone in `c`, which is what a monotone convergence argument needs. -/
theorem min_tsub_min_eq {x y c : ℝ≥0∞} (hyx : y ≤ x) :
    min c x - min c y = min c x - y := by
  rcases le_total y c with hyc | hcy
  · rw [min_eq_right hyc]
  · rw [min_eq_left hcy, min_eq_left (hcy.trans hyx), tsub_self, tsub_eq_zero_iff_le.mpr hcy]

/-- The capped pivotal increment is monotone in the cap. -/
theorem monotone_tsub_min {x y : ℝ≥0∞} (hyx : y ≤ x) :
    Monotone fun c : ℝ≥0∞ => min c x - min c y := by
  intro c d hcd
  change min c x - min c y ≤ min d x - min d y
  rw [min_tsub_min_eq hyx, min_tsub_min_eq hyx]
  exact tsub_le_tsub_right (min_le_min_right x hcd) y

/-- Supremum over natural caps: `⨆ n, min n x = x`. -/
theorem iSup_min_natCast (x : ℝ≥0∞) : (⨆ n : ℕ, min (n : ℝ≥0∞) x) = x := by
  refine le_antisymm (iSup_le fun n => min_le_right _ _) ?_
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [show (⨆ n : ℕ, min (n : ℝ≥0∞) ⊤) = ⨆ n : ℕ, (n : ℝ≥0∞) from
      iSup_congr fun n => min_eq_left le_top]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact le_iSup_of_le n (le_min hn.le le_rfl)

/-- **The capped pivotal increments increase to the uncapped one.** -/
theorem iSup_pivotal_truncation (x y : ℝ≥0∞) (hyx : y ≤ x) :
    (⨆ n : ℕ, (min (n : ℝ≥0∞) x - min (n : ℝ≥0∞) y)) = x - y := by
  rw [iSup_congr fun n => min_tsub_min_eq hyx, ← ENNReal.iSup_sub, iSup_min_natCast]

/-- The capped pivotal increment is monotone in the cap, for natural caps. -/
theorem monotone_pivotal_truncation (x y : ℝ≥0∞) (hyx : y ≤ x) :
    Monotone fun n : ℕ => min (n : ℝ≥0∞) x - min (n : ℝ≥0∞) y :=
  fun m n hmn => monotone_tsub_min hyx (by exact_mod_cast hmn)

/-! ### Measurability -/

/-- The cluster volume of `o` after inserting the pair `e` is measurable in `ω`. -/
theorem measurable_encard_cluster_insert_coe (e : Sym2 V) (o : V) :
    Measurable fun ω : Config V => ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
  Measurable.of_discrete.comp
    ((measurable_encard_cluster (x := o)).comp (measurable_insert e))

/-- The cluster volume of `o` after deleting the pair `e` is measurable in `ω`. -/
theorem measurable_encard_cluster_sdiff_coe (e : Sym2 V) (o : V) :
    Measurable fun ω : Config V => ((cluster (ω \ {e}) o).encard : ℝ≥0∞) :=
  Measurable.of_discrete.comp
    ((measurable_encard_cluster (x := o)).comp (measurable_diff_singleton e))

/-- The capped pivotal increment is measurable. -/
theorem measurable_pivotal_truncation (e : Sym2 V) (o : V) (p n : ℕ) :
    Measurable fun ω : Config V =>
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) :=
  ((measurable_const.min ((measurable_encard_cluster_insert_coe e o).pow_const p)).sub
    (measurable_const.min ((measurable_encard_cluster_sdiff_coe e o).pow_const p)))

/-! ### Flux convergence in `ℝ≥0∞` -/

/-- **Main theorem: the capped pivotal flux converges to the uncapped one.**

For any measure `μ` on bond configurations, any pair `e`, root `o` and exponent `p`, the
pivotal integrals of the capped moments `min (n) (|K_o| ^ p)` increase to the pivotal integral of
`|K_o| ^ p`. No boundedness, no dominator, no cluster finiteness: the statement is in `ℝ≥0∞` and
the truncated subtraction makes the degenerate infinite-cluster case consistent (both sides are
then `0`). -/
theorem tendsto_lintegral_pivotal_truncation (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (p : ℕ) :
    Tendsto (fun n : ℕ => ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      atTop (𝓝 (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)) := by
  have hyx : ∀ ω : Config V, ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  have hmono : Monotone fun n : ℕ => ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
    fun m n hmn => lintegral_mono fun ω => monotone_pivotal_truncation _ _ (hyx ω) hmn
  have hsup : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)
      = ⨆ n : ℕ, ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ := by
    rw [← MeasureTheory.lintegral_iSup
      (f := fun n ω => (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)))
      (fun n => measurable_pivotal_truncation e o p n)
      (fun m n hmn ω => monotone_pivotal_truncation _ _ (hyx ω) hmn)]
    exact lintegral_congr fun ω => (iSup_pivotal_truncation _ _ (hyx ω)).symm
  simpa only [← hsup] using tendsto_atTop_iSup hmono

omit [Countable V] in
/-- **The cap-independent bound.** The capped pivotal flux is dominated by the uncapped pivotal
flux: the natural dominator for the truncation limit is the full flux itself. -/
theorem lintegral_pivotal_truncation_le (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (p n : ℕ) :
    (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      ≤ ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
  refine lintegral_mono fun ω => ?_
  have hyx : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  exact (le_iSup (fun m : ℕ => (min (m : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
    min (m : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))) n).trans_eq
    (iSup_pivotal_truncation _ _ hyx)

/-- **Window flux convergence.** For a finite set `S` of pairs with nonnegative weights `c`, the
window flux of the capped moments converges to the window flux of the uncapped moments. -/
theorem tendsto_lintegral_sum_pivotal_truncation (μ : Measure (Config V))
    (S : Finset (Sym2 V)) (c : Sym2 V → ℝ≥0) (o : V) (p : ℕ) :
    Tendsto (fun n : ℕ => ∑ e ∈ S, (c e : ℝ≥0∞) * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      atTop (𝓝 (∑ e ∈ S, (c e : ℝ≥0∞) * ∫⁻ ω,
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)) := by
  refine tendsto_finsetSum _ fun e _ => ?_
  have hg : Tendsto (fun x : ℝ≥0∞ => (c e : ℝ≥0∞) * x)
      (𝓝 (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ))
      (𝓝 ((c e : ℝ≥0∞) * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)) :=
    (ENNReal.continuous_const_mul (a := (c e : ℝ≥0∞)) (by simp)).tendsto _
  exact hg.comp (tendsto_lintegral_pivotal_truncation μ e o p)


/-! ### The real form -/

omit [Countable V] in
/-- The `ℝ≥0∞` pivotal increment is bounded by the cap. -/
theorem pivotal_truncation_le_cap (x y : ℝ≥0∞) (n : ℕ) :
    min (n : ℝ≥0∞) x - min (n : ℝ≥0∞) y ≤ (n : ℝ≥0∞) :=
  (tsub_le_self).trans (min_le_left _ _)

omit [Countable V] in
/-- The uncapped pivotal increment is finite almost surely when the inserted cluster is. -/
theorem pivotal_truncation_lt_top_of_ne_top {ω : Config V} {e : Sym2 V} {o : V} {p : ℕ}
    (h : ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) < ⊤ :=
  lt_of_le_of_lt tsub_le_self (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 h))

/-- Measurability of the uncapped pivotal increment. -/
theorem measurable_pivotal (e : Sym2 V) (o : V) (p : ℕ) :
    Measurable fun ω : Config V => (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) :=
  ((measurable_encard_cluster_insert_coe e o).pow_const p).sub
    ((measurable_encard_cluster_sdiff_coe e o).pow_const p)

/-- **Real form of the flux convergence.** The capped pivotal fluxes of `|K_o| ^ p`, viewed as
real numbers, converge to the pivotal flux of `|K_o| ^ p`.

The hypotheses are explicit and are exactly the ones under which the `ℝ≥0∞` identity of
`tendsto_lintegral_pivotal_truncation` is the difference of two finite real moments:

* `[IsFiniteMeasure μ]`;
* `hfin : μ`-almost surely the cluster of `o` after inserting `e` is finite (the cluster of `o`
  after deleting `e` is then finite too, since it is contained in it);
* `hflux`: the uncapped pivotal flux is finite. This is the `p`-th moment hypothesis of
  Lemma I.4.1 in the form in which the flux consumes it; it is not automatic and is not hidden.

Nothing is assumed about vertices other than `o` and the endpoints of `e`. -/
theorem tendsto_integral_pivotal_truncation (μ : Measure (Config V)) [IsFiniteMeasure μ]
    (e : Sym2 V) (o : V) (p : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ => ∫ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ)
      atTop (𝓝 (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ)) := by
  have hyx : ∀ ω : Config V, ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  -- each capped flux is finite
  have hne : ∀ n : ℕ, (∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω =>
      pivotal_truncation_le_cap _ _ n)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ univ)
  have hreal := (ENNReal.tendsto_toReal_iff hne hflux).2
    (tendsto_lintegral_pivotal_truncation μ e o p)
  -- identify the limit
  have hlim : (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ)
      = ((∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)).toReal :=
    (integral_toReal (measurable_pivotal e o p).aemeasurable
      (hfin.mono fun ω h => pivotal_truncation_lt_top_of_ne_top h))
  rw [hlim]
  refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hreal
  exact (integral_toReal ((measurable_pivotal_truncation e o p n).aemeasurable)
    (Eventually.of_forall fun ω => lt_of_le_of_lt
      (pivotal_truncation_le_cap _ _ n) (by simp))).symm


/-! ### Non-vacuity -/

/-- **Non-vacuity witness.** On `Bool` with the Dirac law at the empty configuration, `p = 1`,
`e = {false, true}` and `o = false`, both hypotheses of
`tendsto_integral_pivotal_truncation` hold: `Bool` is finite, so the cluster of `o` is a finite set
and its `encard` is not `⊤`; the uncapped pivotal flux is then finite by
`pivotal_truncation_lt_top_of_ne_top`. The conclusion, a genuine real convergence statement with a
nonzero limit, is therefore not vacuous. -/
example :
    Tendsto (fun n : ℕ => ∫ ω : Config Bool,
        (min (n : ℝ≥0∞) (((cluster (insert (s(false, true)) ω) false).encard : ℝ≥0∞) ^ 1) -
          min (n : ℝ≥0∞) (((cluster (ω \ {s(false, true)}) false).encard : ℝ≥0∞) ^ 1)).toReal
        ∂(Measure.dirac (∅ : Config Bool))) atTop
      (𝓝 (∫ ω : Config Bool,
        (((cluster (insert (s(false, true)) ω) false).encard : ℝ≥0∞) ^ 1 -
          ((cluster (ω \ {s(false, true)}) false).encard : ℝ≥0∞) ^ 1).toReal
        ∂(Measure.dirac (∅ : Config Bool)))) := by
  refine tendsto_integral_pivotal_truncation _ (s(false, true)) false 1 ?_ ?_
  · filter_upwards with ω
    simpa using (Set.toFinite (cluster (insert (s(false, true)) ω) false))
  · rw [lintegral_dirac]
    exact ne_of_lt (pivotal_truncation_lt_top_of_ne_top
      (by simpa using (Set.toFinite (cluster (insert (s(false, true)) ∅) false))))

end PercLib.Percolation.Bond

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Analysis

variable {a b M : ℝ}

/-- **Exact capped increment.** For `b ≥ 0` the increment of `x ↦ min x M` across
`a ↦ a + b` is the part of `b` that fits under the cap:
`min (a + b) M - min a M = min b (max 0 (M - a))`. -/
theorem min_add_sub_min_eq_min_sup_zero (hb : 0 ≤ b) :
    min (a + b) M - min a M = min b (max 0 (M - a)) := by
  rcases le_total M a with hMa | haM
  · have h1 : min (a + b) M = M := min_eq_right (by linarith)
    have h2 : min a M = M := min_eq_right hMa
    have h3 : max 0 (M - a) = 0 := max_eq_left (by linarith)
    have h4 : min b 0 = 0 := min_eq_right hb
    rw [h1, h2, h3, h4]
    ring
  · have h1 : min a M = a := min_eq_left haM
    have h3 : max 0 (M - a) = M - a := max_eq_right (by linarith)
    rw [h1, h3]
    rcases le_total (M - a) b with hle | hle
    · have h5 : min (a + b) M = M := min_eq_right (by linarith)
      have h6 : min b (M - a) = M - a := min_eq_right hle
      rw [h5, h6]
    · have h5 : min (a + b) M = a + b := min_eq_left (by linarith)
      have h6 : min b (M - a) = b := min_eq_left hle
      rw [h5, h6]
      ring

/-- **Off the cap the truncation is exact.** If `a + b ≤ M` then
`min (a + b) M - min a M = b`; the capped pivotal increment already equals the untruncated
one. -/
theorem min_add_sub_min_eq_of_add_le (hb : 0 ≤ b) (h : a + b ≤ M) :
    min (a + b) M - min a M = b := by
  rw [min_add_sub_min_eq_min_sup_zero hb]
  exact min_eq_left (le_max_of_le_right (by linarith))

/-- **Monotonicity in the cap.** The capped increment increases with the cap when `b ≥ 0`. -/
theorem monotone_min_add_sub_min (hb : 0 ≤ b) :
    Monotone fun M => min (a + b) M - min a M := by
  intro M M' hMM'
  change min (a + b) M - min a M ≤ min (a + b) M' - min a M'
  rw [min_add_sub_min_eq_min_sup_zero hb, min_add_sub_min_eq_min_sup_zero hb]
  exact min_le_min_left b (max_le_max le_rfl (by linarith))

/-- **Exact merge identity.** `a` times the capped increment of `x ↦ min x M` is
`min a M` times `min b (max 0 (M - a))`. This is the exact form of
`PercLib.Analysis.mul_min_add_sub_min_le`, whose right-hand side `min a M * min b M` is
genuinely larger when `0 < a` and `M < a + b`. -/
theorem mul_min_add_sub_min_eq (hb : 0 ≤ b) :
    a * (min (a + b) M - min a M) = min a M * min b (max 0 (M - a)) := by
  have hid := min_add_sub_min_eq_min_sup_zero (a := a) (b := b) (M := M) hb
  rcases le_total M a with hMa | haM
  · have h2 : min a M = M := min_eq_right hMa
    have h3 : max 0 (M - a) = 0 := max_eq_left (by linarith)
    have h4 : min b 0 = 0 := min_eq_right hb
    rw [hid, h2, h3, h4, mul_zero, mul_zero]
  · have h2 : min a M = a := min_eq_left haM
    rw [hid, h2]

/-- The exact merge identity implies the merge inequality
`PercLib.Analysis.mul_min_add_sub_min_le` for `M ≥ 0`. -/
theorem mul_min_add_sub_min_le_of_eq (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) :
    a * (min (a + b) M - min a M) ≤ min a M * min b M := by
  rw [mul_min_add_sub_min_eq hb]
  exact mul_le_mul_of_nonneg_left (min_le_min_left b (max_le hM (by linarith))) (le_min ha hM)

/-- **Exact capped increment of `p`-th powers.** For nonnegative `a`, `b` the increment of
`x ↦ min (x ^ p) M` across `a ↦ a + b` is the part of the untruncated increment
`(a + b) ^ p - a ^ p` that fits under the cap. This is the `p`-th power form of
`min_add_sub_min_eq_min_sup_zero`, i.e. the pointwise statement behind the truncation step of
Lemma I.4.1's right-hand side. -/
theorem min_pow_sub_min_pow_eq (p : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min ((a + b) ^ p) M - min (a ^ p) M =
      min ((a + b) ^ p - a ^ p) (max 0 (M - a ^ p)) := by
  have hb' : (0 : ℝ) ≤ (a + b) ^ p - a ^ p := by
    have : a ^ p ≤ (a + b) ^ p := pow_le_pow_left₀ ha (by linarith) p
    linarith
  have hid := min_add_sub_min_eq_min_sup_zero (a := a ^ p) (b := (a + b) ^ p - a ^ p)
    (M := M) hb'
  rwa [show a ^ p + ((a + b) ^ p - a ^ p) = (a + b) ^ p by ring] at hid

/-- **The power-capped increment is dominated by the untruncated one.** Uniformly in the cap
`M`: this is the `p`-th power dominator for the flux of the untruncated moment, whose
untruncated value is `(a + b) ^ p - a ^ p`. -/
theorem min_pow_sub_min_pow_le (p : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (M : ℝ) :
    min ((a + b) ^ p) M - min (a ^ p) M ≤ (a + b) ^ p - a ^ p := by
  rw [min_pow_sub_min_pow_eq p ha hb]
  exact min_le_left _ _

/-- **Caps below the minimal cluster volume are degenerate.** Two cluster volumes are at
least `1`, so every cap `M ≤ 1` (negative ones included) truncates both `min (a + b) M` and
`min a M` to `M`, and the increment is `0`. -/
theorem min_add_sub_min_eq_zero_of_one_le (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : M ≤ 1) :
    min (a + b) M - min a M = 0 := by
  rw [min_eq_right (by linarith), min_eq_right (by linarith)]
  ring

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **The capped pivotal increment is monotone in the cap.** The real expression is the one
occurring in the integrand of `hasDerivAt_integral_fun_of_transitive` at
`h = fun x => min x M`. -/
theorem capped_pivotal_mono (ω : Config V) (o y : V) :
    Monotone fun M : ℝ =>
      min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
        min ((cluster ω o).ncard : ℝ) M :=
  PercLib.Analysis.monotone_min_add_sub_min (Nat.cast_nonneg _)

/-- **The untruncated far cluster volume dominates every capped pivotal increment.** For
every cap `M ≥ 0` the capped increment of the cluster volume of `o` across the union with the
cluster of `y` is nonnegative and at most the cluster volume of `y`, uniformly in `M`. This is
the dominator needed to pass capped flux integrals to the untruncated one. On a finite vertex
type `ncard` is the cardinality, so this is the finite-`V` Russo integrand; on an infinite
cluster both sides collapse to `0` because `ncard` is then `0` (see
`ncard_cluster_univ_nat`), which is why infinite-volume statements use `encard`. -/
theorem capped_pivotal_nonneg_le (ω : Config V) (o y : V) (M : ℝ) :
    0 ≤ min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
        min ((cluster ω o).ncard : ℝ) M ∧
      min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
        min ((cluster ω o).ncard : ℝ) M ≤ ((cluster ω y).ncard : ℝ) := by
  rw [PercLib.Analysis.min_add_sub_min_eq_min_sup_zero (Nat.cast_nonneg _)]
  exact ⟨le_min (Nat.cast_nonneg _) (le_max_left 0 _), min_le_left _ _⟩

/-- **Above the sum of the two cluster volumes the cap does not bind.** -/
theorem capped_pivotal_eq_of_add_le (ω : Config V) (o y : V) {M : ℝ}
    (h : ((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ) ≤ M) :
    min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
      min ((cluster ω o).ncard : ℝ) M = ((cluster ω y).ncard : ℝ) :=
  PercLib.Analysis.min_add_sub_min_eq_of_add_le (Nat.cast_nonneg _) h

/-- **A cap at most `1` gives a vanishing pivotal increment.** Every cluster contains its
base vertex, so a finite cluster volume is at least `1`. Consequently the
capped derivative of the first moment is `0` for every cap `M ≤ 1`, and the capped
derivatives can only converge to the untruncated one along `M → ∞`. -/
theorem capped_pivotal_eq_zero_of_cap_le_one (ω : Config V) (o y : V)
    (ho : (cluster ω o).Finite) (hy : (cluster ω y).Finite) {M : ℝ} (hM : M ≤ 1) :
    min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
      min ((cluster ω o).ncard : ℝ) M = 0 := by
  have ho' : (1 : ℝ) ≤ (cluster ω o).ncard :=
    Nat.one_le_cast.2 ((Set.ncard_pos ho).2 ⟨o, mem_cluster_self ω o⟩)
  have hy' : (1 : ℝ) ≤ (cluster ω y).ncard :=
    Nat.one_le_cast.2 ((Set.ncard_pos hy).2 ⟨y, mem_cluster_self ω y⟩)
  exact PercLib.Analysis.min_add_sub_min_eq_zero_of_one_le ho' hy' hM

/-! ### Truncated susceptibility in `ℝ≥0∞` -/

/-- **Capped expected cluster volume increases to the susceptibility.** For every bond law on
a countable vertex type and every vertex `x`, the integer caps recover `chi` in `ℝ≥0∞`
without any finiteness hypothesis; `chi = ∞` is allowed, and then no finite real first moment
exists. -/
theorem iSup_lintegral_min_encard [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    (⨆ n : ℕ, ∫⁻ ω, min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞) ∂(law q)) = chi q x := by
  have hsup : ∀ y : ℝ≥0∞, (⨆ n : ℕ, min y (n : ℝ≥0∞)) = y := by
    intro y
    refine le_antisymm (ciSup_le fun n => min_le_left _ _) ?_
    by_cases hy : y = ⊤
    · subst hy
      rw [show (fun n : ℕ => min (⊤ : ℝ≥0∞) (n : ℝ≥0∞)) = fun n : ℕ => (n : ℝ≥0∞) from by
        funext n; simp]
      exact le_of_eq ENNReal.iSup_natCast.symm
    · have hy' : y ≤ ((⌈y.toNNReal⌉₊ : ℕ) : ℝ≥0∞) := by
        have h1 : y.toNNReal ≤ ⌈y.toNNReal⌉₊ := Nat.le_ceil _
        have h2 : ((y.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((⌈y.toNNReal⌉₊ : ℕ) : ℝ≥0∞) := by
          exact_mod_cast h1
        rwa [ENNReal.coe_toNNReal hy] at h2
      calc y = min y ((⌈y.toNNReal⌉₊ : ℕ) : ℝ≥0∞) := (min_eq_left hy').symm
        _ ≤ ⨆ n : ℕ, min y (n : ℝ≥0∞) := le_iSup (fun n : ℕ => min y (n : ℝ≥0∞)) _
  have hmeas_enc : Measurable fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞) := by
    have h := encard_cluster_eq_tsum (V := V) (x := x)
    simp only [h]
    exact Measurable.tsum fun y => measurable_const.indicator (measurableSet_conn x y)
  have hmono : Monotone fun n : ℕ => (fun ω : Config V =>
      min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞)) :=
    fun n n' h ω => min_le_min_left _ (by exact_mod_cast h)
  calc (⨆ n : ℕ, ∫⁻ ω, min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞) ∂(law q))
      = ∫⁻ ω, ⨆ n : ℕ, min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞) ∂(law q) :=
        (lintegral_iSup (fun n => hmeas_enc.min measurable_const) hmono).symm
    _ = ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂(law q) := by simp only [hsup]
    _ = chi q x := rfl

/-! ### The cap limit fails at intensity one on `ℕ` -/

/-- With every pair open, the cluster of every vertex is all of `ℕ`. -/
theorem cluster_univ_nat (x : ℕ) : cluster (Set.univ : Config ℕ) x = Set.univ := by
  ext y
  simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]

/-- **The infinite cluster has `ncard = 0`.** The `Set.ncard` of the infinite cluster at
intensity `1` on `ℕ` is zero, so a formalisation reading cluster volumes through `ncard`
sees a cluster of volume `0` — and a capped moment `0` for every cap — instead of an
infinite one. -/
theorem ncard_cluster_univ_nat (x : ℕ) : (cluster (Set.univ : Config ℕ) x).ncard = 0 := by
  rw [cluster_univ_nat]
  exact Set.infinite_univ.ncard

/-- The same cluster has full `encard`. -/
theorem encard_cluster_univ_nat (x : ℕ) :
    ((cluster (Set.univ : Config ℕ) x).encard : ℝ≥0∞) = ⊤ := by
  rw [cluster_univ_nat]
  simp

/-- At intensity `1` on `ℕ` the capped expected cluster volume equals the cap, so it
diverges in `ℝ≥0∞`: there is no finite first moment and hence no dominator of the capped
derivatives. -/
theorem lintegral_min_encard_nat (M : ℝ≥0∞) :
    ∫⁻ ω, min ((cluster ω (0 : ℕ)).encard : ℝ≥0∞) M ∂(law (fun _ : Sym2 ℕ => 1)) = M := by
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := cluster_univ_nat 0
  simp [law, PercLib.Probability.prodBernoulli_const, hc]

/-- Consequently `chi` is infinite there: the finite-dominator hypothesis is not merely
convenient at intensity `1` on `ℕ`, it fails. -/
theorem chi_nat_eq_top : chi (fun _ : Sym2 ℕ => 1) 0 = ∞ := by
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := cluster_univ_nat 0
  simp [chi, law, PercLib.Probability.prodBernoulli_const, hc]

/-! ### Non-vacuity -/

/-- The exact identity at concrete numbers where the cap binds. -/
example : min ((1 : ℝ) + 5) 2 - min 1 2 = min 5 (max 0 (2 - 1)) := by
  norm_num

/-- The untruncated increment is genuinely lost by a small cap: for two clusters of size `1`
and cap `1` the pivotal increment is `0`, while the untruncated increment is `1`. -/
example : min ((1 : ℝ) + 1) 1 - min 1 1 = 0 := by
  norm_num

/-- The bond-model domination statement is non-vacuous on the two-vertex set with no open
pair: both clusters are singletons, so the increment is bounded by `1`. -/
example : min (((cluster (∅ : Config Bool) false).ncard : ℝ) +
      ((cluster (∅ : Config Bool) true).ncard : ℝ)) 1 -
      min ((cluster (∅ : Config Bool) false).ncard : ℝ) 1 ≤
    ((cluster (∅ : Config Bool) true).ncard : ℝ) :=
  (capped_pivotal_nonneg_le (∅ : Config Bool) false true 1).2

end PercLib.Percolation.Bond


/-! ## Finite transitive Russo derivatives

The finite symmetric Russo formula also has the oriented form used in the binomial
expansion of Lemma I.4.1. These results use `ncard` on a finite vertex type; they are
not infinite-volume theorems. The cap monotonicity and cap-limit statements are
pointwise prerequisites for the missing infinite-volume argument.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- **Invariance of the oriented pivotal integral.** An intensity automorphism `σ` carries the
oriented flux integrand of the pair `(σ a, σ b)` to that of `(a, b)`. -/
theorem integral_oriented_invariant (J : Sym2 V → ℝ≥0) (σ : V ≃ V)
    (hσ : ∀ e, J (Sym2.map σ e) = J e) (h : ℝ → ℝ) (a b : V) :
    (∫ ω, (if ω ∈ conn (σ a) (σ b) then 0 else
        ((cluster ω (σ a)).ncard : ℝ) *
          (h (((cluster ω (σ a)).ncard : ℝ) + (cluster ω (σ b)).ncard) -
            h ((cluster ω (σ a)).ncard : ℝ))) ∂law (intensityProfile J 1)) =
      ∫ ω, (if ω ∈ conn a b then 0 else
        ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω a).ncard : ℝ))) ∂law (intensityProfile J 1) := by
  rw [← integral_image_sym2Map_of_invariant J σ hσ (fun ω =>
    (if ω ∈ conn (σ a) (σ b) then 0 else
      ((cluster ω (σ a)).ncard : ℝ) *
        (h (((cluster ω (σ a)).ncard : ℝ) + (cluster ω (σ b)).ncard) -
          h ((cluster ω (σ a)).ncard : ℝ))))]
  congr 1
  funext ω
  simp only [image_mem_conn_iff, cluster_image, Set.ncard_image_of_injective _ σ.injective]

open Classical in
/-- **The oriented Russo formula.** For a finite transitive intensity family `λ_u` with derivatives
`w` at `t`, and *any* `h : ℝ → ℝ`, the derivative of `u ↦ E_u h(|K_o|)` is

`∑_{y ≠ o} w(o,y) E_t[1{o ↮ y} |K_o| (h(|K_o| + |K_y|) - h(|K_o|))]`,

with coefficient `1` and only the root term: the shape used in Lemma I.4.1. -/
theorem hasDerivAt_integral_oriented_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ)
    (t : ℝ) (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (h : ℝ → ℝ) :
    HasDerivAt (fun u => ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1))
      (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard))) ∂law (intensityProfile (lam t) 1)) t := by
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨o⟩
  have hncard : ∀ (σ : V ≃ V) (ω : Config V) (x : V),
      (cluster (Sym2.map σ '' ω) (σ x)).ncard = (cluster ω x).ncard := by
    intro σ ω x
    rw [cluster_image, Set.ncard_image_of_injective _ σ.injective]
  have hroot : ∀ u (a : V), ∫ ω, h ((cluster ω a).ncard) ∂law (intensityProfile (lam u) 1) =
      ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1) := by
    intro u a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← integral_image_sym2Map_of_invariant (lam u) σ (hσ u)
      (fun ω => h ((cluster ω o).ncard))]
    congr 1
    funext ω
    rw [← hσa, hncard]
  have hfun : (fun u => ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1)) =
      fun u => (Fintype.card V : ℝ)⁻¹ *
        ∫ ω, ∑ v, h ((cluster ω v).ncard) ∂law (intensityProfile (lam u) 1) := by
    funext u
    rw [integral_finsetSum _ fun v _ => Integrable.of_finite]
    simp_rw [hroot u]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hV.ne', one_mul]
  rw [hfun]
  refine ((hasDerivAt_integral_sum_cluster_fun lam w t hlam h).const_mul _).congr_deriv ?_
  set μ := law (intensityProfile (lam t) 1)
  set G : V → V → ℝ := fun a b => ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
        h ((cluster ω a).ncard : ℝ))) ∂μ with hG
  set G2 : V → V → ℝ := fun a b => ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω b).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
        h ((cluster ω b).ncard : ℝ))) ∂μ with hG2
  -- splitting the symmetric integrand into the two oriented halves
  have hsplit : ∀ a b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω a).ncard : ℝ)) +
        ((cluster ω b).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω b).ncard : ℝ))) ∂μ = w s(a, b) * (G a b + G2 a b) := by
    intro a b
    simp only [hG, hG2]
    congr 1
    rw [← integral_add Integrable.of_finite Integrable.of_finite]
    congr 1
    funext ω
    by_cases hc : ω ∈ conn a b <;> simp [hc]
  -- swapping the two halves over the ordered pairs only uses symmetry of `w`
  have hswap : ∀ a b, G2 b a = G a b := by
    intro a b
    simp only [hG, hG2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hc : ω ∈ conn b a
    · have hc' : ω ∈ conn a b := by simpa only [conn_symm] using hc
      simp only [hc, hc', ↓reduceIte]
    · have hc' : ω ∉ conn a b := by simpa only [conn_symm] using hc
      simp only [hc, hc']
      rw [add_comm ((cluster ω b).ncard : ℝ) ((cluster ω a).ncard : ℝ)]
  have hG2sum : (∑ a, ∑ b, w s(a, b) * G2 a b) = ∑ a, ∑ b, w s(a, b) * G a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [hswap a b, Sym2.eq_swap]
  -- `w` and `G` are invariant under the intensity automorphisms
  have hw : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ e, w (Sym2.map σ e) = w e := by
    intro σ hσ e
    have h1 := hlam (Sym2.map σ e)
    simp_rw [hσ] at h1
    exact h1.unique (hlam e)
  have hGinv : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ a b, G (σ a) (σ b) = G a b := by
    intro σ hσ a b
    simp only [hG]
    exact integral_oriented_invariant (lam t) σ (hσ t) h a b
  have hwmk : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ a b, w s(σ a, σ b) = w s(a, b) := by
    intro σ hσ a b
    have h1 := hw σ hσ s(a, b)
    rwa [Sym2.map_mk] at h1
  -- one row of the oriented pair sum does not depend on the root
  have hrow : ∀ a, ∑ b, w s(a, b) * G a b = ∑ b, w s(o, b) * G o b := by
    intro a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← hσa, ← Equiv.sum_comp σ (fun b => w s(σ a, b) * G (σ a) b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hwmk σ hσ a b, hGinv σ hσ a b]
  -- hence the whole pair sum is `|V|` times the root row
  have hGdiag : G o o = 0 := by simp [hG, conn_self]
  have hR : (∑ a, ∑ b, w s(a, b) * G a b) =
      (Fintype.card V : ℝ) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * G o y := by
    simp_rw [hrow]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ o), hGdiag, mul_zero, zero_add]
  have hS : (∑ a, ∑ b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω a).ncard : ℝ)) +
        ((cluster ω b).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω b).ncard : ℝ))) ∂μ) =
      (∑ a, ∑ b, w s(a, b) * G a b) + (∑ a, ∑ b, w s(a, b) * G2 a b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsplit a b, mul_add]
  rw [hS, hG2sum, hR]
  have hc : (Fintype.card V : ℝ) ≠ 0 := hV.ne'
  field_simp
  ring

/-! ### The coefficient check of I.4.1 -/

/-- **Coefficient check for (I.4.1).** With the root factor kept (the mass-transport form used in
I.4.1), the oriented power integrand expands with the binomial coefficients `binom(p,ℓ)`,
`ℓ = 0, …, p − 1`. This is the root-multiplied form of `add_pow_succ_sub_pow_sub_pow`
(`k = p − 1`), i.e. `A ((A+B)^p − A^p) = ∑_{ℓ<p} binom(p,ℓ) A^{ℓ+1} B^{p−ℓ}`. -/
theorem mul_add_pow_sub_pow (A B : ℝ) (p : ℕ) :
    A * ((A + B) ^ p - A ^ p) =
      ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ^ (ℓ + 1) * B ^ (p - ℓ) := by
  rw [mul_sub, add_pow, Finset.mul_sum, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
  rw [add_sub_cancel_right]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

open Classical in
/-- **I.4.1-shaped power formula.** For a finite transitive intensity family, the derivative of
`u ↦ E_u |K_o|^p` is the oriented (mass-transport) sum with the binomial coefficients of I.4.1,
`∑_{y ≠ o} w(o,y) E_t[1{o ↮ y} ∑_{ℓ<p} binom(p,ℓ) |K_o|^{ℓ+1} |K_y|^{p−ℓ}]`. -/
theorem hasDerivAt_moment_oriented_pow (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (p : ℕ) :
    HasDerivAt (fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ p
        ∂law (intensityProfile (lam u) 1))
      (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) *
          ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) * ((cluster ω y).ncard : ℝ) ^ (p - ℓ))
        ∂law (intensityProfile (lam t) 1)) t := by
  refine (hasDerivAt_integral_oriented_of_transitive lam w t hlam hT o
    (fun x => x ^ p)).congr_deriv ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hc : ω ∈ conn o y
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    exact mul_add_pow_sub_pow _ _ p

open Classical in
/-- **The I.4.1 binomial shape.** The oriented flux of `hasDerivAt_moment_oriented_pow`, rewritten
as in Lemma I.4.1: a sum over `ℓ < p` of `binom(p,ℓ)` times the expectation of `|K_o|^{ℓ+1}`
against the weighted, pivotal-restricted sum over `y` of `|K_y|^{p−ℓ}`. -/
theorem flux_oriented_eq_binomial (J : Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (o : V) (p : ℕ) :
    (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1)) =
      ∑ ℓ ∈ Finset.range p, ∫ ω, (((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ∑ y ∈ Finset.univ.erase o, (if ω ∈ conn o y then 0 else
          w s(o, y) * ((cluster ω y).ncard : ℝ) ^ (p - ℓ)))
        ∂law (intensityProfile J 1) := by
  -- pull the `ℓ`-sum out of the `y`-integral, then swap the two finite sums
  have h1 : ∀ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
      ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1)
      = ∑ ℓ ∈ Finset.range p, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1) := by
    intro y _
    have hsplit : (fun ω : Config V => if ω ∈ conn o y then (0 : ℝ) else
        ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) =
        fun ω : Config V => ∑ ℓ ∈ Finset.range p, (if ω ∈ conn o y then 0 else
          ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
            ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) := by
      funext ω
      by_cases hc : ω ∈ conn o y <;> simp [hc]
    rw [hsplit, integral_finsetSum _ fun ℓ _ => Integrable.of_finite, Finset.mul_sum]
  -- move the weight inside each integral
  have h2 : ∀ ℓ ∈ Finset.range p, (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω,
      (if ω ∈ conn o y then 0 else ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1))
      = ∑ y ∈ Finset.univ.erase o, ∫ ω, (if ω ∈ conn o y then 0 else
        w s(o, y) * (((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ))) ∂law (intensityProfile J 1) := by
    intro ℓ _
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext ω
    by_cases hc : ω ∈ conn o y <;> simp [hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [h2 ℓ (by assumption)]
  rw [← integral_finsetSum _ fun y _ => Integrable.of_finite]
  congr 1
  funext ω
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hc : ω ∈ conn o y
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    ring

open Classical in
/-- **The I.4.1 RHS shape as a derivative.** Combining the oriented power formula with the binomial
rearrangement: in the finite transitive model the derivative of `E_u |K_o|^p` is the paper's
right-hand side, `∑_{ℓ<p} binom(p,ℓ) E_t[ |K_o|^{ℓ+1} ∑_{y ≠ o} w(o,y) 1(o ↮ y) |K_y|^{p−ℓ} ]`
(up to reading `w(o,y)` as the total weight `β|J'(r)| 1(‖o − y‖ ≤ r)` of the cut-off). -/
theorem hasDerivAt_moment_of_transitive_i41 (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (p : ℕ) :
    HasDerivAt (fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ p
        ∂law (intensityProfile (lam u) 1))
      (∑ ℓ ∈ Finset.range p, ∫ ω, (((p.choose ℓ : ℕ) : ℝ) *
          ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ∑ y ∈ Finset.univ.erase o, (if ω ∈ conn o y then 0 else
          w s(o, y) * ((cluster ω y).ncard : ℝ) ^ (p - ℓ)))
        ∂law (intensityProfile (lam t) 1)) t :=
  (hasDerivAt_moment_oriented_pow lam w t hlam hT o p).congr_deriv
    (flux_oriented_eq_binomial (lam t) w o p)

open Classical in
/-- **The bounded truncated power.** For every cap `M`, the derivative of `u ↦ E_u min(|K_o|^p, M)`
is the oriented flux of the truncated integrand. This is the bounded object one differentiates
before letting `M → ∞`; no boundedness of `M` or of the moment is needed, only the cap. -/
theorem hasDerivAt_truncated_pow_oriented (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (p : ℕ) (M : ℝ) :
    HasDerivAt (fun u => ∫ ω, min (((cluster ω o).ncard : ℝ) ^ p) M
        ∂law (intensityProfile (lam u) 1))
      (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) *
          (min ((((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) ^ p) M -
            min (((cluster ω o).ncard : ℝ) ^ p) M))
        ∂law (intensityProfile (lam t) 1)) t :=
  hasDerivAt_integral_oriented_of_transitive lam w t hlam hT o (fun x => min (x ^ p) M)

omit [DecidableEq V] in
/-- **Scope marker: at finite `V` the cap is eventually irrelevant.** For `M ≥ |V|^p` the truncated
moment coincides with the untruncated one. This is recorded to delimit what the finite statements
above can and cannot do: at finite `V` the passage `M → ∞` is vacuous, so no theorem of this file
implies the infinite-volume `M → ∞` step, which needs a dominator there. -/
theorem truncated_pow_eq_pow_of_card_pow_le (lam : ℝ → Sym2 V → ℝ≥0) (o : V) (p : ℕ) {M : ℝ}
    (hM : (Fintype.card V : ℝ) ^ p ≤ M) :
    (fun u => ∫ ω, min (((cluster ω o).ncard : ℝ) ^ p) M ∂law (intensityProfile (lam u) 1)) =
      fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ p ∂law (intensityProfile (lam u) 1) := by
  funext u
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hn : (cluster ω o).ncard ≤ Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_le_card (cluster ω o)
  refine min_eq_left (le_trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn) p) hM)

open Classical in
/-- **Coefficient consistency / mass transport.** The oriented formula (coefficient `1`, root term
only, as in I.4.1) and the library's symmetric formula (coefficient `1/2`, both terms) are two
values of the same derivative, hence equal. This is the mass-transport identity underlying the
step from Russo's formula to (I.4.1); in particular the paper's coefficient `1` is not a
normalisation slip for the library's `1/2`. -/
theorem oriented_eq_half_symm_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (h : ℝ → ℝ) :
    (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard))) ∂law (intensityProfile (lam t) 1)) =
      (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard)) +
          ((cluster ω y).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω y).ncard))) ∂law (intensityProfile (lam t) 1) :=
  (hasDerivAt_integral_oriented_of_transitive lam w t hlam hT o h).unique
    (hasDerivAt_integral_fun_of_transitive lam w t hlam hT o h)

/-- The cap increment of an increasing pair is at most the untruncated increment. -/
theorem min_sub_min_le_sub {a b M : ℝ} (hab : a ≤ b) : min b M - min a M ≤ b - a := by
  rw [min_def, min_def]
  split_ifs <;> linarith

open Classical in
/-- **Flux domination.** With nonnegative derivative weights, the capped flux of
`hasDerivAt_truncated_pow_oriented` is dominated term by term by the untruncated flux of
`hasDerivAt_moment_oriented_pow` (whose integrand is the binomial sum of `mul_add_pow_sub_pow`).
This is the domination inequality needed to pass the derivative formula to the cap limit. -/
theorem truncated_flux_le_flux (J : Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (o : V) (p : ℕ) (M : ℝ) :
    (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) *
          (min ((((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) ^ p) M -
            min (((cluster ω o).ncard : ℝ) ^ p) M))
        ∂law (intensityProfile J 1)) ≤
      ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) *
          ((((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) ^ p -
            ((cluster ω o).ncard : ℝ) ^ p))
        ∂law (intensityProfile J 1) := by
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hw _)
  refine integral_mono Integrable.of_finite Integrable.of_finite fun ω => ?_
  by_cases hc : ω ∈ conn o y
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact min_sub_min_le_sub (pow_le_pow_left₀ (by positivity)
      (le_add_of_nonneg_right (by positivity)) p)

/-! ### The cap passage `M → ∞` of the truncated flux term -/

/-- The cap increment of an increasing pair survives a larger cap. -/
theorem sub_min_sub_le {a b M M' : ℝ} (hab : a ≤ b) (hM : M ≤ M') :
    min a M' - min a M ≤ min b M' - min b M := by
  rw [min_def, min_def, min_def, min_def]
  split_ifs <;> linarith

/-- The truncated oriented flux term is nonnegative and increases with the cap. -/
theorem min_pow_sub_min_pow_mono {A B M M' : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) (hM : M ≤ M') :
    min ((A + B) ^ p) M - min (A ^ p) M ≤ min ((A + B) ^ p) M' - min (A ^ p) M' := by
  have hab : A ^ p ≤ (A + B) ^ p := pow_le_pow_left₀ hA (by linarith) p
  have h := sub_min_sub_le hab hM
  linarith

/-- The truncated oriented flux term is nonnegative. -/
theorem min_pow_sub_min_pow_nonneg {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    0 ≤ min ((A + B) ^ p) M - min (A ^ p) M := by
  have hab : A ^ p ≤ (A + B) ^ p := pow_le_pow_left₀ hA (by linarith) p
  have h := min_le_min_right M hab
  linarith

/-- **Monotone convergence input.** The truncated oriented flux term is monotone in the cap. -/
theorem monotone_min_pow_sub_min_pow {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    Monotone fun M : ℝ => min ((A + B) ^ p) M - min (A ^ p) M :=
  fun _ _ hM => min_pow_sub_min_pow_mono hA hB p hM

/-- **Cap limit.** As the cap grows, the truncated oriented flux term tends to the untruncated one,
i.e. the pointwise limit underlying the `M → ∞` passage from `min (|K_o|^p, M)` to `|K_o|^p`. -/
theorem tendsto_min_pow_sub_min_pow_atTop (A B : ℝ) (p : ℕ) :
    Tendsto (fun M : ℝ => min ((A + B) ^ p) M - min (A ^ p) M) atTop
      (𝓝 ((A + B) ^ p - A ^ p)) := by
  have h1 : Tendsto (fun M : ℝ => min ((A + B) ^ p) M) atTop (𝓝 ((A + B) ^ p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ((A + B) ^ p)] with M hM
    exact (min_eq_left hM).symm
  have h2 : Tendsto (fun M : ℝ => min (A ^ p) M) atTop (𝓝 (A ^ p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (A ^ p)] with M hM
    exact (min_eq_left hM).symm
  exact h1.sub h2

/-! ### Non-vacuity witness -/

open Classical in
/-- **Non-vacuity.** On `ZMod 2` with `λ_u = u⁺` (so `λ_u = u` near `t = 1`, `w = 1`) and the
translations as the transitive group, the hypotheses of the oriented power formula and of its
truncation hold, at `p = 2` and cap `1/2`. -/
example : ∃ D : ℝ, HasDerivAt (fun u : ℝ => ∫ ω,
      min (((cluster ω (0 : ZMod 2)).ncard : ℝ) ^ 2) (1 / 2)
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => u.toNNReal) 1)) D 1 ∧
    D = ∑ y ∈ Finset.univ.erase (0 : ZMod 2), (fun _ : Sym2 (ZMod 2) => (1 : ℝ)) s(0, y) *
      ∫ ω, (if ω ∈ conn 0 y then 0 else
        ((cluster ω (0 : ZMod 2)).ncard : ℝ) *
          (min ((((cluster ω (0 : ZMod 2)).ncard : ℝ) +
              (cluster ω y).ncard) ^ 2) (1 / 2) -
            min (((cluster ω (0 : ZMod 2)).ncard : ℝ) ^ 2) (1 / 2)))
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1) := by
  refine ⟨_, hasDerivAt_truncated_pow_oriented (fun (u : ℝ) _ => u.toNNReal) (fun _ => 1) 1 ?_
    (fun x y => ⟨Equiv.addRight (y - x), by simp, fun _ _ => rfl⟩) 0 2 (1 / 2), rfl⟩
  intro e
  refine (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
  simp [Real.coe_toNNReal _ hu.le]

end PercLib.Percolation.Bond



/-! ## Exact one-edge cluster algebra


-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Loops -/

/-- Opening a diagonal pair does not change the open graph: adjacency in `openGraph` also
requires the two endpoints to be distinct. -/
theorem openGraph_insert_diag (ω : Config V) (a : V) :
    openGraph (insert s(a, a) ω) = openGraph ω := by
  refine SimpleGraph.ext ?_
  ext x y
  rw [openGraph_adj_iff, openGraph_adj_iff]
  by_cases hne : x = y
  · subst hne
    simp
  · have hne' : s(x, y) ≠ s(a, a) := by
      intro h
      have hd : (s(x, y)).IsDiag := h ▸ (Sym2.mk_isDiag_iff (x := a) (y := a)).2 rfl
      exact hne ((Sym2.mk_isDiag_iff (x := x) (y := y)).1 hd)
    have hiff : (s(x, y) ∈ insert s(a, a) ω) ↔ (s(x, y) ∈ ω) := by
      rw [mem_insert_iff]
      exact ⟨fun h => h.elim (fun heq => absurd heq hne') id, fun h => Or.inr h⟩
    rw [hiff]

/-- Opening a diagonal pair does not change the cluster of any vertex. -/
theorem cluster_insert_diag (ω : Config V) (a x : V) :
    cluster (insert s(a, a) ω) x = cluster ω x := by
  simp only [cluster, openGraph_insert_diag]

/-! ### The root-edge identity -/

open Classical in
/-- **The exact root-edge pivotal increment of a cluster moment.** Opening the pair
`s(o, y)` and counting the cluster of `o` by `encard` changes the `p`-th power of its
volume by `((|K_o| + |K_y|)^p - |K_o|^p)` when `o` and `y` were not connected, and by
nothing when they were. The subtraction is truncated, so if the cluster of `o` is
infinite both sides are `0`; no finiteness hypothesis is used. -/
theorem encard_cluster_insert_pow_sub_eq (ω : Config V) (o y : V) (p : ℕ) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p =
      if ω ∈ conn o y then 0
      else (((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p := by
  classical
  by_cases h : ω ∈ conn o y
  · have hKy : cluster ω y = cluster ω o := (cluster_eq_of_mem_conn h).symm
    have hno : cluster (insert s(o, y) ω) o = cluster ω o := by
      refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) o)
      intro z hz
      have hz' := cluster_insert_subset ω o y o hz
      simpa [hKy] using hz'
    rw [hno, ite_eq_left h, tsub_self]
  · have hdisj : Disjoint (cluster ω o) (cluster ω y) := by
      refine Set.disjoint_left.2 fun z hzo hzy => h ?_
      have hzy' : ω ∈ conn z y := by rwa [mem_cluster_iff, conn_symm] at hzy
      have hoz : ω ∈ conn o z := (mem_cluster_iff ω o z).1 hzo
      exact conn_trans hoz hzy'
    have hunion : cluster (insert s(o, y) ω) o = cluster ω o ∪ cluster ω y :=
      cluster_insert_of_mem ω o y o (Or.inl (mem_cluster_self ω o))
    rw [hunion, Set.encard_union_eq hdisj, ite_eq_right h, ENat.toENNReal_add]

/-! ### Pairs with one endpoint in the cluster -/

/-- If both endpoints of the pair `s(a, b)` are already in the cluster of `x`, opening it
does not change that cluster. Includes the loop case `a = b`. -/
theorem cluster_insert_eq_of_mem_of_mem {ω : Config V} {a b x : V}
    (ha : x ∈ cluster ω a) (hb : x ∈ cluster ω b) :
    cluster (insert s(a, b) ω) x = cluster ω x := by
  have hax : a ∈ cluster ω x := (mem_cluster_comm ω x a).2 ha
  have hbx : b ∈ cluster ω x := (mem_cluster_comm ω x b).2 hb
  refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) x)
  intro z hz
  rcases cluster_insert_subset ω a b x hz with (h | h) | h
  · exact h
  · rwa [← cluster_eq_of_mem_conn ((mem_cluster_iff ω x a).1 hax)] at h
  · rwa [← cluster_eq_of_mem_conn ((mem_cluster_iff ω x b).1 hbx)] at h

open Classical in
/-- **Exact increment, one endpoint in the cluster.** If `x` lies in the cluster of `a`
but not in the cluster of `b`, opening `s(a, b)` merges the two clusters and the `p`-th
power of the `encard` of the cluster of `x` (which is that of `a`) grows by
`((|K_a| + |K_b|)^p - |K_a|^p)`. -/
theorem encard_cluster_insert_pow_sub_eq_of_mem_of_not_mem {ω : Config V} {a b x : V}
    (p : ℕ) (ha : x ∈ cluster ω a) (hb : x ∉ cluster ω b) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p -
        ((cluster ω x).encard : ℝ≥0∞) ^ p =
      (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
        ((cluster ω a).encard : ℝ≥0∞) ^ p := by
  have hxK : cluster ω x = cluster ω a :=
    (cluster_eq_of_mem_conn ((mem_cluster_iff ω a x).1 ha)).symm
  have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
    refine Set.disjoint_left.2 fun z hza hzb => hb ?_
    have hax : ω ∈ conn x a := by
      rw [conn_symm]
      exact (mem_cluster_iff ω a x).1 ha
    have haz : ω ∈ conn a z := (mem_cluster_iff ω a z).1 hza
    have h1 : ω ∈ conn x z := conn_trans hax haz
    have h2 : ω ∈ conn z b := by rwa [mem_cluster_iff, conn_symm] at hzb
    have hxb : ω ∈ conn x b := conn_trans h1 h2
    rw [mem_cluster_iff, conn_symm]
    exact hxb
  have hunion : cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b :=
    cluster_insert_of_mem ω a b x (Or.inl ha)
  rw [hunion, Set.encard_union_eq hdisj, hxK, ENat.toENNReal_add]

open Classical in
/-- **Exact increment, the other endpoint in the cluster.** If `x` lies in the cluster of
`b` but not in the cluster of `a`, opening `s(a, b)` grows the `p`-th power of the
`encard` of the cluster of `x` (which is that of `b`) by
`((|K_a| + |K_b|)^p - |K_b|^p)`. -/
theorem encard_cluster_insert_pow_sub_eq_of_not_mem_of_mem {ω : Config V} {a b x : V}
    (p : ℕ) (ha : x ∉ cluster ω a) (hb : x ∈ cluster ω b) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p -
        ((cluster ω x).encard : ℝ≥0∞) ^ p =
      (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
        ((cluster ω b).encard : ℝ≥0∞) ^ p := by
  have hxK : cluster ω x = cluster ω b :=
    (cluster_eq_of_mem_conn ((mem_cluster_iff ω b x).1 hb)).symm
  have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
    refine Set.disjoint_left.2 fun z hza hzb => ha ?_
    have hbx : ω ∈ conn x b := by
      rw [conn_symm]
      exact (mem_cluster_iff ω b x).1 hb
    have hbz : ω ∈ conn b z := (mem_cluster_iff ω b z).1 hzb
    have h1 : ω ∈ conn x z := conn_trans hbx hbz
    have h2 : ω ∈ conn z a := by rwa [mem_cluster_iff, conn_symm] at hza
    have hxa : ω ∈ conn x a := conn_trans h1 h2
    rw [mem_cluster_iff, conn_symm]
    exact hxa
  have hunion : cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b :=
    cluster_insert_of_mem ω a b x (Or.inr hb)
  rw [hunion, Set.encard_union_eq hdisj, hxK, ENat.toENNReal_add]

open Classical in
/-- **The four-case exact increment.** Opening the pair `s(a, b)` changes the `p`-th power
of the `encard` of the cluster of `x` by `0` when `x` is in both clusters or in neither,
and by the merge increment of the two clusters when `x` is in exactly one of them. -/
theorem encard_cluster_insert_pow_sub_eq_cases {ω : Config V} {a b x : V} (p : ℕ) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p -
        ((cluster ω x).encard : ℝ≥0∞) ^ p =
      if x ∈ cluster ω a then
        (if x ∈ cluster ω b then 0
         else (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
           ((cluster ω a).encard : ℝ≥0∞) ^ p)
      else
        (if x ∈ cluster ω b then
          (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
            ((cluster ω b).encard : ℝ≥0∞) ^ p
         else 0) := by
  by_cases ha : x ∈ cluster ω a
  · by_cases hb : x ∈ cluster ω b
    · rw [cluster_insert_eq_of_mem_of_mem ha hb, tsub_self]
      simp only [ha, hb, ↓reduceIte]
    · rw [encard_cluster_insert_pow_sub_eq_of_mem_of_not_mem p ha hb]
      simp only [ha, hb, ↓reduceIte]
  · by_cases hb : x ∈ cluster ω b
    · rw [encard_cluster_insert_pow_sub_eq_of_not_mem_of_mem p ha hb]
      simp only [ha, hb, ↓reduceIte]
    · rw [PercLib.Models.LongRange.cluster_insert_eq_of_forall_not_mem (ω := ω) (o := x)
        (e := s(a, b)) ?_, tsub_self]
      · simp only [ha, hb, ↓reduceIte]
      · intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with hza | hzb
        · subst hza
          exact fun h => ha ((mem_cluster_comm ω x z).1 h)
        · subst hzb
          exact fun h => hb ((mem_cluster_comm ω x z).1 h)

/-! ### The insertion/deletion form used by the derivative -/

open Classical in
/-- **The exact pivotal increment of the derivative integrand.** The function differentiated
by Russo's formula is `F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard`.
For `e = s(o, y)` and `F = (· ^ p)` this is the same root-edge identity, with `ω` replaced
by `ω \ {e}`: inserting into the configuration with `e` deleted is inserting into `ω`. -/
theorem encard_cluster_insert_pow_sub_sdiff_eq (ω : Config V) (o y : V) (p : ℕ) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p =
      if (ω \ {s(o, y)}) ∈ conn o y then 0
      else (((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) +
          ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞)) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p := by
  rw [← Set.insert_sdiff_singleton (s := ω) (a := s(o, y))]
  exact encard_cluster_insert_pow_sub_eq (ω \ {s(o, y)}) o y p

open Classical in
/-- **The first-moment increment is at most the far cluster volume.** For `p = 1` the
root-edge identity gives that opening `s(o, y)` increases the `encard` of the cluster of
`o` by at most `|K_y|`, and by nothing when `o` and `y` are already connected. No
finiteness hypothesis is used: the truncated subtraction `⊤ - ⊤ = 0` only makes the
bound easier. -/
theorem encard_cluster_insert_sub_le (ω : Config V) (o y : V) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) - ((cluster ω o).encard : ℝ≥0∞) ≤
      if ω ∈ conn o y then 0 else ((cluster ω y).encard : ℝ≥0∞) := by
  have h := encard_cluster_insert_pow_sub_eq ω o y 1
  simp only [pow_one] at h
  rw [h]
  by_cases hc : ω ∈ conn o y
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact tsub_le_iff_right.2 (le_of_eq (add_comm _ _))

open Classical in
/-- **The first-moment increment is exactly the far cluster volume when the root cluster is
finite.** With `|K_o| ≠ ⊤` the truncation does not bite and the increment of the `encard`
of the cluster of `o` is exactly `|K_y|` off the connection event, and `0` on it. The
finiteness hypothesis is necessary: for an infinite cluster of `o` the increment is `⊤ - ⊤
= 0` while `|K_y|` may be nonzero. -/
theorem encard_cluster_insert_sub_eq_of_ne_top (ω : Config V) (o y : V)
    (ho : ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) - ((cluster ω o).encard : ℝ≥0∞) =
      if ω ∈ conn o y then 0 else ((cluster ω y).encard : ℝ≥0∞) := by
  have h := encard_cluster_insert_pow_sub_eq ω o y 1
  simp only [pow_one] at h
  rw [h]
  by_cases hc : ω ∈ conn o y
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact (ENNReal.cancel_of_ne ho).add_tsub_cancel_left

/-! ### The capped increment -/

open Classical in
/-- **The capped increment is dominated by the uncapped exact flux.** For every cap `M`,
truncating the `p`-th powers at `M` cannot increase the pivotal increment of the root-edge
identity. This is the pointwise form of the domination used to pass the capped flux
integrals to the uncapped one; it is cap-independent on the right-hand side. -/
theorem min_encard_cluster_insert_pow_sub_le (ω : Config V) (o y : V) (p : ℕ) (M : ℝ≥0∞) :
    min M (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p) -
        min M (((cluster ω o).encard : ℝ≥0∞) ^ p) ≤
      if ω ∈ conn o y then 0
      else (((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p := by
  by_cases h : ω ∈ conn o y
  · have hKy : cluster ω y = cluster ω o := (cluster_eq_of_mem_conn h).symm
    have hno : cluster (insert s(o, y) ω) o = cluster ω o := by
      refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) o)
      intro z hz
      have hz' := cluster_insert_subset ω o y o hz
      simpa [hKy] using hz'
    rw [hno, ite_eq_left h, tsub_self]
  · rw [ite_eq_right h]
    have hmain := encard_cluster_insert_pow_sub_eq ω o y p
    rw [ite_eq_right h] at hmain
    rw [← hmain]
    have hvol : ((cluster ω o).encard : ℝ≥0∞) ≤
        ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) := by
      exact_mod_cast Set.encard_mono (cluster_mono (subset_insert _ _) o)
    have hyx : ((cluster ω o).encard : ℝ≥0∞) ^ p ≤
        ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p :=
      pow_le_pow_left' hvol p
    rw [min_tsub_min_eq hyx]
    have hmin : min M (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p) ≤
        ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p :=
      min_le_right M (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p)
    exact tsub_le_tsub_right hmin _

/-! ### The real form -/

open Classical in
/-- **The real form of the exact pivotal increment.** If the cluster of `o` after opening
`s(o, y)` and the cluster of `y` after deleting it are both finite, then the real
difference of the `p`-th powers of the corresponding `encard`s is the real merge increment
`((|K_o| + |K_y|)^p - |K_o|^p)`, and `0` when `o` and `y` are already connected. The
finiteness hypotheses are explicit and necessary: on an infinite cluster the truncated
`ℝ≥0∞` subtraction is `0`, which no real difference reproduces. -/
theorem encard_cluster_insert_pow_sub_sdiff_eq_real (ω : Config V) (o y : V) (p : ℕ)
    (hX : ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hB : ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞) ≠ ⊤) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞).toReal ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal ^ p =
      if (ω \ {s(o, y)}) ∈ conn o y then 0
      else ((((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal +
          ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞).toReal) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal ^ p) := by
  have hA : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top hX (encard_cluster_sdiff_le_insert_coe ω (s(o, y)) o)
  have hAB : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) +
      ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hA, hB⟩
  have hXA : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ≤
      ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) :=
    encard_cluster_sdiff_le_insert_coe ω (s(o, y)) o
  have hYX : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p :=
    pow_le_pow_left' hXA p
  have hXp : ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p ≠ ⊤ :=
    ENNReal.pow_ne_top hX
  rw [← ENNReal.toReal_pow, ← ENNReal.toReal_pow,
    ← ENNReal.toReal_sub_of_le hYX hXp, encard_cluster_insert_pow_sub_sdiff_eq]
  by_cases h : (ω \ {s(o, y)}) ∈ conn o y
  · simp only [h, ite_eq_left, ENNReal.toReal_zero]
  · simp only [h, ↓reduceIte]
    rw [ENNReal.toReal_sub_of_le (pow_le_pow_left' (le_add_right le_rfl) p)
      (ENNReal.pow_ne_top hAB), ENNReal.toReal_pow, ENNReal.toReal_add hA hB]

/-! ### The exact binomial (far-cluster) expansion -/

/-- **The pivotal increment as a far-cluster binomial sum.** For finite cluster volumes
`A = |K_o|` and `B = |K_y|`, the merge increment of the `p`-th power is the binomial sum
`∑_{ℓ<p} C(p, ℓ) A^ℓ B^{p-ℓ}`: the `ℓ = 0` term is the pure far-cluster term `B^p`, and
every other term carries a power of the far cluster volume. This is the un-multiplied
companion of `mul_pow_sub_pow_eq_sum_choose_ennreal` (which keeps the mass-transport factor
`|K_o|`), and the exact form of the binomial step of Lemma I.4.1 at one edge. -/
theorem pow_add_sub_pow_eq_sum_choose_ennreal {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (p : ℕ) :
    (A + B) ^ p - A ^ p =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * A ^ ℓ * B ^ (p - ℓ) := by
  have ha : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hdiff : 0 ≤ (A.toReal + B.toReal) ^ p - A.toReal ^ p := by
    have hle : A.toReal ^ p ≤ (A.toReal + B.toReal) ^ p :=
      pow_le_pow_left₀ ha (by linarith) p
    linarith
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
    ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ A.toReal + B.toReal),
    ← ENNReal.ofReal_pow ha,
    ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ A.toReal ^ p)]
  rw [← PercLib.Probability.sum_choose_mul_pow_eq_pow_sub]
  rw [ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by positivity)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

end PercLib.Percolation.Bond



/-! ## The infinite pair sum in the truncated Russo flux


-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.Analysis

/-! ### Commuting a monotone `ℕ`-supremum with `∑'` -/

/-- **A supremum over a monotone `ℕ`-family commutes with a finite sum.** -/
theorem iSup_finset_sum_of_monotone {ι : Type*} (s : Finset ι) (f : ℕ → ι → ℝ≥0∞)
    (hmono : ∀ e ∈ s, Monotone fun n => f n e) :
    (⨆ n, ∑ e ∈ s, f n e) = ∑ e ∈ s, ⨆ n, f n e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hmono' : ∀ e ∈ s, Monotone fun n => f n e :=
      fun e he => hmono e (Finset.mem_insert_of_mem he)
    have hsum : Monotone fun n => ∑ e ∈ s, f n e :=
      fun m n hmn => Finset.sum_le_sum fun e he => hmono' e he hmn
    have step : (⨆ n, ∑ e ∈ insert a s, f n e) = ⨆ n, (f n a + ∑ e ∈ s, f n e) :=
      iSup_congr fun n => Finset.sum_insert ha
    rw [step, Finset.sum_insert ha,
      ← ENNReal.iSup_add_iSup_of_monotone (hmono a (Finset.mem_insert_self a s)) hsum,
      ih hmono']

/-- **A supremum over a monotone `ℕ`-family commutes with `∑'`.**

For `f n e` monotone in `n` for every `e`,
`⨆ n, ∑' e, f n e = ∑' e, ⨆ n, f n e`. No summability is involved: both sides are `ℝ≥0∞`. -/
theorem iSup_tsum_of_monotone {ι : Type*} [Countable ι] (f : ℕ → ι → ℝ≥0∞)
    (hmono : ∀ e, Monotone fun n => f n e) :
    (⨆ n, ∑' e, f n e) = ∑' e, ⨆ n, f n e := by
  calc (⨆ n, ∑' e, f n e) = ⨆ n, ⨆ s : Finset ι, ∑ e ∈ s, f n e :=
        iSup_congr fun n => ENNReal.tsum_eq_iSup_sum
    _ = ⨆ s : Finset ι, ⨆ n, ∑ e ∈ s, f n e := iSup_comm
    _ = ⨆ s : Finset ι, ∑ e ∈ s, ⨆ n, f n e :=
        iSup_congr fun s => iSup_finset_sum_of_monotone s f fun e _ => hmono e
    _ = ∑' e, ⨆ n, f n e := (ENNReal.tsum_eq_iSup_sum).symm

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The pair sum and the measure integral -/

/-- **Tonelli for the pivotal flux of `|K_o|^p`.** For any measure on bond configurations, any
pair weight `c : Sym2 V → ℝ≥0∞`, root `o` and exponent `p`, the integral of the weighted pair sum
of pivotal increments is the weighted pair sum of the integrals.

Nothing is assumed about `c`, about the number of pairs with `c e ≠ 0`, about cluster finiteness,
or about finiteness of the sums: the pivotal increments are `ℝ≥0∞`-valued, and the truncated
subtraction makes the degenerate infinite-cluster case consistent. -/
theorem lintegral_tsum_pivotal_flux (μ : Measure (Config V)) (c : Sym2 V → ℝ≥0∞) (o : V)
    (p : ℕ) :
    ∫⁻ ω, ∑' e, c e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ
      = ∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
  rw [lintegral_tsum]
  · exact tsum_congr fun e => lintegral_const_mul (c e) (measurable_pivotal e o p)
  · exact fun e => (measurable_const.mul (measurable_pivotal e o p)).aemeasurable

/-- **The truncation cap can be removed through the infinite weighted pair sum.**

For any measure on bond configurations, any pair weight `c`, root `o` and exponent `p`, the
supremum over the cap `n` of the infinite weighted sums of capped pivotal integrals of `|K_o|^p` is
the infinite weighted sum of the uncapped pivotal integrals.

This monotone argument does not require a summable majorant over the pairs. The unit-weight
witness `tsum_pivotal_flux_eq_top_of_dirac` shows why such a majorant cannot be taken for
granted independently of the model's weights and finite-support restriction. -/
theorem iSup_tsum_lintegral_pivotal_truncation (μ : Measure (Config V)) (c : Sym2 V → ℝ≥0∞)
    (o : V) (p : ℕ) :
    (⨆ n : ℕ, ∑' e, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
  -- the monotonicity in the configuration
  have hyx : ∀ (ω : Config V) (e : Sym2 V),
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω e => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  -- the monotonicity in the cap, for each pair
  have hmono : ∀ e : Sym2 V, Monotone fun n : ℕ => c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ := by
    intro e m n hmn
    refine mul_le_mul_of_nonneg_left (lintegral_mono fun ω => ?_) zero_le
    exact monotone_pivotal_truncation _ _ (hyx ω e) hmn
  -- the cap limit for each pair
  have hper : ∀ e : Sym2 V, (⨆ n : ℕ, ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
    intro e
    rw [← lintegral_iSup (fun n => measurable_pivotal_truncation e o p n)
      (fun m n hmn ω => monotone_pivotal_truncation _ _ (hyx ω e) hmn)]
    exact lintegral_congr fun ω => iSup_pivotal_truncation _ _ (hyx ω e)
  calc (⨆ n : ℕ, ∑' e, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∑' e, ⨆ n : ℕ, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
        PercLib.Analysis.iSup_tsum_of_monotone _ hmono
    _ = ∑' e, c e * ⨆ n : ℕ, ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
        tsum_congr fun e => (ENNReal.mul_iSup _ _).symm
    _ = ∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
        exact tsum_congr fun e => by rw [hper e]

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The real form: the finiteness that is *not* free -/

/-- **Real form of the cap limit through the infinite weighted pair sum.**

If the total uncapped weighted pivotal flux is finite, then the `ℝ≥0∞` cap limit of
`iSup_tsum_lintegral_pivotal_truncation` is a limit of finite `ℝ≥0∞` numbers and can be read in
`ℝ`. The hypothesis `htot` is not a leftover: `tsum_lintegral_pivotal_flux_dirac_eq_top` shows it
fails for this Dirac measure with all pair weights equal to `1`, even though every cluster is
finite and every moment is finite there. It is therefore *not* implied by a.e. finiteness of
clusters, nor by finiteness of any cluster moment. -/
theorem tendsto_toReal_tsum_lintegral_pivotal_truncation (μ : Measure (Config V))
    (c : Sym2 V → ℝ≥0∞) (o : V) (p : ℕ)
    (htot : (∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ => (∑' e, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal)
      atTop (𝓝 ((∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ).toReal)) := by
  have hyx : ∀ (ω : Config V) (e : Sym2 V),
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω e => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  have hmono : Monotone fun n : ℕ => ∑' e, c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
    fun m n hmn => ENNReal.tsum_le_tsum fun e =>
      mul_le_mul_of_nonneg_left (lintegral_mono fun ω =>
        monotone_pivotal_truncation _ _ (hyx ω e) hmn) zero_le
  have hsup := iSup_tsum_lintegral_pivotal_truncation μ c o p
  have hne : ∀ n : ℕ, (∑' e, c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (hsup ▸ htot) (hsup ▸ le_iSup (fun n : ℕ => ∑' e, c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ) n)
  refine (ENNReal.tendsto_toReal_iff hne htot).2 ?_
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-! ### The total uncapped pair flux is infinite at the Dirac law

The next two results answer the question "is the finiteness hypothesis of
`tendsto_toReal_tsum_lintegral_pivotal_truncation` automatic?". It is not, and the failure is not
a formality: at the Dirac law on the empty configuration of `ℤ^d` the cluster of every vertex is
the singleton of that vertex, so every cluster is finite, every moment is finite and the model is
as degenerate as it can be, yet the total pivotal flux over *all* pairs is `⊤` because the
infinitely many pairs at the origin are each pivotal. -/

/-- At the empty configuration, inserting a pair `s(0, y)` with `y ≠ 0` adds `y` to the cluster of
`0`, so the `p`-th power of the cluster volume rises from `1` to at least `2`: the pivotal
increment is at least `1`. -/
theorem one_le_pivotal_flux_dirac (d : ℕ) (p : ℕ) (hp : 1 ≤ p) {y : Fin d → ℤ}
    (hy : y ≠ 0) :
    1 ≤ (((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p -
        ((cluster ((∅ : Config (Fin d → ℤ)) \ {s(0, y)}) 0).encard : ℝ≥0∞) ^ p) := by
  have hmem : y ∈ cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0 := by
    refine SimpleGraph.Adj.reachable ?_
    rw [openGraph_adj_iff]
    exact ⟨by simp, fun h => hy h.symm⟩
  have hsub : ({0, y} : Set (Fin d → ℤ)) ⊆
      cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0 := by
    intro z hz
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · rw [hz]; exact mem_cluster_self _ _
    · rw [Set.mem_singleton_iff.1 hz]; exact hmem
  have hpair : (2 : ℝ≥0∞) ≤
      ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) := by
    have h := Set.encard_le_encard hsub
    rw [Set.encard_pair (Ne.symm hy)] at h
    exact ENat.toENNReal_mono h
  have hbase : ((cluster ((∅ : Config (Fin d → ℤ)) \ {s(0, y)}) 0).encard : ℝ≥0∞) ^ p = 1 := by
    have hset : cluster ((∅ : Config (Fin d → ℤ)) \ {s(0, y)}) 0 = {0} := by
      rw [Set.empty_sdiff, cluster_empty]
    rw [hset]
    simp
  have hpow : (2 : ℝ≥0∞) ≤
      ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p := by
    calc (2 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ≥0∞) ^ p := pow_le_pow_right₀ (by norm_num) hp
      _ ≤ ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p :=
          ENNReal.pow_le_pow_left hpair
  rw [hbase]
  have hmono : (2 : ℝ≥0∞) - 1 ≤
      ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p - 1 :=
    tsub_le_tsub_right hpow 1
  rw [show (2 : ℝ≥0∞) - 1 = 1 by
    rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num, ENNReal.add_sub_cancel_left (by simp)]
    ] at hmono
  exact hmono

/-- **The total uncapped pivotal flux is infinite at the empty configuration of `ℤ^d`.**

For `d ≥ 1`, `p ≥ 1`, the sum over all pairs of the pivotal increment of `|K_0|^p` at `ω = ∅` is
`⊤`: the pairs `s(0, y)`, `y ≠ 0`, are infinitely many and each contributes at least `1`. In
particular this Dirac unit-weight example rules out a nonnegative summable majorant for the
unit-weight all-pairs sum. It is not a statement about a cut-off long-range law or its weights. -/
theorem tsum_pivotal_flux_eq_top_of_dirac (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    (∑' e : Sym2 (Fin d → ℤ),
      (((cluster (insert e (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p -
        ((cluster ((∅ : Config (Fin d → ℤ)) \ {e}) 0).encard : ℝ≥0∞) ^ p)) = ⊤ := by
  classical
  let i : Fin d := ⟨0, hd⟩
  have hne : ∀ n : ℕ, Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1) ≠ 0 := by
    intro n h
    have hval := congrFun h i
    rw [Function.update_self, Pi.zero_apply] at hval
    omega
  have hinj : Function.Injective fun n : ℕ =>
      s(0, Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1)) := by
    intro m n hmn
    have h1 : Function.update (0 : Fin d → ℤ) i ((m : ℤ) + 1) =
        Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1) := by
      rcases (Sym2.mk_eq_mk_iff (p := (0, Function.update (0 : Fin d → ℤ) i ((m : ℤ) + 1)))
        (q := (0, Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1)))).1 hmn with h | h
      · exact congrArg Prod.snd h
      · exact absurd (congrArg Prod.fst h).symm (hne n)
    have hval := congrFun h1 i
    rw [Function.update_self, Function.update_self] at hval
    omega
  have hstep : (∑' n : ℕ, (1 : ℝ≥0∞)) ≤ ∑' e : Sym2 (Fin d → ℤ),
      (((cluster (insert e (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p -
        ((cluster ((∅ : Config (Fin d → ℤ)) \ {e}) 0).encard : ℝ≥0∞) ^ p) := by
    refine le_trans (ENNReal.tsum_le_tsum fun n => ?_)
      (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
    exact one_le_pivotal_flux_dirac d p hp (hne n)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (c := (1 : ℝ≥0∞)) one_ne_zero] at hstep
  exact top_le_iff.1 hstep

/-- **The finiteness hypothesis of the real cap limit fails at a law with finite clusters.**

At the Dirac law on the empty configuration of `ℤ^d`, `d ≥ 1`, the total weighted pivotal flux with
all pair weights `1` is `⊤` (`tsum_pivotal_flux_eq_top_of_dirac` read through the Dirac integral),
while the `p`-th moment of the cluster volume is `1`
(`lintegral_encard_cluster_pow_dirac`). So a.e. finiteness of clusters and finiteness of the
cluster moment do not make the total pair flux finite. -/
theorem tsum_lintegral_pivotal_flux_dirac_eq_top (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    (∑' e : Sym2 (Fin d → ℤ), (1 : ℝ≥0∞) * ∫⁻ ω : Config (Fin d → ℤ),
      (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p)
        ∂Measure.dirac (∅ : Config (Fin d → ℤ))) = ⊤ := by
  simpa using tsum_pivotal_flux_eq_top_of_dirac d hd p hp

/-- The `p`-th moment of the cluster volume at the Dirac law on the empty configuration is `1`, in
particular finite. -/
theorem lintegral_encard_cluster_pow_dirac (d : ℕ) (p : ℕ) :
    ∫⁻ ω : Config (Fin d → ℤ), ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂Measure.dirac (∅ : Config (Fin d → ℤ)) = 1 := by
  rw [lintegral_dirac, cluster_empty]
  simp

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-! ### Non-vacuity of the real cap limit

The finiteness hypothesis of `tendsto_toReal_tsum_lintegral_pivotal_truncation` is satisfiable, and
the convergence it asserts is not a statement about a zero sequence: on `Bool` at the Dirac law on
the empty configuration, with `p = 1` and the pair weight supported on the single pair
`s(false, true)`, the total weighted pivotal flux is `1`. -/

/-- **A witness for the finiteness hypothesis of the real cap limit, with value `1`.** -/
example :
    (∑' e : Sym2 Bool, (if e = s(false, true) then (1 : ℝ≥0∞) else 0) *
      ∫⁻ ω : Config Bool, (((cluster (insert e ω) false).encard : ℝ≥0∞) ^ 1 -
        ((cluster (ω \ {e}) false).encard : ℝ≥0∞) ^ 1) ∂Measure.dirac (∅ : Config Bool)) = 1 := by
  classical
  have hcl : cluster (insert (s(false, true)) (∅ : Config Bool)) false = {false, true} := by
    apply Set.eq_of_subset_of_subset
    · intro x _
      cases x <;> simp
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with h | h
      · rw [h]; exact mem_cluster_self _ _
      · rw [Set.mem_singleton_iff.1 h]
        exact SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨by simp, by simp⟩)
  have hbase : cluster ((∅ : Config Bool) \ {s(false, true)}) false = {false} := by
    rw [Set.empty_sdiff, cluster_empty]
  have hp2 : (({false, true} : Set Bool).encard : ℝ≥0∞) = 2 := by
    rw [Set.encard_pair (by simp)]
    simp
  have hs1 : (({false} : Set Bool).encard : ℝ≥0∞) = 1 := by
    simp
  have hflux : ∫⁻ ω : Config Bool,
      (((cluster (insert (s(false, true)) ω) false).encard : ℝ≥0∞) ^ 1 -
        ((cluster (ω \ {s(false, true)}) false).encard : ℝ≥0∞) ^ 1)
        ∂Measure.dirac (∅ : Config Bool) = 1 := by
    rw [lintegral_dirac, hcl, hbase, pow_one, pow_one, hp2, hs1,
      show (2 : ℝ≥0∞) = 1 + 1 by norm_num, ENNReal.add_sub_cancel_left (by simp)]
  rw [tsum_eq_single (s(false, true)) (fun b hb => by simp [hb]), hflux]
  simp

end PercLib.Percolation.Bond



/-! ## Real-valued cap limits and the uncapped Russo flux

The real observable `F_M` is bounded and eventually constant, fitting the infinite-volume
Russo theorem. The uncapped result keeps the finite-cluster, inserted-moment, dominator,
interval-integrability and measurability hypotheses explicit: the cap supplies none of them.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Analysis

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `min c M → c` as `M → ∞`, for the real order. -/
theorem tendsto_min_atTop (c : ℝ) : Tendsto (fun M : ℝ => min c M) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop c] with M hM
  exact (min_eq_left hM).symm

/-- **The capped integral converges to the uncapped one.** For a nonnegative integrable `f` the
capped integrals `∫ min (f a) M` increase to `∫ f`. The dominator is `f` itself, so nothing
beyond integrability of the uncapped function is needed. -/
theorem tendsto_integral_min_atTop {f : α → ℝ} (hfm : AEMeasurable f μ) (hnn : 0 ≤ f)
    (hf : Integrable f μ) :
    Tendsto (fun M : ℝ => ∫ a, min (f a) M ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence f ?_ ?_ hf ?_
  · filter_upwards with M
    exact ((hfm.min aemeasurable_const).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    filter_upwards [ae_of_all μ hnn] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min ha hM)]
    exact min_le_left _ _
  · exact ae_of_all μ fun a => tendsto_min_atTop (f a)

/-- **The capped pivotal increment converges to the uncapped one.** With `0 ≤ g ≤ f` and `f`
integrable, `∫ (min (f a) M - min (g a) M) → ∫ (f - g)`. This is the per-edge real cap limit for
a difference of cluster volumes, stated for abstract `f, g` so that no cluster finiteness is built
in; the dominator is `f` and no `2 m` bound appears. -/
theorem tendsto_integral_min_sub_min_atTop {f g : α → ℝ} (hfm : AEMeasurable f μ)
    (hgm : AEMeasurable g μ) (hg0 : 0 ≤ᵐ[μ] g) (hgf : g ≤ᵐ[μ] f) (hf : Integrable f μ) :
    Tendsto (fun M : ℝ => ∫ a, (min (f a) M - min (g a) M) ∂μ) atTop
      (𝓝 (∫ a, f a ∂μ - ∫ a, g a ∂μ)) := by
  have hgi : Integrable g μ :=
    hf.mono' hgm.aestronglyMeasurable (by
      filter_upwards [hg0, hgf] with a h0 h1
      simp only [Pi.zero_apply] at h0
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  rw [← integral_sub hf hgi]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence f ?_ ?_ hf ?_
  · filter_upwards with M
    exact (((hfm.min aemeasurable_const).sub (hgm.min aemeasurable_const))
      |>.aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    filter_upwards [hg0, hgf] with a h0 h1
    simp only [Pi.zero_apply] at h0
    have h1' : 0 ≤ min (f a) M - min (g a) M := by
      have := min_le_min h1 (le_refl M)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg h1']
    have h2 : min (f a) M - min (g a) M ≤ f a - g a :=
      PercLib.Percolation.Bond.min_sub_min_le_sub h1
    linarith
  · filter_upwards with a
    exact (tendsto_min_atTop (f a)).sub (tendsto_min_atTop (g a))

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The capped moment observable -/

/-- **The cap is `⊤`-compatible.** On an infinite cluster the capped moment observable takes the
value `M` of the cap, and on a finite cluster it is `min M (|K|^p)`. -/
theorem capped_pow_top (pow : ℕ) (hp : 1 ≤ pow) {M : ℝ} (hM : 0 ≤ M) :
    (min (ENNReal.ofReal M) (((⊤ : ℕ∞) : ℝ≥0∞) ^ pow)).toReal = M := by
  have htop : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ := rfl
  have hp0 : pow ≠ 0 := by omega
  rw [htop, ENNReal.top_pow hp0, min_eq_left le_top, ENNReal.toReal_ofReal hM]

/-- **The capped moment is bounded by the cap.** -/
theorem abs_capped_pow_toReal_le (pow : ℕ) {M : ℝ} (hM : 0 ≤ M) (n : ℕ∞) :
    |(min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal| ≤ M := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  calc (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal
      ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left _ _)
    _ = M := ENNReal.toReal_ofReal hM

/-- **The capped moment is eventually constant.** For `1 ≤ p` and `M ≥ 0` there is `n₀` with
`F_M n = F_M ⊤` for every `n ≥ n₀`, which is the eventual-constancy hypothesis of the library's
Russo formula. -/
theorem capped_pow_eventually_const (pow : ℕ) (hp : 1 ≤ pow) {M : ℝ} (hM : 0 ≤ M) :
    ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n →
      (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal =
        (min (ENNReal.ofReal M) (((⊤ : ℕ∞) : ℝ≥0∞) ^ pow)).toReal := by
  refine ⟨⌊max M 1⌋₊ + 1, fun n hn => ?_⟩
  rw [capped_pow_top pow hp hM]
  rcases eq_or_ne n ⊤ with h | h
  · rw [h, capped_pow_top pow hp hM]
  · have hcoe : ((n.toNat : ℕ) : ℕ∞) = n := ENat.natCast_toNat h
    have hge : (⌊max M 1⌋₊ + 1 : ℕ) ≤ n.toNat := by
      have h2 : ((⌊max M 1⌋₊ + 1 : ℕ) : ℕ∞) ≤ ((n.toNat : ℕ) : ℕ∞) := by rw [hcoe]; exact hn
      exact_mod_cast h2
    have hm : max M 1 ≤ (n.toNat : ℝ) := by
      have h1 : (max M 1 : ℝ) < (⌊max M 1⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊max M 1⌋₊ : ℝ) + 1) ≤ (n.toNat : ℝ) := by
        have h3 : ((⌊max M 1⌋₊ + 1 : ℕ) : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast hge
        push_cast at h3
        linarith
      linarith
    have hm1 : (1 : ℝ) ≤ (n.toNat : ℝ) := le_trans (le_max_right M 1) hm
    have hpow : M ≤ (n.toNat : ℝ) ^ pow := by
      have h4 : (n.toNat : ℝ) ^ 1 ≤ (n.toNat : ℝ) ^ pow := pow_le_pow_right₀ hm1 hp
      have h5 : ((n.toNat : ℝ) ^ 1) ≤ (n.toNat : ℝ) ^ pow := h4
      have h6 : M ≤ (n.toNat : ℝ) ^ 1 := by simpa using le_trans (le_max_left M 1) hm
      exact le_trans h6 h5
    have hmain : ENNReal.ofReal M ≤ ((n : ℝ≥0∞) ^ pow) := by
      have hn' : ((n.toNat : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) := by
        rw [← ENat.toENNReal_coe, hcoe]
      rw [← hn', ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
      exact ENNReal.ofReal_le_ofReal hpow
    rw [min_eq_left hmain, ENNReal.toReal_ofReal hM]


/-! ### The cap in the `ℝ≥0∞`-form used by the cluster volumes -/

/-- On a finite `ℝ≥0∞` value the capped moment is the minimum of the moment and the cap. This is
where a.e. finiteness of the cluster enters: on `⊤` the left side is `M`, not `min M 0`. -/
theorem capped_toReal_eq_min (pow : ℕ) {M : ℝ} (hM : 0 ≤ M) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    (min (ENNReal.ofReal M) (x ^ pow)).toReal = min (x.toReal ^ pow) M := by
  rw [ENNReal.toReal_min ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hx), ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hM, min_comm]

/-- The `p`-th power of the cluster volume of `o` after closing `e` is integrable as soon as it is
integrable after opening `e`: the closed cluster is contained in the open one. -/
theorem integrable_encard_sdiff_pow (μ : Measure (Config V)) (e : Sym2 V) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Integrable (fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) μ := by
  refine hint.mono' ((ENNReal.measurable_toReal.comp
    (measurable_encard_cluster_sdiff_coe e o)).pow_const pow).aestronglyMeasurable ?_
  filter_upwards [hfin] with ω hω
  have hle := encard_cluster_sdiff_le_insert_coe ω e o
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top hω hle
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg pow)]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hω hle) pow

/-- **The capped moment integral converges to the moment.** For an a.e. finite cluster at `o` with
finite `p`-th moment, `∫ min M (|K_o|^p) → ∫ |K_o|^p`. Note that the moment `|K_o|^p` here is the
honest real moment, which is only honest because the cluster is a.e. finite. -/
theorem tendsto_integral_capped_encard (μ : Measure (Config V)) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Tendsto (fun M : ℝ =>
        ∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂μ)
      atTop (𝓝 (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂μ)) := by
  have hm : AEMeasurable (fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) μ :=
    ((ENNReal.measurable_toReal.comp
      (Measurable.of_discrete.comp
        (measurable_encard_cluster (x := o)))).pow_const pow).aemeasurable
  refine (PercLib.Analysis.tendsto_integral_min_atTop (μ := μ) (f := fun ω =>
    (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) hm
    (fun ω => pow_nonneg ENNReal.toReal_nonneg pow) hint).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
  exact (integral_congr_ae (by
    filter_upwards [hfin] with ω hω
    exact capped_toReal_eq_min pow hM hω)).symm

/-- **The per-edge real cap limit, in `min` form.** The capped pivotal increment of the `p`-th
cluster-volume moment converges to the uncapped one. Hypotheses: a.e. finiteness of the cluster of
`o` after opening `e`, and integrability of the `p`-th moment of that cluster. No dominator beyond
the uncapped moment itself is used. -/
theorem tendsto_integral_capped_pivotal (μ : Measure (Config V)) (e : Sym2 V) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Tendsto (fun M : ℝ => ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) := by
  have hfin' : ∀ᵐ ω ∂μ, ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    hfin.mono fun ω h => ne_top_of_le_ne_top h (encard_cluster_sdiff_le_insert_coe ω e o)
  have hgf : (fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
      ≤ᵐ[μ] (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) := by
    filter_upwards [hfin] with ω hω
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg
      (ENNReal.toReal_mono hω (encard_cluster_sdiff_le_insert_coe ω e o)) pow
  have hg0 : (0 : Config V → ℝ) ≤ᵐ[μ]
      (fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) :=
    ae_of_all μ fun ω => pow_nonneg ENNReal.toReal_nonneg pow
  have hfm : AEMeasurable (fun ω : Config V =>
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ :=
    ((ENNReal.measurable_toReal.comp
      (measurable_encard_cluster_insert_coe e o)).pow_const pow).aemeasurable
  have hgm : AEMeasurable (fun ω : Config V =>
      (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) μ :=
    ((ENNReal.measurable_toReal.comp
      (measurable_encard_cluster_sdiff_coe e o)).pow_const pow).aemeasurable
  have hmain := PercLib.Analysis.tendsto_integral_min_sub_min_atTop (μ := μ)
    (f := fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
    (g := fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
    hfm hgm hg0 hgf hint
  rw [← integral_sub hint (integrable_encard_sdiff_pow μ e o pow hfin hint)] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
  exact (integral_congr_ae (by
    filter_upwards [hfin, hfin'] with ω h1 h2
    rw [capped_toReal_eq_min pow hM h1, capped_toReal_eq_min pow hM h2, min_comm])).symm

/-! ### The capped Russo identity for the moment itself -/

/-- **The capped infinite-volume Russo identity for the `p`-th cluster-volume moment.**

Instantiating `integral_sub_eq_integral_flux` at the observable `F_M n = min M (n ^ p)`,
`F_M ⊤ = M` gives, for every cap `M ≥ 0`, the identity between the capped moment difference and
the time integral of the capped flux. The constant in the flux dominator is `(max B 0) (2 M + 3)`:
it grows with the cap, which is precisely why this identity alone does not pass to `M → ∞`. -/
theorem integral_sub_eq_integral_flux_capped_moment
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {u v : ℝ} (Cc : Sym2 V → Set ℝ)
    (hC : ∀ e, (Cc e).Countable)
    (hcont : ∀ e, ContinuousOn (fun r => (p r e : ℝ)) (Ioo u v))
    (hderiv : ∀ e, ∀ r ∈ Ioo u v, r ∉ Cc e → HasDerivAt (fun r => (p r e : ℝ)) (c r e) r)
    (o : V) (pow : ℕ) (hp : 1 ≤ pow) {M : ℝ} (hM : 0 ≤ M) {B : ℝ}
    (hB : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ B)
    {s t : ℝ} (hus : u < s) (hst : s ≤ t) (htv : t < v) :
    (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂law (p r) := by
  have h := PercLib.Models.LongRange.integral_sub_eq_integral_flux
    (F := fun n : ℕ∞ => (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal) (m := M)
    (abs_capped_pow_toReal_le pow hM) (capped_pow_eventually_const pow hp hM) o p c Cc hC hcont
    hderiv (M := max B 0 * (2 * M + 3)) ?_ hus hst htv
  · simpa only using h
  · intro r hr S
    refine (hB r hr S).trans ?_
    have h1 : B ≤ max B 0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ max B 0 := le_max_right _ _
    have h3 : (1 : ℝ) ≤ 2 * M + 3 := by linarith
    nlinarith

/-! ### The all-pairs cap limit -/

/-- **The all-pairs flux cap limit.** Under a.e. finiteness of every inserted cluster, integrability
of every single-edge `p`-th moment, and summability of the all-pairs dominator
`e ↦ |c e| E|K_o(ω ∪ {e})|^p`, the capped flux series converges to the uncapped one. The dominator
is cap-independent; this is the point at which the `2 m` touch bound is replaced by the moment
itself. -/
theorem tendsto_tsum_capped_flux (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V)
    (pow : ℕ) (r : ℝ)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (p r)), ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (p r)))
    (hsum : Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) :
    Tendsto (fun M : ℝ => ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r)))
      atTop (𝓝 (∑' e, c r e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂(law (p r)))) := by
  refine tendsto_tsum_of_dominated_convergence hsum (fun e => ?_) ?_
  · exact (tendsto_integral_capped_pivotal (law (p r)) e o pow (hfin e) (hint e)).const_mul (c r e)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM e
    have hfin' : ∀ᵐ ω ∂(law (p r)), ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
      (hfin e).mono fun ω h => ne_top_of_le_ne_top h (encard_cluster_sdiff_le_insert_coe ω e o)
    have hb : ∀ᵐ ω ∂(law (p r)), ‖(min (ENNReal.ofReal M)
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal‖ ≤
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
      filter_upwards [hfin e, hfin'] with ω h1 h2
      have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
          ((cluster (insert e ω) o).encard : ℝ≥0∞) := encard_cluster_sdiff_le_insert_coe ω e o
      have h2' : (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow ≤
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono h1 hle) pow
      rw [capped_toReal_eq_min pow hM h1, capped_toReal_eq_min pow hM h2, Real.norm_eq_abs,
        abs_of_nonneg]
      · have h3 : min ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) M -
            min ((((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) M ≤
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          PercLib.Percolation.Bond.min_sub_min_le_sub h2'
        have h4 : (0 : ℝ) ≤ (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          pow_nonneg ENNReal.toReal_nonneg pow
        linarith
      · have := min_le_min h2' (le_refl M)
        linarith
    have hle := norm_integral_le_of_norm_le (hint e) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

omit [Countable V] in
/-- **A sufficient condition for the all-pairs dominator.** The summability hypothesis `hsum` of
`abs_tsum_capped_flux_le` and `integral_sub_eq_integral_flux_of_cap` is implied by a
uniform-in-`e` bound `K` on the single-edge `p`-th moments together with summability of the
derivative weights `e ↦ |c r e|`. That summation is free on a finite vertex set but need not
converge on an infinite lattice. The moment and weight inputs are kept separate. -/
theorem summable_flux_dominator_of_uniform_moment (p : ℝ → Sym2 V → unitInterval)
    (c : ℝ → Sym2 V → ℝ) (o : V) (pow : ℕ) (r : ℝ) {K : ℝ}
    (hbound : ∀ e, ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
      ∂(law (p r)) ≤ K)
    (hw : Summable fun e => |c r e|) :
    Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
  refine Summable.of_nonneg_of_le (fun e => mul_nonneg (abs_nonneg _) (integral_nonneg fun ω =>
    pow_nonneg ENNReal.toReal_nonneg pow)) (fun e => ?_) (hw.mul_right K)
  exact mul_le_mul_of_nonneg_left (hbound e) (abs_nonneg _)

omit [Countable V] in
/-- **The cap-independent dominator of the whole capped flux series.**

For every cap `M ≥ 0` the capped all-pairs flux is dominated, uniformly in `M`, by the all-pairs
series of the *uncapped* single-edge `p`-th moments with the edge forced open:
`‖∑_e c_e ∫ (min M f_e - min M g_e)‖ ≤ ∑_e |c_e| ∫ f_e`. This is the honest replacement for the
`2 m` touch bound: the `2 m` bound of `abs_flux_le` is cap-dependent (its `m` is the cap), while
this one is not. The price is exactly the summability hypothesis `hsum`: the uncapped all-pairs
series must converge, which is not implied by finiteness of the single-edge moments. -/
theorem abs_tsum_capped_flux_le (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V)
    (pow : ℕ) (r : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (p r)), ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (p r)))
    (hsum : Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) :
    ‖∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))‖ ≤ ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
  have hfin' : ∀ e, ∀ᵐ ω ∂(law (p r)), ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ := fun e =>
    (hfin e).mono fun ω h => ne_top_of_le_ne_top h (encard_cluster_sdiff_le_insert_coe ω e o)
  have hterm : ∀ e, ‖c r e * ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
      ∂(law (p r))‖ ≤ |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
    intro e
    have hb : ∀ᵐ ω ∂(law (p r)), ‖(min (ENNReal.ofReal M)
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal‖ ≤
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
      filter_upwards [hfin e, hfin' e] with ω h1 h2
      have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
          ((cluster (insert e ω) o).encard : ℝ≥0∞) := encard_cluster_sdiff_le_insert_coe ω e o
      have h2' : (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow ≤
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono h1 hle) pow
      rw [capped_toReal_eq_min pow hM h1, capped_toReal_eq_min pow hM h2, Real.norm_eq_abs,
        abs_of_nonneg]
      · have h3 : min ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) M -
            min ((((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) M ≤
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          PercLib.Percolation.Bond.min_sub_min_le_sub h2'
        have h4 : (0 : ℝ) ≤ (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          pow_nonneg ENNReal.toReal_nonneg pow
        linarith
      · have := min_le_min h2' (le_refl M)
        linarith
    have hle := norm_integral_le_of_norm_le (hint e) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have hsumm' : Summable fun e => c r e * ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
      ∂(law (p r)) := hsum.of_norm_bounded fun i => by
        simpa only [norm_norm] using hterm i
  calc ‖∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))‖
      ≤ ∑' e, ‖c r e * ∫ ω,
          ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
            (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
          ∂(law (p r))‖ := norm_tsum_le_tsum_norm (hsum.of_norm_bounded fun i => by
            simpa only [norm_norm] using hterm i)
    _ ≤ ∑' e, |c r e| *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) :=
      Summable.tsum_le_tsum (fun i => hterm i) (hsum.of_norm_bounded fun i => by
        simpa only [norm_norm] using hterm i) hsum

/-! ### The assembled transfer -/

/-- **The uncapped integrated Russo identity for the `p`-th moment.** From the capped identities for
every cap (proved separately in `integral_sub_eq_integral_flux_capped_moment`) and dominated
convergence of the capped flux series (dominator: the all-pairs series of single-edge `p`-th
moments), the identity passes to the uncapped moment.

What is *not* proved here, and is exposed as hypotheses: a.e. finiteness of every inserted cluster
at `o` and of the cluster at `o` under the two endpoint profiles; integrability of every single-edge
`p`-th moment with the edge forced open, and of the endpoint moments; summability of the all-pairs
dominator; interval-integrability of the dominator; and measurability in the scale `r` of the capped
flux. None of these follows from finite clusters or a finite root moment alone — in particular
`hsum`, `hD` and `hmeas` are extra inputs. -/
theorem integral_sub_eq_integral_flux_of_cap
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {u v : ℝ} (Cc : Sym2 V → Set ℝ)
    (hC : ∀ e, (Cc e).Countable)
    (hcont : ∀ e, ContinuousOn (fun r => (p r e : ℝ)) (Ioo u v))
    (hderiv : ∀ e, ∀ r ∈ Ioo u v, r ∉ Cc e → HasDerivAt (fun r => (p r e : ℝ)) (c r e) r)
    (o : V) (pow : ℕ) (hp : 1 ≤ pow) {B : ℝ}
    (hB : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ B)
    {s t : ℝ} (hus : u < s) (hst : s ≤ t) (htv : t < v)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (p r)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ r ∈ Ioo u v, ∀ e, Integrable (fun ω =>
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) (law (p r)))
    (hsum : ∀ r ∈ Ioo u v, Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)))
    (hD : IntervalIntegrable (fun r => ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)))
      volume s t)
    (hmeas : ∀ M : ℝ, AEStronglyMeasurable (fun r => ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))) (volume.restrict (uIoc s t)))
    (hfinT : ∀ᵐ ω ∂(law (p t)), ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤)
    (hfinS : ∀ᵐ ω ∂(law (p s)), ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤)
    (hintT : Integrable (fun ω => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) (law (p t)))
    (hintS : Integrable (fun ω => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) (law (p s))) :
    (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p t)) -
      (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂(law (p r)) := by
  classical
  -- the LHS at both endpoints
  have hL : Tendsto (fun M : ℝ =>
      ∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p t)) atTop
      (𝓝 (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p t))) :=
    tendsto_integral_capped_encard (law (p t)) o pow hfinT hintT
  have hLs : Tendsto (fun M : ℝ =>
      ∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s)) atTop
      (𝓝 (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p s))) :=
    tendsto_integral_capped_encard (law (p s)) o pow hfinS hintS
  -- the interval-integral side
  have hDnn : ∀ r ∈ Ioo u v, 0 ≤ ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
    intro r hr
    exact tsum_nonneg fun e => mul_nonneg (abs_nonneg _) (integral_nonneg fun ω =>
      pow_nonneg ENNReal.toReal_nonneg pow)
  have hbound : ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Ioo u v, ‖∑' e, c r e * ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
      ∂(law (p r))‖ ≤ ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) :=
    fun M hM r hr => abs_tsum_capped_flux_le p c o pow r hM (hfin r hr) (hint r hr) (hsum r hr)
  -- the per-cap identities
  have hcap : ∀ M : ℝ, 0 ≤ M → (∫ ω, (min (ENNReal.ofReal M)
        (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂law (p r) := fun M hM =>
    integral_sub_eq_integral_flux_capped_moment p c Cc hC hcont hderiv o pow hp hM hB hus hst htv
  have hleft : Tendsto (fun M : ℝ => (∫ ω, (min (ENNReal.ofReal M)
        (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s))) atTop
      (𝓝 ((∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p t)) -
        (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p s)))) := hL.sub hLs
  have hright : Tendsto (fun M : ℝ => ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))) atTop
      (𝓝 (∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂(law (p r)))) := by
    have hsub : uIoc s t ⊆ Ioo u v := by
      rw [uIoc_of_le hst]
      exact fun r hr => ⟨lt_trans hus hr.1, lt_of_le_of_lt hr.2 htv⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun r => ∑' e, |c r e| *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) ?_ ?_ hD ?_
    · filter_upwards with M
      exact hmeas M
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
      filter_upwards with r hr
      exact hbound M hM r (hsub hr)
    · filter_upwards with r hr
      exact tendsto_tsum_capped_flux p c o pow r (hfin r (hsub hr))
        (hint r (hsub hr)) (hsum r (hsub hr))
  have hcongr : (fun M : ℝ => (∫ ω, (min (ENNReal.ofReal M)
        (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s))) =ᶠ[atTop] fun M : ℝ => ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂law (p r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    exact hcap M hM
  exact tendsto_nhds_unique (hleft.congr' hcongr) hright


/-! ### Non-vacuity -/

/-- The cap binds below the cap value and does not bind above it: both branches of
`min M (n ^ p)` occur, and `capped_toReal_eq_min` computes them. -/
example : (min (ENNReal.ofReal (9 : ℝ)) (((6 : ℕ∞) : ℝ≥0∞) ^ 2)).toReal = 9 ∧
    (min (ENNReal.ofReal (9 : ℝ)) (((2 : ℕ∞) : ℝ≥0∞) ^ 2)).toReal = 4 := by
  refine ⟨?_, ?_⟩
  · rw [capped_toReal_eq_min 2 (by norm_num) (by norm_num)]; norm_num
  · rw [capped_toReal_eq_min 2 (by norm_num) (by norm_num)]; norm_num

/-- **Non-vacuity of the moment cap limit.** On the one-point vertex type `Unit` every cluster is
the whole vertex set, so the cluster of `()` is a.e. finite and has first moment `1`; the hypotheses
of `tendsto_integral_capped_encard` therefore hold, and the limit is the nonzero value `1`. -/
example : Tendsto (fun M : ℝ => ∫ ω : Config Unit,
      (min (ENNReal.ofReal M) (((cluster ω ()).encard : ℝ≥0∞) ^ 1)).toReal
      ∂(Measure.dirac (∅ : Config Unit))) atTop (𝓝 1) := by
  have hcl : ∀ ω : Config Unit, cluster ω () = Set.univ := fun ω =>
    Set.eq_univ_of_forall fun x => by
      rw [Subsingleton.elim x ()]
      exact mem_cluster_self ω ()
  have h := tendsto_integral_capped_encard (Measure.dirac (∅ : Config Unit)) () 1
    (by
      filter_upwards with ω
      rw [hcl ω]
      simp)
    (MeasureTheory.integrable_dirac (by simp))
  have hlim : (∫ ω : Config Unit, (((cluster ω ()).encard : ℝ≥0∞).toReal) ^ 1
      ∂(Measure.dirac (∅ : Config Unit))) = 1 := by
    rw [integral_dirac, hcl]
    simp
  rw [hlim] at h
  exact h

end PercLib.Percolation.Bond

/-! ### The capped moment identity on the cut-off family

The per-cap identity of `integral_sub_eq_integral_flux_capped_moment` is stated for an abstract
profile family with an abstract touch dominator. On the cut-off family of Definition I.1.5 all the
abstract inputs except the finiteness of the first moment are discharged (`cutoff_dominator`,
`continuousOn_cutoff_prob`, `hasDerivAt_cutoff_prob`, `countable_cutoff_corners`), so the capped
identity below is unconditional apart from `0 < s ≤ t < R` and `χ_{μ_R}(o) < ∞`. -/

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}

/-- **The capped Russo identity on the cut-off family.** With
`c_r(e) = 1{N(e) < r} β (-K'(r)) e^{-β J_r(e)}` and `μ_r` the cut-off law at scale `r`, for every
cap `M ≥ 0` and `0 < s ≤ t < R`,

`(capped moment at t) - (capped moment at s)
  = ∫_s^t ∑'_e c_r(e) ∫ (min M |K_o(ω ∪ {e})|^p - min M |K_o(ω \ {e})|^p) dμ_r dr`.

This is the per-cap identity of the paper's derivative formula (I.4.1) in integrated form, with the
`p`-th moment capped; it is not the `M → ∞` limit, which needs the cap-independent dominator of
`abs_tsum_capped_flux_le`. -/
theorem integral_sub_eq_integral_flux_cutoff_capped_moment
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (o : Fin d → ℤ) (pow : ℕ) (hp : 1 ≤ pow)
    {M : ℝ} (hM : 0 ≤ M) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (htR : t < R) :
    (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂(law (intensityProfile (cutoffKernel N K t) β))) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂(law (intensityProfile (cutoffKernel N K s) β))) =
      ∫ r in s..t, ∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, ((min (ENNReal.ofReal M)
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  PercLib.Models.LongRange.integral_sub_eq_integral_flux_cutoff hKa hK' hK'c β
    (F := fun n : ℕ∞ => (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal) (m := M)
    (abs_capped_pow_toReal_le pow hM) (capped_pow_eventually_const pow hp hM) o hχ hs hst htR

end PercLib.Models.LongRange



/-! ## Measurability of capped cutoff fluxes

The capped flux is almost everywhere the derivative of the capped moment.
Identifying it with `deriv` supplies measurability on a finite time window outside
countable cutoff corners, with no separate regularity premise.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- The finite-window cutoff flux is a.e. strongly measurable because it is almost everywhere
the derivative of the capped moment. -/
theorem measurable_flux_cutoff_of_bounded
    {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {F : ℕ∞ → ℝ} {m : ℝ}
    (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤)
    (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htR : t < R) :
    AEStronglyMeasurable (fun r => ∑' e, ((radialKernel N
      (fun u => if u < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (volume.restrict (uIoc s t)) := by
  let ψ : ℝ → ℝ := fun r => ∫ ω, F (cluster ω o).encard
    ∂(law (intensityProfile (cutoffKernel N K r) β))
  let Φ : ℝ → ℝ := fun r => ∑' e, ((radialKernel N
    (fun u => if u < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
    ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
      ∂(law (intensityProfile (cutoffKernel N K r) β))
  have hnear : ∀ r ∈ Ioc s t, r ∉ ⋃ e : Sym2 (Fin d → ℤ),
      {u : ℝ | ∃ x y, e = s(x, y) ∧ u = N (Int.cast ∘ (x - y))} → Φ r = deriv ψ r := by
    intro r hr hbad
    have hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r := by
      intro z hz
      apply hbad
      refine Set.mem_iUnion.2 ⟨s(0, z), 0, z, rfl, ?_⟩
      simpa only [zero_sub, intCast_comp_neg, map_neg_eq_map] using hz.symm
    exact (hasDerivAt_integral_cutoff hKa hK' hK'c β hFm hF o hχ
      (hs.trans hr.1) (hr.2.trans_lt htR) hcorner).deriv.symm
  have hcorners : (⋃ e : Sym2 (Fin d → ℤ),
      {r : ℝ | ∃ x y, e = s(x, y) ∧ r = N (Int.cast ∘ (x - y))}).Countable :=
    Set.countable_iUnion fun _ => countable_cutoff_corners _
  have hnull : ∀ᵐ r : ℝ ∂volume, r ∉ ⋃ e : Sym2 (Fin d → ℤ),
      {u : ℝ | ∃ x y, e = s(x, y) ∧ u = N (Int.cast ∘ (x - y))} :=
    measure_eq_zero_iff_ae_notMem.1 (hcorners.measure_zero volume)
  rw [uIoc_of_le hst]
  refine (measurable_deriv ψ).aestronglyMeasurable.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hnull] with r hr hbad
  exact (hnear r hr hbad).symm

end PercLib.Models.LongRange

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

/-- A nonpositive real cap is zero in the `ENNReal.ofReal` cap construction. -/
theorem capped_pow_toReal_eq_zero_of_nonpos {M : ℝ} (hM : M ≤ 0) (n : ℕ∞) (pow : ℕ) :
    (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal = 0 := by
  simp [ENNReal.ofReal_of_nonpos hM]

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- Every real cap produces an a.e.-strongly measurable cutoff flux of the `pow`-th
moment. The cap need not be nonnegative: for a negative cap the flux is identically zero. -/
theorem measurable_capped_flux_cutoff
    {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0)
    (o : Fin d → ℤ) (pow : ℕ) (hp : 1 ≤ pow) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htR : t < R) (M : ℝ) :
    AEStronglyMeasurable (fun r => ∑' e, ((radialKernel N
      (fun u => if u < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, ((min (ENNReal.ofReal M)
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (volume.restrict (uIoc s t)) := by
  by_cases hM : 0 ≤ M
  · exact measurable_flux_cutoff_of_bounded hKa hK' hK'c β
      (abs_capped_pow_toReal_le pow hM) (capped_pow_eventually_const pow hp hM)
      o hχ hs hst htR
  · have hMn : M ≤ 0 := le_of_not_ge hM
    simp_rw [capped_pow_toReal_eq_zero_of_nonpos hMn]
    exact measurable_flux_cutoff_of_bounded hKa hK' hK'c β
      (F := fun _ : ℕ∞ => (0 : ℝ)) (m := 0) (fun _ => by simp) ⟨0, fun _ _ => rfl⟩
      o hχ hs hst htR

end PercLib.Models.LongRange

/-! ## Differentiation of capped moments and the uncapped cap passage

The bounded Russo formula applies at every natural cap. The differentiability transfer to
uncapped moments is conditional on a finite cluster/moment bundle and a genuinely
interval-integrable all-pairs dominator, with continuity of the uncapped flux supplied
explicitly too. Neither of those model inputs is discharged here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open PercLib.Percolation.Bond
open PercLib.Analysis

namespace PercLib.Models.LongRange

/-- Measurability of the `p`-th power of a cluster volume. -/
theorem measurable_encard_cluster_pow {V : Type*} [Countable V] (o : V) (p : ℕ) :
    Measurable fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p := by
  have h : (fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p)
      = fun ω : Config V => (((cluster ω o).encard ^ p : ℕ∞) : ℝ≥0∞) := by
    funext ω
    simp
  rw [h]
  exact Measurable.of_discrete.comp ((measurable_encard_cluster o).pow_const p)

/-- Capped `p`-th cluster moments increase to the uncapped one, in `ℝ≥0∞`. -/
theorem tendsto_lintegral_min_pow_encard {V : Type*} [Countable V]
    (μ : Measure (Config V)) (o : V) (p : ℕ) :
    Tendsto (fun n : ℕ => ∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)
      atTop (𝓝 (∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)) := by
  have hmeas : Measurable fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p :=
    measurable_encard_cluster_pow o p
  have hmono : Monotone fun n : ℕ => fun ω : Config V =>
      min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) :=
    fun m n hmn ω => min_le_min_right _ (by exact_mod_cast hmn)
  have hiSup : (⨆ n : ℕ, ∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)
      = ∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ := by
    rw [← lintegral_iSup (f := fun n : ℕ => fun ω : Config V =>
      min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p))
      (fun n => measurable_const.min hmeas) hmono]
    exact lintegral_congr fun ω => iSup_min_natCast _
  have hmono' : Monotone fun n : ℕ =>
      ∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ :=
    fun m n hmn => lintegral_mono fun ω => hmono hmn ω
  have h := tendsto_atTop_iSup hmono'
  rwa [hiSup] at h

/-- Real form: the capped `p`-th moments converge to the uncapped one whenever the latter is
finite. -/
theorem tendsto_integral_min_pow_encard {V : Type*} [Countable V]
    (μ : Measure (Config V)) [IsFiniteMeasure μ] (o : V) (p : ℕ)
    (hmom : (∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p)).toReal ∂μ)
      atTop (𝓝 (∫ ω, (((((cluster ω o).encard : ℝ≥0∞)) ^ p)).toReal ∂μ)) := by
  have hmeas : Measurable fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p :=
    measurable_encard_cluster_pow o p
  have hne : ∀ n : ℕ, (∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω => min_le_left _ _)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ univ)
  have hreal := (ENNReal.tendsto_toReal_iff hne hmom).2 (tendsto_lintegral_min_pow_encard μ o p)
  have h1 : (∫ ω, (((((cluster ω o).encard : ℝ≥0∞)) ^ p)).toReal ∂μ)
      = ((∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)).toReal :=
    integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hmom)
  rw [h1]
  refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hreal
  exact (integral_toReal ((measurable_const.min hmeas)).aemeasurable
    (Eventually.of_forall fun ω => lt_of_le_of_lt (min_le_left (n:ℝ≥0∞) _) (by simp))).symm

/-- **Per-edge domination of the capped pivotal flux.** The capped pivotal `p`-flux is bounded
in absolute value by the uncapped pivotal `ℝ≥0∞` flux, uniformly in the cap. -/
theorem abs_integral_pivotal_truncation_le {V : Type*} [Countable V]
    (μ : Measure (Config V)) [IsFiniteMeasure μ] (e : Sym2 V) (o : V) (p n : ℕ)
    (hflux : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    |∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ|
      ≤ (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ).toReal := by
  have hIntCap : ∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ
      = (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal :=
    integral_toReal (measurable_pivotal_truncation e o p n).aemeasurable
      (Eventually.of_forall fun ω => lt_of_le_of_lt (pivotal_truncation_le_cap _ _ n) (by simp))
  have hle : (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal
      ≤ (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ).toReal :=
    ENNReal.toReal_mono hflux (lintegral_pivotal_truncation_le μ e o p n)
  calc |∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ|
      ≤ ∫ ω, |(min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal| ∂μ :=
        abs_integral_le_integral_abs
    _ = ∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact abs_of_nonneg ENNReal.toReal_nonneg
    _ ≤ _ := by rw [hIntCap]; exact hle

/-- **Abstract series cap passage.** If the weighted family `g` has all finite weighted partial
sums bounded by `K`, and `f n → g` pointwise with `|f n| ≤ |g|` termwise, then the weighted
series of `f n` converges to the weighted series of `g`. -/
theorem tendsto_tsum_of_dominated_convergence_real {ι : Type*} [Countable ι]
    {f : ℕ → ι → ℝ} {g : ι → ℝ} {w : ι → ℝ} {K : ℝ}
    (hK : ∀ S : Finset ι, ∑ e ∈ S, |w e| * |g e| ≤ K)
    (hconv : ∀ e, Tendsto (fun n => f n e) atTop (𝓝 (g e)))
    (hle : ∀ n e, |f n e| ≤ |g e|) :
    Tendsto (fun n => ∑' e, w e * f n e) atTop (𝓝 (∑' e, w e * g e)) := by
  have hbound_nn : ∀ e, 0 ≤ |w e| * |g e| := fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsumm : Summable fun e => |w e| * |g e| := summable_of_sum_le hbound_nn hK
  have hdom : ∀ᶠ (n : ℕ) in atTop, ∀ e, ‖w e * f n e‖ ≤ |w e| * |g e| := by
    refine Eventually.of_forall fun n e => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hle n e) (abs_nonneg _)
  have hlim : ∀ e, Tendsto (fun n => w e * f n e) atTop (𝓝 (w e * g e)) :=
    fun e => (hconv e).const_mul (w e)
  exact tendsto_tsum_of_dominated_convergence hsumm hlim hdom

/-- **The cap passage of the infinite-volume Russo derivative for the `p`-th moment.**

Let `q r` be a family of bond laws on a countable vertex set, `c r e` the derivative in the
parameter `r` of the pair probability of `e`, `o` a root and `p : ℕ`. Assume:

* `hKd`: the weighted uncapped pivotal `p`-flux has all finite partial sums bounded by the
  fixed function `Kd` (the all-pairs dominator), and `Kd` is interval integrable;
* `hfin`: for every `r` in the parameter interval and every pair `e`, the cluster of `o` after
  forcing `e` open is almost surely finite;
* `hflux`: the uncapped pivotal `p`-flux of every pair is finite;
* `hmom`: the uncapped `p`-th cluster moment is finite;
* `hd`: every capped moment `r ↦ E[min (|K_o|^p) n]` is differentiable with derivative the
  capped pivotal series (this is the finite-window Russo formula for the bounded observable);
* `hmeas`, `hcont`: the capped flux functions are a.e. strongly measurable and the uncapped
  flux is continuous in the parameter.

Then the uncapped `p`-th cluster moment is differentiable with derivative the infinite
pivotal flux series. -/
theorem hasDerivAt_integral_pow_of_cap_flux {V : Type*} [Countable V]
    (q : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V) (p : ℕ)
    {u v r₀ : ℝ} (hur : u < r₀) (hrv : r₀ < v)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V), ∑ e ∈ S, |c r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))| ≤ Kd r)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (q r)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂(law (q r))) ≠ ⊤)
    (hmom : ∀ r ∈ Ioo u v, (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p) ∂(law (q r))) ≠ ⊤)
    (hd : ∀ n : ℕ, ∀ r ∈ Ioo u v, HasDerivAt (fun s =>
        ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q s)))
      (∑' e, c r e * (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂(law (q r))).toReal) r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, c r e * (∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂(law (q r))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, c r e * ∫ ω,
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r)))
      (∑' e, c r₀ e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r₀))) r₀ := by
  classical
  let Q : ℝ → Sym2 V → ℝ := fun r e => ∫ ω,
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))
  let P : ℝ → Sym2 V → ℝ≥0∞ := fun r e => ∫⁻ ω,
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂(law (q r))
  let Pn : ℕ → ℝ → Sym2 V → ℝ := fun n r e => (∫⁻ ω,
    (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
      min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂(law (q r))).toReal
  let Φn : ℕ → ℝ → ℝ := fun n r => ∑' e, c r e * Pn n r e
  let Φ : ℝ → ℝ := fun r => ∑' e, c r e * Q r e
  let ψn : ℕ → ℝ → ℝ := fun n r =>
    ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q r))
  let ψ : ℝ → ℝ := fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))
  have hPn_eq : ∀ n r e, Pn n r e = ∫ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
      min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q r)) := by
    intro n r e
    refine (integral_toReal ((measurable_pivotal_truncation e o p n).aemeasurable) ?_).symm
    filter_upwards with ω
    exact lt_of_le_of_lt (pivotal_truncation_le_cap _ _ n) (by simp)
  have hQ_eq : ∀ r ∈ Ioo u v, ∀ e, Q r e = (P r e).toReal := by
    intro r hr e
    refine (integral_toReal (measurable_pivotal e o p).aemeasurable ?_).trans rfl
    filter_upwards [hfin r hr e] with ω hω
    exact pivotal_truncation_lt_top_of_ne_top hω
  have hmomconv : ∀ r ∈ Ioo u v, Tendsto (fun n => ψn n r) atTop (𝓝 (ψ r)) := by
    intro r hr
    exact tendsto_integral_min_pow_encard (law (q r)) o p (hmom r hr)
  have hedge : ∀ r ∈ Ioo u v, ∀ e, Tendsto (fun n => Pn n r e) atTop (𝓝 (Q r e)) := by
    intro r hr e
    have h0 := tendsto_integral_pivotal_truncation (law (q r)) e o p (hfin r hr e) (hflux r hr e)
    exact h0.congr' (Eventually.of_forall fun n => (hPn_eq n r e).symm)
  have hle : ∀ r ∈ Ioo u v, ∀ n e, |Pn n r e| ≤ |Q r e| := by
    intro r hr n e
    have h := abs_integral_pivotal_truncation_le (law (q r)) e o p n (hflux r hr e)
    have h1 : Pn n r e = ∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q r)) :=
      hPn_eq n r e
    have h2 : Q r e = (P r e).toReal := hQ_eq r hr e
    rw [h1, h2, abs_of_nonneg ENNReal.toReal_nonneg]
    exact h
  have hΦconv : ∀ r ∈ Ioo u v, Tendsto (fun n => Φn n r) atTop (𝓝 (Φ r)) := by
    intro r hr
    exact tendsto_tsum_of_dominated_convergence_real (hKd r hr) (hedge r hr) (hle r hr)
  have hbound : ∀ n : ℕ, ∀ r ∈ Ioo u v, |Φn n r| ≤ Kd r := by
    intro n r hr
    have hnn : ∀ e, 0 ≤ |c r e| * |Q r e| := fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsumm : Summable fun e => |c r e| * |Q r e| := summable_of_sum_le hnn (hKd r hr)
    have hsumm' : Summable fun e => |c r e| * |Pn n r e| :=
      hsumm.of_norm_bounded (fun e => by
        simpa only [Real.norm_eq_abs, abs_mul, abs_abs] using
          mul_le_mul_of_nonneg_left (hle r hr n e) (abs_nonneg (c r e)))
    have htri : |Φn n r| ≤ ∑' e, |c r e| * |Pn n r e| := by
      calc |Φn n r| = ‖∑' e, c r e * Pn n r e‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∑' e, ‖c r e * Pn n r e‖ :=
            norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs, abs_mul] using hsumm')
        _ = ∑' e, |c r e| * |Pn n r e| :=
            tsum_congr fun e => by rw [Real.norm_eq_abs, abs_mul]
    refine htri.trans (Real.tsum_le_of_sum_le
      (fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (fun S => ?_))
    refine le_trans (Finset.sum_le_sum fun e _ => ?_) (hKd r hr S)
    exact mul_le_mul_of_nonneg_left (hle r hr n e) (abs_nonneg _)
  have hsubst : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, uIoc s t ⊆ Ioo u v := by
    intro s hs t ht x hx
    exact ⟨lt_trans (lt_min hs.1 ht.1) hx.1, lt_of_le_of_lt hx.2 (max_lt hs.2 ht.2)⟩
  have hsubst' : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, uIcc s t ⊆ Ioo u v := by
    intro s hs t ht x hx
    refine ⟨lt_of_lt_of_le (lt_min hs.1 ht.1) ?_, lt_of_le_of_lt ?_ (max_lt hs.2 ht.2)⟩
    · rw [Set.uIcc] at hx; exact hx.1
    · rw [Set.uIcc] at hx; exact hx.2
  have hcap : ∀ n : ℕ, ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, ∫ r in s..t, Φn n r = ψn n t - ψn n s := by
    intro n s hs t ht
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd n x (hsubst' s hs t ht hx)) ?_
    · exact IntervalIntegrable.mono_fun' (hKdint s hs t ht)
        ((hmeas n).mono_measure (Measure.restrict_mono_set volume (hsubst s hs t ht)))
        ((ae_restrict_mem measurableSet_uIoc).mono fun x hx =>
          (by simpa only [Real.norm_eq_abs] using hbound n x (hsubst s hs t ht hx)))
  have hlimint : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v,
      Tendsto (fun n => ∫ r in s..t, Φn n r) atTop (𝓝 (∫ r in s..t, Φ r)) := by
    intro s hs t ht
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := atTop) (a := s) (b := t) (f := Φ) (F := fun n => Φn n) Kd ?_ ?_ (hKdint s hs t ht) ?_
    · exact Eventually.of_forall fun n =>
        (hmeas n).mono_measure (Measure.restrict_mono_set volume (hsubst s hs t ht))
    · exact Eventually.of_forall fun n => by
        filter_upwards with x hx
        simpa only [Real.norm_eq_abs] using hbound n x (hsubst s hs t ht hx)
    · filter_upwards with x hx
      exact hΦconv x (hsubst s hs t ht hx)
  have hident : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, ∫ r in s..t, Φ r = ψ t - ψ s := by
    intro s hs t ht
    have h2 : Tendsto (fun n => ∫ r in s..t, Φn n r) atTop (𝓝 (ψ t - ψ s)) := by
      refine ((hmomconv t ht).sub (hmomconv s hs)).congr' (Eventually.of_forall fun n => ?_)
      exact (hcap n s hs t ht).symm
    exact tendsto_nhds_unique (hlimint s hs t ht) h2
  have hmem : Ioo u v ∈ 𝓝 r₀ := Ioo_mem_nhds hur hrv
  have hident' : ψ =ᶠ[𝓝 r₀] fun r => ψ r₀ + ∫ x in r₀..r, Φ x := by
    filter_upwards [hmem] with r hr
    rcases le_total r₀ r with h | h
    · have h1 := hident r₀ ⟨hur, hrv⟩ r hr
      rw [h1]; ring
    · have h1 := hident r hr r₀ ⟨hur, hrv⟩
      rw [intervalIntegral.integral_symm, h1]; ring
  have hInt : HasDerivAt (fun r => ψ r₀ + ∫ x in r₀..r, Φ x) (Φ r₀) r₀ :=
    (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hcont.stronglyMeasurableAtFilter isOpen_Ioo r₀ ⟨hur, hrv⟩)
      (hcont.continuousAt hmem)).const_add (ψ r₀)
  exact hInt.congr_of_eventuallyEq hident'

/-- **Bridge between the real-difference and the truncated-`ℝ≥0∞` form of the capped pivotal
flux.** The library's bounded-observable Russo formula `hasDerivAt_integral_cutoff` writes the
flux through a pair as the integral of the difference of the (real) observable, while the cap
passage here uses the `ℝ≥0∞` truncated subtraction. On a finite measure the two agree. -/
theorem integral_pivotal_min_sub_eq_lintegral {V : Type*} [Countable V]
    (μ : Measure (Config V)) [IsFiniteMeasure μ] (e : Sym2 V) (o : V) (p n : ℕ) :
    ∫ ω, ((min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ
      = (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal := by
  have hpt : ∀ ω : Config V,
      ((min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
      = (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal := by
    intro ω
    rw [ENNReal.toReal_sub_of_le
      (min_le_min_left (n : ℝ≥0∞)
        (ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)))
      (ne_top_of_le_ne_top (by simp) (min_le_left (n : ℝ≥0∞) _))]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_toReal
    (measurable_pivotal_truncation e o p n).aemeasurable]
  exact Eventually.of_forall fun ω => lt_of_le_of_lt (pivotal_truncation_le_cap _ _ n) (by simp)


/-- The capped `p`-th power observable `k ↦ min (n) |k|^p` is bounded by its cap. -/
theorem abs_capped_pow_encard_le (n p : ℕ) (k : ℕ∞) :
    |(min (n : ℝ≥0∞) (((k : ℝ≥0∞)) ^ p)).toReal| ≤ (n : ℝ) := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (by simp) (min_le_left (n : ℝ≥0∞) _)

/-- The capped `p`-th power observable `k ↦ min (n) |k|^p` is eventually constant at `⊤`. -/
theorem capped_pow_encard_eventually_const (p : ℕ) (hp : 1 ≤ p) (n : ℕ) :
    ∃ n₀ : ℕ, ∀ k : ℕ∞, (n₀ : ℕ∞) ≤ k →
      (min (n : ℝ≥0∞) (((k : ℝ≥0∞)) ^ p)).toReal
        = (min (n : ℝ≥0∞) ((((⊤ : ℕ∞) : ℝ≥0∞)) ^ p)).toReal := by
  refine ⟨n, fun k hk => ?_⟩
  have hnk : (n : ℝ≥0∞) ≤ ((k : ℝ≥0∞)) := by
    have h1 : ((n : ℕ∞) : ℝ≥0∞) ≤ ((k : ℕ∞) : ℝ≥0∞) := by exact_mod_cast hk
    simpa using h1
  have hkp : (n : ℝ≥0∞) ≤ ((k : ℝ≥0∞) ^ p) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h1 : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) :=
        (by exact_mod_cast hn : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞)).trans hnk
      exact hnk.trans (le_self_pow₀ h1 (by omega))
  have htop : (n : ℝ≥0∞) ≤ (((⊤ : ℕ∞) : ℝ≥0∞) ^ p) := by
    rw [show ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ from by simp, ENNReal.top_pow (by omega)]
    exact le_top
  rw [min_eq_left hkp, min_eq_left htop]

/-- **Russo derivative of the capped `p`-th cluster moment of the cut-off family.** For every
cap `n`, the capped moment `s ↦ E[min (|K_o|^p) n]` under the cut-off law at scale `s` is
differentiable at `r ∈ (0, R)`, away from the corner values `N (z)`, with derivative the
(capped) infinite pivotal flux series in the truncated-`ℝ≥0∞` form consumed by the cap
passage `hasDerivAt_integral_pow_of_cap_flux`. Discharged from the library's bounded
Russo formula `hasDerivAt_integral_cutoff` with `F = k ↦ min (n) |k|^p`. -/
theorem hasDerivAt_capped_moment_cutoff {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p n : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r) :
    HasDerivAt (fun s => ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal
        ∂(law (intensityProfile (cutoffKernel N K s) β)))
      (∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal) r := by
  have h := hasDerivAt_integral_cutoff hKa hK' hK'c β
    (F := fun k : ℕ∞ => (min (n : ℝ≥0∞) (((k : ℝ≥0∞)) ^ p)).toReal)
    (abs_capped_pow_encard_le n p) (capped_pow_encard_eventually_const p hp n)
    o hχ hr hrR hcorner
  refine h.congr_deriv ?_
  refine tsum_congr fun e => ?_
  rw [integral_pivotal_min_sub_eq_lintegral]


/-- **Russo derivative of the capped `p`-th moment, with the cut-off weight as a parameter.**
This is `hasDerivAt_capped_moment_cutoff` with the (large) explicit edge weight replaced by a
parameter `cw` together with its defining equation `hcw`; nothing about the model changes. -/
theorem hasDerivAt_capped_moment_cutoff_of_weight {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p n : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r) :
    HasDerivAt (fun s => ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal
        ∂(law (intensityProfile (cutoffKernel N K s) β)))
      (∑' e, cw r e *
        (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal) r :=
  (hasDerivAt_capped_moment_cutoff hKa hK' hK'c β p n hp o hχ hr hrR hcorner).congr_deriv
    (tsum_congr fun e => by rw [hcw])

/-- **The cap passage for the cut-off family, with the edge weight as a parameter.**

This is the conclusion of `hasDerivAt_integral_pow_of_cap_flux` for the cut-off law
`r ↦ law (intensityProfile (cutoffKernel N K r) β)`: the uncapped `p`-th cluster moment
`r ↦ E |K_o|^p` is differentiable at `r₀` with derivative the infinite pivotal flux series.

The cut-off edge weight `cw` and its defining equation `hcw` are explicit parameters so that no
large series expression has to be beta-reduced during elaboration. Assumptions kept as inputs:
the all-pairs dominator `hKd` with its interval integrability, the per-edge finiteness of the
inserted cluster and of the pivotal flux, the finite `p`-th moment, and the a.e. strong
measurability of the capped flux and the continuity of the uncapped flux in the parameter.
In particular `hcont` is an input: it is *not* discharged by `continuousOn_flux_cutoff`, which
only applies to bounded observables and hence not to the untruncated `p`-th moment. -/
theorem hasDerivAt_integral_cutoff_pow {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hmom : ∀ r ∈ Ioo u v, (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p)
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (∑' e, cw r₀ e *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r₀) β))) r₀ :=
  hasDerivAt_integral_pow_of_cap_flux (V := Fin d → ℤ)
    (q := fun r => intensityProfile (cutoffKernel N K r) β) (c := cw) (o := o) (p := p)
    (u := u) (v := v) (r₀ := r₀) (Kd := Kd) hur hrv hKdint hKd hfin hflux hmom
    (fun n r hr => hasDerivAt_capped_moment_cutoff_of_weight (N := N) (K := K) (K' := K')
      hKa hK' hK'c β p n hp o hχ cw hcw (hu.trans hr.1) (hr.2.trans_le hvR)
      (fun z hz => hcorner z (by
        simpa only [hz] using (show r ∈ Ioo u v from ⟨hr.1, hr.2⟩))))
    hmeas hcont

/-- **Non-vacuity of the cap passage.** On the one-vertex type `Unit` every cluster is the
whole vertex set, so with zero weights `c = 0`, zero dominator `Kd = 0` and an arbitrary bond
law family `q`, every hypothesis of `hasDerivAt_integral_pow_of_cap_flux` holds:

* the uncapped `p = 1` moment is the constant `1` (so finite);
* every pivotal increment vanishes identically, so the pivotal fluxes are `0`;
* hence the uncapped flux series and all capped flux series are the constant `0`, which is
  bounded by `Kd = 0`, a.e. strongly measurable and continuous;
* the capped moment `s ↦ E[min (|K_()|^1) n]` is the constant `min n 1`, whose derivative is
  `0`, i.e. the capped pivotal series.

The conclusion is therefore the genuine differentiability statement for the (constant) `p`-th
moment of the single-vertex model, with derivative `0` equal to the pivotal flux series. -/
theorem nonvacuous_cap_flux (q : ℝ → Sym2 Unit → unitInterval) :
    HasDerivAt (fun r => ∫ ω : Config Unit, (((cluster ω ()).encard : ℝ≥0∞) ^ 1).toReal
        ∂(law (q r)))
      (∑' e : Sym2 Unit, (0 : ℝ) * ∫ ω : Config Unit,
        ((((cluster (insert e ω) ())).encard : ℝ≥0∞) ^ 1 -
          ((((cluster (ω \ {e}) ())).encard : ℝ≥0∞)) ^ 1).toReal ∂(law (q 1))) 1 := by
  have hcl : ∀ (ω : Config Unit) (x : Unit), ((cluster ω x).encard : ℝ≥0∞) = 1 := by
    intro ω x
    have h : cluster ω x = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      simpa only [Subsingleton.elim y x] using mem_cluster_self ω x
    rw [h]
    simp
  have hzero : ∀ (r : ℝ) (e : Sym2 Unit),
      (∫⁻ ω : Config Unit, ((((cluster (insert e ω) ())).encard : ℝ≥0∞) ^ 1 -
        ((((cluster (ω \ {e}) ())).encard : ℝ≥0∞)) ^ 1) ∂(law (q r))) = 0 := by
    intro r e
    refine lintegral_eq_zero_iff ?_ |>.2 (Eventually.of_forall fun ω => ?_)
    · exact (measurable_pivotal e () 1)
    · simp only [hcl]
      simp
  refine hasDerivAt_integral_pow_of_cap_flux (V := Unit) (q := q) (c := fun _ _ => (0 : ℝ))
    (o := ()) (p := 1) (u := 0) (v := 2) (r₀ := 1) (Kd := fun _ => 0)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ => intervalIntegrable_const
  · intro r _ S
    simp
  · intro r _ e
    filter_upwards with ω
    simp only [hcl]
    exact (by simp : ((1 : ℝ≥0∞)) ≠ ⊤)
  · intro r _ e
    rw [hzero r e]
    simp
  · intro r _
    have hone : ∀ ω : Config Unit, ((cluster ω ()).encard : ℝ≥0∞) ^ 1 = 1 := by
      intro ω
      rw [hcl ω ()]
      simp
    simp only [hone]
    simp
  · intro n r _
    have hconst : (fun s => ∫ ω : Config Unit,
        (min (n : ℝ≥0∞) ((((cluster ω ()).encard : ℝ≥0∞)) ^ 1)).toReal ∂(law (q s)))
        = fun _ => (min (n : ℝ≥0∞) 1).toReal := by
      funext s
      have hone : ∀ ω : Config Unit, ((cluster ω ()).encard : ℝ≥0∞) ^ 1 = 1 := by
        intro ω
        rw [hcl ω ()]
        simp
      simp only [hone]
      rw [integral_const]
      simp
    rw [hconst]
    simpa using hasDerivAt_const (x := r) (c := (min (n : ℝ≥0∞) 1).toReal)
  · intro n
    simpa only [zero_mul, tsum_zero] using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (volume.restrict (Ioo (0 : ℝ) 2)))
  · simpa only [zero_mul, tsum_zero] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo (0 : ℝ) 2))

end PercLib.Models.LongRange

/-! ## L1 convergence of weighted series

Pointwise dominated convergence of weighted series is supplemented by an absolute
L1 estimate for their differences, using the same summability input.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PercLib.Analysis

/-- Weighted L1 convergence gives convergence of a real weighted series. -/
theorem tendsto_tsum_of_l1_dominated {ι : Type*} [Countable ι]
    {f : ℕ → ι → ℝ} {g w : ι → ℝ}
    (hsum : Summable fun e => |w e| * |g e|)
    (hconv : ∀ e, Tendsto (fun n => f n e) atTop (𝓝 (g e)))
    (hle : ∀ n e, |f n e| ≤ |g e|) :
    Tendsto (fun n => ∑' e, w e * f n e) atTop (𝓝 (∑' e, w e * g e)) := by
  have hbound : ∀ n e, |w e * f n e - w e * g e| ≤ 2 * (|w e| * |g e|) := by
    intro n e
    calc |w e * f n e - w e * g e| ≤ |w e * f n e| + |w e * g e| := abs_sub _ _
      _ = |w e| * |f n e| + |w e| * |g e| := by rw [abs_mul, abs_mul]
      _ ≤ |w e| * |g e| + |w e| * |g e| := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left (hle n e) (abs_nonneg _)) _
      _ = 2 * (|w e| * |g e|) := by ring
  have hs2 : Summable fun e => 2 * (|w e| * |g e|) := hsum.mul_left 2
  have hconv0 : ∀ e, Tendsto (fun n => |w e * f n e - w e * g e|) atTop (𝓝 0) := by
    intro e
    have h := ((hconv e).const_mul (w e)).sub_const (w e * g e)
    simpa using h.abs
  have hnorm : ∀ n, Summable fun e => |w e * f n e - w e * g e| := by
    intro n
    exact Summable.of_nonneg_of_le (fun e => abs_nonneg _) (hbound n) hs2
  have hl1 : Tendsto (fun n => ∑' e, |w e * f n e - w e * g e|) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hs2 hconv0
      (Eventually.of_forall fun n e => by
        simpa only [Real.norm_eq_abs, abs_abs] using hbound n e)
  have hf : ∀ n, Summable fun e => w e * f n e := by
    intro n
    exact hsum.of_norm_bounded fun e => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hle n e) (abs_nonneg _)
  have hg : Summable fun e => w e * g e := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs, abs_mul, abs_abs] using hsum
  have hnorm_sub : ∀ n, ‖(∑' e, w e * f n e) - ∑' e, w e * g e‖ ≤
      ∑' e, |w e * f n e - w e * g e| := by
    intro n
    rw [← (hf n).tsum_sub hg]
    calc ‖∑' e, (w e * f n e - w e * g e)‖
        ≤ ∑' e, ‖w e * f n e - w e * g e‖ := norm_tsum_le_tsum_norm
          (by simpa only [Real.norm_eq_abs] using hnorm n)
      _ = ∑' e, |w e * f n e - w e * g e| := by
        exact tsum_congr fun e => Real.norm_eq_abs _
  have hz : Tendsto (fun n => ‖(∑' e, w e * f n e) - ∑' e, w e * g e‖) atTop (𝓝 0) := by
    exact squeeze_zero (fun n => norm_nonneg _) hnorm_sub (by simpa using hl1)
  have hz' : Tendsto (fun n => (∑' e, w e * f n e) - ∑' e, w e * g e)
      atTop (𝓝 0) := by
    simpa only [Metric.tendsto_atTop, dist_eq_norm, sub_zero, norm_norm] using hz
  exact tendsto_sub_nhds_zero_iff.1 hz'

end PercLib.Analysis

/-! ## Uniform moment bounds after a single edge insertion

A per-vertex moment bound controls the moment after inserting an edge. The root
moment is necessary, as a compiled counterexample shows.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The two-term inequality in `ℝ≥0∞` -/

/-- **`(u + v)^p ≤ 2^(p - 1) (u^p + v^p)` in `ℝ≥0∞`.** The real inequality is
`add_pow_le`; this is its `ℝ≥0∞` form, valid also for `u = ⊤` or `v = ⊤`, where both sides
are `⊤` (and for `p = 0`, where both sides are `1` and `2`). -/
theorem ennreal_add_pow_le (u v : ℝ≥0∞) (p : ℕ) :
    (u + v) ^ p ≤ 2 ^ (p - 1) * (u ^ p + v ^ p) := by
  rcases eq_or_ne u ⊤ with hu | hu
  · subst hu
    rcases p with _ | k
    · simp
    · rw [top_add, Nat.add_sub_cancel, ENNReal.top_pow (Nat.succ_ne_zero k), top_add,
        ENNReal.mul_top (by simp : ((2 : ℝ≥0∞)) ^ k ≠ 0)]
  · rcases eq_or_ne v ⊤ with hv | hv
    · subst hv
      rcases p with _ | k
      · simp
      · rw [add_top, Nat.add_sub_cancel, ENNReal.top_pow (Nat.succ_ne_zero k), add_top,
          ENNReal.mul_top (by simp : ((2 : ℝ≥0∞)) ^ k ≠ 0)]
    · have huv : u + v ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hu, hv⟩
      have hup : u ^ p ≠ ⊤ := ENNReal.pow_ne_top hu
      have hvp : v ^ p ≠ ⊤ := ENNReal.pow_ne_top hv
      have htwo : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
      have htwo0 : (2 : ℝ≥0∞) ^ (p - 1) ≠ 0 := by
        rcases Nat.eq_zero_or_pos p with h | h
        · subst h; simp
        · exact pow_ne_zero _ (by simp)
      rw [← ENNReal.toReal_le_toReal (ENNReal.pow_ne_top huv)
        (ENNReal.mul_ne_top htwo (ENNReal.add_ne_top.2 ⟨hup, hvp⟩))]
      simp only [ENNReal.toReal_pow, ENNReal.toReal_add hu hv, ENNReal.toReal_mul,
        ENNReal.toReal_add hup hvp, ENNReal.toReal_ofNat]
      exact add_pow_le ENNReal.toReal_nonneg ENNReal.toReal_nonneg p

/-! ### The pointwise pivotal increment of the volume bound -/

/-- **Opening one pair joins at most three clusters, in volume form.**
`|K_x(ω ∪ {s(a, b)})| ≤ |K_x(ω)| + |K_a(ω)| + |K_b(ω)|` in `ℝ≥0∞`; no finiteness
hypothesis, an infinite cluster makes both sides `⊤`. -/
theorem encard_cluster_insert_le_add (ω : Config V) (a b x : V) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ≤
      ((cluster ω x).encard : ℝ≥0∞) + ((cluster ω a).encard : ℝ≥0∞) +
        ((cluster ω b).encard : ℝ≥0∞) := by
  have hsub := Set.encard_mono (cluster_insert_subset ω a b x)
  have hstep : (cluster ω x ∪ cluster ω a ∪ cluster ω b).encard ≤
      (cluster ω x).encard + (cluster ω a).encard + (cluster ω b).encard := by
    refine (Set.encard_union_le (s := cluster ω x ∪ cluster ω a) (t := cluster ω b)).trans ?_
    exact add_le_add (Set.encard_union_le (s := cluster ω x) (t := cluster ω a)) le_rfl
  calc ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞)
      ≤ (((cluster ω x ∪ cluster ω a ∪ cluster ω b).encard : ℕ∞) : ℝ≥0∞) := by
        exact_mod_cast hsub
    _ ≤ (((cluster ω x).encard + (cluster ω a).encard + (cluster ω b).encard : ℕ∞) :
          ℝ≥0∞) := by exact_mod_cast hstep
    _ = ((cluster ω x).encard : ℝ≥0∞) + ((cluster ω a).encard : ℝ≥0∞) +
          ((cluster ω b).encard : ℝ≥0∞) := by
        rw [ENat.toENNReal_add, ENat.toENNReal_add]

/-- **The four-case volume bound for the inserted cluster.** With `p` arbitrary,
`|K_x(ω ∪ {s(a, b)})|^p ≤ |K_x(ω)|^p + 2^(p - 1) (|K_a(ω)|^p + |K_b(ω)|^p)`.

The cases are the four possible membership patterns of `x` in the clusters of `a` and `b`:
neither (`x`'s cluster is unchanged, so the bound is `le_add_right`), both (all three clusters
coincide), and exactly one (the cluster becomes `K_a ∪ K_b`, which is a disjoint union, and
the two-term inequality applies). No finiteness hypothesis is used: an infinite cluster on
either side makes both sides `⊤`. -/
theorem encard_cluster_insert_pow_le (ω : Config V) (a b x : V) (p : ℕ) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p ≤
      ((cluster ω x).encard : ℝ≥0∞) ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p) := by
  classical
  by_cases ha : x ∈ cluster ω a
  · by_cases hb : x ∈ cluster ω b
    · rw [cluster_insert_eq_of_mem_of_mem ha hb]
      exact le_add_right le_rfl
    · have hxK : cluster ω x = cluster ω a :=
        (cluster_eq_of_mem_conn ((mem_cluster_iff ω a x).1 ha)).symm
      have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
        refine Set.disjoint_left.2 fun z hza hzb => hb ?_
        have hax : ω ∈ conn x a := by
          rw [conn_symm]
          exact (mem_cluster_iff ω a x).1 ha
        have haz : ω ∈ conn a z := (mem_cluster_iff ω a z).1 hza
        have h1 : ω ∈ conn x z := conn_trans hax haz
        have h2 : ω ∈ conn z b := by rwa [mem_cluster_iff, conn_symm] at hzb
        have hxb : ω ∈ conn x b := conn_trans h1 h2
        rw [mem_cluster_iff, conn_symm]
        exact hxb
      have hunion : cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b :=
        cluster_insert_of_mem ω a b x (Or.inl ha)
      rw [hunion, Set.encard_union_eq hdisj, ENat.toENNReal_add, hxK]
      exact le_add_left (ennreal_add_pow_le _ _ p)
  · by_cases hb : x ∈ cluster ω b
    · have hxK : cluster ω x = cluster ω b :=
        (cluster_eq_of_mem_conn ((mem_cluster_iff ω b x).1 hb)).symm
      have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
        refine Set.disjoint_left.2 fun z hza hzb => ha ?_
        have hbx : ω ∈ conn x b := by
          rw [conn_symm]
          exact (mem_cluster_iff ω b x).1 hb
        have hbz : ω ∈ conn b z := (mem_cluster_iff ω b z).1 hzb
        have h1 : ω ∈ conn x z := conn_trans hbx hbz
        have h2 : ω ∈ conn z a := by rwa [mem_cluster_iff, conn_symm] at hza
        have hxa : ω ∈ conn x a := conn_trans h1 h2
        rw [mem_cluster_iff, conn_symm]
        exact hxa
      have hunion : cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b :=
        cluster_insert_of_mem ω a b x (Or.inr hb)
      rw [hunion, Set.encard_union_eq hdisj, ENat.toENNReal_add, hxK]
      exact (ennreal_add_pow_le _ _ p).trans (le_add_left le_rfl)
    · rw [PercLib.Models.LongRange.cluster_insert_eq_of_forall_not_mem (ω := ω) (o := x)
        (e := s(a, b)) ?_]
      · exact le_add_right le_rfl
      · intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with hza | hzb
        · subst hza
          exact fun h => ha ((mem_cluster_comm ω x z).1 h)
        · subst hzb
          exact fun h => hb ((mem_cluster_comm ω x z).1 h)

/-! ### The real form, under a.e. finiteness of the three clusters -/

/-- **The volume bound in `ℝ`.** The `ℝ`-valued form of `encard_cluster_insert_pow_le`, with
the explicit finiteness hypotheses that `toReal` needs: the clusters of `x`, `a` and `b` in
`ω` must have finite `encard`. The insertion itself needs no hypothesis: the bound forces
`|K_x(ω ∪ {e})|` to be finite as well. -/
theorem encard_cluster_insert_pow_toReal_le (ω : Config V) (a b x : V) (p : ℕ)
    (hx : ((cluster ω x).encard : ℝ≥0∞) ≠ ⊤)
    (ha : ((cluster ω a).encard : ℝ≥0∞) ≠ ⊤)
    (hb : ((cluster ω b).encard : ℝ≥0∞) ≠ ⊤) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p ≤
      ((cluster ω x).encard : ℝ≥0∞).toReal ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
          ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  · have hmain := encard_cluster_insert_pow_le ω a b x p
    have hxp : ((cluster ω x).encard : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.pow_ne_top hx
    have hap : ((cluster ω a).encard : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.pow_ne_top ha
    have hbp : ((cluster ω b).encard : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.pow_ne_top hb
    have hsum : ((cluster ω a).encard : ℝ≥0∞) ^ p + ((cluster ω b).encard : ℝ≥0∞) ^ p
        ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hap, hbp⟩
    have htwo : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
    have hRHS : ((cluster ω x).encard : ℝ≥0∞) ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hxp, ENNReal.mul_ne_top htwo hsum⟩
    have hL : ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p ≠ ⊤ :=
      ne_top_of_le_ne_top hRHS hmain
    have hX : ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ≠ ⊤ := by
      intro h
      exact hL (by rw [h, ENNReal.top_pow (by omega)])
    calc ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p
        = (((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p).toReal :=
          (ENNReal.toReal_pow _ _).symm
      _ ≤ _ := ENNReal.toReal_mono hRHS hmain
      _ = ((cluster ω x).encard : ℝ≥0∞).toReal ^ p +
          2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
            ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) := by
        rw [ENNReal.toReal_add hxp (ENNReal.mul_ne_top htwo hsum), ENNReal.toReal_mul,
          ENNReal.toReal_add hap hbp]
        simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-! ### The inserted side of the truncation hypotheses -/

/-- **A.e. finiteness of the inserted cluster.** If every per-vertex cluster volume is a.e.
finite, then so is the cluster volume of `o` after opening any single pair, by the three-cluster
bound `encard_cluster_insert_le_add`. This is the hypothesis `hfin` of
`tendsto_tsum_capped_flux` for the inserted side. -/
theorem ae_ne_top_encard_cluster_insert (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (hfin : ∀ y, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ := by
  induction e using Sym2.ind with
  | _ a b =>
    filter_upwards [(hfin o), (hfin a), (hfin b)] with ω ho ha hb
    refine ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨ho, ENNReal.add_ne_top.2 ⟨ha, hb⟩⟩) ?_
    simpa only [add_assoc] using encard_cluster_insert_le_add ω a b o

/-- **Integrability of the inserted `p`-th moment.** Dominated by the three per-vertex moments
through `encard_cluster_insert_pow_toReal_le`. This is the hypothesis `hint` of
`tendsto_tsum_capped_flux` for the inserted side, obtained from the `ω`-side data alone. -/
theorem integrable_encard_cluster_insert_pow [Countable V] (μ : Measure (Config V))
    (e : Sym2 V) (o : V) (p : ℕ)
    (hfin : ∀ y, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ y, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p) μ) :
    Integrable (fun ω => ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p) μ := by
  induction e using Sym2.ind with
  | _ a b =>
    refine Integrable.mono' ((hint o).add (((hint a).add (hint b)).const_mul ((2 : ℝ) ^ (p - 1))))
      ?_ ?_
    · exact ((ENNReal.measurable_toReal.comp
        (measurable_encard_cluster_insert_coe (s(a, b)) o)).pow_const p).aestronglyMeasurable
    · filter_upwards [(hfin o), (hfin a), (hfin b)] with ω ho ha hb
      rw [Real.norm_of_nonneg (pow_nonneg ENNReal.toReal_nonneg p)]
      exact encard_cluster_insert_pow_toReal_le ω a b o p ho ha hb

/-! ### The expectation bound -/

/-- **The inserted pivotal moment against the three per-vertex moments.**

For any measure `μ` on bond configurations, root `o`, pair `s(a, b)` and exponent `p`:
`E|K_o(ω ∪ {s(a, b)})|^p ≤ E|K_o|^p + 2^(p - 1) (E|K_a|^p + E|K_b|^p)`.

The hypotheses are exactly what the real form needs: a.e. finiteness and integrability of the
three per-vertex moments. No hypothesis on the inserted cluster itself is needed: its moment is
integrable as a consequence, and that is `integrable_encard_cluster_insert_pow`. -/
theorem integral_encard_cluster_insert_pow_le [Countable V] (μ : Measure (Config V))
    (x a b : V) (p : ℕ)
    (hfx : ∀ᵐ ω ∂μ, ((cluster ω x).encard : ℝ≥0∞) ≠ ⊤)
    (hfa : ∀ᵐ ω ∂μ, ((cluster ω a).encard : ℝ≥0∞) ≠ ⊤)
    (hfb : ∀ᵐ ω ∂μ, ((cluster ω b).encard : ℝ≥0∞) ≠ ⊤)
    (hix : Integrable (fun ω => ((cluster ω x).encard : ℝ≥0∞).toReal ^ p) μ)
    (hia : Integrable (fun ω => ((cluster ω a).encard : ℝ≥0∞).toReal ^ p) μ)
    (hib : Integrable (fun ω => ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) μ) :
    ∫ ω, ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p ∂μ ≤
      ∫ ω, ((cluster ω x).encard : ℝ≥0∞).toReal ^ p ∂μ +
        2 ^ (p - 1) * (∫ ω, ((cluster ω a).encard : ℝ≥0∞).toReal ^ p ∂μ +
          ∫ ω, ((cluster ω b).encard : ℝ≥0∞).toReal ^ p ∂μ) := by
  have hbound : ∀ᵐ ω ∂μ, ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p ≤
      ((cluster ω x).encard : ℝ≥0∞).toReal ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
          ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) := by
    filter_upwards [hfx, hfa, hfb] with ω ho ha hb
    exact encard_cluster_insert_pow_toReal_le ω a b x p ho ha hb
  have hInt : Integrable (fun ω => ((cluster ω x).encard : ℝ≥0∞).toReal ^ p +
      2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
        ((cluster ω b).encard : ℝ≥0∞).toReal ^ p)) μ :=
    hix.add ((hia.add hib).const_mul ((2 : ℝ) ^ (p - 1)))
  have hIntNew : Integrable (fun ω =>
      ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p) μ := by
    refine Integrable.mono' hInt ?_ ?_
    · exact ((ENNReal.measurable_toReal.comp
        (measurable_encard_cluster_insert_coe (s(a, b)) x)).pow_const p).aestronglyMeasurable
    · filter_upwards [hbound] with ω h
      rwa [Real.norm_of_nonneg (pow_nonneg ENNReal.toReal_nonneg p)]
  calc ∫ ω, ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p ∂μ
      ≤ ∫ ω, (((cluster ω x).encard : ℝ≥0∞).toReal ^ p +
          2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
            ((cluster ω b).encard : ℝ≥0∞).toReal ^ p)) ∂μ :=
        integral_mono_ae hIntNew hInt hbound
    _ = ∫ ω, ((cluster ω x).encard : ℝ≥0∞).toReal ^ p ∂μ +
          2 ^ (p - 1) * (∫ ω, ((cluster ω a).encard : ℝ≥0∞).toReal ^ p ∂μ +
            ∫ ω, ((cluster ω b).encard : ℝ≥0∞).toReal ^ p ∂μ) := by
        have e1 : ∫ ω, (((cluster ω x).encard : ℝ≥0∞).toReal ^ p +
            2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
              ((cluster ω b).encard : ℝ≥0∞).toReal ^ p)) ∂μ =
            ∫ ω, (((cluster ω x).encard : ℝ≥0∞).toReal ^ p) ∂μ +
              ∫ ω, (2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
                ((cluster ω b).encard : ℝ≥0∞).toReal ^ p)) ∂μ :=
          integral_add hix ((hia.add hib).const_mul ((2 : ℝ) ^ (p - 1)))
        have e2 : ∫ ω, (2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
              ((cluster ω b).encard : ℝ≥0∞).toReal ^ p)) ∂μ =
            2 ^ (p - 1) * ∫ ω, (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
              ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) ∂μ :=
          integral_const_mul _ _
        have e3 : ∫ ω, (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
              ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) ∂μ =
            ∫ ω, (((cluster ω a).encard : ℝ≥0∞).toReal ^ p) ∂μ +
              ∫ ω, (((cluster ω b).encard : ℝ≥0∞).toReal ^ p) ∂μ :=
          integral_add hia hib
        rw [e1, e2, e3]

/-- **The uniform inserted-moment bound in `ℝ`.** If every per-vertex `p`-th cluster moment is
integrable, a.e. finite and bounded by the same `m ≥ 0`, then the `p`-th moment of the cluster of
`x` after opening any pair is at most `(1 + 2^(p + 1)) m`.

The constant is what the pointwise four-case bound gives: the root term survives with weight `1`
and the two endpoint terms enter with weight `2^(p - 1) * 2 = 2^p` for `p ≥ 1`. It is uniform in
the pair, which is what `summable_flux_dominator_of_uniform_moment` needs. -/
theorem integral_encard_cluster_insert_pow_le_of_uniform [Countable V]
    (μ : Measure (Config V)) (p : ℕ) {m : ℝ}
    (hfin : ∀ y, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ y, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p) μ)
    (hm : 0 ≤ m)
    (hbd : ∀ y, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ∂μ ≤ m)
    (x a b : V) :
    ∫ ω, ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p ∂μ ≤
      (1 + 2 ^ (p + 1)) * m := by
  have hmain := integral_encard_cluster_insert_pow_le μ x a b p (hfin x) (hfin a) (hfin b)
    (hint x) (hint a) (hint b)
  have h2 : (2 : ℝ) ^ (p - 1) * 2 ≤ 2 ^ (p + 1) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      norm_num
    · rw [← pow_succ, Nat.sub_add_cancel hp]
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ p)
  calc ∫ ω, ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞).toReal ^ p ∂μ
      ≤ ∫ ω, ((cluster ω x).encard : ℝ≥0∞).toReal ^ p ∂μ +
          2 ^ (p - 1) * (∫ ω, ((cluster ω a).encard : ℝ≥0∞).toReal ^ p ∂μ +
            ∫ ω, ((cluster ω b).encard : ℝ≥0∞).toReal ^ p ∂μ) := hmain
    _ ≤ m + 2 ^ (p - 1) * (m + m) := by
        have hc : (0 : ℝ) ≤ 2 ^ (p - 1) := by positivity
        have hs : ∫ ω, ((cluster ω a).encard : ℝ≥0∞).toReal ^ p ∂μ +
            ∫ ω, ((cluster ω b).encard : ℝ≥0∞).toReal ^ p ∂μ ≤ m + m := by
          linarith [hbd a, hbd b]
        exact add_le_add (hbd x) (mul_le_mul_of_nonneg_left hs hc)
    _ = m + (2 ^ (p - 1) * 2) * m := by ring
    _ ≤ m + 2 ^ (p + 1) * m := by
        have hle := mul_le_mul_of_nonneg_right h2 hm
        linarith
    _ = (1 + 2 ^ (p + 1)) * m := by ring

/-- **The uniform inserted-moment bound, pair-indexed.** The `Sym2` form of
`integral_encard_cluster_insert_pow_le_of_uniform`, i.e. exactly the hypothesis `hbound` of
`summable_flux_dominator_of_uniform_moment` (and the integrability part of `hint` in
`tendsto_tsum_capped_flux`), with the explicit uniform per-vertex input. -/
theorem integral_encard_cluster_insert_pow_le_of_uniform_sym2 [Countable V]
    (μ : Measure (Config V)) (p : ℕ) {m : ℝ}
    (hfin : ∀ y, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ y, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p) μ)
    (hm : 0 ≤ m)
    (hbd : ∀ y, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ∂μ ≤ m)
    (e : Sym2 V) (o : V) :
    ∫ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p ∂μ ≤ (1 + 2 ^ (p + 1)) * m := by
  induction e using Sym2.ind with
  | _ a b => exact integral_encard_cluster_insert_pow_le_of_uniform μ p hfin hint hm hbd o a b

/-! ### The all-pairs dominator from a uniform per-vertex moment bound -/

/-- **The all-pairs flux dominator.** The summability hypothesis `hsum` of
`abs_tsum_capped_flux_le`, `tendsto_tsum_capped_flux` and `integral_sub_eq_integral_flux_of_cap`,
from two explicit inputs: a uniform bound `m` on the per-vertex `p`-th cluster moments (with
a.e. finiteness and integrability), and summability of the derivative weights
`e ↦ |c r e|`. The two inputs are independent: the weights do not control the moments, and the
moments do not control the weights. On a finite vertex set
`hw` follows from `Summable.of_finite`; on an infinite lattice the weights can fail to be
summable. The moment bound remains a separate sharpness input. -/
theorem summable_flux_dominator_of_uniform_vertex_moment [Countable V]
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V) (pow : ℕ) (r : ℝ) {m : ℝ}
    (hfin : ∀ y, ∀ᵐ ω ∂(law (p r)), ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ y, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow)
      (law (p r)))
    (hm : 0 ≤ m)
    (hbd : ∀ y, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow ∂(law (p r)) ≤ m)
    (hw : Summable fun e => |c r e|) :
    Summable fun e => |c r e| *
      ∫ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ pow ∂(law (p r)) :=
  summable_flux_dominator_of_uniform_moment p c o pow r
    (fun e => integral_encard_cluster_insert_pow_le_of_uniform_sym2 (law (p r)) pow hfin hint hm
      hbd e o) hw

/-! ### The inserted-side inputs of `tendsto_tsum_capped_flux`, uniformly in the pair -/

/-- **A.e. finiteness of every inserted cluster volume**, from the `ω`-side data alone. This is
the hypothesis `hfin : ∀ e, ∀ᵐ ω, |K_o(ω ∪ {e})| ≠ ⊤` of `tendsto_tsum_capped_flux`. -/
theorem ae_ne_top_encard_cluster_insert_forall (μ : Measure (Config V)) (o : V)
    (hfin : ∀ y, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤) :
    ∀ e : Sym2 V, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ :=
  fun e => ae_ne_top_encard_cluster_insert μ e o hfin

/-- **Integrability of every inserted `p`-th moment**, from the `ω`-side data alone. This is the
hypothesis `hint : ∀ e, Integrable (fun ω => |K_o(ω ∪ {e})|^p)` of `tendsto_tsum_capped_flux`. -/
theorem integrable_encard_cluster_insert_pow_forall [Countable V] (μ : Measure (Config V))
    (o : V) (p : ℕ)
    (hfin : ∀ y, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ y, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p) μ) :
    ∀ e : Sym2 V, Integrable (fun ω => ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p) μ :=
  fun e => integrable_encard_cluster_insert_pow μ e o p hfin hint

/-! ### Non-vacuity: the zero profile on `ℕ` -/

/-- **Non-vacuity of the uniform input: the zero profile on `ℕ`.**

Under `law 0` every pair is closed almost surely, so every cluster is a single vertex, every
per-vertex `p`-th moment equals `1`, and the uniform input of
`integral_encard_cluster_insert_pow_le_of_uniform` holds with `m = 1`. The conclusion of that
theorem then reads `E|K_o(ω ∪ {s(a, b)})|^p ≤ 1 + 2^(p + 1)`, which is finite and uniform in the
pair: the hypothesis bundle is satisfiable by an honest bond profile, not only by hypothesis.
(The true value in this instance is `1` when `o ∉ {a, b}` and `2^p` otherwise, so the constant
is not sharp but is of the right order.) -/
theorem integral_encard_cluster_insert_pow_le_zero_profile (pow : ℕ) (o a b : ℕ) :
    ∫ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞).toReal ^ pow
      ∂(law (fun _ : Sym2 ℕ => (0 : unitInterval))) ≤ 1 + 2 ^ (pow + 1) := by
  have hae : ∀ᵐ ω ∂(law (fun _ : Sym2 ℕ => (0 : unitInterval))), ω = ∅ := by
    filter_upwards [ae_config_subset_positive (fun _ : Sym2 ℕ => (0 : unitInterval))] with ω hω
    exact Set.subset_empty_iff.mp fun e he => (lt_irrefl (0 : ℝ) (hω he))
  have hfin : ∀ y : ℕ, ∀ᵐ ω ∂(law (fun _ : Sym2 ℕ => (0 : unitInterval))),
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤ := by
    intro y
    filter_upwards [hae] with ω h
    rw [h, cluster_empty, Set.encard_singleton]
    simp
  have hint : ∀ y : ℕ, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow)
      (law (fun _ : Sym2 ℕ => (0 : unitInterval))) := by
    intro y
    refine (integrable_const (1 : ℝ)).congr ?_
    filter_upwards [hae] with ω h
    rw [h, cluster_empty, Set.encard_singleton]
    simp
  have hbd : ∀ y : ℕ, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow
      ∂(law (fun _ : Sym2 ℕ => (0 : unitInterval))) ≤ 1 := by
    intro y
    have h1 : ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow
        ∂(law (fun _ : Sym2 ℕ => (0 : unitInterval))) =
        ∫ _ : Config ℕ, (1 : ℝ) ∂(law (fun _ : Sym2 ℕ => (0 : unitInterval))) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with ω h
      rw [h, cluster_empty, Set.encard_singleton]
      simp
    rw [h1]
    simp
  have := integral_encard_cluster_insert_pow_le_of_uniform
    (law (fun _ : Sym2 ℕ => (0 : unitInterval))) pow hfin hint zero_le_one hbd o a b
  simpa using this

/-! ### Loops -/

/-- **Loops are covered without hypotheses.** For a diagonal pair `s(a, a)` the inserted cluster
is the original one, so the pivotal moment does not move at all. This is the loop case of the
quantification over all `e : Sym2 V`, which includes the diagonal elements, and it needs no
finiteness hypothesis. -/
theorem encard_cluster_insert_diag_pow_eq (ω : Config V) (a x : V) (p : ℕ) :
    ((cluster (insert s(a, a) ω) x).encard : ℝ≥0∞) ^ p =
      ((cluster ω x).encard : ℝ≥0∞) ^ p := by
  rw [cluster_insert_diag]

/-! ### Finite vertex sets: every profile satisfies the uniform input -/

/-- **Non-vacuity on a finite vertex set: the uniform input is free.** If `V` is finite then every
cluster has at most `Fintype.card V` vertices, so for *every* bond profile and every root the
per-vertex `p`-th moment is bounded by `(Fintype.card V)^p`. Consequently the inserted pivotal
moment is bounded by `(1 + 2^(p + 1)) * (Fintype.card V)^p` with no input beyond finiteness of the
vertex set and normalisation of the measure. This is the finite-volume regime of the finite Russo
formulas, where the moment bound is not a sharpness statement. -/
theorem integral_encard_cluster_insert_pow_le_fintype [Fintype V] [Countable V]
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] (p : ℕ) (o a b : V) :
    ∫ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞).toReal ^ p ∂μ ≤
      (1 + 2 ^ (p + 1)) * (Fintype.card V : ℝ) ^ p := by
  have hcard : ∀ (y : V) (ω : Config V),
      ((cluster ω y).encard : ℝ≥0∞) ≤ ((Fintype.card V : ℕ) : ℝ≥0∞) := by
    intro y ω
    have h := Set.encard_mono (Set.subset_univ (cluster ω y))
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card] at h
    exact_mod_cast h
  have hle : ∀ (y : V) (ω : Config V),
      ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ≤ (Fintype.card V : ℝ) ^ p := by
    intro y ω
    have h4 : ((cluster ω y).encard : ℝ≥0∞).toReal ≤ (Fintype.card V : ℝ) := by
      have h := ENNReal.toReal_mono (by simp : ((Fintype.card V : ℕ) : ℝ≥0∞) ≠ ⊤) (hcard y ω)
      simpa using h
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg h4 p
  have hfin : ∀ y : V, ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤ := by
    intro y
    exact Filter.Eventually.of_forall fun ω => ne_top_of_le_ne_top (by simp) (hcard y ω)
  have hint : ∀ y : V, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p) μ := by
    intro y
    refine Integrable.mono' (integrable_const ((Fintype.card V : ℝ) ^ p)) ?_ ?_
    · exact ((ENNReal.measurable_toReal.comp
        (Measurable.of_discrete.comp (measurable_encard_cluster (x := y)))).pow_const p
        ).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_of_nonneg (pow_nonneg ENNReal.toReal_nonneg p)]
      exact hle y ω
  have hbd : ∀ y : V, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ∂μ ≤
      (Fintype.card V : ℝ) ^ p := by
    intro y
    calc ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ∂μ
        ≤ ∫ _ : Config V, (Fintype.card V : ℝ) ^ p ∂μ :=
          integral_mono_ae (hint y) (integrable_const _) (Filter.Eventually.of_forall (hle y))
      _ = (Fintype.card V : ℝ) ^ p := by simp
  exact integral_encard_cluster_insert_pow_le_of_uniform μ p hfin hint (by positivity) hbd o a b

/-- **The inserted-side inputs of `integral_sub_eq_integral_flux_of_cap`, in its shape.**

The uncapped transfer `integral_sub_eq_integral_flux_of_cap` asks, for every `r` in an interval
`(u, v)`, for (i) a.e. finiteness of every inserted cluster at the root, (ii) integrability of
every inserted `p`-th moment, and (iii) summability of `e ↦ |c r e|` times that moment. This
theorem produces all three from a uniform per-vertex moment bound and summable weights, so that
only `hB`, `hD`, `hmeas` (the flux-side inputs) remain explicit in the transfer. -/
theorem forall_inputs_of_uniform_vertex_moment [Countable V]
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V) (pow : ℕ) {u v m : ℝ}
    (hm : 0 ≤ m)
    (hfin : ∀ r ∈ Ioo u v, ∀ y, ∀ᵐ ω ∂(law (p r)), ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ r ∈ Ioo u v, ∀ y, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow)
      (law (p r)))
    (hbd : ∀ r ∈ Ioo u v, ∀ y, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow ∂(law (p r)) ≤ m)
    (hw : ∀ r ∈ Ioo u v, Summable fun e => |c r e|) :
    (∀ r ∈ Ioo u v, ∀ e : Sym2 V, ∀ᵐ ω ∂(law (p r)),
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) ∧
      (∀ r ∈ Ioo u v, ∀ e : Sym2 V, Integrable (fun ω =>
        ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ pow) (law (p r))) ∧
      (∀ r ∈ Ioo u v, Summable fun e => |c r e| *
        ∫ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ pow ∂(law (p r))) :=
  ⟨fun r hr => ae_ne_top_encard_cluster_insert_forall (law (p r)) o (hfin r hr),
   fun r hr => integrable_encard_cluster_insert_pow_forall (law (p r)) o pow (hfin r hr)
     (hint r hr),
   fun r hr => summable_flux_dominator_of_uniform_vertex_moment p c o pow r (hfin r hr)
     (hint r hr) hm (hbd r hr) (hw r hr)⟩

/-- The two-term bound with no root term is false: a path `0-1-2-3` and two isolated
vertices `10`, `11`. -/
theorem two_term_bound_false :
    ∃ (o a b : ℕ) (ω : Config ℕ) (p : ℕ),
      2 ^ p * (((cluster ω a).encard : ℝ≥0∞).toReal ^ p +
          ((cluster ω b).encard : ℝ≥0∞).toReal ^ p) <
        ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞).toReal ^ p := by
  have hstep : ∀ (ω : Config ℕ) (y a b : ℕ), cluster ω y = {y} → a ≠ y → b ≠ y →
      cluster (insert s(a, b) ω) y = {y} := by
    intro ω y a b h ha hb
    refine (PercLib.Models.LongRange.cluster_insert_eq_of_forall_not_mem (ω := ω) (o := y)
      (e := s(a, b)) ?_).trans h
    intro z hz
    rw [Sym2.mem_iff] at hz
    obtain h' | h' := hz
    · subst h'; rw [h]; simpa using ha
    · subst h'; rw [h]; simpa using hb
  have h1 : cluster (∅ : Config ℕ) 0 = {0} := cluster_empty 0
  have h2 : cluster (insert s(2, 3) (∅ : Config ℕ)) 0 = {0} :=
    hstep ∅ 0 2 3 (cluster_empty 0) (by norm_num) (by norm_num)
  have h3 : cluster (insert s(2, 3) (∅ : Config ℕ)) 1 = {1} :=
    hstep ∅ 1 2 3 (cluster_empty 1) (by norm_num) (by norm_num)
  have h4 : cluster (insert s(2, 3) (∅ : Config ℕ)) 2 = {2, 3} := by
    rw [cluster_insert_of_mem _ _ _ 2 (Or.inl (mem_cluster_self _ 2)), cluster_empty,
      cluster_empty, Set.singleton_union]
  have h5 : cluster (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ))) 0 = {0} :=
    hstep _ 0 1 2 h2 (by norm_num) (by norm_num)
  have h6 : cluster (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ))) 1 = {1, 2, 3} := by
    rw [cluster_insert_of_mem _ _ _ 1 (Or.inl (mem_cluster_self _ 1)), h3, h4,
      Set.singleton_union]
  have h7 : cluster (insert s(0, 1) (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ)))) 0 =
      {0, 1, 2, 3} := by
    rw [cluster_insert_of_mem _ _ _ 0 (Or.inl (mem_cluster_self _ 0)), h5, h6,
      Set.singleton_union]
  have h8 : cluster (insert s(0, 1) (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ)))) 10 =
      {10} := by
    refine hstep _ 10 0 1 (hstep _ 10 1 2 (hstep _ 10 2 3 (cluster_empty 10) ?_ ?_) ?_ ?_) ?_ ?_
      <;> norm_num
  have h9 : cluster (insert s(0, 1) (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ)))) 11 =
      {11} := by
    refine hstep _ 11 0 1 (hstep _ 11 1 2 (hstep _ 11 2 3 (cluster_empty 11) ?_ ?_) ?_ ?_) ?_ ?_
      <;> norm_num
  have h10 : cluster (insert s(10, 11)
      (insert s(0, 1) (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ))))) 0 = {0, 1, 2, 3} := by
    refine (PercLib.Models.LongRange.cluster_insert_eq_of_forall_not_mem
      (ω := insert s(0, 1) (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ)))) (o := 0)
      (e := s(10, 11)) ?_).trans h7
    intro z hz
    rw [Sym2.mem_iff] at hz
    obtain h' | h' := hz
    · subst h'; rw [h7]; simp
    · subst h'; rw [h7]; simp
  refine ⟨0, 10, 11, insert s(0, 1) (insert s(1, 2) (insert s(2, 3) (∅ : Config ℕ))), 3, ?_⟩
  rw [h8, h9, h10]
  have e4 : (({0, 1, 2, 3} : Set ℕ).encard : ℝ≥0∞) = 4 := by
    rw [show ({0, 1, 2, 3} : Set ℕ) = insert 0 (insert 1 (insert 2 ({3} : Set ℕ))) from rfl]
    rw [Set.encard_insert_of_notMem (by simp), Set.encard_insert_of_notMem (by simp),
      Set.encard_insert_of_notMem (by simp), Set.encard_singleton]
    norm_num
  rw [show (({10} : Set ℕ).encard : ℝ≥0∞).toReal = 1 from by simp,
    show (({11} : Set ℕ).encard : ℝ≥0∞).toReal = 1 from by simp,
    show (({0, 1, 2, 3} : Set ℕ).encard : ℝ≥0∞).toReal = 4 from by rw [e4]; norm_num]
  norm_num


/-- **The two-term integral bound without a root term is false.** Even for a probability measure,
here a Dirac mass, the `p`-th moment of the cluster of `o` after opening `s(a, b)` is not bounded
by `2^p` times the two endpoint moments: `two_term_bound_false` is a configuration where the
pointwise inequality fails, and a Dirac mass reproduces pointwise values as integrals. -/
theorem not_integral_two_term_bound :
    ¬ ∀ (μ : Measure (Config ℕ)) (o a b : ℕ) (p : ℕ),
        ∫ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞).toReal ^ p ∂μ ≤
          2 ^ p * (∫ ω, ((cluster ω a).encard : ℝ≥0∞).toReal ^ p ∂μ +
            ∫ ω, ((cluster ω b).encard : ℝ≥0∞).toReal ^ p ∂μ) := by
  intro h
  obtain ⟨o, a, b, ω, p, hlt⟩ := two_term_bound_false
  have h1 := h (Measure.dirac ω) o a b p
  simp only [integral_dirac] at h1
  linarith

end PercLib.Percolation.Bond

/-! ## Closed-coordinate Russo normalization

Condition a Bernoulli product law along an edge, distinguishing a bounded observable
from its limit. This supplies the unordered-pair flux normalization.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal unitInterval

namespace PercLib.Probability

open Classical in
/-- A bounded measurable integral is affine in one product-Bernoulli coordinate. -/
theorem integral_prodBernoulli_affine {ι : Type*} (q : ι → unitInterval) (e : ι)
    (G : Set ι → ℝ) (hG : Measurable G) {m : ℝ} (hGm : ∀ ω, |G ω| ≤ m) :
    (∫ ω, G ω ∂prodBernoulli q) = (q e : ℝ) * ∫ ω, G ω ∂prodBernoulli (update q e 1) +
      (1 - (q e : ℝ)) * ∫ ω, G ω ∂prodBernoulli (update q e 0) := by
  classical
  have hint : ∀ p : ι → unitInterval, Integrable G (prodBernoulli p) := by
    intro p
    exact Integrable.of_bound (C := m) hG.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hGm ω)
  have hmix := prodBernoulli_update_eq_smul_add_smul q e (q e)
  rw [Function.update_eq_self] at hmix
  rw [hmix]
  have hμ := (hint (update q e 1)).smul_measure
    (by simp : ((unitInterval.toNNReal (q e) : ℝ≥0∞)) ≠ ⊤)
  have hν := (hint (update q e 0)).smul_measure
    (by simp : ((unitInterval.toNNReal (σ (q e)) : ℝ≥0∞)) ≠ ⊤)
  calc
    (∫ ω, G ω ∂(unitInterval.toNNReal (q e) • prodBernoulli (update q e 1) +
      unitInterval.toNNReal (σ (q e)) • prodBernoulli (update q e 0))) =
        (∫ ω, G ω ∂unitInterval.toNNReal (q e) • prodBernoulli (update q e 1)) +
          ∫ ω, G ω ∂unitInterval.toNNReal (σ (q e)) • prodBernoulli (update q e 0) :=
        integral_add_measure hμ hν
    _ = _ := by
      have hsm1 := integral_smul_measure (μ := prodBernoulli (update q e 1)) G
        ((unitInterval.toNNReal (q e) : ℝ≥0∞))
      have hsm2 := integral_smul_measure (μ := prodBernoulli (update q e 0)) G
        ((unitInterval.toNNReal (σ (q e)) : ℝ≥0∞))
      exact congrArg₂ (fun (x y : ℝ) => x + y) hsm1 hsm2

open Classical in
/-- One-coordinate Russo, in the closed-coordinate normalization, for a bounded measurable
observable on an arbitrary (in particular a countably infinite) product space. -/
theorem one_sub_mul_integral_insert_sub_basic {ι : Type*} (q : ι → unitInterval) (e : ι)
    (G : Set ι → ℝ) (hG : Measurable G) {m : ℝ} (hGm : ∀ ω, |G ω| ≤ m) :
    (1 - (q e : ℝ)) * ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂prodBernoulli q =
      ∫ ω, (if e ∈ ω then 0 else G (insert e ω) - G ω) ∂prodBernoulli q := by
  classical
  let Δ : Set ι → ℝ := fun ω => G (insert e ω) - G (ω \ {e})
  have hΔmeas : Measurable Δ :=
    (hG.comp (measurable_insert e)).sub (hG.comp (measurable_diff_singleton e))
  have hΔbound : ∀ ω, |Δ ω| ≤ 2 * m := by
    intro ω
    exact (abs_sub _ _).trans (by linarith [hGm (insert e ω), hGm (ω \ {e})])
  have hint : ∀ p : ι → unitInterval, Integrable G (prodBernoulli p) := by
    intro p
    exact Integrable.of_bound (C := m) hG.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hGm ω)
  have hΔ_integral : ∀ p : ι → unitInterval, (∫ ω, Δ ω ∂prodBernoulli p) =
      (∫ ω, G ω ∂prodBernoulli (update p e 1)) -
        ∫ ω, G ω ∂prodBernoulli (update p e 0) := by
    intro p
    have hintInsert : Integrable (fun ω => G (insert e ω)) (prodBernoulli p) := by
      exact Integrable.of_bound (C := m) (hG.comp (measurable_insert e)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hGm (insert e ω))
    have hintDelete : Integrable (fun ω => G (ω \ {e})) (prodBernoulli p) := by
      exact Integrable.of_bound (C := m)
        (hG.comp (measurable_diff_singleton e)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hGm (ω \ {e}))
    rw [integral_sub (f := fun ω => G (insert e ω)) (g := fun ω => G (ω \ {e}))
      hintInsert hintDelete]
    congr 1
    · rw [← prodBernoulli_map_insert, integral_map (measurable_insert e).aemeasurable
        hG.aestronglyMeasurable]
    · rw [← prodBernoulli_map_diff_singleton, integral_map
        (measurable_diff_singleton e).aemeasurable hG.aestronglyMeasurable]
  let A : Set (Set ι) := {ω | e ∉ ω}
  have hA : MeasurableSet A := (measurableSet_mem e).compl
  have hopen0 : prodBernoulli (update q e 0) {ω | e ∈ ω} = 0 := by
    simp only [prodBernoulli_setOf_mem, Function.update_self]
    rfl
  have hclosed1 : prodBernoulli (update q e 1) A = 0 := by
    have hone : prodBernoulli (update q e 1) {ω | e ∈ ω} = 1 := by
      simp only [prodBernoulli_setOf_mem, Function.update_self]
      rfl
    rw [show A = {ω | e ∈ ω}ᶜ from rfl,
      measure_compl (measurableSet_mem e) (by simp)]
    rw [hone]
    simp
  have hzero : ∀ᵐ ω ∂prodBernoulli (update q e 1), A.indicator Δ ω = 0 := by
    have hae : ∀ᵐ ω ∂prodBernoulli (update q e 1), e ∈ ω := mem_ae_iff.1 hclosed1
    filter_upwards [hae] with ω hω
    simp [A, Set.indicator, hω]
  have hfactor : ∀ᵐ ω ∂prodBernoulli (update q e 0), A.indicator Δ ω = Δ ω := by
    have hae : ∀ᵐ ω ∂prodBernoulli (update q e 0), e ∉ ω :=
      measure_eq_zero_iff_ae_notMem.1 hopen0
    filter_upwards [hae] with ω hω
    simp [A, Set.indicator, hω]
  have hbind : ∀ ω, A.indicator Δ ω = if e ∈ ω then 0 else G (insert e ω) - G ω := by
    intro ω
    by_cases h : e ∈ ω <;> simp [A, Δ, Set.indicator, h]
  have hm0 : 0 ≤ m := (abs_nonneg (G ∅)).trans (hGm ∅)
  have hgm : ∀ ω, |A.indicator Δ ω| ≤ 2 * m := by
    intro ω
    by_cases h : e ∈ ω
    · simp [A, Set.indicator, h, hm0]
    · simp [A, Set.indicator, h, hΔbound ω]
  have hformula := integral_prodBernoulli_affine q e (A.indicator Δ)
    (hΔmeas.indicator hA) hgm
  have hclosed : (∫ ω, A.indicator Δ ω ∂prodBernoulli q) =
      (1 - (q e : ℝ)) * ∫ ω, Δ ω ∂prodBernoulli (update q e 0) := by
    rw [hformula, integral_congr_ae hzero, integral_congr_ae hfactor]
    simp
  calc (1 - (q e : ℝ)) * ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂prodBernoulli q
      = (1 - (q e : ℝ)) * ∫ ω, Δ ω ∂prodBernoulli q := rfl
    _ = (1 - (q e : ℝ)) * ∫ ω, Δ ω ∂prodBernoulli (update q e 0) := by
        simp only [hΔ_integral, Function.update_idem]
    _ = ∫ ω, A.indicator Δ ω ∂prodBernoulli q := hclosed.symm
    _ = ∫ ω, (if e ∈ ω then 0 else G (insert e ω) - G ω) ∂prodBernoulli q := by
        rw [integral_congr_ae (Eventually.of_forall hbind)]

end PercLib.Probability

/-! ## Cutoff supports and dominator bounds

On `ℤ^d`, cutoff support is radial in the displacement vector: the same short displacement
occurs at infinitely many pairs. Summability of the derivative weight alone therefore is not a
general bound. Finite vertex dominators are explicit; on infinite lattices the relevant
additional input is summability of the radially weighted moment diagram.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology unitInterval

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-! ### Where the pivotal increment is supported -/

/-- If no endpoint of the pair `e` lies in the cluster of `o`, then forcing `e` open and forcing
`e` closed give the same cluster of `o`. This is the precise sense in which the pivotal increment
of `o` is supported on the pairs touching the cluster of `o`; in particular the cluster of `o`
after inserting `e` is not, in general, the union of the endpoint clusters. -/
theorem cluster_insert_eq_cluster_sdiff_of_forall_not_mem {V : Type*} {ω : Config V} {o : V}
    {e : Sym2 V} (he : ∀ x ∈ e, x ∉ cluster ω o) :
    cluster (insert e ω) o = cluster (ω \ {e}) o := by
  have hsub : cluster (ω \ {e}) o ⊆ cluster ω o :=
    cluster_mono (sdiff_subset (s := ω) (t := {e})) o
  have h1 : cluster (insert e (ω \ {e})) o = cluster (ω \ {e}) o :=
    cluster_insert_eq_of_forall_not_mem fun x hx hmem => he x hx (hsub hmem)
  rwa [Set.insert_sdiff_singleton] at h1

/-- The `p`-th pivotal increment of `o` vanishes at every configuration in which the pair `e` does
not touch the cluster of `o`. -/
theorem pivotal_encard_pow_sub_eq_zero_of_forall_not_mem {V : Type*} {ω : Config V} {o : V}
    {e : Sym2 V} {pow : ℕ} (he : ∀ x ∈ e, x ∉ cluster ω o) :
    ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow = 0 := by
  rw [cluster_insert_eq_cluster_sdiff_of_forall_not_mem he, tsub_self]

/-- Monotonicity of the `pow`-th cluster volume under forcing the pair `e` open. -/
theorem encard_sdiff_pow_le_insert_pow {V : Type*} {ω : Config V} {o : V} {e : Sym2 V}
    {pow : ℕ} :
    ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow := by
  have hsub : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) := by
    exact_mod_cast Set.encard_le_encard
      (cluster_mono ((sdiff_subset (s := ω) (t := {e})).trans (subset_insert e ω)) o)
  exact pow_le_pow_left₀ (zero_le : (0 : ℝ≥0∞) ≤ _) hsub pow

/-! ### The size of the cut-off derivative weight -/

variable {d : ℕ}

/-- **The derivative weight is bounded by the radial indicator times `β L`.** For `|K' r| ≤ L` the
weight `c_r(e) = 1{N(e) < r} * β (-K'(r)) * exp (-β J_r(e))` of the cut-off family is at most
`β L` times the indicator `1{N(e) < r}`; the exponential factor is at most `1` because the cut-off
kernel is nonnegative and `β ≥ 0`. -/
theorem abs_radialKernel_indicator_mul_exp_le (N : Seminorm ℝ (Fin d → ℝ)) (β : ℝ≥0)
    (K K' : ℝ → ℝ) {r L : ℝ} (hL : |K' r| ≤ L) (e : Sym2 (Fin d → ℤ)) :
    |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))| ≤
      (β : ℝ) * L * (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) := by
  have hind0 : (0 : ℝ) ≤ (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) :=
    (radialKernel N (fun s => if s < r then 1 else 0) e).coe_nonneg
  have hJ : (0 : ℝ) ≤ (cutoffKernel N K r e : ℝ) := (cutoffKernel N K r e).coe_nonneg
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
  have hL0 : 0 ≤ L := (abs_nonneg (K' r)).trans hL
  have hexp1 : Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hJ
  have hfac : |(β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))| ≤
      (β : ℝ) * L := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_pos (Real.exp_pos _)]
    calc ((β : ℝ) * |K' r|) * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))
        ≤ ((β : ℝ) * L) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL hβ) hexp1 (Real.exp_pos _).le
            (mul_nonneg hβ hL0)
      _ = (β : ℝ) * L := mul_one _
  calc |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))|
      = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        |(β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))| := by
        rw [abs_mul, abs_of_nonneg hind0]
    _ ≤ (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * ((β : ℝ) * L) :=
        mul_le_mul_of_nonneg_left hfac hind0
    _ = (β : ℝ) * L * (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) := by ring

/-- The same bound with the indicator dropped: on `|K' r| ≤ L` every derivative weight of the
cut-off family is at most `β L`. This is the pointwise bound a finite vertex set needs, where the
edge set is finite. -/
theorem abs_radialKernel_indicator_mul_exp_le_const (N : Seminorm ℝ (Fin d → ℝ)) (β : ℝ≥0)
    (K K' : ℝ → ℝ) {r L : ℝ} (hL : |K' r| ≤ L) (e : Sym2 (Fin d → ℤ)) :
    |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))| ≤ (β : ℝ) * L := by
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
  have hL0 : 0 ≤ L := (abs_nonneg (K' r)).trans hL
  refine (abs_radialKernel_indicator_mul_exp_le N β K K' hL e).trans ?_
  have hind1 : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≤ 1 := by
    rcases radialKernel_indicator_eq_zero_or_one N r e with h | h
    · rw [h]; norm_num
    · rw [h]
  calc (β : ℝ) * L * (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ)
      ≤ (β : ℝ) * L * 1 := mul_le_mul_of_nonneg_left hind1 (mul_nonneg hβ hL0)
    _ = (β : ℝ) * L := mul_one _

/-- The indicator `1{N (e) < r}` vanishes off the cut-off: for `N (x - y) ≥ r` the weight factor is
`0`. -/
theorem radialKernel_indicator_eq_zero_of_not_lt {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ}
    {x y : Fin d → ℤ} (h : ¬ N (Int.cast ∘ (x - y)) < r) :
    (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) = 0 := by
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [radialKernel_of_ne hxy]
    simp [h]

/-- **The finite support of the weight is radial.** The derivative weight is not a finitely
supported function of the pair on `ℤ^d` — every short difference vector occurs at infinitely many
positions — but it vanishes at every pair whose difference vector is outside the finite set
`{z ≠ 0 : N z < r}` of `finite_norm_lt`. This is the exact form in which finite support is
available in infinite volume. -/
theorem exists_finset_cutoff_deriv_weight_eq_zero (N : ModelNorm (Fin d → ℝ)) (β : ℝ≥0)
    (K K' : ℝ → ℝ) (r : ℝ) :
    ∃ D : Finset (Fin d → ℤ), ∀ z ∉ D, ∀ x : Fin d → ℤ,
      (radialKernel N (fun s => if s < r then 1 else 0) s(x + z, x) : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r s(x + z, x) : ℝ))) = 0 := by
  classical
  refine ⟨(finite_norm_lt N r).toFinset, fun z hz x => ?_⟩
  by_cases hz0 : z = 0
  · subst hz0
    simp
  · have hlt : ¬ N (Int.cast ∘ z) < r := fun hc =>
      hz ((finite_norm_lt N r).mem_toFinset.mpr ⟨hz0, hc⟩)
    have hsub : (x + z) - x = z := by abel
    have hne : ¬ N (Int.cast ∘ ((x + z) - x)) < r := by rw [hsub]; exact hlt
    rw [radialKernel_indicator_eq_zero_of_not_lt (N := N) (x := x + z) (y := x) hne, zero_mul]


/-! ### The per-edge pivotal moment bound -/

/-- **The pivotal `p`-th increment is at most the inserted `p`-th moment.** Forcing `e` closed only
shrinks the cluster of `o`, so the increment is nonnegative and at most the inserted cluster volume
to the `p`; integrating gives the bound. No independence, no mass transport and no moment input
beyond the integrability of the inserted moment are used. -/
theorem abs_integral_pivotal_encard_pow_le {V : Type*} [Countable V] (μ : Measure (Config V))
    (e : Sym2 V) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ∂μ| ≤
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂μ := by
  have hle : ∀ᵐ ω ∂μ, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ≤
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
    filter_upwards [hfin] with ω hω
    have htop : ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow ≠ ⊤ := ENNReal.pow_ne_top hω
    have hmono := ENNReal.toReal_mono htop (tsub_le_self :
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)
    rwa [ENNReal.toReal_pow] at hmono
  have hnonneg : 0 ≤ ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ∂μ :=
    integral_nonneg fun ω => ENNReal.toReal_nonneg
  rw [abs_of_nonneg hnonneg]
  exact integral_mono_of_nonneg (Eventually.of_forall fun ω => ENNReal.toReal_nonneg) hint hle

/-! ### The weight is not summable on the infinite lattice -/

/-- The multiples of a nonzero integer vector are distinct. -/
theorem nsmul_injective_of_ne_zero {d : ℕ} {z : Fin d → ℤ} (hz : z ≠ 0) :
    Function.Injective fun n : ℕ => n • z := by
  have hcoord : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  obtain ⟨i, hi⟩ := hcoord
  intro n m h
  have h2 : ((n : ℤ) * z i) = ((m : ℤ) * z i) := by
    have h3 := congrFun h i
    simpa only [Pi.smul_apply, nsmul_eq_mul] using h3
  have h4 : (n : ℤ) = (m : ℤ) := by
    refine (mul_right_inj' (a := z i) hi).mp ?_
    rw [mul_comm (z i) ((n : ℤ)), mul_comm (z i) ((m : ℤ))]
    exact h2
  exact_mod_cast h4

/-- The pairs `{n z + z, n z}` are distinct for distinct `n`, when `z ≠ 0`. -/
theorem injective_pair_succ_nsmul {d : ℕ} {z : Fin d → ℤ} (hz : z ≠ 0) :
    Function.Injective fun n : ℕ => s(n • z + z, n • z) := by
  intro n m h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact nsmul_injective_of_ne_zero hz h2
  · have e1 : (n + 1) • z = m • z := by rw [succ_nsmul]; exact h1
    have e2 : n • z = (m + 1) • z := by rw [succ_nsmul]; exact h2
    have h3 := nsmul_injective_of_ne_zero hz e1
    have h4 := nsmul_injective_of_ne_zero hz e2
    omega

/-- **The radial indicator is not summable on `ℤ^d`.** Along the pairs `{n z, (n+1) z}` the
indicator `1{N (e) < r}` is constantly `1`, so as soon as some nonzero lattice point has `N z < r`
the indicator has infinite `ℓ¹` mass. This is the exact obstruction that keeps
`summable_flux_dominator_of_uniform_moment` — and hence `abs_tsum_capped_flux_le` with a
position-independent weight — out of reach on the infinite lattice: the pairs of a fixed short
length are infinitely many, and no bound that forgets the position of the pair can sum over them.
The replacement is `dominator_cutoff_of_summable_indicator_moment`, whose hypothesis is about the
inserted *moments* and not about the weights alone. -/
theorem not_summable_radialKernel_indicator (N : ModelNorm (Fin d → ℝ)) {r : ℝ}
    {z : Fin d → ℤ} (hz : z ≠ 0) (hzr : N (Int.cast ∘ z) < r) :
    ¬ Summable fun e : Sym2 (Fin d → ℤ) =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) := by
  intro hsum
  have hne : ∀ n : ℕ, n • z + z ≠ n • z := by
    intro n h
    refine hz ?_
    have h' := congrArg (fun t => t - n • z) h
    simpa using h'
  have hval : ∀ n : ℕ,
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) = 1 := by
    intro n
    rw [coe_radialKernel_of_ne (N := N) (K := fun s => if s < r then 1 else 0)
      (x := n • z + z) (y := n • z) (hne n) (by positivity)]
    simp [hzr]
  have hcomp : Summable fun n : ℕ =>
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) :=
    hsum.comp_injective (injective_pair_succ_nsmul hz)
  rw [show (fun n : ℕ => (radialKernel N (fun s => if s < r then 1 else 0)
      (s(n • z + z, n • z)) : ℝ)) = fun _ => (1 : ℝ) from funext hval] at hcomp
  exact absurd (tendsto_nhds_unique hcomp.tendsto_atTop_zero tendsto_const_nhds) (by norm_num)

-- the statement and the value computation both unfold the cut-off kernel at a concrete pair
/-- **The cut-off derivative weight is not summable on `ℤ^d`.** For `β > 0` and `K' r ≠ 0` the same
pair family shows that `|c_r(e)|` is a *positive constant* along `e = {n z + z, n z}`: the radial
indicator is `1` and the cut-off kernel, hence the exponential factor, depends only on the
difference `z`. So `Summable fun e => |c r e|` — the weight hypothesis of
`summable_flux_dominator_of_uniform_moment` and of `abs_tsum_capped_flux_le` — fails on the infinite
lattice whenever the cut-off is not degenerate. This closes that route for infinite volume: the
unweighted all-pairs series can only be controlled through the inserted moments, as in
`dominator_cutoff_of_summable_indicator_moment`. -/
theorem not_summable_cutoff_deriv_weight (N : ModelNorm (Fin d → ℝ)) (β : ℝ≥0)
    {K K' : ℝ → ℝ} {r : ℝ} {z : Fin d → ℤ} (hz : z ≠ 0) (hzr : N (Int.cast ∘ z) < r)
    (hβ : 0 < (β : ℝ)) (hK' : K' r ≠ 0) :
    ¬ Summable fun e : Sym2 (Fin d → ℤ) =>
      |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))| := by
  intro hsum
  have hne : ∀ n : ℕ, n • z + z ≠ n • z := by
    intro n h
    refine hz ?_
    have h' := congrArg (fun t => t - n • z) h
    simpa using h'
  -- the value of the cut-off kernel at the pair family, which depends only on `z`
  have hck : ∀ n : ℕ, (cutoffKernel N K r (s(n • z + z, n • z)) : ℝ) =
      ((cutoffProfile K r (N.toSeminorm (Int.cast ∘ z))).toNNReal : ℝ) := by
    intro n
    rw [cutoffKernel, radialKernel_of_ne (x := n • z + z) (y := n • z) (hne n),
      show (n • z + z) - n • z = z from by abel]
  have hind : ∀ n : ℕ,
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) = 1 := by
    intro n
    rw [coe_radialKernel_of_ne (N := N) (K := fun s => if s < r then 1 else 0)
      (x := n • z + z) (y := n • z) (hne n) (by positivity),
      show (n • z + z) - n • z = z from by abel]
    simp [hzr]
  set δ : ℝ := (β : ℝ) * |K' r| *
    Real.exp (-(β : ℝ) * ((cutoffProfile K r (N.toSeminorm (Int.cast ∘ z))).toNNReal : ℝ)) with hδ
  have hδpos : 0 < δ := by
    have h1 : 0 < |K' r| := abs_pos.mpr hK'
    have h2 : 0 < Real.exp (-(β : ℝ) *
      ((cutoffProfile K r (N.toSeminorm (Int.cast ∘ z))).toNNReal : ℝ)) :=
      Real.exp_pos _
    rw [hδ]
    positivity
  have hval : ∀ n : ℕ,
      |(radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) *
        ((β : ℝ) * -K' r *
          Real.exp (-(β : ℝ) * (cutoffKernel N K r (s(n • z + z, n • z)) : ℝ)))| = δ := by
    intro n
    rw [hind n, hck n, one_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg β.coe_nonneg,
      abs_of_pos (Real.exp_pos _), hδ]
  have hcomp : Summable fun n : ℕ =>
      |(radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) *
        ((β : ℝ) * -K' r *
          Real.exp (-(β : ℝ) * (cutoffKernel N K r (s(n • z + z, n • z)) : ℝ)))| :=
    hsum.comp_injective (injective_pair_succ_nsmul hz)
  rw [show (fun n : ℕ => |(radialKernel N (fun s => if s < r then 1 else 0)
      (s(n • z + z, n • z)) : ℝ) *
        ((β : ℝ) * -K' r *
          Real.exp (-(β : ℝ) * (cutoffKernel N K r (s(n • z + z, n • z)) : ℝ)))|)
      = fun _ => δ from funext hval] at hcomp
  exact hδpos.ne' (tendsto_nhds_unique hcomp.tendsto_atTop_zero tendsto_const_nhds).symm

/-! ### The all-pairs dominator on a finite vertex set -/

section Finite

variable {V : Type*} [Countable V] [Fintype V]

/-- **The all-pairs dominator with an explicit constant, finite vertex set.** If every derivative
weight is bounded by `C` and every inserted `p`-th moment by `K`, then every finite partial sum of
`|c r e|` times the absolute pivotal `p`-th increment is at most `C K #(Sym2 V)`. This is the
`hKd` shape of `hasDerivAt_integral_pow_of_cap_flux` with `Kd r = C K #(Sym2 V)`; finiteness of the
edge set is what makes the constant independent of `S`. -/
theorem sum_abs_weight_mul_abs_integral_pivotal_le (μ : Measure (Config V)) (c : Sym2 V → ℝ)
    (o : V) (pow : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : ∀ e, |c e| ≤ C)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ)
    (hbound : ∀ e, ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂μ ≤ K)
    (S : Finset (Sym2 V)) :
    ∑ e ∈ S, |c e| * |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ∂μ| ≤
      C * K * (Fintype.card (Sym2 V) : ℝ) := by
  have hflux : ∀ e, |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ∂μ| ≤ K := fun e =>
    (abs_integral_pivotal_encard_pow_le μ e o pow (hfin e) (hint e)).trans (hbound e)
  calc ∑ e ∈ S, |c e| * |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ∂μ|
      ≤ ∑ _e ∈ S, C * K := by
        refine Finset.sum_le_sum fun e _ => ?_
        exact mul_le_mul (hw e) (hflux e) (abs_nonneg _) hC
    _ = (S.card : ℝ) * (C * K) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (Sym2 V) : ℝ) * (C * K) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC hK)
        exact_mod_cast Finset.card_le_univ S
    _ = C * K * (Fintype.card (Sym2 V) : ℝ) := by ring

omit [Countable V] in
/-- The weighted inserted `p`-th moments are summable on a finite vertex set, with the explicit
bound `C K #(Sym2 V)`. This is the `hsum` of `abs_tsum_capped_flux_le` under a pointwise weight
bound, i.e. `Summable fun e => |c r e|` supplied concretely. -/
theorem tsum_abs_weight_mul_integral_pivotal_le (μ : Measure (Config V)) (c : Sym2 V → ℝ)
    (o : V) (pow : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : ∀ e, |c e| ≤ C)
    (hbound : ∀ e, ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂μ ≤ K) :
    ∑' e, |c e| * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂μ ≤
      C * K * (Fintype.card (Sym2 V) : ℝ) := by
  have hle : ∀ S : Finset (Sym2 V), ∑ e ∈ S, |c e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂μ ≤
      C * K * (Fintype.card (Sym2 V) : ℝ) := by
    intro S
    calc ∑ e ∈ S, |c e| * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂μ
        ≤ ∑ _e ∈ S, C * K := by
          refine Finset.sum_le_sum fun e _ => ?_
          exact mul_le_mul (hw e) (hbound e)
            (integral_nonneg fun ω => pow_nonneg ENNReal.toReal_nonneg pow) hC
      _ = (S.card : ℝ) * (C * K) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (Sym2 V) : ℝ) * (C * K) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC hK)
          exact_mod_cast Finset.card_le_univ S
      _ = C * K * (Fintype.card (Sym2 V) : ℝ) := by ring
  exact Real.tsum_le_of_sum_le (fun e => mul_nonneg (abs_nonneg _)
    (integral_nonneg fun ω => pow_nonneg ENNReal.toReal_nonneg pow)) hle

omit [Countable V] in
/-- On a finite vertex set no cluster has more than `#V` vertices. -/
theorem encard_cluster_insert_le_card (e : Sym2 V) (o : V) (ω : Config V) :
    ((cluster (insert e ω) o).encard : ℝ≥0∞) ≤ (Fintype.card V : ℝ≥0∞) := by
  have h3 : (cluster (insert e ω) o).encard ≤ (univ : Set V).encard :=
    Set.encard_le_encard (subset_univ _)
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card] at h3
  exact_mod_cast h3

omit [Countable V] in
/-- On a finite vertex set every cluster has at most `#V` vertices, so the inserted `p`-th moment is
at most `(#V)^p` pointwise. -/
theorem encard_cluster_insert_toReal_pow_le_card (e : Sym2 V) (o : V) (pow : ℕ)
    (ω : Config V) :
    (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ≤ (Fintype.card V : ℝ) ^ pow := by
  have h2 := encard_cluster_insert_le_card e o ω
  calc (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
      ≤ ((Fintype.card V : ℝ≥0∞).toReal) ^ pow :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (by simp) h2) pow
    _ = (Fintype.card V : ℝ) ^ pow := by rw [ENNReal.toReal_natCast]

omit [Countable V] in
/-- **The uniform inserted `p`-th moment bound holds automatically on a finite vertex set**, with
the explicit constant `(#V)^p`. So the finite-volume form of the dominator needs no moment input at
all. -/
theorem integral_encard_cluster_pow_le_card (q : Sym2 V → unitInterval) (e : Sym2 V) (o : V)
    (pow : ℕ) :
    ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law q) ≤
      (Fintype.card V : ℝ) ^ pow := by
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω =>
    pow_nonneg ENNReal.toReal_nonneg pow) (integrable_const ((Fintype.card V : ℝ) ^ pow))
    (Eventually.of_forall fun ω => encard_cluster_insert_toReal_pow_le_card e o pow ω)).trans
    (le_of_eq ?_)
  rw [integral_const, Measure.real, measure_univ]
  simp

/-- **The dominator and its interval integrability, fully discharged on a finite vertex set.** With
the weight bound `C`, the automatic moment bound `(#V)^p` and `Kd r = C (#V)^p #(Sym2 V)`, both
`hKd` and `hKdint` of `hasDerivAt_integral_pow_of_cap_flux` hold at every parameter and every
interval. -/
theorem exists_dominator_fintype (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V)
    (pow : ℕ) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ r e, |c r e| ≤ C) :
    (∀ r : ℝ, ∀ S : Finset (Sym2 V), ∑ e ∈ S, |c r e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal ∂(law (p r))| ≤
        C * (Fintype.card V : ℝ) ^ pow * (Fintype.card (Sym2 V) : ℝ)) ∧
      (∀ u v : ℝ, IntervalIntegrable
        (fun _ : ℝ => C * (Fintype.card V : ℝ) ^ pow * (Fintype.card (Sym2 V) : ℝ))
        volume u v) := by
  have hK : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ pow := pow_nonneg (Nat.cast_nonneg _) pow
  have hfin : ∀ (r : ℝ) (e : Sym2 V), ∀ᵐ ω ∂(law (p r)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ :=
    fun r e => Eventually.of_forall fun ω =>
      ne_top_of_le_ne_top (by simp) (encard_cluster_insert_le_card e o ω)
  have hint : ∀ (r : ℝ) (e : Sym2 V), Integrable
      (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) (law (p r)) := by
    intro r e
    refine Integrable.of_bound
      ((measurable_encard_cluster_insert_coe e o).ennreal_toReal.pow_const pow).aestronglyMeasurable
      ((Fintype.card V : ℝ) ^ pow) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg ENNReal.toReal_nonneg pow)]
    exact encard_cluster_insert_toReal_pow_le_card e o pow ω
  refine ⟨fun r S => ?_, fun u v => intervalIntegrable_const⟩
  exact sum_abs_weight_mul_abs_integral_pivotal_le (law (p r)) (c r) o pow hC hK (hw r)
    (hfin r) (hint r) (fun e => integral_encard_cluster_pow_le_card (p r) e o pow) S

omit [Countable V] in
/-- **The `hsum` of `abs_tsum_capped_flux_le`, with the weight summability supplied concretely.** On
a finite vertex set a pointwise weight bound gives `Summable fun e => |c r e|`, hence the weighted
inserted moments are summable in the shape consumed by `summable_flux_dominator_of_uniform_moment`,
which is the dominator hypothesis of `abs_tsum_capped_flux_le` and
`integral_sub_eq_integral_flux_of_cap`, with the explicit value `C K #(Sym2 V)`. On `ℤ^d` this
route is closed (the weight has infinite `ℓ¹` mass);
`dominator_cutoff_of_summable_indicator_moment` is the replacement there. -/
theorem summable_weight_mul_integral_pivotal_of_fintype (p : ℝ → Sym2 V → unitInterval)
    (c : ℝ → Sym2 V → ℝ) (o : V) (pow : ℕ) (r : ℝ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hw : ∀ e, |c r e| ≤ C)
    (hbound : ∀ e, ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
      ∂(law (p r)) ≤ K) :
    Summable (fun e => |c r e| * ∫ ω,
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) ∧
      ∑' e, |c r e| * ∫ ω,
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) ≤
        C * K * (Fintype.card (Sym2 V) : ℝ) := by
  have hsumm : Summable (fun e => |c r e| * ∫ ω,
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) :=
    summable_flux_dominator_of_uniform_moment p c o pow r hbound Summable.of_finite
  exact ⟨hsumm, tsum_abs_weight_mul_integral_pivotal_le (law (p r)) (c r) o pow hC hK (hw)
    (hbound)⟩

end Finite

/-! ### Non-vacuity -/

/-- Non-vacuity of the finite-volume dominator: on the one-point vertex type every cluster is the
whole vertex set, so the inserted `p`-th moment is exactly `1` and the bound with `(#V)^p = 1`
holds. -/
example (q : Sym2 Unit → unitInterval) (e : Sym2 Unit) (o : Unit) (pow : ℕ) :
    ∫ ω : Config Unit, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law q) ≤ 1 := by
  have h := integral_encard_cluster_pow_le_card (V := Unit) q e o pow
  simpa using h

end PercLib.Models.LongRange

/-! ## Closed normalization of the cutoff derivative coefficient

On an active cutoff pair, the derivative coefficient times the endpoint integral equals
the profile rate times the closed-coordinate integral. The active-pair hypothesis is
necessary: an inactive radial coefficient vanishes, while an arbitrary bounded observable
need not.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology unitInterval

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- Exact closed-coordinate form of the cutoff Russo coefficient, for a bounded observable. -/
theorem cutoff_pivotal_eq_closed {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (β : ℝ≥0) (r : ℝ) (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ)
    (hactive : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0) :
    ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      (β : ℝ) * -K' r *
        ∫ ω, (if e ∈ ω then 0 else F (cluster (insert e ω) o).encard -
          F (cluster ω o).encard) ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  let q := intensityProfile (cutoffKernel N K r) β
  let G : Config (Fin d → ℤ) → ℝ := fun ω => F (cluster ω o).encard
  have hG : Measurable G :=
    (measurable_of_countable F).comp (measurable_encard_cluster o)
  have hGbd : ∀ ω, |G ω| ≤ m := by intro ω; exact hFm _
  have hclosed : (1 - (q e : ℝ)) * ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q =
      ∫ ω, (if e ∈ ω then 0 else G (insert e ω) - G ω) ∂law q :=
    one_sub_mul_integral_insert_sub_basic q e G hG hGbd
  have hprob : (1 - (q e : ℝ)) =
      Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) := by
    simp [q, intensityProfile]
  have hleft : (β : ℝ) * -K' r * (1 - (q e : ℝ)) *
      ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q =
      (β : ℝ) * -K' r * ∫ ω, (if e ∈ ω then 0 else G (insert e ω) - G ω) ∂law q := by
    calc (β : ℝ) * -K' r * (1 - (q e : ℝ)) *
        ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q =
        (β : ℝ) * -K' r * ((1 - (q e : ℝ)) *
          ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q) := by ring
      _ = _ := by rw [hclosed]
  change ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
    ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q = _
  have hrad : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) = 1 :=
    (radialKernel_indicator_eq_zero_or_one N r e).resolve_left hactive
  rw [← hprob, hrad, one_mul]
  simpa only [G, q] using hleft

/-- A zero-seminorm active-pair witness. -/
example :
    (radialKernel (0 : Seminorm ℝ (Fin 1 → ℝ))
      (fun s => if s < (2 : ℝ) then 1 else 0)
      (s(0, fun _ : Fin 1 => (1 : ℤ))) : ℝ) ≠ 0 := by
  have hne : (0 : Fin 1 → ℤ) ≠ fun _ : Fin 1 => (1 : ℤ) := by
    intro h
    have hi := congrFun h 0
    norm_num at hi
  rw [coe_radialKernel_of_ne hne (by positivity)]
  norm_num

end PercLib.Models.LongRange

/-! ## The radial-indicator moment dominator

Nonnegativity and summability of a radially weighted moment diagram give a dominator
for the actual pivotal flux, including the inserted-moment and `hKd` formulations.
The diagram itself and continuity of the uncapped flux remain separate hypotheses.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology unitInterval

namespace PercLib.Models.LongRange
open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- If weights are bounded by `C κ` and fluxes by `m`, their total weighted flux is at most
`C` times the sum of `κ m`, assuming it is finite. -/
theorem sum_abs_mul_abs_le_tsum {ι : Type*} [Countable ι] {w κ m Q : ι → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hκ : ∀ e, 0 ≤ κ e) (hw : ∀ e, |w e| ≤ C * κ e)
    (hm : ∀ e, 0 ≤ m e) (hQ : ∀ e, |Q e| ≤ m e)
    (hsum : Summable fun e => κ e * m e) :
    ∀ S : Finset ι, ∑ e ∈ S, |w e| * |Q e| ≤ C * ∑' e, κ e * m e := by
  intro S
  have hstep : ∀ e ∈ S, |w e| * |Q e| ≤ C * (κ e * m e) := by
    intro e _
    exact (mul_le_mul (hw e) (hQ e) (abs_nonneg _) (mul_nonneg hC (hκ e))).trans_eq
      (mul_assoc C (κ e) (m e))
  calc ∑ e ∈ S, |w e| * |Q e|
      ≤ ∑ e ∈ S, C * (κ e * m e) := Finset.sum_le_sum hstep
    _ = C * ∑ e ∈ S, κ e * m e := by rw [Finset.mul_sum]
    _ ≤ C * ∑' e, κ e * m e := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact hsum.sum_le_tsum S fun i _ => mul_nonneg (hκ i) (hm i)

/-- The same bound with the cutoff coefficient and radial indicator, under a nonnegative
per-edge majorant whose indicator-weighted sum converges. -/
theorem dominator_of_abs_flux_le {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ))
    (K K' : ℝ → ℝ) (β : ℝ≥0) {r L : ℝ} (hL : |K' r| ≤ L)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {Q m : Sym2 (Fin d → ℤ) → ℝ} (hm : ∀ e, 0 ≤ m e)
    (hQ : ∀ e, |Q e| ≤ m e)
    (hsum : Summable fun e =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| * |Q e| ≤
      (β : ℝ) * L * ∑' e,
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e := by
  refine sum_abs_mul_abs_le_tsum (w := cw) (Q := Q) (m := m)
    (C := (β : ℝ) * L) ?_ (fun e => ?_) (fun e => ?_) hm hQ hsum
  · exact mul_nonneg β.coe_nonneg ((abs_nonneg (K' r)).trans hL)
  · exact (radialKernel N (fun s => if s < r then 1 else 0) e).coe_nonneg
  · simpa only [hcw] using abs_radialKernel_indicator_mul_exp_le N β K K' hL e

/-- **The radial-indicator weighted moment dominator.** The only convergence input is the
indicator-weighted sum of nonnegative bounds on the actual per-edge pivotal fluxes. -/
theorem dominator_cutoff_of_summable_indicator_moment {d : ℕ}
    (N : Seminorm ℝ (Fin d → ℝ)) (β : ℝ≥0) (K K' : ℝ → ℝ)
    {r L : ℝ} (hL : |K' r| ≤ L) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (o : Fin d → ℤ) (pow : ℕ)
    {m : Sym2 (Fin d → ℤ) → ℝ} (hm : ∀ e, 0 ≤ m e)
    (hflux : ∀ e, |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ m e)
    (hsum : Summable fun e =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
      (β : ℝ) * L * ∑' e,
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e :=
  by
  exact dominator_of_abs_flux_le N K K' β hL cw hcw hm hflux hsum

/-- The previous result written using the draft's `ModelNorm` binder. -/
theorem dominator_cutoff_of_summable_indicator_moment_modelNorm {d : ℕ}
    (N : ModelNorm (Fin d → ℝ)) (β : ℝ≥0) (K K' : ℝ → ℝ)
    {r L : ℝ} (hL : |K' r| ≤ L) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (o : Fin d → ℤ) (pow : ℕ)
    {m : Sym2 (Fin d → ℤ) → ℝ} (hm : ∀ e, 0 ≤ m e)
    (hflux : ∀ e, |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ m e)
    (hsum : Summable fun e =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
      (β : ℝ) * L * ∑' e,
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e :=
  dominator_cutoff_of_summable_indicator_moment N.toSeminorm β K K' hL cw hcw o pow hm
    hflux hsum



/-- The indicator-weighted inserted-moment dominator, using integral bounds for the flux. -/
theorem dominator_cutoff_of_summable_indicator_insertedMoment {d : ℕ}
    (N : Seminorm ℝ (Fin d → ℝ)) (β : ℝ≥0) (K K' : ℝ → ℝ)
    {r L : ℝ} (hL : |K' r| ≤ L) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (o : Fin d → ℤ) (pow : ℕ)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable
      (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (intensityProfile (cutoffKernel N K r) β)))
    (hsum : Summable fun e =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
          ∂(law (intensityProfile (cutoffKernel N K r) β))) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
      (β : ℝ) * L * ∑' e,
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
            ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  refine dominator_cutoff_of_summable_indicator_moment N β K K' hL cw hcw o pow
    (fun e => integral_nonneg fun ω => pow_nonneg ENNReal.toReal_nonneg pow) ?_ hsum
  intro e
  exact abs_integral_pivotal_encard_pow_le (law (intensityProfile (cutoffKernel N K r) β)) e o
    pow (hfin e) (hint e)

/-- The literal `hKd` dominator for the cutoff family. -/
theorem hKd_cutoff_of_summable_indicator_moment {d : ℕ}
    (N : Seminorm ℝ (Fin d → ℝ)) (β : ℝ≥0) (K K' : ℝ → ℝ)
    {u v L : ℝ} (hL : ∀ r ∈ Ioo u v, |K' r| ≤ L)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (o : Fin d → ℤ) (pow : ℕ)
    {m : ℝ → Sym2 (Fin d → ℤ) → ℝ} (hm : ∀ r e, 0 ≤ m r e)
    (hflux : ∀ r ∈ Ioo u v, ∀ e, |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ m r e)
    (hsum : ∀ r ∈ Ioo u v, Summable fun e =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m r e) :
    ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ S, |cw r e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
      (β : ℝ) * L * ∑' e,
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m r e := by
  intro r hr S
  exact dominator_cutoff_of_summable_indicator_moment N β K K' (hL r hr) (cw r) (hcw r) o pow (hm r)
    (fun e => hflux r hr e) (hsum r hr) S

/-- A nonzero, supported example of the diagram bound. -/
theorem nonvacuous_dominator_of_abs_flux_le {d : ℕ}
    (N : Seminorm ℝ (Fin d → ℝ)) (K K' : ℝ → ℝ) (β : ℝ≥0)
    {r L : ℝ} (hL : |K' r| ≤ L) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (e₀ : Sym2 (Fin d → ℤ)) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| * |(if e = e₀ then (1 : ℝ) else 0)| ≤
      (β : ℝ) * L * ∑' e,
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            (if e = e₀ then (1 : ℝ) else 0) := by
  classical
  refine dominator_of_abs_flux_le N K K' β hL cw hcw (Q := fun e => if e = e₀ then 1 else 0)
    (fun e => ?_) (fun e => ?_) ?_
  · split <;> norm_num
  · rw [abs_of_nonneg (by split <;> norm_num)]
  · refine summable_of_ne_finset_zero (s := {e₀}) fun b hb => ?_
    have hb' : b ≠ e₀ := by simpa using hb
    simp [hb']

/-- A non-diagonal pair at distance `< r` has indicator value one. -/
theorem radialKernel_indicator_eq_one {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) {r : ℝ}
    {x y : Fin d → ℤ} (hxy : x ≠ y) (hlt : N (Int.cast ∘ (x - y)) < r) :
    (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) = 1 := by
  rw [coe_radialKernel_of_ne (N := N) (K := fun s => if s < r then 1 else 0)
    (x := x) (y := y) hxy (by positivity)]
  simp [hlt]

/-- Summing a radially weighted single pair. -/
theorem tsum_single_pair {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) (e₀ : Sym2 (Fin d → ℤ)) :
    ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        (if e = e₀ then (1 : ℝ) else 0) =
      (radialKernel N (fun s => if s < r then 1 else 0) e₀ : ℝ) := by
  classical
  refine (tsum_eq_single (f := fun e =>
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      (if e = e₀ then (1 : ℝ) else 0)) e₀ ?_).trans ?_
  · intro b hb
    simp [hb]
  · simp

/-- The concrete single-edge nonlinear dominator. -/
theorem nonvacuous_bound_le {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) (K K' : ℝ → ℝ)
    (β : ℝ≥0) {r L : ℝ} (hL : |K' r| ≤ L) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {x y : Fin d → ℤ} (hxy : x ≠ y)
    (hlt : N (Int.cast ∘ (x - y)) < r) (S : Finset (Sym2 (Fin d → ℤ))) :
    ∑ e ∈ S, |cw e| * |(if e = s(x, y) then (1 : ℝ) else 0)| ≤
      (β : ℝ) * L := by
  refine ((nonvacuous_dominator_of_abs_flux_le N K K' β hL cw hcw s(x, y)) S).trans_eq ?_
  rw [tsum_single_pair, radialKernel_indicator_eq_one N hxy hlt, mul_one]

end PercLib.Models.LongRange
/-! ### Closed-coordinate capped and uncapped moments -/

open Filter
open scoped Topology unitInterval

namespace PercLib.Analysis

/-- **The `ℕ`-cap of a power converges.** For `x ≠ ⊤` the real numbers `(min n (x ^ p)).toReal`
increase to `x.toReal ^ p`; this is the scalar form of the cap passage used on the
closed-coordinate side of the pivotal identity. -/
theorem tendsto_min_nat_toReal_pow (pow : ℕ) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    Tendsto (fun n : ℕ => (min (n : ℝ≥0∞) (x ^ pow)).toReal) atTop (𝓝 (x.toReal ^ pow)) := by
  have hcast : Tendsto (fun n : ℕ => ((n : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
  refine ((tendsto_min_atTop (x.toReal ^ pow)).comp hcast).congr' ?_
  filter_upwards with n
  change min (x.toReal ^ pow) (n : ℝ) = (min (n : ℝ≥0∞) (x ^ pow)).toReal
  rw [← ENNReal.ofReal_natCast,
    ← PercLib.Percolation.Bond.capped_toReal_eq_min pow (Nat.cast_nonneg n) hx]

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

open Classical in
/-- **Cap passage on the closed-coordinate side of the pivotal identity.**

For an arbitrary measure `μ` on bond configurations, a pair `e` and a root `o`, the
closed-coordinate increments of the capped moments `min n (|K_o| ^ p)` converge to the
closed-coordinate increment of the uncapped moment.  The event `e ∈ ω` is killed first, so the
integrand is the one produced by the closed-coordinate conditioning
`one_sub_mul_integral_insert_sub_basic`.

Hypotheses, and nothing else: `|K_o|` is `μ`-a.e. finite after opening `e`, and the inserted
`p`-th moment is integrable; the latter is the dominator of the convergence.  No finiteness of
`μ`, no bound on the closed cluster and no summability over pairs is used. -/
theorem tendsto_integral_closed_pivotal_truncation (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Tendsto (fun n : ℕ => ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) := by
  classical
  have hA : Measurable fun ω : Config V => ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
    measurable_encard_cluster_insert_coe e o
  have hB : Measurable fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) :=
    Measurable.of_discrete.comp (measurable_encard_cluster (x := o))
  have hle : ∀ ω : Config V,
      ((cluster ω o).encard : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) := by
    intro ω
    exact_mod_cast encard_mono (cluster_mono (subset_insert e ω) o)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) ?_ ?_ hint ?_
  · filter_upwards with n
    have hX : Measurable fun ω : Config V =>
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal :=
      (ENNReal.measurable_toReal.comp (measurable_const.min (hA.pow_const pow))).sub
        (ENNReal.measurable_toReal.comp (measurable_const.min (hB.pow_const pow)))
    exact (Measurable.ite (measurableSet_mem e) measurable_const hX).aestronglyMeasurable
  · filter_upwards with n
    filter_upwards [hfin] with ω hω
    have hpow : ((cluster ω o).encard : ℝ≥0∞) ^ pow ≤
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow := ENNReal.pow_le_pow_left (hle ω)
    have hmin : min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow) ≤
        min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow) :=
      min_le_min_left _ hpow
    have htop : min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    have hreal : (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ≤
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal :=
      ENNReal.toReal_mono htop hmin
    have hupper : (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal ≤
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
      rw [← ENNReal.toReal_pow]
      exact ENNReal.toReal_mono (ENNReal.pow_ne_top hω) (min_le_right _ _)
    by_cases h : e ∈ ω
    · simp only [h, ite_true, Real.norm_eq_abs, abs_zero]
      exact pow_nonneg ENNReal.toReal_nonneg pow
    · simp only [h, ite_false, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hreal)]
      exact (sub_le_self _ ENNReal.toReal_nonneg).trans hupper
  · filter_upwards [hfin] with ω hω
    have hBtop : ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top hω (hle ω)
    by_cases h : e ∈ ω
    · simp only [h, ite_true]
      exact tendsto_const_nhds
    · simp only [h, ite_false]
      exact (PercLib.Analysis.tendsto_min_nat_toReal_pow pow hω).sub
        (PercLib.Analysis.tendsto_min_nat_toReal_pow pow hBtop)

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

open Classical in
/-- **The closed-coordinate pivotal identity for the uncapped `p`-th cluster moment.**

`cutoff_pivotal_eq_closed` proves the closed-coordinate normalisation for a bounded observable;
this is the same identity for the moment observable `ω ↦ |K_o(ω)| ^ p` itself, which is the
shape in which the cutoff Russo derivative `hasDerivAt_integral_cutoff_pow` presents the flux.

The pair must be active (`hactive`), and the two numerical inputs are exactly the ones the cap
passage consumes: `|K_o|` is a.e. finite after opening the pair, and the inserted `p`-th moment
is integrable.  Note that integrability of the inserted moment *implies* integrability of the
deleted one (`integrable_encard_sdiff_pow`), but not conversely: inserting an edge can merge the
cluster of `o` into an infinite component, so `hint` is genuinely an input and is not obtained
from the unconditional moment by monotonicity. -/
theorem cutoff_pivotal_eq_closed_pow {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (pow : ℕ) (β : ℝ≥0) (r : ℝ) (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ)
    (hactive : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0)
    (hfin : ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (intensityProfile (cutoffKernel N K r) β))) :
    ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
    (β : ℝ) * -K' r *
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  classical
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K r) β)
  let cw : ℝ := (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ)
  let c₀ : ℝ := (β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))
  let c₁ : ℝ := (β : ℝ) * -K' r
  have hkey : ∀ n : ℕ, cw * c₀ * (∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ) =
      c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else (min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ := by
    intro n
    have h := cutoff_pivotal_eq_closed (K := K) (K' := K')
      (F := fun k : ℕ∞ => (min (n : ℝ≥0∞) ((k : ℝ≥0∞) ^ pow)).toReal) (m := (n : ℝ))
      (fun k => abs_capped_pow_encard_le n pow k) β r e o hactive
    simpa only [μ, cw, c₀, c₁] using h
  have hlhs : Tendsto (fun n : ℕ => ∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) := by
    have h := (tendsto_integral_capped_pivotal μ e o pow hfin hint).comp
      tendsto_natCast_atTop_atTop
    refine h.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, ENNReal.ofReal_natCast]
  have hrhs : Tendsto (fun n : ℕ => ∫ ω, (if e ∈ ω then (0 : ℝ) else (min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    tendsto_integral_closed_pivotal_truncation μ e o pow hfin hint
  have h1 : Tendsto (fun n : ℕ => cw * c₀ * ∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (cw * c₀ * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    hlhs.const_mul (cw * c₀)
  have h2 : Tendsto (fun n : ℕ => c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else (min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    hrhs.const_mul c₁
  have h2' : Tendsto (fun n : ℕ => cw * c₀ * ∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    h2.congr' (Eventually.of_forall fun n => (hkey n).symm)
  simpa only [μ, cw, c₀, c₁] using tendsto_nhds_unique h1 h2'

open Classical in
/-- **The pair-summed closed-coordinate form of the cutoff pivotal flux.**

This is the summed form of `cutoff_pivotal_eq_closed_pow`: with the cutoff weight `cw` given by
its defining equation `hcw` (the shape in which `hasDerivAt_integral_cutoff_pow` carries it),
the pivotal flux series equals the profile rate times the closed-coordinate series, with the
radial indicator `radialKernel` retained as a factor.  The indicator is retained because it is
exactly the activity of the pair: for a pair with `radialKernel = 0` the weight `cw` vanishes and
the closed-coordinate contribution is also killed by the indicator, so the identity is not the
(forbidden) statement that an inactive pair contributes its closed-coordinate flux.

The two per-pair inputs are those of `cutoff_pivotal_eq_closed_pow`, uniformly over pairs.

**The remaining input of Lemma I.4.1 is not discharged here.**  The identity is stated with
Lean's `∑'`, which is `0` for a non-summable family; to use it as an identity of the paper's
fluxes one must *also* prove summability of the right-hand side
`∑'_e ‖radialKernel e * ∫ (if e ∈ ω then 0 else …)‖`.  No hypothesis in the library implies
that (in particular `hKd` bounds the pivotal flux, not the closed-coordinate flux), so it stays
an explicit input of any summed application. -/
theorem tsum_cutoff_pivotal_eq_closed_pow {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (pow : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (intensityProfile (cutoffKernel N K r) β))) :
    (∑' e, cw e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      ((β : ℝ) * -K' r) *
        ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  classical
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K r) β)
  let rk : Sym2 (Fin d → ℤ) → ℝ :=
    fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ)
  let Piv : Sym2 (Fin d → ℤ) → ℝ := fun e => ∫ ω,
    ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
      (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ
  let Clo : Sym2 (Fin d → ℤ) → ℝ := fun e => ∫ ω, (if e ∈ ω then (0 : ℝ) else
    (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
      (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ
  have hstep : ∀ e, cw e * Piv e = ((β : ℝ) * -K' r) * (rk e * Clo e) := by
    intro e
    rcases radialKernel_indicator_eq_zero_or_one N r e with h | h
    · simp only [rk, hcw e, h, zero_mul, mul_zero]
    · have hact : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0 := by
        rw [h]
        exact one_ne_zero
      have hz := cutoff_pivotal_eq_closed_pow (K := K) (K' := K') pow β r e o hact
        (hfin e) (hint e)
      rw [hcw e]
      simpa only [μ, rk, Piv, Clo, h, one_mul] using hz
  calc ∑' e, cw e * Piv e = ∑' e, ((β : ℝ) * -K' r) * (rk e * Clo e) := tsum_congr hstep
    _ = ((β : ℝ) * -K' r) * ∑' e, rk e * Clo e := tsum_mul_left

open Classical in
/-- **The per-pair closed-coordinate identity from unconditional per-vertex moments.**

The two inputs `hfin`/`hint` of `cutoff_pivotal_eq_closed_pow` concern the cluster of `o`
*after* opening the pair `e`, which is not the object the model controls.  Both follow from the
unconditional data at the three vertices `o` and the endpoints of `e`, through
`ae_ne_top_encard_cluster_insert` and `integrable_encard_cluster_insert_pow`; this is the
version to apply in a model where only per-vertex moments are available. -/
theorem cutoff_pivotal_eq_closed_pow_of_vertexMoments {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (pow : ℕ) (β : ℝ≥0) (r : ℝ) (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ)
    (hactive : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0)
    (hfinU : ∀ y : Fin d → ℤ, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hintU : ∀ y : Fin d → ℤ, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow)
      (law (intensityProfile (cutoffKernel N K r) β))) :
    ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
    (β : ℝ) * -K' r *
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  cutoff_pivotal_eq_closed_pow (K := K) (K' := K') pow β r e o hactive
    (PercLib.Percolation.Bond.ae_ne_top_encard_cluster_insert
      (law (intensityProfile (cutoffKernel N K r) β)) e o hfinU)
    (PercLib.Percolation.Bond.integrable_encard_cluster_insert_pow
      (law (intensityProfile (cutoffKernel N K r) β)) e o pow hfinU hintU)

open Classical in
/-- **The pair-summed closed-coordinate identity from unconditional per-vertex moments.**

Same replacement of the per-pair inserted-cluster inputs as
`cutoff_pivotal_eq_closed_pow_of_vertexMoments`, now for the summed form.  The remaining input of
Lemma I.4.1 described in `tsum_cutoff_pivotal_eq_closed_pow` (summability of the closed-coordinate
series) is unchanged. -/
theorem tsum_cutoff_pivotal_eq_closed_pow_of_vertexMoments {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (pow : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hfinU : ∀ y : Fin d → ℤ, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hintU : ∀ y : Fin d → ℤ, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow)
      (law (intensityProfile (cutoffKernel N K r) β))) :
    (∑' e, cw e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      ((β : ℝ) * -K' r) *
        ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  tsum_cutoff_pivotal_eq_closed_pow (K := K) (K' := K') pow β r o cw hcw
    (fun e => PercLib.Percolation.Bond.ae_ne_top_encard_cluster_insert
      (law (intensityProfile (cutoffKernel N K r) β)) e o hfinU)
    (fun e => PercLib.Percolation.Bond.integrable_encard_cluster_insert_pow
      (law (intensityProfile (cutoffKernel N K r) β)) e o pow hfinU hintU)


end PercLib.Models.LongRange

/-! ## Non-vacuity of the cap passage

On `Bool` with the Dirac law at the empty configuration the cap passage is a genuine convergence
with a non-zero limit: opening the pair `{false, true}` merges two singleton clusters, so the
closed-coordinate increment is `2 - 1 = 1`.  The pair is counted once, which is the normalisation
the closed-coordinate conditioning must produce. -/

namespace PercLib.Percolation.Bond

open Classical in
/-- The inserted cluster of `false` after opening the pair `{false, true}` in the empty
configuration is the whole two-point vertex set. -/
theorem bool_encard_cluster_insert_pair_eq_two :
    ((cluster (insert s(false, true) (∅ : Config Bool)) false).encard : ℝ≥0∞) = 2 := by
  have hcl : cluster ({s(false, true)} : Config Bool) false = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    cases y
    · exact mem_cluster_self _ _
    · rw [mem_cluster_iff]
      exact mem_conn_of_mem (by simp) (by simp)
  rw [show insert s(false, true) (∅ : Config Bool) = {s(false, true)} from by simp, hcl,
    Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, Fintype.card_bool]
  norm_num

open Classical in
/-- **Non-vacuity with a non-zero limit.** The Dirac law at the empty configuration satisfies the
hypotheses of `tendsto_integral_closed_pivotal_truncation` for the pair `{false, true}`, the root
`false` and the first moment. -/
theorem nonvacuous_tendsto_integral_closed_pivotal_truncation :
    Tendsto (fun n : ℕ => ∫ ω : Config Bool, (if s(false, true) ∈ ω then (0 : ℝ) else
        (min (n : ℝ≥0∞) (((cluster (insert s(false, true) ω) false).encard : ℝ≥0∞) ^ 1)).toReal -
          (min (n : ℝ≥0∞) (((cluster ω false).encard : ℝ≥0∞) ^ 1)).toReal)
        ∂(Measure.dirac (∅ : Config Bool)))
      atTop (𝓝 (∫ ω : Config Bool, (if s(false, true) ∈ ω then (0 : ℝ) else
        (((cluster (insert s(false, true) ω) false).encard : ℝ≥0∞).toReal) ^ 1 -
          (((cluster ω false).encard : ℝ≥0∞).toReal) ^ 1)
        ∂(Measure.dirac (∅ : Config Bool)))) := by
  have hfin : ∀ᵐ ω ∂(Measure.dirac (∅ : Config Bool)),
      ((cluster (insert s(false, true) ω) false).encard : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards with ω
    simpa using (Set.toFinite (cluster (insert s(false, true) ω) false))
  have hint : Integrable (fun ω : Config Bool =>
      (((cluster (insert s(false, true) ω) false).encard : ℝ≥0∞).toReal) ^ 1)
      (Measure.dirac (∅ : Config Bool)) := by
    refine Integrable.of_bound (C := 2) ((ENNReal.measurable_toReal.comp
      (measurable_encard_cluster_insert_coe s(false, true) false)).pow_const 1).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg ENNReal.toReal_nonneg 1)]
    simpa using PercLib.Models.LongRange.encard_cluster_insert_toReal_pow_le_card
      (V := Bool) s(false, true) false 1 ω
  exact tendsto_integral_closed_pivotal_truncation _ _ _ _ hfin hint

open Classical in
/-- The limit in `nonvacuous_tendsto_integral_closed_pivotal_truncation` is `1`, so the
convergence is not the trivial `0 → 0` and the closed-coordinate increment of a single pair is
counted once. -/
theorem nonvacuous_closed_pivotal_limit_eq_one :
    (∫ ω : Config Bool, (if s(false, true) ∈ ω then (0 : ℝ) else
      (((cluster (insert s(false, true) ω) false).encard : ℝ≥0∞).toReal) ^ 1 -
        (((cluster ω false).encard : ℝ≥0∞).toReal) ^ 1)
      ∂(Measure.dirac (∅ : Config Bool))) = 1 := by
  have hA := bool_encard_cluster_insert_pair_eq_two
  have hB : ((cluster (∅ : Config Bool) false).encard : ℝ≥0∞) = 1 := by
    rw [cluster_empty]
    simp
  rw [integral_dirac, Set.mem_empty_iff_false, ite_false, hA, hB]
  norm_num

end PercLib.Percolation.Bond


namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-! ### The per-pair closed-coordinate identity without an active-pair hypothesis -/

open Classical in
/-- **Per-pair closed-coordinate identity, radial weight kept.**

For every pair `e` (active or not), the cutoff Russo coefficient times the pivotal integral
of a bounded observable equals `β (-J'(r))` times the radial indicator of `e` times the
closed-coordinate integral of the same observable.  The `hactive` hypothesis of
`cutoff_pivotal_eq_closed` is not needed: on an inactive pair the radial weight and hence
the coefficient vanish, so both sides are `0` once the radial weight is written explicitly.

This is the per-pair input of the orientation step: the factor
`radialKernel N (fun s => if s < r then 1 else 0) e` on the right is exactly the paper's
`1(∥x - y∥ ≤ r)` for the pair `e = s(x, y)`. -/
theorem cutoff_pivotal_eq_closed_rad {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m) (β : ℝ≥0) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ) :
    ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      (β : ℝ) * -K' r * ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then 0 else F (cluster (insert e ω) o).encard -
          F (cluster ω o).encard)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) := by
  rcases radialKernel_indicator_eq_zero_or_one N r e with h0 | h1
  · rw [h0]; ring
  · have h := cutoff_pivotal_eq_closed (d := d) (N := N) (K := K) (K' := K') hFm β r e o
      (by rw [h1]; norm_num)
    rw [h1, one_mul] at h ⊢
    rw [h]
    ring

open Classical in
/-- **The pivotal flux series in closed coordinates.**

Summing the per-pair identity over all pairs: the pivotal `p`-th flux series of the cutoff
family is `β (-J'(r))` times the radially weighted closed-event flux series.  No
summability is needed for the identity itself (both sides are `tsum`s of the same family
up to the constant `β (-J'(r))`, and `tsum_congr` does not require summability).

The radial factor on the right is the `1(∥x - y∥ ≤ r)` of Russo's formula in the paper's
ordered presentation; this is the normalisation that turns the unordered pair sum into the
root-anchored sum over the ball. -/
theorem tsum_cutoff_pivotal_eq_closed {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m) (β : ℝ≥0) (r : ℝ)
    (o : Fin d → ℤ) (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) :
    (∑' e, cw r e *
        ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      (β : ℝ) * -K' r *
        ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then 0 else F (cluster (insert e ω) o).encard -
            F (cluster ω o).encard)
            ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  classical
  rw [← tsum_mul_left]
  exact tsum_congr fun e => by
    rw [hcw e]
    exact cutoff_pivotal_eq_closed_rad hFm β r e o
end PercLib.Models.LongRange


namespace PercLib.Models.LongRange
/-! ### Corner reconciliation: the strict radial indicator is the paper's closed ball -/

/-- **The derivative's radial indicator is the paper's ball indicator away from the corner.**

The cutoff derivative coefficient of `hasDerivAt_integral_cutoff_pow` carries the *strict*
indicator `1(N (y - x) < r)`, while the Russo formula of the paper and the compiled
`i41_massTransport` carry the *closed* ball `1(∥y - x∥ ≤ r)`.  Under the corner hypothesis
`hcorner` (no lattice displacement has norm exactly `r` on `(u, v)`) the two indicators agree.
This is the `strict`/`non-strict` normalisation that a real form of Lemma I.4.1 must fix. -/
theorem indicator_lt_eq_le {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (z : Fin d → ℤ) :
    (if N (Int.cast ∘ z) < r then (1 : ℝ≥0∞) else 0) =
      if N (Int.cast ∘ z) ≤ r then 1 else 0 := by
  have hne : N (Int.cast ∘ z) ≠ r := fun h => hcorner z (by rw [h]; exact hr)
  by_cases h : N (Int.cast ∘ z) < r
  · simp only [h, h.le, ite_true]
  · have hle : ¬ (N (Int.cast ∘ z) ≤ r) := fun hle => h (lt_of_le_of_ne hle hne)
    simp only [h, hle, ite_false]

/-- The real-valued form of the corner reconciliation, for the derivative coefficient. -/
theorem indicator_lt_eq_le_real {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (z : Fin d → ℤ) :
    (if N (Int.cast ∘ z) < r then (1 : ℝ) else 0) =
      if N (Int.cast ∘ z) ≤ r then 1 else 0 := by
  have hne : N (Int.cast ∘ z) ≠ r := fun h => hcorner z (by rw [h]; exact hr)
  by_cases h : N (Int.cast ∘ z) < r
  · simp only [h, h.le, ite_true]
  · have hle : ¬ (N (Int.cast ∘ z) ≤ r) := fun hle => h (lt_of_le_of_ne hle hne)
    simp only [h, hle, ite_false]

/-- **The radial indicator of a non-diagonal pair is the ball indicator.**

`radialKernel N (fun s => if s < r then 1 else 0) s(x, y) = 1(N (y - x) ≤ r)` for `x ≠ y`.
The diagonal is *not* covered: the loop convention of `radialKernel` sets it to `0` while the
ball indicator is `1`.  This is the loop asymmetry that any unordered/oriented comparison must
handle; in the ordered sum of Lemma I.4.1 the diagonal is nevertheless zero, because the
summand carries `1(y ∉ K_0)` and `x ∈ K_0` (see `indicator_not_mem_self`). -/
theorem radialKernel_indicator_eq_ball_of_ne {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) =
      if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0 := by
  rw [coe_radialKernel_of_ne (N := N) (K := fun s => if s < r then 1 else 0)
    (x := x) (y := y) hxy (by positivity)]
  have hNz : N (Int.cast ∘ (x - y)) = N (Int.cast ∘ (y - x)) := by
    rw [intCast_comp_sub, intCast_comp_sub, map_sub_rev]
  rw [hNz]
  exact indicator_lt_eq_le_real N hcorner hr _

open Classical in
/-- On the diagonal the ordered summand of Lemma I.4.1 vanishes: the factor `1(y ∉ K_0)`
with `y = x ∈ K_0` is zero.  Hence the loop convention of `radialKernel` (which is `0` on the
diagonal) and the ball indicator (which is `1` on the diagonal) give the same contribution to
the root-anchored sum. -/
theorem indicator_not_mem_self {d : ℕ} (ω : Config (Fin d → ℤ)) (x : Fin d → ℤ)
    (t : ℝ) :
    (if x ∈ cluster ω x then 0 else 1) * t = 0 := by
  simp [mem_cluster_self ω x]
end PercLib.Models.LongRange


namespace PercLib.Models.LongRange
/-! ### The pivotal `toReal` bridge and the uncapped closed-coordinate step -/

/-- **The `p`-th pivotal increment in real form.**

For finite inserted cluster and `B ≤ A`, the real number `(A^p - B^p).toReal` of the truncated
`ℝ≥0∞` subtraction is the honest real difference `A.toReal^p - B.toReal^p`.  This is the
pointwise bridge between the flux series of `hasDerivAt_integral_cutoff_pow` (which carries the
`ℝ≥0∞` subtraction) and the real closed-coordinate series of the paper's proof. -/
theorem toReal_pow_sub_pow {A B : ℝ≥0∞} (hBA : B ≤ A) (hA : A ≠ ⊤) (p : ℕ) :
    (A ^ p - B ^ p).toReal = A.toReal ^ p - B.toReal ^ p := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.pow_le_pow_left hBA) (ENNReal.pow_ne_top hA),
    ENNReal.toReal_pow, ENNReal.toReal_pow]

/-- The integral form of `toReal_pow_sub_pow`: the pivotal flux of
`hasDerivAt_integral_cutoff_pow` is the integral of the honest real difference of the
`p`-th powers of the two cluster volumes,
almost surely. -/
theorem integral_pivotal_pow_eq_real_sub {V : Type*} [Countable V]
    (μ : Measure (Config V)) (e : Sym2 V) (o : V) (p : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ =
      ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hfin] with ω hω
  exact toReal_pow_sub_pow (encard_cluster_sdiff_le_insert_coe ω e o) hω p

open Classical in
/-- **The uncapped closed-coordinate orientation step, from its real-difference form.**

The closed-coordinate form of the pivotal flux series follows from its real-difference form,
as supplied by `tsum_cutoff_pivotal_eq_closed_pow`.  The only input is the pointwise `toReal`
bridge above plus the a.e. finiteness of the inserted cluster.  No summability hypothesis is
needed: both
sides are `tsum`s of pointwise equal families. -/
theorem pivotal_flux_eq_closed_of_real {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hclosedPow : (∑' e, cw e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      (β : ℝ) * -K' r *
        ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
            ∂(law (intensityProfile (cutoffKernel N K r) β))) :
    (∑' e, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      (β : ℝ) * -K' r *
        ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
            ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  refine hclosedPow ▸ tsum_congr fun e => ?_
  rw [integral_pivotal_pow_eq_real_sub _ e o p (hfin e)]

end PercLib.Models.LongRange


namespace PercLib.Models.LongRange

/-! ### Summability of the closed-coordinate series from `hKd` -/

open Classical in
/-- **`hKd` makes the radially weighted closed-coordinate flux series summable.**

The summed closed-coordinate identity of Lemma I.4.1 is a `tsum`, and Lean's `tsum` is `0`
for a non-summable family, so a summed application needs summability of the radially weighted
closed-event flux.  The library's `hKd` bounds the *pivotal* flux, not this one, and no
library hypothesis mentions the closed-coordinate flux — but the two are proportional once the
per-pair closed rewrite holds: for every pair `e`

`radial(e) * closedflux(e) = (β (-K'(r)))⁻¹ * (cw(e) * pivotalflux(e))`,

so `∑_{e ∈ S} |radial(e) * closedflux(e)| ≤ |(β (-K'(r)))⁻¹| * Kd(r)` for every finite `S`.
Hence `hKd` plus the per-pair closed rewrite plus `β K'(r) ≠ 0` already give the summability
(and the explicit bound on the series) that a summed form of the paper's identity needs; no
further uniform-integrability hypothesis is required. -/
theorem summable_closed_flux_of_hKd {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd)
    (hpair : ∀ e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ((β : ℝ) * -K' r)⁻¹ * (cw e *
        ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β)))) :
    Summable (fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) ∧
      (∑' e, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
        |((β : ℝ) * -K' r)⁻¹| * Kd) := by
  have hstep : ∀ e, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| =
      |((β : ℝ) * -K' r)⁻¹| * (|cw e| *
        |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))|) := by
    intro e
    rw [hpair e, abs_mul, abs_mul]
  have hle : ∀ S : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ S, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
        |((β : ℝ) * -K' r)⁻¹| * Kd := by
    intro S
    have h1 : ∑ e ∈ S, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))| =
        |((β : ℝ) * -K' r)⁻¹| * ∑ e ∈ S, |cw e| *
          |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
            ∂(law (intensityProfile (cutoffKernel N K r) β))| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => hstep e
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hKd S) (abs_nonneg _)
  have hs : Summable fun e => |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| :=
    summable_of_sum_le (fun e => abs_nonneg _) hle
  exact ⟨summable_abs_iff.mp hs,
    Real.tsum_le_of_sum_le (fun e => abs_nonneg _) hle⟩

end PercLib.Models.LongRange



/-! ### Pointwise crossing-pair identities -/

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

variable {V : Type*}

/-! ### The four-case pointwise closed-event flux -/

open Classical in
/-- **Pointwise closed-event cluster flux through an arbitrary pair.**  For every configuration
`ω`, every pair `s(a, b)` and every observable `F : ℕ∞ → ℝ` of the cluster volume, the change of
`F (|K_o|)` when the pair is forced open, guarded by the closed-event indicator, is:

* `0` if both endpoints lie in `K_o`, or both lie outside `K_o`;
* `F (|K_o| + |K_b|) - F (|K_o|)` if `a ∈ K_o` and `b ∉ K_o`;
* `F (|K_o| + |K_a|) - F (|K_o|)` if `b ∈ K_o` and `a ∉ K_o`.

The volumes are `Set.encard`, so the statement covers infinite clusters as well; the deletion
`ω \ {s(a, b)}` is the one appearing in the Russo integrand, and the closed-event indicator
`1(s(a, b) ∉ ω)` is what makes it equal to the insertion increment at `ω`. -/
theorem rootFlux_pointwise (ω : Config V) (a b o : V) (F : ℕ∞ → ℝ) :
    (if s(a, b) ∈ ω then (0 : ℝ) else
        F (cluster (insert s(a, b) ω) o).encard - F (cluster (ω \ {s(a, b)}) o).encard) =
      if a ∈ cluster ω o then
        (if b ∈ cluster ω o then 0
         else F ((cluster ω o).encard + (cluster ω b).encard) - F (cluster ω o).encard)
      else
        (if b ∈ cluster ω o then
          F ((cluster ω o).encard + (cluster ω a).encard) - F (cluster ω o).encard
         else 0) := by
  classical
  by_cases hmem_a : a ∈ cluster ω o
  · by_cases hmem_b : b ∈ cluster ω o
    · by_cases he : s(a, b) ∈ ω
      · rw [ite_eq_left he, ite_eq_left hmem_a, ite_eq_left hmem_b]
      · rw [ite_eq_right he, ite_eq_left hmem_a, ite_eq_left hmem_b,
          cluster_insert_eq_of_mem_of_mem ((mem_cluster_comm ω o a).1 hmem_a)
            ((mem_cluster_comm ω o b).1 hmem_b),
          Set.sdiff_singleton_eq_self he, sub_self]
    · -- `a` inside the root cluster, `b` outside
      have hne : a ≠ b := fun h => hmem_b (h ▸ hmem_a)
      have he : s(a, b) ∉ ω := fun hmem =>
        hmem_b ((mem_cluster_iff ω o b).2
          (conn_trans ((mem_cluster_iff ω o a).1 hmem_a) (mem_conn_of_mem hne hmem)))
      have ha_eq : cluster ω a = cluster ω o :=
        (cluster_eq_iff_conn ω a o).2 (by
          rw [conn_symm]
          exact (mem_cluster_iff ω o a).1 hmem_a)
      have hdisj : Disjoint (cluster ω o) (cluster ω b) := by
        refine Set.disjoint_left.2 fun z hzo hzb => hmem_b ?_
        have hzy : ω ∈ conn z b := by
          rwa [mem_cluster_iff, conn_symm] at hzb
        exact conn_trans ((mem_cluster_iff ω o z).1 hzo) hzy
      have hunion : cluster (insert s(a, b) ω) o = cluster ω o ∪ cluster ω b := by
        rw [cluster_insert_of_mem ω a b o (Or.inl ((mem_cluster_comm ω o a).1 hmem_a)),
          ha_eq]
      rw [ite_eq_right he, ite_eq_left hmem_a, ite_eq_right hmem_b,
        Set.sdiff_singleton_eq_self he, hunion, Set.encard_union_eq hdisj]
  · by_cases hmem_b : b ∈ cluster ω o
    · -- `b` inside the root cluster, `a` outside (the mirror image)
      have hne : b ≠ a := fun h => hmem_a (h ▸ hmem_b)
      have he : s(a, b) ∉ ω := fun hmem => by
        have hmem' : s(b, a) ∈ ω := by rwa [Sym2.eq_swap]
        exact hmem_a ((mem_cluster_iff ω o a).2
          (conn_trans ((mem_cluster_iff ω o b).1 hmem_b) (mem_conn_of_mem hne hmem')))
      have hb_eq : cluster ω b = cluster ω o :=
        (cluster_eq_iff_conn ω b o).2 (by
          rw [conn_symm]
          exact (mem_cluster_iff ω o b).1 hmem_b)
      have hdisj : Disjoint (cluster ω o) (cluster ω a) := by
        refine Set.disjoint_left.2 fun z hzo hza => hmem_a ?_
        have hza' : ω ∈ conn z a := by
          rwa [mem_cluster_iff, conn_symm] at hza
        exact conn_trans ((mem_cluster_iff ω o z).1 hzo) hza'
      have hunion : cluster (insert s(a, b) ω) o = cluster ω o ∪ cluster ω a := by
        have h := cluster_insert_of_mem ω b a o (Or.inl ((mem_cluster_comm ω o b).1 hmem_b))
        rw [Sym2.eq_swap, hb_eq] at h
        exact h
      rw [ite_eq_right he, ite_eq_right hmem_a, ite_eq_left hmem_b,
        Set.sdiff_singleton_eq_self he, hunion, Set.encard_union_eq hdisj]
    · -- both endpoints outside the root cluster: forcing the pair open changes nothing
      have hpoint : ∀ x ∈ s(a, b), x ∉ cluster ω o := by
        intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact hmem_a
        · exact hmem_b
      by_cases he : s(a, b) ∈ ω
      · rw [ite_eq_left he, ite_eq_right hmem_a, ite_eq_right hmem_b]
      · rw [ite_eq_right he, ite_eq_right hmem_a, ite_eq_right hmem_b,
          cluster_insert_eq_cluster_sdiff_of_forall_not_mem hpoint, sub_self]

open Classical in
/-- **Pointwise closed-event flux through a pair incident to the root.**  Specializing
`rootFlux_pointwise` to `a = o` gives the pointwise shape of Lemma I.4.1: the change of the
root observable through `s(o, y)` is zero when `o` and `y` are already connected, and otherwise
the merge increment `F (|K_o| + |K_y|) - F (|K_o|)`.  No hypothesis on `y` (in particular none
`y ≠ o`) is needed: at `y = o` both sides are `0`. -/
theorem rootFlux_pointwise_root (ω : Config V) (o y : V) (F : ℕ∞ → ℝ) :
    (if s(o, y) ∈ ω then (0 : ℝ) else
        F (cluster (insert s(o, y) ω) o).encard - F (cluster (ω \ {s(o, y)}) o).encard) =
      if ω ∈ conn o y then 0
      else F ((cluster ω o).encard + (cluster ω y).encard) - F (cluster ω o).encard := by
  classical
  have h := rootFlux_pointwise ω o y o F
  simp only [mem_cluster_self, ↓reduceIte] at h
  rw [h]
  simp only [mem_cluster_iff]

open Classical in
/-- At `y = o` the root identity is the tautology `0 = 0`: the diagonal pair carries no cluster
flux.  (Its cutoff weight also vanishes, `radialKernel_diag`; the two facts are independent.) -/
theorem rootFlux_pointwise_root_diag (ω : Config V) (o : V) (F : ℕ∞ → ℝ) :
    (if s(o, o) ∈ ω then (0 : ℝ) else
        F (cluster (insert s(o, o) ω) o).encard - F (cluster (ω \ {s(o, o)}) o).encard) = 0 := by
  classical
  rw [rootFlux_pointwise_root]
  simp [conn_self]

/-! ### Integration and closed-coordinate conditioning -/

open Classical in
/-- **Integral form of the pointwise root identity.**  For an arbitrary bond law the two
integrands are pointwise equal, so the integrals agree; no measurability, boundedness or
integrability hypothesis is needed for the identity itself. -/
theorem rootFlux_integral_root (q : Sym2 V → unitInterval) (o y : V) (F : ℕ∞ → ℝ) :
    ∫ ω, (if s(o, y) ∈ ω then (0 : ℝ) else
        F (cluster (insert s(o, y) ω) o).encard - F (cluster (ω \ {s(o, y)}) o).encard)
        ∂law q =
      ∫ ω, (if ω ∈ conn o y then (0 : ℝ)
        else F ((cluster ω o).encard + (cluster ω y).encard) - F (cluster ω o).encard)
        ∂law q :=
  integral_congr_ae (Filter.Eventually.of_forall fun ω => rootFlux_pointwise_root ω o y F)

open Classical in
/-- **Integral form of the root identity in the closed-event notation.**  The Russo integrand
deletes `s(o, y)` from `ω`; on the closed event `s(o, y) ∉ ω` the deletion is the identity, so
the integral against the closed-event indicator is the same as the integral of the deletion
form. -/
theorem rootFlux_integral_root_closed (q : Sym2 V → unitInterval) (o y : V) (F : ℕ∞ → ℝ) :
    ∫ ω, (if s(o, y) ∈ ω then (0 : ℝ) else
        F (cluster (insert s(o, y) ω) o).encard - F (cluster ω o).encard) ∂law q =
      ∫ ω, (if ω ∈ conn o y then (0 : ℝ)
        else F ((cluster ω o).encard + (cluster ω y).encard) - F (cluster ω o).encard)
        ∂law q := by
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans
    (rootFlux_integral_root q o y F)
  by_cases he : s(o, y) ∈ ω
  · rw [ite_eq_left he, ite_eq_left he]
  · rw [ite_eq_right he, ite_eq_right he, Set.sdiff_singleton_eq_self he]

open Classical in
/-- **Closed-coordinate form of the root flux for a bounded observable.**  For an arbitrary bond
law `q`, pair `s(o, y)` and bounded observable `F` of the cluster volume, the conditional
closed integral `(1 - q e) * ∫ (G (ω ∪ {e}) - G (ω \ {e}))` equals the oriented Lemma-I.4.1
integrand `∫ 1(o ↮ y) * (F (|K_o| + |K_y|) - F (|K_o|))`.

This is `one_sub_mul_integral_insert_sub_basic` with the pointwise root identity substituted on
the right; the radial cutoff factor and its active-pair hypothesis are not involved. -/
theorem rootFlux_one_sub_mul_integral [Countable V] (q : Sym2 V → unitInterval) (o y : V)
    {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m) :
    (1 - (q (s(o, y)) : ℝ)) *
        ∫ ω, (F (cluster (insert s(o, y) ω) o).encard -
          F (cluster (ω \ {s(o, y)}) o).encard) ∂law q =
      ∫ ω, (if ω ∈ conn o y then (0 : ℝ)
        else F ((cluster ω o).encard + (cluster ω y).encard) - F (cluster ω o).encard)
        ∂law q := by
  have hG : Measurable (fun ω : Config V => F (cluster ω o).encard) :=
    (measurable_of_countable F).comp (measurable_encard_cluster o)
  have hGm : ∀ ω : Config V, |F (cluster ω o).encard| ≤ m := fun ω => hFm _
  have h := one_sub_mul_integral_insert_sub_basic q (s(o, y))
    (fun ω : Config V => F (cluster ω o).encard) hG hGm
  simp only [law] at h ⊢
  rw [h]
  simpa only [law] using rootFlux_integral_root_closed q o y F

end PercLib.Models.LongRange


namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

variable {V : Type*}

/-! ### The boundary decomposition over the root cluster -/

open Classical in
/-- **Pointwise boundary decomposition of the pivotal edge sum over the root cluster.**  Let
`X` be a finite set of vertices *inside* the cluster of `o` and `Y` a finite set of vertices
*outside* it.  Then the pair-weighted pivotal flux of the edges `{x, y}` (`x ∈ X`, `y ∈ Y`)
equals the sum over the outside endpoints `y` of the total weight `∑_{x ∈ X} c (x, y)` times the
merge increment `F (|K_o| + |K_y|) - F (|K_o|)`.

This is the pointwise content of the mass-transport step of Lemma I.4.1: the inside endpoint
does not enter the increment, so summing over the inside vertices produces exactly the factor
`∑_{x ∈ K_o} c (x, y)` multiplying the root-anchored increment, and at a translation-invariant
law that factor is what becomes `|K_o|` times the root weight.  Edges leaving `K_o` are the only
ones with a nonzero pivotal increment (`rootFlux_pointwise`). -/
theorem rootFlux_sum_product_eq_oriented (ω : Config V) (o : V) (X Y : Finset V)
    (hX : ∀ x ∈ X, x ∈ cluster ω o) (hY : ∀ y ∈ Y, y ∉ cluster ω o)
    (F : ℕ∞ → ℝ) (c : Sym2 V → ℝ) :
    ∑ p ∈ X ×ˢ Y,
        c (s(p.1, p.2)) * (if s(p.1, p.2) ∈ ω then (0 : ℝ) else
          F (cluster (insert s(p.1, p.2) ω) o).encard -
            F (cluster (ω \ {s(p.1, p.2)}) o).encard) =
      ∑ y ∈ Y, (∑ x ∈ X, c (s(x, y))) *
        (F ((cluster ω o).encard + (cluster ω y).encard) - F (cluster ω o).encard) := by
  classical
  rw [Finset.sum_product]
  have hterm : ∀ x ∈ X, ∀ y ∈ Y,
      c (s(x, y)) * (if s(x, y) ∈ ω then (0 : ℝ) else
          F (cluster (insert s(x, y) ω) o).encard -
            F (cluster (ω \ {s(x, y)}) o).encard) =
        c (s(x, y)) *
          (F ((cluster ω o).encard + (cluster ω y).encard) - F (cluster ω o).encard) := by
    intro x hx y hy
    rw [rootFlux_pointwise, ite_eq_left (hX x hx), ite_eq_right (hY y hy)]
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hterm x hx y hy,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]

open Classical in
/-- **No double counting in the boundary decomposition.**  With `X` inside the root cluster and
`Y` outside it, the map `(x, y) ↦ s(x, y)` is injective on `X × Y`: an ordered pair of vertices
of the product corresponds to exactly one unordered edge, so the boundary sum really is an edge
sum and not twice one. -/
theorem rootFlux_product_pair_injective (ω : Config V) (o : V) (X Y : Finset V)
    (hX : ∀ x ∈ X, x ∈ cluster ω o) (hY : ∀ y ∈ Y, y ∉ cluster ω o) :
    ∀ p ∈ X ×ˢ Y, ∀ q ∈ X ×ˢ Y, s(p.1, p.2) = s(q.1, q.2) → p = q := by
  classical
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq h
  simp only [Finset.mem_product] at hp hq
  obtain ⟨hxX, hyY⟩ := hp
  obtain ⟨hx'X, hy'Y⟩ := hq
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : x = x' := h1
    have h2' : y = y' := h2
    rw [h1', h2']
  · exfalso
    have h2' : y = x' := h2
    exact hY y hyY (h2' ▸ hX x' hx'X)


end PercLib.Models.LongRange


/-! ### Finite-cardinality bridges for real-valued moments -/

namespace PercLib.Percolation.Bond

section Cardinality

variable {V : Type*}

/-- **The `ℝ`-valued cluster volume is the `ncard` volume.**  For every set `s`,
`((s.encard : ℝ≥0∞)).toReal = s.ncard`.  When `s` is infinite both sides are `0`: `encard`
is `⊤`, whose `toReal` is `0`, and `ncard` has junk value `0`.  Consequently any real-valued
identity phrased through `toReal ∘ encard` carries no information on infinite clusters. -/
theorem toReal_encard_eq_ncard (s : Set V) : ((s.encard : ℝ≥0∞)).toReal = (s.ncard : ℝ) := by
  by_cases h : s.Finite
  · rw [← h.cast_ncard_eq, ENat.toENNReal_coe, ENNReal.toReal_natCast]
  · have hinf : s.Infinite := h
    rw [hinf.encard_eq, hinf.ncard, ENat.toENNReal_top, ENNReal.toReal_top, Nat.cast_zero]

/-- The cluster instance of `toReal_encard_eq_ncard`, in the shape used by the derivative. -/
theorem toReal_encard_cluster_eq_ncard (ω : Config V) (o : V) :
    ((cluster ω o).encard : ℝ≥0∞).toReal = ((cluster ω o).ncard : ℝ) :=
  toReal_encard_eq_ncard _

end Cardinality

section Binomial

/-- **Real form of the merge increment, under explicit finiteness.**  If both cluster volumes
are finite, the `ℝ≥0∞` truncated difference `(A+B)^p − A^p` casts to the honest real
difference `(A+B)^p − A^p`. -/
theorem pow_add_sub_pow_toReal {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (p : ℕ) :
    ((A + B) ^ p - A ^ p).toReal = (A.toReal + B.toReal) ^ p - A.toReal ^ p := by
  have hAB : A + B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hA, hB⟩
  rw [ENNReal.toReal_sub_of_le (pow_le_pow_left' (le_add_right le_rfl) p)
      (ENNReal.pow_ne_top hAB),
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_add hA hB]

/-- **The `toReal` of the `ℝ≥0∞` binomial sum.**  Under finiteness of `A` and `B`, the cast of
the expansion `∑_{ℓ<p} C(p,ℓ) A^ℓ B^{p−ℓ}` is the paper's real binomial sum. -/
theorem toReal_sum_choose {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (p : ℕ) :
    (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * A ^ ℓ * B ^ (p - ℓ)).toReal =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * A.toReal ^ ℓ * B.toReal ^ (p - ℓ) := by
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_natCast]
  · intro ℓ _
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top (p.choose ℓ)) (ENNReal.pow_ne_top hA))
      (ENNReal.pow_ne_top hB)

/-- The mass-transported shape of the binomial sum, with the root-cluster factor
`A^{ℓ+1}` of Lemma I.4.1. -/
theorem toReal_sum_choose_succ {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (p : ℕ) :
    (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) * B ^ (p - ℓ)).toReal =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * A.toReal ^ (ℓ + 1) * B.toReal ^ (p - ℓ) := by
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_natCast]
  · intro ℓ _
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top (p.choose ℓ)) (ENNReal.pow_ne_top hA))
      (ENNReal.pow_ne_top hB)

/-- **The `ℝ`/`ℝ≥0∞` moment bridge.**  Under a.e. finiteness, the real integral of the cast of an
`ℝ≥0∞`-valued function is the cast of its `ℝ≥0∞` integral.  This is the passage from the
library's `ℝ≥0∞` moments and pivotal fluxes to the paper's real expectations; the a.e. finiteness
is the `hfin` input of `i41_binomial`, and it is not removable. -/
theorem integral_toReal_eq_toReal_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hmeas : AEMeasurable f μ) (hfin : ∀ᵐ a ∂μ, f a ≠ ⊤) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal :=
  MeasureTheory.integral_toReal hmeas
    (by filter_upwards [hfin] with a ha; exact lt_top_iff_ne_top.2 ha)

/-- **The paper's mass-transported summand, in real form, under finiteness.**  The cast of the
`ℝ≥0∞` product `A ((A+B)^p − A^p)` is `∑_{ℓ<p} C(p,ℓ) A^{ℓ+1} B^{p−ℓ}` in `ℝ`. -/
theorem mul_pow_add_sub_pow_toReal_sum {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (p : ℕ) :
    (A * ((A + B) ^ p - A ^ p)).toReal =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * A.toReal ^ (ℓ + 1) * B.toReal ^ (p - ℓ) := by
  rw [ENNReal.toReal_mul, pow_add_sub_pow_toReal hA hB p,
    PercLib.Probability.mul_pow_sub_pow_eq_sum_choose]

end Binomial

section ModelBridge

variable {V : Type*}

open Classical in
/-- **The real per-edge pivotal flux in the exact binomial shape of Lemma I.4.1.**  If the root
cluster after opening `s(o,y)` and the far cluster of `y` after deleting it are both finite, the
`ℝ`-valued pivotal flux of the edge `s(o,y)`, i.e. the cast of
`|K_o^{(insert)}|^p − |K_o^{(delete)}|^p`, is the paper's real sum
`∑_{ℓ<p} C(p,ℓ) |K_o|^{ℓ} |K_y|^{p−ℓ}` off the connection event, and `0` on it.

The finiteness hypotheses are explicit and necessary: `real_pivotal_eq_zero_of_cluster_eq_top`
shows that with an infinite root cluster the same cast is `0` while the honest increment is
infinite. -/
theorem pivotal_flux_toReal_eq_sum_choose (ω : Config V) (o y : V) (p : ℕ)
    (hX : ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hB : ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞) ≠ ⊤) :
    ((((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p).toReal) =
      if (ω \ {s(o, y)}) ∈ conn o y then 0
      else ∑ ℓ ∈ Finset.range p,
        (p.choose ℓ : ℝ) *
          ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal ^ ℓ *
          ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞).toReal ^ (p - ℓ) := by
  have hA : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top hX (encard_cluster_sdiff_le_insert_coe ω (s(o, y)) o)
  have hpiv := encard_cluster_insert_pow_sub_sdiff_eq ω o y p
  rw [hpiv]
  by_cases h : (ω \ {s(o, y)}) ∈ conn o y
  · simp only [h, ↓reduceIte, ENNReal.toReal_zero]
  · simp only [h, ↓reduceIte]
    rw [pow_add_sub_pow_toReal hA hB p,
      ← PercLib.Probability.sum_choose_mul_pow_eq_pow_sub]

open Classical in
/-- The mass-transported version: with the root-cluster factor `|K_o|` and the edge closed off
the connection event, the real flux is exactly the `A^{ℓ+1}` binomial sum of Lemma I.4.1. -/
theorem mul_pivotal_flux_toReal_eq_sum_choose (ω : Config V) (o y : V) (p : ℕ)
    (hX : ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hB : ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞) ≠ ⊤)
    (hdis : (ω \ {s(o, y)}) ∉ conn o y) :
    ((((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) *
        (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p)).toReal) =
      ∑ ℓ ∈ Finset.range p,
        (p.choose ℓ : ℝ) *
          ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal ^ (ℓ + 1) *
          ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞).toReal ^ (p - ℓ) := by
  have hA : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top hX (encard_cluster_sdiff_le_insert_coe ω (s(o, y)) o)
  have hpiv := encard_cluster_insert_pow_sub_sdiff_eq ω o y p
  rw [hpiv, ite_eq_right (by simpa using hdis)]
  exact mul_pow_add_sub_pow_toReal_sum hA hB p

/-- **The `ℝ`-valued pivotal flux vanishes identically on an infinite root cluster.**  Both
cluster volumes being `⊤`, the truncated `ℝ≥0∞` difference of the `p`-th powers is `0`, hence so
is its cast, for every `p`.  This is the reason the finiteness inputs of
`pivotal_flux_toReal_eq_sum_choose` and of the derivative interfaces cannot be dropped. -/
theorem real_pivotal_eq_zero_of_cluster_eq_top (ω : Config V) (e : Sym2 V) (o : V) (p : ℕ)
    (hA : ((cluster (insert e ω) o).encard : ℝ≥0∞) = ⊤)
    (hB : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) = ⊤) :
    ((((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal) = 0 := by
  rw [hA, hB, tsub_self, ENNReal.toReal_zero]

end ModelBridge

end PercLib.Percolation.Bond

/-! ### The cutoff diagram and a summability consequence -/

open Filter
open scoped Topology unitInterval

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

variable {d : ℕ}

/-! ## The coefficient: rate times the closed probability -/

/-- **The edge rate of the continuous cut-off family.**  Away from the corner
`r = N (x - y)`, the derivative in the scale of the edge probability `q_r(e)` of
`intensityProfile (cutoffKernel N K r) β` is

  `1{N(e) < r} * (1 - q_r(e)) * (β * -K' r)`,

that is the paper's rate `β |J'(r)| 1(‖x - y‖ ≤ r)` multiplied by the probability that the edge
is closed.  Equivalently it is `1{N(e) < r} * β * (-K' r) * exp (-(β) * J_r(e))`, the defining
equation `hcw` of `hKd_cutoff_of_summable_indicator_moment`.

Recording the identity in the `(1 - q)` form makes explicit that the exponential factor is the
closed probability: it cannot be dropped, and after the closed-coordinate conversion of
`cutoff_pivotal_eq_closed` it must not be kept either.  The indicator is the library's
`radialKernel` of `1_{(·) < r}`; it equals one on a short non-diagonal pair and zero otherwise. -/
theorem diagram_pairProb_deriv_eq_closedProb_mul_rate
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (β : ℝ≥0) {r : ℝ} (hr : 0 < r) (e : Sym2 (Fin d → ℤ))
    (hre : ∀ x y, e = s(x, y) → r ≠ N (Int.cast ∘ (x - y))) :
    HasDerivAt (fun s => (intensityProfile (cutoffKernel N K s) β e : ℝ))
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((1 - (intensityProfile (cutoffKernel N K r) β e : ℝ)) * ((β : ℝ) * -K' r))) r := by
  have h := hasDerivAt_cutoff_prob (N := N) hKa hK' β hr e hre
  refine h.congr_deriv ?_
  have hq : (1 : ℝ) - (intensityProfile (cutoffKernel N K r) β e : ℝ) =
      Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) := by
    change 1 - (1 - Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))) = _
    ring
  rw [hq]
  ring

/-- **The activation check.**  The closed probability factor is a genuine loss: whenever the
edge is open with positive probability and the rate `c = β * -K' r` is positive, the true
increment `(1 - q) * c` is strictly smaller than `c`.  A coefficient `β |J'(r)|` used without
this factor therefore overcounts exactly the configurations in which the edge is already open. -/
theorem diagram_closedProb_mul_rate_lt {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    (1 - q) * c < c := by
  have : (1 - q) * c = c - q * c := by ring
  rw [this]
  have : 0 < q * c := mul_pos hq hc
  linarith

/-! ## The quantitative diagram: finitely many short vectors, infinitely many short pairs -/

/-- The paper's ball is finite when stored as a set of *difference vectors*: only finitely many
nonzero lattice vectors have norm below `r`. -/
theorem diagram_finite_short_vectors (N : ModelNorm (Fin d → ℝ)) (r : ℝ) :
    ({z : Fin d → ℤ | z ≠ 0 ∧ N (Int.cast ∘ z) < r}).Finite :=
  finite_norm_lt N r

/-- Every pair of the family `{n • z + z, n • z}` has difference vector `z`, hence is short. -/
theorem diagram_short_pair_diff {z : Fin d → ℤ} (n : ℕ) :
    (n • z + z) - n • z = z := by
  abel

/-- The radial indicator `1{N(e) < r}` equals `1` on every pair of the family
`{n • z + z, n • z}` of short differences. -/
theorem diagram_indicator_family_eq_one {N : ModelNorm (Fin d → ℝ)} {z : Fin d → ℤ}
    (hz : z ≠ 0) {r : ℝ} (hzr : N (Int.cast ∘ z) < r) (n : ℕ) :
    (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) = 1 := by
  have hne : n • z + z ≠ n • z := by
    intro h
    refine hz ?_
    have h' := congrArg (fun t => t - n • z) h
    simpa using h'
  rw [coe_radialKernel_of_ne (N := N) (K := fun s => if s < r then 1 else 0)
    (x := n • z + z) (y := n • z) (hne) (by positivity), diagram_short_pair_diff]
  simp [hzr]

/-- **Infinitely many pairs at one short distance.**  For any nonzero `z` with `N z < r`, the
pairs `{n • z + z, n • z}` are pairwise distinct and all have difference `z`, hence ball radius
below `r`.  Consequently the library's sum over `Sym2 (Fin d → ℤ)` is a sum over infinitely many
pairs of the same length, whereas the paper's `∑_{y ∈ B_r}` is a finite sum: the two can only be
identified after the mass transport of `i41_massTransport`, never term by term. -/
theorem diagram_infinite_short_pairs {N : ModelNorm (Fin d → ℝ)} {z : Fin d → ℤ}
    (hz : z ≠ 0) {r : ℝ} (hzr : N (Int.cast ∘ z) < r) :
    {e : Sym2 (Fin d → ℤ) |
      ∃ x y : Fin d → ℤ, e = s(x, y) ∧ N (Int.cast ∘ (x - y)) < r}.Infinite := by
  refine (Set.infinite_range_of_injective (injective_pair_succ_nsmul hz)).mono ?_
  rintro e ⟨n, rfl⟩
  exact ⟨n • z + z, n • z, rfl, by rw [diagram_short_pair_diff]; exact hzr⟩


/-! ## The inserted-moment route to `hKd` is vacuous in infinite volume -/

open Classical in
/-- **Abstract obstruction: the radial-weighted diagram cannot converge over a short-pair family.**
If a majorant `m` is at least `1` on the pairs `{n • z + z, n • z}` of a single short
length, then `e ↦ 1{N(e) < r} * m e` is not summable.

This is the quantitative-diagram fact behind
`diagram_not_summable_indicator_inserted_moment`, stated without any reference to moments: the
`Sym2` sum of `hKd` / `dominator_cutoff_of_summable_indicator_moment` can only converge if the
majorant *decays* along every fixed short length (equivalently, in the position of the pair
relative to the root).  Any majorant that is bounded below by a positive constant on a short-pair
family — in particular any per-vertex moment bound — is therefore unusable, however small the
constant. -/
theorem diagram_not_summable_indicator_of_one_le_on_short
    (N : ModelNorm (Fin d → ℝ)) {r : ℝ} {z : Fin d → ℤ} (hz : z ≠ 0)
    (hzr : N (Int.cast ∘ z) < r) {m : Sym2 (Fin d → ℤ) → ℝ}
    (h1 : ∀ n : ℕ, 1 ≤ m (s(n • z + z, n • z))) :
    ¬ Summable fun e : Sym2 (Fin d → ℤ) =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * m e := by
  intro hsum
  have hcomp : Summable fun n : ℕ =>
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) *
        m (s(n • z + z, n • z)) :=
    hsum.comp_injective (injective_pair_succ_nsmul hz)
  have hone : Summable fun _ : ℕ => (1 : ℝ) := by
    refine hcomp.of_nonneg_of_le (fun n => zero_le_one) (fun n => ?_)
    rw [diagram_indicator_family_eq_one hz hzr n, one_mul]
    exact h1 n
  have hfin' : (Set.univ : Set ℕ).Finite :=
    Set.Finite.of_summable_const (b := (1 : ℝ)) one_pos (by simpa using hone)
  exact Set.infinite_univ hfin'



open Classical in
/-- **The inserted-moment weighted diagram diverges.**  For any nonzero `z` with `N z < r`, the
pairs `{n • z + z, n • z}` all have the same short difference, so the radial indicator is `1` on
all of them, while the inserted `p`-th moment
`∫ |K_o(ω ∪ {n • z + z, n • z})|^p` is at least `1` for every `n`: the cluster of `o` contains
`o`, and inserting an edge only enlarges it.  Consequently

  `∑'_e 1{N(e) < r} * ∫ |K_o(ω ∪ e)|^p`

diverges in `ℝ`.  The hypotheses are the two inputs that
`dominator_cutoff_of_summable_indicator_insertedMoment` needs for the inserted moment (a.e.
finiteness of the inserted cluster and its integrability), so the `hsum` hypothesis of that
theorem is **unsatisfiable** for the actual cut-off family: the inserted-moment dominator cannot
be used to discharge `hKd` in infinite volume.

The repair is not an algebraic one.  `diagram_summable_closed_flux_of_hKd` below shows that
`hKd` is precisely a decay statement for the *actual* pivotal flux `Q e`, which the inserted
moment does not see. -/
theorem diagram_not_summable_indicator_inserted_moment
    (N : ModelNorm (Fin d → ℝ)) (K : ℝ → ℝ) (β : ℝ≥0) {r : ℝ}
    (o : Fin d → ℤ) (pow : ℕ)
    {z : Fin d → ℤ} (hz : z ≠ 0) (hzr : N (Int.cast ∘ z) < r)
    (hfin : ∀ e : Sym2 (Fin d → ℤ),
      ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable
      (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (intensityProfile (cutoffKernel N K r) β))) :
    ¬ Summable fun e : Sym2 (Fin d → ℤ) =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  intro hsum
  have hne : ∀ n : ℕ, n • z + z ≠ n • z := by
    intro n h
    refine hz ?_
    have h' := congrArg (fun t => t - n • z) h
    simpa using h'
  -- the radial indicator is `1` along the family
  have hind : ∀ n : ℕ,
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) = 1 :=
    fun n => diagram_indicator_family_eq_one hz hzr n
  -- the inserted moment is at least `1`
  have hbig : ∀ e : Sym2 (Fin d → ℤ),
      1 ≤ ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
        ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
    intro e
    have hpt : ∀ ω : Config (Fin d → ℤ), ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ →
        (1 : ℝ) ≤ (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
      intro ω hω
      have h1 : ((1 : ℕ∞) : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) := by
        exact_mod_cast Set.one_le_encard_iff_nonempty.mpr ⟨o, mem_cluster_self (insert e ω) o⟩
      have h2 : (1 : ℝ) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal := by
        have := ENNReal.toReal_mono hω (by simpa using h1)
        simpa using this
      calc (1 : ℝ) = (1 : ℝ) ^ pow := (one_pow pow).symm
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 pow
    calc (1 : ℝ) = ∫ _ω : Config (Fin d → ℤ), (1 : ℝ)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by simp
      _ ≤ ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
            ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
        integral_mono_ae (integrable_const (1 : ℝ)) (hint e) (by
          filter_upwards [hfin e] with ω hω
          exact hpt ω hω)
  have hcomp : Summable fun n : ℕ =>
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ) *
        ∫ ω, (((cluster (insert s(n • z + z, n • z) ω) o).encard : ℝ≥0∞).toReal) ^ pow
          ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
    hsum.comp_injective (injective_pair_succ_nsmul hz)
  have hone : Summable fun _ : ℕ => (1 : ℝ) := by
    refine hcomp.of_nonneg_of_le (fun n => zero_le_one) (fun n => ?_)
    rw [hind n, one_mul]
    exact hbig _
  have hfin' : (Set.univ : Set ℕ).Finite :=
    Set.Finite.of_summable_const (b := (1 : ℝ)) one_pos (by simpa using hone)
  exact Set.infinite_univ hfin'

open Classical in
/-- **The same divergence in `ℝ≥0∞`, with no finiteness or integrability hypothesis.**  The
weighted `ℝ≥0∞` inserted-moment diagram is `⊤` as soon as the ball of radius `r` contains a
nonzero lattice vector.  This is the unconditional form of the previous theorem: it does not even
need the clusters to be finite, because `encard` is compared in `ℝ≥0∞`. -/
theorem diagram_tsum_indicator_inserted_moment_eq_top
    (N : ModelNorm (Fin d → ℝ)) (K : ℝ → ℝ) (β : ℝ≥0) {r : ℝ}
    (o : Fin d → ℤ) (pow : ℕ)
    {z : Fin d → ℤ} (hz : z ≠ 0) (hzr : N (Int.cast ∘ z) < r) :
    (∑' e : Sym2 (Fin d → ℤ),
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
        ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) = ⊤ := by
  have hne : ∀ n : ℕ, n • z + z ≠ n • z := by
    intro n h
    refine hz ?_
    have h' := congrArg (fun t => t - n • z) h
    simpa using h'
  have hind : ∀ n : ℕ,
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ≥0∞) = 1 := by
    intro n
    have h : ((radialKernel N (fun s => if s < r then 1 else 0)
        (s(n • z + z, n • z)) : ℝ≥0)) = 1 :=
      NNReal.coe_inj.mp (diagram_indicator_family_eq_one hz hzr n)
    rw [h]
    simp
  have hbig : ∀ e : Sym2 (Fin d → ℤ),
      (1 : ℝ≥0∞) ≤ ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
    intro e
    have h1 : ∀ ω : Config (Fin d → ℤ),
        (1 : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) := by
      intro ω
      have := Set.one_le_encard_iff_nonempty.mpr ⟨o, mem_cluster_self (insert e ω) o⟩
      exact_mod_cast this
    calc (1 : ℝ≥0∞) = ∫⁻ _ω : Config (Fin d → ℤ), (1 : ℝ≥0∞)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by simp
      _ ≤ ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
        lintegral_mono (fun ω => one_le_pow₀ (h1 ω))
  have hterm : ∀ n : ℕ, (1 : ℝ≥0∞) ≤
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ≥0∞) *
        ∫⁻ ω, (((cluster (insert s(n • z + z, n • z) ω) o).encard : ℝ≥0∞) ^ pow)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
    intro n
    rw [hind n, one_mul]
    exact hbig _
  have hcomp : (∑' n : ℕ,
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ≥0∞) *
        ∫⁻ ω, (((cluster (insert s(n • z + z, n • z) ω) o).encard : ℝ≥0∞) ^ pow)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) = ⊤ := by
    have hN : ∀ n : ℕ, (n : ℝ≥0∞) ≤ (∑' m : ℕ,
        (radialKernel N (fun s => if s < r then 1 else 0) (s(m • z + z, m • z)) : ℝ≥0∞) *
          ∫⁻ ω, (((cluster (insert s(m • z + z, m • z) ω) o).encard : ℝ≥0∞) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K r) β))) := by
      intro n
      have hle : (n : ℝ≥0∞) = ∑ m ∈ Finset.range n, (1 : ℝ≥0∞) := by simp
      rw [hle]
      exact ENNReal.summable.sum_le_tsum (Finset.range n) (fun m _ => zero_le)
        |>.trans' (Finset.sum_le_sum (fun m _ => hterm m))
    refine le_antisymm le_top ?_
    calc (⊤ : ℝ≥0∞) = ⨆ n : ℕ, (n : ℝ≥0∞) := (ENNReal.iSup_natCast).symm
      _ ≤ _ := iSup_le hN
  have hle : (∑' n : ℕ,
      (radialKernel N (fun s => if s < r then 1 else 0) (s(n • z + z, n • z)) : ℝ≥0∞) *
        ∫⁻ ω, (((cluster (insert s(n • z + z, n • z) ω) o).encard : ℝ≥0∞) ^ pow)
          ∂(law (intensityProfile (cutoffKernel N K r) β)))
      ≤ ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
          ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
    ENNReal.tsum_comp_le_tsum_of_injective (injective_pair_succ_nsmul hz)
      (fun e : Sym2 (Fin d → ℤ) =>
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
          ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K r) β)))
  rw [hcomp] at hle
  exact top_le_iff.mp hle

/-! ## `hKd` is exactly summability of the closed flux -/

open Classical in
/-- **`hKd` forces summability of the closed flux.**  With `J_r = cutoffKernel N K r` and
`ind = 1{N(e) < r}`, the defining equation of the cut-off weight reads
`|cw e| = β * |K' r| * ind e * exp (-(β) * J_r(e))`.  Hence, whenever `β > 0` and `K' r ≠ 0`, a
dominator `hKd` for the weighted pivotal flux

  `∑_{e ∈ S} |cw e| * |Q e| ≤ Kd`

is *the same thing as* summability of the closed flux
`e ↦ ind e * exp (-(β) * J_r(e)) * |Q e|`.  In particular `hKd` is a decay statement for the
actual pivotal flux `Q`, not a moment bound: the exponential factor is the probability that the
edge is closed, and it is part of the object being summed. -/
theorem diagram_summable_closed_flux_of_hKd
    (N : ModelNorm (Fin d → ℝ)) (K K' : ℝ → ℝ) {β : ℝ≥0} {r : ℝ}
    {cw Q : Sym2 (Fin d → ℤ) → ℝ}
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hβ : 0 < (β : ℝ)) (hK' : K' r ≠ 0) {Kd : ℝ}
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| * |Q e| ≤ Kd) :
    Summable fun e : Sym2 (Fin d → ℤ) =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| := by
  set F : Sym2 (Fin d → ℤ) → ℝ := fun e =>
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| with hF
  have hFnn : ∀ e, 0 ≤ F e := by
    intro e; rw [hF]; positivity
  have hcoef : (0 : ℝ) < (β : ℝ) * |K' r| :=
    mul_pos hβ (abs_pos.mpr hK')
  have hpt : ∀ e, |cw e| * |Q e| = ((β : ℝ) * |K' r|) * F e := by
    intro e
    rw [hcw e, hF]
    have hind : (0 : ℝ) ≤ (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) :=
      (radialKernel N _ e).coe_nonneg
    have hexp : (0 : ℝ) < Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) := Real.exp_pos _
    rw [abs_mul, abs_of_nonneg hind, abs_mul, abs_mul, abs_neg,
      abs_of_pos hexp, abs_of_nonneg β.coe_nonneg]
    ring
  refine summable_of_sum_le (c := Kd / ((β : ℝ) * |K' r|)) hFnn (fun S => ?_)
  have h1 : ((β : ℝ) * |K' r|) * ∑ e ∈ S, F e = ∑ e ∈ S, |cw e| * |Q e| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => (hpt e).symm
  have h2 : ((β : ℝ) * |K' r|) * ∑ e ∈ S, F e ≤ Kd := by rw [h1]; exact hKd S
  refine (le_div_iff₀ hcoef).mpr ?_
  rwa [mul_comm]

open Classical in
/-- **Summability of the closed flux gives `hKd`, with the sharp constant `β * |K' r|`.**  This is
the converse of `diagram_summable_closed_flux_of_hKd` for the same object: the weighted pivotal
flux is at most `β * |K' r|` times the closed-flux series.  It is not
`dominator_of_abs_flux_le` with the majorant `exp (-(β) * J_r(e)) * |Q e|` (that majorant is
smaller than `|Q e|`); the constant is instead exactly the factor removed by the defining equation
of `cw`. -/
theorem diagram_hKd_of_summable_closed_flux
    (N : ModelNorm (Fin d → ℝ)) (K K' : ℝ → ℝ) {β : ℝ≥0} {r : ℝ}
    {cw Q : Sym2 (Fin d → ℤ) → ℝ}
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hsum : Summable fun e : Sym2 (Fin d → ℤ) =>
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e|) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| * |Q e| ≤
      (β : ℝ) * |K' r| * ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| := by
  have hFnn : ∀ e : Sym2 (Fin d → ℤ), 0 ≤
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| := by
    intro e; positivity
  have hterm : ∀ e, |cw e| * |Q e| = ((β : ℝ) * |K' r|) *
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e|) := by
    intro e
    rw [hcw e]
    have hind : (0 : ℝ) ≤ (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) :=
      (radialKernel N _ e).coe_nonneg
    have hexp : (0 : ℝ) < Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) := Real.exp_pos _
    rw [abs_mul, abs_of_nonneg hind, abs_mul, abs_mul, abs_neg,
      abs_of_pos hexp, abs_of_nonneg β.coe_nonneg]
    ring
  intro S
  calc ∑ e ∈ S, |cw e| * |Q e|
      = ((β : ℝ) * |K' r|) * ∑ e ∈ S,
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => hterm e
    _ ≤ ((β : ℝ) * |K' r|) * ∑' e,
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hsum.sum_le_tsum S (fun i _ => hFnn i)

open Classical in
/-- **`hKd` is exactly summability of the closed flux.**  A finite all-pairs dominator for the
weighted pivotal flux exists **iff** the closed flux
`e ↦ 1{N(e) < r} * exp (-(β) * J_r(e)) * |Q e|` is summable.  This is the precise shape of the
remaining input of `hasDerivAt_integral_cutoff_pow`: it is a decay statement for the actual pivotal
flux `Q`, not a per-vertex moment bound (which by
`diagram_not_summable_indicator_inserted_moment` cannot supply it). -/
theorem diagram_hKd_iff_summable_closed_flux
    (N : ModelNorm (Fin d → ℝ)) (K K' : ℝ → ℝ) {β : ℝ≥0} {r : ℝ}
    {cw Q : Sym2 (Fin d → ℤ) → ℝ}
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hβ : 0 < (β : ℝ)) (hK' : K' r ≠ 0) :
    (∃ Kd : ℝ, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| * |Q e| ≤ Kd)
      ↔ Summable fun e : Sym2 (Fin d → ℤ) =>
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) * |Q e| := by
  constructor
  · rintro ⟨Kd, hKd⟩
    exact diagram_summable_closed_flux_of_hKd N K K' hcw hβ hK' hKd
  · intro hsum
    exact ⟨_, diagram_hKd_of_summable_closed_flux N K K' hcw hsum⟩

open Classical in
/-- **Non-vacuity of the coefficient, with the strict activation loss.**  On `ℤ` with the sup norm
and the antitone profile `K s = -s`, at scale `r = 2` and the short pair `{0, 1}` (distance
`1 < 2`), the identity of `diagram_pairProb_deriv_eq_closedProb_mul_rate` evaluates to
`exp (-1)`: the radial indicator is `1`, the profile rate is `β * -K' 2 = 1`, and the closed
probability is `1 - q = exp (-1)`.  The "rate without closed probability" would give `1`, so the
factor is a genuine loss on this instance, not a normalisation artefact. -/
theorem diagram_rate_example :
    HasDerivAt (fun s => (intensityProfile
        (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun t : ℝ => -t) s) 1
        (s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ))) : ℝ)) (Real.exp (-1)) 2 := by
  have hanti : AntitoneOn (fun t : ℝ => -t) (Ioi 0) := by
    intro a _ b _ hab
    change -b ≤ -a
    linarith
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => -t) (-1) t := by
    intro t _
    simpa using (hasDerivAt_neg' (x := (t : ℝ)))
  have h01 : (0 : Fin 1 → ℤ) ≠ fun _ => (1 : ℤ) := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hN1 : (normSeminorm ℝ (Fin 1 → ℝ))
      (Int.cast ∘ ((0 : Fin 1 → ℤ) - (fun _ => (1 : ℤ)))) = 1 := by
    rw [normSeminorm_intCast]; norm_num
  have hN2 : (normSeminorm ℝ (Fin 1 → ℝ))
      (Int.cast ∘ ((fun _ => (1 : ℤ)) - (0 : Fin 1 → ℤ))) = 1 := by
    rw [normSeminorm_intCast]; norm_num
  have hre : ∀ x y : Fin 1 → ℤ,
      s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ)) = s(x, y) →
      (2 : ℝ) ≠ (normSeminorm ℝ (Fin 1 → ℝ)) (Int.cast ∘ (x - y)) := by
    intro x y hxy
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hN1]; norm_num
    · rw [hN2]; norm_num
  have h := diagram_pairProb_deriv_eq_closedProb_mul_rate
    (N := ModelNorm.ofNorm (Fin 1 → ℝ)) (K := fun t : ℝ => -t) (K' := fun _ => -1)
    hanti hderiv (1 : ℝ≥0) (r := 2) (by norm_num) (s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ))) hre
  have hrad : (radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (fun s => if s < 2 then 1 else 0) (s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ))) : ℝ) = 1 := by
    rw [coe_radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ))
      (K := fun s => if s < 2 then 1 else 0) (x := (0 : Fin 1 → ℤ)) (y := fun _ => (1 : ℤ)) h01
      (by positivity), hN1]
    norm_num
  have hck : (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun t : ℝ => -t) 2
      (s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ))) : ℝ) = 1 := by
    rw [cutoffKernel, radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ)) h01, hN1,
      cutoffProfile_of_le (by norm_num), Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have hcl : (1 : ℝ) - (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (fun t : ℝ => -t) 2) 1 (s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ))) : ℝ) = Real.exp (-1) := by
    change 1 - (1 - Real.exp (-(1 : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
      (fun t : ℝ => -t) 2 (s((0 : Fin 1 → ℤ), fun _ => (1 : ℤ))) : ℝ))) = Real.exp (-1)
    rw [hck]; norm_num
  refine h.congr_deriv ?_
  simp only [ModelNorm.toSeminorm_ofNorm]
  rw [hrad, hcl]
  norm_num

/-- The instance above is strictly smaller than the "rate without closed probability": on `ℤ` at
`r = 2` with `K s = -s` and `β = 1` the true rate is `exp (-1) < 1 = β * -K' 2`. -/
theorem diagram_rate_example_lt : Real.exp (-1) < 1 := by
  rw [Real.exp_lt_one_iff]; norm_num


/-! ## Loops and the cut-off: the support of the derivative weight -/

/-- **Loops carry no weight.**  The `Sym2` index of the derivative sum includes the diagonal pairs
`s(x, x)`; the radial kernel is zero there, so they contribute nothing.  This is the loop check
for the unordered `Sym2` normalisation of Lemma I.4.1. -/
theorem diagram_weight_diag (N : Seminorm ℝ (Fin d → ℝ)) (K K' : ℝ → ℝ) (β : ℝ≥0) (r : ℝ)
    (x : Fin d → ℤ) :
    (radialKernel N (fun s => if s < r then 1 else 0) (s(x, x)) : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r (s(x, x)) : ℝ))) = 0 := by
  rw [radialKernel_diag]
  simp

/-- **Only short pairs carry weight.**  If the pair is not strictly inside the cut-off, the radial
indicator vanishes, so the derivative weight is zero: increasing `r` at a scale where
`N (x - y) > r` does not move the edge.  Together with `diagram_weight_diag` this says that the
`Sym2` sum of `hasDerivAt_cutoff_pow` is supported on short non-diagonal pairs, matching the
paper's `B_r`. -/
theorem diagram_weight_eq_zero_of_not_short {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    {β : ℝ≥0} {r : ℝ} {x y : Fin d → ℤ} (h : ¬ N (Int.cast ∘ (x - y)) < r) :
    (radialKernel N (fun s => if s < r then 1 else 0) (s(x, y)) : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r (s(x, y)) : ℝ))) = 0 := by
  rw [radialKernel_indicator_eq_zero_of_not_lt h, zero_mul]


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- With a nonzero cutoff rate, a uniform finite-sum bound on the real pivotal flux
controls the radially weighted closed-coordinate flux series as well. -/
theorem summable_closed_flux_cutoff_of_hKd {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β)))
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd)
    (hrate : (β : ℝ) * -K' r ≠ 0) :
    Summable (fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) ∧
      (∑' e, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
        |((β : ℝ) * -K' r)⁻¹| * Kd) := by
  apply summable_closed_flux_of_hKd p β r o cw Kd hKd
  intro e
  rcases radialKernel_indicator_eq_zero_or_one N r e with h0 | h1
  · simp [h0, hcw e]
  · rw [h1, one_mul]
    apply (eq_inv_mul_iff_mul_eq₀ hrate).2
    have hp := cutoff_pivotal_eq_closed_pow (K' := K') p β r e o
      (by rw [h1]; norm_num) (hfin e) (hint e)
    simpa only [hcw e, h1, one_mul] using hp.symm


end PercLib.Models.LongRange


/-! ### Ordered crossing sums and the binomial expectation -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- **Fibre computation for the collapse of a double vertex sum onto `Sym2`.**

For distinct `u v`, the double sum over `(x, y)` of the indicator of `s(x, y) = s(u, v)`
times an arbitrary weight is the sum of the two orientations `g u v + g v u`.  This is the
counting step that turns the ordered crossing sum of Lemma I.4.1 into an unordered edge
sum: every unordered non-degenerate pair has exactly two ordered representatives, and a
crossing pair has exactly one of them with the first endpoint inside the root cluster. -/
theorem tsum_tsum_sym2_eq_add {u v : V} (huv : u ≠ v) (g : V → V → ℝ≥0∞) :
    ∑' x : V, ∑' y : V, (if s(x, y) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x y
      = g u v + g v u := by
  classical
  have hmem : ∀ x y : V, s(x, y) = s(u, v) → y = u ∨ y = v := by
    intro x y h
    rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  have hxmem : ∀ x y : V, s(x, y) = s(u, v) → x = u ∨ x = v := by
    intro x y h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hinner : ∀ x : V, (∑' y : V, (if s(x, y) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x y)
      = ∑ y ∈ ({u, v} : Finset V),
          (if s(x, y) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x y := by
    intro x
    refine tsum_eq_sum (s := ({u, v} : Finset V)) ?_
    intro y hy
    have hy' : y ≠ u ∧ y ≠ v := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hy
    have hne : s(x, y) ≠ s(u, v) := fun h => (hmem x y h).elim hy'.1 hy'.2
    simp only [hne, ite_false, zero_mul]
  have houter : (∑' x : V, ∑ y ∈ ({u, v} : Finset V),
        (if s(x, y) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x y)
      = ∑ x ∈ ({u, v} : Finset V), ∑ y ∈ ({u, v} : Finset V),
          (if s(x, y) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x y := by
    refine tsum_eq_sum (s := ({u, v} : Finset V)) ?_
    intro x hx
    have hx' : x ≠ u ∧ x ≠ v := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have hne : s(x, y) ≠ s(u, v) := fun h => (hxmem x y h).elim hx'.1 hx'.2
    simp only [hne, ite_false, zero_mul]
  rw [tsum_congr hinner, houter]
  have hpair : ∀ x : V, (∑ y ∈ ({u, v} : Finset V),
      (if s(x, y) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x y)
      = (if s(x, u) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x u
        + (if s(x, v) = s(u, v) then (1 : ℝ≥0∞) else 0) * g x v := by
    intro x
    rw [show ({u, v} : Finset V) = insert u {v} from rfl,
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
  rw [show ({u, v} : Finset V) = insert u {v} from rfl,
    Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
  rw [hpair u, hpair v]
  simp only [Sym2.eq_swap, ite_true]
  have huu : s(u, u) ≠ s(u, v) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact huv h2
    · exact huv h1
  have hvv : s(v, v) ≠ s(u, v) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact huv h1.symm
    · exact huv h1.symm
  simp only [huu, hvv, ite_false, zero_mul, add_zero, one_mul, zero_add]

open Classical in
/-- The diagonal fibre: the only ordered pair representing the loop `s(u, u)` is `(u, u)`. -/
theorem tsum_tsum_sym2_eq_diag {u : V} (g : V → V → ℝ≥0∞) :
    ∑' x : V, ∑' y : V, (if s(x, y) = s(u, u) then (1 : ℝ≥0∞) else 0) * g x y
      = g u u := by
  classical
  have hmem : ∀ x y : V, s(x, y) = s(u, u) → y = u := by
    intro x y h
    rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2
    · exact h2
  have hxmem : ∀ x y : V, s(x, y) = s(u, u) → x = u := by
    intro x y h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact h1
  have hinner : ∀ x : V, (∑' y : V, (if s(x, y) = s(u, u) then (1 : ℝ≥0∞) else 0) * g x y)
      = ∑ y ∈ ({u} : Finset V),
          (if s(x, y) = s(u, u) then (1 : ℝ≥0∞) else 0) * g x y := by
    intro x
    refine tsum_eq_sum (s := ({u} : Finset V)) ?_
    intro y hy
    have hy' : y ≠ u := by simpa using hy
    have hne : s(x, y) ≠ s(u, u) := fun h => hy' (hmem x y h)
    simp only [hne, ite_false, zero_mul]
  have houter : (∑' x : V, ∑ y ∈ ({u} : Finset V),
        (if s(x, y) = s(u, u) then (1 : ℝ≥0∞) else 0) * g x y)
      = ∑ x ∈ ({u} : Finset V), ∑ y ∈ ({u} : Finset V),
          (if s(x, y) = s(u, u) then (1 : ℝ≥0∞) else 0) * g x y := by
    refine tsum_eq_sum (s := ({u} : Finset V)) ?_
    intro x hx
    have hx' : x ≠ u := by simpa using hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have hne : s(x, y) ≠ s(u, u) := fun h => hx' (hxmem x y h)
    simp only [hne, ite_false, zero_mul]
  rw [tsum_congr hinner, houter, Finset.sum_singleton, Finset.sum_singleton]
  simp


/-- Rearrangement helper: a vanishing indicator product kills the term.  Used to read the
increment `pivotal_increment_eq_crossing` in the factor order of the ordered crossing sum. -/
theorem mul_left_eq_zero_of_mul_eq_zero {c₁ c₂ r H : ℝ≥0∞} (h : c₁ * c₂ = 0) :
    c₁ * r * c₂ * H = 0 := by
  rw [show c₁ * r * c₂ * H = (c₁ * c₂) * (r * H) from by ring, h, zero_mul]

open Classical in
/-- **The pivotal increment of the root cluster as the sum of the two crossing orientations.**

For any pair `s(a, b)` and any `p`, opening `s(a, b)` changes the `p`-th power of the `encard`
of the root cluster by `1(a ∈ K_o) 1(b ∉ K_o) ((|K_o| + |K_b|)^p - |K_o|^p)` plus the same
expression with `a` and `b` interchanged.  Each summand carries the root cluster volume and the
volume of the *outside* endpoint's cluster, so this is the unordered (edge-indexed) form of the
Lemma I.4.1 summand.  Only one of the two terms can be nonzero, and the diagonal `a = b` gives
`0` on both sides.

No finiteness hypothesis is used: with an infinite root cluster the truncated subtraction is
`⊤ - ⊤ = 0` on both sides and with `|K_b| = ⊤` both are infinite. -/
theorem pivotal_increment_eq_crossing {ω : Config V} {o a b : V} (p : ℕ) :
    (((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) =
      (if a ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if b ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) +
        (if b ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if a ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω a).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) := by
  classical
  rw [encard_cluster_insert_pow_sub_eq_cases (ω := ω) (a := a) (b := b) (x := o) p]
  simp only [mem_cluster_comm ω o a, mem_cluster_comm ω o b]
  by_cases ha : o ∈ cluster ω a
  · by_cases hb : o ∈ cluster ω b
    · simp [ha, hb]
    · have hKa : cluster ω a = cluster ω o :=
        cluster_eq_of_mem_conn ((mem_cluster_iff ω a o).1 ha)
      simp [hb, hKa]
  · by_cases hb : o ∈ cluster ω b
    · have hKb : cluster ω b = cluster ω o :=
        cluster_eq_of_mem_conn ((mem_cluster_iff ω b o).1 hb)
      have hsum : (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω o).encard : ℝ≥0∞)) =
          (((cluster ω o).encard : ℝ≥0∞) + ((cluster ω a).encard : ℝ≥0∞)) := add_comm _ _
      simp [ha, hKb, hsum]
    · simp [ha, hb]

open Classical in
/-- **An open pair has both endpoints on the same side of the root cluster.**

If `s(a, b)` is already open, then `a` and `b` are in a common cluster, so the two crossing
factors of `pivotal_increment_eq_crossing` cannot both be nonzero: an open pair contributes no
pivotal flux.  This is why the `1(e ∉ ω)` factor of the closed-coordinate form is redundant on
the pivotal side. -/
theorem crossing_indicator_eq_zero_of_mem {ω : Config V} {o a b : V} (hab : a ≠ b)
    (hopen : s(a, b) ∈ ω) :
    (if a ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if b ∈ cluster ω o then 0 else 1) = 0 ∧
      (if b ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if a ∈ cluster ω o then 0 else 1) = 0 := by
  classical
  have hcl : cluster ω a = cluster ω b := cluster_eq_of_mem_conn (mem_conn_of_mem hab hopen)
  have hiff : a ∈ cluster ω o ↔ b ∈ cluster ω o := by
    rw [mem_cluster_comm ω o a, mem_cluster_comm ω o b, hcl]
  constructor
  · by_cases ha : a ∈ cluster ω o
    · rw [show (if a ∈ cluster ω o then (1 : ℝ≥0∞) else 0) = 1 from ite_eq_left ha,
        show (if b ∈ cluster ω o then (0 : ℝ≥0∞) else 1) = 0 from ite_eq_left (hiff.1 ha),
        mul_zero]
    · rw [show (if a ∈ cluster ω o then (1 : ℝ≥0∞) else 0) = 0 from ite_eq_right ha, zero_mul]
  · by_cases ha : a ∈ cluster ω o
    · rw [show (if a ∈ cluster ω o then (0 : ℝ≥0∞) else 1) = 0 from ite_eq_left ha, mul_zero]
    · rw [show (if a ∈ cluster ω o then (0 : ℝ≥0∞) else 1) = 1 from ite_eq_right ha,
        show (if b ∈ cluster ω o then (1 : ℝ≥0∞) else 0) = 0 from
          ite_eq_right (fun h => ha (hiff.2 h)),
        zero_mul]

open Classical in
/-- **The pivotal increment is killed by an open pair.** -/
theorem pivotal_increment_eq_zero_of_mem {ω : Config V} {o a b : V} (p : ℕ) (hab : a ≠ b)
    (hopen : s(a, b) ∈ ω) :
    (((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) = 0 := by
  obtain ⟨h1, h2⟩ := crossing_indicator_eq_zero_of_mem (o := o) hab hopen
  rw [pivotal_increment_eq_crossing (ω := ω) (o := o) (a := a) (b := b) p, h1, h2]
  simp


open Classical in
/-- **The unordered pivotal sum is the ordered crossing sum (Lemma I.4.1, pointwise, `ℝ≥0∞`).**

For a fixed configuration `ω`, root `o`, exponent `p` and an arbitrary edge weight `radial`,
the pivotal sum over *unordered* pairs

`∑' e, radial e * (1(e ∉ ω)) · (|K_o(ω ∪ e)|^p − |K_o(ω)|^p)`

equals the *ordered* crossing sum of the paper's proof of Lemma I.4.1,

`∑' x, ∑' y, 1(x ∈ K_o) · radial {x,y} · 1(y ∉ K_o) · ((|K_o| + |K_y|)^p − |K_o|^p)`.

Each crossing unordered pair `{x, y}` occurs exactly once on the right, with the inside endpoint
as `x`; diagonal pairs and pairs with both endpoints on the same side contribute `0` on both
sides.  The `1(e ∉ ω)` factor on the left is redundant:
`pivotal_increment_eq_zero_of_mem` kills the increment of an already-open pair, and no case
split on `e ∈ ω` is needed.

Everything is `ℝ≥0∞` with truncated subtraction, so there is no finiteness hypothesis: an
infinite root cluster gives `⊤ - ⊤ = 0` termwise on both sides, and an infinite far cluster gives
`⊤` on both sides.  No summability hypothesis is needed either, since `ℝ≥0∞` sums are
unconditionally defined and Tonelli applies to `ENNReal.tsum_comm`.

The reduction is: (i) `Sym2.inductionOn` plus the fibre counts `tsum_tsum_sym2_eq_add` /
`tsum_tsum_sym2_eq_diag` collapse the ordered sum onto the unordered one, (ii) the per-pair
identity `pivotal_increment_eq_crossing` identifies the two summands, (iii) `ENNReal.tsum_comm`
twice moves the `Sym2` sum innermost. -/
theorem tsum_pivotal_eq_tsum_crossing {V : Type*} (ω : Config V) (o : V) (p : ℕ)
    (radial : Sym2 V → ℝ≥0∞) :
    (∑' e : Sym2 V, radial e * (if e ∈ ω then (0 : ℝ≥0∞) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p))) =
      ∑' x : V, ∑' y : V,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * radial s(x, y) *
          (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) := by
  classical
  let G : V → V → ℝ≥0∞ := fun x y =>
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * radial s(x, y) *
        (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)
  change (∑' e : Sym2 V, radial e * (if e ∈ ω then (0 : ℝ≥0∞) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p)))
      = ∑' x : V, ∑' y : V, G x y
  have hkey : ∀ e : Sym2 V, radial e * (if e ∈ ω then (0 : ℝ≥0∞) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p))
      = ∑' x : V, ∑' y : V, (if s(x, y) = e then (1 : ℝ≥0∞) else 0) * G x y := by
    intro e
    refine Sym2.inductionOn e ?_
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [tsum_tsum_sym2_eq_diag (u := a) (g := G), cluster_insert_diag, tsub_self]
      by_cases ha : a ∈ cluster ω o
      · dsimp only [G]
        simp [ha]
      · dsimp only [G]
        simp [ha]
    · rw [tsum_tsum_sym2_eq_add (u := a) (v := b) hab (g := G),
        pivotal_increment_eq_crossing (ω := ω) (o := o) (a := a) (b := b) p]
      dsimp only [G]
      rw [show radial (s(b, a)) = radial (s(a, b)) from by rw [Sym2.eq_swap]]
      by_cases hopen : s(a, b) ∈ ω
      · obtain ⟨h1, h2⟩ := crossing_indicator_eq_zero_of_mem (o := o) hab hopen
        rw [ite_eq_left hopen, mul_zero,
          mul_left_eq_zero_of_mul_eq_zero (r := radial s(a, b)) h1,
          mul_left_eq_zero_of_mul_eq_zero (r := radial s(a, b)) h2]
        simp
      · rw [ite_eq_right hopen, mul_add]
        ring
  calc (∑' e : Sym2 V, radial e * (if e ∈ ω then (0 : ℝ≥0∞) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p)))
      = ∑' e : Sym2 V, ∑' x : V, ∑' y : V,
          (if s(x, y) = e then (1 : ℝ≥0∞) else 0) * G x y := tsum_congr hkey
    _ = ∑' x : V, ∑' e : Sym2 V, ∑' y : V,
          (if s(x, y) = e then (1 : ℝ≥0∞) else 0) * G x y := ENNReal.tsum_comm
    _ = ∑' x : V, ∑' y : V, ∑' e : Sym2 V,
          (if s(x, y) = e then (1 : ℝ≥0∞) else 0) * G x y :=
          tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' x : V, ∑' y : V, G x y := by
          refine tsum_congr fun x => tsum_congr fun y => ?_
          rw [tsum_eq_single (s(x, y)) (fun e he => by simp [Ne.symm he])]
          simp


end PercLib.Percolation.Bond


namespace PercLib.Percolation.Bond

open Classical in
/-- **Non-vacuity of the crossing identity.**  On `Bool` with the empty configuration and root
`false`, the ordered crossing sum of unit weight at `p = 1` is `1`: the only crossing pair is
`{false, true}`, contributing `(|K_false| + |K_true|) - |K_false| = (1 + 1) - 1`. -/
theorem tsum_crossing_bool_empty :
    (∑' x : Bool, ∑' y : Bool,
        (if x ∈ cluster (∅ : Config Bool) false then (1 : ℝ≥0∞) else 0) * (1 : ℝ≥0∞) *
          (if y ∈ cluster (∅ : Config Bool) false then 0 else 1) *
          ((((cluster (∅ : Config Bool) false).encard : ℝ≥0∞) +
              ((cluster (∅ : Config Bool) y).encard : ℝ≥0∞)) ^ 1 -
            ((cluster (∅ : Config Bool) false).encard : ℝ≥0∞) ^ 1)) = 1 := by
  classical
  simp only [tsum_fintype, Fintype.sum_bool]
  simp [cluster_empty]

open Classical in
/-- **The pivotal sum of the witness is `1` as well**, so `tsum_pivotal_eq_tsum_crossing` is not
the identity `0 = 0` on this configuration. -/
theorem tsum_pivotal_bool_empty :
    (∑' e : Sym2 Bool, (1 : ℝ≥0∞) *
        (((cluster (insert e (∅ : Config Bool)) false).encard : ℝ≥0∞) ^ 1 -
          ((cluster (∅ : Config Bool) false).encard : ℝ≥0∞) ^ 1)) = 1 := by
  classical
  have h := (tsum_pivotal_eq_tsum_crossing (ω := (∅ : Config Bool)) (o := false) (p := 1)
    (radial := fun _ => (1 : ℝ≥0∞))).trans tsum_crossing_bool_empty
  simpa using h

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-- The radial indicator of a non-diagonal pair, as a `ℝ≥0`-valued ball indicator.  This is
`radialKernel_indicator_eq_ball_of_ne` with the `ℝ`-coercion removed, so that it can be used as
a factor in an `ℝ≥0∞` sum. -/
theorem radialKernel_indicator_eq_ball_of_ne_nn {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Set.Ioo u v) (hr : r ∈ Set.Ioo u v)
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    radialKernel N (fun s => if s < r then 1 else 0) s(x, y) =
      if N (Int.cast ∘ (y - x)) ≤ r then (1 : ℝ≥0) else 0 := by
  have h := radialKernel_indicator_eq_ball_of_ne N hcorner hr hxy
  by_cases hc : N (Int.cast ∘ (y - x)) ≤ r
  · rw [ite_eq_left hc]
    rw [ite_eq_left hc] at h
    apply NNReal.coe_injective
    rw [h, NNReal.coe_one]
  · rw [ite_eq_right hc]
    rw [ite_eq_right hc] at h
    apply NNReal.coe_injective
    rw [h, NNReal.coe_zero]

/-- The same reconciliation in `ℝ≥0∞`, the shape in which it multiplies an `ℝ≥0∞` flux. -/
theorem radialKernel_indicator_eq_ball_of_ne_enn {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Set.Ioo u v) (hr : r ∈ Set.Ioo u v)
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    ((radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0) : ℝ≥0∞) =
      if N (Int.cast ∘ (y - x)) ≤ r then (1 : ℝ≥0∞) else 0 := by
  have h := radialKernel_indicator_eq_ball_of_ne_nn hcorner hr hxy
  by_cases hc : N (Int.cast ∘ (y - x)) ≤ r
  · rw [ite_eq_left hc]
    rw [ite_eq_left hc] at h
    rw [h, ENNReal.coe_one]
  · rw [ite_eq_right hc]
    rw [ite_eq_right hc] at h
    rw [h, ENNReal.coe_zero]

open Classical in
/-- **Lemma I.4.1, boundary-sum form at the cut-off radius (pointwise, `ℝ≥0∞`).**

Specializing `tsum_pivotal_eq_tsum_crossing` to the radial indicator `1(N(y - x) < r)` of the
cut-off derivative coefficient, and reconciling the derivative's *strict* indicator with the
paper's *closed* ball `B_r(x) = {y : ‖y - x‖ ≤ r}`, gives the unordered pivotal sum as the
ordered lattice sum

`∑' x, ∑' y, 1(x ∈ K_o) · 1(‖y - x‖ ≤ r) · 1(y ∉ K_o) · ((|K_o| + |K_y|)^p − |K_o|^p)`,

which is the integrand of the first display in the proof of Lemma I.4.1 (before the
mass-transport step).  The corner hypothesis is used *only* to pass from `< r` to `≤ r`; on the
diagonal nothing is needed, because `1(y ∉ K_o)` with `y = x ∈ K_o` already vanishes. -/
theorem tsum_radialKernel_pivotal_eq_tsum_ball {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Set.Ioo u v) (hr : r ∈ Set.Ioo u v)
    (ω : Config (Fin d → ℤ)) (o : Fin d → ℤ) (p : ℕ) :
    (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))) =
      ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if N (Int.cast ∘ (y - x)) ≤ r then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) := by
  classical
  rw [PercLib.Percolation.Bond.tsum_pivotal_eq_tsum_crossing (ω := ω) (o := o) (p := p)
    (radial := fun e => ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞))]
  refine tsum_congr fun x => tsum_congr fun y => ?_
  by_cases hxy : x = y
  · subst hxy
    rw [radialKernel_diag]
    simp only [ENNReal.coe_zero]
    by_cases hx : x ∈ cluster ω o
    · simp [hx]
    · simp [hx]
  · rw [radialKernel_indicator_eq_ball_of_ne_enn hcorner hr hxy]

end PercLib.Models.LongRange


open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Analysis

namespace PercLib.Models.LongRange

variable {V : Type*}
variable {d : ℕ}

/-! ### The sharpened pointwise binomial step -/

/-- **The `ℝ≥0∞` binomial step needs only the root cluster to be finite.**

For `A ≠ ⊤` and *arbitrary* `B : ℝ≥0∞` (in particular `B = ⊤`, an infinite far cluster),

`A * ((A + B)^p − A^p) = ∑_{ℓ<p} C(p,ℓ) A^{ℓ+1} B^{p−ℓ}`.

This drops the hypothesis `B ≠ ⊤` of `mul_pow_sub_pow_eq_sum_choose_ennreal`.  The case
`B = ⊤` is the degenerate one: for `A ≠ 0` both sides are `⊤`, for `A = 0` both are `0`. -/
theorem mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite {A B : ℝ≥0∞} (hA : A ≠ ⊤) (p : ℕ) :
    A * ((A + B) ^ p - A ^ p) =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) * B ^ (p - ℓ) := by
  by_cases hB : B = ⊤
  · subst hB
    rcases eq_or_ne A 0 with hA0 | hA0
    · simp [hA0]
    · rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        simp
      · have htop : (⊤ : ℝ≥0∞) ^ p = ⊤ := by
          cases p with
          | zero => omega
          | succ n => simp
        have hAp : A ^ p ≠ ⊤ := ENNReal.pow_ne_top hA
        have hL : A * ((A + ⊤) ^ p - A ^ p) = ⊤ := by
          rw [add_top, htop, ENNReal.sub_eq_top_iff.2 ⟨rfl, hAp⟩, ENNReal.mul_top hA0]
        rw [hL]
        refine (ENNReal.sum_eq_top.2 ⟨0, Finset.mem_range.2 hp, ?_⟩).symm
        rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.zero_add, htop,
          pow_one]
        exact ENNReal.mul_top hA0
  · exact mul_pow_sub_pow_eq_sum_choose_ennreal hA hB p

/-! ### The root-cluster finiteness is not removable -/

/-- **Sharpness: with an infinite root cluster the binomial step fails.**

For `A = ⊤`, `B ≠ 0` and `p ≥ 1` the left side is `⊤ * (⊤ − ⊤) = 0` while the binomial
sum is `⊤` (its `ℓ = 0` term is `⊤`).  So the hypothesis `A ≠ ⊤` in
`mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite` is exactly the right one. -/
theorem top_mul_pow_sub_pow_ne_sum_choose {B : ℝ≥0∞} (hB : B ≠ 0) {p : ℕ} (hp : 1 ≤ p) :
    (⊤ : ℝ≥0∞) * ((⊤ + B) ^ p - ⊤ ^ p) ≠
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ⊤ ^ (ℓ + 1) * B ^ (p - ℓ) := by
  have htop : (⊤ : ℝ≥0∞) ^ p = ⊤ := by
    cases p with
    | zero => omega
    | succ n => simp
  have hL : (⊤ : ℝ≥0∞) * ((⊤ + B) ^ p - ⊤ ^ p) = 0 := by
    rw [top_add, htop, tsub_self, mul_zero]
  have hR : ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ⊤ ^ (ℓ + 1) * B ^ (p - ℓ) = ⊤ := by
    refine ENNReal.sum_eq_top.2 ⟨0, Finset.mem_range.2 hp, ?_⟩
    rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.zero_add, pow_one]
    exact ENNReal.top_mul (pow_ne_zero p hB)
  rw [hL, hR]
  exact ENNReal.zero_ne_top

/-- **In the bond model the failure is at hand at every infinite root cluster.**

A cluster volume is never `0` (`one_le_encard_cluster`), so for `p ≥ 1` the pointwise
binomial step fails at every configuration whose root cluster is infinite, for every far
vertex `y`.  Hence the `A ≠ ⊤` hypothesis of the sharpened step is not removable inside
the model, and no argument that only inspects the pointwise algebra can prove the binomial
step of Lemma I.4.1 without almost-sure finiteness of the root cluster. -/
theorem root_cluster_binomial_fails_of_encard_eq_top (ω : Config V) (o y : V) {p : ℕ}
    (hp : 1 ≤ p) (h : ((cluster ω o).encard : ℝ≥0∞) = ⊤) :
    ((cluster ω o).encard : ℝ≥0∞) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) ≠
      ∑ ℓ ∈ Finset.range p,
        (p.choose ℓ : ℝ≥0∞) * ((cluster ω o).encard : ℝ≥0∞) ^ (ℓ + 1) *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) := by
  have hpos : (1 : ℝ≥0∞) ≤ ((cluster ω y).encard : ℝ≥0∞) := by
    have h1 : (1 : ℕ∞) ≤ (cluster ω y).encard := one_le_encard_cluster ω y
    exact_mod_cast h1
  have hB : ((cluster ω y).encard : ℝ≥0∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hpos)
  simpa only [h] using
    top_mul_pow_sub_pow_ne_sum_choose (B := ((cluster ω y).encard : ℝ≥0∞)) hB hp



/-! ### The pointwise binomial form with a finite root cluster only -/

/-- **The pointwise binomial form of (I.4.1)** under finiteness of the root cluster alone. -/
theorem russoRHS_eq_binomial_of_root_finite {ω : Config (Fin d → ℤ)}
    (h : ((cluster ω 0).encard : ℝ≥0∞) ≠ ⊤) (p : ℕ)
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
  have hA0 : ((cluster ω 0).encard : ℝ≥0∞) ≠ ⊤ := h
  have hbin : ∀ y : Fin d → ℤ,
      ((cluster ω 0).encard : ℝ≥0∞) *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)
        = ∑ ℓ ∈ Finset.range p,
            (p.choose ℓ : ℝ≥0∞) * ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) :=
    fun y => mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite hA0 p
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

/-! ### The binomial step with a finite root cluster only -/

/-- **Lemma I.4.1 in binomial form, with the root-cluster finiteness hypothesis only.**

The far clusters `K_y` may be infinite; the `ℝ≥0∞` identity absorbs them, and by
`root_cluster_binomial_fails_of_encard_eq_top` the present hypothesis on `K_0` is not
removable.  No moment finiteness is assumed. -/
theorem i41_binomial_of_root_finite (μ : Measure (Config (Fin d → ℤ)))
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
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
  have hae : ∀ᵐ ω ∂μ, ((cluster ω 0).encard : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfin] with ω h
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
        exact russoRHS_eq_binomial_of_root_finite h p N r
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



/-! ### The moment form: only the root moment has to be finite -/

/-- **The binomial step of Lemma I.4.1 under finiteness of the root moment.**

`i41_binomial` assumes that every cluster is almost surely finite.  By the sharpened
pointwise step only the root cluster matters, so that hypothesis can be replaced by the
paper's actual input, finiteness of the `p`-th moment of `|K_0|` (which implies
`|K_0| < ∞` almost surely).  The far clusters are unrestricted. -/
theorem i41_binomial_of_root_moment (μ : Measure (Config (Fin d → ℤ))) {p : ℕ} (hp : 1 ≤ p)
    (hmom : ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂μ ≠ ⊤)
    (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
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
  have hSmeas : MeasurableSet {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} :=
    (measurable_encard_cluster_coe (0 : Fin d → ℤ)) (measurableSet_singleton ⊤)
  have hzero : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0 := by
    by_contra hne
    apply hmom
    refine le_antisymm le_top ?_
    have htop : (⊤ : ℝ≥0∞) * μ {ω : Config (Fin d → ℤ) |
        ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = ⊤ := by
      rw [ENNReal.top_mul hne]
    calc (⊤ : ℝ≥0∞)
        = ⊤ * μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} := htop.symm
      _ = ∫⁻ ω, ({ω : Config (Fin d → ℤ) |
            ((cluster ω 0).encard : ℝ≥0∞) = ⊤}.indicator (fun _ => ⊤) ω) ∂μ :=
          (lintegral_indicator_const hSmeas ⊤).symm
      _ ≤ ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤}
          · rw [Set.indicator_of_mem hω]
            have hc : ((cluster ω 0).encard : ℝ≥0∞) = ⊤ := hω
            rw [hc]
            exact le_of_eq (by
              cases p with
              | zero => omega
              | succ n => simp)
          · rw [Set.indicator_of_notMem hω]
            exact zero_le
  exact i41_binomial_of_root_finite μ hzero p N r

/-! ### Non-vacuity of the sharpness statement -/

/-- With every bond open the cluster of the origin is everything, so the configuration in
`root_cluster_binomial_fails_of_encard_eq_top` exists: the sharpness statement is not
vacuous, and its hypothesis `|K_o| = ⊤` is realised on the infinite line. -/
theorem cluster_univ_int_encard_eq_top :
    ((cluster (Set.univ : Config ℤ) 0).encard : ℝ≥0∞) = ⊤ := by
  have hcl : cluster (Set.univ : Config ℤ) 0 = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true, mem_cluster_iff]
    rcases eq_or_ne y 0 with rfl | hy
    · exact mem_cluster_self Set.univ 0
    · exact mem_conn_of_mem (Ne.symm hy) (Set.mem_univ _)
  rw [hcl]
  have hinf : (Set.univ : Set ℤ).Infinite := Set.infinite_univ
  rw [hinf.encard_eq]
  simp

/-- The sharpness statement at a concrete, non-vacuous configuration: with every bond open
on `ℤ` the pointwise binomial step of `i41_binomial` fails at `p = 2`, `o = 0`, `y = 1`. -/
example :
    ((cluster (Set.univ : Config ℤ) 0).encard : ℝ≥0∞) *
        ((((cluster (Set.univ : Config ℤ) 0).encard : ℝ≥0∞) +
          ((cluster (Set.univ : Config ℤ) 1).encard : ℝ≥0∞)) ^ 2 -
          ((cluster (Set.univ : Config ℤ) 0).encard : ℝ≥0∞) ^ 2) ≠
      ∑ ℓ ∈ Finset.range 2,
        ((2 : ℕ).choose ℓ : ℝ≥0∞) * ((cluster (Set.univ : Config ℤ) 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          ((cluster (Set.univ : Config ℤ) 1).encard : ℝ≥0∞) ^ (2 - ℓ) :=
  root_cluster_binomial_fails_of_encard_eq_top (ω := Set.univ) 0 1 (by norm_num)
    cluster_univ_int_encard_eq_top


/-! ### The production forms: cut-off and general intensity -/

/-- **Lemma I.4.1 in binomial form for the cut-off model, with a moment hypothesis.**

This is `i41_cutoff_binomial` with its hypothesis "every cluster is almost surely finite"
replaced by finiteness of the `p`-th moment of the root cluster volume, which is the input
the paper actually has. -/
theorem i41_cutoff_binomial_of_root_moment {N : ModelNorm (Fin d → ℝ)} (K : ℝ → ℝ) (r : ℝ)
    (β : ℝ≥0) {p : ℕ} (hp : 1 ≤ p)
    (hmom : ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≠ ⊤) :
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
  i41_binomial_of_root_moment _ hp hmom N r

/-- **Lemma I.4.1 in binomial form for any intensity, with a moment hypothesis.**

This is `i41_intensityProfile_binomial` with its all-clusters a.e.-finiteness hypothesis
replaced by finiteness of the root moment; no translation invariance is needed. -/
theorem i41_intensityProfile_binomial_of_root_moment {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (β : ℝ≥0) {p : ℕ} (hp : 1 ≤ p) (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ)
    (hmom : ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂(law (intensityProfile J β)) ≠ ⊤) :
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
  i41_binomial_of_root_moment _ hp hmom N r

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

variable {d : ℕ}

open Classical in
/-- **The corner reconciliation of the ordered sum.**

At a radius `r` with no lattice displacement of norm in the corner interval `(u, v)`, the
ordered double sum of Lemma I.4.1 with the cutoff derivative's *strict* pair weight
`radialKernel N 1(s < r)` equals the paper's sum with the *closed* ball indicator
`1(∥y - x∥ ≤ r)`.  Both sums carry `1(x ∈ K_0)` and `1(y ∉ K_0)`, so the diagonal `x = y`
contributes `0` to both sides and the loop convention of `radialKernel` never needs to be
matched against the ball indicator there. -/
theorem tsum_ordered_radial_eq_ball (N : Seminorm ℝ (Fin d → ℝ)) {u v r : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (ω : Config (Fin d → ℤ)) (p : ℕ) :
    (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p))
      = ∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (if N (Int.cast ∘ (y - x)) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p) := by
  classical
  refine tsum_congr fun x => tsum_congr fun y => ?_
  have hx1 : (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω =
      if ω ∈ conn 0 x then 1 else 0 := by
    simp [Set.indicator_apply]
  have hy1 : (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω =
      if ω ∈ (conn 0 y)ᶜ then 1 else 0 := by
    simp [Set.indicator_apply]
  rw [hx1, hy1]
  by_cases hx : ω ∈ conn 0 x
  · by_cases hy : ω ∈ conn 0 y
    · have hy'' : ¬ (ω ∈ (conn 0 y)ᶜ) := fun h => h hy
      rw [ite_eq_left hx, ite_eq_right hy'']
      simp
    · have hxy : x ≠ y := by
        rintro rfl
        exact hy hx
      have hy' : ω ∈ (conn 0 y)ᶜ := hy
      rw [ite_eq_left hx, ite_eq_left hy',
        radialKernel_indicator_eq_ball_of_ne_enn (N := N) hcorner hr hxy]
  · rw [ite_eq_right hx]
    simp


end PercLib.Models.LongRange

/-! ### The assembled extended-nonnegative binomial identity -/

namespace PercLib.Models.LongRange

variable {d : ℕ}

open PercLib.Percolation.Bond

/-- The ordered strict-radial crossing sum has the paper's binomial form under only
almost-sure finiteness of the root cluster. -/
theorem i41_ordered_binomial_of_root_finite (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p : ℕ} {u v : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v) :
    ∫⁻ ω, (∑' x, ∑' y,
        (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ :=
  (lintegral_congr fun ω => tsum_ordered_radial_eq_ball N hcorner hr ω p).trans
    ((i41_massTransport μ hμ p N r).trans (i41_binomial_of_root_finite μ hfin p N r))

open Classical in
/-- The unordered-to-ordered reindex is sufficient for the assembled extended-nonnegative
identity, with only root-cluster finiteness required in the binomial step. -/
theorem i41_enn_of_pointwise_reindex (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p : ℕ} {u v : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (hreindex : ∀ ω : Config (Fin d → ℤ),
      (∑' e : Sym2 (Fin d → ℤ),
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
            (if e ∈ ω then 0 else
              ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p))
        = ∑' x, ∑' y,
            (conn 0 x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
              (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p)) :
    ∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
          (if e ∈ ω then 0 else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ :=
  (lintegral_congr hreindex).trans
    (i41_ordered_binomial_of_root_finite μ hμ hfin hcorner hr)

open Classical in
/-- The unordered pivotal flux has the paper's extended-nonnegative binomial form under
shift invariance and almost-sure finiteness of the root cluster. -/
theorem i41_enn_of_root_finite (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p : ℕ} {u v : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v) :
    ∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
          (if e ∈ ω then 0 else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ := by
  apply i41_enn_of_pointwise_reindex μ hμ hfin hcorner hr
  intro ω
  have h := PercLib.Percolation.Bond.tsum_pivotal_eq_tsum_crossing ω 0 p
    (fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞))
  simp only [mem_cluster_iff] at h
  refine h.trans ?_
  refine tsum_congr fun x => tsum_congr fun y => ?_
  by_cases hy : ω ∈ conn 0 y <;> simp [Set.indicator_apply, hy]

end PercLib.Models.LongRange
/-! ### Cutoff normalization and coefficient signs -/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology unitInterval

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-- **Numeric `p`-th power differences do not need `toReal`.**  For natural `a`, `b` and `p`, the
truncated `ℝ≥0∞` difference `a^p - b^p` is the cast of the truncated natural difference.  This is
the `toReal`-free companion of `pow_add_sub_pow_toReal`, and it is what makes the finite
`ℝ≥0∞` arithmetic of the audit reduce to `ℕ`. -/
theorem ennreal_pow_sub_pow_natCast (a b p : ℕ) :
    ((a : ℝ≥0∞) ^ p - (b : ℝ≥0∞) ^ p) = ((a ^ p - b ^ p : ℕ) : ℝ≥0∞) := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, ← ENNReal.natCast_sub (a ^ p) (b ^ p)]


section Corner

/-- The sup seminorm of a one-dimensional integer displacement is the absolute value of its
coordinate, expressed through `Int.natAbs` so that it is visibly a natural number. -/
theorem normSeminorm_fin_one_intCast (z : Fin 1 → ℤ) :
    normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) = ((z 0).natAbs : ℝ) := by
  have h1 : normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) = |(((z 0) : ℤ) : ℝ)| := by
    rw [show normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) = ‖(Int.cast ∘ z : Fin 1 → ℝ)‖ from rfl,
      Pi.norm_def]
    simp
  have h2 : |(((z 0) : ℤ) : ℝ)| = ((z 0).natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp
  rw [h1, h2]

/-- **No corner at `r = 3/2`.**  No integer displacement of the one-dimensional lattice has norm
strictly between `1` and `2`, which is exactly the corner hypothesis of
`indicator_lt_eq_le`/`radialKernel_indicator_eq_ball_of_ne` at `r = 3/2`. -/
theorem corner_free_at_three_halves :
    ∀ z : Fin 1 → ℤ, normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) ∉ Set.Ioo (1 : ℝ) 2 := by
  intro z
  rw [normSeminorm_fin_one_intCast]
  have hsplit : (z 0).natAbs = 0 ∨ (z 0).natAbs = 1 ∨ 2 ≤ (z 0).natAbs := by omega
  rcases hsplit with h | h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
  · intro hc
    have h2 : (2 : ℝ) ≤ ((z 0).natAbs : ℝ) := by exact_mod_cast h
    linarith [hc.2]

/-- **The corner reconciliation holds at `r = 3/2`**: the strict indicator of the cutoff
derivative and the paper's closed ball agree on every integer displacement. -/
theorem strict_eq_closed_at_three_halves (z : Fin 1 → ℤ) :
    (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) < (3 / 2 : ℝ) then (1 : ℝ≥0∞) else 0) =
      if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) ≤ (3 / 2 : ℝ) then 1 else 0 :=
  indicator_lt_eq_le _ corner_free_at_three_halves (by norm_num) z

/-- The cutoff radial kernel at `r = 3/2` equals the closed-ball indicator off the diagonal: the
compiled form of `radialKernel_indicator_eq_ball_of_ne` at a radius that has no corner. -/
theorem radialKernel_three_halves_eq_ball (x y : Fin 1 → ℤ) (hxy : x ≠ y) :
    (radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => if s < (3 / 2 : ℝ) then 1 else 0)
        s(x, y) : ℝ) =
      if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ (y - x)) ≤ (3 / 2 : ℝ) then 1 else 0 :=
  radialKernel_indicator_eq_ball_of_ne _ corner_free_at_three_halves (by norm_num) hxy

/-- **The corner hypothesis is not removable.**  At the integer radius `r = 2` the strict
indicator and the closed ball genuinely differ, at the displacement `2`; hence the corner
hypothesis in `indicator_lt_eq_le` is a real restriction and not a convenience. -/
theorem corner_at_two :
    ¬ ∀ z : Fin 1 → ℤ,
      (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) < (2 : ℝ) then (1 : ℝ≥0∞) else 0) =
        if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ z) ≤ (2 : ℝ) then 1 else 0 := by
  intro h
  have hz := h (fun _ => (2 : ℤ))
  rw [normSeminorm_fin_one_intCast] at hz
  norm_num at hz

end Corner

open Classical in
/-- **The corner hypothesis of `tsum_radialKernel_pivotal_eq_tsum_ball` is inhabited in the
one-dimensional model.**  At `d = 1`, `u = 1`, `v = 2`, `r = 3/2` the hypothesis holds for every
configuration, root and exponent, so the strict radial indicator of the cutoff derivative and the
paper's closed ball agree there.  This is a non-vacuity certificate, not a weakening: the
hypothesis is genuinely a restriction, since at `r = 2` the two indicators differ. -/
theorem tsum_radialKernel_pivotal_eq_tsum_ball_at_three_halves (ω : Config (Fin 1 → ℤ))
    (o : Fin 1 → ℤ) (p : ℕ) :
    (∑' e : Sym2 (Fin 1 → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
            (fun s => if s < (3 / 2 : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))) =
      ∑' x : Fin 1 → ℤ, ∑' y : Fin 1 → ℤ,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ (y - x)) ≤ (3 / 2 : ℝ) then
            (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) :=
  tsum_radialKernel_pivotal_eq_tsum_ball (d := 1) (N := normSeminorm ℝ (Fin 1 → ℝ))
    (u := 1) (v := 2) (r := 3 / 2) corner_free_at_three_halves (by norm_num) ω o p


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

/-- An antitone profile has nonpositive derivative at every positive differentiable point. -/
theorem cutoffProfile_deriv_nonpos {K K' : ℝ → ℝ} (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t) {r : ℝ} (hr : 0 < r) : K' r ≤ 0 :=
  (hK' r hr).hasDerivWithinAt.nonpos_of_antitoneOn (isOpen_Ioi.preperfect r hr) hKa

/-- The cutoff Russo coefficient is nonnegative on every pair. -/
theorem nonneg_cutoff_deriv_weight {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (β : ℝ≥0) {r : ℝ} (hr : 0 < r) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (e : Sym2 (Fin d → ℤ)) : 0 ≤ cw e := by
  rw [hcw e]
  refine mul_nonneg (radialKernel N _ e).coe_nonneg ?_
  exact mul_nonneg (mul_nonneg β.coe_nonneg
    (neg_nonneg.mpr (cutoffProfile_deriv_nonpos hKa hK' hr))) (Real.exp_pos _).le


end PercLib.Models.LongRange

/-! ### Real and extended-nonnegative cutoff-moment bridges -/

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Per-pair arithmetic of the truncated subtraction -/

/-- **The truncated subtraction casts to the real difference, except in one case.**

For `B ≤ A`, the `ℝ`-cast of the truncated difference `A ^ p - B ^ p` is the real difference of
the cast `p`-th powers, provided `A` is finite, or `B` is zero (both sides are then the cast of
`A ^ p`), or `B` is infinite (and then `A = ⊤` as well, and both sides vanish). -/
theorem toReal_pow_sub_pow_of_finite_or_zero {A B : ℝ≥0∞} (hBA : B ≤ A) (p : ℕ)
    (h : A ≠ ⊤ ∨ B = 0 ∨ B = ⊤) :
    (A ^ p - B ^ p).toReal = A.toReal ^ p - B.toReal ^ p := by
  rcases h with hA | hB0 | hBtop
  · exact toReal_pow_sub_pow hBA hA p
  · subst hB0
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [zero_pow hp, tsub_zero, ENNReal.toReal_pow, ENNReal.toReal_zero, zero_pow hp,
        sub_zero]
  · have hA : A = ⊤ := top_le_iff.1 (hBtop ▸ hBA)
    subst hA
    subst hBtop
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [ENNReal.top_pow hp, tsub_self, ENNReal.toReal_zero, ENNReal.toReal_top,
        zero_pow hp, sub_self]

/-- **Sharp form of `toReal_pow_sub_pow_of_finite_or_zero` for `p ≥ 1`.**

For `p ≥ 1` and `B ≤ A`, the cast of the truncated difference agrees with the real difference
exactly when `A ≠ ⊤`, or `B = 0`, or `B = ⊤`.  Hence the only obstruction to the pointwise
real/extended-nonnegative conversion is a pair whose inserted cluster is infinite while its
deleted cluster is finite and nonempty. -/
theorem toReal_pow_sub_pow_eq_iff {A B : ℝ≥0∞} (hBA : B ≤ A) {p : ℕ} (hp : 1 ≤ p) :
    (A ^ p - B ^ p).toReal = A.toReal ^ p - B.toReal ^ p ↔
      (A ≠ ⊤ ∨ B = 0 ∨ B = ⊤) := by
  refine ⟨fun h => ?_, toReal_pow_sub_pow_of_finite_or_zero hBA p⟩
  by_contra hc
  push Not at hc
  obtain ⟨hA, hB0, hBtop⟩ := hc
  subst hA
  have hpne : p ≠ 0 := by omega
  have hBne : B ^ p ≠ ⊤ := ENNReal.pow_ne_top hBtop
  have hBpos : 0 < B.toReal := ENNReal.toReal_pos hB0 hBtop
  have hpow : 0 < B.toReal ^ p := pow_pos hBpos p
  rw [ENNReal.top_pow hpne, ENNReal.top_sub hBne, ENNReal.toReal_top,
    zero_pow hpne, zero_sub] at h
  exact hpow.ne' (neg_eq_zero.1 h.symm)

/-! ### The pointwise series identity -/

/-- **The pivotal increment in real form, one pair at a time.**  The cast of the truncated
difference of the `p`-th cluster moments over the pair `e` is the real difference of the cast
moments, as soon as the inserted cluster is finite (or the deleted one is empty or infinite). -/
theorem toReal_pivotal_increment {ω : Config V} {o : V} (e : Sym2 V) (p : ℕ)
    (h : ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ ∨
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) = 0 ∨
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) = ⊤) :
    ((((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal) =
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p :=
  toReal_pow_sub_pow_of_finite_or_zero (encard_cluster_sdiff_le_insert_coe ω e o) p h

/-- **The cast of the weighted pivotal series is the weighted real pivotal series.**

For a fixed bond configuration and an `ℝ≥0∞`-valued weight, if every weighted truncated pivotal
increment is finite (`hjunk`, which for a finite weight only asks the inserted cluster to be
finite) and every pair casts correctly (`hmatch`), then the `ℝ`-cast of the extended-nonnegative
pivotal series is the real pivotal series.  There is no summability hypothesis: if the
nonnegative extended-nonnegative series diverges, `ENNReal.tsum_toReal_eq` reports `0` on both
sides. -/
theorem toReal_tsum_pivotal_eq_tsum_real [Countable V] (ω : Config V) (o : V) (p : ℕ)
    (w : Sym2 V → ℝ≥0∞)
    (hjunk : ∀ e, w e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ≠ ⊤)
    (hmatch : ∀ e, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ ∨
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) = 0 ∨
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) = ⊤) :
    (∑' e : Sym2 V, w e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal =
      ∑' e : Sym2 V, (w e).toReal *
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) := by
  rw [ENNReal.tsum_toReal_eq hjunk]
  refine tsum_congr fun e => ?_
  rw [ENNReal.toReal_mul, toReal_pivotal_increment e p (hmatch e)]

/-- **The cast of the weighted pivotal series is the weighted real pivotal series**, in the
usable form: the weight is finite and the inserted cluster is finite for every pair. -/
theorem toReal_tsum_pivotal_eq_tsum_real_of_finite [Countable V] (ω : Config V) (o : V) (p : ℕ)
    (w : Sym2 V → ℝ≥0∞) (hw : ∀ e, w e ≠ ⊤)
    (hfin : ∀ e, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    (∑' e : Sym2 V, w e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal =
      ∑' e : Sym2 V, (w e).toReal *
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) :=
  toReal_tsum_pivotal_eq_tsum_real ω o p w
    (fun e => ENNReal.mul_ne_top (hw e)
      (ne_top_of_le_ne_top (ENNReal.pow_ne_top (hfin e)) tsub_le_self))
    (fun e => Or.inl (hfin e))

open Classical in
/-- **The closed-coordinate series in real form.**  Off the open event `e ∈ ω` the pair
contributes its pivotal increment; on it, the closed-coordinate normalisation of
`i41_enn_of_root_finite` sets the contribution to zero, and the real series does the same. -/
theorem toReal_tsum_closed_eq_tsum_real [Countable V] (ω : Config V) (o : V) (p : ℕ)
    (w : Sym2 V → ℝ≥0∞) (hw : ∀ e, w e ≠ ⊤)
    (hfin : ∀ e, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    (∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal =
      ∑' e : Sym2 V, (w e).toReal * (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) := by
  have hdiff : ∀ e : Sym2 V, e ∉ ω →
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p) ≠ ⊤ := by
    intro e _
    refine ne_top_of_le_ne_top (ENNReal.pow_ne_top (hfin e)) tsub_le_self
  rw [ENNReal.tsum_toReal_eq (f := fun e => w e * (if e ∈ ω then (0 : ℝ≥0∞) else
    ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p)) ?_]
  · refine tsum_congr fun e => ?_
    rw [ENNReal.toReal_mul]
    by_cases he : e ∈ ω
    · rw [ite_eq_left he, ite_eq_left he, ENNReal.toReal_zero]
    · rw [ite_eq_right he, ite_eq_right he]
      have hsd : ω \ {e} = ω := Set.sdiff_singleton_eq_self he
      rw [toReal_pow_sub_pow (B := ((cluster ω o).encard : ℝ≥0∞)) (by
        have h := encard_cluster_sdiff_le_insert_coe ω e o
        rwa [hsd] at h) (hfin e) p]
  · intro e
    by_cases he : e ∈ ω
    · rw [ite_eq_left he, mul_zero]
      exact ENNReal.zero_ne_top
    · rw [ite_eq_right he]
      exact ENNReal.mul_ne_top (hw e) (hdiff e he)

/-- **The a.e. form under per-pair a.e. finiteness.**  Since `Sym2 V` is countable, the null
sets of the per-pair hypotheses have a null union, and the pointwise identity holds almost
surely. -/
theorem ae_toReal_tsum_pivotal_eq_tsum_real [Countable V]
    (μ : MeasureTheory.Measure (Config V)) (o : V)
    (p : ℕ) (w : Sym2 V → ℝ≥0∞) (hw : ∀ e, w e ≠ ⊤)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    ∀ᵐ ω ∂μ, (∑' e : Sym2 V, w e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal =
      ∑' e : Sym2 V, (w e).toReal *
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) := by
  filter_upwards [MeasureTheory.ae_all_iff.2 hfin] with ω hω
  exact toReal_tsum_pivotal_eq_tsum_real_of_finite ω o p w hw hω

open Classical in
/-- **The a.e. closed-coordinate form under per-pair a.e. finiteness.** -/
theorem ae_toReal_tsum_closed_eq_tsum_real [Countable V]
    (μ : MeasureTheory.Measure (Config V)) (o : V)
    (p : ℕ) (w : Sym2 V → ℝ≥0∞) (hw : ∀ e, w e ≠ ⊤)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    ∀ᵐ ω ∂μ, (∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal =
      ∑' e : Sym2 V, (w e).toReal * (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) := by
  filter_upwards [MeasureTheory.ae_all_iff.2 hfin] with ω hω
  exact toReal_tsum_closed_eq_tsum_real ω o p w hw hω


/-! ### The per-pair finiteness hypothesis is not removable -/

/-- **A cluster is a singleton when the root has no open pair.** -/
theorem cluster_eq_singleton_of_isolated {ω : Config V} {x : V}
    (h : ∀ y, ¬ (openGraph ω).Adj x y) : cluster ω x = {x} := by
  have hkey : ∀ {u v : V}, (openGraph ω).Walk u v → u = x → v = x := by
    intro u v w
    induction w with
    | nil => exact id
    | cons hadj _ _ =>
      intro hu
      exact absurd (hu ▸ hadj) (h _)
  ext y
  constructor
  · intro hy
    obtain ⟨w⟩ := hy
    exact hkey w rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact mem_cluster_self ω x

/-- **The star configuration on `ℕ`** `{ {1,n} : n ≥ 2 }`: the origin is isolated. -/
theorem star_zero_isolated :
    ∀ y : ℕ, ¬ (openGraph {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)}).Adj 0 y := by
  intro y hy
  obtain ⟨hmem, -⟩ := (openGraph_adj_iff _ 0 y).1 hy
  obtain ⟨n, hn, hEq⟩ := hmem
  rcases Sym2.eq_iff.1 hEq with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Nat.zero_ne_one h1
  · omega

/-- In the star configuration the cluster of the origin is a singleton. -/
theorem star_cluster_zero :
    cluster {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)} 0 = {0} :=
  cluster_eq_singleton_of_isolated star_zero_isolated

/-- The pair `{0,1}` is closed in the star configuration. -/
theorem star_not_mem : s(0, 1) ∉ {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)} := by
  rintro ⟨n, hn, hEq⟩
  rcases Sym2.eq_iff.1 hEq with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Nat.zero_ne_one h1
  · omega

/-- Opening `{0,1}` in the star configuration connects the origin to everything. -/
theorem star_insert_cluster_univ :
    cluster (insert (s(0, 1)) {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)}) 0 = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  rcases eq_or_ne y 0 with rfl | h0
  · exact mem_cluster_self _ 0
  rcases eq_or_ne y 1 with rfl | h1
  · exact mem_conn_of_mem (by norm_num) (Set.mem_insert _ _)
  · have hy : 2 ≤ y := by omega
    exact conn_trans (mem_conn_of_mem (by norm_num) (Set.mem_insert _ _))
      (mem_conn_of_mem (by omega) (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩))

/-- In the star configuration the inserted cluster of the origin is infinite. -/
theorem star_insert_cluster_encard_top :
    ((cluster (insert (s(0, 1)) {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)}) 0).encard :
      ℝ≥0∞) = ⊤ := by
  rw [star_insert_cluster_univ]
  have hinf : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  rw [hinf.encard_eq]
  simp

/-- **The general obstruction to removing the finiteness hypothesis.**  If one pair `e₀` carries
all the weight, has an infinite inserted cluster and a finite nonempty deleted cluster, then the
cast of the weighted extended-nonnegative pivotal series is `0` while the weighted real pivotal
series is strictly negative. -/
theorem toReal_tsum_pivotal_ne_tsum_real [Countable V] (ω : Config V) (o : V) (p : ℕ)
    (hp : 1 ≤ p) (w : Sym2 V → ℝ≥0∞) (e₀ : Sym2 V) (hsupp : ∀ e, e ≠ e₀ → w e = 0)
    (hw0 : w e₀ ≠ 0) (hwt : w e₀ ≠ ⊤)
    (hA : ((cluster (insert e₀ ω) o).encard : ℝ≥0∞) = ⊤)
    (hB0 : ((cluster (ω \ {e₀}) o).encard : ℝ≥0∞) ≠ 0)
    (hBt : ((cluster (ω \ {e₀}) o).encard : ℝ≥0∞) ≠ ⊤) :
    (∑' e : Sym2 V, w e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ≠
      ∑' e : Sym2 V, (w e).toReal *
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) := by
  have hpne : p ≠ 0 := by omega
  have hBfin : ((cluster (ω \ {e₀}) o).encard : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.pow_ne_top hBt
  have hdiff : ((cluster (insert e₀ ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e₀}) o).encard : ℝ≥0∞) ^ p = ⊤ := by
    rw [hA, ENNReal.top_pow hpne, ENNReal.top_sub hBfin]
  have hL : (∑' e : Sym2 V, w e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) = ⊤ := by
    rw [tsum_eq_single e₀]
    · rw [hdiff, ENNReal.mul_top hw0]
    · intro e he
      rw [hsupp e he, zero_mul]
  have hR : (∑' e : Sym2 V, (w e).toReal *
      ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)) =
      (w e₀).toReal * (-((((cluster (ω \ {e₀}) o).encard : ℝ≥0∞)).toReal ^ p)) := by
    rw [tsum_eq_single e₀]
    · rw [hA, ENNReal.toReal_top, zero_pow hpne, zero_sub]
    · intro e he
      rw [hsupp e he, ENNReal.toReal_zero, zero_mul]
  have hBpos : 0 < (((cluster (ω \ {e₀}) o).encard : ℝ≥0∞)).toReal :=
    ENNReal.toReal_pos hB0 hBt
  have hwpos : (w e₀).toReal ≠ 0 := (ENNReal.toReal_pos hw0 hwt).ne'
  have hpow : 0 < ((((cluster (ω \ {e₀}) o).encard : ℝ≥0∞)).toReal ^ p) := pow_pos hBpos p
  rw [hL, hR, ENNReal.toReal_top]
  intro hcontra
  rw [mul_neg] at hcontra
  exact mul_ne_zero hwpos hpow.ne' (neg_eq_zero.1 hcontra.symm)

/-- **The per-pair finiteness hypothesis of `toReal_tsum_pivotal_eq_tsum_real` is not
removable.**  In the star configuration on `ℕ` the origin is isolated, so deleting the pair
`{0,1}` leaves the cluster of `0` a singleton, while opening it merges the origin into the
infinite component of `1`.  For the weight concentrated on that single pair and `p = 1` the cast
of the extended-nonnegative pivotal series is `0`, while the real pivotal series is `-1`. -/
theorem star_counterexample_pivotal :
    (∑' e : Sym2 ℕ, (if e = s(0, 1) then (1 : ℝ≥0∞) else 0) *
        (((cluster (insert e {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)}) 0).encard :
            ℝ≥0∞) ^ 1 -
          ((cluster ({f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)} \ {e}) 0).encard :
            ℝ≥0∞) ^ 1)).toReal ≠
      ∑' e : Sym2 ℕ, ((if e = s(0, 1) then (1 : ℝ≥0∞) else 0)).toReal *
        ((((cluster (insert e {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)}) 0).encard :
            ℝ≥0∞).toReal) ^ 1 -
          (((cluster ({f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)} \ {e}) 0).encard :
            ℝ≥0∞).toReal) ^ 1) := by
  let ω : Config ℕ := {f : Sym2 ℕ | ∃ n : ℕ, 2 ≤ n ∧ f = s(1, n)}
  have hBval : ((cluster (ω \ {s(0, 1)}) 0).encard : ℝ≥0∞) = 1 := by
    rw [Set.sdiff_singleton_eq_self (star_not_mem), star_cluster_zero]
    simp
  refine toReal_tsum_pivotal_ne_tsum_real ω 0 1 le_rfl
    (fun e => if e = s(0, 1) then (1 : ℝ≥0∞) else 0) (s(0, 1)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro e he
    exact ite_eq_right he
  · simp
  · simp
  · exact star_insert_cluster_encard_top
  · rw [hBval]
    exact one_ne_zero
  · rw [hBval]
    exact ENNReal.one_ne_top

open Classical in
/-- **The closed-coordinate a.e. conversion in the shape used by the cutoff derivative.**  The
weight is the library's `radialKernel` of the cutoff indicator, whose `ℝ`-cast is the weight of
`tsum_cutoff_pivotal_eq_closed_pow`. -/
theorem ae_toReal_tsum_radialKernel_closed_eq_tsum_real {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ}
    (μ : MeasureTheory.Measure (Config (Fin d → ℤ))) (p : ℕ)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ≠ ⊤) :
    ∀ᵐ ω ∂μ, (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)).toReal =
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p) := by
  filter_upwards [ae_toReal_tsum_closed_eq_tsum_real μ 0 p
    (fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞))
    (fun e => ENNReal.coe_ne_top) hfin] with ω hω
  refine hω.trans (tsum_congr fun e => ?_)
  simp

open Classical in
/-- **The assembled real form of the closed-coordinate flux from its extended-nonnegative
identity.**

This is the exact composition of the two real/extended-nonnegative passages:
`integral_toReal_eq_toReal_lintegral` on the extended-nonnegative series (inputs: a.e. finiteness
of the series and its a.e. measurability), the pointwise conversion
`ae_toReal_tsum_closed_eq_tsum_real`, and the integral/sum interchange `hinter`.

The interchange is *not* supplied by `hKd`: `hKd` bounds the pivotal flux, and
`summable_closed_flux_of_hKd` needs its `hpair` input as well.  The a.e. finiteness `hne` of the
extended-nonnegative series is likewise not implied by the per-pair finiteness `hflux` of
`hasDerivAt_integral_cutoff_pow`: it is a genuine extra input of the real passage. -/
theorem toReal_lintegral_tsum_closed_eq_tsum_integral [Countable V]
    (μ : MeasureTheory.Measure (Config V)) (o : V) (p : ℕ) (w : Sym2 V → ℝ≥0∞)
    (hw : ∀ e, w e ≠ ⊤)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hmeas : AEMeasurable (fun ω => ∑' e : Sym2 V, w e *
      (if e ∈ ω then (0 : ℝ≥0∞) else ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) μ)
    (hne : ∀ᵐ ω ∂μ, (∑' e : Sym2 V, w e *
      (if e ∈ ω then (0 : ℝ≥0∞) else ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ≠ ⊤)
    (hinter : ∫ ω, (∑' e : Sym2 V, (w e).toReal * (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ =
      ∑' e : Sym2 V, (w e).toReal * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ) :
    (∫⁻ ω, ∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal =
      ∑' e : Sym2 V, (w e).toReal * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
  rw [← integral_toReal_eq_toReal_lintegral hmeas hne,
    MeasureTheory.integral_congr_ae
      (ae_toReal_tsum_closed_eq_tsum_real μ o p w hw hfin), hinter]

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

/-! ### Almost sure finiteness from finite moments -/

/-- **A.e. finiteness from a finite moment.** If the `p`-th power of a nonnegative
observable has finite integral (`p ≥ 1`), the observable is finite almost surely. -/
theorem ae_ne_top_of_lintegral_pow_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (p : ℕ) (hp : 1 ≤ p)
    (hmom : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    ∀ᵐ a ∂μ, f a ≠ ⊤ := by
  filter_upwards [ae_lt_top (hf.pow_const p) hmom] with a ha htop
  rw [htop, ENNReal.top_pow (by omega : p ≠ 0)] at ha
  exact absurd ha (lt_irrefl ⊤)

/-- **Integrability of the inserted real moment from the inserted `ℝ≥0∞` moment.** Under a
finite inserted `p`-th moment, the real function `|K_o(ω ∪ {e})|^p` (`toReal` applied
pointwise) is integrable. This is the `hint` input of `summable_closed_flux_cutoff_of_hKd`,
obtained from the same moment hypothesis that gives `hflux`. -/
theorem integrable_toReal_pow_encard_cluster_insert {V : Type*} [Countable V]
    {μ : Measure (Config V)} (e : Sym2 V) (o : V) (p : ℕ)
    (h : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p) μ := by
  have hm : AEMeasurable
      (fun ω : Config V => ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_insert_coe e o).pow_const p).aemeasurable
  refine (integrable_toReal_of_lintegral_ne_top hm h).congr ?_
  filter_upwards with ω
  exact ENNReal.toReal_pow _ p

/-- **The susceptibility is bounded by any moment.** The cluster of `o` always contains `o`,
so its volume is at least `1`; hence `|K_o| ≤ |K_o|^p` for `p ≥ 1` and the first moment
(`chi`) is finite as soon as the `p`-th moment is. This discharges the susceptibility input
of the cutoff derivative from a moment hypothesis at the same scale. -/
theorem chi_ne_top_of_lintegral_pow_ne_top {V : Type*} (q : Sym2 V → unitInterval) (o : V)
    (p : ℕ) (hp : 1 ≤ p)
    (hmom : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(law q)) ≠ ⊤) :
    chi q o ≠ ⊤ := by
  refine ne_top_of_le_ne_top hmom (lintegral_mono fun ω => ?_)
  have h1 : (1 : ℝ≥0∞) ≤ ((cluster ω o).encard : ℝ≥0∞) := by
    exact_mod_cast one_le_encard_cluster ω o
  exact le_self_pow₀ h1 (by omega)

/-! ### The pivotal increment is bounded by the inserted moment -/

/-- **The plain moment is bounded by the inserted moment.** Inserting a pair can only
enlarge the cluster of `o`, so finiteness of the inserted `p`-th moment gives finiteness of
the plain one. -/
theorem lintegral_pow_encard_ne_top_of_insert {V : Type*} {μ : Measure (Config V)}
    (e : Sym2 V) (o : V) (p : ℕ)
    (h : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ :=
  ne_top_of_le_ne_top h (lintegral_mono fun ω => ENNReal.pow_le_pow_left (by
    exact_mod_cast Set.encard_mono (cluster_mono (subset_insert e ω) o)))

/-- **The pivotal increment is at most the inserted moment.** For every configuration the
truncated difference `|K_o(ω ∪ {e})|^p - |K_o(ω \ {e})|^p` is bounded by the first term,
so the same holds for the integrals. No finiteness is needed for this step. -/
theorem lintegral_pivotal_increment_le_lintegral_insert_pow {V : Type*} {μ : Measure (Config V)}
    (e : Sym2 V) (o : V) (p : ℕ) :
    (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≤
      ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ :=
  lintegral_mono fun _ => tsub_le_self

/-- **`hflux` from a finite inserted moment.** -/
theorem lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top {V : Type*}
    {μ : Measure (Config V)} (e : Sym2 V) (o : V) (p : ℕ)
    (h : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤ :=
  ne_top_of_le_ne_top h (lintegral_pivotal_increment_le_lintegral_insert_pow e o p)

/-! ### The inserted moment is the moment in the law with `e` forced open -/

open Classical in
/-- **Finite-energy form of the inserted moment.** Inserting the pair `e` into a
configuration with law `law q` produces the law in which the open probability of `e` is
`1`, so the `p`-th moment of the cluster of `o` after inserting `e` is the `p`-th moment of
the plain cluster of `o` under `law (Function.update q e 1)`. -/
theorem lintegral_insert_pow_encard_eq_update {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) (e : Sym2 V) (o : V) (p : ℕ) :
    (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂(law q)) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(law (Function.update q e 1)) := by
  change (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂(prodBernoulli q)) =
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(prodBernoulli (Function.update q e 1))
  rw [← prodBernoulli_map_insert q e,
    lintegral_map (f := fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) ^ p)
      (g := fun ω : Config V => insert e ω)
      ((Measurable.of_discrete.comp (measurable_encard_cluster (x := o))).pow_const p)
      (measurable_insert e)]

open Classical in
/-- The same statement in the form in which the derivative interface uses it. -/
theorem lintegral_insert_pow_ne_top_iff_update {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) (e : Sym2 V) (o : V) (p : ℕ) :
    ((∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂(law q)) ≠ ⊤) ↔
      ((∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(law (Function.update q e 1))) ≠ ⊤) := by
  rw [lintegral_insert_pow_encard_eq_update]

/-! ### The derivative interface with one moment hypothesis -/

open Classical in
/-- **The cutoff Russo derivative from per-pair moment finiteness.**

This is `hasDerivAt_integral_cutoff_pow` with the three finiteness hypotheses `hmom`,
`hfin` and `hflux` replaced by the single per-pair hypothesis `hins`: for every scale `r`
in the interval and every pair `e`, the `p`-th moment of the cluster of `o` after inserting
`e` is finite. Each of the three is recovered from `hins`:

* `hmom` because `cluster ω o ⊆ cluster (insert e ω) o` monotone in the configuration;
* `hfin` by `ae_ne_top_of_lintegral_pow_ne_top`;
* `hflux` by `lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top`.

The all-pairs dominator (`hKd` with `hKdint`), the a.e. strong measurability of the capped
flux series (`hmeas`) and the continuity of the uncapped flux series (`hcont`) remain
inputs: moment finiteness does not supply them. -/
theorem hasDerivAt_integral_cutoff_pow_of_insert_moments {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hins : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (∑' e, cw r₀ e *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r₀) β))) r₀ := by
  refine hasDerivAt_integral_cutoff_pow hKa hK' hK'c β p hp o hχ cw hcw hu hur hrv hvR
    hcorner ?_ ?_ ?_ Kd hKdint hKd hmeas hcont
  · -- `hmom`: the plain cluster is contained in the inserted cluster
    intro r hr
    exact lintegral_pow_encard_ne_top_of_insert s(0, 0) o p (hins r hr s(0, 0))
  · -- `hfin`
    intro r hr e
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o)
      p hp (hins r hr e)
  · -- `hflux`
    intro r hr e
    exact lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top e o p (hins r hr e)

/-! ### The moment hypothesis is not a consequence of the flux bound -/

open Classical in
/-- **A finite pivotal flux does not force a finite inserted moment.**

This is the sharpness of the reduction: `hflux` alone cannot replace `hins`. On `ℤ` with
the configuration that has every pair open, both the inserted and the deleted cluster of `0`
are the whole line, so the truncated pivotal increment is `⊤ - ⊤ = 0` while the inserted
moment is `⊤`. Hence the moment hypothesis of
`hasDerivAt_integral_cutoff_pow_of_insert_moments` is a genuine input (in the paper it comes
from sharpness of the phase transition), not a consequence of the flux bound. -/
theorem pivotal_flux_ne_top_of_insert_moment_eq_top :
    ((∫⁻ ω : Config ℤ, (((cluster (insert s(0, 0) ω) 0).encard : ℝ≥0∞) ^ 1 -
        ((cluster (ω \ {s(0, 0)}) 0).encard : ℝ≥0∞) ^ 1)
        ∂(Measure.dirac (Set.univ : Config ℤ))) ≠ ⊤) ∧
      ((∫⁻ ω : Config ℤ, ((cluster (insert s(0, 0) ω) 0).encard : ℝ≥0∞) ^ 1
        ∂(Measure.dirac (Set.univ : Config ℤ))) = ⊤) := by
  -- the pair `s(0,0)` is a loop, so neither inserting nor deleting it changes the graph
  have hclins : cluster (insert s(0, 0) (Set.univ : Config ℤ)) 0 = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true, mem_cluster_iff]
    rcases eq_or_ne y 0 with rfl | hy
    · exact mem_cluster_self _ 0
    · exact mem_conn_of_mem (Ne.symm hy) (by simp)
  have hsdiff : cluster ((Set.univ : Config ℤ) \ {s(0, 0)}) 0 = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true, mem_cluster_iff]
    rcases eq_or_ne y 0 with rfl | hy
    · exact mem_cluster_self _ 0
    · refine mem_conn_of_mem (Ne.symm hy) ?_
      simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      intro h
      rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hy h2
      · exact hy h2
  have henc : ((Set.univ : Set ℤ).encard : ℝ≥0∞) = ⊤ := by
    have hinf : (Set.univ : Set ℤ).Infinite := Set.infinite_univ
    rw [hinf.encard_eq]
    simp
  have hflux : (∫⁻ ω : Config ℤ, (((cluster (insert s(0, 0) ω) 0).encard : ℝ≥0∞) ^ 1 -
      ((cluster (ω \ {s(0, 0)}) 0).encard : ℝ≥0∞) ^ 1)
      ∂(Measure.dirac (Set.univ : Config ℤ))) = 0 := by
    rw [lintegral_dirac' _ (measurable_pivotal (s(0, 0)) 0 1), hclins, hsdiff, henc]
    simp
  have hmom : (∫⁻ ω : Config ℤ, ((cluster (insert s(0, 0) ω) 0).encard : ℝ≥0∞) ^ 1
      ∂(Measure.dirac (Set.univ : Config ℤ))) = ⊤ := by
    rw [lintegral_dirac' _ ((measurable_encard_cluster_insert_coe (s(0, 0)) 0).pow_const 1),
      hclins, henc]
    simp
  exact ⟨by rw [hflux]; simp, hmom⟩


/-! ### Closed-flux summability from the inserted moment -/

open Classical in
/-- **Radially weighted closed-flux summability from the inserted moment.**

This is `summable_closed_flux_cutoff_of_hKd` with its two finiteness inputs (`hfin`, the a.e.
finiteness of the inserted cluster, and `hint`, the real integrability of its `p`-th
moment) derived from the single `ℝ≥0∞` moment hypothesis `hins`, exactly as in
`hasDerivAt_integral_cutoff_pow_of_insert_moments`. The exponent is required to be at least
one so that `⊤ ^ p = ⊤` recovers a.e. finiteness. The dominator `hKd` and its bound, the
defining weight equation and the nonvanishing of the rate remain inputs. -/
theorem summable_closed_flux_cutoff_of_insert_moments {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hp : 1 ≤ p)
    (hins : ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd)
    (hrate : (β : ℝ) * -K' r ≠ 0) :
    Summable (fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) ∧
      (∑' e, |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
        |((β : ℝ) * -K' r)⁻¹| * Kd) :=
  summable_closed_flux_cutoff_of_hKd p β r o cw Kd hcw
    (fun e => ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o)
      p hp (hins e))
    (fun e => integrable_toReal_pow_encard_cluster_insert e o p (hins e))
    hKd hrate

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-! ### The abstract interchange -/

/-- **Integral and sum commute for a nonnegative family with a finite `ℓ¹` flux.**

No integrability is assumed: the finite `ℓ¹` hypothesis makes both sides honest.  This is the
form in which the interchange is needed; the content is that the pointwise `tsum` on the left
is *not* junk, because the family of `L¹` norms is summable. -/
theorem integral_tsum_of_nonneg_of_lintegral_tsum_ne_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Countable ι] {F : ι → α → ℝ}
    (hF : ∀ e, AEStronglyMeasurable (F e) μ)
    (h0 : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ F e ω)
    (hsum : (∑' e, ∫⁻ ω, ENNReal.ofReal (F e ω) ∂μ) ≠ ⊤) :
    ∫ ω, ∑' e, F e ω ∂μ = ∑' e, ∫ ω, F e ω ∂μ := by
  have hnorm : ∀ e, ∫⁻ ω, ‖F e ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal (F e ω) ∂μ := by
    intro e
    refine lintegral_congr_ae ?_
    filter_upwards [h0 e] with ω h
    rw [Real.enorm_eq_ofReal h]
  refine MeasureTheory.integral_tsum hF ?_
  rw [tsum_congr hnorm]
  exact hsum

/-- **Interchange through an `ℝ≥0∞` model of the flux.**

The pointwise identity `ofReal (F e ω) = w e * φ e ω` transfers the finiteness of the
`ℝ≥0∞` flux `∑' e, w e * ∫⁻ φ e` to the `ℓ¹` hypothesis of
`integral_tsum_of_nonneg_of_lintegral_tsum_ne_top`. -/
theorem integral_tsum_of_nonneg_of_bridge {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Countable ι] {F : ι → α → ℝ} {φ : ι → α → ℝ≥0∞}
    {w : ι → ℝ≥0∞}
    (hF : ∀ e, AEStronglyMeasurable (F e) μ)
    (h0 : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ F e ω)
    (hφ : ∀ e, Measurable (φ e))
    (hbridge : ∀ e, ∀ᵐ ω ∂μ, ENNReal.ofReal (F e ω) = w e * φ e ω)
    (hsum : (∑' e, w e * ∫⁻ ω, φ e ω ∂μ) ≠ ⊤) :
    ∫ ω, ∑' e, F e ω ∂μ = ∑' e, ∫ ω, F e ω ∂μ := by
  refine integral_tsum_of_nonneg_of_lintegral_tsum_ne_top hF h0 ?_
  have h1 : (∑' e, ∫⁻ ω, ENNReal.ofReal (F e ω) ∂μ)
      = ∑' e, w e * ∫⁻ ω, φ e ω ∂μ := by
    refine tsum_congr fun e => ?_
    rw [lintegral_congr_ae (hbridge e), lintegral_const_mul (w e) (hφ e)]
  rw [h1]
  exact hsum

/-! ### The `toReal` bridge for the pivotal increment -/

/-- **`ofReal` of the real `p`-th power difference is the `ℝ≥0∞` pivotal increment.**

For `B ≤ A` and `A ≠ ⊤`, the truncated `ℝ≥0∞` difference of the `p`-th powers is the
`ofReal` of the honest real difference of the `toReal`s.  This is the converse direction of
`toReal_pow_sub_pow`, and it is what lets the finiteness of an `ℝ≥0∞` flux bound the `ℓ¹`
norm of the real family. -/
theorem ofReal_toReal_pow_sub_pow {A B : ℝ≥0∞} (hBA : B ≤ A) (hA : A ≠ ⊤) (p : ℕ) :
    ENNReal.ofReal (A.toReal ^ p - B.toReal ^ p) = A ^ p - B ^ p := by
  have hB : B ≠ ⊤ := ne_top_of_le_ne_top hA hBA
  have hBA' : B.toReal ≤ A.toReal := ENNReal.toReal_mono hA hBA
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_toReal hA, ENNReal.ofReal_toReal hB]

/-! ### Measurability of the two families -/

variable {d : ℕ}

open Classical in
/-- Measurability of the closed-coordinate pivotal family `1(e ∉ ω)(|K_o(ω ∪ e)|^p - |K_o(ω)|^p)`,
with the indicator `1(e ∉ ω)` retained. -/
theorem measurable_closed_pivotal (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ) (p : ℕ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) := by
  have hB : Measurable fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) :=
    Measurable.of_discrete.comp (measurable_encard_cluster (x := o))
  exact Measurable.ite (measurableSet_mem e) measurable_const
    (((measurable_encard_cluster_insert_coe e o).pow_const p).sub (hB.pow_const p))

open Classical in
/-- Measurability of the *real* closed-coordinate pivotal family. -/
theorem measurable_real_closed_pivotal (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ) (p : ℕ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal ^ p -
        ((cluster ω o).encard : ℝ≥0∞).toReal ^ p)) := by
  have hB : Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster ω o).encard : ℝ≥0∞).toReal :=
    ENNReal.measurable_toReal.comp
      (Measurable.of_discrete.comp (measurable_encard_cluster (x := o)))
  have hA : Measurable fun ω : Config (Fin d → ℤ) =>
      ((cluster (insert e ω) o).encard : ℝ≥0∞).toReal :=
    ENNReal.measurable_toReal.comp (measurable_encard_cluster_insert_coe e o)
  exact Measurable.ite (measurableSet_mem e) measurable_const
    ((hA.pow_const p).sub (hB.pow_const p))

/-- Measurability of the *real* pivotal family in `insert`/`sdiff` form. -/
theorem measurable_real_pivotal (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ) (p : ℕ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) :=
  ((ENNReal.measurable_toReal.comp (measurable_encard_cluster_insert_coe e o)).pow_const p).sub
    ((ENNReal.measurable_toReal.comp (measurable_encard_cluster_sdiff_coe e o)).pow_const p)

/-- Monotonicity of the closed-coordinate cluster volume: `|K_o(ω)| ≤ |K_o(ω ∪ e)|`. -/
theorem encard_cluster_le_insert_coe (ω : Config (Fin d → ℤ)) (e : Sym2 (Fin d → ℤ))
    (o : Fin d → ℤ) :
    ((cluster ω o).encard : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) := by
  exact_mod_cast Set.encard_mono (cluster_mono (subset_insert e ω) o)

/-! ### The closed-coordinate form (the paper's family) -/

open Classical in
/-- **Integral/sum interchange for the closed-coordinate real pivotal flux.**

The real series `∑' e, r k e * 1(e ∉ ω)(|K_o(ω ∪ e)|^p - |K_o(ω)|^p)` is the family whose
`ℝ≥0∞` version appears in `i41_enn_of_root_finite`; this is the step that turns the series of
per-pair integrals back into an integral of the pointwise pair sum.  The finiteness
hypothesis `hsum` is exactly finiteness of the paper's `ℝ≥0∞` pivotal flux. -/
theorem integral_tsum_closed_pivotal_real (μ : Measure (Config (Fin d → ℤ)))
    (p : ℕ) (o : Fin d → ℤ) (rk : Sym2 (Fin d → ℤ) → ℝ) (hrk : ∀ e, 0 ≤ rk e)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hsum : (∑' e, ENNReal.ofReal (rk e) * ∫⁻ ω,
      (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤) :
    ∫ ω, (∑' e, rk e * (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ
      = ∑' e, rk e * ∫ ω, (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
  have hmain : ∫ ω, (∑' e, rk e * (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ
      = ∑' e, ∫ ω, rk e * (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
    refine integral_tsum_of_nonneg_of_bridge (w := fun e => ENNReal.ofReal (rk e))
      (φ := fun e ω => if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ?_ ?_ ?_ ?_ hsum
    · intro e
      exact (measurable_const.mul (measurable_real_closed_pivotal e o p)).aestronglyMeasurable
    · intro e
      filter_upwards [hfin e] with ω hω
      refine mul_nonneg (hrk e) ?_
      split_ifs with he
      · exact le_refl 0
      · exact sub_nonneg.2 (pow_le_pow_left₀ ENNReal.toReal_nonneg
          (ENNReal.toReal_mono hω (encard_cluster_le_insert_coe ω e o)) p)
    · intro e
      exact measurable_closed_pivotal e o p
    · intro e
      filter_upwards [hfin e] with ω hω
      by_cases he : e ∈ ω
      · simp only [he, ite_true, mul_zero, ENNReal.ofReal_zero]
      · simp only [he, ite_false]
        rw [ENNReal.ofReal_mul (hrk e),
          ofReal_toReal_pow_sub_pow (encard_cluster_le_insert_coe ω e o) hω p]
  refine hmain.trans (tsum_congr fun e => ?_)
  rw [integral_const_mul]

/-! ### The pivotal form (the family of `hasDerivAt_integral_cutoff_pow`) -/

/-- **Integral/sum interchange for the real pivotal flux in `insert`/`sdiff` form.**

This is the family that `hasDerivAt_integral_cutoff_pow` produces, with the deleted cluster
`K_o(ω ∖ e)` rather than the closed-coordinate `K_o(ω)`; it differs from the closed family
exactly on the event `e ∈ ω`, where the closed family is set to `0` by its indicator.  The
`ℝ≥0∞` finiteness hypothesis is again the pivotal flux itself, now in the untruncated
`insert`/`sdiff` normalisation. -/
theorem integral_tsum_pivotal_real (μ : Measure (Config (Fin d → ℤ)))
    (p : ℕ) (o : Fin d → ℤ) (rk : Sym2 (Fin d → ℤ) → ℝ) (hrk : ∀ e, 0 ≤ rk e)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hsum : (∑' e, ENNReal.ofReal (rk e) * ∫⁻ ω,
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    ∫ ω, (∑' e, rk e * ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ
      = ∑' e, rk e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
  have hmain : ∫ ω, (∑' e, rk e * ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ
      = ∑' e, ∫ ω, rk e * ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
    refine integral_tsum_of_nonneg_of_bridge (w := fun e => ENNReal.ofReal (rk e))
      (φ := fun e ω => (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ?_ ?_ ?_ ?_ hsum
    · intro e
      exact (measurable_const.mul (measurable_real_pivotal e o p)).aestronglyMeasurable
    · intro e
      filter_upwards [hfin e] with ω hω
      refine mul_nonneg (hrk e) (sub_nonneg.2 ?_)
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg
        (ENNReal.toReal_mono hω (encard_cluster_sdiff_le_insert_coe ω e o)) p
    · intro e
      exact measurable_pivotal e o p
    · intro e
      filter_upwards [hfin e] with ω hω
      rw [ENNReal.ofReal_mul (hrk e),
        ofReal_toReal_pow_sub_pow (encard_cluster_sdiff_le_insert_coe ω e o) hω p]
  refine hmain.trans (tsum_congr fun e => ?_)
  rw [integral_const_mul]

/-! ### The hypothesis in the shape of the paper's `ℝ≥0∞` flux -/

open Classical in
/-- **The `ℝ≥0∞` flux series is the `ℝ≥0∞` integral of the pointwise flux** (Tonelli).

This is the bridge that makes the hypothesis of `integral_tsum_closed_pivotal_real`
recognisable: the left-hand side is the series of per-pair `ℝ≥0∞` fluxes, the right-hand side
is the `ℝ≥0∞` pivotal flux integral `∫⁻ ω, ∑' e, …` of Lemma I.4.1 (the left-hand side of
`i41_enn_of_root_finite`, with the weight and the root `o` generalised). -/
theorem tsum_lintegral_closed_pivotal (μ : Measure (Config (Fin d → ℤ)))
    (p : ℕ) (o : Fin d → ℤ) (w : Sym2 (Fin d → ℤ) → ℝ≥0∞) :
    (∑' e, w e * ∫⁻ ω, (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∫⁻ ω, ∑' e, w e * (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ := by
  rw [lintegral_tsum]
  · exact tsum_congr fun e =>
      (lintegral_const_mul (w e) (measurable_closed_pivotal e o p)).symm
  · intro e
    exact (measurable_const.mul (measurable_closed_pivotal e o p)).aemeasurable

open Classical in
/-- **The closed-coordinate interchange with the finiteness hypothesis in the paper's shape.**

Same statement as `integral_tsum_closed_pivotal_real`, but the finiteness input is now
`hflux : ∫⁻ ω, ∑' e, … ≠ ⊤`, i.e. *the pivotal flux integral of Lemma I.4.1 is finite* —
the same object that the extended-nonnegative identity `i41_enn_of_root_finite` computes. -/
theorem integral_tsum_closed_pivotal_real_of_lintegral (μ : Measure (Config (Fin d → ℤ)))
    (p : ℕ) (o : Fin d → ℤ) (rk : Sym2 (Fin d → ℤ) → ℝ) (hrk : ∀ e, 0 ≤ rk e)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : (∫⁻ ω, ∑' e, ENNReal.ofReal (rk e) * (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤) :
    ∫ ω, (∑' e, rk e * (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ
      = ∑' e, rk e * ∫ ω, (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ :=
  integral_tsum_closed_pivotal_real μ p o rk hrk hfin
    ((tsum_lintegral_closed_pivotal μ p o (fun e => ENNReal.ofReal (rk e))).trans_ne hflux)


/-! ### The `Summable` form, matching `hasSum_integral_of_summable_integral_norm` -/

/-- **The interchange from `L¹`-norm summability, in the `Summable` normalisation.**

This is the same conclusion as `integral_tsum_of_nonneg_of_lintegral_tsum_ne_top`, but with
the hypothesis in the shape used by `hasSum_integral_of_summable_integral_norm`: individual
integrability plus `Summable (fun e => ∫ ω, ‖F e ω‖ ∂μ)`.  Nothing here is nonnegative, so this
is the general form; the proof is exactly Mathlib's dominated convergence for series.  It is
this hypothesis — summability of the family of *`L¹` norms* — that `hKd` would have to supply
and does not: `hKd` bounds `∑_{e ∈ S} |rk e * ∫ g_e|`, i.e. absolute values *after*
integrating. -/
theorem integral_tsum_of_summable_integral_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Countable ι] {F : ι → α → ℝ}
    (hint : ∀ e, Integrable (F e) μ)
    (hsum : Summable fun e => ∫ ω, ‖F e ω‖ ∂μ) :
    (∑' e, ∫ ω, F e ω ∂μ) = ∫ ω, ∑' e, F e ω ∂μ :=
  (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq

open Classical in
/-- **The cutoff derivative's series is the integral of the pointwise closed-coordinate flux.**

This composes the summed closed-coordinate rewrite `tsum_cutoff_pivotal_eq_closed_pow` with the
integral/sum interchange `integral_tsum_closed_pivotal_real_of_lintegral`.  The result is the
shape in which Lemma I.4.1 states its right-hand side — the profile rate `β |K'(r)|` times an
*expectation of a pointwise sum over pairs*, rather than a series of per-pair expectations.

Inputs, all explicit:

* `hcw`, `hfin`, `hint`: the inputs of `tsum_cutoff_pivotal_eq_closed_pow`; `hfin`/`hint`
  concern the cluster of `o` after opening a pair and are derivable from per-vertex moments via
  `tsum_cutoff_pivotal_eq_closed_pow_of_vertexMoments`;
* `hflux`: finiteness of the paper's `ℝ≥0∞` pivotal flux `∫⁻ ω, ∑' e, J_r(e) 1(e ∉ ω) (…)`,
  the object that `i41_enn_of_root_finite` computes and that any passage of the identity through
  `ENNReal.toReal` must assume.  It is *not* implied by `hKd`. -/
theorem tsum_cutoff_pivotal_eq_integral_closed {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β)))
    (hflux : (∫⁻ ω, ∑' e,
        ENNReal.ofReal (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤) :
    (∑' e, cw e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      = ((β : ℝ) * -K' r) *
        ∫ ω, (∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          (if e ∈ ω then 0 else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  let rk : Sym2 (Fin d → ℤ) → ℝ :=
    fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ)
  have hrk : ∀ e, 0 ≤ rk e := fun e => by positivity
  have hflux' : (∫⁻ ω, ∑' e, ENNReal.ofReal (rk e) * (if e ∈ ω then 0 else
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p))
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤ := by
    simpa only [rk] using hflux
  refine (tsum_cutoff_pivotal_eq_closed_pow (N := N) (K := K) (K' := K') p β r o cw
    hcw hfin hint).trans ?_
  rw [← integral_tsum_closed_pivotal_real_of_lintegral
    (μ := law (intensityProfile (cutoffKernel N K r) β)) p o rk hrk hfin hflux']

end PercLib.Models.LongRange

namespace PercLib.Analysis

/-- If every finite sum of absolute real contributions is bounded and the extended-nonnegative
terms are finite, then the extended-nonnegative series is finite. -/
theorem tsum_ofReal_mul_ne_top_of_real_bound {ι : Type*} (rk : ι → ℝ) (hrk : ∀ e, 0 ≤ rk e)
    (q : ι → ℝ≥0∞) (hq : ∀ e, q e ≠ ⊤) (Kd : ℝ)
    (hbound : ∀ S : Finset ι, ∑ e ∈ S, |rk e| * |(q e).toReal| ≤ Kd) :
    (∑' e, ENNReal.ofReal (rk e) * q e) ≠ ⊤ := by
  have hnn : ∀ e, 0 ≤ |rk e| * |(q e).toReal| := fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsumm : Summable (fun e => |rk e| * |(q e).toReal|) :=
    summable_of_sum_le hnn hbound
  have hpt : ∀ e, ENNReal.ofReal (rk e) * q e =
      ENNReal.ofReal (|rk e| * |(q e).toReal|) := by
    intro e
    rw [abs_of_nonneg (hrk e), abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_mul (hrk e), ENNReal.ofReal_toReal (hq e)]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal Kd) ENNReal.ofReal_ne_top ?_
  calc (∑' e, ENNReal.ofReal (rk e) * q e)
      = ENNReal.ofReal (∑' e, |rk e| * |(q e).toReal|) := by
        rw [ENNReal.ofReal_tsum_of_nonneg hnn hsumm]
        exact tsum_congr hpt
    _ ≤ ENNReal.ofReal Kd := ENNReal.ofReal_le_ofReal (Real.tsum_le_of_sum_le hnn hbound)


end PercLib.Analysis


/-! ### The real binomial identity and its analytic assembly -/

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### `toReal` of an indicator -/

/-- `toReal` of the closed-event indicator of the root cluster, in the value `1` form used by
the ordered sum of Lemma I.4.1. -/
theorem toReal_indicator_one_compl_conn (ω : Config (Fin d → ℤ)) (y : Fin d → ℤ) :
    (((conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω).toReal) =
      (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω := by
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

/-- `toReal` of a `{0,1}`-valued ball indicator. -/
theorem toReal_ite_one_zero {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} (y : Fin d → ℤ) :
    (((if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0)).toReal) =
      (if N (Int.cast ∘ y) ≤ r then (1 : ℝ) else 0) := by
  split_ifs <;> simp

/-! ### The pointwise `toReal` bridge for the ordered right-hand side -/

/-- Under finiteness of the clusters of the closed ball `B_r` off the root cluster, every summand
of the ordered `ℝ≥0∞` sum of Lemma I.4.1 is finite, so `ENNReal.tsum_toReal_eq` applies to it. -/
theorem ne_top_summand_of_ball_finite {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p ℓ : ℕ}
    {ω : Config (Fin d → ℤ)}
    (hball : ∀ y : Fin d → ℤ, N (Int.cast ∘ y) ≤ r → ω ∉ conn 0 y →
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (y : Fin d → ℤ) :
    (if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
        (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) ≠ ⊤ := by
  classical
  by_cases hy : N (Int.cast ∘ y) ≤ r
  · by_cases hc : ω ∈ (conn 0 y)ᶜ
    · rw [ite_eq_left hy, Set.indicator_of_mem hc]
      simpa using ENNReal.pow_ne_top (hball y hy hc)
    · rw [Set.indicator_of_notMem hc]
      simp
  · rw [ite_eq_right hy]
    simp

/-- **Pointwise `toReal` of the ordered right-hand side of Lemma I.4.1.**

The right-hand side of the extended-nonnegative identity at a fixed configuration `ω` is the
product of the root-cluster moment `|K_0|^{ℓ+1}` and the ordered sum over `y`.  Its `toReal`
is the paper's real expression

`|K_0|^{ℓ+1} ∑_y 1(‖y‖ ≤ r) 1(y ∉ K_0) |K_y|^{p−ℓ}`,

where `|K_y|` is `ℝ≥0∞`-`toReal`, i.e. the `ncard` of the cluster.

The only hypothesis is finiteness of the clusters of the ball points that are not in the root
cluster: the inner `toReal` of a `tsum` is the `tsum` of the `toReal`s only when every summand is
finite, and a summand carrying `|K_y| = ⊤` with `y ∉ K_0` in the ball is `⊤`, whose `toReal` is
`0`.  Summands with `y` outside the ball, or with `y ∈ K_0`, are already `0` in `ℝ≥0∞` and need
no hypothesis on `|K_y|`; hence finiteness of *all* ball clusters (the stronger hypothesis used
by `i41_real_of_root_finite`'s derivation) is more than is needed. -/
theorem toReal_ordered_rhs_of_ball_finite {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p ℓ : ℕ}
    {ω : Config (Fin d → ℤ)}
    (hball : ∀ y : Fin d → ℤ, N (Int.cast ∘ y) ≤ r → ω ∉ conn 0 y →
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤) :
    (((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        ∑' y, (if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)).toReal
      = (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        ∑' y, (if N (Int.cast ∘ y) ≤ r then (1 : ℝ) else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
          (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ) := by
  classical
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.tsum_toReal_eq
    (fun y => ne_top_summand_of_ball_finite (p := p) (ℓ := ℓ) hball y)]
  refine congrArg (fun t => (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) * t) ?_
  refine tsum_congr fun y => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_ite_one_zero (N := N) (r := r) y, toReal_indicator_one_compl_conn ω y]

/-! ### Measurability of the pivotal flux series -/

open Classical in
/-- The `ℝ≥0∞` pivotal flux series of the cut-off family is measurable in the configuration. -/
theorem measurable_pivotal_series {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} (p : ℕ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      ∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) := by
  classical
  refine Measurable.tsum fun e => ?_
  refine measurable_const.mul ?_
  refine Measurable.ite (measurableSet_mem e) measurable_const ?_
  exact ((measurable_encard_cluster_insert_coe e 0).pow_const p).sub
    ((measurable_encard_cluster_coe 0).pow_const p)

/-! ### The real binomial expectation identity -/

open Classical in
/-- **Lemma I.4.1 as a real expectation identity, in the paper's binomial form.**

Under translation invariance of the law, almost-sure finiteness of the root cluster (the input
`i41_enn_of_root_finite` needs, and which `i41_binomial_of_root_moment` weakens to a finite root
moment), the corner hypothesis, and finiteness of the cut-off pivotal flux series at `r`, the
real integral of the pivotal flux series is the paper's binomial sum of real expectations

`∑_{ℓ<p} C(p,ℓ) ∫ |K_0|^{ℓ+1} ∑_{y ∈ B_r} 1(y ∉ K_0) |K_y|^{p−ℓ}`

at the origin, with `|K|` the `toReal` cluster volume (`ncard`).

The only finiteness input beyond root-cluster finiteness is `hflux`, and it supplies every
`toReal` passage consumed below.

* It makes the pivotal series finite at almost every configuration (`MeasureTheory.ae_lt_top`),
  so the left side is the `toReal` of a finite `ℝ≥0∞` integral.
* Through the extended-nonnegative identity itself it makes every `ℓ`-th ordered moment
  integral finite (`lintegral_ordered_rhs_ne_top_of_flux`), hence every `ℓ`-th right-hand
  integrand finite almost everywhere.
* Reading that a.e. finiteness at `ℓ = 0` forces every cluster of a ball point that is *not*
  in the root cluster to be finite almost everywhere: such a cluster would make the summand
  `⊤` (`ordered_rhs_eq_top_of_ball_cluster_top`) and hence the integrand `⊤`.  This is exactly
  what `ENNReal.tsum_toReal_eq` needs in order to move the `toReal` inside the ordered sum over
  `y`; without it `(⊤).toReal = 0` would silently replace an infinite cluster volume by `0`.
  Vertices outside the ball never matter, because the ball indicator kills their summands in
  `ℝ≥0∞` before any `toReal` is taken.

So the hypothesis bundle is exactly the extended-nonnegative one plus `1 ≤ p`: no separate
cluster-finiteness assumption is needed, and `hflux` is not removable
(`lintegral_pivotal_eq_top_of_ball_cluster_top`).  Root-cluster finiteness is used only through
`i41_enn_of_root_finite`; the pointwise `toReal` step on the right-hand side needs no finiteness
of `K_0`. -/
theorem i41_real_of_root_finite {d : ℕ} (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p : ℕ} {u v : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (hp : 1 ≤ p)
    (hflux : (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤) :
    (∫ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)).toReal ∂μ)
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y : Fin d → ℤ,
            (if N (Int.cast ∘ y) ≤ r then (1 : ℝ) else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ)) ∂μ := by
  classical
  set P : Config (Fin d → ℤ) → ℝ≥0∞ := fun ω => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
        (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p) with hPdef
  set A : ℕ → Config (Fin d → ℤ) → ℝ≥0∞ := fun ℓ ω =>
      ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) with hAdef
  set R : ℕ → Config (Fin d → ℤ) → ℝ := fun ℓ ω =>
      (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if N (Int.cast ∘ y) ≤ r then (1 : ℝ) else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ)) with hRdef
  have hflux' : (∫⁻ ω, P ω ∂μ) ≠ ⊤ := hflux
  have hPmeas : Measurable P := measurable_pivotal_series (N := N) (r := r) p
  have hENN : ∫⁻ ω, P ω ∂μ =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ∫⁻ ω, A ℓ ω ∂μ :=
    i41_enn_of_root_finite μ hμ hfin hcorner hr
  have hsumne : (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ∫⁻ ω, A ℓ ω ∂μ) ≠ ⊤ := by
    rw [← hENN]; exact hflux'
  have hterm : ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ∫⁻ ω, A ℓ ω ∂μ ≠ ⊤ :=
    ENNReal.sum_ne_top.mp hsumne
  have hAint : ∀ ℓ ∈ Finset.range p, (∫⁻ ω, A ℓ ω ∂μ) ≠ ⊤ := by
    intro ℓ hℓ
    by_contra h
    have hlt : ℓ < p := Finset.mem_range.mp hℓ
    have hc : (p.choose ℓ : ℝ≥0∞) ≠ 0 := by
      have hpos : 0 < p.choose ℓ := Nat.choose_pos (by omega)
      exact_mod_cast hpos.ne'
    exact hterm ℓ hℓ (by rw [h, ENNReal.mul_top hc])
  have htsum : ∀ ℓ : ℕ, Measurable fun ω : Config (Fin d → ℤ) =>
      ∑' y : Fin d → ℤ,
        (if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) := by
    intro ℓ
    refine Measurable.tsum fun y => ?_
    exact (measurable_const.mul
      (measurable_const.indicator (measurableSet_conn 0 y).compl)).mul
      ((measurable_encard_cluster_coe y).pow_const (p - ℓ))
  have hAmeas : ∀ ℓ : ℕ, Measurable (A ℓ) := fun ℓ =>
    ((measurable_encard_cluster_coe 0).pow_const (ℓ + 1)).mul (htsum ℓ)
  have hAae : ∀ ℓ ∈ Finset.range p, ∀ᵐ ω ∂μ, A ℓ ω ≠ ⊤ := by
    intro ℓ hℓ
    filter_upwards [ae_lt_top (hAmeas ℓ) (hAint ℓ hℓ)] with ω hω
    exact hω.ne
  have hPae : ∀ᵐ ω ∂μ, P ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hPmeas hflux'] with ω hω
    exact hω.ne
  have hAae0 : ∀ᵐ ω ∂μ, A 0 ω ≠ ⊤ := hAae 0 (Finset.mem_range.mpr hp)
  have hball_ae : ∀ᵐ ω ∂μ, ∀ y : Fin d → ℤ, N (Int.cast ∘ y) ≤ r → ω ∉ conn 0 y →
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [hAae0] with ω hω
    intro y hy hconn htop
    refine hω ?_
    have hsummand : (if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
        (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ (p - 0) = ⊤ := by
      rw [ite_eq_left hy, Set.indicator_of_mem hconn, htop,
        ENNReal.top_pow (show p - 0 ≠ 0 by omega)]
      simp
    have h1 : (1 : ℝ≥0∞) ≤ ((cluster ω 0).encard : ℝ≥0∞) ^ (0 + 1) :=
      one_le_pow₀ (by exact_mod_cast one_le_encard_cluster ω 0)
    have h2 : ((if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - 0)) ≤
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - 0)) :=
      ENNReal.le_tsum (f := fun z : Fin d → ℤ =>
        (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
          (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω z).encard : ℝ≥0∞) ^ (p - 0)) y
    refine le_antisymm le_top ?_
    calc (⊤ : ℝ≥0∞) = (1 : ℝ≥0∞) *
          ((if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - 0)) := by rw [hsummand, one_mul]
      _ ≤ ((cluster ω 0).encard : ℝ≥0∞) ^ (0 + 1) *
          (∑' z : Fin d → ℤ,
            (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
              (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω z).encard : ℝ≥0∞) ^ (p - 0)) := mul_le_mul' h1 h2
      _ = A 0 ω := rfl
  calc ∫ ω, (P ω).toReal ∂μ
      = (∫⁻ ω, P ω ∂μ).toReal :=
        integral_toReal_eq_toReal_lintegral hPmeas.aemeasurable hPae
    _ = (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ∫⁻ ω, A ℓ ω ∂μ).toReal := by
        rw [hENN]
    _ = ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℝ≥0∞) * ∫⁻ ω, A ℓ ω ∂μ).toReal :=
        ENNReal.toReal_sum hterm
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * (∫⁻ ω, A ℓ ω ∂μ).toReal := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω, (A ℓ ω).toReal ∂μ := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [integral_toReal_eq_toReal_lintegral (hAmeas ℓ).aemeasurable (hAae ℓ hℓ)]
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω, R ℓ ω ∂μ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [integral_congr_ae]
        filter_upwards [hball_ae] with ω hb
        exact toReal_ordered_rhs_of_ball_finite (N := N) (r := r) (p := p) (ℓ := ℓ) hb

/-! ### Sharpness: the a.e.-finiteness of the ball clusters is not removable -/

open Classical in
/-- **An infinite ball cluster outside the root cluster makes the `ℓ`-th ordered integrand
infinite.**

If `y` is a lattice point of the closed ball `B_r`, is not connected to the origin, and its
cluster is infinite, then for every `ℓ < p` the `ℓ`-th `ℝ≥0∞` integrand of the binomial form of
Lemma I.4.1 is `⊤`: the summand of `y` is `⊤` because `|K_y|^{p−ℓ}` is an infinite power
`p − ℓ ≥ 1`, and it is not killed by `1(y ∉ K_0)`.  Consequently its `toReal` is `0`, while the
honest real cluster volume of `K_y` is infinite.

This is precisely the pointwise reason for the hypothesis `hball` of `i41_real_of_root_finite`:
`toReal` silently replaces an infinite cluster volume by `0`, so the real identity cannot hold
without almost-sure finiteness of the clusters that appear in the ball. -/
theorem ordered_rhs_eq_top_of_ball_cluster_top {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p ℓ : ℕ}
    {ω : Config (Fin d → ℤ)} {y : Fin d → ℤ}
    (hy : N (Int.cast ∘ y) ≤ r) (hconn : ω ∉ conn 0 y) (hℓ : ℓ < p)
    (hKy : ((cluster ω y).encard : ℝ≥0∞) = ⊤) :
    ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) = ⊤ := by
  classical
  have hterm : (if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
      (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) = ⊤ := by
    rw [ite_eq_left hy, Set.indicator_of_mem hconn, hKy, ENNReal.top_pow (by omega)]
    simp
  have h1 : (1 : ℝ≥0∞) ≤ ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) :=
    one_le_pow₀ (by exact_mod_cast one_le_encard_cluster ω 0)
  refine le_antisymm le_top ?_
  calc (⊤ : ℝ≥0∞) = (1 : ℝ≥0∞) *
        ((if N (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) := by rw [hterm, one_mul]
    _ ≤ ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) :=
        mul_le_mul' h1 (ENNReal.le_tsum (f := fun z : Fin d → ℤ =>
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) y)

open Classical in
/-- **The `ℓ`-th ordered `ℝ≥0∞` moment integral is infinite whenever a ball cluster is infinite
with positive probability.**

Consequently the finiteness hypothesis `hball` of `i41_real_of_root_finite` is a necessary
condition for its conclusion: through the extended-nonnegative identity `∫⁻ P = ∑_ℓ C ∫⁻ A_ℓ`,
an infinite ball cluster forces the `ℝ≥0∞` pivotal-flux integral to be `⊤` (that is, `hflux`
fails), and simultaneously forces `(∫⁻ A_ℓ).toReal = 0` while the real integrand
`(A_ℓ).toReal = 0` still holds pointwise, so the `toReal` passage carries no information.

No finiteness of the root cluster, and no moment hypothesis, is used. -/
theorem lintegral_ordered_rhs_eq_top_of_ball_cluster_top
    (μ : Measure (Config (Fin d → ℤ))) {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p ℓ : ℕ}
    {y : Fin d → ℤ} (hy : N (Int.cast ∘ y) ≤ r) (hℓ : ℓ < p)
    (hpos : μ {ω : Config (Fin d → ℤ) |
      ((cluster ω y).encard : ℝ≥0∞) = ⊤ ∧ ω ∉ conn 0 y} ≠ 0) :
    (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ) = ⊤ := by
  classical
  set S : Set (Config (Fin d → ℤ)) :=
    {ω | ((cluster ω y).encard : ℝ≥0∞) = ⊤ ∧ ω ∉ conn 0 y} with hS
  have hSmeas : MeasurableSet S :=
    ((measurable_encard_cluster_coe y) (measurableSet_singleton ⊤)).inter
      (measurableSet_conn 0 y).compl
  have hle : ∫⁻ ω, S.indicator (fun _ => (⊤ : ℝ≥0∞)) ω ∂μ ≤
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ := by
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact le_of_eq (ordered_rhs_eq_top_of_ball_cluster_top hy hω.2 hℓ hω.1).symm
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  rw [lintegral_indicator_const hSmeas, ENNReal.top_mul hpos] at hle
  exact le_antisymm le_top hle

/-! ### What the pivotal-flux bound supplies -/

open Classical in
/-- **The `ℝ≥0∞` pivotal-flux bound supplies finiteness of every `ℓ`-th ordered moment integral.**

This is the exact content of `hflux` for the right-hand side, and it is all the right-hand side
gets from the flux bound.  It is *not* a.e. finiteness of the integrands: a finite `ℝ≥0∞`
integral only forces the integrand to be finite almost everywhere, and the individual cluster
volumes `|K_y|` cannot be recovered from it — see
`ordered_rhs_eq_top_of_ball_cluster_top` and
`lintegral_ordered_rhs_eq_top_of_ball_cluster_top`, which show that a single infinite ball
cluster off the root cluster makes the very same integral `⊤`. -/
theorem lintegral_ordered_rhs_ne_top_of_flux {d : ℕ} (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p : ℕ} {u v : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (hflux : (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤) :
    ∀ ℓ ∈ Finset.range p,
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ) ≠ ⊤ := by
  classical
  have hENN : (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ) =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' z : Fin d → ℤ,
            (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
              (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ :=
    i41_enn_of_root_finite μ hμ hfin hcorner hr
  have hsumne : (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ) ≠ ⊤ := by
    rw [← hENN]; exact hflux
  intro ℓ hℓ
  by_contra h
  refine ENNReal.sum_ne_top.mp hsumne ℓ hℓ ?_
  have hlt : ℓ < p := Finset.mem_range.mp hℓ
  have hc : (p.choose ℓ : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < p.choose ℓ := Nat.choose_pos (by omega)
    exact_mod_cast hpos.ne'
  rw [h, ENNReal.mul_top hc]

open Classical in
/-- **Positive probability of an infinite ball cluster makes the `ℝ≥0∞` pivotal-flux integral
infinite.**

This closes the sharpness loop for `i41_real_of_root_finite`: a single lattice point `y` of the
closed ball `B_r`, not connected to the origin, whose cluster is infinite on a set of
configurations of positive measure already forces the extended-nonnegative pivotal-flux integral
to be `⊤`.  That is exactly the hypothesis `hflux` of the real identity, so `hflux` cannot hold
in that situation, and the a.e. finiteness of the ball clusters that the `toReal` passage needs
is a genuine consequence of `hflux` rather than an extra assumption. -/
theorem lintegral_pivotal_eq_top_of_ball_cluster_top {d : ℕ}
    (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ t : Fin d → ℤ,
      μ.map (fun ω => Sym2.map (fun x : Fin d → ℤ => x + t) '' ω) = μ)
    (hfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0)
    {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} {p : ℕ} {u v : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v) (hp : 1 ≤ p)
    {y : Fin d → ℤ} (hy : N (Int.cast ∘ y) ≤ r)
    (hpos : μ {ω : Config (Fin d → ℤ) |
      ((cluster ω y).encard : ℝ≥0∞) = ⊤ ∧ ω ∉ conn 0 y} ≠ 0) :
    (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ) = ⊤ := by
  classical
  have hA0 : (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (0 + 1) *
      (∑' z : Fin d → ℤ,
        (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
          (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω z).encard : ℝ≥0∞) ^ (p - 0)) ∂μ) = ⊤ :=
    lintegral_ordered_rhs_eq_top_of_ball_cluster_top μ hy (by omega) hpos
  have hterm : (p.choose 0 : ℝ≥0∞) *
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (0 + 1) *
        (∑' z : Fin d → ℤ,
          (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω z).encard : ℝ≥0∞) ^ (p - 0)) ∂μ) = ⊤ := by
    rw [Nat.choose_zero_right, Nat.cast_one, one_mul, hA0]
  rw [i41_enn_of_root_finite μ hμ hfin hcorner hr]
  refine le_antisymm le_top ?_
  calc (⊤ : ℝ≥0∞) = (p.choose 0 : ℝ≥0∞) *
        (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (0 + 1) *
          (∑' z : Fin d → ℤ,
            (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
              (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω z).encard : ℝ≥0∞) ^ (p - 0)) ∂μ) := hterm.symm
    _ ≤ ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' z : Fin d → ℤ,
            (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
              (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ :=
        Finset.single_le_sum (f := fun ℓ => (p.choose ℓ : ℝ≥0∞) *
          ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
            (∑' z : Fin d → ℤ,
              (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) *
                (conn 0 z)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
                ((cluster ω z).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ)
          (fun _ _ => zero_le) (Finset.mem_range.mpr hp)

/-! ### Non-vacuity of the hypothesis bundle -/

open Classical in
/-- **The hypothesis bundle of `i41_real_of_root_finite` is satisfiable.**

Take the one-dimensional lattice, the Dirac law at the empty configuration (which is invariant
under every shift, since the shift map fixes `∅`), `p = 1` and `r = 1/2` with the corner
window `(1/4, 3/4)`.  Every cluster of the empty configuration is a singleton
(`cluster_empty`), so the root cluster is finite; an integer vector has sup-norm `0` or at least
`1`, so no lattice displacement has norm in `(1/4, 3/4)`; and the cut-off weight
`1{N(e) < 1/2}` vanishes on every pair, because a non-diagonal pair has norm at least `1` and a
loop carries weight `0` by the loop convention.  Hence the pivotal flux series is identically
`0`, its `ℝ≥0∞` integral is finite, and the real identity is the genuine statement `0 = 0` for
this law.

This guards against the identity being vacuous through an unsatisfiable flux hypothesis. -/
theorem i41_real_dirac_empty :
    (∫ ω : Config (Fin 1 → ℤ), (∑' e : Sym2 (Fin 1 → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
            (fun s => if s < 1 / 2 then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ 1 -
              ((cluster ω 0).encard : ℝ≥0∞) ^ 1)).toReal
        ∂(Measure.dirac (∅ : Config (Fin 1 → ℤ))))
      = ∑ ℓ ∈ Finset.range 1, ((1 : ℕ).choose ℓ : ℝ) *
        ∫ ω : Config (Fin 1 → ℤ),
          (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin 1 → ℤ,
              (if (normSeminorm ℝ (Fin 1 → ℝ)) (Int.cast ∘ y) ≤ 1 / 2 then (1 : ℝ) else 0) *
                (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
                (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (1 - ℓ))
          ∂(Measure.dirac (∅ : Config (Fin 1 → ℤ))) := by
  classical
  have hshift : ∀ t : Fin 1 → ℤ,
      (Measure.dirac (∅ : Config (Fin 1 → ℤ))).map
        (fun ω => Sym2.map (fun x : Fin 1 → ℤ => x + t) '' ω) =
        Measure.dirac (∅ : Config (Fin 1 → ℤ)) := by
    intro t
    rw [Measure.map_dirac]
    simp
  have hrootfin : (Measure.dirac (∅ : Config (Fin 1 → ℤ)))
      {ω : Config (Fin 1 → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0 := by
    rw [Measure.dirac_apply]
    simp [cluster_empty]
  have hcorner : ∀ z : Fin 1 → ℤ,
      (normSeminorm ℝ (Fin 1 → ℝ)) (Int.cast ∘ z) ∉ Ioo (1 / 4) (3 / 4) := by
    intro z hz
    rw [normSeminorm_fin_one_intCast] at hz
    rcases eq_or_ne (z 0).natAbs 0 with h0 | h0
    · rw [h0] at hz; norm_num at hz
    · have hgeNat : 1 ≤ (z 0).natAbs := by omega
      have h1 : (1 : ℝ) ≤ ((z 0).natAbs : ℝ) := by exact_mod_cast hgeNat
      linarith [hz.2]
  have hrk : ∀ e : Sym2 (Fin 1 → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (fun s => if s < 1 / 2 then 1 else 0) e : ℝ≥0) : ℝ≥0∞) = 0 := by
    intro e
    refine Sym2.inductionOn e fun x y => ?_
    by_cases hxy : x = y
    · subst y
      rw [radialKernel_diag]
      simp
    · have hlt : ¬ (normSeminorm ℝ (Fin 1 → ℝ)) (Int.cast ∘ (x - y)) < 1 / 2 := by
        rw [normSeminorm_fin_one_intCast]
        have hne : x 0 - y 0 ≠ 0 := by
          intro hzero
          apply hxy
          funext i
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          exact sub_eq_zero.mp hzero
        have hpos : 0 < ((x - y) 0).natAbs := Int.natAbs_pos.mpr hne
        have hge : (1 : ℝ) ≤ (((x - y) 0).natAbs : ℝ) := by exact_mod_cast hpos
        linarith
      have h0 : radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (fun s => if s < 1 / 2 then 1 else 0) s(x, y) = 0 :=
        NNReal.coe_eq_zero.mp (radialKernel_indicator_eq_zero_of_not_lt hlt)
      rw [h0]
      simp
  have hflux : (∫⁻ ω : Config (Fin 1 → ℤ), (∑' e : Sym2 (Fin 1 → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (fun s => if s < 1 / 2 then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
        (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ 1 -
            ((cluster ω 0).encard : ℝ≥0∞) ^ 1))
      ∂(Measure.dirac (∅ : Config (Fin 1 → ℤ)))) ≠ ⊤ := by
    have hzero : (∑' e : Sym2 (Fin 1 → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
            (fun s => if s < 1 / 2 then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ (∅ : Config (Fin 1 → ℤ)) then (0 : ℝ≥0∞) else
            ((cluster (insert e (∅ : Config (Fin 1 → ℤ))) 0).encard : ℝ≥0∞) ^ 1 -
              ((cluster (∅ : Config (Fin 1 → ℤ)) 0).encard : ℝ≥0∞) ^ 1)) = 0 := by
      have hfun : (fun e : Sym2 (Fin 1 → ℤ) =>
          ((radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
              (fun s => if s < 1 / 2 then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
            (if e ∈ (∅ : Config (Fin 1 → ℤ)) then (0 : ℝ≥0∞) else
              ((cluster (insert e (∅ : Config (Fin 1 → ℤ))) 0).encard : ℝ≥0∞) ^ 1 -
                ((cluster (∅ : Config (Fin 1 → ℤ)) 0).encard : ℝ≥0∞) ^ 1)) =
          fun _ => (0 : ℝ≥0∞) := by
        funext e
        rw [hrk e, zero_mul]
      rw [hfun, tsum_zero]
    rw [lintegral_dirac' _ (measurable_pivotal_series
      (N := normSeminorm ℝ (Fin 1 → ℝ)) (r := (1 / 2 : ℝ)) 1)]
    intro htop
    simp only [Set.mem_empty_iff_false, ↓reduceIte] at hzero htop
    exact ENNReal.zero_ne_top (hzero.symm.trans htop)
  exact i41_real_of_root_finite (d := 1) (Measure.dirac (∅ : Config (Fin 1 → ℤ)))
    hshift hrootfin hcorner ⟨by norm_num, by norm_num⟩ (le_refl 1) hflux


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-! ### Discharging the finiteness hypothesis from the library's `hKd` bound -/

open Classical in
/-- **The per-pair closed/pivotal relation in the orientation `summable_closed_flux_of_hKd`
consumes it.**

`cutoff_pivotal_eq_closed_pow` states `(r k e · w) · ∫ pivotal = w · ∫ closed` with
`w = β (-K'(r)) exp(-β J_r(e))`.  Because the cutoff weight `r k e` is `{0,1}`-valued
(`radialKernel_indicator_eq_zero_or_one`), the *unit* case gives
`∫ closed = exp(-β J_r(e)) ∫ pivotal`, whence
`r k e ∫ closed = (β (-K'(r)))⁻¹ (cw e ∫ pivotal)`, and both sides vanish when `r k e = 0`.
This is the `hpair` input of `summable_closed_flux_of_hKd`, here derived rather than assumed;
the only extra input is `β (-K'(r)) ≠ 0`, which any derivative formula needs anyway. -/
theorem radialKernel_mul_integral_closed_eq {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hK' : (β : ℝ) * -K' r ≠ 0)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β))) :
    ∀ e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ∫ ω, (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ((β : ℝ) * -K' r)⁻¹ * (cw e *
        ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) := by
  intro e
  rcases radialKernel_indicator_eq_zero_or_one N r e with h | h
  · -- the pair is inactive: both sides carry the vanishing factor `cw e`
    have hcw0 : cw e = 0 := by rw [hcw e, h]; ring
    rw [h, hcw0]
    ring
  · -- the pair is active: divide the per-pair identity by `β (-K'(r))`
    have hz := cutoff_pivotal_eq_closed_pow (K := K) (K' := K') p β r e o
      (by rw [h]; norm_num) (hfin e) (hint e)
    simp only [h, one_mul] at hz
    have hsplit : Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
        ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) =
        ∫ ω, (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
      refine mul_left_cancel₀ hK' ?_
      rw [← hz]
      ring
    rw [hcw e, h, one_mul, one_mul, ← hsplit]
    conv_rhs => rw [show ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))) *
      ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ((β : ℝ) * -K' r) * (Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
        ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β))) from by ring]
    rw [inv_mul_cancel_left₀ hK']

open Classical in
/-- **The closed-coordinate integral/sum interchange with only the library's `hKd` input.**

This is `integral_tsum_closed_pivotal_real` with its `ℝ≥0∞` flux finiteness hypothesis replaced
by the cutoff dominator `hKd` of `hasDerivAt_integral_cutoff_pow` (together with the per-pair
inputs `hfin`/`hint` and `β (-K'(r)) ≠ 0`).  The route is:

* `radialKernel_mul_integral_closed_eq` turns `hKd` (which bounds
  `∑_{e ∈ S} |cw e · ∫ pivotal|`) into the absolute summability
  `∑' e, r k e ∫ closed < ∞` supplied by `summable_closed_flux_of_hKd`;
* `hint` makes each pair integrable, so that `∑' e, ∫ ‖…‖` *is* that sum;
* `integral_tsum_of_summable_integral_norm` (dominated convergence for series) then gives the
  interchange.

So in the paper's model the interchange needs nothing beyond `hKd` and the per-pair
integrability of the inserted `p`-th moment — in particular no summability hypothesis on the
closed-coordinate flux has to be assumed separately. -/
theorem integral_tsum_closed_pivotal_real_of_hKd {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hK' : (β : ℝ) * -K' r ≠ 0)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β)))
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd) :
    ∫ ω, (∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K r) β)
  let rk : Sym2 (Fin d → ℤ) → ℝ :=
    fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ)
  have hrk : ∀ e, 0 ≤ rk e := fun e => by positivity
  have hsumm : Summable fun e => rk e *
      ∫ ω, (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
    refine (summable_closed_flux_of_hKd (N := N) (K := K) (K' := K') p β r o cw Kd
      ?_ ?_).1
    · exact hKd
    · intro e
      exact radialKernel_mul_integral_closed_eq (N := N) (K := K) (K' := K') p β r o cw
        hcw hK' hfin hint e
  have hInt : ∀ e, Integrable (fun ω => rk e * (if e ∈ ω then 0 else
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) μ := by
    intro e
    refine Integrable.mono' ((hint e).const_mul (rk e))
      (measurable_const.mul (measurable_real_closed_pivotal e o p)).aestronglyMeasurable ?_
    filter_upwards [hfin e] with ω hω
    have hnn : 0 ≤ (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) := by
      split_ifs with he
      · exact le_refl 0
      · exact sub_nonneg.2 (pow_le_pow_left₀ ENNReal.toReal_nonneg
          (ENNReal.toReal_mono hω (encard_cluster_le_insert_coe ω e o)) p)
    have hle : (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ≤
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p := by
      split_ifs with he
      · exact pow_nonneg ENNReal.toReal_nonneg p
      · exact sub_le_self _ (pow_nonneg ENNReal.toReal_nonneg p)
    rw [Real.norm_of_nonneg (mul_nonneg (hrk e) hnn)]
    exact mul_le_mul_of_nonneg_left hle (hrk e)
  have hnorm : Summable (fun e => ∫ ω, ‖rk e * (if e ∈ ω then 0 else
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)‖ ∂μ) := by
    refine hsumm.congr fun e => ?_
    have hae : ∀ᵐ ω ∂μ, ‖rk e * (if e ∈ ω then 0 else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)‖ =
        rk e * (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) := by
      filter_upwards [hfin e] with ω hω
      refine Real.norm_of_nonneg (mul_nonneg (hrk e) ?_)
      split_ifs with he
      · exact le_refl 0
      · exact sub_nonneg.2 (pow_le_pow_left₀ ENNReal.toReal_nonneg
          (ENNReal.toReal_mono hω (encard_cluster_le_insert_coe ω e o)) p)
    rw [integral_congr_ae hae, integral_const_mul]
  have hmain := integral_tsum_of_summable_integral_norm
    (F := fun e ω => rk e * (if e ∈ ω then 0 else
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) hInt hnorm
  refine hmain.symm.trans (tsum_congr fun e => ?_)
  rw [integral_const_mul]


open Classical in
/-- **The `hKd` interchange from unconditional per-vertex moments.**

`integral_tsum_closed_pivotal_real_of_hKd` asks for the two per-pair inputs `hfin`/`hint`
concerning the cluster of `o` *after* opening a pair, which is not the object a bond model
controls.  Both follow from the unconditional per-vertex data at `o` and at the endpoints of
the pair (`ae_ne_top_encard_cluster_insert`, `integrable_encard_cluster_insert_pow`), exactly as
in `tsum_cutoff_pivotal_eq_closed_pow_of_vertexMoments`; this is the version to apply in a model
where only per-vertex moments are available.  No root-cluster finiteness is assumed, and no
vertex other than `o` and the two endpoints of a pair is mentioned. -/
theorem integral_tsum_closed_pivotal_real_of_hKd_vertexMoments {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hK' : (β : ℝ) * -K' r ≠ 0)
    (hfinU : ∀ y : Fin d → ℤ,
      ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
        ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤)
    (hintU : ∀ y : Fin d → ℤ,
      Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p)
        (law (intensityProfile (cutoffKernel N K r) β)))
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd) :
    ∫ ω, (∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  integral_tsum_closed_pivotal_real_of_hKd (K := K) (K' := K') p β r o cw Kd hcw hK'
    (fun e => PercLib.Percolation.Bond.ae_ne_top_encard_cluster_insert
      (law (intensityProfile (cutoffKernel N K r) β)) e o hfinU)
    (fun e => PercLib.Percolation.Bond.integrable_encard_cluster_insert_pow
      (law (intensityProfile (cutoffKernel N K r) β)) e o p hfinU hintU)
    hKd


open Classical in
/-- **The derivative series in the paper's shape, with `hKd` as the only summability input.**

Composition of the summed closed-coordinate rewrite `tsum_cutoff_pivotal_eq_closed_pow` with
the `hKd` interchange `integral_tsum_closed_pivotal_real_of_hKd`: the series of per-pair
pivotal integrals is `β (-K'(r))` times the integral of the pointwise closed-coordinate pair
sum.  This is the "series of per-pair integrals → integral of the pointwise sum" step, stated
for the exact expression that appears as the derivative in
`hasDerivAt_integral_cutoff_pow`. -/
theorem tsum_cutoff_pivotal_eq_integral_closed_of_hKd {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hK' : (β : ℝ) * -K' r ≠ 0)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β)))
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd) :
    (∑' e, cw e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      ((β : ℝ) * -K' r) *
        ∫ ω, (∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          (if e ∈ ω then 0 else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
  refine (tsum_cutoff_pivotal_eq_closed_pow (N := N) (K := K) (K' := K') p β r o cw
    hcw hfin hint).trans ?_
  rw [← integral_tsum_closed_pivotal_real_of_hKd (K := K) (K' := K') p β r o cw Kd hcw
    hK' hfin hint hKd]

open Classical in
/-- **The cutoff Russo derivative in the paper's shape (value conversion only).**

`hasDerivAt_integral_cutoff_pow` presents the derivative of `r ↦ E_r |K_o|^p` as the series
`∑' e, cw r₀ e * ∫ ω, (pivotal increment) ∂μ_{r₀}` of *per-pair* integrals.  This theorem
converts that value into `β (-K'(r₀))` times the *integral* `∫ ω, ∑' e, …` of the pointwise
closed-coordinate pair sum — the shape in which Lemma I.4.1 states its right-hand side before
the mass-transport and binomial steps.

The derivative statement itself is an explicit input `hd`, so that a caller can supply
`hasDerivAt_integral_cutoff_pow` verbatim (its derivative has exactly the shape assumed here);
`hd`'s function `f` is arbitrary.  Besides `hd` the inputs are those of
`tsum_cutoff_pivotal_eq_integral_closed_of_hKd`: the weight equation `hcw`, nondegeneracy
`β (-K'(r₀)) ≠ 0`, the per-pair `hfin`/`hint` and the dominator bound `hKd`.  Nothing here
asserts the binomial or expectation form of Lemma I.4.1. -/
theorem hasDerivAt_cutoff_closed_of_pivotal {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ) {f : ℝ → ℝ} {r₀ : ℝ}
    (hd : HasDerivAt f
      (∑' e, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) r₀)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hK' : (β : ℝ) * -K' r ≠ 0)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β)))
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd) :
    HasDerivAt f (((β : ℝ) * -K' r) *
        ∫ ω, (∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          (if e ∈ ω then 0 else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β))) r₀ := by
  have hstep : (∑' e, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel N K r) β))) =
      ∑' e, cw e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β)) := by
    refine tsum_congr fun e => ?_
    rw [integral_pivotal_pow_eq_real_sub _ e o p (hfin e)]
  exact hd.congr_deriv (hstep.trans (tsum_cutoff_pivotal_eq_integral_closed_of_hKd
    (K := K) (K' := K') p β r o cw Kd hcw hK' hfin hint hKd))

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- **Measurability of the closed-coordinate summand.** -/
theorem measurable_closed_pivotal_integrand [Countable V] (o : V) (p : ℕ) (e : Sym2 V) :
    Measurable fun ω : Config V => (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p) :=
  Measurable.ite (measurableSet_mem e) measurable_const
    (((measurable_encard_cluster_insert_coe e o).pow_const p).sub
      ((Measurable.of_discrete.comp (measurable_encard_cluster (x := o))).pow_const p))

open Classical in
/-- **Measurability of a weighted closed-coordinate summand.** -/
theorem measurable_closed_pivotal_term [Countable V] (o : V) (p : ℕ) (w : Sym2 V → ℝ≥0∞)
    (e : Sym2 V) :
    Measurable fun ω : Config V => w e * (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p) :=
  measurable_const.mul (measurable_closed_pivotal_integrand o p e)

open Classical in
/-- **Measurability of the weighted closed-coordinate flux series.**  Every summand is
measurable because the inserted cluster volume is (`measurable_encard_cluster_insert_coe`), and
the sum is over the countable type `Sym2 V`. -/
theorem measurable_tsum_closed_pivotal [Countable V] (o : V) (p : ℕ)
    (w : Sym2 V → ℝ≥0∞) :
    Measurable fun ω : Config V => ∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p) :=
  Measurable.tsum fun e => measurable_closed_pivotal_term o p w e

open Classical in
/-- **The a.e. finiteness input `hne` is implied by a finite integral.**  The pointwise finiteness
of the extended-nonnegative closed-coordinate flux series needed by
`toReal_lintegral_tsum_closed_eq_tsum_integral` follows from finiteness of its `ℝ≥0∞`-integral,
which is the shape in which a mass-transport or moment bound is available. -/
theorem ae_ne_top_tsum_closed_pivotal_of_lintegral_ne_top [Countable V]
    (μ : MeasureTheory.Measure (Config V)) (o : V) (p : ℕ) (w : Sym2 V → ℝ≥0∞)
    (h : (∫⁻ ω, ∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    ∀ᵐ ω ∂μ, (∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ≠ ⊤ := by
  filter_upwards [MeasureTheory.ae_lt_top (measurable_tsum_closed_pivotal o p w) h] with ω hω
  exact hω.ne

open Classical in
/-- **The assembled real form of the closed-coordinate flux from its extended-nonnegative
identity.**

This is the exact composition of the two real/extended-nonnegative passages:
`integral_toReal_eq_toReal_lintegral` on the extended-nonnegative series (inputs: a.e. finiteness
of the series and its a.e. measurability), the pointwise conversion
`ae_toReal_tsum_closed_eq_tsum_real`, and the integral/sum interchange `hinter`.

The interchange is *not* supplied by `hKd`: `hKd` bounds the pivotal flux, and
`summable_closed_flux_of_hKd` needs its `hpair` input as well.  The a.e. finiteness `hne` of the
extended-nonnegative series is likewise not implied by the per-pair finiteness `hflux` of
`hasDerivAt_integral_cutoff_pow`: it is a genuine extra input of the real passage. -/
theorem toReal_lintegral_tsum_closed_eq_tsum_integral_of_measurable [Countable V]
    (μ : MeasureTheory.Measure (Config V)) (o : V) (p : ℕ) (w : Sym2 V → ℝ≥0∞)
    (hw : ∀ e, w e ≠ ⊤)
    (hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hne : ∀ᵐ ω ∂μ, (∑' e : Sym2 V, w e *
      (if e ∈ ω then (0 : ℝ≥0∞) else ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ≠ ⊤)
    (hinter : ∫ ω, (∑' e : Sym2 V, (w e).toReal * (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)) ∂μ =
      ∑' e : Sym2 V, (w e).toReal * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ) :
    (∫⁻ ω, ∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal =
      ∑' e : Sym2 V, (w e).toReal * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
  rw [← integral_toReal_eq_toReal_lintegral
      (measurable_tsum_closed_pivotal o p w).aemeasurable hne,
    MeasureTheory.integral_congr_ae
      (ae_toReal_tsum_closed_eq_tsum_real μ o p w hw hfin), hinter]

open Classical in
/-- **The pivotal flux series is the rate times the cast of the assembled
extended-nonnegative flux.**

This is the passage from the derivative's real pivotal series to the left side of the assembled
extended-nonnegative identity `i41_enn_of_root_finite`, without ever interchanging a real series
with an integral: the only interchange is `MeasureTheory.lintegral_tsum` at `ℝ≥0∞` level, which
needs no summability hypothesis, and the real/extended-nonnegative conversion is
`ENNReal.tsum_toReal_eq`, which is unconditional.  `hpair` is the per-pair input supplied by
`cutoff_pivotal_eq_closed_pow` after `integral_toReal_eq_toReal_lintegral`, and `hflux` is the
per-pair finiteness from `hasDerivAt_integral_cutoff_pow`. -/
theorem tsum_pivotal_eq_rate_mul_toReal_lintegral [Countable V]
    (μ : MeasureTheory.Measure (Config V)) (o : V) (p : ℕ) (w : Sym2 V → ℝ≥0∞)
    (cw : Sym2 V → ℝ) (rate : ℝ) (hw : ∀ e, w e ≠ ⊤)
    (hflux : ∀ e, (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤)
    (hpair : ∀ e, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ =
      rate * ((w e).toReal * (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal)) :
    (∑' e : Sym2 V, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ) =
      rate * (∫⁻ ω, ∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal := by
  have hLC : ∀ e : Sym2 V, (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤ := by
    intro e
    refine ne_top_of_le_ne_top (hflux e) (MeasureTheory.lintegral_mono fun ω => ?_)
    by_cases he : e ∈ ω
    · rw [ite_eq_left he]
      simp
    · rw [ite_eq_right he, Set.sdiff_singleton_eq_self he]
  have hlcm : (∑' e : Sym2 V, w e * (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ)) =
      ∑' e : Sym2 V, ∫⁻ ω, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ :=
    tsum_congr fun e =>
      (MeasureTheory.lintegral_const_mul (w e) (measurable_closed_pivotal_integrand o p e)).symm
  calc (∑' e : Sym2 V, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ)
      = ∑' e : Sym2 V, rate * ((w e).toReal * (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal) := tsum_congr hpair
    _ = rate * ∑' e : Sym2 V, (w e).toReal * (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal := tsum_mul_left
    _ = rate * ∑' e : Sym2 V, (w e * (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ)).toReal := by
        congr 1
        exact tsum_congr fun e => (ENNReal.toReal_mul).symm
    _ = rate * (∑' e : Sym2 V, w e * (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ)).toReal := by
        rw [ENNReal.tsum_toReal_eq fun e => ENNReal.mul_ne_top (hw e) (hLC e)]
    _ = rate * (∑' e : Sym2 V, ∫⁻ ω, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal := by
        rw [hlcm]
    _ = rate * (∫⁻ ω, ∑' e : Sym2 V, w e * (if e ∈ ω then (0 : ℝ≥0∞) else
          ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ).toReal := by
        rw [MeasureTheory.lintegral_tsum fun e =>
          (measurable_closed_pivotal_term o p w e).aemeasurable]

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

/-! ### Non-vacuity of the moment hypothesis -/

/-- **The moment hypothesis is satisfiable.** On the one-vertex type every cluster is the
whole vertex set, so its volume is `1`; the inserted `p`-th moment is therefore `1` for
every law, pair and exponent. Hence `hins` is not an empty hypothesis, and the reductions
above apply to a genuine model. -/
theorem insert_moment_ne_top_unit (q : Sym2 Unit → unitInterval) (e : Sym2 Unit) (p : ℕ) :
    (∫⁻ ω : Config Unit, ((cluster (insert e ω) ()).encard : ℝ≥0∞) ^ p ∂(law q)) ≠ ⊤ := by
  have hcl : ∀ ω : Config Unit, ((cluster ω ()).encard : ℝ≥0∞) = 1 := by
    intro ω
    have h : cluster ω () = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      simpa only [Subsingleton.elim y ()] using mem_cluster_self ω ()
    rw [h]
    simp
  have hone : (fun ω : Config Unit => ((cluster (insert e ω) ()).encard : ℝ≥0∞) ^ p)
      = fun _ => 1 := by
    funext ω
    rw [hcl]
    simp
  rw [hone, lintegral_const, measure_univ, one_mul]
  simp

end PercLib.Models.LongRange

/-! ### Conditional binomial differentiation after realization of the flux bound -/

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- Finiteness of the actual extended-nonnegative cutoff flux follows from per-pair inserted
moments, a uniform pivotal-flux bound, and a nonzero cutoff rate. -/
theorem lintegral_radial_pivotal_ne_top_of_insert_moments {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hp : 1 ≤ p)
    (hins : ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd)
    (hrate : (β : ℝ) * -K' r ≠ 0) :
    (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤ := by
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K r) β)
  let rk : Sym2 (Fin d → ℤ) → ℝ := fun e =>
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ)
  let Q : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e => ∫⁻ ω,
    (if e ∈ ω then (0 : ℝ≥0∞) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
  have hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ := by
    intro e
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o)
      p hp (hins e)
  have hQfin : ∀ e, Q e ≠ ⊤ := by
    intro e
    refine ne_top_of_le_ne_top
      (lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top e o p (hins e)) ?_
    exact lintegral_mono fun ω => by
      by_cases he : e ∈ ω
      · simp [he]
      · rw [ite_eq_right he, Set.sdiff_singleton_eq_self he]
  have hQreal : ∀ e, (Q e).toReal = ∫ ω, (if e ∈ ω then (0 : ℝ) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
    intro e
    have hm : AEMeasurable _ μ :=
      (measurable_closed_pivotal_integrand o p e).aemeasurable
    have hne : ∀ᵐ ω ∂μ, ((if e ∈ ω then (0 : ℝ≥0∞) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) : ℝ≥0∞) ≠ ⊤ := by
      filter_upwards [hfin e] with ω hω
      by_cases he : e ∈ ω
      · simp [he]
      · rw [ite_eq_right he]
        exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hω) tsub_le_self
    rw [show (Q e).toReal =
        (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal from rfl]
    rw [← integral_toReal_eq_toReal_lintegral hm hne]
    apply integral_congr_ae
    filter_upwards [hfin e] with ω hω
    by_cases he : e ∈ ω
    · rw [ite_eq_left he, ite_eq_left he]
      simp
    · rw [ite_eq_right he, ite_eq_right he]
      have hs : ω \ {e} = ω := Set.sdiff_singleton_eq_self he
      have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
          ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
        encard_cluster_sdiff_le_insert_coe ω e o
      rw [hs] at hle
      exact toReal_pow_sub_pow hle hω p
  have hsumm := summable_closed_flux_cutoff_of_insert_moments p β r o cw Kd hcw hp hins hKd hrate
  have hsummAbs : Summable (fun e => |rk e * ∫ ω, (if e ∈ ω then (0 : ℝ) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ|) := hsumm.1.abs
  have hrk : ∀ e, 0 ≤ rk e := fun e => by positivity
  have hbound : ∀ S : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ S, |rk e| * |(Q e).toReal| ≤ |((β : ℝ) * -K' r)⁻¹| * Kd := by
    intro S
    calc ∑ e ∈ S, |rk e| * |(Q e).toReal| =
        ∑ e ∈ S, |rk e * ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ| := by
          apply Finset.sum_congr rfl
          intro e _
          rw [hQreal, abs_mul, abs_of_nonneg (hrk e)]
      _ ≤ ∑' e, |rk e * ∫ ω, (if e ∈ ω then (0 : ℝ) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ| :=
        hsummAbs.sum_le_tsum S (fun e _ => abs_nonneg _)
      _ ≤ |((β : ℝ) * -K' r)⁻¹| * Kd := hsumm.2
  have hout : (∑' e, ENNReal.ofReal (rk e) * Q e) ≠ ⊤ :=
    tsum_ofReal_mul_ne_top_of_real_bound rk hrk Q hQfin
      (|((β : ℝ) * -K' r)⁻¹| * Kd) hbound
  rw [tsum_lintegral_closed_pivotal μ p o (fun e => ENNReal.ofReal (rk e))] at hout
  simpa only [Q, rk, ENNReal.ofReal_coe_nnreal] using hout


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- The cutoff cluster moment has the paper's binomial derivative at the origin, conditional
on the remaining geometric, moment, measurability and continuity inputs. The per-pair moment
hypothesis is retained explicitly: this is not a proof of sharpness. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hins : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v))
    (hrate : (β : ℝ) * -K' r₀ ≠ 0) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel (d := d) N K r₀) β)
  have hr₀ : r₀ ∈ Ioo u v := ⟨hur, hrv⟩
  have hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ≠ ⊤ := by
    intro e
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e 0)
      p hp (hins r₀ hr₀ e)
  have hint : ∀ e, Integrable
      (fun ω => (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p) μ := by
    intro e
    exact integrable_toReal_pow_encard_cluster_insert e 0 p (hins r₀ hr₀ e)
  have hKdReal : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r₀ e| *
      |∫ ω, ((((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) 0).encard : ℝ≥0∞).toReal) ^ p) ∂μ| ≤ Kd r₀ := by
    intro S
    refine le_trans ?_ (hKd r₀ hr₀ S)
    refine Finset.sum_le_sum fun e _ => ?_
    rw [integral_pivotal_pow_eq_real_sub μ e 0 p (hfin e)]
  have hd := hasDerivAt_integral_cutoff_pow_of_insert_moments hKa hK' hK'c β p hp 0 hχ cw hcw
    hu hur hrv hvR hcorner hins Kd hKdint hKd hmeas hcont
  have hd' := hasDerivAt_cutoff_closed_of_pivotal (K := K) (K' := K') p β r₀ 0
    (cw r₀) (Kd r₀) hd (hcw r₀) hrate hfin hint hKdReal
  have hmom : (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ :=
    lintegral_pow_encard_ne_top_of_insert (s(0, 0)) 0 p (hins r₀ hr₀ (s(0, 0)))
  have hrootfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_coe 0) p hp hmom
  have hflux : (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r₀ then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤ :=
    lintegral_radial_pivotal_ne_top_of_insert_moments p β r₀ 0 (cw r₀) (Kd r₀)
      (hcw r₀) hp (hins r₀ hr₀) hKdReal hrate
  refine hd'.congr_deriv ?_
  have hbin : ∫ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r₀ then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)).toReal ∂μ =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ)) ∂μ :=
    i41_real_of_root_finite μ (law_cutoffKernel_map_translate K r₀ β) hrootfin hcorner hr₀ hp hflux
  calc
    (β : ℝ) * -K' r₀ * ∫ ω, (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel N (fun s => if s < r₀ then 1 else 0) e : ℝ) *
          (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p)) ∂μ =
      (β : ℝ) * -K' r₀ * ∫ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r₀ then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p)).toReal ∂μ := by
        congr 1
        exact integral_congr_ae
          ((ae_toReal_tsum_radialKernel_closed_eq_tsum_real (N := N.toSeminorm) (r := r₀)
            μ p hfin).mono
            (fun _ h => h.symm))
    _ = (β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ)) ∂μ := by
        rw [hbin]


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- A zero cutoff rate makes the entire cutoff pivotal-flux derivative coefficient vanish. -/
theorem hasDerivAt_of_zero_cutoff_rate {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (o : Fin d → ℤ) {f : ℝ → ℝ}
    (cw : Sym2 (Fin d → ℤ) → ℝ) {r : ℝ}
    (hd : HasDerivAt f (∑' e, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel N K r) β))) r)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hzero : (β : ℝ) * -K' r = 0) :
    HasDerivAt f 0 r := by
  have hseries : (∑' e, cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel N K r) β))) = 0 := by
    simp only [hcw, hzero, zero_mul, mul_zero, tsum_zero]
  exact hd.congr_deriv hseries


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- The cutoff cluster moment has the paper's binomial derivative at the origin, conditional
on the remaining geometric, moment, measurability and continuity inputs. The per-pair moment
hypothesis is retained explicitly: this is not a proof of sharpness. -/
theorem hasDerivAt_integral_cutoff_pow_binomial {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hins : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  have hd := hasDerivAt_integral_cutoff_pow_of_insert_moments hKa hK' hK'c β p hp 0 hχ cw hcw
    hu hur hrv hvR hcorner hins Kd hKdint hKd hmeas hcont
  by_cases hrate : (β : ℝ) * -K' r₀ = 0
  · have hz := hasDerivAt_of_zero_cutoff_rate (K := K) (K' := K') β p 0
      (cw r₀) hd (hcw r₀) hrate
    simpa only [hrate, zero_mul] using hz
  · exact hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments
      hKa hK' hK'c β p hp hχ cw hcw hu hur hrv hvR hcorner hins Kd hKdint hKd hmeas hcont hrate

end PercLib.Models.LongRange


/-! ### Parameter measurability and per-vertex moments -/

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- **The set of cut-off corners is null.** The corner values of the cut-off family are the
norms `N (Int.cast ∘ z)` of the non-zero lattice displacements; there are countably many, so
they are Lebesgue-null and the Russo derivative formula holds at almost every scale. -/
theorem ae_notMem_cutoff_corners (d : ℕ) (N : ModelNorm (Fin d → ℝ)) :
    ∀ᵐ r : ℝ ∂volume, r ∉ ⋃ e : Sym2 (Fin d → ℤ),
      {a : ℝ | ∃ x y, e = s(x, y) ∧ a = N (Int.cast ∘ (x - y))} := by
  have hcorners : (⋃ e : Sym2 (Fin d → ℤ),
      {a : ℝ | ∃ x y, e = s(x, y) ∧ a = N (Int.cast ∘ (x - y))}).Countable :=
    Set.countable_iUnion fun _ => countable_cutoff_corners _
  exact measure_eq_zero_iff_ae_notMem.1 (hcorners.measure_zero volume)

/-- **A.e. strong measurability of the capped cut-off flux in the cut-off parameter.**

For `0 < u` and `v ≤ R`, the capped flux
`r ↦ ∑'_e c_r(e) * ∫⁻ (min n |K_o(ω ∪ {e})|^p - min n |K_o(ω \ {e})|^p) ∂μ_r`
is a.e. strongly measurable on `(u, v)`. Every hypothesis is a hypothesis of the cut-off family
and of the bounded Russo formula: monotonicity and differentiability of the profile, continuity
of `K'`, finiteness of the susceptibility at the cut-off scale `R`, and the defining equation
for the derivative weight `cw`. -/
theorem aestronglyMeasurable_capped_flux_cutoff {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {u v : ℝ} (hu : 0 < u) (hvR : v ≤ R) (n : ℕ) :
    AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal)
      (volume.restrict (Ioo u v)) := by
  refine (measurable_deriv (fun r : ℝ =>
      ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))).aestronglyMeasurable.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (ae_notMem_cutoff_corners d N)] with r hr hbad
  have hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r := by
    intro z hz
    exact hbad (Set.mem_iUnion.2 ⟨s(0, z), 0, z, rfl,
      by simpa only [zero_sub, intCast_comp_neg, map_neg_eq_map] using hz.symm⟩)
  exact (hasDerivAt_capped_moment_cutoff_of_weight hKa hK' hK'c β p n hp o hχ cw hcw
    (hu.trans hr.1) (hr.2.trans_le hvR) hcorner).deriv

/-- **`∀`-form of the capped-flux measurability.** This is the `hmeas` input of
`hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments`, for the cut-off family at the
origin of `ℤ^d`, with the interval `(u, v)` and the cut-off scale `R ≥ v`. -/
theorem aestronglyMeasurable_capped_flux_cutoff_binomial {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v : ℝ} (hu : 0 < u) (hvR : v ≤ R) :
    ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))).toReal)
      (volume.restrict (Ioo u v)) :=
  fun n => aestronglyMeasurable_capped_flux_cutoff hKa hK' hK'c β 0 p hp hχ cw hcw
    hu hvR n

end PercLib.Models.LongRange

end


noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- **The binomial cut-off moment derivative with its measurability input discharged.**

This is `hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments` with the hypothesis `hmeas`
removed: `aestronglyMeasurable_capped_flux_cutoff_binomial` supplies it from the remaining
hypotheses alone. The point is the endpoint: the packaged statement has only `v ≤ R`, while the
cap measurability available from the bounded Russo formula (and `measurable_capped_flux_cutoff`)
is stated on `uIoc s t` with `t < R`. Working on the open interval `(u, v)` removes that gap,
because `r ∈ (u, v)` gives `r < v ≤ R` and only the interior point `r₀ ∈ (u, v)` needs the
derivative identity.

No other hypothesis changes, so the geometric inputs (the per-pair inserted moments `hins`, the
all-pairs dominator `Kd` with its interval integrability and bound `hKd`, the corner condition
`hcorner`, the uncapped flux continuity `hcont` and the nonvanishing rate `hrate`) stay explicit;
this remains a conditional statement and says nothing about sharpness. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments_of_measurable
    {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hins : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v))
    (hrate : (β : ℝ) * -K' r₀ ≠ 0) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments hKa hK' hK'c β p hp hχ cw hcw
    hu hur hrv hvR hcorner hins Kd hKdint hKd
    (aestronglyMeasurable_capped_flux_cutoff_binomial hKa hK' hK'c β p hp hχ cw hcw hu hvR)
    hcont hrate

end PercLib.Models.LongRange

end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- **The cap passage for the cut-off family with its measurability input discharged.**

This is `hasDerivAt_integral_cutoff_pow` with the hypothesis `hmeas` removed: the general-root
form `aestronglyMeasurable_capped_flux_cutoff` supplies it from the remaining hypotheses alone.
Everything else, in particular the uncapped flux continuity `hcont` and the finite-moment,
a.e.-finiteness and finite-flux inputs, stays explicit. -/
theorem hasDerivAt_integral_cutoff_pow_of_measurable
    {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hmom : ∀ r ∈ Ioo u v, (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p)
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd r)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (∑' e, cw r₀ e *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow hKa hK' hK'c β p hp o hχ cw hcw hu hur hrv hvR hcorner
    hmom hfin hflux Kd hKdint hKd
    (aestronglyMeasurable_capped_flux_cutoff hKa hK' hK'c β o p hp hχ cw hcw hu hvR) hcont

end PercLib.Models.LongRange

end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- **The insert-moments cap passage for the cut-off family with `hmeas` discharged.**

This is `hasDerivAt_integral_cutoff_pow_of_insert_moments` with the measurability input removed;
`aestronglyMeasurable_capped_flux_cutoff` supplies it from the remaining hypotheses. This is the
form in which the capped measurability is consumed by the binomial moment derivative, so a
consumer of that chain no longer carries a separate measurability obligation. -/
theorem hasDerivAt_integral_cutoff_pow_of_insert_moments_of_measurable
    {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hins : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd r)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (∑' e, cw r₀ e *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow_of_insert_moments hKa hK' hK'c β p hp o hχ cw hcw
    hu hur hrv hvR hcorner hins Kd hKdint hKd
    (aestronglyMeasurable_capped_flux_cutoff hKa hK' hK'c β o p hp hχ cw hcw hu hvR) hcont

end PercLib.Models.LongRange

end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- **The binomial cut-off moment derivative with neither `hmeas` nor `hrate` as an input.**

This is `hasDerivAt_integral_cutoff_pow_binomial`, the rate-free form of the binomial moment
derivative, with the capped-flux measurability input removed:
`aestronglyMeasurable_capped_flux_cutoff_binomial` supplies it from the remaining hypotheses.
The zero-rate case is already handled there by `hasDerivAt_of_zero_cutoff_rate`, so what remains
here is exactly the geometric and moment data: the inserted moments `hins`, the dominator `Kd`
with `hKdint` and `hKd`, the corner condition `hcorner`, and the uncapped flux continuity `hcont`.
This is still a conditional statement; it is not a proof of sharpness. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_measurable
    {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hins : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow_binomial hKa hK' hK'c β p hp hχ cw hcw
    hu hur hrv hvR hcorner hins Kd hKdint hKd
    (aestronglyMeasurable_capped_flux_cutoff_binomial hKa hK' hK'c β p hp hχ cw hcw hu hvR)
    hcont

end PercLib.Models.LongRange

end


namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- The `ℝ≥0∞`-valued cluster volume of a fixed vertex is measurable. -/
theorem measurable_encard_cluster_toENNReal (y : V) :
    Measurable fun ω : Config V => ((cluster ω y).encard : ℝ≥0∞) :=
  Measurable.of_discrete.comp (measurable_encard_cluster (x := y))

/-- A per-vertex cluster is finite almost surely as soon as its `p`-th moment is finite. -/
theorem ae_ne_top_encard_cluster_of_lintegral_pow_ne_top (μ : Measure (Config V)) (y : V)
    (p : ℕ) (hp : 1 ≤ p) (h : (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤ :=
  PercLib.Models.LongRange.ae_ne_top_of_lintegral_pow_ne_top
    (measurable_encard_cluster_toENNReal y) p hp h

/-- The real `p`-th per-vertex cluster moment is integrable as soon as the `ℝ≥0∞`-valued one
is finite. -/
theorem integrable_toReal_pow_encard_cluster_of_lintegral_ne_top (μ : Measure (Config V))
    (y : V) (p : ℕ) (h : (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p) μ := by
  have hm : AEMeasurable (fun ω : Config V => ((cluster ω y).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal y).pow_const p).aemeasurable
  refine (integrable_toReal_of_lintegral_ne_top hm h).congr ?_
  filter_upwards with ω
  exact ENNReal.toReal_pow _ p

/-- A uniform `ℝ≥0∞` bound on the per-vertex `p`-th moment bounds the real expectation. -/
theorem integral_toReal_pow_encard_cluster_le (μ : Measure (Config V)) (y : V) (p : ℕ)
    (hp : 1 ≤ p) {M : ℝ≥0∞} (hM : (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≤ M)
    (hMtop : M ≠ ⊤) :
    ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ∂μ ≤ M.toReal := by
  have hfin : (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hM (lt_top_iff_ne_top.2 hMtop))
  have hae := ae_ne_top_encard_cluster_of_lintegral_pow_ne_top μ y p hp hfin
  have hne : ∀ᵐ ω ∂μ, ((cluster ω y).encard : ℝ≥0∞) ^ p ≠ ⊤ := by
    filter_upwards [hae] with ω hω
    exact ENNReal.pow_ne_top hω
  have hm : AEMeasurable (fun ω : Config V => ((cluster ω y).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal y).pow_const p).aemeasurable
  calc ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ p ∂μ
      = ∫ ω, (((cluster ω y).encard : ℝ≥0∞) ^ p).toReal ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with ω
        exact (ENNReal.toReal_pow _ p).symm
    _ = (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ).toReal :=
        integral_toReal_eq_toReal_lintegral hm hne
    _ ≤ M.toReal := ENNReal.toReal_mono hMtop hM

/-- **Opening one pair preserves finiteness of the `p`-th cluster moment.**

The pointwise volume bound `encard_cluster_insert_pow_le` dominates the inserted `p`-th moment
by the moments of the three clusters at the root and at the endpoints of the pair; all three
are per-vertex data.  No finiteness of the cluster of the root itself is assumed, and a vertex
with an infinite cluster is allowed: the moment hypothesis is what excludes it. -/
theorem lintegral_pow_encard_cluster_insert_ne_top (μ : Measure (Config V)) (o a b : V) (p : ℕ)
    (ho : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤)
    (ha : (∫⁻ ω, ((cluster ω a).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤)
    (hb : (∫⁻ ω, ((cluster ω b).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    (∫⁻ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ := by
  have hmo : AEMeasurable (fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal o).pow_const p).aemeasurable
  have hma : AEMeasurable (fun ω : Config V => ((cluster ω a).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal a).pow_const p).aemeasurable
  have hmb : AEMeasurable (fun ω : Config V => ((cluster ω b).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal b).pow_const p).aemeasurable
  have htwo : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hrhs : (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p)) ∂μ) =
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) +
        2 ^ (p - 1) * ((∫⁻ ω, ((cluster ω a).encard : ℝ≥0∞) ^ p ∂μ) +
          ∫⁻ ω, ((cluster ω b).encard : ℝ≥0∞) ^ p ∂μ) := by
    rw [lintegral_add_left' hmo,
      lintegral_const_mul'' ((2 : ℝ≥0∞) ^ (p - 1))
        (f := fun ω => ((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p) (hma.add hmb),
      lintegral_add_left' hma]
  have hbound : (∫⁻ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≤
      ∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p)) ∂μ :=
    lintegral_mono fun ω => encard_cluster_insert_pow_le ω a b o p
  refine ne_top_of_le_ne_top ?_ hbound
  rw [hrhs]
  exact ENNReal.add_ne_top.2
    ⟨ho, ENNReal.mul_ne_top htwo (ENNReal.add_ne_top.2 ⟨ha, hb⟩)⟩

/-- The pair-by-pair form: every insertion keeps the `p`-th cluster moment of the root
finite, as soon as every vertex has a finite `p`-th cluster moment. -/
theorem lintegral_pow_encard_cluster_insert_ne_top_forall (μ : Measure (Config V)) (o : V)
    (p : ℕ) (h : ∀ y : V, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤) :
    ∀ e : Sym2 V, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ := by
  intro e
  induction e using Sym2.ind with
  | _ a b => exact lintegral_pow_encard_cluster_insert_ne_top μ o a b p (h o) (h a) (h b)

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

variable {d : ℕ}

/-! ### The inserted-moment hypothesis from per-vertex moments -/

/-- **`hins` from per-vertex moments.**  The cutoff interfaces ask for finiteness of the `p`-th
moment of the cluster of the root after *opening* a pair `e`; per-vertex moment finiteness at
every vertex supplies it, for the law of any cutoff profile. -/
theorem insert_moments_of_vertex_moments {N : Seminorm ℝ (Fin d → ℝ)} {K : ℝ → ℝ}
    (β : ℝ≥0) (p : ℕ) (r : ℝ) (o : Fin d → ℤ)
    (hmom : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤) :
    ∀ e : Sym2 (Fin d → ℤ), (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ :=
  PercLib.Percolation.Bond.lintegral_pow_encard_cluster_insert_ne_top_forall _ o p hmom

/-- The same, uniformly over a scale interval: this is the shape of the `hins` hypothesis of
`hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments`. -/
theorem insert_moments_of_vertex_moments_Ioo {N : Seminorm ℝ (Fin d → ℝ)} {K : ℝ → ℝ}
    (β : ℝ≥0) (p : ℕ) (o : Fin d → ℤ) {u v : ℝ}
    (hmom : ∀ r ∈ Ioo u v, ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤) :
    ∀ r ∈ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ :=
  fun r hr => insert_moments_of_vertex_moments β p r o (hmom r hr)

/-- The same for a `ModelNorm`, which is the norm type of the cutoff derivative interface. -/
theorem insert_moments_of_vertex_moments_Ioo_modelNorm {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (β : ℝ≥0) (p : ℕ) (o : Fin d → ℤ) {u v : ℝ}
    (hmom : ∀ r ∈ Ioo u v, ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤) :
    ∀ r ∈ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ :=
  fun r hr => PercLib.Percolation.Bond.lintegral_pow_encard_cluster_insert_ne_top_forall
    _ o p (hmom r hr)

/-! ### The flux interface with per-vertex moments -/

open Classical in
/-- The cutoff flux is finite, with the per-pair inserted-moment hypothesis replaced by
per-vertex moment finiteness. -/
theorem lintegral_radial_pivotal_ne_top_of_vertex_moments {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hp : 1 ≤ p)
    (hmom : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd)
    (hrate : (β : ℝ) * -K' r ≠ 0) :
    (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤ :=
  lintegral_radial_pivotal_ne_top_of_insert_moments p β r o cw Kd hcw hp
    (insert_moments_of_vertex_moments β p r o hmom) hKd hrate

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

open Classical in
/-- **The cutoff cluster moment has the paper's binomial derivative at the origin, from
per-vertex moments.**

This is `hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments` with the per-pair
inserted-moment hypothesis `hins` replaced by moment finiteness at every vertex, uniformly over
the scale interval `Ioo u v` (`insert_moments_of_vertex_moments_Ioo`).  The geometric,
`hKd`, measurability, continuity and nonzero-rate inputs are unchanged and explicit; this is
still a conditional statement, not a proof of Lemma I.4.1 or of sharpness. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_vertex_moments {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hmom : ∀ r ∈ Ioo u v, ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v))
    :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow_binomial (K := K) (K' := K')
    (R := R) (u := u) (v := v) (r₀ := r₀)
    hKa hK' hK'c β p hp hχ cw hcw hu hur hrv hvR hcorner
    (insert_moments_of_vertex_moments_Ioo_modelNorm β p 0 hmom) Kd hKdint hKd hmeas hcont

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

open Classical in
/-- **The three real per-vertex inputs from one `ℝ≥0∞` per-vertex moment bound.**

`forall_inputs_of_uniform_vertex_moment` asks for almost sure finiteness, integrability and a
uniform real bound for the per-vertex `p`-th moments.  All three follow from the single
`ℝ≥0∞`-valued bound `∫⁻ |K_y| ^ p ≤ ofReal m`, uniformly in the scale and in the vertex.  So
the model-side moment input of the cutoff campaign can be stated once, at every vertex, in the
extended-nonnegative form in which cluster moments are actually computed. -/
theorem vertex_moment_inputs_of_lintegral_le {V : Type*} [Countable V]
    (q : ℝ → Sym2 V → unitInterval) (pow : ℕ) (hp : 1 ≤ pow) {m : ℝ} (hm : 0 ≤ m) {u v : ℝ}
    (hU : ∀ r ∈ Ioo u v, ∀ y : V,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ pow ∂(law (q r))) ≤ ENNReal.ofReal m) :
    (∀ r ∈ Ioo u v, ∀ y : V, ∀ᵐ ω ∂(law (q r)), ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤) ∧
      (∀ r ∈ Ioo u v, ∀ y : V, Integrable (fun ω =>
        ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow) (law (q r))) ∧
      (∀ r ∈ Ioo u v, ∀ y : V, ∫ ω, ((cluster ω y).encard : ℝ≥0∞).toReal ^ pow
        ∂(law (q r)) ≤ m) := by
  have hne : ∀ r ∈ Ioo u v, ∀ y : V,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ pow ∂(law (q r))) ≠ ⊤ := by
    intro r hr y
    exact ne_of_lt (lt_of_le_of_lt (hU r hr y) ENNReal.ofReal_lt_top)
  refine ⟨?_, ?_, ?_⟩
  · intro r hr y
    exact ae_ne_top_encard_cluster_of_lintegral_pow_ne_top _ y pow hp (hne r hr y)
  · intro r hr y
    exact integrable_toReal_pow_encard_cluster_of_lintegral_ne_top _ y pow (hne r hr y)
  · intro r hr y
    have hle := integral_toReal_pow_encard_cluster_le (law (q r)) y pow hp
      (M := ENNReal.ofReal m) (hU r hr y) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hm] at hle

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

open Classical in
/-- **The `hKd` integral/sum interchange from `ℝ≥0∞` per-vertex moments.**

`integral_tsum_closed_pivotal_real_of_hKd_vertexMoments` takes two per-vertex real inputs
(`hfinU`, `hintU`).  Both are consequences of `ℝ≥0∞`-valued moment finiteness at every vertex
(and `1 ≤ p`), so this restatement has a single per-vertex moment hypothesis. -/
theorem integral_tsum_closed_pivotal_real_of_hKd_lintegral {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ) (Kd : ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hK' : (β : ℝ) * -K' r ≠ 0) (hp : 1 ≤ p)
    (hmom : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ p)
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd) :
    ∫ ω, (∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ∫ ω, (if e ∈ ω then 0 else
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
            (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  integral_tsum_closed_pivotal_real_of_hKd_vertexMoments (K := K) (K' := K')
    p β r o cw Kd hcw hK'
    (fun y => ae_ne_top_encard_cluster_of_lintegral_pow_ne_top _ y p hp (hmom y))
    (fun y => integrable_toReal_pow_encard_cluster_of_lintegral_ne_top _ y p (hmom y)) hKd

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

section Nonvacuity

open PercLib.Probability

/-- **Non-vacuity of the per-vertex moment input: the zero profile.**  Under `law 0` every pair
is closed almost surely, so every cluster is a single vertex and every per-vertex `p`-th moment
equals `1`.  This is an honest bond profile on an infinite vertex set, so the new hypothesis is
not vacuous. -/
theorem vertex_moment_ne_top_zeroProfile {V : Type*} [Countable V] (y : V) (p : ℕ) :
    (∫⁻ ω : Config V, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (fun _ : Sym2 V => (0 : unitInterval)))) ≠ ⊤ := by
  have hae : ∀ᵐ ω ∂(law (fun _ : Sym2 V => (0 : unitInterval))), ω = ∅ := by
    filter_upwards [ae_config_subset_positive (fun _ : Sym2 V => (0 : unitInterval))] with ω hω
    exact Set.subset_empty_iff.mp fun e he => (lt_irrefl (0 : ℝ) (hω he))
  have hone : (fun ω : Config V => ((cluster ω y).encard : ℝ≥0∞) ^ p)
      =ᵐ[law (fun _ : Sym2 V => (0 : unitInterval))] fun _ => 1 := by
    filter_upwards [hae] with ω h
    rw [h, cluster_empty, Set.encard_singleton]
    simp
  rw [lintegral_congr_ae hone, lintegral_const, measure_univ, mul_one]
  exact ENNReal.one_ne_top

/-- **Non-vacuity on a finite ball: the per-vertex moment input is free.**  Every cluster has at
most `N` vertices, so the per-vertex `p`-th moment is finite for *every* bond profile and every
vertex of `Fin N`.  This is the finite-volume regime in which the cutoff hypotheses hold without
a moment theorem. -/
theorem vertex_moment_ne_top_fin (N : ℕ) (q : Sym2 (Fin N) → unitInterval) (y : Fin N)
    (p : ℕ) : (∫⁻ ω : Config (Fin N), ((cluster ω y).encard : ℝ≥0∞) ^ p ∂(law q)) ≠ ⊤ := by
  have hcard : ∀ ω : Config (Fin N), ((cluster ω y).encard : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
    intro ω
    have h := Set.encard_mono (Set.subset_univ (cluster ω y))
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card] at h
    simpa using h
  have hle : (∫⁻ ω : Config (Fin N), ((cluster ω y).encard : ℝ≥0∞) ^ p ∂(law q))
      ≤ (N : ℝ≥0∞) ^ p := by
    calc (∫⁻ ω : Config (Fin N), ((cluster ω y).encard : ℝ≥0∞) ^ p ∂(law q))
        ≤ ∫⁻ _ : Config (Fin N), (N : ℝ≥0∞) ^ p ∂(law q) :=
          lintegral_mono fun ω => ENNReal.pow_le_pow_left (hcard ω)
      _ = (N : ℝ≥0∞) ^ p * (law q) Set.univ := lintegral_const _
      _ = (N : ℝ≥0∞) ^ p := by rw [measure_univ, mul_one]
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (by simp)) hle

end Nonvacuity

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

open Classical in
/-- **The cutoff binomial derivative from one per-vertex moment hypothesis.**

`hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments` takes both the per-pair inserted
moments `hins` on `Ioo u v` and the susceptibility bound `hχ` at the outer scale `R`.  Both are
consequences of the single hypothesis that every per-vertex `p`-th cluster moment is finite on
`Ioo u v ∪ {R}`: `hins` from `insert_moments_of_vertex_moments_Ioo`, and `hχ` from
`chi_ne_top_of_lintegral_pow_ne_top` at `r = R` (the cluster of the root contains the root, so a
finite moment bounds the susceptibility).  Every other input stays explicit. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_moments {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hmom : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), ∀ y : Fin d → ℤ,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v))
    :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  have hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤ :=
    chi_ne_top_of_lintegral_pow_ne_top _ 0 p hp (hmom R (Set.mem_union_right _ rfl) 0)
  refine hasDerivAt_integral_cutoff_pow_binomial_of_vertex_moments (K := K) (K' := K')
    (R := R) (u := u) (v := v) (r₀ := r₀) hKa hK' hK'c β p hp hχ cw hcw hu hur hrv hvR
    hcorner ?_ Kd hKdint hKd hmeas hcont
  exact fun r hr => hmom r (Set.mem_union_left _ hr)

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

variable {d : ℕ}

open Classical in
/-- **The cutoff law is translation invariant, so the vertex in the moment hypothesis is free.**

For the cutoff profile the law is invariant under every shift of the configuration
(`law_cutoffKernel_map_translate`), and a shift carries the cluster of `y` to the cluster of the
origin (`encard_cluster_translate`).  Hence finiteness of the `p`-th moment of the cluster of a
single vertex — the shape in which moment bounds are proved — gives it at every vertex. -/
theorem vertex_moment_ne_top_of_root_moment {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (β : ℝ≥0) (r : ℝ) (p : ℕ) (y : Fin d → ℤ)
    (h : (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤) :
    (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
  have hmap : (law (intensityProfile (cutoffKernel (d := d) N K r) β)).map
      (fun ω : Config (Fin d → ℤ) => Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) =
      law (intensityProfile (cutoffKernel (d := d) N K r) β) :=
    law_cutoffKernel_map_translate (N := N) K r β (-y)
  have hcl : ∀ ω : Config (Fin d → ℤ),
      ((cluster (Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) 0).encard : ℝ≥0∞) =
        ((cluster ω y).encard : ℝ≥0∞) := by
    intro ω
    have h' := encard_cluster_translate (-y) y ω
    rw [show y + -y = 0 from add_neg_cancel y] at h'
    rw [h']
  have hstep : (∫⁻ ω, ((cluster (Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) 0).encard :
        ℝ≥0∞) ^ p ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) =
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) := by
    rw [← lintegral_map_shift (law (intensityProfile (cutoffKernel (d := d) N K r) β)) (-y)
      (fun ω => ((cluster ω 0).encard : ℝ≥0∞) ^ p), hmap]
  have hfin : (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) =
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) := by
    calc (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
        = ∫⁻ ω, ((cluster (Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) 0).encard :
            ℝ≥0∞) ^ p ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) :=
          lintegral_congr fun ω => by rw [hcl ω]
      _ = _ := hstep
  rw [hfin]
  exact h

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond PercLib.Analysis

variable {d : ℕ}

open Classical in
/-- **The cutoff binomial derivative from the root moment alone.**

On `ℤ^d` the cutoff law is translation invariant, so the per-vertex moment hypothesis of
`hasDerivAt_integral_cutoff_pow_binomial_of_moments` is the same as finiteness of the `p`-th
moment of the cluster of the origin at each scale in `Ioo u v ∪ {R}`
(`vertex_moment_ne_top_of_root_moment`).  This is the sharpest form of the moment input in the
file: one vertex, and `hχ` is not needed separately.  Everything else — the profile
hypotheses, the corner condition, `hKd` with its interval integrability, `hmeas`, `hcont` and
the nonvanishing rate — stays explicit, and sharpness is not claimed. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_root_moment {N : ModelNorm (Fin d → ℝ)}
    {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v))
    :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow_binomial_of_moments (K := K) (K' := K') (R := R) (u := u)
    (v := v) (r₀ := r₀) hKa hK' hK'c β p hp cw hcw hu hur hrv hvR hcorner
    (fun r hr y => vertex_moment_ne_top_of_root_moment β r p y (hroot r hr))
    Kd hKdint hKd hmeas hcont

end PercLib.Models.LongRange


/-! ### Concrete models and uniform continuity criteria -/

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability MeasureTheory Set

open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-- The sup norm of a nonzero integer displacement is at least one. -/
theorem one_le_normSeminorm_intCast {z : Fin d → ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) := by
  rw [normSeminorm_intCast]
  exact one_le_norm_of_ne_zero hz

/-- The cutoff kernel of the linear profile `s ↦ -s` vanishes at every scale `r ≤ 1`: no
integer displacement has sup norm below one, so the profile difference is never positive. -/
theorem linear_cutoffKernel_eq_zero_of_le_one {r : ℝ} (hr : r ≤ 1) (e : Sym2 (Fin d → ℤ)) :
    cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · simp [cutoffKernel_def, h]
    · rw [cutoffKernel_def, radialKernel_of_ne h]
      have h1 : (1 : ℝ) ≤ normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) :=
        one_le_normSeminorm_intCast (sub_ne_zero.2 h)
      by_cases hlt : normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) ≤ r
      · rw [cutoffProfile_of_le hlt, Real.toNNReal_eq_zero]
        show -normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) - -r ≤ 0
        linarith
      · rw [cutoffProfile_of_lt (not_le.1 hlt), Real.toNNReal_zero]

/-- The strict radial indicator `1{N (x - y) < r}` of the cutoff derivative vanishes at every
scale `r ≤ 1`. -/
theorem linear_radialKernel_indicator_eq_zero_of_le_one {r : ℝ} (hr : r ≤ 1)
    (e : Sym2 (Fin d → ℤ)) :
    radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · simp [h]
    · have h1 : (1 : ℝ) ≤ normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) :=
        one_le_normSeminorm_intCast (sub_ne_zero.2 h)
      have h2 : (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) s(x, y) : ℝ) = 0 :=
        radialKernel_indicator_eq_zero_of_not_lt (by linarith)
      exact NNReal.coe_eq_zero.1 h2

/-- The derivative weight of the linear profile with `β = 1` and `K' = -1` vanishes at every
scale `r ≤ 1`, because the strict radial indicator does. -/
theorem linear_weight_eq_zero {r : ℝ} (hr : r ≤ 1) (e : Sym2 (Fin d → ℤ)) :
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
        Real.exp (-(1 : ℝ) *
          (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ))) = 0 := by
  rw [linear_radialKernel_indicator_eq_zero_of_le_one hr e]
  simp

/-- On the window the intensity profile of the cut-off linear kernel is the identically zero
profile: the cutoff kernel vanishes and `1 - exp 0 = 0`. -/
theorem linear_intensityProfile_eq_zero_of_le_one {r : ℝ} (hr : r ≤ 1) :
    intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r) (1 : ℝ≥0) =
      fun _ => (0 : unitInterval) := by
  have hker : cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r = fun _ => 0 :=
    funext fun e => linear_cutoffKernel_eq_zero_of_le_one hr e
  rw [hker]
  funext e
  apply Subtype.ext
  simp [intensityProfile]

/-- Under the identically zero bond profile the configuration is empty almost surely. -/
theorem ae_eq_empty_zero_profile (d : ℕ) :
    ∀ᵐ ω ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))), ω = ∅ := by
  filter_upwards [ae_config_subset_positive (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))]
    with ω hω
  exact Set.subset_empty_iff.mp fun e he => (lt_irrefl (0 : ℝ) (hω he))

/-- The susceptibility of the cut-off linear profile at scale one is one: the profile vanishes
off the diagonal, so every cluster is a single vertex. -/
theorem chi_linear_cutoffKernel_eq_one (o : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) 1)
      (1 : ℝ≥0)) o = 1 := by
  refine chi_eq_one_of_offDiagonal_zero _ ?_ o
  intro v w _hwv
  have hker : cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) 1 s(v, w) = 0 :=
    linear_cutoffKernel_eq_zero_of_le_one le_rfl s(v, w)
  apply Subtype.ext
  simp [intensityProfile, hker]

/-- The volume of the cluster of `o` after inserting one pair into the empty configuration is
at most three. -/
theorem encard_cluster_insert_empty_le_three (o a b : Fin d → ℤ) :
    ((cluster (insert s(a, b) (∅ : Config (Fin d → ℤ))) o).encard : ℝ≥0∞) ≤ 3 := by
  have h := encard_cluster_insert_le_add (V := Fin d → ℤ) (∅ : Config (Fin d → ℤ)) a b o
  rw [cluster_empty, cluster_empty, cluster_empty, Set.encard_singleton,
    Set.encard_singleton, Set.encard_singleton] at h
  refine h.trans ?_
  norm_num

/-- Every inserted `p`-th moment is finite on the window: the law is that of the empty bond
configuration, where inserting one pair produces a configuration with at most one open edge
and hence a cluster of at most three vertices. -/
theorem lintegral_pow_encard_cluster_insert_ne_top_linear (p : ℕ) {r : ℝ} (hr : r < 1)
    (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
        (1 : ℝ≥0)))) ≠ ⊤ := by
  rw [linear_intensityProfile_eq_zero_of_le_one hr.le]
  have hae := ae_eq_empty_zero_profile (d := d)
  have hbound : (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)))) ≤ (3 : ℝ≥0∞) ^ p := by
    calc (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
          ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))))
        ≤ ∫⁻ _ : Config (Fin d → ℤ), (3 : ℝ≥0∞) ^ p
            ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with ω hω
          induction e using Sym2.ind with
          | _ a b =>
            rw [hω]
            exact ENNReal.pow_le_pow_left (encard_cluster_insert_empty_le_three o a b)
      _ = (3 : ℝ≥0∞) ^ p := by
          rw [lintegral_const, measure_univ, mul_one]
  have h3 : (3 : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  exact ne_top_of_le_ne_top h3 hbound

/-- The moment function is identically one on the window: the law is that of the empty bond
configuration and the cluster of `o` there is the singleton `{o}`. -/
theorem integral_linear_moment_eq_one (p : ℕ) {r : ℝ} (hr : r ≤ 1) (o : Fin d → ℤ) :
    ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
        (1 : ℝ≥0))) = 1 := by
  rw [linear_intensityProfile_eq_zero_of_le_one hr]
  have h : ∀ᵐ ω ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))),
      (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal = 1 := by
    filter_upwards [ae_eq_empty_zero_profile (d := d)] with ω hω
    rw [hω, cluster_empty, Set.encard_singleton]
    norm_num
  calc ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval)))
      = ∫ _ : Config (Fin d → ℤ), (1 : ℝ)
          ∂(law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))) := integral_congr_ae h
    _ = 1 := by simp


/-! ### The instantiation -/

open Classical in
/-- **The conditional binomial differentiation theorem at an explicit nondegenerate model.**

On the integer lattice with the sup norm, the linear profile `K s = -s` (`K' = -1`), intensity
`β = 1` and the radius `r₀ = 1/2`, the conclusion of
`hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments` holds at every outer scale `R ≥ 3/4`
for which the susceptibility input `hχ` holds at `R`. Every other hypothesis is met by a proof,
not by a choice of hypothesis: the profile data, the corner condition, the inserted moments, the
dominator and its interval integrability, the capped measurability and the uncapped continuity
are all constructed.

The rate `β * -K' r₀ = 1` is nonzero, so the instance is not the degenerate `β = 0` or
`K' = 0` case. The window `(1/4, 3/4)` contains no norm of an integer displacement, so the
cutoff kernel and the strict radial indicator both vanish there: the law is the one of the
identically closed configuration, the inserted moments are those of a single-edge
configuration, the dominator is the constant zero, and the capped and uncapped flux series
vanish identically on the window. Of the hypotheses of the conditional theorem only `hχ`
depends on the outer scale `R`, which is why it is the single remaining argument. -/
theorem hasDerivAt_integral_linear_cutoff_pow_of_chi (d : ℕ) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (hR : (3 / 4 : ℝ) ≤ R)
    (hχ : chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) R)
      (1 : ℝ≥0)) (0 : Fin d → ℤ) ≠ ⊤) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0))))
      (1 / 2) := by
  let cw : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r e =>
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
        Real.exp (-(1 : ℝ) *
          (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ)))
  have hcw : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)), cw r e =
      (radialKernel (ModelNorm.ofNorm (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) r) *
          Real.exp (-(((1 : ℝ≥0) : ℝ)) *
            (cutoffKernel (ModelNorm.ofNorm (Fin d → ℝ)) (fun s => -s) r e : ℝ))) :=
    fun _ _ => rfl
  have hwzero : ∀ r ∈ Ioo (1 / 4 : ℝ) (3 / 4), ∀ e, cw r e = 0 := by
    intro r hr e
    exact linear_weight_eq_zero (d := d) (by linarith [hr.2]) e
  have htsum_zero : ∀ r ∈ Ioo (1 / 4 : ℝ) (3 / 4),
      ∀ X : Sym2 (Fin d → ℤ) → ℝ, ∑' e, cw r e * X e = 0 := by
    intro r hr X
    have hterm : ∀ e, cw r e * X e = 0 := by
      intro e
      rw [hwzero r hr e, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  have key := hasDerivAt_integral_cutoff_pow_binomial_of_insert_moments
    (d := d) (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := fun s => -s) (K' := fun _ => -1)
    (R := R) (u := (1 / 4 : ℝ)) (v := (3 / 4 : ℝ)) (r₀ := (1 / 2 : ℝ))
    (by
      intro a _ b _ hab
      change -b ≤ -a
      linarith)
    (by
      intro t _
      exact (hasDerivAt_id t).neg)
    (continuous_const : Continuous fun _ : ℝ => (-1 : ℝ)).continuousOn
    (1 : ℝ≥0) p hp
    (by
      simp only [ModelNorm.toSeminorm_ofNorm]
      exact hχ)
    cw hcw
    (by norm_num) (by norm_num) (by norm_num) hR
    (by
      intro z hz
      by_cases h : z = 0
      · subst h
        have h0 : ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ (0 : Fin d → ℤ)) = 0 := by simp
        rw [h0] at hz
        linarith [hz.1]
      · have h1 : (1 : ℝ) ≤ ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ z) := by
          simpa using one_le_normSeminorm_intCast (d := d) h
        linarith [hz.2])
    (fun r hr e => by
      have h := lintegral_pow_encard_cluster_insert_ne_top_linear (d := d) p (r := r)
        (by linarith [hr.2]) (0 : Fin d → ℤ) e
      simpa only [ModelNorm.toSeminorm_ofNorm] using h)
    (fun _ => 0)
    (fun a _ b _ => intervalIntegrable_const)
    (by
      intro r hr S
      refine (Finset.sum_eq_zero ?_).trans_le (le_refl (0 : ℝ))
      intro e _
      rw [hwzero r hr e, abs_zero, zero_mul])
    (fun n => by
      have h0 : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (volume.restrict (Ioo (1 / 4 : ℝ) (3 / 4))) := aestronglyMeasurable_const
      refine h0.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (htsum_zero r hr _).symm)
    (by
      have h0 : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo (1 / 4 : ℝ) (3 / 4)) :=
        continuousOn_const
      refine h0.congr ?_
      intro r hr
      exact htsum_zero r hr _)
    (by norm_num)
  simpa using key

/-- **The instantiation at scale `R = 1`.** The finite-susceptibility input is the only
scale-dependent hypothesis of `hasDerivAt_integral_linear_cutoff_pow_of_chi`, and at `R = 1`
it holds because the cutoff kernel vanishes off the diagonal: the susceptibility is one. -/
theorem hasDerivAt_integral_linear_cutoff_pow (d : ℕ) (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0))))
      (1 / 2)  :=
  hasDerivAt_integral_linear_cutoff_pow_of_chi (R := 1) d p hp (by norm_num) (by
    rw [chi_linear_cutoffKernel_eq_one (d := d) (0 : Fin d → ℤ)]
    exact ENNReal.one_ne_top)

/-- **The moment function of the linear model is constant near `r₀`.** On the window the law is
that of the empty configuration and the cluster of the origin there is a singleton, so the
moment function equals one and its derivative at `r₀ = 1/2` is zero. -/
theorem hasDerivAt_integral_linear_cutoff_pow_zero (d : ℕ) (p : ℕ) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0)))) 0 (1 / 2) := by
  refine HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)) ?_
  filter_upwards [Iio_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
  exact integral_linear_moment_eq_one (d := d) p hr.le 0

/-- **The binomial sum of the instantiated statement is zero.** The derivative of the moment
function at `r₀ = 1/2` is unique, and it is zero by the constant-on-a-neighbourhood computation,
so the value produced by the conditional theorem — the binomial sum weighted by the rate — is
zero as well. This is the check that the instantiation is consistent: the identity it proves is
`0 = 0`, at a nonzero rate. -/
theorem eq_zero_of_hasDerivAt_integral_linear_cutoff_pow (d : ℕ) (p : ℕ) {S : ℝ}
    (h : HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0)))) S (1 / 2)) : S = 0 :=
  h.unique (hasDerivAt_integral_linear_cutoff_pow_zero d p)


/-! ### The finite-susceptibility input at an interacting scale -/

/-- On `Fin 1 → ℤ` two functions are equal exactly when their coordinates agree. -/
theorem fun_fin_one_eq_iff (a b : Fin 1 → ℤ) : a = b ↔ a 0 = b 0 := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  funext i
  fin_cases i
  exact h

/-- The cut-off kernel of the linear profile at scale `3/2` equals `1/2` at every pair whose
displacement has sup norm exactly one. -/
theorem linear_cutoffKernel_three_halves_of_natAbs_eq_one {x y : Fin 1 → ℤ} (hxy : x ≠ y)
    (h : ((x - y) 0).natAbs = 1) :
    (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2) s(x, y) : ℝ) = 1 / 2 := by
  rw [cutoffKernel_def, radialKernel_of_ne hxy, normSeminorm_fin_one_intCast, h]
  rw [cutoffProfile_of_le (by norm_num : ((1 : ℕ) : ℝ) ≤ 3 / 2),
    Real.coe_toNNReal _ (by norm_num)]
  norm_num

/-- The cut-off kernel of the linear profile at scale `3/2` vanishes at every pair whose
displacement has sup norm at least two. -/
theorem linear_cutoffKernel_three_halves_eq_zero {x y : Fin 1 → ℤ} (hxy : x ≠ y)
    (h : 2 ≤ ((x - y) 0).natAbs) :
    cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2) s(x, y) = 0 := by
  rw [cutoffKernel_def, radialKernel_of_ne hxy, normSeminorm_fin_one_intCast]
  have hlt : (3 / 2 : ℝ) < ((x - y) 0).natAbs := by
    have h2 : (2 : ℝ) ≤ ((x - y) 0).natAbs := by exact_mod_cast h
    linarith
  rw [cutoffProfile_of_lt hlt, Real.toNNReal_zero]

/-- The open probability at a unit displacement, at scale `3/2` and intensity one. -/
theorem intensityProfile_linear_three_halves_of_natAbs_eq_one {x y : Fin 1 → ℤ} (hxy : x ≠ y)
    (h : ((x - y) 0).natAbs = 1) :
    (unitInterval.toNNReal (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (fun s => -s) (3 / 2)) (1 : ℝ≥0) s(x, y)) : ℝ≥0∞) =
      ENNReal.ofReal (1 - Real.exp (-(1 / 2))) := by
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  change ENNReal.ofReal (1 - Real.exp (-(1 : ℝ) *
      (((cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2) s(x, y)) : ℝ≥0) : ℝ))) =
    ENNReal.ofReal (1 - Real.exp (-(1 / 2)))
  rw [linear_cutoffKernel_three_halves_of_natAbs_eq_one hxy h]
  norm_num

/-- The open probability vanishes at every non-unit displacement, at scale `3/2`. -/
theorem intensityProfile_linear_three_halves_eq_zero {x y : Fin 1 → ℤ} (hxy : x ≠ y)
    (h : 2 ≤ ((x - y) 0).natAbs) :
    (unitInterval.toNNReal (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (fun s => -s) (3 / 2)) (1 : ℝ≥0) s(x, y)) : ℝ≥0∞) = 0 := by
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  change ENNReal.ofReal (1 - Real.exp (-(1 : ℝ) *
      (((cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2) s(x, y)) : ℝ≥0) : ℝ))) =
    0
  rw [linear_cutoffKernel_three_halves_eq_zero hxy h]
  simp

/-- **The row sum of the cut-off linear profile at scale `3/2` and intensity one.** The
one-dimensional lattice has exactly two unit displacements, `±1`, so every row sum equals
`2 (1 - e^{-1/2})`. -/
theorem rowSum_linear_three_halves (v : Fin 1 → ℤ) :
    rowSum (fun e => unitInterval.toENNReal (intensityProfile
      (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2)) (1 : ℝ≥0) e)) v =
      2 * ENNReal.ofReal (1 - Real.exp (-(1 / 2))) := by
  rw [rowSum_toENNReal]
  have hzero : ∀ w ∉ ({v + fun _ => (1 : ℤ), v - fun _ => (1 : ℤ)} : Finset (Fin 1 → ℤ)),
      (if w = v then (0 : ℝ≥0∞)
        else (unitInterval.toNNReal (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (fun s => -s) (3 / 2)) (1 : ℝ≥0) s(v, w)) : ℝ≥0∞)) = 0 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    obtain ⟨hw1, hw2⟩ := hw
    by_cases hwv : w = v
    · simp [hwv]
    · rw [ite_eq_right hwv]
      have hne0 : (v - w) 0 ≠ 0 := by
        intro hc
        refine hwv ((fun_fin_one_eq_iff w v).2 ?_)
        simp only [Pi.sub_apply] at hc
        linarith
      have hne1 : (v - w) 0 ≠ 1 := by
        intro hc
        refine hw2 ((fun_fin_one_eq_iff w (v - fun _ => (1 : ℤ))).2 ?_)
        simp only [Pi.sub_apply] at hc ⊢
        linarith
      have hnen1 : (v - w) 0 ≠ -1 := by
        intro hc
        refine hw1 ((fun_fin_one_eq_iff w (v + fun _ => (1 : ℤ))).2 ?_)
        simp only [Pi.sub_apply, Pi.add_apply] at hc ⊢
        linarith
      have h2 : 2 ≤ ((v - w) 0).natAbs := by
        rcases Nat.lt_or_ge ((v - w) 0).natAbs 2 with hlt | hge
        · have hcases : ((v - w) 0).natAbs = 0 ∨ ((v - w) 0).natAbs = 1 := by omega
          rcases hcases with hc | hc
          · exact absurd (Int.natAbs_eq_zero.1 hc) hne0
          · exfalso
            have h1 : ((v - w) 0).natAbs = ((1 : ℤ)).natAbs := by rw [hc]; norm_num
            rcases Int.natAbs_eq_natAbs_iff.mp h1 with hc1 | hc1
            · exact hne1 hc1
            · exact hnen1 hc1
        · exact hge
      exact intensityProfile_linear_three_halves_eq_zero (fun hv => hwv hv.symm) h2
  rw [tsum_eq_sum (s := ({v + fun _ => (1 : ℤ), v - fun _ => (1 : ℤ)} : Finset (Fin 1 → ℤ)))
    (fun w hw => hzero w hw)]
  have hplus : ((v + fun _ => (1 : ℤ)) : Fin 1 → ℤ) ≠ v := by
    intro hc
    have := congrFun hc 0
    simp only [Pi.add_apply] at this
    omega
  have hminus : ((v - fun _ => (1 : ℤ)) : Fin 1 → ℤ) ≠ v := by
    intro hc
    have := congrFun hc 0
    simp only [Pi.sub_apply] at this
    omega
  have hne : ((v + fun _ => (1 : ℤ)) : Fin 1 → ℤ) ≠ v - fun _ => (1 : ℤ) := by
    intro hc
    have := congrFun hc 0
    simp only [Pi.add_apply, Pi.sub_apply] at this
    omega
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    ite_eq_right hplus, ite_eq_right hminus]
  have hstep : ((v - ((v + fun _ => (1 : ℤ)) : Fin 1 → ℤ)) 0).natAbs = 1 := by
    simp only [Pi.sub_apply, Pi.add_apply]
    norm_num
  have hstep' : ((v - ((v - fun _ => (1 : ℤ)) : Fin 1 → ℤ)) 0).natAbs = 1 := by
    simp only [Pi.sub_apply]
    norm_num
  rw [intensityProfile_linear_three_halves_of_natAbs_eq_one (fun hv => hplus hv.symm) hstep,
    intensityProfile_linear_three_halves_of_natAbs_eq_one (fun hv => hminus hv.symm) hstep']
  ring

/-- **The susceptibility of the cut-off linear profile at scale `3/2` is finite.** At intensity
one the model is nearest-neighbour bond percolation on `ℤ` with `q = 1 - e^{-1/2}`: the row sum
is `2 (1 - e^{-1/2}) < 1` because `e^{-1/2} > 1/2`, so the row-sum criterion applies. -/
theorem chi_linear_cutoffKernel_three_halves_lt_top (o : Fin 1 → ℤ) :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2))
      (1 : ℝ≥0)) o < ⊤ := by
  have h_exp : (1 / 2 : ℝ) < Real.exp (-(1 / 2)) := by
    have := Real.add_one_lt_exp (x := -(1 / 2)) (by norm_num)
    linarith
  have hExp : (2 : ℝ) * (1 - Real.exp (-(1 / 2))) < 1 := by linarith
  refine chi_lt_top_of_rowSum _ (ENNReal.ofReal (2 * (1 - Real.exp (-(1 / 2)))))
    (fun v => ?_) ?_ o
  · rw [rowSum_linear_three_halves]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [ENNReal.ofReal_lt_one]
    exact hExp

/-- **The instantiation at the interacting scale `R = 3/2`.** All the inputs of the conditional
binomial theorem hold with the finite-susceptibility hypothesis taken at a scale where the model
is nearest-neighbour percolation rather than empty. -/
theorem hasDerivAt_integral_linear_cutoff_pow_three_halves (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin 1 → ℤ,
              (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin 1 → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0))))
      (1 / 2)  :=
  hasDerivAt_integral_linear_cutoff_pow_of_chi (d := 1) (R := 3 / 2) p hp (by norm_num) (by
    have h := chi_linear_cutoffKernel_three_halves_lt_top (0 : Fin 1 → ℤ)
    exact ne_of_lt h)

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

variable {d : ℕ} {K K' : ℝ → ℝ}

/-! ### Uniform limits of continuous functions -/

/-- **A uniform limit of continuous functions is continuous.** Stated with an explicit
`ε`-approximation, which is the form in which the cap passage below produces it. -/
theorem continuousOn_of_forall_exists_uniform_approx {ι : Type*} {s : Set ℝ} {f : ℝ → ℝ}
    {g : ι → ℝ → ℝ} (hg : ∀ n, ContinuousOn (g n) s)
    (happrox : ∀ ε > 0, ∃ n, ∀ x ∈ s, |f x - g n x| ≤ ε) :
    ContinuousOn f s := by
  intro x₀ hx₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := happrox (ε / 3) (by linarith)
  have hgx : ContinuousWithinAt (g n) s x₀ := hg n x₀ hx₀
  rw [Metric.continuousWithinAt_iff] at hgx
  obtain ⟨δ, hδ0, hδ⟩ := hgx (ε / 3) (by linarith)
  refine ⟨δ, hδ0, fun x hx hxd => ?_⟩
  have h1 : |f x - g n x| ≤ ε / 3 := hn x hx
  have h2 : |f x₀ - g n x₀| ≤ ε / 3 := hn x₀ hx₀
  have h3 : dist (g n x) (g n x₀) < ε / 3 := hδ hx hxd
  rw [Real.dist_eq] at h3
  rw [Real.dist_eq]
  have hkey : f x - f x₀ = (f x - g n x) + (g n x - g n x₀) + (g n x₀ - f x₀) := by ring
  have hstep : |f x - f x₀| ≤ |f x - g n x| + |g n x - g n x₀| + |g n x₀ - f x₀| := by
    rw [hkey]
    exact abs_add_three _ _ _
  have h2' : |g n x₀ - f x₀| ≤ ε / 3 := by rw [abs_sub_comm]; exact h2
  linarith

/-! ### The uncapped flux from a uniform-in-the-parameter dominator -/

/-- **Flux continuity from a uniform dominator.** If each summand of the uncapped pivotal flux
is continuous in the cut-off parameter on `(u, v)`, and one summable function of the pair
dominates every summand *for every parameter value* in `(u, v)`, then the flux series itself is
continuous on `(u, v)`.

The hypothesis `hdom` is stronger than the all-pairs dominator of the cap passage, which is
allowed to depend on the parameter: the constant there may move with `r`, and a series of
continuous functions has no reason to be continuous under a parameter-dependent bound. -/
theorem continuousOn_flux_cutoff_of_uniform_dominator {N : ModelNorm (Fin d → ℝ)} (β : ℝ≥0)
    (p : ℕ) (o : Fin d → ℤ) {u v : ℝ} (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    {g : Sym2 (Fin d → ℤ) → ℝ} (hg : Summable g)
    (hpair : ∀ e, ContinuousOn (fun r => cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v))
    (hdom : ∀ (e : Sym2 (Fin d → ℤ)) ⦃r : ℝ⦄, r ∈ Ioo u v →
      |cw r e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ g e) :
    ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v) :=
  continuousOn_tsum (u := g) (f := fun e r => cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
    hpair hg fun e r hr => by rw [Real.norm_eq_abs]; exact hdom e hr

/-! ### The capped flux is continuous -/

/-- **Continuity of the capped pivotal flux in the cut-off parameter.** This is the
bounded-observable theorem `continuousOn_flux_cutoff` at the cap `n ↦ min M (n ^ p)`, which is
bounded by `M` and eventually constant; no unbounded observable occurs. -/
theorem continuousOn_flux_cutoff_capped {N : ModelNorm (Fin d → ℝ)}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u v : ℝ} (hu : 0 < u)
    (hvR : v ≤ R) (hI : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (M : ℝ) (hM : 0 ≤ M) :
    ContinuousOn (fun r => ∑' e,
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v) :=
  continuousOn_flux_cutoff (F := fun n : ℕ∞ => (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ p)).toReal)
    (m := M) hKa hK' hK'c β (abs_capped_pow_toReal_le p hM) (capped_pow_eventually_const p hp hM)
    o hχ hu hvR hI

/-- **Continuity of the capped pivotal term of a single pair.** The per-pair form of
`continuousOn_flux_cutoff_capped`. -/
theorem continuousOn_pivotal_cutoff_capped {N : ModelNorm (Fin d → ℝ)}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u : ℝ} (hu : 0 < u)
    (e : Sym2 (Fin d → ℤ)) (M : ℝ) (hM : 0 ≤ M) :
    ContinuousOn (fun r => ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u R) :=
  continuousOn_pivotal_cutoff (F := fun n : ℕ∞ => (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ p)).toReal)
    (m := M) hKa hK' hK'c β (abs_capped_pow_toReal_le p hM) (capped_pow_eventually_const p hp hM)
    o hχ hu e

/-! ### The uncapped flux from a uniform-in-the-parameter cap approximation -/

/-- **The uncapped flux is continuous once the capped fluxes approximate it uniformly in the
parameter.** The capped flux is continuous in the parameter by `continuousOn_flux_cutoff_capped`,
so a uniform-in-`r` approximation by capped fluxes gives the uncapped continuity.

The hypothesis `hcap` is exactly what the pointwise all-pairs dominator of the cap passage does
*not* supply: the cap error may be finite at every parameter and yet not tend to zero uniformly
on `(u, v)`. -/
theorem continuousOn_flux_cutoff_of_uniform_cap {N : ModelNorm (Fin d → ℝ)}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u v : ℝ} (hu : 0 < u)
    (hvR : v ≤ R) (hI : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hcap : ∀ ε > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Ioo u v,
      |(∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))) -
        (∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
          ∂(law (intensityProfile (cutoffKernel N K r) β)))| ≤ ε) :
    ContinuousOn (fun r => ∑' e,
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v) := by
  refine continuousOn_of_forall_exists_uniform_approx (ι := {M : ℝ // 0 ≤ M})
    (g := fun M r => ∑' e,
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, ((min (ENNReal.ofReal M.val) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (ENNReal.ofReal M.val) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
    (fun M => continuousOn_flux_cutoff_capped hKa hK' hK'c β p hp o hχ hu hvR hI M.val M.2)
    (fun ε hε => ?_)
  obtain ⟨M, hM0, hM⟩ := hcap ε hε
  exact ⟨⟨M, hM0⟩, fun r hr => hM r hr⟩

/-! ### The last fundamental-theorem-of-calculus step with an almost-everywhere limit -/

/-- **The cap passage's last step needs only an a.e. limit, not continuity.** If the moment
function agrees near `r₀` with `ψ r₀ + ∫_{r₀}^{r} Φ` and `Φ` is strongly measurable near `r₀`
with an almost sure limit `Φ r₀` there, then the moment function is differentiable at `r₀` with
derivative `Φ r₀`. This replaces the continuity input of the cap passage by a strictly weaker
pair of conditions. -/
theorem hasDerivAt_of_ae_tendsto_flux {ψ Φ : ℝ → ℝ} {r₀ : ℝ}
    (hident : ψ =ᶠ[𝓝 r₀] fun r => ψ r₀ + ∫ x in r₀..r, Φ x)
    (hmeas : StronglyMeasurableAtFilter Φ (𝓝 r₀))
    (hlim : Tendsto Φ (𝓝 r₀ ⊓ ae volume) (𝓝 (Φ r₀))) :
    HasDerivAt ψ (Φ r₀) r₀ :=
  ((intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right IntervalIntegrable.refl hmeas hlim)
    |>.const_add (ψ r₀)).congr_of_eventuallyEq hident

/-- Continuity at a point gives the almost sure limit used in
`hasDerivAt_of_ae_tendsto_flux`; the converse fails in general. -/
theorem tendsto_inf_ae_of_continuousAt {f : ℝ → ℝ} {x : ℝ} (h : ContinuousAt f x) :
    Tendsto f (𝓝 x ⊓ ae volume) (𝓝 (f x)) :=
  h.mono_left inf_le_left


/-- **Per-pair uncapped continuity from a uniform-in-the-parameter cap bound.** The per-pair
companion of `continuousOn_flux_cutoff_of_uniform_cap`, and the `hpair` input of
`continuousOn_flux_cutoff_of_uniform_dominator`: the capped term of a pair is continuous
(`continuousOn_pivotal_cutoff_capped`), so a cap approximation uniform on `(u, R)` gives the
uncapped term. -/
theorem continuousOn_pivotal_cutoff_uncapped_of_uniform_cap {N : ModelNorm (Fin d → ℝ)}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u : ℝ} (hu : 0 < u)
    (e : Sym2 (Fin d → ℤ))
    (hrem : ∀ ε > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Ioo u R,
      |(∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))) -
        (∫ ω, ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
          ∂(law (intensityProfile (cutoffKernel N K r) β)))| ≤ ε) :
    ContinuousOn (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u R) := by
  refine continuousOn_of_forall_exists_uniform_approx (ι := {M : ℝ // 0 ≤ M})
    (g := fun M r => ∫ ω,
      ((min (ENNReal.ofReal M.val) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (ENNReal.ofReal M.val) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
    (fun M => continuousOn_pivotal_cutoff_capped hKa hK' hK'c β p hp o hχ hu e M.val M.2)
    (fun ε hε => ?_)
  obtain ⟨M, hM0, hM⟩ := hrem ε hε
  exact ⟨⟨M, hM0⟩, fun r hr => hM r hr⟩

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

open Classical in
/-- The real integral of the closed-coordinate truncated extended-nonnegative increment is
exactly the real closed-coordinate difference, assuming only a.e. finiteness after insertion. -/
theorem integral_toReal_closed_pivotal (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (p : ℕ) (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal =
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ p) ∂μ := by
  have hm : AEMeasurable _ μ :=
    (PercLib.Models.LongRange.measurable_closed_pivotal_integrand o p e).aemeasurable
  have hne : ∀ᵐ ω ∂μ, (if e ∈ ω then (0 : ℝ≥0∞) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ≠ ⊤ := by
    filter_upwards [hfin] with ω hω
    by_cases he : e ∈ ω
    · simp [he]
    · rw [ite_eq_right he]
      exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hω) tsub_le_self
  rw [← integral_toReal_eq_toReal_lintegral hm hne]
  apply integral_congr_ae
  filter_upwards [hfin] with ω hω
  by_cases he : e ∈ ω
  · simp [he]
  · rw [ite_eq_right he, ite_eq_right he]
    have hs : ω \ {e} = ω := Set.sdiff_singleton_eq_self he
    have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
        ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
      encard_cluster_sdiff_le_insert_coe ω e o
    rw [hs] at hle
    exact PercLib.Models.LongRange.toReal_pow_sub_pow hle hω p

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- A finite bound on each binomial diagram term gives the same bound on the weighted pivotal
flux at that radius. -/
theorem lintegral_radial_pivotal_le_of_binomial_diagram {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (r : ℝ)
    (hins : ∀ e : Sym2 (Fin d → ℤ), (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (D : ℕ → ℝ≥0∞)
    (hD : ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y, (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
        ∂(law (intensityProfile (cutoffKernel N K r) β)) ≤ D ℓ)
    {u v : ℝ} (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hr : r ∈ Ioo u v) :
    (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster ω 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))) ≤ ∑ ℓ ∈ Finset.range p, D ℓ := by
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K r) β)
  have hmom : (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ :=
    lintegral_pow_encard_ne_top_of_insert (s(0, 0)) 0 p (hins (s(0, 0)))
  have hrootfin : μ {ω : Config (Fin d → ℤ) | ((cluster ω 0).encard : ℝ≥0∞) = ⊤} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_coe 0) p hp hmom
  have hENN := i41_enn_of_root_finite (p := p) μ (law_cutoffKernel_map_translate K r β)
    hrootfin hcorner hr
  rw [hENN]
  exact Finset.sum_le_sum fun ℓ hℓ => hD ℓ hℓ

open Classical in
/-- The per-pair cutoff coefficient is the rate times `toReal` of the radially weighted
closed-coordinate l integral. -/
theorem cutoff_weight_mul_integral_eq_rate_mul_closed_toReal {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel N K r) β))) (e : Sym2 (Fin d → ℤ)) :
    cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ((β : ℝ) * -K' r) * ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal) := by
  rcases radialKernel_indicator_eq_zero_or_one N r e with h0 | h1
  · simp [hcw e, h0]
  · have hp := cutoff_pivotal_eq_closed_pow (K := K) (K' := K') p β r e o
      (by rw [h1]; norm_num) (hfin e) (hint e)
    rw [h1, one_mul] at hp
    have hclose := integral_toReal_closed_pivotal
      (law (intensityProfile (cutoffKernel N K r) β)) e o p (hfin e)
    rw [integral_pivotal_pow_eq_real_sub
      (law (intensityProfile (cutoffKernel N K r) β)) e o p (hfin e)]
    rw [← hclose] at hp
    simpa only [hcw e, h1, one_mul, mul_left_comm, mul_assoc] using hp

open Classical in
/-- A finite extended-nonnegative closed-coordinate flux controls the absolute cutoff
pivotal sums, with the absolute cutoff rate as its constant. -/
theorem finite_sum_cutoff_pivotal_le_toReal_of_lintegral_le {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ} (p : ℕ) (β : ℝ≥0) (r : ℝ)
    (o : Fin d → ℤ) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hp : 1 ≤ p)
    (hins : ∀ e, (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (D : ℝ≥0∞) (hDtop : D ≠ ⊤)
    (hD : (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))) ≤ D) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
      |(β : ℝ) * -K' r| * D.toReal := by
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K r) β)
  let w : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e =>
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0)
  let Q : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e => ∫⁻ ω,
    (if e ∈ ω then (0 : ℝ≥0∞) else
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
  have hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ := by
    intro e
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o)
      p hp (hins e)
  have hint : ∀ e, Integrable
      (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p) μ := by
    intro e
    exact integrable_toReal_pow_encard_cluster_insert e o p (hins e)
  have hQ : ∀ e, Q e ≠ ⊤ := by
    intro e
    refine ne_top_of_le_ne_top
      (lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top e o p (hins e)) ?_
    exact lintegral_mono fun ω => by
      by_cases he : e ∈ ω
      · simp [he]
      · rw [ite_eq_right he, Set.sdiff_singleton_eq_self he]
  have hT : (∑' e, w e * Q e) ≤ D := by
    rw [show (∑' e, w e * Q e) = ∫⁻ ω, ∑' e, w e *
      (if e ∈ ω then (0 : ℝ≥0∞) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ from
      tsum_lintegral_closed_pivotal μ p o w]
    exact hD
  have hTtop : (∑' e, w e * Q e) ≠ ⊤ := ne_top_of_le_ne_top hDtop hT
  have hsum : Summable (fun e => (w e * Q e).toReal) := ENNReal.summable_toReal hTtop
  have hbound : ∀ S : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ S, (w e * Q e).toReal ≤ D.toReal := by
    intro S
    calc
      ∑ e ∈ S, (w e * Q e).toReal ≤ ∑' e, (w e * Q e).toReal :=
        hsum.sum_le_tsum S (fun _ _ => ENNReal.toReal_nonneg)
      _ = (∑' e, w e * Q e).toReal :=
        (ENNReal.tsum_toReal_eq fun e => ENNReal.mul_ne_top ENNReal.coe_ne_top (hQ e)).symm
      _ ≤ D.toReal := (ENNReal.toReal_le_toReal hTtop hDtop).2 hT
  intro S
  calc
    ∑ e ∈ S, |cw e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ| =
        |(β : ℝ) * -K' r| * ∑ e ∈ S, (w e * Q e).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      have hcoef := cutoff_weight_mul_integral_eq_rate_mul_closed_toReal
        (K := K) (K' := K') p β r o cw hcw hfin hint e
      change |cw e| *
        |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ| =
        |(β : ℝ) * -K' r| * (w e * Q e).toReal
      calc
        |cw e| * |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ| =
            |cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ| := (abs_mul _ _).symm
        _ = |((β : ℝ) * -K' r) *
            ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * (Q e).toReal)| := by
          rw [hcoef]
        _ = |(β : ℝ) * -K' r| *
            ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) * (Q e).toReal) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg
            (radialKernel N _ e).coe_nonneg ENNReal.toReal_nonneg)]
        _ = |(β : ℝ) * -K' r| * (w e * Q e).toReal := by
          rw [ENNReal.toReal_mul]
          simp [w]
    _ ≤ |(β : ℝ) * -K' r| * D.toReal :=
      mul_le_mul_of_nonneg_left (hbound S) (abs_nonneg _)

open Classical in
/-- The fused binomial-diagram estimate gives the cutoff dominator used by the derivative
interface. Keeping its several inputs separate records precisely which analytic and geometric
estimates remain; this is not an assumption of Lemma I.4.1 itself. -/
theorem finite_sum_cutoff_pivotal_le_of_binomial_diagram {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (r : ℝ)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    (hins : ∀ e : Sym2 (Fin d → ℤ), (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (D : ℕ → ℝ≥0∞) (hDtop : (∑ ℓ ∈ Finset.range p, D ℓ) ≠ ⊤)
    (hD : ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y, (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
        ∂(law (intensityProfile (cutoffKernel N K r) β)) ≤ D ℓ)
    {u v : ℝ} (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hr : r ∈ Ioo u v) :
    ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤
      |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal := by
  refine finite_sum_cutoff_pivotal_le_toReal_of_lintegral_le p β r 0 (cw r) (hcw r) hp hins
    (∑ ℓ ∈ Finset.range p, D ℓ) hDtop ?_
  exact lintegral_radial_pivotal_le_of_binomial_diagram β p hp r hins D hD hcorner hr


open Classical in
/-- The cutoff binomial derivative from a finite root-cluster moment and a uniform finite
binomial-diagram bound. The diagram supplies both the dominator and its local integrability;
the uncapped flux continuity remains an explicit, separate input. This assembly interface keeps
all those inputs visible rather than introducing a new structure. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_root_moment_of_diagram {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (D : ℕ → ℝ≥0∞) (hDtop : (∑ ℓ ∈ Finset.range p, D ℓ) ≠ ⊤)
    (hD : ∀ r ∈ Ioo u v, ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
      ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y, (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
          (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ D ℓ)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  let Kd : ℝ → ℝ := fun r => |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal
  have hmom : ∀ r ∈ Ioo u v, ∀ y : Fin d → ℤ,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
    intro r hr y
    exact vertex_moment_ne_top_of_root_moment β r p y (hroot r (Set.mem_union_left _ hr))
  have hins : ∀ r ∈ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ :=
    insert_moments_of_vertex_moments_Ioo_modelNorm β p 0 hmom
  have hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) 0 ≠ ⊤ :=
    chi_ne_top_of_lintegral_pow_ne_top _ 0 p hp (hroot R (Set.mem_union_right _ rfl))
  have hKdc : ContinuousOn Kd (Ioi 0) := by
    change ContinuousOn
      (fun r => |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal) (Ioi 0)
    exact (continuousOn_const.mul hK'c.neg).abs.mul continuousOn_const
  have hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b := by
    intro a ha b hb
    apply ContinuousOn.intervalIntegrable (hKdc.mono ?_)
    intro x hx
    change x ∈ Icc (min a b) (max a b) at hx
    have hmin : 0 < min a b := lt_min (hu.trans ha.1) (hu.trans hb.1)
    exact hmin.trans_le hx.1
  have hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤ Kd r := by
    intro r hr S
    exact finite_sum_cutoff_pivotal_le_of_binomial_diagram β p hp r cw hcw (hins r hr)
      D hDtop (hD r hr) hcorner hr S
  exact hasDerivAt_integral_cutoff_pow_binomial_of_measurable hKa hK' hK'c β p hp hχ
    cw hcw hu hur hrv hvR hcorner hins Kd hKdint hKd hcont


end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

open Classical in
/-- A uniform `n`-th moment at every vertex bounds the mixed finite-ball cluster diagram
with exponents summing to `n`. The estimate also holds for an infinite vertex set. -/
theorem lintegral_cluster_mul_tsum_compl_pow_le {V : Type*} [Countable V]
    (μ : Measure (Config V)) (o : V) (W : Set V) (a b n : ℕ) (hab : a + b = n)
    (M : ℝ≥0∞) (hmom : ∀ y, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ n ∂μ) ≤ M) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ a *
      (∑' y, (if y ∈ W then (1 : ℝ≥0∞) else 0) *
        (conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ b) ∂μ) ≤
      (W.encard : ℝ≥0∞) * (2 * M) := by
  have hA (k : ℕ) : Measurable (fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) ^ k) :=
    ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard_cluster o)).pow_const k
  have hB (y : V) (k : ℕ) :
      Measurable (fun ω : Config V => ((cluster ω y).encard : ℝ≥0∞) ^ k) :=
    ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard_cluster y)).pow_const k
  have hind (o y : V) : Measurable (fun ω : Config V =>
      (conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
    measurable_const.indicator (measurableSet_conn o y).compl
  have hpow (A B : ℝ≥0∞) : A ^ a * B ^ b ≤ A ^ n + B ^ n := by
    rcases le_total A B with hAB | hBA
    · calc
        A ^ a * B ^ b ≤ B ^ a * B ^ b := mul_le_mul_left (pow_le_pow_left' hAB a) _
        _ = B ^ (a + b) := (pow_add _ _ _).symm
        _ = B ^ n := by rw [hab]
        _ ≤ A ^ n + B ^ n := le_add_left le_rfl
    · calc
        A ^ a * B ^ b ≤ A ^ a * A ^ b := mul_le_mul_right (pow_le_pow_left' hBA b) _
        _ = A ^ (a + b) := (pow_add _ _ _).symm
        _ = A ^ n := by rw [hab]
        _ ≤ A ^ n + B ^ n := le_add_right le_rfl
  have hterm : ∀ y : V, (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ a *
      ((if y ∈ W then (1 : ℝ≥0∞) else 0) *
        (conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ b) ∂μ) ≤
      if y ∈ W then 2 * M else 0 := by
    intro y
    by_cases hy : y ∈ W
    · simp only [hy, ite_true, one_mul]
      calc
        (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ a *
          ((conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ b) ∂μ) ≤
            ∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ n +
              ((cluster ω y).encard : ℝ≥0∞) ^ n) ∂μ := by
          refine lintegral_mono fun ω => ?_
          calc
            ((cluster ω o).encard : ℝ≥0∞) ^ a *
                ((conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
                  ((cluster ω y).encard : ℝ≥0∞) ^ b) ≤
              ((cluster ω o).encard : ℝ≥0∞) ^ a *
                ((cluster ω y).encard : ℝ≥0∞) ^ b := by
              apply mul_le_mul_right
              calc
                (conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
                    ((cluster ω y).encard : ℝ≥0∞) ^ b ≤
                    1 * ((cluster ω y).encard : ℝ≥0∞) ^ b := by
                  apply mul_le_mul_left
                  by_cases h : ω ∈ conn o y <;> simp [h]
                _ = ((cluster ω y).encard : ℝ≥0∞) ^ b := one_mul _
            _ ≤ ((cluster ω o).encard : ℝ≥0∞) ^ n +
                ((cluster ω y).encard : ℝ≥0∞) ^ n := hpow _ _
        _ = (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ n ∂μ) +
            (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ n ∂μ) := lintegral_add_left (hA n) _
        _ ≤ M + M := add_le_add (hmom o) (hmom y)
        _ = 2 * M := by ring
    · simp [hy]
  calc
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ a *
      (∑' y, (if y ∈ W then (1 : ℝ≥0∞) else 0) *
        (conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ b) ∂μ) =
        ∑' y, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ a *
          ((if y ∈ W then (1 : ℝ≥0∞) else 0) *
            (conn o y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ b) ∂μ := by
      conv_lhs =>
        enter [2, ω]
        rw [← ENNReal.tsum_mul_left]
      exact lintegral_tsum fun y => ((hA a).mul
        ((measurable_const.mul (hind o y)).mul (hB y b))).aemeasurable
    _ ≤ ∑' y, if y ∈ W then 2 * M else 0 := ENNReal.tsum_le_tsum hterm
    _ = (W.encard : ℝ≥0∞) * (2 * M) := by
      change (∑' y, W.indicator (fun _ => (2 : ℝ≥0∞) * M) y) = _
      rw [← tsum_subtype W (fun _ => 2 * M), ENNReal.tsum_set_const]

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond

/-- The binomial diagram at scale `r` is bounded by the cardinality of its norm ball once
the `(p+1)`-st moment at every vertex is bounded. -/
theorem lintegral_i41_binomial_term_le_of_vertex_moments {d : ℕ}
    {N : Seminorm ℝ (Fin d → ℝ)} (μ : Measure (Config (Fin d → ℤ))) (p ℓ : ℕ)
    (hℓ : ℓ < p) (M : ℝ≥0∞)
    (hmom : ∀ y, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ (p + 1) ∂μ) ≤ M) (r : ℝ) :
    (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
      (∑' y, (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
        (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) ∂μ) ≤
      ({y : Fin d → ℤ | N (Int.cast ∘ y) ≤ r}.encard : ℝ≥0∞) * (2 * M) := by
  apply lintegral_cluster_mul_tsum_compl_pow_le μ 0 {y : Fin d → ℤ | N (Int.cast ∘ y) ≤ r}
    (ℓ + 1) (p - ℓ) (p + 1) (by omega) M hmom

/-- Closed lattice balls for a model norm are finite. -/
theorem finite_norm_le_closed {d : ℕ} (N : ModelNorm (Fin d → ℝ)) (R : ℝ) :
    {z : Fin d → ℤ | N (Int.cast ∘ z) ≤ R}.Finite := by
  refine ((Set.finite_singleton (0 : Fin d → ℤ)).union
    (finite_norm_lt N (R + 1))).subset ?_
  intro z hz
  by_cases hzero : z = 0
  · exact Or.inl hzero
  · exact Or.inr ⟨hzero, hz.trans_lt (lt_add_one R)⟩

/-- Translation invariance makes every cutoff vertex moment equal to the root moment. -/
theorem lintegral_pow_encard_cluster_eq_root {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {K : ℝ → ℝ} (β : ℝ≥0) (r : ℝ) (p : ℕ) (y : Fin d → ℤ) :
    (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) =
    (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) := by
  have hmap : (law (intensityProfile (cutoffKernel (d := d) N K r) β)).map
      (fun ω : Config (Fin d → ℤ) => Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) =
      law (intensityProfile (cutoffKernel (d := d) N K r) β) :=
    law_cutoffKernel_map_translate (N := N) K r β (-y)
  have hcl : ∀ ω : Config (Fin d → ℤ),
      ((cluster (Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) 0).encard : ℝ≥0∞) =
        ((cluster ω y).encard : ℝ≥0∞) := by
    intro ω
    have h' := encard_cluster_translate (-y) y ω
    rw [show y + -y = 0 from add_neg_cancel y] at h'
    rw [h']
  have hstep : (∫⁻ ω, ((cluster (Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) 0).encard :
        ℝ≥0∞) ^ p ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) =
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) := by
    rw [← lintegral_map_shift (law (intensityProfile (cutoffKernel (d := d) N K r) β)) (-y)
      (fun ω => ((cluster ω 0).encard : ℝ≥0∞) ^ p), hmap]
  calc
    (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) =
        ∫⁻ ω, ((cluster (Sym2.map (fun x : Fin d → ℤ => x + -y) '' ω) 0).encard :
          ℝ≥0∞) ^ p ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) :=
      lintegral_congr fun ω => by rw [hcl ω]
    _ = _ := hstep

/-- A root-moment bound is equally a bound at every vertex of the cutoff lattice. -/
theorem lintegral_pow_encard_cluster_le_of_root_le {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {K : ℝ → ℝ} (β : ℝ≥0) (r : ℝ) (p : ℕ) (y : Fin d → ℤ) (M : ℝ≥0∞)
    (h : (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M) :
    (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
  rw [lintegral_pow_encard_cluster_eq_root β r p y]
  exact h

/-- A uniform root `(p+1)`-moment bounds every term of the binomial diagram, uniformly in
a cutoff interval, with a finite constant determined by the outer lattice ball. -/
theorem exists_uniform_i41_diagram_bound_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ} (β : ℝ≥0) (p : ℕ)
    (M : ℝ≥0∞) (hM : M ≠ ⊤) {u v : ℝ}
    (hroot : ∀ r ∈ Ioo u v, (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M) :
    ∃ D : ℕ → ℝ≥0∞, (∑ ℓ ∈ Finset.range p, D ℓ) ≠ ⊤ ∧
      ∀ r ∈ Ioo u v, ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ D ℓ := by
  let B : Set (Fin d → ℤ) := {y | N (Int.cast ∘ y) ≤ v}
  let D : ℕ → ℝ≥0∞ := fun ℓ => (p.choose ℓ : ℝ≥0∞) * ((B.encard : ℝ≥0∞) * (2 * M))
  have hBfin : B.Finite := finite_norm_le_closed N v
  have hBtop : (B.encard : ℝ≥0∞) ≠ ⊤ :=
    ENat.toENNReal_ne_top.2 hBfin.encard_lt_top.ne
  refine ⟨D, ?_, ?_⟩
  · apply ENNReal.sum_ne_top.2
    intro ℓ _
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top hBtop (ENNReal.mul_ne_top (by norm_num) hM))
  · intro r hr ℓ hℓ
    have hmom : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
      intro y
      exact lintegral_pow_encard_cluster_le_of_root_le β r (p + 1) y M (hroot r hr)
    have hbound := lintegral_i41_binomial_term_le_of_vertex_moments (N := N.toSeminorm)
      (law (intensityProfile (cutoffKernel (d := d) N K r) β))
      p ℓ (Finset.mem_range.mp hℓ) M hmom r
    have hsub : {y : Fin d → ℤ | N (Int.cast ∘ y) ≤ r} ⊆ B := by
      intro y hy
      exact hy.trans hr.2.le
    calc
      (p.choose ℓ : ℝ≥0∞) *
          ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (ℓ + 1) *
            (∑' y, (if N (Int.cast ∘ y) ≤ r then 1 else 0) *
              (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤
          (p.choose ℓ : ℝ≥0∞) *
            (({y : Fin d → ℤ | N (Int.cast ∘ y) ≤ r}.encard : ℝ≥0∞) * (2 * M)) :=
        mul_le_mul_right hbound _
      _ ≤ (p.choose ℓ : ℝ≥0∞) * ((B.encard : ℝ≥0∞) * (2 * M)) := by
        apply mul_le_mul_right
        apply mul_le_mul_left
        exact ENat.toENNReal_mono (Set.encard_le_encard hsub)
      _ = D ℓ := rfl

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- The cutoff binomial derivative from a uniform finite `(p+1)`-st root-moment bound.
This supplies every vertex moment needed by the binomial diagram, the diagram dominator and its
local integrability, and the original root-`p` finiteness. The uncapped flux continuity remains
an explicit, separate input; sharpness and the all-radius corner claim are not asserted. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  have hrootp : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ),
      (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
    intro r hr
    refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hM (hroot r hr)) ?_
    refine lintegral_mono fun ω => ?_
    have hbase : (1 : ℝ≥0∞) ≤ ((cluster ω 0).encard : ℝ≥0∞) := by
      exact_mod_cast one_le_encard_cluster ω 0
    exact pow_le_pow_right₀ hbase (Nat.le_succ p)
  obtain ⟨D, hDtop, hD⟩ := exists_uniform_i41_diagram_bound_of_root_succ_moment
    (K := K) β p M hM (fun r hr => hroot r (Set.mem_union_left _ hr))
  exact hasDerivAt_integral_cutoff_pow_binomial_of_root_moment_of_diagram
    (K := K) (K' := K') (R := R) (u := u) (v := v) (r₀ := r₀)
    hKa hK' hK'c β p hp cw hcw hu hur hrv hvR hcorner hrootp D hDtop hD hcont


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability MeasureTheory Set

open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-- **The root moment is finite throughout the zero-cutoff window.** For `r ≤ 1` the linear
cutoff kernel vanishes identically, so the law is that of the empty configuration and the
cluster of `o` is the singleton `{o}`; its `p`-th moment is one. -/
theorem linear_root_moment_ne_top_of_le_one (p : ℕ) {r : ℝ} (hr : r ≤ 1) (o : Fin d → ℤ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
        (1 : ℝ≥0)))) ≠ ⊤ := by
  rw [linear_intensityProfile_eq_zero_of_le_one hr]
  have hae : (fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) ^ p)
      =ᵐ[law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))] fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [ae_eq_empty_zero_profile (d := d)] with ω hω
    rw [hω, cluster_empty, Set.encard_singleton]
    norm_num
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]
  exact ENNReal.one_ne_top

/-- **Every summand of the binomial diagram vanishes on the window.** A site `y` contributing
to the sum satisfies `N y ≤ r < 1`, hence `y = 0`, and there the connection indicator
`1{y ∉ K}` is zero because `0` is connected to itself. -/
theorem linear_diagram_tsum_eq_zero (p ℓ : ℕ) {r : ℝ} (hr : r < 1) (ω : Config (Fin d → ℤ)) :
    (∑' y : Fin d → ℤ,
      (if ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
        (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) = 0 := by
  rw [ENNReal.tsum_eq_zero]
  intro y
  by_cases hy : y = 0
  · subst hy
    rw [conn_self]
    simp
  · have h1 : (1 : ℝ) ≤ ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ y) := by
      simpa using one_le_normSeminorm_intCast (d := d) hy
    rw [ite_eq_right (by linarith :
      ¬ (ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ y) ≤ r))]
    simp

/-- **Every binomial diagram term has integral zero on the window**, so `D = 0` is a valid
uniform majorant there. -/
theorem linear_diagram_integral_eq_zero (p : ℕ) {r : ℝ} (hr : r < 1) (ℓ : ℕ) :
    (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0)))) = 0 := by
  have hfun : (fun ω : Config (Fin d → ℤ) =>
        ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y : Fin d → ℤ,
            (if ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ y) ≤ r then (1 : ℝ≥0∞) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))) = fun _ => 0 := by
    funext ω
    rw [linear_diagram_tsum_eq_zero (d := d) p ℓ hr ω, mul_zero]
  rw [hfun, lintegral_zero]

/-- The derivative weight vanishes identically on the window, because the strict radial
indicator `1{N e < r}` does. -/
theorem linear_cw_eq_zero {r : ℝ} (hr : r ≤ 1) (e : Sym2 (Fin d → ℤ)) :
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
        Real.exp (-(1 : ℝ) *
          (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ))) = 0 :=
  linear_weight_eq_zero hr e

/-- The whole weighted flux series vanishes on the window. -/
theorem linear_cw_tsum_eq_zero {r : ℝ} (hr : r ≤ 1) (X : Sym2 (Fin d → ℤ) → ℝ) :
    (∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
          Real.exp (-(1 : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ)))) * X e) = 0 := by
  have hterm : ∀ e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
          Real.exp (-(1 : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ)))) * X e = 0 := by
    intro e
    rw [linear_cw_eq_zero hr e, zero_mul]
  rw [tsum_congr hterm, tsum_zero]

/-- **The rate at `r₀ = 1/2` is one**, so the instantiation has nonzero cutoff rate. -/
theorem linear_rate_eq_one :
    ((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) = 1 := by
  norm_num

/-! ### The instantiation -/

open Classical in
/-- **The uniform binomial-diagram derivative holds non-vacuously in the linear model.**

With `N` the sup norm on `ℤ^d`, `K s = -s`, `K' = -1`, `β = 1`, `u = 1/4`, `v = 3/4`,
`r₀ = 1/2` and outer scale `R = 1`, the majorant `D = 0` satisfies every hypothesis of
`hasDerivAt_integral_cutoff_pow_binomial_of_root_moment_of_diagram`: the root moments are finite
on the window and at `R` by `linear_root_moment_ne_top_of_le_one`, the diagram terms vanish by
`linear_diagram_integral_eq_zero`, and the flux series vanishes identically on the window, which
gives both the dominator and its continuity. The conclusion is the same proposition as the
existing witness `hasDerivAt_integral_linear_cutoff_pow`. -/
theorem hasDerivAt_integral_linear_cutoff_pow_diagram (d : ℕ) (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0))))
      (1 / 2) := by
  let cw : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r e =>
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
        Real.exp (-(1 : ℝ) *
          (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ)))
  have hcw : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)), cw r e =
      (radialKernel (ModelNorm.ofNorm (Fin d → ℝ))
        (fun s => if s < r then 1 else 0) e : ℝ) *
        (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) r) *
          Real.exp (-(((1 : ℝ≥0) : ℝ)) *
            (cutoffKernel (ModelNorm.ofNorm (Fin d → ℝ)) (fun s => -s) r e : ℝ))) :=
    fun _ _ => rfl
  have hwzero : ∀ r ∈ Ioo (1 / 4 : ℝ) (3 / 4), ∀ e, cw r e = 0 := by
    intro r hr e
    exact linear_cw_eq_zero (d := d) (by linarith [hr.2]) e
  have htsum_zero : ∀ r ∈ Ioo (1 / 4 : ℝ) (3 / 4),
      ∀ X : Sym2 (Fin d → ℤ) → ℝ, ∑' e, cw r e * X e = 0 := by
    intro r hr X
    have hterm : ∀ e, cw r e * X e = 0 := by
      intro e
      rw [hwzero r hr e, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  have key := hasDerivAt_integral_cutoff_pow_binomial_of_root_moment_of_diagram
    (d := d) (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := fun s => -s) (K' := fun _ => -1)
    (R := 1) (u := (1 / 4 : ℝ)) (v := (3 / 4 : ℝ)) (r₀ := (1 / 2 : ℝ))
    (by
      intro a _ b _ hab
      change -b ≤ -a
      linarith)
    (by
      intro t _
      exact (hasDerivAt_id t).neg)
    (continuous_const : Continuous fun _ : ℝ => (-1 : ℝ)).continuousOn
    (1 : ℝ≥0) p hp
    cw hcw
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      intro z hz
      by_cases h : z = 0
      · subst h
        have h0 : ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ (0 : Fin d → ℤ)) = 0 := by simp
        rw [h0] at hz
        linarith [hz.1]
      · have h1 : (1 : ℝ) ≤ ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ z) := by
          simpa using one_le_normSeminorm_intCast (d := d) h
        linarith [hz.2])
    (by
      intro r hr
      have hr1 : r ≤ 1 := by
        rcases hr with hr | hr
        · exact le_of_lt (by linarith [hr.2])
        · rw [mem_singleton_iff] at hr
          rw [hr]
      exact linear_root_moment_ne_top_of_le_one (d := d) p hr1 0)
    (fun _ => 0)
    (by simp)
    (by
      intro r hr ℓ _
      have h := linear_diagram_integral_eq_zero (d := d) p (by linarith [hr.2]) ℓ
      simp only [ModelNorm.toSeminorm_ofNorm] at h ⊢
      rw [h]
      simp)
    (by
      have h0 : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo (1 / 4 : ℝ) (3 / 4)) :=
        continuousOn_const
      refine h0.congr ?_
      intro r hr
      exact htsum_zero r hr _)
  simpa using key

/-- **The instantiated conclusion is exactly the existing linear witness.** Both terms are
proofs of the same proposition, which is the machine-checked form of the statement that the
diagram interface, applied with `D = 0` on the zero-cutoff window, reproduces the existing
conclusion at `r₀ = 1/2` with rate one. -/
example (d : ℕ) (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0))))
      (1 / 2) :=
  hasDerivAt_integral_linear_cutoff_pow d p hp

/-- **The produced derivative value is zero**, consistently with the moment function being
constant on the window; the nonzero rate multiplies a vanishing binomial sum. -/
theorem linear_diagram_derivative_value_eq_zero (d : ℕ) (p : ℕ) (hp : 1 ≤ p) :
    (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0)))) = 0 :=
  (hasDerivAt_integral_linear_cutoff_pow_diagram d p hp).unique
    (hasDerivAt_integral_linear_cutoff_pow_zero d p)

end PercLib.Models.LongRange

open Filter Set Topology
open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability
open scoped Topology NNReal ENNReal

namespace PercLib.Models.LongRange

/-! ## One-sided limits of the derivative -/

/-- If `f` is differentiable at `n` and its derivative tends to `L` from the left at `n`, then
`L` is the derivative of `f` at `n`. -/
theorem tendsto_deriv_nhdsLT_eq_deriv {f : ℝ → ℝ} {n L m : ℝ}
    (hdiff : ∀ y < n, DifferentiableAt ℝ f y) (hcont : ContinuousAt f n)
    (hL : Tendsto (deriv f) (𝓝[<] n) (𝓝 L)) (hm : HasDerivAt f m n) : L = m := by
  have h1 : HasDerivWithinAt f L (Iic n) n :=
    hasDerivWithinAt_Iic_of_tendsto_deriv (fun y hy => (hdiff y hy).differentiableWithinAt)
      hcont.continuousWithinAt self_mem_nhdsWithin hL
  have e1 : derivWithin f (Iic n) n = L := h1.derivWithin (uniqueDiffWithinAt_Iic n)
  have e2 : derivWithin f (Iic n) n = m :=
    hm.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic n)
  rw [← e1, e2]

/-- If `f` is differentiable at `n` and its derivative tends to `L` from the right at `n`, then
`L` is the derivative of `f` at `n`. -/
theorem tendsto_deriv_nhdsGT_eq_deriv {f : ℝ → ℝ} {n L m : ℝ}
    (hdiff : ∀ y, n < y → DifferentiableAt ℝ f y) (hcont : ContinuousAt f n)
    (hR : Tendsto (deriv f) (𝓝[>] n) (𝓝 L)) (hm : HasDerivAt f m n) : L = m := by
  have h1 : HasDerivWithinAt f L (Ici n) n :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (fun y hy => (hdiff y hy).differentiableWithinAt)
      hcont.continuousWithinAt self_mem_nhdsWithin hR
  have e1 : derivWithin f (Ici n) n = L := h1.derivWithin (uniqueDiffWithinAt_Ici n)
  have e2 : derivWithin f (Ici n) n = m :=
    hm.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici n)
  rw [← e1, e2]

/-- If `f` is differentiable on both sides of `n`, continuous at `n`, and its derivative has the
common one-sided limit `L` at `n`, then `f` is differentiable at `n` with derivative `L`. -/
theorem hasDerivAt_of_tendsto_deriv_oneSided {f : ℝ → ℝ} {n L : ℝ}
    (hdiffL : ∀ y < n, DifferentiableAt ℝ f y) (hdiffR : ∀ y, n < y → DifferentiableAt ℝ f y)
    (hcont : ContinuousAt f n)
    (hL : Tendsto (deriv f) (𝓝[<] n) (𝓝 L)) (hR : Tendsto (deriv f) (𝓝[>] n) (𝓝 L)) :
    HasDerivAt f L n := by
  have h1 : HasDerivWithinAt f L (Iic n) n :=
    hasDerivWithinAt_Iic_of_tendsto_deriv (fun y hy => (hdiffL y hy).differentiableWithinAt)
      hcont.continuousWithinAt self_mem_nhdsWithin hL
  have h2 : HasDerivWithinAt f L (Ici n) n :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (fun y hy => (hdiffR y hy).differentiableWithinAt)
      hcont.continuousWithinAt self_mem_nhdsWithin hR
  simpa using h2.union h1

/-- **Corner criterion.** Suppose that `f` is differentiable on both sides of `n`, continuous at
`n`, and that `deriv f` has one-sided limits `L₁` (from below) and `L₂` (from above) at `n`.
Then `f` has a two-sided derivative at `n` if and only if the two one-sided limits agree; and
then the derivative is their common value. -/
theorem exists_hasDerivAt_iff_tendsto_deriv_oneSided {f : ℝ → ℝ} {n L₁ L₂ : ℝ}
    (hdiffL : ∀ y < n, DifferentiableAt ℝ f y) (hdiffR : ∀ y, n < y → DifferentiableAt ℝ f y)
    (hcont : ContinuousAt f n)
    (hL : Tendsto (deriv f) (𝓝[<] n) (𝓝 L₁)) (hR : Tendsto (deriv f) (𝓝[>] n) (𝓝 L₂)) :
    (∃ m, HasDerivAt f m n) ↔ L₁ = L₂ := by
  constructor
  · rintro ⟨m, hm⟩
    exact (tendsto_deriv_nhdsLT_eq_deriv hdiffL hcont hL hm).trans
      (tendsto_deriv_nhdsGT_eq_deriv hdiffR hcont hR hm).symm
  · intro h
    subst h
    exact ⟨L₁, hasDerivAt_of_tendsto_deriv_oneSided hdiffL hdiffR hcont hL hR⟩

/-- **Corner obstruction.** Different one-sided limits of the derivative at `n` exclude every
two-sided derivative at `n`. -/
theorem not_exists_hasDerivAt_of_tendsto_deriv_oneSided_ne {f : ℝ → ℝ} {n L₁ L₂ : ℝ}
    (hdiffL : ∀ y < n, DifferentiableAt ℝ f y) (hdiffR : ∀ y, n < y → DifferentiableAt ℝ f y)
    (hcont : ContinuousAt f n)
    (hL : Tendsto (deriv f) (𝓝[<] n) (𝓝 L₁)) (hR : Tendsto (deriv f) (𝓝[>] n) (𝓝 L₂))
    (hne : L₁ ≠ L₂) : ¬ ∃ m, HasDerivAt f m n := by
  rw [exists_hasDerivAt_iff_tendsto_deriv_oneSided hdiffL hdiffR hcont hL hR]
  exact hne

/-- **Corner recovery stated for the flux.** Let `ψ` be a scale-dependent expectation whose
scale derivative is the flux `Φ` at every scale other than `n`, and let `Φ` have one-sided limits
`L₁` (from below) and `L₂` (from above) at `n`. Then a two-sided derivative of `ψ` at `n` exists if
and only if `L₁ = L₂`, and then it is their common value. This is the form in which the
corner-free interval theorems feed the corner: they supply `Φ` on each side of `n`. -/
theorem exists_hasDerivAt_iff_tendsto_flux_oneSided {ψ Φ : ℝ → ℝ} {n L₁ L₂ : ℝ}
    (hd : ∀ y, y ≠ n → HasDerivAt ψ (Φ y) y) (hψ : ContinuousAt ψ n)
    (hL : Tendsto Φ (𝓝[<] n) (𝓝 L₁)) (hR : Tendsto Φ (𝓝[>] n) (𝓝 L₂)) :
    (∃ m, HasDerivAt ψ m n) ↔ L₁ = L₂ := by
  have hEqL : Φ =ᶠ[𝓝[<] n] deriv ψ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hd y (ne_of_lt hy)).deriv).symm
  have hEqR : Φ =ᶠ[𝓝[>] n] deriv ψ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hd y (ne_of_gt hy)).deriv).symm
  exact exists_hasDerivAt_iff_tendsto_deriv_oneSided
    (fun y hy => (hd y (ne_of_lt hy)).differentiableAt)
    (fun y hy => (hd y (ne_of_gt hy)).differentiableAt)
    hψ (Filter.Tendsto.congr' hEqL hL) (Filter.Tendsto.congr' hEqR hR)

/-- **Concrete obstruction for the cut-off moment.** If the flux `Φ` has different one-sided
limits at the corner `n` and `ψ' = Φ` off `n`, then `ψ` has no two-sided derivative at `n`. -/
theorem not_exists_hasDerivAt_of_tendsto_flux_oneSided_ne {ψ Φ : ℝ → ℝ} {n L₁ L₂ : ℝ}
    (hd : ∀ y, y ≠ n → HasDerivAt ψ (Φ y) y) (hψ : ContinuousAt ψ n)
    (hL : Tendsto Φ (𝓝[<] n) (𝓝 L₁)) (hR : Tendsto Φ (𝓝[>] n) (𝓝 L₂))
    (hne : L₁ ≠ L₂) : ¬ ∃ m, HasDerivAt ψ m n := by
  rw [exists_hasDerivAt_iff_tendsto_flux_oneSided hd hψ hL hR]
  exact hne

/-! ## The corner of the cut-off edge probability in the scale

The cut-off edge probability of a non-diagonal pair at distance `s` is `0` on `(-∞, s]` and
`1 - exp (-(β (K s - K r)))` for `r > s`. Its derivative in the scale therefore has the
one-sided limits `0` (from below) and `β (-K'(s))` (from above) at `r = s`; this is the
sharpest instance of the corner of the cut-off family, and the criterion above turns the
mismatch into the absence of a two-sided derivative. -/

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K₂ : ℝ → ℝ} {β : ℝ≥0}

/-- The cut-off edge probability of a non-diagonal pair vanishes below its length. -/
theorem coe_cutoffEdgeProbability_eq_zero_of_lt {x y : Fin d → ℤ} (hxy : x ≠ y) {r : ℝ}
    (hr : r < N (Int.cast ∘ (x - y))) :
    (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ) = 0 := by
  rw [coe_intensityProfile_eq]
  have hk : (cutoffKernel N K r s(x, y) : ℝ≥0) = 0 := by
    rw [cutoffKernel_def, radialKernel_of_ne hxy]
    have h : cutoffProfile K r (N.toSeminorm (Int.cast ∘ (x - y))) = 0 := cutoffProfile_of_lt hr
    rw [h, Real.toNNReal_zero]
  rw [hk, NNReal.coe_zero, mul_zero]
  simp

/-- **Left limit of the scale derivative at an edge length.** Below the length of the pair the
cut-off edge probability is identically zero, so its derivative tends to `0`. -/
theorem tendsto_deriv_cutoffEdgeProbability_nhdsLT {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Tendsto (deriv fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ))
      (𝓝[<] N (Int.cast ∘ (x - y))) (𝓝 0) := by
  have hEq : deriv (fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ))
      =ᶠ[𝓝[<] N (Int.cast ∘ (x - y))] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hev : (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ))
        =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hr] with r' hr'
      exact coe_cutoffEdgeProbability_eq_zero_of_lt hxy hr'
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds

/-- **Right limit of the scale derivative at an edge length.** Above the length of the pair the
derivative of the cut-off edge probability is `β (-K' r) exp (-(β (K s - K r)))`, which tends to
`β (-K' s)` at the corner. -/
theorem tendsto_deriv_cutoffEdgeProbability_nhdsGT (hKa : AntitoneOn K (Ioi 0))
    (hK₂ : ∀ t, 0 < t → HasDerivAt K (K₂ t) t) (hK₂c : ContinuousOn K₂ (Ioi 0))
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Tendsto (deriv fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ))
      (𝓝[>] N (Int.cast ∘ (x - y))) (𝓝 ((β : ℝ) * -K₂ (N (Int.cast ∘ (x - y))))) := by
  rw [cutoffEdgeProbability_eq_one_sub_exp (N := N) hKa hxy]
  simp only [neg_mul]
  set s₀ : ℝ := N (Int.cast ∘ (x - y)) with hs₀
  have hs : 0 < s₀ := N.intCast_comp_sub_pos hxy
  have hEq : deriv (fun r => 1 - Real.exp (-(β * cutoffProfile K r s₀)))
      =ᶠ[𝓝[>] s₀] fun r =>
        (β : ℝ) * -K₂ r * Real.exp (-(β * cutoffProfile K r s₀)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hd := hasDerivAt_cutoffEdgeProbability_if (K := K) (K' := -K₂ r) (r := r) (s := s₀)
      (ne_of_lt hr) (by simpa using hK₂ r (hs.trans hr)) (β : ℝ)
    rw [hd.deriv, ite_eq_left hr.le]
  rw [tendsto_congr' hEq]
  have hKcont : Tendsto K (𝓝[>] s₀) (𝓝 (K s₀)) :=
    (hK₂ s₀ hs).continuousAt.mono_left nhdsWithin_le_nhds
  have hK₂cont : Tendsto K₂ (𝓝[>] s₀) (𝓝 (K₂ s₀)) :=
    tendsto_nhdsWithin_mono_left (Ioi_subset_Ioi hs.le) (hK₂c s₀ hs)
  have hprof : Tendsto (fun r => cutoffProfile K r s₀) (𝓝[>] s₀) (𝓝 0) := by
    have hev : (fun r => cutoffProfile K r s₀) =ᶠ[𝓝[>] s₀] fun r => K s₀ - K r := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact cutoffProfile_of_le hr.le
    rw [tendsto_congr' hev]
    simpa using hKcont.const_sub (K s₀)
  have hexp : Tendsto (fun r => Real.exp (-(β * cutoffProfile K r s₀)))
      (𝓝[>] s₀) (𝓝 1) := by
    have h1 : Tendsto (fun r => -(β * cutoffProfile K r s₀)) (𝓝[>] s₀) (𝓝 0) := by
      simpa using (hprof.const_mul (β : ℝ)).neg
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp h1
  have := (hK₂cont.neg.const_mul (β : ℝ)).mul hexp
  simpa using this

/-- Off the corner the cut-off edge probability of a non-diagonal pair is differentiable in the
scale. -/
theorem differentiableAt_cutoffEdgeProbability_of_ne (hKa : AntitoneOn K (Ioi 0))
    (hK₂ : ∀ t, 0 < t → HasDerivAt K (K₂ t) t) {x y : Fin d → ℤ} (hxy : x ≠ y) {r : ℝ}
    (hr : r ≠ N (Int.cast ∘ (x - y))) :
    DifferentiableAt ℝ (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ)) r := by
  set s₀ : ℝ := N (Int.cast ∘ (x - y)) with hs₀
  have hs : 0 < s₀ := N.intCast_comp_sub_pos hxy
  rcases lt_or_gt_of_ne hr with h | h
  · refine ((hasDerivAt_const (x := r) (c := (0 : ℝ))).congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards [Iio_mem_nhds h] with r' hr'
    exact coe_cutoffEdgeProbability_eq_zero_of_lt hxy hr'
  · rw [cutoffEdgeProbability_eq_one_sub_exp (N := N) hKa hxy]
    simp only [neg_mul]
    exact (hasDerivAt_cutoffEdgeProbability_if (K := K) (K' := -K₂ r) (r := r) (s := s₀)
      (ne_of_lt h) (by simpa using hK₂ r (hs.trans h)) (β : ℝ)).differentiableAt

/-- The cut-off edge probability of a non-diagonal pair is continuous in the scale at the corner:
both one-sided branches meet at `0`. -/
theorem continuousAt_cutoffEdgeProbability (hKa : AntitoneOn K (Ioi 0))
    (hK₂ : ∀ t, 0 < t → HasDerivAt K (K₂ t) t) {x y : Fin d → ℤ} (hxy : x ≠ y) :
    ContinuousAt (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ))
      (N (Int.cast ∘ (x - y))) := by
  rw [cutoffEdgeProbability_eq_one_sub_exp (N := N) hKa hxy]
  simp only [neg_mul]
  set s₀ : ℝ := N (Int.cast ∘ (x - y)) with hs₀
  have hs : 0 < s₀ := N.intCast_comp_sub_pos hxy
  have hbound : ∀ r : ℝ, ‖cutoffProfile K r s₀‖ ≤ ‖K s₀ - K r‖ := by
    intro r
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_or_gt s₀ r with h | h
    · rw [cutoffProfile_of_le h]
    · rw [cutoffProfile_of_lt h, abs_zero]
      exact abs_nonneg _
  have hdiff : Tendsto (fun r => K s₀ - K r) (𝓝 s₀) (𝓝 0) := by
    simpa using (hK₂ s₀ hs).continuousAt.const_sub (K s₀)
  have hnorm : Tendsto (fun r => ‖K s₀ - K r‖) (𝓝 s₀) (𝓝 0) := by
    simpa using hdiff.norm
  have hprof : Tendsto (fun r => cutoffProfile K r s₀) (𝓝 s₀) (𝓝 0) :=
    squeeze_zero_norm hbound hnorm
  have hexp : Tendsto (fun r => Real.exp (-(β * cutoffProfile K r s₀)))
      (𝓝 s₀) (𝓝 1) := by
    have h1 : Tendsto (fun r => -(β * cutoffProfile K r s₀)) (𝓝 s₀) (𝓝 0) := by
      simpa using (hprof.const_mul (β : ℝ)).neg
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp h1
  have hmain : Tendsto (fun r => 1 - Real.exp (-(β * cutoffProfile K r s₀)))
      (𝓝 s₀) (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub hexp :
      Tendsto (fun r => 1 - Real.exp (-(β * cutoffProfile K r s₀))) (𝓝 s₀) (𝓝 (1 - 1)))
  have hval : (fun r => 1 - Real.exp (-(β * cutoffProfile K r s₀))) s₀ = 0 := by
    have h0 : cutoffProfile K s₀ s₀ = 0 := by
      rw [cutoffProfile_of_le (le_refl s₀), sub_self]
    simp only [h0, mul_zero, neg_zero, Real.exp_zero, sub_self]
  change Tendsto (fun r => 1 - Real.exp (-(β * cutoffProfile K r s₀))) (𝓝 s₀)
    (𝓝 ((fun r => 1 - Real.exp (-(β * cutoffProfile K r s₀))) s₀))
  rw [hval]
  exact hmain

/-- **The corner of the cut-off edge probability, seen through the criterion.** At the length of
a non-diagonal pair the one-sided limits of the scale derivative are `0` and `β (-K' s)`; when
the latter is nonzero no two-sided derivative exists. This is the model-level instance of
`not_exists_hasDerivAt_of_tendsto_deriv_oneSided_ne`, with both one-sided values explicit. -/
theorem not_exists_hasDerivAt_cutoffEdgeProbability_oneSided (hKa : AntitoneOn K (Ioi 0))
    (hK₂ : ∀ t, 0 < t → HasDerivAt K (K₂ t) t) (hK₂c : ContinuousOn K₂ (Ioi 0))
    {x y : Fin d → ℤ} (hxy : x ≠ y)
    (hβK : (β : ℝ) * -K₂ (N (Int.cast ∘ (x - y))) ≠ 0) :
    ¬ ∃ m, HasDerivAt (fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ)) m
      (N (Int.cast ∘ (x - y))) := by
  refine not_exists_hasDerivAt_of_tendsto_deriv_oneSided_ne
    (fun r hr => differentiableAt_cutoffEdgeProbability_of_ne hKa hK₂ hxy (ne_of_lt hr))
    (fun r hr => differentiableAt_cutoffEdgeProbability_of_ne hKa hK₂ hxy (ne_of_gt hr))
    (continuousAt_cutoffEdgeProbability hKa hK₂ hxy)
    (tendsto_deriv_cutoffEdgeProbability_nhdsLT (K := K) (β := β) hxy)
    (tendsto_deriv_cutoffEdgeProbability_nhdsGT hKa hK₂ hK₂c hxy) ?_
  intro h0
  exact hβK h0.symm

/-- **Corner recovery at an edge length, sharp form.** The cut-off edge probability of a
non-diagonal pair has a two-sided derivative in the scale at its own length if and only if the
cut-off rate `β (-K')` vanishes there. So the corner restriction of
`hasDerivAt_integral_cutoff_pow_binomial_of_root_moment_of_diagram` cannot be dropped at a scale
carrying a nonvanishing rate: the one-sided values really differ. -/
theorem exists_hasDerivAt_cutoffEdgeProbability_iff (hKa : AntitoneOn K (Ioi 0))
    (hK₂ : ∀ t, 0 < t → HasDerivAt K (K₂ t) t) (hK₂c : ContinuousOn K₂ (Ioi 0))
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    (∃ m, HasDerivAt (fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ)) m
      (N (Int.cast ∘ (x - y)))) ↔ (β : ℝ) * -K₂ (N (Int.cast ∘ (x - y))) = 0 := by
  have hcrit := exists_hasDerivAt_iff_tendsto_deriv_oneSided
    (f := fun r => (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ))
    (n := N (Int.cast ∘ (x - y))) (L₁ := 0) (L₂ := (β : ℝ) * -K₂ (N (Int.cast ∘ (x - y))))
    (fun r hr => differentiableAt_cutoffEdgeProbability_of_ne hKa hK₂ hxy (ne_of_lt hr))
    (fun r hr => differentiableAt_cutoffEdgeProbability_of_ne hKa hK₂ hxy (ne_of_gt hr))
    (continuousAt_cutoffEdgeProbability hKa hK₂ hxy)
    (tendsto_deriv_cutoffEdgeProbability_nhdsLT (K := K) (β := β) hxy)
    (tendsto_deriv_cutoffEdgeProbability_nhdsGT hKa hK₂ hK₂c hxy)
  refine hcrit.trans (eq_comm (a := (0 : ℝ)) (b := (β : ℝ) * -K₂ (N (Int.cast ∘ (x - y)))))

/-- **The linear model has a genuine corner with the maximal rate.** For the profile
`K s = -s` and `β = 1` the cut-off rate at every positive scale is `β (-K') = 1`, so the cut-off
edge probability of any non-diagonal pair has no two-sided derivative in the scale at its own
length. -/
theorem not_exists_hasDerivAt_cutoffEdgeProbability_linear {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    ¬ ∃ m, HasDerivAt (fun r => (intensityProfile
        (cutoffKernel N (fun s => -s) r) 1 s(x, y) : ℝ)) m (N (Int.cast ∘ (x - y))) := by
  refine not_exists_hasDerivAt_cutoffEdgeProbability_oneSided
    (K := fun s => -s) (K₂ := fun _ => -1) (β := 1)
    (fun a ha b hb hab => neg_le_neg hab)
    (fun t ht => by simpa using (hasDerivAt_id t).const_mul (-1))
    (continuousOn_const) hxy ?_
  norm_num

/-- **The rate factor of the derivative coefficient does not change inside a corner-free
interval.** For `r, r'` in an interval containing no lattice norm, the paper's ball indicator is
the same, so the only scale dependence of the right-hand side inside the interval comes from the
law and the rate. -/
theorem ball_indicator_eq_of_corner_free {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) {u v r r' : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v) (hr : r ∈ Ioo u v)
    (hr' : r' ∈ Ioo u v) (z : Fin d → ℤ) :
    (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0) =
      if N (Int.cast ∘ z) ≤ r' then 1 else 0 := by
  have hz : N (Int.cast ∘ z) ∉ Ioo u v := hcorner z
  rcases le_or_gt (N (Int.cast ∘ z)) u with h | h
  · have h1 : N (Int.cast ∘ z) ≤ r := h.trans hr.1.le
    have h2 : N (Int.cast ∘ z) ≤ r' := h.trans hr'.1.le
    rw [ite_eq_left h1, ite_eq_left h2]
  · have hlt : v ≤ N (Int.cast ∘ z) := by
      by_contra hlt
      exact hz ⟨h, not_le.1 hlt⟩
    have h1 : ¬ N (Int.cast ∘ z) ≤ r := not_le.2 (hr.2.trans_le hlt)
    have h2 : ¬ N (Int.cast ∘ z) ≤ r' := not_le.2 (hr'.2.trans_le hlt)
    rw [ite_eq_right h1, ite_eq_right h2]

/-- **The rate factor of the derivative coefficient jumps at an exact-edge scale.** For a
non-diagonal pair the strict radial factor `1 (N(x − y) < r)` of the cut-off derivative
coefficient tends to `0` from below the pair's length and to `1` from above it. -/
theorem tendsto_radialKernel_indicator_nhdsLT {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Tendsto (fun r => (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ))
      (𝓝[<] N (Int.cast ∘ (x - y))) (𝓝 0) := by
  have hfun : ∀ r : ℝ, (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) =
      if N (Int.cast ∘ (x - y)) < r then 1 else 0 := by
    intro r
    rw [coe_radialKernel_of_ne hxy (by positivity)]
  simp only [hfun]
  have hEq : (fun r => (if N (Int.cast ∘ (x - y)) < r then (1 : ℝ) else 0))
      =ᶠ[𝓝[<] N (Int.cast ∘ (x - y))] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ite_eq_right (not_lt.2 hr.le)]
  exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds

/-- The same rate factor tends to `1` from above the pair's length. -/
theorem tendsto_radialKernel_indicator_nhdsGT {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Tendsto (fun r => (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ))
      (𝓝[>] N (Int.cast ∘ (x - y))) (𝓝 1) := by
  have hfun : ∀ r : ℝ, (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) =
      if N (Int.cast ∘ (x - y)) < r then 1 else 0 := by
    intro r
    rw [coe_radialKernel_of_ne hxy (by positivity)]
  simp only [hfun]
  have hEq : (fun r => (if N (Int.cast ∘ (x - y)) < r then (1 : ℝ) else 0))
      =ᶠ[𝓝[>] N (Int.cast ∘ (x - y))] fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ite_eq_left (show N (Int.cast ∘ (x - y)) < r from hr)]
  exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds

/-! ## The strict radial indicator and the closed ball at a corner

The derivative coefficient of the cut-off family carries the *strict* radial indicator
`1 (N (y - x) < r)` (the edge of length exactly `r` is closed at scale `r`, so its contribution
to the derivative vanishes), while the Russo formula of the paper carries the closed ball
`1 (‖y - x‖ ≤ r)`. Off the corners the two agree (`indicator_lt_eq_le`); at a corner they differ
by exactly the displacements of norm exactly `n`. -/

/-- At a corner `n` the closed-ball weight is the strict weight plus the exact-length weight. -/
theorem tsum_ball_indicator_eq_strict_add_corner {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ))
    (f : (Fin d → ℤ) → ℝ≥0∞) (n : ℝ) :
    (∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) ≤ n then (1 : ℝ≥0∞) else 0) * f z) =
      (∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) < n then (1 : ℝ≥0∞) else 0) * f z) +
        ∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) = n then (1 : ℝ≥0∞) else 0) * f z := by
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun z => ?_
  rcases lt_trichotomy (N (Int.cast ∘ z)) n with h | h | h
  · simp [h, h.le, ne_of_lt h]
  · simp [h]
  · have hle : ¬ N (Int.cast ∘ z) ≤ n := not_le.2 h
    have hlt : ¬ N (Int.cast ∘ z) < n := not_lt.2 h.le
    have hne : N (Int.cast ∘ z) ≠ n := ne_of_gt h
    simp [hle, hlt, hne]

/-- Consequently, at a corner `n` the closed-ball weight is *strictly* larger than the strict
weight whenever the exact-length term does not vanish and the strict sum is finite. So the two
conventions of the derivative formula differ exactly by the flux through the displacements of
norm exactly `n`. -/
theorem tsum_strict_indicator_lt_ball {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ))
    (f : (Fin d → ℤ) → ℝ≥0∞) (n : ℝ)
    (hC : (∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) = n then (1 : ℝ≥0∞) else 0) * f z) ≠ 0)
    (hS : (∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) < n then (1 : ℝ≥0∞) else 0) * f z) ≠ ⊤) :
    (∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) < n then (1 : ℝ≥0∞) else 0) * f z) <
      ∑' (z : Fin d → ℤ), (if N (Int.cast ∘ z) ≤ n then (1 : ℝ≥0∞) else 0) * f z := by
  rw [tsum_ball_indicator_eq_strict_add_corner N f n]
  exact ENNReal.lt_add_right hS hC

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- If a scale derivative is known at every point to the right and its value has a right limit,
then that limit is the right derivative. No assertion is made about the left derivative. -/
theorem hasDerivWithinAt_Ici_of_tendsto_flux {ψ Φ : ℝ → ℝ} {n L : ℝ}
    (hd : ∀ y, n < y → HasDerivAt ψ (Φ y) y)
    (hψ : ContinuousWithinAt ψ (Ici n) n)
    (hΦ : Tendsto Φ (𝓝[>] n) (𝓝 L)) :
    HasDerivWithinAt ψ L (Ici n) n := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioi n)
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (hψ.mono Ioi_subset_Ici_self) self_mem_nhdsWithin
  have hEq : Φ =ᶠ[𝓝[>] n] deriv ψ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hd y hy).deriv).symm
  exact Tendsto.congr' hEq hΦ

open Classical in
/-- The stronger higher-moment binomial cutoff derivative at every non-corner scale in
`(0,R)`, without presenting an interval of profile regularity as a literal all-radius claim. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_noncorner {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r₀)
    (hroot : ∀ r ∈ (Ioo 0 R ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo 0 R)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  obtain ⟨δ, hδ, hu, hvR, hI⟩ := exists_corner_free hr₀ hr₀R hcorner
  have hsub : Ioo (r₀ - δ) (r₀ + δ) ⊆ Ioo 0 R :=
    fun r hr => ⟨hu.trans hr.1, hr.2.trans_le hvR⟩
  exact hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment
    (K := K) (K' := K') (R := R) (u := r₀ - δ) (v := r₀ + δ) (r₀ := r₀)
    hKa hK' hK'c β p hp M hM cw hcw hu (by linarith) (by linarith) hvR hI
    (fun r hr => by
      rcases hr with hr | hr
      · exact hroot r (Or.inl (hsub hr))
      · exact hroot r (Or.inr hr))
    (hcont.mono hsub)

end PercLib.Models.LongRange

namespace PercLib.Analysis

open MeasureTheory
open scoped ENNReal

/-- Real integrals of finite extended-nonnegative functions subtract through truncated
extended-nonnegative subtraction. -/
theorem integral_toReal_sub_eq_toReal_lintegral_sub {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ≥0∞}
    (hfm : AEMeasurable f μ) (hgm : Measurable g)
    (hfin : ∀ᵐ x ∂μ, f x < ⊤) (hgf : ∀ᵐ x ∂μ, g x ≤ f x)
    (hIfin : (∫⁻ x, f x ∂μ) ≠ ⊤) :
    (∫ x, (f x).toReal ∂μ) - (∫ x, (g x).toReal ∂μ) =
      (∫⁻ x, f x - g x ∂μ).toReal := by
  have hgfin : ∀ᵐ x ∂μ, g x < ⊤ := by
    filter_upwards [hfin, hgf] with x hfx hgx
    exact hgx.trans_lt hfx
  have hle : (∫⁻ x, g x ∂μ) ≤ ∫⁻ x, f x ∂μ := lintegral_mono_ae hgf
  have hIgm : (∫⁻ x, g x ∂μ) ≠ ⊤ := ne_top_of_le_ne_top hIfin hle
  rw [MeasureTheory.integral_toReal hfm hfin,
    MeasureTheory.integral_toReal hgm.aemeasurable hgfin,
    ← ENNReal.toReal_sub_of_le hle hIfin,
    MeasureTheory.lintegral_sub hgm hIgm hgf]

end PercLib.Analysis

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability MeasureTheory
open scoped ENNReal NNReal

/-! ### Real cap error -/

theorem sub_min_eq_max (x M : ℝ) : x - min M x = max 0 (x - M) := by
  rcases le_total x M with h | h
  · rw [min_eq_right h, sub_self, max_eq_left (a := (0:ℝ)) (b := x - M) (by linarith)]
  · rw [min_eq_left h, max_eq_right (a := (0:ℝ)) (b := x - M) (by linarith)]

theorem sub_min_mono {x y M : ℝ} (hyx : y ≤ x) : y - min M y ≤ x - min M x := by
  rw [sub_min_eq_max, sub_min_eq_max]
  exact max_le_max le_rfl (by linarith)

/-- The excess of `a ^ p` over the cap `N ^ p` is at most `a ^ (p+1) / N`. -/
theorem pow_sub_min_pow_le_div {a N : ℝ} (ha : 0 ≤ a) (hN : 0 < N) (p : ℕ) :
    a ^ p - min (N ^ p) (a ^ p) ≤ a ^ (p + 1) / N := by
  rcases le_total a N with h | h
  · have h1 : a ^ p ≤ N ^ p := pow_le_pow_left₀ ha h p
    rw [min_eq_right h1, sub_self]
    positivity
  · have h1 : N ^ p ≤ a ^ p := pow_le_pow_left₀ hN.le h p
    rw [min_eq_left h1]
    have h2 : a ^ p - N ^ p ≤ a ^ p := by
      have hNp : (0 : ℝ) ≤ N ^ p := by positivity
      linarith
    have h3 : a ^ p ≤ a ^ (p + 1) / N := by
      rw [le_div_iff₀ hN, pow_succ]
      exact mul_le_mul_of_nonneg_left h (pow_nonneg ha p)
    linarith

/-! ### The pointwise cap error of a single pivotal increment -/

/-- **The capped pivotal increment is dominated by the uncapped one.** -/
theorem pivotal_capped_le_uncapped {V : Type*} (ω : Config V) (e : Sym2 V) (o : V) (p : ℕ)
    {N : ℝ} (hN : 0 ≤ N) (hfin : ((cluster (insert e ω) o).encard : ℝ≥0∞) < ⊤) :
    min (ENNReal.ofReal (N ^ p)) ((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)
        - min (ENNReal.ofReal (N ^ p)) ((↑(cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
      ≤ (↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        - (↑(cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p := by
  classical
  set A1 : ℝ≥0∞ := ↑(cluster (insert e ω) o).encard with hA1
  set A0 : ℝ≥0∞ := ↑(cluster (ω \ {e}) o).encard with hA0
  have hsub_self : ∀ (a b : ℝ≥0∞), a - b ≤ a := fun a b => tsub_le_self
  have hA0le : A0 ≤ A1 := encard_cluster_sdiff_le_insert_coe ω e o
  have hA1t : A1 < ⊤ := hfin
  have h1t : A1 ^ p < ⊤ := ENNReal.pow_lt_top (n := p) hA1t
  have h0t : A0 ^ p < ⊤ := ENNReal.pow_lt_top (n := p) (lt_of_le_of_lt hA0le hA1t)
  have hle : A0 ^ p ≤ A1 ^ p := ENNReal.pow_le_pow_left hA0le
  have hMt : min (ENNReal.ofReal (N ^ p)) (A1 ^ p) < ⊤ :=
    lt_of_le_of_lt (min_le_left _ _) ENNReal.ofReal_lt_top
  have hminle : min (ENNReal.ofReal (N ^ p)) (A0 ^ p)
      ≤ min (ENNReal.ofReal (N ^ p)) (A1 ^ p) := min_le_min_left _ hle
  have h1 : min (ENNReal.ofReal (N ^ p)) (A1 ^ p)
        - min (ENNReal.ofReal (N ^ p)) (A0 ^ p) ≠ ⊤ :=
    ne_top_of_le_ne_top hMt.ne (hsub_self _ _)
  have h2 : A1 ^ p - A0 ^ p ≠ ⊤ := ne_top_of_le_ne_top h1t.ne (hsub_self _ _)
  refine (ENNReal.toReal_le_toReal h1 h2).1 ?_
  rw [ENNReal.toReal_sub_of_le hminle hMt.ne, ENNReal.toReal_sub_of_le hle h1t.ne,
    ENNReal.toReal_min ENNReal.ofReal_ne_top h0t.ne,
    ENNReal.toReal_min ENNReal.ofReal_ne_top h1t.ne,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ N ^ p)]
  have hba : A0.toReal ^ p ≤ A1.toReal ^ p := by
    rw [← ENNReal.toReal_pow, ← ENNReal.toReal_pow]
    exact ENNReal.toReal_mono h1t.ne hle
  have hmono := sub_min_mono (M := N ^ p) hba
  have hb : (0:ℝ) ≤ A0.toReal ^ p - min (N ^ p) (A0.toReal ^ p) := by
    have hle' := min_le_right (N ^ p) (A0.toReal ^ p)
    linarith
  linarith


/-- **The signed cap error is at most the excess of the inserted moment over its cap.** -/
theorem pivotal_error_le_excess {V : Type*} (ω : Config V) (e : Sym2 V) (o : V) (p : ℕ)
    {N : ℝ} (hN : 0 ≤ N) (hfin : ((cluster (insert e ω) o).encard : ℝ≥0∞) < ⊤) :
    (((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        - (↑(cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
      - (min (ENNReal.ofReal (N ^ p)) ((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)
        - min (ENNReal.ofReal (N ^ p)) ((↑(cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)))
      ≤ (↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        - min (ENNReal.ofReal (N ^ p)) ((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) := by
  classical
  set A1 : ℝ≥0∞ := ↑(cluster (insert e ω) o).encard with hA1
  set A0 : ℝ≥0∞ := ↑(cluster (ω \ {e}) o).encard with hA0
  have hsub_self : ∀ (a b : ℝ≥0∞), a - b ≤ a := fun a b => tsub_le_self
  have hA1t : A1 < ⊤ := hfin
  have h1t : A1 ^ p < ⊤ := ENNReal.pow_lt_top (n := p) hA1t
  have h0t : A0 ^ p < ⊤ := ENNReal.pow_lt_top (n := p)
    (lt_of_le_of_lt (encard_cluster_sdiff_le_insert_coe ω e o) hA1t)
  have hle : A0 ^ p ≤ A1 ^ p := ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  have hMt : min (ENNReal.ofReal (N ^ p)) (A1 ^ p) < ⊤ :=
    lt_of_le_of_lt (min_le_left _ _) ENNReal.ofReal_lt_top
  have hminle : min (ENNReal.ofReal (N ^ p)) (A0 ^ p) ≤ min (ENNReal.ofReal (N ^ p)) (A1 ^ p) :=
    min_le_min_left _ hle
  have hcapped : min (ENNReal.ofReal (N ^ p)) (A1 ^ p) - min (ENNReal.ofReal (N ^ p)) (A0 ^ p)
      ≤ A1 ^ p - A0 ^ p := pivotal_capped_le_uncapped ω e o p hN hfin
  have h1 : (A1 ^ p - A0 ^ p) - (min (ENNReal.ofReal (N ^ p)) (A1 ^ p)
      - min (ENNReal.ofReal (N ^ p)) (A0 ^ p)) ≠ ⊤ :=
    ne_top_of_le_ne_top h1t.ne (le_trans (hsub_self _ _) (hsub_self _ _))
  have h2 : A1 ^ p - min (ENNReal.ofReal (N ^ p)) (A1 ^ p) ≠ ⊤ :=
    ne_top_of_le_ne_top h1t.ne (hsub_self _ _)
  refine (ENNReal.toReal_le_toReal h1 h2).1 ?_
  rw [ENNReal.toReal_sub_of_le hcapped (ne_top_of_le_ne_top h1t.ne (hsub_self _ _)),
    ENNReal.toReal_sub_of_le hle h1t.ne,
    ENNReal.toReal_sub_of_le (min_le_right _ _) h1t.ne,
    ENNReal.toReal_sub_of_le hminle hMt.ne,
    ENNReal.toReal_min ENNReal.ofReal_ne_top h1t.ne,
    ENNReal.toReal_min ENNReal.ofReal_ne_top h0t.ne,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ N ^ p)]
  have hba : A0.toReal ^ p ≤ A1.toReal ^ p := by
    rw [← ENNReal.toReal_pow, ← ENNReal.toReal_pow]
    exact ENNReal.toReal_mono h1t.ne hle
  have hmono := sub_min_mono (M := N ^ p) hba
  have hb : (0:ℝ) ≤ A0.toReal ^ p - min (N ^ p) (A0.toReal ^ p) := by
    have hle' := min_le_right (N ^ p) (A0.toReal ^ p)
    linarith
  linarith

/-- **The excess of the inserted `p`-th moment over its cap.** -/
theorem pivotal_excess_le {V : Type*} (ω : Config V) (e : Sym2 V) (o : V) (p : ℕ)
    {N : ℝ} (hN : 1 ≤ N) (hfin : ((cluster (insert e ω) o).encard : ℝ≥0∞) < ⊤) :
    (↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        - min (ENNReal.ofReal (N ^ p)) ((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)
      ≤ ENNReal.ofReal (1 / N) * (↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) := by
  classical
  set A1 : ℝ≥0∞ := ↑(cluster (insert e ω) o).encard with hA1
  have hsub_self : ∀ (a b : ℝ≥0∞), a - b ≤ a := fun a b => tsub_le_self
  have hA1t : A1 < ⊤ := hfin
  have h1t : A1 ^ p < ⊤ := ENNReal.pow_lt_top (n := p) hA1t
  have h1p : A1 ^ (p + 1) < ⊤ := ENNReal.pow_lt_top (n := p + 1) hA1t
  have hRt : ENNReal.ofReal (1 / N) * A1 ^ (p + 1) < ⊤ := by
    have hc : ENNReal.ofReal (1 / N) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_one (by linarith : (0:ℝ) < N)]
      exact hN
    calc ENNReal.ofReal (1 / N) * A1 ^ (p + 1) ≤ 1 * A1 ^ (p + 1) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = A1 ^ (p + 1) := one_mul _
      _ < ⊤ := h1p
  have h1 : A1 ^ p - min (ENNReal.ofReal (N ^ p)) (A1 ^ p) ≠ ⊤ :=
    ne_top_of_le_ne_top h1t.ne (hsub_self _ _)
  refine (ENNReal.toReal_le_toReal h1 hRt.ne).1 ?_
  rw [ENNReal.toReal_sub_of_le (min_le_right _ _) h1t.ne,
    ENNReal.toReal_min ENNReal.ofReal_ne_top h1t.ne,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow]
  have hmain := pow_sub_min_pow_le_div (a := A1.toReal) ENNReal.toReal_nonneg
    (by linarith : (0:ℝ) < N) p
  have hrw : A1.toReal ^ (p + 1) / N = 1 / N * A1.toReal ^ (p + 1) := by ring
  rw [hrw] at hmain
  exact hmain


/-- **The cap error of a single pivotal increment.** -/
theorem pivotal_cap_error_le {V : Type*} (ω : Config V) (e : Sym2 V) (o : V) (p : ℕ)
    {N : ℝ} (hN : 1 ≤ N) (hfin : ((cluster (insert e ω) o).encard : ℝ≥0∞) < ⊤) :
    (((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        - (↑(cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
      - (min (ENNReal.ofReal (N ^ p)) ((↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)
        - min (ENNReal.ofReal (N ^ p)) ((↑(cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)))
      ≤ ENNReal.ofReal (1 / N) * (↑(cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) :=
  (pivotal_error_le_excess ω e o p (by linarith) hfin).trans
    (pivotal_excess_le ω e o p hN hfin)

/-! ### The cap error of a single pair, at the level of the integral -/

/-- **The signed cap error of a single pivotal increment.** For a finite measure and a pair `e`
whose inserted cluster has finite `(p+1)`-moment at most `C`, the difference between the pivotal
`p`-th moment and its cap at `N ^ p` is at most `C / N`. -/
theorem integral_pivotal_cap_error_le {V : Type*} [Countable V] (μ : Measure (Config V))
    (e : Sym2 V) (o : V) (p : ℕ) {N C : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) < ⊤)
    (hmom : ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≤ ENNReal.ofReal C) :
    |(∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ) -
        (∫ ω, ((min (ENNReal.ofReal (N ^ p))
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
            (min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ)|
      ≤ C * (1 / N) := by
  classical
  have hsub_self : ∀ (a b : ℝ≥0∞), a - b ≤ a := fun a b => tsub_le_self
  have hm1 : Measurable fun ω : Config V => ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
    measurable_encard_cluster_insert_coe e o
  have hm0 : Measurable fun ω : Config V => ((cluster (ω \ {e}) o).encard : ℝ≥0∞) :=
    measurable_encard_cluster_sdiff_coe e o
  have hincr : Measurable fun ω : Config V =>
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) :=
    (hm1.pow_const p).sub (hm0.pow_const p)
  have hincrM : Measurable fun ω : Config V =>
      (min (ENNReal.ofReal (N ^ p)) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) :=
    (measurable_const.min (hm1.pow_const p)).sub (measurable_const.min (hm0.pow_const p))
  have hone : ∀ ω : Config V, (1 : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) := by
    intro ω
    exact_mod_cast one_le_encard_cluster (insert e ω) o
  have hincrle : ∀ ω : Config V,
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) := by
    intro ω
    refine (hsub_self _ _).trans ?_
    exact pow_le_pow_right₀ (hone ω) (Nat.le_succ p)
  have hIntIncr_le : ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ ≤ ENNReal.ofReal C :=
    (lintegral_mono hincrle).trans hmom
  have hIntIncr_ne : ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIntIncr_le
  have hcaple : ∀ᵐ ω ∂μ,
      (min (ENNReal.ofReal (N ^ p)) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ≤
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) := by
    filter_upwards [hfin] with ω hω
    exact pivotal_capped_le_uncapped ω e o p (by linarith) hω
  have herr : ∀ᵐ ω ∂μ,
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) -
      (min (ENNReal.ofReal (N ^ p)) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ≤
      ENNReal.ofReal (1 / N) * ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) := by
    filter_upwards [hfin] with ω hω
    exact pivotal_cap_error_le ω e o p hN hω
  have hIntIncrM_le : ∫⁻ ω, (min (ENNReal.ofReal (N ^ p))
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
      min (ENNReal.ofReal (N ^ p))
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ ≤
      ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := lintegral_mono_ae hcaple
  have hIntIncrM_ne : ∫⁻ ω, (min (ENNReal.ofReal (N ^ p))
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
      min (ENNReal.ofReal (N ^ p))
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hIntIncr_ne hIntIncrM_le
  have hQM : ∫ ω, ((min (ENNReal.ofReal (N ^ p))
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (ENNReal.ofReal (N ^ p))
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ =
      (∫⁻ ω, (min (ENNReal.ofReal (N ^ p))
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (ENNReal.ofReal (N ^ p))
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal := by
    rw [← integral_toReal hincrM.aemeasurable (by
      filter_upwards with ω
      exact lt_of_le_of_lt (hsub_self _ _)
        (lt_of_le_of_lt (min_le_left _ _) ENNReal.ofReal_lt_top))]
    refine integral_congr_ae ?_
    filter_upwards [hfin] with ω hω
    have h0t : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p < ⊤ :=
      ENNReal.pow_lt_top (n := p)
        (lt_of_le_of_lt (encard_cluster_sdiff_le_insert_coe ω e o) hω)
    have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p
        ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
      ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
    have hminle : min (ENNReal.ofReal (N ^ p))
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
        ≤ min (ENNReal.ofReal (N ^ p))
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) :=
      min_le_min_left _ hle
    exact (ENNReal.toReal_sub_of_le hminle
      (lt_of_le_of_lt (min_le_left _ _) ENNReal.ofReal_lt_top).ne).symm
  have hdiff : (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ) -
        (∫ ω, ((min (ENNReal.ofReal (N ^ p))
              (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
            (min (ENNReal.ofReal (N ^ p))
              (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ) =
      (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) -
        (min (ENNReal.ofReal (N ^ p))
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (ENNReal.ofReal (N ^ p))
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal := by
    have hcapt : ∀ᵐ ω ∂μ, (min (ENNReal.ofReal (N ^ p))
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (ENNReal.ofReal (N ^ p))
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) < ⊤ := by
      filter_upwards with ω
      exact lt_of_le_of_lt (hsub_self _ _)
        (lt_of_le_of_lt (min_le_left _ _) ENNReal.ofReal_lt_top)
    have hdiff' := PercLib.Analysis.integral_toReal_sub_eq_toReal_lintegral_sub
      hincr.aemeasurable hincrM ?_ hcaple hIntIncr_ne
    · rw [MeasureTheory.integral_toReal hincrM.aemeasurable hcapt] at hdiff'
      rw [hQM]
      exact hdiff'
    · filter_upwards [hfin] with ω hω
      exact lt_of_le_of_lt (hsub_self _ _) (ENNReal.pow_lt_top (n := p) hω)
  have hb1 : ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) -
        (min (ENNReal.ofReal (N ^ p)) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (1 / N) * ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ :=
    lintegral_mono_ae herr
  have hb2 : ∫⁻ ω, ENNReal.ofReal (1 / N) * ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ
      = ENNReal.ofReal (1 / N) * ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ :=
    lintegral_const_mul _ (hm1.pow_const (p + 1))
  have hb3 : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) -
        (min (ENNReal.ofReal (N ^ p)) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal
      ≤ (ENNReal.ofReal (1 / N) * ENNReal.ofReal C).toReal := by
    refine ENNReal.toReal_mono ?_ (hb1.trans (le_of_eq hb2) |>.trans ?_)
    · rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith : (0:ℝ) ≤ N))]
      exact ENNReal.ofReal_ne_top
    · exact mul_le_mul_of_nonneg_left hmom zero_le
  have hfin4 : (ENNReal.ofReal (1 / N) * ENNReal.ofReal C).toReal = C * (1 / N) := by
    rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith : (0:ℝ) ≤ N)),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hnn : 0 ≤ (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ) -
        (∫ ω, ((min (ENNReal.ofReal (N ^ p))
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
            (min (ENNReal.ofReal (N ^ p))
              (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ) := by
    rw [hdiff]
    exact ENNReal.toReal_nonneg
  rw [abs_of_nonneg hnn]
  exact (le_of_eq hdiff).trans (hb3.trans_eq hfin4)

/-! ### The cap approximation in the form needed by the cap passage -/

/-- **A root-cap choice.** For a moment bound `C` and `ε > 0` there is a root cap `N ≥ 1` whose
reciprocal times `C` is at most `ε`. -/
theorem exists_cap_root {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N : ℝ, 1 ≤ N ∧ C * (1 / N) ≤ ε := by
  refine ⟨(C + 1) / ε + 1, ?_, ?_⟩
  · have h0 : (0:ℝ) ≤ (C + 1) / ε := div_nonneg (by linarith) hε.le
    linarith
  · have hNpos : (0:ℝ) < (C + 1) / ε + 1 := by
      have h0 : (0:ℝ) ≤ (C + 1) / ε := div_nonneg (by linarith) hε.le
      linarith
    have h1 : 1 / ((C + 1) / ε + 1) ≤ ε / (C + 1) := by
      rw [div_le_iff₀ hNpos]
      have hNexp : ε / (C + 1) * ((C + 1) / ε + 1) = 1 + ε / (C + 1) := by
        field_simp
      rw [hNexp]
      have h0 : (0:ℝ) ≤ ε / (C + 1) := by positivity
      linarith
    refine (mul_le_mul_of_nonneg_left h1 hC).trans ?_
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0:ℝ) < C + 1)]
    nlinarith

/-- **The cap error of a single pair from a uniform finite `(p+1)`-moment.** -/
theorem integral_pivotal_cap_error_le_of_lintegral_le {V : Type*} [Countable V]
    (μ : Measure (Config V)) (e : Sym2 V) (o : V) (p : ℕ) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hmom : ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≤ M) {N : ℝ}
    (hN : 1 ≤ N) :
    |(∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ) -
        (∫ ω, ((min (ENNReal.ofReal (N ^ p))
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
            (min (ENNReal.ofReal (N ^ p)) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ)|
      ≤ M.toReal * (1 / N) := by
  have hmom' : ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ
      ≤ ENNReal.ofReal M.toReal := by
    rw [ENNReal.ofReal_toReal hM]
    exact hmom
  have hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) < ⊤ := by
    have hne : ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hM hmom
    have hlt := MeasureTheory.ae_lt_top
      ((measurable_encard_cluster_insert_coe e o).pow_const (p + 1)) hne
    filter_upwards [hlt] with ω hω
    rcases lt_or_eq_of_le (le_top : ((cluster (insert e ω) o).encard : ℝ≥0∞) ≤ ⊤) with h | h
    · exact h
    · rw [h, ENNReal.top_pow (by omega : p + 1 ≠ 0)] at hω
      exact absurd hω (lt_irrefl ⊤)
  exact integral_pivotal_cap_error_le μ e o p hN ENNReal.toReal_nonneg hfin hmom'

/-- **A cap approximation of a single pivotal moment uniform in nothing but the pair.** For a
measure on configurations, a pair and a finite `(p+1)`-moment bound `M`, every `ε > 0` admits a
real cap `M' ≥ 0` with the capped pivotal moment within `ε` of the uncapped one. -/
theorem exists_pivotal_cap_approx {V : Type*} [Countable V] (μ : Measure (Config V))
    (e : Sym2 V) (o : V) (p : ℕ) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hmom : ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M' : ℝ, 0 ≤ M' ∧
      |(∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ) -
        (∫ ω, ((min (ENNReal.ofReal M') (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
            (min (ENNReal.ofReal M') (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ)|
        ≤ ε := by
  obtain ⟨N, hN1, hNb⟩ := exists_cap_root ENNReal.toReal_nonneg hε
  exact ⟨N ^ p, by positivity,
    (integral_pivotal_cap_error_le_of_lintegral_le μ e o p M hM hmom hN1).trans hNb⟩

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability MeasureTheory
open scoped ENNReal NNReal

/-- Uncapped single-pair continuity from a uniform finite higher inserted moment. -/
theorem continuousOn_pivotal_cutoff_uncapped_of_uniform_root_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Set.Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Set.Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u : ℝ} (hu : 0 < u)
    (e : Sym2 (Fin d → ℤ)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hmom : ∀ r ∈ Set.Ioo u R, ∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel N K r) β)) ≤ M) :
    ContinuousOn (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Set.Ioo u R) := by
  have hrem : ∀ ε > 0, ∃ Mcap : ℝ, 0 ≤ Mcap ∧ ∀ r ∈ Set.Ioo u R,
      |(∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))) -
        (∫ ω, ((min (ENNReal.ofReal Mcap)
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
          (min (ENNReal.ofReal Mcap)
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
          ∂(law (intensityProfile (cutoffKernel N K r) β)))| ≤ ε := by
    intro ε hε
    obtain ⟨N', hN'1, hN'b⟩ := exists_cap_root ENNReal.toReal_nonneg hε
    refine ⟨N' ^ p, by positivity, ?_⟩
    intro r hr
    have hbound := integral_pivotal_cap_error_le_of_lintegral_le
      (V := Fin d → ℤ) (μ := law (intensityProfile (cutoffKernel N K r) β))
      (e := e) (o := o) (p := p) (M := M) (N := N') hM (hmom r hr) hN'1
    exact hbound.trans hN'b
  exact continuousOn_pivotal_cutoff_uncapped_of_uniform_cap (K := K) (K' := K')
    hKa hK' hK'c β p hp o hχ hu e hrem

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

open Classical in
/-- Per-vertex `p`-moments bounded by `M` give the displayed bound on an inserted-cluster
`p`-moment. -/
theorem lintegral_pow_encard_cluster_insert_le {V : Type*} [Countable V]
    (μ : Measure (Config V)) (o a b : V) (p : ℕ) (M : ℝ≥0∞)
    (ho : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) ≤ M)
    (ha : (∫⁻ ω, ((cluster ω a).encard : ℝ≥0∞) ^ p ∂μ) ≤ M)
    (hb : (∫⁻ ω, ((cluster ω b).encard : ℝ≥0∞) ^ p ∂μ) ≤ M) :
    (∫⁻ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≤
      M + 2 ^ (p - 1) * (M + M) := by
  have hmo : AEMeasurable (fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal o).pow_const p).aemeasurable
  have hma : AEMeasurable (fun ω : Config V => ((cluster ω a).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal a).pow_const p).aemeasurable
  have hmb : AEMeasurable (fun ω : Config V => ((cluster ω b).encard : ℝ≥0∞) ^ p) μ :=
    ((measurable_encard_cluster_toENNReal b).pow_const p).aemeasurable
  have hrhs : (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p +
        2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p)) ∂μ) =
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) +
        2 ^ (p - 1) * ((∫⁻ ω, ((cluster ω a).encard : ℝ≥0∞) ^ p ∂μ) +
          ∫⁻ ω, ((cluster ω b).encard : ℝ≥0∞) ^ p ∂μ) := by
    rw [lintegral_add_left' hmo,
      lintegral_const_mul'' ((2 : ℝ≥0∞) ^ (p - 1))
        (f := fun ω => ((cluster ω a).encard : ℝ≥0∞) ^ p +
          ((cluster ω b).encard : ℝ≥0∞) ^ p) (hma.add hmb),
      lintegral_add_left' hma]
  calc
    (∫⁻ ω, ((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≤
        ∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p +
          2 ^ (p - 1) * (((cluster ω a).encard : ℝ≥0∞) ^ p +
            ((cluster ω b).encard : ℝ≥0∞) ^ p)) ∂μ :=
      lintegral_mono fun ω => encard_cluster_insert_pow_le ω a b o p
    _ = (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) +
        2 ^ (p - 1) * ((∫⁻ ω, ((cluster ω a).encard : ℝ≥0∞) ^ p ∂μ) +
          ∫⁻ ω, ((cluster ω b).encard : ℝ≥0∞) ^ p ∂μ) := hrhs
    _ ≤ M + 2 ^ (p - 1) * (M + M) := by gcongr

/-- The bound holds for every unordered pair. -/
theorem lintegral_pow_encard_cluster_insert_le_forall {V : Type*} [Countable V]
    (μ : Measure (Config V)) (o : V) (p : ℕ) (M : ℝ≥0∞)
    (hmom : ∀ y : V, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≤ M)
    (e : Sym2 V) :
    (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p ∂μ) ≤
      M + 2 ^ (p - 1) * (M + M) := by
  induction e using Sym2.ind with
  | _ a b =>
    exact lintegral_pow_encard_cluster_insert_le μ o a b p M
      (hmom o) (hmom a) (hmom b)

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- Uncapped single-pair continuity from a uniform finite per-vertex cluster moment,
without a separate inserted-moment hypothesis. -/
theorem continuousOn_pivotal_cutoff_uncapped_of_uniform_vertex_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {u : ℝ} (hu : 0 < u)
    (e : Sym2 (Fin d → ℤ)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hmom : ∀ r ∈ Ioo u R, ∀ y : Fin d → ℤ,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel N K r) β))) ≤ M) :
    ContinuousOn (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u R) := by
  have hMins : M + 2 ^ ((p + 1) - 1) * (M + M) ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨hM, ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
      (ENNReal.add_ne_top.2 ⟨hM, hM⟩)⟩
  refine continuousOn_pivotal_cutoff_uncapped_of_uniform_root_moment
    hKa hK' hK'c β p hp o hχ hu e (M + 2 ^ ((p + 1) - 1) * (M + M)) hMins ?_
  intro r hr
  exact lintegral_pow_encard_cluster_insert_le_forall
    (law (intensityProfile (cutoffKernel N K r) β)) o (p + 1) M (hmom r hr) e


/-- Single-pair uncapped cutoff continuity from a uniform finite root `(p+1)`-moment.
This also supplies the outer-scale susceptibility bound. -/
theorem continuousOn_pivotal_cutoff_uncapped_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    {u : ℝ} (hu : 0 < u) (e : Sym2 (Fin d → ℤ)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Ioo u R ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M) :
    ContinuousOn (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u R) := by
  have hχ : chi (intensityProfile (cutoffKernel (d := d) N K R) β) o ≠ ⊤ := by
    have hRoM : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel N K R) β))) ≤ M :=
      lintegral_pow_encard_cluster_le_of_root_le β R (p + 1) o M
        (hroot R (Set.mem_union_right _ rfl))
    apply chi_ne_top_of_lintegral_pow_ne_top _ o p hp
    refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hM hRoM) ?_
    refine lintegral_mono fun ω => ?_
    have hbase : (1 : ℝ≥0∞) ≤ ((cluster ω o).encard : ℝ≥0∞) := by
      exact_mod_cast one_le_encard_cluster ω o
    exact pow_le_pow_right₀ hbase (Nat.le_succ p)
  refine continuousOn_pivotal_cutoff_uncapped_of_uniform_vertex_moment
    hKa hK' hK'c β p hp o hχ hu e M hM ?_
  intro r hr y
  exact lintegral_pow_encard_cluster_le_of_root_le β r (p + 1) y M
    (hroot r (Set.mem_union_left _ hr))

end PercLib.Models.LongRange

open Filter
open scoped Topology

namespace PercLib.Analysis

/-! ### Tails of summable families -/

/-- **The tail of a summable nonnegative family is uniformly small.** For a summable nonnegative
real family on an index type and every `ε > 0` there is a finite set `F` with
`∑' e ∉ F, g e ≤ ε`. -/
theorem exists_finset_tsum_compl_le {ι : Type*} {g : ι → ℝ} (hsum : Summable g)
    (_hg : ∀ e, 0 ≤ g e) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, ∑' e : ↥(F : Set ι)ᶜ, g e.1 ≤ ε := by
  have ht : Tendsto (fun F : Finset ι => ∑' e : ↥(F : Set ι)ᶜ, g e.1) atTop (𝓝 0) := by
    have h0 : Tendsto (fun F : Finset ι => (∑' e, g e) - ∑ e ∈ F, g e) atTop
        (𝓝 ((∑' e, g e) - ∑' e, g e)) := tendsto_const_nhds.sub hsum.hasSum
    have h1 : Tendsto (fun F : Finset ι => ∑' e : ↥(F : Set ι)ᶜ, g e.1) atTop
        (𝓝 ((∑' e, g e) - ∑' e, g e)) := by
      refine h0.congr fun F => ?_
      have := hsum.sum_add_tsum_compl (s := F)
      rw [← this]
      ring
    simpa using h1
  obtain ⟨F, hF⟩ := (ht.eventually (isOpen_Iio.mem_nhds hε)).exists
  exact ⟨F, le_of_lt hF⟩

/-! ### The finite-core / small-tail criterion -/

/-- **Continuity of a series from a uniform-in-a-neighbourhood tail estimate.**

Let `f : ι → ℝ → ℝ` be a family of functions continuous on a set `s` of parameters, absolutely
summable at every point of `s`, and suppose that at every point `x₀ ∈ s` and for every `ε > 0`
there are a neighbourhood `U` of `x₀` and a *finite* set `F` of indices such that on `U ∩ s` the
whole complement of `F` carries at most `ε` of total mass. Then `x ↦ ∑' e, f e x` is continuous
on `s`.

The finite set `F` and the neighbourhood `U` are produced point by point, so this is strictly
weaker than domination by one summable function on all of `s` (`continuousOn_tsum`). -/
theorem continuousOn_tsum_of_uniform_tail {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (hcont : ∀ e, ContinuousOn (f e) s)
    (habs : ∀ x ∈ s, Summable fun e => ‖f e x‖)
    (htail : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι,
      ∀ x ∈ U ∩ s, ∑' e : ↥(F : Set ι)ᶜ, ‖f e.1 x‖ ≤ ε) :
    ContinuousOn (fun x => ∑' e, f e x) s := by
  intro x₀ hx₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨U, hU, F, hF⟩ := htail x₀ hx₀ (ε / 3) (by linarith)
  obtain ⟨ρ, hρ0, hρU⟩ := Metric.mem_nhds_iff.1 hU
  have hcontF : ContinuousWithinAt (fun x => ∑ e ∈ F, f e x) s x₀ :=
    tendsto_finsetSum F fun e _ => hcont e x₀ hx₀
  rw [Metric.continuousWithinAt_iff] at hcontF
  obtain ⟨δ, hδ0, hδ⟩ := hcontF (ε / 3) (by linarith)
  refine ⟨min δ ρ, lt_min hδ0 hρ0, fun x hx hxd => ?_⟩
  have hxδ : dist x x₀ < δ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hxU : x ∈ U := hρU (lt_of_lt_of_le hxd (min_le_right _ _))
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  -- the series at `x` and at `x₀` split into a finite core and a tail
  have hsplitx : (∑' e, f e x) = (∑ e ∈ F, f e x) + ∑' e : ↥(F : Set ι)ᶜ, f e.1 x :=
    (((habs x hx).of_norm).sum_add_tsum_compl (s := F)).symm
  have hsplit₀ : (∑' e, f e x₀) = (∑ e ∈ F, f e x₀) + ∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀ :=
    (((habs x₀ hx₀).of_norm).sum_add_tsum_compl (s := F)).symm
  have htailx : ‖∑' e : ↥(F : Set ι)ᶜ, f e.1 x‖ ≤ ε / 3 :=
    (norm_tsum_le_tsum_norm ((habs x hx).subtype ((F : Set ι)ᶜ))).trans (hF x ⟨hxU, hx⟩)
  have htail₀ : ‖∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀‖ ≤ ε / 3 :=
    (norm_tsum_le_tsum_norm ((habs x₀ hx₀).subtype ((F : Set ι)ᶜ))).trans
      (hF x₀ ⟨hx₀U, hx₀⟩)
  have hcore : ‖(∑ e ∈ F, f e x) - (∑ e ∈ F, f e x₀)‖ < ε / 3 := by
    have h := hδ hx hxδ
    rw [Real.dist_eq] at h
    rwa [Real.norm_eq_abs]
  have hkey : (∑' e, f e x) - (∑' e, f e x₀) =
      ((∑ e ∈ F, f e x) - (∑ e ∈ F, f e x₀)) +
        ((∑' e : ↥(F : Set ι)ᶜ, f e.1 x) - (∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀)) := by
    rw [hsplitx, hsplit₀]; ring
  rw [Real.dist_eq, hkey]
  have h1 : ‖(∑' e : ↥(F : Set ι)ᶜ, f e.1 x) - (∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀)‖ ≤
      ε / 3 + ε / 3 := (norm_sub_le _ _).trans (add_le_add htailx htail₀)
  calc |((∑ e ∈ F, f e x) - (∑ e ∈ F, f e x₀)) +
        ((∑' e : ↥(F : Set ι)ᶜ, f e.1 x) - (∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀))|
      = ‖((∑ e ∈ F, f e x) - (∑ e ∈ F, f e x₀)) +
          ((∑' e : ↥(F : Set ι)ᶜ, f e.1 x) - (∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖(∑ e ∈ F, f e x) - (∑ e ∈ F, f e x₀)‖ +
          ‖(∑' e : ↥(F : Set ι)ᶜ, f e.1 x) - (∑' e : ↥(F : Set ι)ᶜ, f e.1 x₀)‖ := norm_add_le _ _
    _ < ε := by linarith

/-- **Continuity from a dominator that may depend on the point.** If every point of the parameter
set has a neighbourhood on which the family is dominated by one fixed summable function, then the
series of the family is continuous there. The dominator may therefore change with the point, as it
does when the all-pairs moment bound moves with the cut-off parameter. -/
theorem continuousOn_tsum_of_local_dominator {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (hcont : ∀ e, ContinuousOn (f e) s)
    (hloc : ∀ x₀ ∈ s, ∃ U ∈ 𝓝 x₀, ∃ g : ι → ℝ, Summable g ∧
      ∀ e, ∀ x ∈ U ∩ s, ‖f e x‖ ≤ g e) :
    ContinuousOn (fun x => ∑' e, f e x) s := by
  refine continuousOn_tsum_of_uniform_tail hcont (fun x hx => ?_) (fun x₀ hx₀ ε hε => ?_)
  · obtain ⟨U, hU, g, hg, hb⟩ := hloc x hx
    exact hg.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => hb e x ⟨mem_of_mem_nhds hU, hx⟩)
  · obtain ⟨U, hU, g, hg, hb⟩ := hloc x₀ hx₀
    have hg0 : ∀ e, 0 ≤ g e := fun e => (norm_nonneg _).trans (hb e x₀ ⟨mem_of_mem_nhds hU, hx₀⟩)
    obtain ⟨F, hF⟩ := exists_finset_tsum_compl_le hg hg0 hε
    refine ⟨U, hU, F, fun x hx => ?_⟩
    have hf' : Summable fun e : ↥((F : Set ι)ᶜ) => ‖f (e : ι) x‖ :=
      (hg.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => hb e x ⟨hx.1, hx.2⟩)).subtype
        ((F : Set ι)ᶜ)
    have hcomp := Summable.tsum_le_tsum (f := fun e : ↥((F : Set ι)ᶜ) => ‖f (e : ι) x‖)
      (g := fun e : ↥((F : Set ι)ᶜ) => g (e : ι)) (fun e => hb (e : ι) x ⟨hx.1, hx.2⟩)
      hf' (hg.subtype ((F : Set ι)ᶜ))
    exact hcomp.trans hF

/-! ### The sublinear power estimate -/

/-- **The sublinear power estimate, on the correct side.** For `0 < q ≤ 1` and
`0 < δ ≤ P` one has `P ^ q ≤ δ ^ (q - 1) * P`: the `q`-th power of a *large* quantity is bounded by
a negative power of the threshold times the quantity itself. Nothing of the kind holds for `P ≤ δ`,
where `δ ^ (q - 1) * P ≤ P ^ q` instead; see `not_rpow_le_rpow_sub_one_mul`. -/
theorem rpow_le_rpow_sub_one_mul {q P δ : ℝ} (hδ : 0 < δ) (hPδ : δ ≤ P) (hq1 : q ≤ 1) :
    P ^ q ≤ δ ^ (q - 1) * P := by
  have hP : 0 < P := lt_of_lt_of_le hδ hPδ
  have h1q : (0 : ℝ) ≤ 1 - q := by linarith
  have hstep : δ ^ (1 - q) ≤ P ^ (1 - q) := Real.rpow_le_rpow hδ.le hPδ h1q
  have hexp : δ ^ (q - 1) = (δ ^ (1 - q))⁻¹ := by
    rw [show q - 1 = -(1 - q) by ring, Real.rpow_neg hδ.le]
  have hexpP : P ^ (q - 1) = (P ^ (1 - q))⁻¹ := by
    rw [show q - 1 = -(1 - q) by ring, Real.rpow_neg hP.le]
  have hpow : P ^ q = P ^ (q - 1) * P := by
    rw [← Real.rpow_add_one hP.ne']
    congr 1
    ring
  rw [hpow, hexp, hexpP]
  exact mul_le_mul_of_nonneg_right
    ((inv_le_inv₀ (Real.rpow_pos_of_pos hP _) (Real.rpow_pos_of_pos hδ _)).mpr hstep) hP.le

/-- The sublinear power estimate fails on the other side of the threshold: with `q = 1/2`,
`δ = 4` and `P = 1 ≤ δ` the bound `P ^ q ≤ δ ^ (q - 1) * P` would read `1 ≤ 1/2`. -/
theorem not_rpow_le_rpow_sub_one_mul :
    ¬ ((1 : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2 - 1) * 1) := by
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hexp : (4 : ℝ) ^ ((1 : ℝ) / 2 - 1) = ((4 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [show (1 : ℝ) / 2 - 1 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  rw [hexp, h4, Real.one_rpow]
  norm_num

end PercLib.Analysis

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- The cutoff derivative weight of one pair is continuous on a norm-corner-free interval. -/
theorem continuousOn_cutoff_deriv_weight {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {u v : ℝ} (hu : 0 < u)
    (hI : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (e : Sym2 (Fin d → ℤ)) :
    ContinuousOn (fun r => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ)))) (Ioo u v) := by
  have hKc : ContinuousOn K (Ioi 0) := fun t ht => (hK' t ht).continuousAt.continuousWithinAt
  have hsub : Ioo u v ⊆ Ioi 0 := fun r hr => hu.trans hr.1
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [radialKernel_diag, NNReal.coe_zero, zero_mul]
      exact continuousOn_const
    have hcst : ∃ a : ℝ, ∀ r ∈ Ioo u v,
        (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) = a := by
      have hz := hI (x - y)
      by_cases hle : N (Int.cast ∘ (x - y)) ≤ u
      · exact ⟨1, fun r hr => by
          rw [radialKernel_of_ne hxy]
          simp [hle.trans_lt hr.1]⟩
      · have hge : v ≤ N (Int.cast ∘ (x - y)) := by
          by_contra h'
          exact hz ⟨not_le.1 hle, not_le.1 h'⟩
        exact ⟨0, fun r hr => by
          rw [radialKernel_of_ne hxy]
          simp [not_lt.2 (hr.2.le.trans hge)]⟩
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

open Classical in
/-- The full weighted uncapped summand of a cutoff pair is continuous from a uniform finite
root `(p+1)`-moment. This is single-pair regularity, not an all-pairs small-tail estimate. -/
theorem continuousOn_cutoff_weight_mul_pivotal_uncapped_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    {u v : ℝ} (hu : 0 < u) (hvR : v ≤ R)
    (hI : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (e : Sym2 (Fin d → ℤ)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M) :
    ContinuousOn (fun r =>
      ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v) := by
  have hRoM : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K R) β))) ≤ M :=
    lintegral_pow_encard_cluster_le_of_root_le β R (p + 1) o M
      (hroot R (Set.mem_union_right _ rfl))
  have hχR : chi (intensityProfile (cutoffKernel (d := d) N K R) β) o ≠ ⊤ := by
    apply chi_ne_top_of_lintegral_pow_ne_top _ o p hp
    refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hM hRoM) ?_
    refine lintegral_mono fun ω => ?_
    have hbase : (1 : ℝ≥0∞) ≤ ((cluster ω o).encard : ℝ≥0∞) := by
      exact_mod_cast one_le_encard_cluster ω o
    exact pow_le_pow_right₀ hbase (Nat.le_succ p)
  have hχv : chi (intensityProfile (cutoffKernel (d := d) N K v) β) o ≠ ⊤ :=
    ne_top_of_le_ne_top hχR (chi_mono (intensityProfile_le_of_le
      (fun e => monotone_cutoffKernel hKa e hvR) β) o)
  have hpiv : ContinuousOn (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v) := by
    refine continuousOn_pivotal_cutoff_uncapped_of_uniform_vertex_moment
      hKa hK' hK'c β p hp o hχv hu e M hM ?_
    intro r hr y
    exact lintegral_pow_encard_cluster_le_of_root_le β r (p + 1) y M
      (hroot r (Set.mem_union_left _ hr))
  exact (continuousOn_cutoff_deriv_weight hKa hK' hK'c β hu hI e).mul hpiv

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- Higher root moments supply every weighted summand's continuity. The whole pair series is
then continuous from pointwise absolute summability and a local small-tail estimate. -/
theorem continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v : ℝ} (hu : 0 < u) (hvR : v ≤ R)
    (hI : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (habs : ∀ r ∈ Ioo u v, Summable fun e => ‖cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖)
    (htail : ∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε) :
    ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v) := by
  let Q : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r e =>
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))
  have hpair : ∀ e : Sym2 (Fin d → ℤ), ContinuousOn (fun r => Q r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v) := by
    intro e
    refine (continuousOn_cutoff_weight_mul_pivotal_uncapped_of_root_succ_moment
      hKa hK' hK'c β p hp o hu hvR hI e M hM hroot).congr ?_
    intro r hr
    simp only [Q]
  have habs' : ∀ r ∈ Ioo u v, Summable fun e => ‖Q r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))‖ := by
    intro r hr
    simpa only [Q, hcw] using habs r hr
  have hseries := PercLib.Analysis.continuousOn_tsum_of_uniform_tail hpair habs'
    (fun r₀ hr₀ ε hε => by
      obtain ⟨U, hU, F, hF⟩ := htail r₀ hr₀ ε hε
      exact ⟨U, hU, F, fun r hr => by simpa only [Q, hcw] using hF r hr⟩)
  refine hseries.congr ?_
  intro r hr
  exact tsum_congr fun e => by simp only [Q, hcw]


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- The cutoff binomial derivative from higher root moments, pointwise absolute
summability, and a local small-tail estimate. The latter replaces an explicit global continuity
assumption. Sharpness and the literal all-radius corner claim are not asserted. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_local_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (habs : ∀ r ∈ Ioo u v, Summable fun e => ‖cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖)
    (htail : ∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  exact hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment
    (K := K) (K' := K') (R := R) (u := u) (v := v) (r₀ := r₀)
    hKa hK' hK'c β p hp M hM cw hcw hu hur hrv hvR hcorner hroot
    (continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail
      hKa hK' hK'c β p hp 0 M hM cw hcw hu hvR hcorner hroot habs htail)

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- A uniform finite root `(p+1)`-moment gives pointwise absolute summability of the full
weighted uncapped cutoff flux. The zero-rate case is treated separately, without inversion. -/
theorem summable_norm_cutoff_flux_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v : ℝ} (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ Ioo u v, (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M) :
    ∀ r ∈ Ioo u v, Summable fun e => ‖cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ := by
  obtain ⟨D, hDtop, hD⟩ := exists_uniform_i41_diagram_bound_of_root_succ_moment
    (K := K) β p M hM hroot
  intro r hr
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel (d := d) N K r) β)
  have hrootp : (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hM (hroot r hr)) ?_
    refine lintegral_mono fun ω => ?_
    have hbase : (1 : ℝ≥0∞) ≤ ((cluster ω 0).encard : ℝ≥0∞) := by
      exact_mod_cast one_le_encard_cluster ω 0
    exact pow_le_pow_right₀ hbase (Nat.le_succ p)
  have hvmom : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p ∂μ) ≠ ⊤ := by
    intro y
    exact vertex_moment_ne_top_of_root_moment β r p y hrootp
  have hins : ∀ e : Sym2 (Fin d → ℤ), (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
      ∂μ) ≠ ⊤ := by
    intro e
    exact insert_moments_of_vertex_moments β p r 0 hvmom e
  have hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂μ| ≤
      |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal := by
    intro S
    exact finite_sum_cutoff_pivotal_le_of_binomial_diagram β p hp r cw hcw hins
      D hDtop (hD r hr) hcorner hr S
  by_cases hrate : (β : ℝ) * -K' r = 0
  · have hzero : (fun e : Sym2 (Fin d → ℤ) => ‖cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂μ‖) = fun _ => 0 := by
      funext e
      simp [hcw r e, hrate]
    rw [hzero]
    exact summable_zero
  · have hfin : ∀ e, ∀ᵐ ω ∂μ, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ≠ ⊤ := by
      intro e
      exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e 0)
        p hp (hins e)
    have hint : ∀ e, Integrable
        (fun ω => (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p) μ := by
      intro e
      exact integrable_toReal_pow_encard_cluster_insert e 0 p (hins e)
    have hKdReal : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
        |∫ ω, ((((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) 0).encard : ℝ≥0∞).toReal) ^ p) ∂μ| ≤
        |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal := by
      intro S
      refine le_trans ?_ (hKd S)
      refine Finset.sum_le_sum fun e _ => ?_
      rw [integral_pivotal_pow_eq_real_sub μ e 0 p (hfin e)]
    have hclosed := summable_closed_flux_cutoff_of_insert_moments
      (N := N.toSeminorm) (K := K) (K' := K') p β r 0 (cw r)
      (|(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal)
      (hcw r) hp hins hKdReal hrate
    let rate : ℝ := (β : ℝ) * -K' r
    have hpair : ∀ e : Sym2 (Fin d → ℤ), cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂μ =
        rate * ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p) ∂μ) := by
      intro e
      calc
        cw r e * ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂μ =
          ((β : ℝ) * -K' r) * ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
              (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
                ((cluster ω 0).encard : ℝ≥0∞) ^ p)) ∂μ).toReal) :=
          cutoff_weight_mul_integral_eq_rate_mul_closed_toReal p β r 0 (cw r)
            (hcw r) hfin hint e
        _ = _ := by
          rw [integral_toReal_closed_pivotal μ e 0 p (hfin e)]
    have hsum := hclosed.1.mul_left rate
    have hsum' : Summable fun e : Sym2 (Fin d → ℤ) => cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂μ := by
      apply hsum.congr
      intro e
      exact (hpair e).symm
    exact hsum'.norm

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- Higher root moments supply every weighted summand's continuity. The whole pair series is
then continuous from pointwise absolute summability and a local small-tail estimate. -/
theorem continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v : ℝ} (hu : 0 < u) (hvR : v ≤ R)
    (hI : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (htail : ∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε) :
    ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (Ioo u v) := by
  exact continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail
    hKa hK' hK'c β p hp 0 M hM cw hcw hu hvR hI hroot
    (summable_norm_cutoff_flux_of_root_succ_moment β p hp M hM cw hcw hI
      (fun r hr => hroot r (Set.mem_union_left _ hr))) htail


open Classical in
/-- The cutoff binomial derivative from higher root moments, pointwise absolute
summability, and a local small-tail estimate. The latter replaces an explicit global continuity
assumption. Sharpness and the literal all-radius corner claim are not asserted. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (htail : ∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ := by
  exact hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment
    (K := K) (K' := K') (R := R) (u := u) (v := v) (r₀ := r₀)
    hKa hK' hK'c β p hp M hM cw hcw hu hur hrv hvR hcorner hroot
    (continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail
      hKa hK' hK'c β p hp M hM cw hcw hu hvR hcorner hroot htail)


end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability MeasureTheory
open Filter Set
open scoped ENNReal NNReal Topology

open Classical in
/-- **Uniform bound on the total absolute weighted cutoff flux.**

A uniform finite root `(p+1)`-moment bound on a corner-free interval `Ioo u v` produces a single
constant `C` such that, at every `r ∈ Ioo u v`, the weighted uncapped cutoff pivotal series is
absolutely summable and its total mass is at most `|β(-K'(r))| * C`.

The proof does not assume the finite-sum dominator `hKd` or the summand behaviour: those come from
the root moment, through the binomial diagram. The case `β(-K'(r)) = 0`, where the summands vanish
identically, is treated separately; the nonzero case uses the closed-coordinate criterion with the
per-pair conversion identity. -/
theorem exists_uniform_tsum_norm_cutoff_flux_le_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v : ℝ} (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ Ioo u v, (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo u v,
      Summable (fun e => ‖cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖) ∧
      (∑' e, ‖cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖) ≤
        |(β : ℝ) * -K' r| * C := by
  obtain ⟨D, hDtop, hD⟩ := exists_uniform_i41_diagram_bound_of_root_succ_moment
    (K := K) β p M hM hroot
  refine ⟨(∑ ℓ ∈ Finset.range p, D ℓ).toReal, ENNReal.toReal_nonneg, ?_⟩
  have hrootp : ∀ r ∈ Ioo u v, (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
    intro r hr
    refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hM (hroot r hr)) ?_
    refine lintegral_mono fun ω => ?_
    have hbase : (1 : ℝ≥0∞) ≤ ((cluster ω 0).encard : ℝ≥0∞) := by
      exact_mod_cast one_le_encard_cluster ω 0
    exact pow_le_pow_right₀ hbase (Nat.le_succ p)
  have hvmom : ∀ r ∈ Ioo u v, ∀ y : Fin d → ℤ,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
    intro r hr y
    exact vertex_moment_ne_top_of_root_moment β r p y (hrootp r hr)
  have hins := insert_moments_of_vertex_moments_Ioo_modelNorm β p 0 hvmom
  intro r hr
  have hKd : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤
      |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal :=
    fun S => finite_sum_cutoff_pivotal_le_of_binomial_diagram β p hp r cw hcw
      (hins r hr) D hDtop (hD r hr) hcorner hr S
  by_cases hrate : (β : ℝ) * -K' r = 0
  · have hzero : (fun e : Sym2 (Fin d → ℤ) => ‖cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖) = fun _ => 0 := by
      funext e
      simp [hcw r e, hrate]
    refine ⟨?_, ?_⟩
    · rw [hzero]
      exact summable_zero
    · rw [hzero, tsum_zero]
      simp [hrate]
  · have hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)),
        ((cluster (insert e ω) 0).encard : ℝ≥0∞) ≠ ⊤ := by
      intro e
      exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e 0)
        p hp (hins r hr e)
    have hint : ∀ e, Integrable
        (fun ω => (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p)
        (law (intensityProfile (cutoffKernel (d := d) N K r) β)) := by
      intro e
      exact integrable_toReal_pow_encard_cluster_insert e 0 p (hins r hr e)
    have hKdReal : ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
        |∫ ω, ((((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
          (((cluster (ω \ {e}) 0).encard : ℝ≥0∞).toReal) ^ p)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| ≤
        |(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal := by
      intro S
      refine le_trans ?_ (hKd S)
      refine Finset.sum_le_sum fun e _ => ?_
      rw [integral_pivotal_pow_eq_real_sub _ e 0 p (hfin e)]
    have hclosed := summable_closed_flux_cutoff_of_insert_moments
      (N := N.toSeminorm) (K := K) (K' := K') p β r 0 (cw r)
      (|(β : ℝ) * -K' r| * (∑ ℓ ∈ Finset.range p, D ℓ).toReal)
      (hcw r) hp (fun e => hins r hr e) hKdReal hrate
    have hpair : ∀ e : Sym2 (Fin d → ℤ), cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) =
        ((β : ℝ) * -K' r) *
          ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            ∫ ω, (if e ∈ ω then (0 : ℝ) else
              (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
                (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p)
              ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) := by
      intro e
      rw [cutoff_weight_mul_integral_eq_rate_mul_closed_toReal p β r 0 (cw r) (hcw r)
          hfin hint e,
        integral_toReal_closed_pivotal _ e 0 p (hfin e)]
    have hsum : Summable fun e : Sym2 (Fin d → ℤ) => ((β : ℝ) * -K' r) *
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
              (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p)
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) :=
      hclosed.1.mul_left _
    have hsum' : Summable fun e : Sym2 (Fin d → ℤ) => cw r e *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) :=
      hsum.congr fun e => (hpair e).symm
    refine ⟨hsum'.norm, ?_⟩
    have hnormeq : (∑' e, ‖cw r e *
          ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖) =
        |(β : ℝ) * -K' r| * ∑' e,
          |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
            ∫ ω, (if e ∈ ω then (0 : ℝ) else
              (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
                (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p)
              ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| := by
      have hcongr : (fun e : Sym2 (Fin d → ℤ) => ‖cw r e *
            ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal
              ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖) =
          fun e => |(β : ℝ) * -K' r| *
            |(radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
              ∫ ω, (if e ∈ ω then (0 : ℝ) else
                (((cluster (insert e ω) 0).encard : ℝ≥0∞).toReal) ^ p -
                  (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ p)
                ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))| := by
        funext e
        rw [hpair e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [hcongr, tsum_mul_left]
    rw [hnormeq]
    refine le_trans (mul_le_mul_of_nonneg_left hclosed.2 (abs_nonneg _)) ?_
    rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hrate), one_mul]

end PercLib.Models.LongRange

namespace PercLib.Analysis

/-- A finite `ℝ≥0∞`-valued tail on a cofinite set forces summability of the norm series. -/
theorem summable_norm_of_ennreal_tsum_compl_ne_top {ι : Type*} (g : ι → ℝ) (F : Finset ι)
    (h : (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖g e.1‖) ≠ ⊤) :
    Summable fun e => ‖g e‖ := by
  have hsub : Summable fun e : ↥((F : Set ι)ᶜ) => ‖g (e : ι)‖ := by
    refine summable_of_sum_le (f := fun e : ↥((F : Set ι)ᶜ) => ‖g (e : ι)‖)
      (c := (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖g (e : ι)‖).toReal)
      (fun e => norm_nonneg _) fun s => ?_
    have hle : (∑ e ∈ s, ENNReal.ofReal ‖g (e : ι)‖) ≤
        ∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖g (e : ι)‖ := ENNReal.sum_le_tsum s
    have hfin : (∑ e ∈ s, ENNReal.ofReal ‖g (e : ι)‖) =
        ENNReal.ofReal (∑ e ∈ s, ‖g (e : ι)‖) :=
      (ENNReal.ofReal_sum_of_nonneg (fun e _ => norm_nonneg _)).symm
    have hto : (∑ e ∈ s, ENNReal.ofReal ‖g (e : ι)‖).toReal = ∑ e ∈ s, ‖g (e : ι)‖ := by
      rw [hfin, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun e _ => norm_nonneg _))]
    calc ∑ e ∈ s, ‖g (e : ι)‖ = (∑ e ∈ s, ENNReal.ofReal ‖g (e : ι)‖).toReal := hto.symm
      _ ≤ (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖g (e : ι)‖).toReal :=
          ENNReal.toReal_mono h hle
  exact (Finset.summable_compl_iff (s := F) (f := fun e : ι => ‖g e‖)).mp hsub

/-- A local `ℝ≥0∞` small-tail estimate gives pointwise absolute summability. -/
theorem summable_of_local_ennreal_tail {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (htail : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ ENNReal.ofReal ε) :
    ∀ x ∈ s, Summable fun e => ‖f e x‖ := by
  intro x hx
  obtain ⟨U, hU, F, hF⟩ := htail x hx 1 one_pos
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hle : (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ 1 := by
    simpa using hF x ⟨hxU, hx⟩
  exact summable_norm_of_ennreal_tsum_compl_ne_top (fun e => f e x) F
    (ne_top_of_le_ne_top ENNReal.one_ne_top hle)

/-- A real tail bound follows from the `ℝ≥0∞` one, using the summability it supplies. -/
theorem tsum_compl_le_of_ennreal_tail {ι : Type*} {g : ι → ℝ} (F : Finset ι) {ε : ℝ}
    (h : (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖g e.1‖) ≤ ENNReal.ofReal ε)
    (hε : 0 ≤ ε) (hsum : Summable fun e => ‖g e‖) :
    (∑' e : ↥((F : Set ι)ᶜ), ‖g e.1‖) ≤ ε := by
  have hsub : Summable fun e : ↥((F : Set ι)ᶜ) => ‖g (e : ι)‖ := hsum.subtype _
  have hkey : ENNReal.ofReal (∑' e : ↥((F : Set ι)ᶜ), ‖g (e : ι)‖) =
      ∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖g (e : ι)‖ :=
    ENNReal.ofReal_tsum_of_nonneg (f := fun e : ↥((F : Set ι)ᶜ) => ‖g (e : ι)‖)
      (fun e => norm_nonneg _) hsub
  rw [← hkey] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp h

/-- **Continuity of a series from a local `ℝ≥0∞` small-tail estimate.**

This is `continuousOn_tsum_of_uniform_tail` with the pointwise absolute summability hypothesis
removed: the `ℝ≥0∞` tail bound is total (it is `⊤` exactly when the tail fails to be summable),
so it already implies summability at every point of `s`. -/
theorem continuousOn_tsum_of_local_tail_ennreal {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (hcont : ∀ e, ContinuousOn (f e) s)
    (htail : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ ENNReal.ofReal ε) :
    ContinuousOn (fun x => ∑' e, f e x) s := by
  have habs := summable_of_local_ennreal_tail htail
  refine continuousOn_tsum_of_uniform_tail hcont habs fun x₀ hx₀ ε hε => ?_
  obtain ⟨U, hU, F, hF⟩ := htail x₀ hx₀ ε hε
  exact ⟨U, hU, F, fun x hx =>
    tsum_compl_le_of_ennreal_tail F (hF x hx) hε.le (habs x hx.2)⟩

/-- The `ℝ≥0∞` local tail is equivalent to a bound on every finite sub-sum of the complement,
which is the form supplied by a finite-exhaustion estimate. -/
theorem localTail_ennreal_of_finite_subset_tail {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (h : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      ∀ t : Finset ↥((F : Set ι)ᶜ), ∑ e ∈ t, ‖f (e : ι) x‖ ≤ ε) :
    ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ ENNReal.ofReal ε := by
  intro x₀ hx₀ ε hε
  obtain ⟨U, hU, F, hF⟩ := h x₀ hx₀ ε hε
  refine ⟨U, hU, F, fun x hx => ?_⟩
  have hbound : ∀ t : Finset ↥((F : Set ι)ᶜ),
      ∑ e ∈ t, ENNReal.ofReal ‖f (e : ι) x‖ ≤ ENNReal.ofReal ε := by
    intro t
    have hsplit : (∑ e ∈ t, ENNReal.ofReal ‖f (e : ι) x‖) =
        ENNReal.ofReal (∑ e ∈ t, ‖f (e : ι) x‖) :=
      (ENNReal.ofReal_sum_of_nonneg (f := fun e : ↥((F : Set ι)ᶜ) => ‖f (e : ι) x‖)
        (fun e _ => norm_nonneg _)).symm
    rw [hsplit]
    exact ENNReal.ofReal_le_ofReal (hF x hx t)
  calc (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f (e : ι) x‖)
      = ⨆ t : Finset ↥((F : Set ι)ᶜ), ∑ e ∈ t, ENNReal.ofReal ‖f (e : ι) x‖ :=
        ENNReal.tsum_eq_iSup_sum
    _ ≤ ENNReal.ofReal ε := iSup_le hbound

/-- The finite-subset form of the local small tail already gives continuity, with no separate
summability hypothesis. -/
theorem continuousOn_tsum_of_finite_subset_tail {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (hcont : ∀ e, ContinuousOn (f e) s)
    (h : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      ∀ t : Finset ↥((F : Set ι)ᶜ), ∑ e ∈ t, ‖f (e : ι) x‖ ≤ ε) :
    ContinuousOn (fun x => ∑' e, f e x) s :=
  continuousOn_tsum_of_local_tail_ennreal hcont (localTail_ennreal_of_finite_subset_tail h)

/-- Conversely, the `ℝ≥0∞` local tail bounds every finite sub-sum of the complement. -/
theorem finite_subset_tail_of_localTail_ennreal {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (htail : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ ENNReal.ofReal ε) :
    ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      ∀ t : Finset ↥((F : Set ι)ᶜ), ∑ e ∈ t, ‖f (e : ι) x‖ ≤ ε := by
  intro x₀ hx₀ ε hε
  obtain ⟨U, hU, F, hF⟩ := htail x₀ hx₀ ε hε
  refine ⟨U, hU, F, fun x hx t => ?_⟩
  have hsplit : (∑ e ∈ t, ENNReal.ofReal ‖f (e : ι) x‖) =
      ENNReal.ofReal (∑ e ∈ t, ‖f (e : ι) x‖) :=
    (ENNReal.ofReal_sum_of_nonneg (f := fun e : ↥((F : Set ι)ᶜ) => ‖f (e : ι) x‖)
      (fun e _ => norm_nonneg _)).symm
  have hle : (∑ e ∈ t, ENNReal.ofReal ‖f (e : ι) x‖) ≤ ENNReal.ofReal ε :=
    (ENNReal.sum_le_tsum t).trans (hF x hx)
  rw [hsplit] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hle

/-- A local summable majorant supplies the `ℝ≥0∞` local small-tail hypothesis. -/
theorem localTail_ennreal_of_local_dominator {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (hloc : ∀ x₀ ∈ s, ∃ U ∈ 𝓝 x₀, ∃ g : ι → ℝ, Summable g ∧
      ∀ e, ∀ x ∈ U ∩ s, ‖f e x‖ ≤ g e) :
    ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ ENNReal.ofReal ε := by
  intro x₀ hx₀ ε hε
  obtain ⟨U, hU, g, hg, hb⟩ := hloc x₀ hx₀
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  have hg0 : ∀ e, 0 ≤ g e := fun e => (norm_nonneg _).trans (hb e x₀ ⟨hx₀U, hx₀⟩)
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_le hg hg0 hε
  refine ⟨U, hU, F, fun x hx => ?_⟩
  have hsub : Summable fun e : ↥((F : Set ι)ᶜ) => g (e : ι) := hg.subtype _
  calc (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖)
      ≤ ∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal (g (e : ι)) :=
        ENNReal.tsum_le_tsum fun e => ENNReal.ofReal_le_ofReal (hb (e : ι) x ⟨hx.1, hx.2⟩)
    _ = ENNReal.ofReal (∑' e : ↥((F : Set ι)ᶜ), g (e : ι)) :=
        (ENNReal.ofReal_tsum_of_nonneg (f := fun e : ↥((F : Set ι)ᶜ) => g (e : ι))
          (fun e => hg0 (e : ι)) hsub).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hF

/-- The real-valued small-tail hypothesis together with pointwise summability implies the
`ℝ≥0∞` form, so the new criterion generalises the existing one. -/
theorem localTail_ennreal_of_real_tail {ι : Type*} {s : Set ℝ} {f : ι → ℝ → ℝ}
    (habs : ∀ x ∈ s, Summable fun e => ‖f e x‖)
    (htail : ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      ∑' e : ↥((F : Set ι)ᶜ), ‖f e.1 x‖ ≤ ε) :
    ∀ x₀ ∈ s, ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∃ F : Finset ι, ∀ x ∈ U ∩ s,
      (∑' e : ↥((F : Set ι)ᶜ), ENNReal.ofReal ‖f e.1 x‖) ≤ ENNReal.ofReal ε := by
  intro x₀ hx₀ ε hε
  obtain ⟨U, hU, F, hF⟩ := htail x₀ hx₀ ε hε
  refine ⟨U, hU, F, fun x hx => ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun e : ↥((F : Set ι)ᶜ) => ‖f (e : ι) x‖)
    (fun e => norm_nonneg _) ((habs x hx.2).subtype _)]
  exact ENNReal.ofReal_le_ofReal (hF x hx)

end PercLib.Analysis

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-! ### The strict indicator from the right -/

/-- From the right of `n` the strict indicator `1 (s < r)` converges to the closed-ball value
`1 (s ≤ n)`.  This is the single scalar fact behind the corner. -/
theorem tendsto_indicator_lt_nhdsGT_le {s n : ℝ} :
    Tendsto (fun r : ℝ => (if s < r then (1 : ℝ) else 0)) (𝓝[>] n)
      (𝓝 (if s ≤ n then (1 : ℝ) else 0)) := by
  by_cases h : s ≤ n
  · rw [ite_eq_left h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (ite_eq_left (lt_of_le_of_lt h hr)).symm
  · rw [ite_eq_right h]
    have hs : n < s := not_le.1 h
    have hmem : Iio s ∈ 𝓝[>] n :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hs)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem] with r hr
    exact (ite_eq_right (not_lt.2 hr.le)).symm

/-- The same statement for the radial kernel of a single unordered pair: from the right, the
strict radial weight `1 (N z < r)` converges to the closed-ball weight `1 (N z ≤ n)`.  On the
diagonal both sides are `0`. -/
theorem tendsto_coe_radialKernel_indicator_nhdsGT {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    (n : ℝ) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ))
      (𝓝[>] n) (𝓝 (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ)) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [radialKernel_diag, NNReal.coe_zero]
      exact tendsto_const_nhds
    · have h1 : ∀ r : ℝ,
          (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) =
            if N (Int.cast ∘ (x - y)) < r then 1 else 0 := by
        intro r
        rw [coe_radialKernel_of_ne (K := fun s => if s < r then 1 else 0) hxy
          (by split <;> norm_num)]
      have h2 : (radialKernel N (fun s => if s ≤ n then 1 else 0) s(x, y) : ℝ) =
          if N (Int.cast ∘ (x - y)) ≤ n then 1 else 0 := by
        rw [coe_radialKernel_of_ne (K := fun s => if s ≤ n then 1 else 0) hxy
          (by split <;> norm_num)]
      simp only [h1, h2]
      exact tendsto_indicator_lt_nhdsGT_le

/-! ### Right continuity of the cut-off kernel in the scale -/

/-- For a profile that is continuous and decreasing on `(0, ∞)` and a positive scale, the
cut-off kernel of every unordered pair is right-continuous in the scale at that scale. -/
theorem tendsto_coe_cutoffKernel {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hKc : ContinuousOn K (Ioi 0))
    {n : ℝ} (hn : 0 < n) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (cutoffKernel N K r e : ℝ)) (𝓝[>] n)
      (𝓝 (cutoffKernel N K n e : ℝ)) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [cutoffKernel_def, radialKernel_diag, NNReal.coe_zero]
      exact tendsto_const_nhds
    · rw [coe_cutoffKernel_eq_max hKa hn hxy]
      have hKca : ContinuousAt K n := hKc.continuousAt (isOpen_Ioi.mem_nhds hn)
      have hKr : Tendsto K (𝓝[>] n) (𝓝 (K n)) := hKca.mono_left nhdsWithin_le_nhds
      have hlim : Tendsto (fun r : ℝ => max (K (N (Int.cast ∘ (x - y))) - K r) 0) (𝓝[>] n)
          (𝓝 (max (K (N (Int.cast ∘ (x - y))) - K n) 0)) :=
        (tendsto_const_nhds.sub hKr).max tendsto_const_nhds
      have hmem : Ioi (0 : ℝ) ∈ 𝓝[>] n := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hn)
      refine Tendsto.congr' ?_ hlim
      filter_upwards [hmem] with r hr
      exact (coe_cutoffKernel_eq_max hKa hr hxy).symm

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-! ### Right continuity of the full derivative weight -/

/-- The derivative weight of a cut-off pair is right-continuous in the scale, and its right limit
is the same expression with the **closed-ball** radial factor `1 (N z ≤ n)`.  Off the diagonal the
strict and closed radial factors differ only at `r = n` itself; on the diagonal both vanish. -/
theorem tendsto_cutoff_coeff_nhdsGT {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {n : ℝ} (hn : 0 < n)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
      (𝓝[>] n)
      (𝓝 ((radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel N K n e : ℝ))))) := by
  have hKc : ContinuousOn K (Ioi 0) := fun t ht => (hK' t ht).continuousAt.continuousWithinAt
  have hK'ca : ContinuousAt K' n := hK'c.continuousAt (isOpen_Ioi.mem_nhds hn)
  have hK'r : Tendsto K' (𝓝[>] n) (𝓝 (K' n)) := hK'ca.mono_left nhdsWithin_le_nhds
  have hrate : Tendsto (fun r : ℝ => (β : ℝ) * -K' r) (𝓝[>] n)
      (𝓝 ((β : ℝ) * -K' n)) := hK'r.neg.const_mul (β : ℝ)
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))
      (𝓝[>] n) (𝓝 (Real.exp (-(β : ℝ) * (cutoffKernel N K n e : ℝ)))) :=
    (Real.continuous_exp.tendsto _).comp
      ((tendsto_coe_cutoffKernel hKa hKc hn e).const_mul (-(β : ℝ)))
  exact (tendsto_coe_radialKernel_indicator_nhdsGT n e).mul (hrate.mul hexp)

/-! ### The aggregate right limit of the pivotal flux -/

/-- **The aggregate right limit of the cut-off pivotal flux at a corner.**

If every weighted pivotality `cw r e * pivotal r e` converges to its value at `n` along `𝓝[>] n`
and, on a right-neighbourhood of `n`, the whole family is bounded in norm by one summable
`bound`, then Tannery's theorem gives the right limit of the *entire* pair series, and that limit
carries the closed-ball radial factor.

This is the passage the moment derivative at a lattice norm needs.  The uniform one-sided
dominator `hbd` is the remaining premise: it is not inferred from pointwise finiteness. -/
theorem tendsto_tsum_flux_nhdsGT_of_dominated {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {n : ℝ} (hn : 0 < n)
    (f : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hf : ∀ r e, f r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (Piv : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hPiv : ∀ e, Tendsto (fun r => Piv r e) (𝓝[>] n) (𝓝 (Piv n e)))
    (bound : Sym2 (Fin d → ℤ) → ℝ) (hbound : Summable bound)
    (hbd : ∀ᶠ r in 𝓝[>] n, ∀ e, ‖f r e * Piv r e‖ ≤ bound e) :
    Tendsto (fun r => ∑' e, f r e * Piv r e) (𝓝[>] n)
      (𝓝 (∑' e, (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))) *
        Piv n e)) := by
  have hlim : ∀ e : Sym2 (Fin d → ℤ), Tendsto (fun r : ℝ => f r e * Piv r e) (𝓝[>] n)
      (𝓝 ((radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))) *
        Piv n e)) := by
    intro e
    have h1 : Tendsto (fun r : ℝ => f r e) (𝓝[>] n)
        (𝓝 ((radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))))) := by
      simp only [hf]
      exact tendsto_cutoff_coeff_nhdsGT hKa hK' hK'c β hn e
    exact h1.mul (hPiv e)
  exact tendsto_tsum_of_dominated_convergence hbound hlim hbd

/-! ### Discharging the per-pair pivotality limit from a uniform root moment -/

/-- A uniform finite root `(p+1)`-st moment on a window that *contains* `n` in its interior gives
continuity in the scale of every uncapped single-pair pivotality at `n`, hence the per-pair
convergence hypothesis of `tendsto_tsum_flux_nhdsGT_of_dominated`. -/
theorem continuousAt_pivotal_cutoff_uncapped_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R u n : ℝ}
    (hu : 0 < u) (hun : u < n) (hnR : n < R) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Ioo u R ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (𝓝[>] n)
      (𝓝 (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K n) β)))) := by
  have hcont : ContinuousOn (fun r : ℝ => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u R) :=
    continuousOn_pivotal_cutoff_uncapped_of_root_succ_moment
      hKa hK' hK'c β p hp o hu e M hM hroot
  have hmem : Ioo u R ∈ 𝓝 n := isOpen_Ioo.mem_nhds ⟨hun, hnR⟩
  exact ((hcont.continuousAt hmem).mono_left nhdsWithin_le_nhds)

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- **The right limit of the actual cut-off pivotal flux at a lattice norm.**

Uniform finite root `(p+1)`-st moments on a window containing `n` in its interior supply every
single-pair pivotality limit, so the aggregate right limit of
`r ↦ Σ'_e cw r e * pivotal r e` is the same series with the **closed-ball** radial factor.  The
only premise that is neither a moment bound nor a continuity statement is `hbd`: a summable
dominator for the whole weighted pair series, uniformly on one side of `n`.  That uniform
one-sided domination is *not* derived here — pointwise finiteness of the flux does not give it. -/
theorem tendsto_tsum_cutoff_pivotal_flux_nhdsGT_of_root_succ_moment {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ)
    {R u n : ℝ} (hu : 0 < u) (hun : u < n) (hnR : n < R) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Ioo u R ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (bound : Sym2 (Fin d → ℤ) → ℝ) (hbound : Summable bound)
    (hbd : ∀ᶠ r in 𝓝[>] n, ∀ e, ‖cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ bound e) :
    Tendsto (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (𝓝[>] n)
      (𝓝 (∑' e, (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K n) β)))) := by
  have hPiv : ∀ e : Sym2 (Fin d → ℤ), Tendsto (fun r : ℝ =>
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r) β))) (𝓝[>] n)
      (𝓝 (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K n) β)))) :=
    fun e => continuousAt_pivotal_cutoff_uncapped_of_root_succ_moment
      hKa hK' hK'c β p hp o hu hun hnR M hM hroot e
  exact tendsto_tsum_flux_nhdsGT_of_dominated (n := n) (hn := hu.trans hun)
    hKa hK' hK'c β cw hcw
    (fun r e => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) hPiv bound hbound hbd

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-! ### The strict side: the left limit

From the left the strict radial weight `1 (N z < r)` returns to its own value `1 (N z < n)`: it
does *not* pick up the exact-norm shell.  Together with the right-limit results above this pins
the jump of the flux at a lattice norm to exactly that shell. -/

/-- From the left the strict indicator is left-continuous: `1 (s < r) → 1 (s < n)` alone
`𝓝[<] n`. -/
theorem tendsto_indicator_lt_nhdsLT_lt {s n : ℝ} :
    Tendsto (fun r : ℝ => (if s < r then (1 : ℝ) else 0)) (𝓝[<] n)
      (𝓝 (if s < n then (1 : ℝ) else 0)) := by
  by_cases h : s < n
  · rw [ite_eq_left h]
    have hmem : Ioi s ∈ 𝓝[<] n := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds h)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem] with r hr
    exact (ite_eq_left hr).symm
  · rw [ite_eq_right h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (ite_eq_right (not_lt.2 (hr.le.trans (not_lt.1 h)))).symm

/-- The radial kernel of a single unordered pair is left-continuous in the scale, with the strict
weight `1 (N z < n)` as its left limit. -/
theorem tendsto_coe_radialKernel_indicator_nhdsLT {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    (n : ℝ) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ))
      (𝓝[<] n) (𝓝 (radialKernel N (fun s => if s < n then 1 else 0) e : ℝ)) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [radialKernel_diag, NNReal.coe_zero]
      exact tendsto_const_nhds
    · have h1 : ∀ r : ℝ,
          (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) =
            if N (Int.cast ∘ (x - y)) < r then 1 else 0 := by
        intro r
        rw [coe_radialKernel_of_ne (K := fun s => if s < r then 1 else 0) hxy
          (by split <;> norm_num)]
      simp only [h1]
      exact tendsto_indicator_lt_nhdsLT_lt

/-- Right continuity of the cut-off kernel in the scale, for any filter refining the
neighbourhood filter of the scale.  This is the form needed on both sides of a corner. -/
theorem tendsto_coe_cutoffKernel_of_le {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hKc : ContinuousOn K (Ioi 0)) {n : ℝ} (hn : 0 < n)
    {l : Filter ℝ} (hl : l ≤ 𝓝 n) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (cutoffKernel N K r e : ℝ)) l (𝓝 (cutoffKernel N K n e : ℝ)) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [cutoffKernel_def, radialKernel_diag, NNReal.coe_zero]
      exact tendsto_const_nhds
    · rw [coe_cutoffKernel_eq_max hKa hn hxy]
      have hKca : ContinuousAt K n := hKc.continuousAt (isOpen_Ioi.mem_nhds hn)
      have hKr : Tendsto K l (𝓝 (K n)) := hKca.mono_left hl
      have hlim : Tendsto (fun r : ℝ => max (K (N (Int.cast ∘ (x - y))) - K r) 0) l
          (𝓝 (max (K (N (Int.cast ∘ (x - y))) - K n) 0)) :=
        (tendsto_const_nhds.sub hKr).max tendsto_const_nhds
      have hmem : Ioi (0 : ℝ) ∈ l := hl (isOpen_Ioi.mem_nhds hn)
      refine Tendsto.congr' ?_ hlim
      filter_upwards [hmem] with r hr
      exact (coe_cutoffKernel_eq_max hKa hr hxy).symm

/-- The rate-and-exponential factor of the derivative weight converges to its value at `n` along
any filter refining `𝓝 n`. -/
theorem tendsto_cutoff_rate_exp_of_le {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {n : ℝ} (hn : 0 < n)
    {l : Filter ℝ} (hl : l ≤ 𝓝 n) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))
      l (𝓝 ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel N K n e : ℝ)))) := by
  have hKc : ContinuousOn K (Ioi 0) := fun t ht => (hK' t ht).continuousAt.continuousWithinAt
  have hK'ca : ContinuousAt K' n := hK'c.continuousAt (isOpen_Ioi.mem_nhds hn)
  have hrate : Tendsto (fun r : ℝ => (β : ℝ) * -K' r) l (𝓝 ((β : ℝ) * -K' n)) :=
    (hK'ca.mono_left hl).neg.const_mul (β : ℝ)
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))) l
      (𝓝 (Real.exp (-(β : ℝ) * (cutoffKernel N K n e : ℝ)))) :=
    (Real.continuous_exp.tendsto _).comp
      ((tendsto_coe_cutoffKernel_of_le hKa hKc hn hl e).const_mul (-(β : ℝ)))
  exact hrate.mul hexp

/-- The derivative weight of a cut-off pair is left-continuous in the scale: from the left its
limit is its own value at `n`, with the strict radial factor. -/
theorem tendsto_cutoff_coeff_nhdsLT {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {n : ℝ} (hn : 0 < n)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
      (𝓝[<] n)
      (𝓝 ((radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel N K n e : ℝ))))) :=
  (tendsto_coe_radialKernel_indicator_nhdsLT n e).mul
    (tendsto_cutoff_rate_exp_of_le hKa hK' hK'c β hn nhdsWithin_le_nhds e)

/-- **The aggregate left limit of the cut-off pivotal flux at a corner.**  From the left the whole
series converges to its own value at `n`: no exact-norm shell is added.  The dominator needed here
is one-sided too. -/
theorem tendsto_tsum_flux_nhdsLT_of_dominated {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {n : ℝ} (hn : 0 < n)
    (f : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hf : ∀ r e, f r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (Piv : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hPiv : ∀ e, Tendsto (fun r => Piv r e) (𝓝[<] n) (𝓝 (Piv n e)))
    (bound : Sym2 (Fin d → ℤ) → ℝ) (hbound : Summable bound)
    (hbd : ∀ᶠ r in 𝓝[<] n, ∀ e, ‖f r e * Piv r e‖ ≤ bound e) :
    Tendsto (fun r => ∑' e, f r e * Piv r e) (𝓝[<] n) (𝓝 (∑' e, f n e * Piv n e)) := by
  have hlim : ∀ e : Sym2 (Fin d → ℤ), Tendsto (fun r : ℝ => f r e * Piv r e) (𝓝[<] n)
      (𝓝 (f n e * Piv n e)) := by
    intro e
    simp only [hf]
    have h1 : Tendsto (fun r : ℝ => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
        (𝓝[<] n)
        (𝓝 ((radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))))) :=
      tendsto_cutoff_coeff_nhdsLT hKa hK' hK'c β hn e
    exact h1.mul (hPiv e)
  exact tendsto_tsum_of_dominated_convergence hbound hlim hbd

/-! ### The two-sided obstruction -/

/-- If a function has different one-sided limits at `n`, it has no limit at `n`.  Applied to the
cut-off flux at a lattice norm this is the exact corner obstruction: the right limit carries the
closed ball, the left limit the strict ball, and the two differ by the exact-norm shell. -/
theorem not_exists_tendsto_of_nhdsGT_nhdsLT_ne {Φ : ℝ → ℝ} {n L₁ L₂ : ℝ}
    (h₁ : Tendsto Φ (𝓝[>] n) (𝓝 L₁)) (h₂ : Tendsto Φ (𝓝[<] n) (𝓝 L₂)) (hne : L₁ ≠ L₂) :
    ¬ ∃ L, Tendsto Φ (𝓝 n) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hL₁ : L₁ = L := tendsto_nhds_unique h₁ (hL.mono_left nhdsWithin_le_nhds)
  have hL₂ : L₂ = L := tendsto_nhds_unique h₂ (hL.mono_left nhdsWithin_le_nhds)
  exact hne (hL₁.trans hL₂.symm)

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-! ### The exact-norm shell as the exact corner gap -/

/-- Pointwise, the closed-ball radial weight is the strict weight plus the weight of the
displacements of norm exactly `n`.  On the diagonal all three vanish. -/
theorem coe_radialKernel_closed_eq_strict_add_exact {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    (n : ℝ) (e : Sym2 (Fin d → ℤ)) :
    (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) =
      (radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) +
        (radialKernel N (fun s => if s = n then 1 else 0) e : ℝ) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp
    · have h1 : (radialKernel N (fun s => if s ≤ n then 1 else 0) s(x, y) : ℝ) =
          if N (Int.cast ∘ (x - y)) ≤ n then 1 else 0 := by
        rw [coe_radialKernel_of_ne (K := fun s => if s ≤ n then 1 else 0) hxy
          (by split <;> norm_num)]
      have h2 : (radialKernel N (fun s => if s < n then 1 else 0) s(x, y) : ℝ) =
          if N (Int.cast ∘ (x - y)) < n then 1 else 0 := by
        rw [coe_radialKernel_of_ne (K := fun s => if s < n then 1 else 0) hxy
          (by split <;> norm_num)]
      have h3 : (radialKernel N (fun s => if s = n then 1 else 0) s(x, y) : ℝ) =
          if N (Int.cast ∘ (x - y)) = n then 1 else 0 := by
        rw [coe_radialKernel_of_ne (K := fun s => if s = n then 1 else 0) hxy
          (by split <;> norm_num)]
      rw [h1, h2, h3]
      rcases lt_trichotomy (N (Int.cast ∘ (x - y))) n with h | h | h
      · rw [ite_eq_left h.le, ite_eq_left h, ite_eq_right (ne_of_lt h)]
        ring
      · rw [ite_eq_left h.le, ite_eq_right (not_lt.2 h.ge), ite_eq_left h]
        ring
      · rw [ite_eq_right (not_le.2 h), ite_eq_right (not_lt.2 h.le),
          ite_eq_right (ne_of_gt h)]
        ring

/-- Since the strict and exact weights are nonnegative, the strict weight alone is bounded by the
closed-ball weight. -/
theorem coe_radialKernel_strict_le_closed {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    (n : ℝ) (e : Sym2 (Fin d → ℤ)) :
    (radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) ≤
      (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) := by
  have hid := coe_radialKernel_closed_eq_strict_add_exact (N := N) n e
  have hex : (0 : ℝ) ≤ (radialKernel N (fun s => if s = n then 1 else 0) e : ℝ) :=
    NNReal.coe_nonneg _
  rw [hid]
  linarith

/-- `‖a * c * g‖ = a * |c| * |g|` for `a ≥ 0`, the form in which the weighted summands are
compared. -/
theorem norm_mul_abs_mul_abs {a c g : ℝ} (ha : 0 ≤ a) :
    ‖a * c * g‖ = a * |c| * |g| := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ha]

/-- Replacing the strict radial weight by the closed-ball weight can only increase the norm of a
weighted summand. -/
theorem norm_mul_radialKernel_strict_le_closed {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {n : ℝ} (e : Sym2 (Fin d → ℤ)) (c g : ℝ) :
    ‖(radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) * c * g‖ ≤
      ‖(radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) * c * g‖ := by
  have hstr : (0 : ℝ) ≤ (radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) :=
    NNReal.coe_nonneg _
  have hle := coe_radialKernel_strict_le_closed (N := N) n e
  rw [norm_mul_abs_mul_abs hstr, norm_mul_abs_mul_abs (hstr.trans hle)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle (abs_nonneg c)) (abs_nonneg g)

/-- **The right limit of the flux is the left limit plus the exact-norm shell.**  If the
closed-ball weighted series is absolutely summable at the corner, the closed-ball sum splits into
the strict sum plus the sum over the displacements of norm exactly `n`.  Combining this with the
one-sided limit theorems above gives `L₊ = L₋ + (exact-norm shell)`, so a non-vanishing shell is
exactly the obstruction to a two-sided limit of the flux at a lattice norm. -/
theorem tsum_radialKernel_closed_eq_strict_add_exact {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {n c : ℝ} (g : Sym2 (Fin d → ℤ) → ℝ)
    (hsum : Summable fun e =>
      ‖(radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) * c * g e‖) :
    (∑' e, (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) * c * g e) =
      (∑' e, (radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) * c * g e) +
        ∑' e, (radialKernel N (fun s => if s = n then 1 else 0) e : ℝ) * c * g e := by
  have hstrict : Summable fun e =>
      ‖(radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) * c * g e‖ :=
    Summable.of_nonneg_of_le (fun e => norm_nonneg _)
      (fun e => norm_mul_radialKernel_strict_le_closed e c (g e)) hsum
  have hexact : Summable fun e =>
      ‖(radialKernel N (fun s => if s = n then 1 else 0) e : ℝ) * c * g e‖ := by
    have hid := coe_radialKernel_closed_eq_strict_add_exact (N := N) n
    refine Summable.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => ?_) hsum
    have hstr : (0 : ℝ) ≤ (radialKernel N (fun s => if s < n then 1 else 0) e : ℝ) :=
      NNReal.coe_nonneg _
    have hcl : (0 : ℝ) ≤ (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) :=
      NNReal.coe_nonneg _
    have hle : (radialKernel N (fun s => if s = n then 1 else 0) e : ℝ) ≤
        (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) := by
      have hh := hid e
      linarith
    rw [norm_mul_abs_mul_abs (NNReal.coe_nonneg _), norm_mul_abs_mul_abs hcl]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (abs_nonneg c)) (abs_nonneg (g e))
  rw [← Summable.tsum_add hstrict.of_norm hexact.of_norm]
  refine tsum_congr fun e => ?_
  have hid := coe_radialKernel_closed_eq_strict_add_exact (N := N) n e
  rw [hid]
  ring

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-- **The root moment of the linear model equals one on the window.** For `r <= 1` the cut-off
kernel vanishes identically, so the configuration is empty almost surely and the cluster of `o`
is the singleton `{o}`. -/
theorem lintegral_pow_encard_cluster_linear_eq_one (n : ℕ) {r : ℝ} (hr : r ≤ 1)
    (o : Fin d → ℤ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ n
      ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
        (1 : ℝ≥0)))) = 1 := by
  rw [linear_intensityProfile_eq_zero_of_le_one hr]
  have hae : (fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) ^ n)
      =ᵐ[law (fun _ : Sym2 (Fin d → ℤ) => (0 : unitInterval))] fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [ae_eq_empty_zero_profile (d := d)] with ω hω
    rw [hω, cluster_empty, Set.encard_singleton]
    norm_num
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]


theorem hasDerivAt_integral_linear_cutoff_pow_small_tail (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (1 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (1 / 2 : ℝ) then
                (1 : ℝ) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) (1 / 2))
              (1 : ℝ≥0))))
      (1 / 2) := by
  let cw : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r e =>
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
        Real.exp (-(1 : ℝ) *
          (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => -s) r e : ℝ)))
  have hcw : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)), cw r e =
      (radialKernel (ModelNorm.ofNorm (Fin d → ℝ))
        (fun s => if s < r then 1 else 0) e : ℝ) *
        (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) r) *
          Real.exp (-(((1 : ℝ≥0) : ℝ)) *
            (cutoffKernel (ModelNorm.ofNorm (Fin d → ℝ)) (fun s => -s) r e : ℝ))) :=
    fun _ _ => rfl
  have hwzero : ∀ r ∈ Ioo (1 / 4 : ℝ) (3 / 4), ∀ e, cw r e = 0 := by
    intro r hr e
    exact linear_cw_eq_zero (d := d) (by linarith [hr.2]) e
  have hcorner : ∀ z : Fin d → ℤ,
      ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ z) ∉ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro z hz
    by_cases h : z = 0
    · subst h
      have h0 : ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ (0 : Fin d → ℤ)) = 0 := by simp
      rw [h0] at hz
      linarith [hz.1]
    · have h1 : (1 : ℝ) ≤ ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ z) := by
        simpa using one_le_normSeminorm_intCast (d := d) h
      linarith [hz.2]
  have hroot : ∀ r ∈ (Ioo (1 / 4 : ℝ) (3 / 4) ∪ {1} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) (ModelNorm.ofNorm (Fin d → ℝ))
          (fun s => -s) r) (1 : ℝ≥0)))) ≤ 1 := by
    intro r hr
    have hr1 : r ≤ 1 := by
      rcases hr with hr | hr
      · exact le_of_lt (by linarith [hr.2])
      · rw [mem_singleton_iff] at hr
        rw [hr]
    have h := lintegral_pow_encard_cluster_linear_eq_one (d := d) (p + 1) hr1
      (0 : Fin d → ℤ)
    simp only [ModelNorm.toSeminorm_ofNorm] at h ⊢
    rw [h]
  have htail : ∀ r₀ ∈ Ioo (1 / 4 : ℝ) (3 / 4), ∀ ε > 0, ∃ U ∈ 𝓝 r₀,
      ∃ F : Finset (Sym2 (Fin d → ℤ)), ∀ r ∈ U ∩ Ioo (1 / 4 : ℝ) (3 / 4),
        ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ, ‖cw r e.1 *
          ∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (d := d) (ModelNorm.ofNorm (Fin d → ℝ))
              (fun s => -s) r) (1 : ℝ≥0)))‖ ≤ ε := by
    intro r₀ _hr₀ ε hε
    refine ⟨univ, Filter.univ_mem, ∅, ?_⟩
    intro r hr
    have hzero : ∀ e : ↥((∅ : Finset (Sym2 (Fin d → ℤ))) : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 *
          ∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (d := d) (ModelNorm.ofNorm (Fin d → ℝ))
              (fun s => -s) r) (1 : ℝ≥0)))‖ = 0 := by
      intro e
      rw [hwzero r hr.2 e.1, zero_mul, norm_zero]
    rw [tsum_congr hzero, tsum_zero]
    exact hε.le
  have key := hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail
    (d := d) (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := fun s => -s) (K' := fun _ => -1)
    (R := 1) (u := (1 / 4 : ℝ)) (v := (3 / 4 : ℝ)) (r₀ := (1 / 2 : ℝ))
    (by
      intro a _ b _ hab
      change -b ≤ -a
      linarith)
    (by
      intro t _
      exact (hasDerivAt_id t).neg)
    (continuous_const : Continuous fun _ : ℝ => (-1 : ℝ)).continuousOn
    (1 : ℝ≥0) p hp (1 : ℝ≥0∞) ENNReal.one_ne_top cw hcw
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcorner hroot htail
  simpa using key


end PercLib.Models.LongRange

open PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-! ### Geometry: where far pivotal pairs can sit -/

/-- **A pair whose `K_o`-endpoint is in the window `Λ_L` and whose displacement is at most `v`
lies in `Λ_{L+v}`.** -/
theorem mem_window_of_le_norm_sub (N : Seminorm ℝ (Fin d → ℝ)) {x y : Fin d → ℤ} {L v : ℝ}
    (hv : 0 ≤ v) (hxv : N (Int.cast ∘ x) ≤ L) (hd : N (Int.cast ∘ (y - x)) ≤ v) :
    ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v := by
  intro z hz
  rw [Sym2.mem_iff] at hz
  rcases hz with hzx | hzy
  · rw [hzx]; linarith
  · rw [hzy]
    have hadd : (Int.cast ∘ (y - x) : Fin d → ℝ) + (Int.cast ∘ x) = Int.cast ∘ y := by
      funext i
      simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]
      push_cast
      ring
    calc N (Int.cast ∘ y)
        = N ((Int.cast ∘ (y - x) : Fin d → ℝ) + (Int.cast ∘ x)) := by rw [hadd]
      _ ≤ N (Int.cast ∘ (y - x)) + N (Int.cast ∘ x) := N.add_le' _ _
      _ ≤ v + L := by linarith
      _ = L + v := by ring

/-! ### Where the capped pivotal increment is supported -/

/-- **The capped pivotal increment vanishes if the pair misses the root cluster.** -/
theorem min_sub_min_eq_zero_of_forall_not_mem {V : Type*} {ω : Config V} {o : V} {e : Sym2 V}
    {pow : ℕ} (M : ℝ≥0∞) (he : ∀ x ∈ e, x ∉ cluster ω o) :
    min M (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow) -
        min M (((cluster ω o).encard : ℝ≥0∞) ^ pow) = 0 := by
  rw [cluster_insert_eq_of_forall_not_mem he, tsub_self]

/-- **The capped pivotal increment vanishes if both endpoints are in the root cluster.** -/
theorem min_sub_min_eq_zero_of_mem_mem {V : Type*} {ω : Config V} {o a b : V} {pow : ℕ}
    (M : ℝ≥0∞) (ha : o ∈ cluster ω a) (hb : o ∈ cluster ω b) :
    min M (((cluster (insert s(a, b) ω) o).encard : ℝ≥0∞) ^ pow) -
        min M (((cluster ω o).encard : ℝ≥0∞) ^ pow) = 0 := by
  rw [cluster_insert_eq_of_mem_of_mem ha hb, tsub_self]

/-- A truncated difference of two capped quantities is at most the cap. -/
theorem min_tsub_min_le (M X Y : ℝ≥0∞) : min M X - min M Y ≤ M :=
  (tsub_le_self).trans (min_le_left _ _)

/-- **The capped pivotal increment is at most the cap.** -/
theorem min_sub_min_le_cap {V : Type*} {ω : Config V} {o : V} {e : Sym2 V} {pow : ℕ}
    (M : ℝ≥0∞) :
    min M (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow) -
        min M (((cluster ω o).encard : ℝ≥0∞) ^ pow) ≤ M :=
  (tsub_le_self).trans (min_le_left _ _)

end PercLib.Percolation.Bond

/-! ### The far-tail count

The two model inputs below are used: (i) a pair with a weight and displacement at most `v` whose
`K_o`-endpoint lies in `Λ_L` is itself contained in `Λ_{L+v}`, so it carries no tail weight;
(ii) the capped pivotal increment is at most the cap and vanishes off the pivotal pairs.  The
rolling map `x ↦ (the pairs of displacement at most v through x)` has at most `#Λ_v` elements
per cluster point, which is why the far tail costs one factor of the far part of the root
cluster and nothing else.
-/

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-- An indicator of a `{0,1}`-valued proposition is at most one. -/
theorem ite_one_zero_le_one (p : Prop) [Decidable p] : (if p then (1 : ℝ≥0∞) else 0) ≤ 1 := by
  split <;> simp

/-- The complementary indicator is at most one. -/
theorem ite_zero_one_le_one (p : Prop) [Decidable p] : (if p then (0 : ℝ≥0∞) else 1) ≤ 1 := by
  split <;> simp

open Classical in
/-- **Tail weight kills the window part.** If a pair has a nonzero weight, displacement at most
`v`, and its `K_o`-endpoint lies in `Λ_L`, then it is contained in `Λ_{L+v}`, hence carries the
tail weight `0`. -/
theorem tail_weight_eq_zero_of_mem_window (N : Seminorm ℝ (Fin d → ℝ))
    (rad : Sym2 (Fin d → ℤ) → ℝ≥0∞) {v L : ℝ} (hv : 0 ≤ v)
    (hradB : ∀ x y, x ≠ y → rad s(x, y) ≠ 0 → N (Int.cast ∘ (y - x)) ≤ v)
    {ω : Config (Fin d → ℤ)} {o x y : Fin d → ℤ}
    (hx : x ∈ cluster ω o) (hy : y ∉ cluster ω o) (hxL : N (Int.cast ∘ x) ≤ L) :
    (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) = 0 := by
  classical
  by_cases hr : rad s(x, y) = 0
  · by_cases hc : (∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v)
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc, hr]
  · have hxy : x ≠ y := by rintro rfl; exact hy hx
    rw [ite_eq_left (mem_window_of_le_norm_sub N hv hxL (hradB x y hxy hr))]

open Classical in
/-- **The tail weight of a pair is bounded by the ball indicator.** -/
theorem tail_weight_le_ball (N : Seminorm ℝ (Fin d → ℝ))
    (rad : Sym2 (Fin d → ℤ) → ℝ≥0∞) {v C : ℝ}
    (hradC : ∀ e, rad e ≤ ENNReal.ofReal C)
    (hradB : ∀ x y, x ≠ y → rad s(x, y) ≠ 0 → N (Int.cast ∘ (y - x)) ≤ v)
    (hrad0 : ∀ x, rad s(x, x) = 0) (x y : Fin d → ℤ) :
    rad s(x, y) ≤ ENNReal.ofReal C * (if N (Int.cast ∘ (y - x)) ≤ v then (1 : ℝ≥0∞) else 0) := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [hrad0 x]
    simp
  · by_cases hr : rad s(x, y) = 0
    · rw [hr]; simp
    · rw [ite_eq_left (hradB x y hxy hr), mul_one]
      exact hradC _

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-- A product of two complementary indicators is at most one. -/
theorem ite_mul_ite_le_one (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ℝ≥0∞) else 0) * (if q then 0 else 1) ≤ 1 := by
  refine le_trans (mul_le_mul (ite_one_zero_le_one p) (ite_zero_one_le_one q)
    (by positivity) (by positivity)) ?_
  simp

/-- Dropping the two pivotal indicators from a capped summand. -/
theorem indicator_mul_indicator_mul_le (p q : Prop) [Decidable p] [Decidable q]
    (a b : ℝ≥0∞) : (if p then (1 : ℝ≥0∞) else 0) * a * (if q then 0 else 1) * b ≤ a * b := by
  calc (if p then (1 : ℝ≥0∞) else 0) * a * (if q then 0 else 1) * b
      = ((if p then (1 : ℝ≥0∞) else 0) * (if q then 0 else 1)) * (a * b) := by ring
    _ ≤ 1 * (a * b) := by
        refine mul_le_mul_of_nonneg_right (ite_mul_ite_le_one p q) (by positivity)
    _ = a * b := one_mul _

open Classical in
/-- **The far tail of the capped ordered pivotal sum.**

The capped Russo integrand of Lemma I.4.1 (ordered, with the closed ball of radius `v`) restricted
to the pairs outside the window `Λ_{L+v}` is bounded by the cap times one rolling factor `#Λ_v`
per *far* point of the root cluster.  No summability, moment or independence hypothesis is used:
the count is the pointwise one, since the tail pairs must leave the window through the root
cluster. -/
theorem far_tail_ordered_le (N : Seminorm ℝ (Fin d → ℝ))
    (ω : Config (Fin d → ℤ)) (o : Fin d → ℤ) (pow : ℕ) {Mcap C v L : ℝ}
    (hv : 0 ≤ v) (rad : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hradC : ∀ e, rad e ≤ ENNReal.ofReal C)
    (hradB : ∀ x y, x ≠ y → rad s(x, y) ≠ 0 → N (Int.cast ∘ (y - x)) ≤ v)
    (hrad0 : ∀ x, rad s(x, x) = 0) :
    (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) *
          (if y ∈ cluster ω o then 0 else 1) *
          (min (ENNReal.ofReal (Mcap ^ pow))
              ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
            min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow)))
      ≤ ENNReal.ofReal (Mcap ^ pow) * ENNReal.ofReal C *
          (∑' z : Fin d → ℤ, (if N (Int.cast ∘ z) ≤ v then (1 : ℝ≥0∞) else 0)) *
          (∑' x : Fin d → ℤ,
            (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0)) := by
  have hterm : ∀ x y : Fin d → ℤ,
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) *
          (if y ∈ cluster ω o then 0 else 1) *
          (min (ENNReal.ofReal (Mcap ^ pow))
              ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
            min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow))
      ≤ (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0) *
          (ENNReal.ofReal (Mcap ^ pow) * (ENNReal.ofReal C *
            (if N (Int.cast ∘ (y - x)) ≤ v then (1 : ℝ≥0∞) else 0))) := by
    intro x y
    by_cases hx : x ∈ cluster ω o
    · by_cases hxL : N (Int.cast ∘ x) ≤ L
      · have hzero : (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) *
            (if y ∈ cluster ω o then 0 else 1) *
            (min (ENNReal.ofReal (Mcap ^ pow))
                ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
              min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow)) = 0 := by
          by_cases hy : y ∈ cluster ω o
          · simp [hy]
          · rw [tail_weight_eq_zero_of_mem_window N rad hv hradB hx hy hxL]
            simp
        rw [hzero, ite_eq_right (by tauto : ¬ (x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L)))]
        simp
      · have hidx : (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0) = 1 :=
          ite_eq_left ⟨hx, hxL⟩
        rw [hidx, one_mul]
        have hstep : (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
              (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) *
              (if y ∈ cluster ω o then 0 else 1) *
              (min (ENNReal.ofReal (Mcap ^ pow))
                  ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
                min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow))
            ≤ rad s(x, y) * ENNReal.ofReal (Mcap ^ pow) := by
          have h1 := indicator_mul_indicator_mul_le (x ∈ cluster ω o) (y ∈ cluster ω o)
            (rad s(x, y))
            (min (ENNReal.ofReal (Mcap ^ pow))
                ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
              min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow))
          have h2 : (min (ENNReal.ofReal (Mcap ^ pow))
                ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
              min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow))
              ≤ ENNReal.ofReal (Mcap ^ pow) := min_tsub_min_le _ _ _
          have h3 : (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞)
              else rad s(x, y)) ≤ rad s(x, y) := by
            split
            · exact bot_le
            · exact le_rfl
          calc (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
                (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) *
                (if y ∈ cluster ω o then 0 else 1) *
                (min (ENNReal.ofReal (Mcap ^ pow))
                    ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
                  min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow))
              ≤ (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * rad s(x, y) *
                  (if y ∈ cluster ω o then 0 else 1) * ENNReal.ofReal (Mcap ^ pow) := by
                gcongr
            _ ≤ rad s(x, y) * ENNReal.ofReal (Mcap ^ pow) :=
                indicator_mul_indicator_mul_le _ _ _ _
        refine hstep.trans ?_
        have hball := tail_weight_le_ball N rad hradC hradB hrad0 x y
        calc rad s(x, y) * ENNReal.ofReal (Mcap ^ pow)
            ≤ (ENNReal.ofReal C * (if N (Int.cast ∘ (y - x)) ≤ v then (1 : ℝ≥0∞) else 0)) *
                ENNReal.ofReal (Mcap ^ pow) := by
              exact mul_le_mul_of_nonneg_right hball (by positivity)
          _ = ENNReal.ofReal (Mcap ^ pow) * (ENNReal.ofReal C *
                (if N (Int.cast ∘ (y - x)) ≤ v then (1 : ℝ≥0∞) else 0)) := by ring
    · rw [ite_eq_right hx, zero_mul, zero_mul,
        ite_eq_right (by tauto : ¬ (x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L)))]
      simp
  calc (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + v then (0 : ℝ≥0∞) else rad s(x, y)) *
          (if y ∈ cluster ω o then 0 else 1) *
          (min (ENNReal.ofReal (Mcap ^ pow))
              ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
            min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow)))
      ≤ ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0) *
            (ENNReal.ofReal (Mcap ^ pow) * (ENNReal.ofReal C *
              (if N (Int.cast ∘ (y - x)) ≤ v then (1 : ℝ≥0∞) else 0))) :=
        ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y => hterm x y
    _ = ∑' x : Fin d → ℤ,
          (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0) *
            ((ENNReal.ofReal (Mcap ^ pow) * ENNReal.ofReal C) *
              (∑' z : Fin d → ℤ, (if N (Int.cast ∘ z) ≤ v then (1 : ℝ≥0∞) else 0))) := by
        refine tsum_congr fun x => ?_
        have hreindex : (∑' y : Fin d → ℤ,
            (if N (Int.cast ∘ (y - x)) ≤ v then (1 : ℝ≥0∞) else 0))
            = ∑' z : Fin d → ℤ, (if N (Int.cast ∘ z) ≤ v then (1 : ℝ≥0∞) else 0) := by
          simp only [sub_eq_add_neg]
          exact (Equiv.addRight (-x)).tsum_eq
            (fun z => (if N (Int.cast ∘ z) ≤ v then (1 : ℝ≥0∞) else 0))
        simp only [ENNReal.tsum_mul_left, hreindex]
        ring
    _ = ENNReal.ofReal (Mcap ^ pow) * ENNReal.ofReal C *
          (∑' z : Fin d → ℤ, (if N (Int.cast ∘ z) ≤ v then (1 : ℝ≥0∞) else 0)) *
          (∑' x : Fin d → ℤ,
            (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0)) := by
        simp only [ENNReal.tsum_mul_right]
        ring

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {d : ℕ}

open Classical in
/-- **Non-vacuity on the actual cutoff weight.** The radial indicator of the cutoff derivative
satisfies the three weight hypotheses of `far_tail_ordered_le` with `C = 1` and `v = r`: it is
bounded by one, vanishes on the diagonal, and vanishes at every pair whose displacement is at
least `r`. -/
theorem radial_indicator_weight_hypotheses (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ) :
    (∀ e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal 1) ∧
      (∀ x y : Fin d → ℤ, x ≠ y →
        ((radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0) : ℝ≥0∞) ≠ 0 →
        N (Int.cast ∘ (y - x)) ≤ r) ∧
      (∀ x : Fin d → ℤ,
        ((radialKernel N (fun s => if s < r then 1 else 0) s(x, x) : ℝ≥0) : ℝ≥0∞) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have hreal : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≤ 1 := by
      rcases radialKernel_indicator_eq_zero_or_one N r e with h | h
      · simp [h]
      · simp [h]
    have hnn : (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) ≤ 1 := by
      exact_mod_cast hreal
    calc ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞)
        ≤ ((1 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hnn
      _ = ENNReal.ofReal 1 := by simp
  · intro x y hxy hne
    by_contra hcon
    have hnot : ¬ N (Int.cast ∘ (y - x)) < r := not_lt.2 (le_of_lt (not_le.1 hcon))
    have h0 : (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0) = 0 := by
      apply NNReal.coe_injective
      rw [Sym2.eq_swap,
        radialKernel_indicator_eq_zero_of_not_lt (N := N) (x := y) (y := x) hnot]
      simp
    exact hne (by rw [h0]; simp)
  · intro x
    rw [radialKernel_diag]
    simp

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {d : ℕ}

open Classical in
/-- **The far tail of the actual cut-off Russo sum.** Specialisation of `far_tail_ordered_le` to
the radial indicator of the cut-off derivative: for `0 ≤ r` and `0 ≤ Mcap`, the pairs outside
`Λ_{L+r}` contribute at most `Mcap^pow · #Λ_r · |K_o \ Λ_L|` to the capped ordered pivotal sum.
This is a statement about the actual bond model on `ℤ^d`, uniform in everything but the root
configuration. -/
theorem far_tail_cutoff_le (N : Seminorm ℝ (Fin d → ℝ)) {r : ℝ} (hr : 0 ≤ r)
    (ω : Config (Fin d → ℤ)) (o : Fin d → ℤ) (pow : ℕ) (Mcap : ℝ) (L : ℝ) :
    (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if ∀ z ∈ s(x, y), N (Int.cast ∘ z) ≤ L + r then (0 : ℝ≥0∞)
            else ((radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0) : ℝ≥0∞)) *
          (if y ∈ cluster ω o then 0 else 1) *
          (min (ENNReal.ofReal (Mcap ^ pow))
              ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ pow) -
            min (ENNReal.ofReal (Mcap ^ pow)) (((cluster ω o).encard : ℝ≥0∞) ^ pow)))
      ≤ ENNReal.ofReal (Mcap ^ pow) *
          (∑' z : Fin d → ℤ, (if N (Int.cast ∘ z) ≤ r then (1 : ℝ≥0∞) else 0)) *
          (∑' x : Fin d → ℤ,
            (if x ∈ cluster ω o ∧ ¬ (N (Int.cast ∘ x) ≤ L) then (1 : ℝ≥0∞) else 0)) := by
  obtain ⟨hC, hB, h0⟩ := radial_indicator_weight_hypotheses N r
  have hmain := far_tail_ordered_le N ω o pow (Mcap := Mcap) (C := 1) (v := r) (L := L) hr
    (fun e => ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0) : ℝ≥0∞))
    hC hB h0
  refine hmain.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_one, mul_one]

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

/-- The cut-off kernel of the linear profile `s ↦ -s` at a unit displacement, for every scale
`r > 1`: the profile difference `-1 - (-r)` is positive, so the truncation does nothing. -/
theorem coe_cutoffKernel_linear_unit {x y : Fin 1 → ℤ} {r : ℝ} (hr : 1 < r) (hxy : x ≠ y)
    (h : ((x - y) 0).natAbs = 1) :
    ((cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) s(x, y) : ℝ) = r - 1 := by
  rw [cutoffKernel_def, radialKernel_of_ne hxy, normSeminorm_fin_one_intCast, h]
  rw [cutoffProfile_of_le (K := fun s => -s) (r := r) (s := ((1 : ℕ) : ℝ))
    (by exact_mod_cast hr.le)]
  rw [Real.coe_toNNReal _ (by push_cast; linarith)]
  push_cast
  ring

/-- The open probability of a unit-displacement pair at every scale `r > 1`:
`1 - e^{-β (r-1)}`. -/
theorem coe_intensityProfile_linear_unit {x y : Fin 1 → ℤ} {r : ℝ} (hr : 1 < r) (hxy : x ≠ y)
    (h : ((x - y) 0).natAbs = 1) (β : ℝ≥0) :
    ((intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β) s(x, y) : ℝ)
      = 1 - Real.exp (-(β : ℝ) * (r - 1)) := by
  simp only [intensityProfile, coe_cutoffKernel_linear_unit hr hxy h]

/-- At a genuinely interacting scale `r > 1` and a nonzero intensity, a unit bond is open with
probability strictly between `0` and `1`: neither the all-closed nor the all-open event is
forced. -/
theorem bond_prob_linear_unit_pos {x y : Fin 1 → ℤ} {r : ℝ} (hr : 1 < r) (hxy : x ≠ y)
    (h : ((x - y) 0).natAbs = 1) {β : ℝ≥0} (hβ : (β : ℝ) ≠ 0) :
    0 < ((intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
        s(x, y) : ℝ) ∧
      ((intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
        s(x, y) : ℝ) < 1 := by
  have hβpos : (0 : ℝ) < (β : ℝ) := lt_of_le_of_ne β.coe_nonneg (Ne.symm hβ)
  have harg : 0 < (β : ℝ) * (r - 1) := mul_pos hβpos (by linarith)
  rw [coe_intensityProfile_linear_unit hr hxy h β]
  constructor
  · have hlt : Real.exp (-(β : ℝ) * (r - 1)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  · have hpos : 0 < Real.exp (-(β : ℝ) * (r - 1)) := Real.exp_pos _
    linarith

/-- The exact marginal of a single unit bond under the interacting law. -/
theorem law_open_linear_unit {x y : Fin 1 → ℤ} {r : ℝ} (hr : 1 < r)
    (hxy : x ≠ y) (h : ((x - y) 0).natAbs = 1) (β : ℝ≥0) :
    law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
        {ω | s(x, y) ∈ ω}
      = ENNReal.ofReal (1 - Real.exp (-(β : ℝ) * (r - 1))) := by
  have hset : {ω : Config (Fin 1 → ℤ) | s(x, y) ∈ ω} =
      {ω | (({s(x, y)} : Finset (Sym2 (Fin 1 → ℤ))) : Set (Sym2 (Fin 1 → ℤ))) ⊆ ω} := by
    ext ω
    simp
  rw [law, hset, prodBernoulli_subset, Finset.prod_singleton]
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
    coe_intensityProfile_linear_unit hr hxy h β]

/-- **The two-point function of the interacting window is strictly positive.** -/
theorem tau_linear_unit_pos {r : ℝ} (hr : 1 < r) {β : ℝ≥0} (hβ : (β : ℝ) ≠ 0) :
    0 < tau (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
      (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ)) := by
  have hxy : (0 : Fin 1 → ℤ) ≠ (fun _ => (1 : ℤ)) := by
    intro hc
    have h0 := congrFun hc 0
    simp at h0
  have hnat : (((0 : Fin 1 → ℤ) - (fun _ => (1 : ℤ)) : Fin 1 → ℤ) 0).natAbs = 1 := by
    have hz : ((0 : Fin 1 → ℤ) - (fun _ => (1 : ℤ)) : Fin 1 → ℤ) 0 = -1 := by
      simp
    rw [hz]
    norm_num
  have hsub : {ω : Config (Fin 1 → ℤ) | s((0 : Fin 1 → ℤ), (fun _ => (1 : ℤ))) ∈ ω} ⊆
      conn (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ)) :=
    fun ω hω => mem_conn_of_mem hxy hω
  have hpos := (bond_prob_linear_unit_pos hr hxy hnat hβ).1
  rw [coe_intensityProfile_linear_unit hr hxy hnat β] at hpos
  have hne : law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
      {ω | s((0 : Fin 1 → ℤ), (fun _ => (1 : ℤ))) ∈ ω} ≠ 0 := by
    rw [law_open_linear_unit hr hxy hnat]
    exact (ENNReal.ofReal_pos.2 hpos).ne'
  exact lt_of_lt_of_le (zero_lt_iff.2 hne) (measure_mono hsub)

/-- **The susceptibility of the interacting window is strictly bigger than one.** The cluster of
the origin contains the second endpoint whenever the unit bond is open, so
`|K| ≥ 1 + 1{0 ↔ 1}` pointwise and `χ ≥ 1 + τ(0,1) > 1`. -/
theorem one_lt_chi_linear_unit {r : ℝ} (hr : 1 < r) {β : ℝ≥0} (hβ : (β : ℝ) ≠ 0) :
    1 < chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
      (0 : Fin 1 → ℤ) := by
  have hxy : (0 : Fin 1 → ℤ) ≠ (fun _ => (1 : ℤ)) := by
    intro hc
    have h0 := congrFun hc 0
    simp at h0
  have htau := tau_linear_unit_pos hr hβ
  have hle : ∀ ω : Config (Fin 1 → ℤ),
      ((1 : ℝ≥0∞) + (conn (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ))).indicator (fun _ => 1) ω) ≤
        ((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) := by
    intro ω
    by_cases hc : ω ∈ conn (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ))
    · rw [Set.indicator_of_mem hc]
      have hsub : (({((0 : Fin 1 → ℤ)), (fun _ => (1 : ℤ))} : Set (Fin 1 → ℤ))) ⊆
          cluster ω (0 : Fin 1 → ℤ) := by
        intro v hv
        rcases Set.mem_insert_iff.1 hv with hv0 | hv1
        · rw [hv0]; exact mem_cluster_self ω 0
        · rw [Set.mem_singleton_iff.1 hv1]
          exact (mem_cluster_iff ω (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ))).2 hc
      have h2 : (2 : ℝ≥0∞) ≤ ((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) := by
        have hmono := Set.encard_mono hsub
        rw [Set.encard_pair hxy] at hmono
        exact_mod_cast hmono
      rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
      exact h2
    · rw [Set.indicator_of_notMem hc]
      simp only [add_zero]
      exact_mod_cast one_le_encard_cluster ω (0 : Fin 1 → ℤ)
  have hmono : (∫⁻ ω, ((1 : ℝ≥0∞) +
        (conn (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ))).indicator (fun _ => 1) ω)
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (fun s => -s) r) β)))
      ≤ chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
        (0 : Fin 1 → ℤ) :=
    lintegral_mono hle
  have heq : (∫⁻ ω, ((1 : ℝ≥0∞) +
        (conn (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ))).indicator (fun _ => 1) ω)
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (fun s => -s) r) β)))
      = 1 + tau (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (fun s => -s) r) β) (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ)) := by
    rw [lintegral_add_left measurable_const]
    congr 1
    · rw [lintegral_const, measure_univ, mul_one]
    · rw [lintegral_indicator (measurableSet_conn _ _), lintegral_const,
        Measure.restrict_apply_univ, one_mul]
      rfl
  rw [heq] at hmono
  exact lt_of_lt_of_le (ENNReal.lt_add_right (by simp) htau.ne') hmono

/-! ### The interacting window is nearest-neighbour percolation -/

/-- The linear cut-off kernel vanishes at every displacement of norm at least two, for every
scale `r < 2`. -/
theorem coe_cutoffKernel_linear_eq_zero_of_two_le {x y : Fin 1 → ℤ} {r : ℝ} (hr : r < 2)
    (hxy : x ≠ y) (h : 2 ≤ ((x - y) 0).natAbs) :
    ((cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) s(x, y) : ℝ) = 0 := by
  rw [cutoffKernel_def, radialKernel_of_ne hxy, normSeminorm_fin_one_intCast]
  have hlt : r < (((x - y) 0).natAbs : ℝ) := by
    have h2 : (2 : ℝ) ≤ (((x - y) 0).natAbs : ℝ) := by exact_mod_cast h
    linarith
  rw [cutoffProfile_of_lt hlt, Real.toNNReal_zero]
  simp

/-- The open probability at a displacement of norm at least two vanishes at every scale `r < 2`. -/
theorem coe_intensityProfile_linear_eq_zero_of_two_le {x y : Fin 1 → ℤ} {r : ℝ} (hr : r < 2)
    (hxy : x ≠ y) (h : 2 ≤ ((x - y) 0).natAbs) (β : ℝ≥0) :
    ((intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
      s(x, y) : ℝ) = 0 := by
  simp only [intensityProfile, coe_cutoffKernel_linear_eq_zero_of_two_le hr hxy h]
  simp

/-- **Almost surely every open bond of the interacting window has unit displacement**: for
`1 < r < 2` the law is nearest-neighbour bond percolation with open probability
`1 - exp (-(β (r-1)))`, and no longer bond is ever open. -/
theorem ae_open_pair_natAbs_one {r : ℝ} (_hr : 1 < r) (hr2 : r < 2) (β : ℝ≥0) :
    ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)),
      ∀ x y : Fin 1 → ℤ, s(x, y) ∈ ω → x ≠ y → ((x - y) 0).natAbs = 1 := by
  filter_upwards [ae_config_subset_positive
    (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)]
    with ω hω x y hmem hxy
  have hne0 : (x - y) 0 ≠ 0 := by
    intro hc
    apply hxy
    rw [fun_fin_one_eq_iff]
    simp only [Pi.sub_apply] at hc
    linarith
  by_contra hcon
  have h2 : 2 ≤ ((x - y) 0).natAbs := by omega
  have hzero : ((intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
      s(x, y) : ℝ) = 0 := coe_intensityProfile_linear_eq_zero_of_two_le hr2 hxy h2 β
  have hpos : (0 : unitInterval) <
      (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β) s(x, y) :=
    hω hmem
  have hzero' : (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r) β)
      s(x, y) = 0 := by
    apply Subtype.ext
    simpa using hzero
  rw [hzero'] at hpos
  exact absurd hpos (not_lt.2 (le_refl _))

/-- **The derivative weight of the interacting window is supported on unit bonds.** For `r < 2`
the strict radial indicator `1{N (x-y) < r}` kills every pair of displacement norm at least two,
whatever the cut-off rate and the exponential factor. -/
theorem coe_cutoff_weight_eq_zero_of_two_le {x y : Fin 1 → ℤ} {r : ℝ} (hr : r < 2)
    (h : 2 ≤ ((x - y) 0).natAbs) {K' : ℝ → ℝ} {β : ℝ} :
    (radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => if s < r then 1 else 0) s(x, y) : ℝ) *
      (β * -K' r * Real.exp (-β * ((cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (fun s => -s) r) s(x, y) : ℝ))) = 0 := by
  have hlt : ¬ (normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ (x - y)) < r) := by
    rw [normSeminorm_fin_one_intCast]
    have h2 : (2 : ℝ) ≤ (((x - y) 0).natAbs : ℝ) := by exact_mod_cast h
    linarith
  rw [radialKernel_indicator_eq_zero_of_not_lt hlt]
  simp

/-! ### Exact finite support of the Lemma I.4.1 right-hand side at `r₀ = 3/2` -/

/-- Displacements of sup norm at most `3 / 2` in the one-dimensional lattice are `0`, `1` and
`-1`: no integer displacement has norm strictly between one and two. -/
theorem fin_one_intCast_le_three_halves {y : Fin 1 → ℤ}
    (h : normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ)) :
    y = (0 : Fin 1 → ℤ) ∨ y = (fun _ => (1 : ℤ)) ∨ y = (fun _ => (-1 : ℤ)) := by
  rw [normSeminorm_fin_one_intCast] at h
  have h1 : (y 0).natAbs ≤ 1 := by
    by_contra hc
    have h2 : 2 ≤ (y 0).natAbs := by omega
    have h3 : (2 : ℝ) ≤ ((y 0).natAbs : ℝ) := by exact_mod_cast h2
    linarith
  have hy : y 0 = -1 ∨ y 0 = 0 ∨ y 0 = 1 := by omega
  rcases hy with h' | h' | h'
  · exact Or.inr (Or.inr ((fun_fin_one_eq_iff y (fun _ => (-1 : ℤ))).2 (by simpa using h')))
  · exact Or.inl ((fun_fin_one_eq_iff y (0 : Fin 1 → ℤ)).2 (by simpa using h'))
  · exact Or.inr (Or.inl ((fun_fin_one_eq_iff y (fun _ => (1 : ℤ))).2 (by simpa using h')))

/-- At `r₀ = 3 / 2` the inner vertex sum of the Lemma I.4.1 right-hand side is supported on the
three neighbours `0, 1, -1` of the origin, and the `y = 0` term vanishes because the origin is
always connected to itself.  Hence the interacting-window right-hand side is the two-term
nearest-neighbour expression displayed below: only the bonds `{0,1}` and `{0,-1}` contribute. -/
theorem tsum_i41_neighbour_support (p ℓ : ℕ) (ω : Config (Fin 1 → ℤ)) :
    (∑' y : Fin 1 → ℤ,
      (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ) else 0) *
        (conn (0 : Fin 1 → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
        (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
      = (conn (0 : Fin 1 → ℤ) (fun _ => (1 : ℤ)))ᶜ.indicator (fun _ => (1 : ℝ)) ω *
          (((cluster ω (fun _ => (1 : ℤ))).encard : ℝ≥0∞).toReal) ^ (p - ℓ) +
        (conn (0 : Fin 1 → ℤ) (fun _ => (-1 : ℤ)))ᶜ.indicator (fun _ => (1 : ℝ)) ω *
          (((cluster ω (fun _ => (-1 : ℤ))).encard : ℝ≥0∞).toReal) ^ (p - ℓ) := by
  classical
  have hsupp : ∀ y : Fin 1 → ℤ, y ≠ (0 : Fin 1 → ℤ) → y ≠ (fun _ => (1 : ℤ)) →
      y ≠ (fun _ => (-1 : ℤ)) →
      (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ) else 0) = 0 := by
    intro y h0 h1 hm1
    split_ifs with hle
    · rcases fin_one_intCast_le_three_halves hle with h | h | h
      · exact absurd h h0
      · exact absurd h h1
      · exact absurd h hm1
    · rfl
  have hzero : (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ (0 : Fin 1 → ℤ)) ≤ (3 / 2 : ℝ)
      then (1 : ℝ) else 0) *
        (conn (0 : Fin 1 → ℤ) (0 : Fin 1 → ℤ))ᶜ.indicator (fun _ => (1 : ℝ)) ω *
        (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (p - ℓ) = 0 := by
    rw [conn_self]
    simp
  have h01 : (0 : Fin 1 → ℤ) ≠ ((fun _ => (1 : ℤ)) : Fin 1 → ℤ) := by
    intro hc
    have h := congrFun hc 0
    simp at h
  have h0m : (0 : Fin 1 → ℤ) ≠ ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ) := by
    intro hc
    have h := congrFun hc 0
    simp at h
  have h1m : ((fun _ => (1 : ℤ)) : Fin 1 → ℤ) ≠ ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ) := by
    intro hc
    have h := congrFun hc 0
    simp at h
  rw [tsum_eq_sum (s := ({(0 : Fin 1 → ℤ), (fun _ => (1 : ℤ)), (fun _ => (-1 : ℤ))} :
    Finset (Fin 1 → ℤ))) (fun y hy => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      rw [hsupp y hy.1 hy.2.1 hy.2.2]
      simp)]
  have hm1 : (0 : Fin 1 → ℤ) ∉ ({(fun _ => (1 : ℤ)), (fun _ => (-1 : ℤ))} :
      Finset (Fin 1 → ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h01, h0m⟩
  have hm2 : (fun _ => (1 : ℤ)) ∉ ({(fun _ => (-1 : ℤ))} : Finset (Fin 1 → ℤ)) := by
    simp only [Finset.mem_singleton]
    exact h1m
  have hone : (if normSeminorm ℝ (Fin 1 → ℝ)
      (Int.cast ∘ ((fun _ => (1 : ℤ)) : Fin 1 → ℤ)) ≤ (3 / 2 : ℝ) then (1 : ℝ) else 0) = 1 := by
    rw [normSeminorm_fin_one_intCast]
    norm_num
  have honem : (if normSeminorm ℝ (Fin 1 → ℝ)
      (Int.cast ∘ ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ)) ≤ (3 / 2 : ℝ) then (1 : ℝ) else 0) = 1 := by
    rw [normSeminorm_fin_one_intCast]
    norm_num
  rw [Finset.sum_insert hm1, Finset.sum_insert hm2, Finset.sum_singleton, hzero, zero_add,
    hone, honem, one_mul, one_mul]

/-! ### The interacting window as a genuine instance of the cut-off derivative interface -/

/-- **The interacting window at `r₀ = 3 / 2` is a genuine instance of the Lemma I.4.1 cut-off
derivative interface.** For `d = 1`, `K s = -s`, `β = 1`, window `u = 5/4`, `v = R = 8/5` and
`r₀ = 3/2` (which is corner-free), every hypothesis of
`hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail` is discharged except
the two genuinely model-dependent inputs: the uniform root `(p+1)`-moment `M` and the local
small-tail estimate `htail`.  Both are stated here for the actual nearest-neighbour window, so
the remaining gap is visible in one place. -/
theorem hasDerivAt_linear_three_halves_of_moment_of_tail
    (p : ℕ) (hp : 1 ≤ p) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Set.Ioo (5 / 4 : ℝ) (8 / 5) ∪ {(8 / 5 : ℝ)} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0)))) ≤ M)
    (htail : ∀ r₀ ∈ Set.Ioo (5 / 4 : ℝ) (8 / 5), ∀ ε > 0, ∃ U ∈ 𝓝 r₀,
      ∃ F : Finset (Sym2 (Fin 1 → ℤ)), ∀ r ∈ U ∩ Set.Ioo (5 / 4 : ℝ) (8 / 5),
        ∑' e : ↥(F : Set (Sym2 (Fin 1 → ℤ)))ᶜ,
          ‖((radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => if s < r then 1 else 0)
              e.1 : ℝ) *
            ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
              Real.exp (-(1 : ℝ) *
                (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r e.1 : ℝ)))) *
           ∫ ω, (((cluster (insert e.1 ω) (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p -
             ((cluster (ω \ {e.1}) (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p).toReal
             ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
               (fun s => -s) r) (1 : ℝ≥0)))‖ ≤ ε) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (3 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin 1 → ℤ,
              (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ) else 0) *
              (conn (0 : Fin 1 → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2))
              (1 : ℝ≥0))))
      (3 / 2) := by
  let cw : ℝ → Sym2 (Fin 1 → ℤ) → ℝ := fun r e =>
    (radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
        Real.exp (-(1 : ℝ) *
          (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r e : ℝ)))
  have hcw : ∀ (r : ℝ) (e : Sym2 (Fin 1 → ℤ)), cw r e =
      (radialKernel (ModelNorm.ofNorm (Fin 1 → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) r) *
          Real.exp (-(((1 : ℝ≥0) : ℝ)) *
            (cutoffKernel (ModelNorm.ofNorm (Fin 1 → ℝ)) (fun s => -s) r e : ℝ))) :=
    fun _ _ => rfl
  have hcorner : ∀ z : Fin 1 → ℤ,
      ModelNorm.ofNorm (Fin 1 → ℝ) (Int.cast ∘ z) ∉ Set.Ioo (5 / 4 : ℝ) (8 / 5) := by
    intro z hz
    have hsub : Set.Ioo (5 / 4 : ℝ) (8 / 5) ⊆ Set.Ioo (1 : ℝ) 2 := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact corner_free_at_three_halves z (hsub hz)
  have hroot' : ∀ r ∈ (Set.Ioo (5 / 4 : ℝ) (8 / 5) ∪ {(8 / 5 : ℝ)} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (ModelNorm.ofNorm (Fin 1 → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0)))) ≤ M := by
    intro r hr
    simpa only [ModelNorm.toSeminorm_ofNorm] using hroot r hr
  have key := hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail
    (d := 1) (N := ModelNorm.ofNorm (Fin 1 → ℝ)) (K := fun s => -s) (K' := fun _ => -1)
    (R := (8 / 5 : ℝ)) (u := (5 / 4 : ℝ)) (v := (8 / 5 : ℝ)) (r₀ := (3 / 2 : ℝ))
    (by intro a _ b _ hab; change -b ≤ -a; linarith)
    (by intro t _; exact (hasDerivAt_id t).neg)
    (continuous_const : Continuous fun _ : ℝ => (-1 : ℝ)).continuousOn
    (1 : ℝ≥0) p hp M hM cw hcw (by norm_num) (by norm_num) (by norm_num) (le_refl _)
    hcorner hroot'
    (by
      intro r₀ hr₀ ε hε
      obtain ⟨U, hU, F, hF⟩ := htail r₀ hr₀ ε hε
      exact ⟨U, hU, F, fun r hr => hF r hr⟩)
  have hcoe : ∀ x : Fin 1 → ℝ,
      (ModelNorm.ofNorm (Fin 1 → ℝ)) x = (normSeminorm ℝ (Fin 1 → ℝ)) x := by
    intro x
    change (ModelNorm.ofNorm (Fin 1 → ℝ)).toSeminorm x = _
    rw [ModelNorm.toSeminorm_ofNorm]
  simpa only [ModelNorm.toSeminorm_ofNorm, hcoe] using key

/-- **The Lemma I.4.1 integrand at `r₀ = 3/2` reduces to its two nearest-neighbour terms**:
the vertex sum inside the flux integral is exactly the sum over `y = 1` and `y = -1`. -/
theorem integral_linear_three_halves_i41_integrand (p ℓ : ℕ) :
    (∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        (∑' y : Fin 1 → ℤ,
          (if normSeminorm ℝ (Fin 1 → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ) else 0) *
          (conn (0 : Fin 1 → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
          (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s)
          (3 / 2)) (1 : ℝ≥0))))
      = ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        ((conn (0 : Fin 1 → ℤ) ((fun _ => (1 : ℤ)) : Fin 1 → ℤ))ᶜ.indicator
            (fun _ => (1 : ℝ)) ω *
          (((cluster ω ((fun _ => (1 : ℤ)) : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (p - ℓ) +
        (conn (0 : Fin 1 → ℤ) ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ))ᶜ.indicator
            (fun _ => (1 : ℝ)) ω *
          (((cluster ω ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s)
          (3 / 2)) (1 : ℝ≥0))) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [tsum_i41_neighbour_support p ℓ ω]

/-- **The same interacting derivative with the right-hand side reduced to its two
nearest-neighbour terms.** This is the shape the sharpness input has to match: only the bonds
`{0,1}` and `{0,-1}` appear, with the two-point factors `1{0 not↔ ±1}`. -/
theorem hasDerivAt_linear_three_halves_neighbours
    (p : ℕ) (hp : 1 ≤ p) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Set.Ioo (5 / 4 : ℝ) (8 / 5) ∪ {(8 / 5 : ℝ)} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0)))) ≤ M)
    (htail : ∀ r₀ ∈ Set.Ioo (5 / 4 : ℝ) (8 / 5), ∀ ε > 0, ∃ U ∈ 𝓝 r₀,
      ∃ F : Finset (Sym2 (Fin 1 → ℤ)), ∀ r ∈ U ∩ Set.Ioo (5 / 4 : ℝ) (8 / 5),
        ∑' e : ↥(F : Set (Sym2 (Fin 1 → ℤ)))ᶜ,
          ‖((radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => if s < r then 1 else 0)
              e.1 : ℝ) *
            ((1 : ℝ) * -((fun _ : ℝ => -1) r) *
              Real.exp (-(1 : ℝ) *
                (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r e.1 : ℝ)))) *
           ∫ ω, (((cluster (insert e.1 ω) (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p -
             ((cluster (ω \ {e.1}) (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p).toReal
             ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
               (fun s => -s) r) (1 : ℝ≥0)))‖ ≤ ε) :
    HasDerivAt (fun r : ℝ => ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) r)
          (1 : ℝ≥0))))
      (((1 : ℝ≥0) : ℝ) * -((fun _ : ℝ => -1) (3 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            ((conn (0 : Fin 1 → ℤ) ((fun _ => (1 : ℤ)) : Fin 1 → ℤ))ᶜ.indicator
                (fun _ => (1 : ℝ)) ω *
              (((cluster ω ((fun _ => (1 : ℤ)) : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (p - ℓ) +
            (conn (0 : Fin 1 → ℤ) ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ))ᶜ.indicator
                (fun _ => (1 : ℝ)) ω *
              (((cluster ω ((fun _ => (-1 : ℤ)) : Fin 1 → ℤ)).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile
              (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s => -s) (3 / 2))
              (1 : ℝ≥0))))
      (3 / 2) := by
  refine (hasDerivAt_linear_three_halves_of_moment_of_tail
    p hp M hM hroot htail).congr_deriv ?_
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => by
    rw [integral_linear_three_halves_i41_integrand p ℓ]

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The bounded cut-off radius makes every vertex fibre finite

The cut-off weight of a pair `s(x, y)` vanishes unless `N (x - y) < r`.  A `ModelNorm` ball is
bounded, hence it meets `ℤ^d` in finitely many points, so for a fixed first endpoint `x` only
finitely many second endpoints carry weight.  This is the geometric input that a single-pair
estimate cannot supply. -/

/-- **Finitely many short difference vectors.**  `diagram_finite_short_vectors` excludes `0`; the
fibre count below is cleaner with `0` included. -/
theorem finite_short_vectors {d : ℕ} (N : PercLib.Analysis.ModelNorm (Fin d → ℝ)) (r : ℝ) :
    {z : Fin d → ℤ | N (Int.cast ∘ z) < r}.Finite := by
  refine Set.Finite.subset
    ((PercLib.Models.LongRange.diagram_finite_short_vectors N r).insert 0) ?_
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · exact Set.mem_insert_iff.2 (Or.inr ⟨hz0, hz⟩)

/-- **Fibre bound.**  Let `S` contain every short difference vector.  A nonnegative family
`f` on the lattice which vanishes off the `r`-neighbourhood of `x` and is bounded by `C`
everywhere has total mass at most `#S * C`.  This is the step that turns a per-pair bound into a
summable bound along a vertex fibre. -/
theorem tsum_fibre_le {d : ℕ} {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (x : Fin d → ℤ) (f : (Fin d → ℤ) → ℝ≥0∞) (C : ℝ≥0∞)
    (hzero : ∀ y, ¬ (N (Int.cast ∘ (y - x)) < r) → f y = 0)
    (hbound : ∀ y, f y ≤ C) :
    ∑' y, f y ≤ (S.card : ℝ≥0∞) * C := by
  classical
  have hfin : ∀ y, f y ≠ 0 → y ∈ S.image (fun z => x + z) := by
    intro y hy
    refine Finset.mem_image.2 ⟨y - x, hS (y - x) ?_, ?_⟩
    · by_contra hlt
      exact hy (hzero y hlt)
    · abel
  have hzero' : ∀ y, y ∉ S.image (fun z => x + z) → f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (hfin y hne)
  rw [tsum_eq_sum hzero']
  calc ∑ y ∈ S.image (fun z => x + z), f y
      ≤ ∑ _y ∈ S.image (fun z => x + z), C := Finset.sum_le_sum fun y _ => hbound y
    _ = ((S.image (fun z => x + z)).card : ℝ≥0∞) * C := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ≥0∞) * C := by
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast Finset.card_image_le (f := fun z => x + z)

section Window

open Classical in
/-- **Finite-window tail bound for the cut-off pivotal `ℝ≥0∞` series.**

The cut-off radius is `r`, `S` is any finite set of difference vectors containing every
`z` with `N z < r`, `c` is a nonnegative pair weight supported on the cut-off (`hcsupp`), and
`W` is a finite vertex window.  Then the pivotal mass carried by pairs which are *not* both
inside `W` is at most twice `#S` times the `W`-exterior mass of a vertex weight `g`, where `g`
bounds the per-pair pivotal mass in the two crossing orientations (`hx`, `hy`).

The two model inputs are: (i) `pivotal_increment_eq_crossing`, which makes the increment vanish
unless an endpoint of the pair lies in the root cluster, and (ii) the bounded cut-off radius,
which makes every vertex fibre finite.  Nothing is assumed about the law. -/
theorem lintegral_window_tail_le {d : ℕ} {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) → c (s(x, y)) = 0)
    (W : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → ℝ≥0∞)
    (hx : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g x)
    (hy : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g y) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) := by
  classical
  set F : Finset (Sym2 (Fin d → ℤ)) :=
    (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2)) with hF
  set X : (Fin d → ℤ) → (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞ := fun x y ω =>
    (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
      ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) with hX
  have hx' : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ ≤ g x := hx
  have hy' : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ ≤ g y := hy
  -- measurability of the crossing integrand
  have hXm : ∀ x y : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) => X x y ω := by
    intro x y
    have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn o x) measurable_const measurable_const
    have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn o y) measurable_const measurable_const
    have h3 : Measurable fun ω : Config (Fin d → ℤ) =>
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) :=
      ((measurable_encard_cluster_toENNReal o).add
        (measurable_encard_cluster_toENNReal y)).pow_const p |>.sub
        ((measurable_encard_cluster_toENNReal o).pow_const p)
    exact (h1.mul h2).mul h3
  have hcm : ∀ x y : Fin d → ℤ,
      AEMeasurable (fun ω : Config (Fin d → ℤ) => c (s(x, y)) * X x y ω) μ :=
    fun x y => (measurable_const.mul (hXm x y)).aemeasurable
  -- the pointwise crossing identity
  have hcross : ∀ ω : Config (Fin d → ℤ),
      (∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ F then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)))
      = ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y))) := by
    intro ω
    rw [tsum_pivotal_eq_tsum_crossing ω o p
      (fun e => (if e ∈ F then (0 : ℝ≥0∞) else 1) * c e)]
    refine tsum_congr fun x => tsum_congr fun y => ?_
    simp only [hX]
    ac_rfl
  -- pairs both of whose endpoints lie in the window are in `F`
  have hmemF : ∀ x y : Fin d → ℤ, x ∈ W → y ∈ W → s(x, y) ∈ F := by
    intro x y hxw hyw
    refine Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hxw, hyw⟩, rfl⟩
  have hIW : ∀ x y : Fin d → ℤ, (if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) ≤
      (if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1) := by
    intro x y
    by_cases hs : s(x, y) ∈ F
    · rw [ite_eq_left hs]
      exact zero_le
    · rw [ite_eq_right hs]
      by_cases hxw : x ∈ W
      · by_cases hyw : y ∈ W
        · exact absurd (hmemF x y hxw hyw) hs
        · simp [hxw, hyw]
      · simp [hxw]
  -- pointwise: the window-exterior pair mass is charged to the window-exterior vertices
  have hpt : ∀ ω : Config (Fin d → ℤ),
      (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y))))
      ≤ ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            (c (s(x, y)) * X x y ω) := by
    intro ω
    refine ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y => ?_
    have h := mul_le_mul (le_refl (X x y ω * c (s(x, y)))) (hIW x y)
      zero_le zero_le
    calc X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y)))
        = (X x y ω * c (s(x, y))) * (if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) := by ac_rfl
      _ ≤ (X x y ω * c (s(x, y))) *
            ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) := h
      _ = ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            (c (s(x, y)) * X x y ω) := by ac_rfl
  -- exterior fibre bound, in the second coordinate
  have hfibY : ∀ x : Fin d → ℤ,
      ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ ≤ (S.card : ℝ≥0∞) * g x := by
    intro x
    refine tsum_fibre_le S hS x (fun y => ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) (g x) ?_ ?_
    · intro y hy
      simp [hcsupp x y hy]
    · intro y
      exact hx' x y
  have hcsupp' : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (x - y)) < r) → c (s(x, y)) = 0 := by
    intro x y hxy
    refine hcsupp x y ?_
    have heq : (Int.cast ∘ (y - x) : Fin d → ℝ) = -(Int.cast ∘ (x - y)) := by
      funext i
      simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply]
      push_cast
      ring
    rw [heq, map_neg_eq_map]
    exact hxy
  have hfibX : ∀ y : Fin d → ℤ,
      ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ ≤ (S.card : ℝ≥0∞) * g y := by
    intro y
    refine tsum_fibre_le S hS y (fun x => ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) (g y) ?_ ?_
    · intro x hx
      simp [hcsupp' x y hx]
    · intro x
      exact hy' x y
  have hmeasT : ∀ x : Fin d → ℤ, AEMeasurable
      (fun ω : Config (Fin d → ℤ) => ∑' y : Fin d → ℤ,
        ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
          (c (s(x, y)) * X x y ω)) μ := by
    intro x
    refine AEMeasurable.tsum fun y => ?_
    exact (hcm x y).const_mul _
  calc ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ F then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∫⁻ ω, ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y))) ∂μ :=
        lintegral_congr hcross
    _ ≤ ∫⁻ ω, ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            (c (s(x, y)) * X x y ω) ∂μ := lintegral_mono hpt
    _ = ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ := by
        rw [lintegral_tsum hmeasT]
        refine tsum_congr fun x => ?_
        rw [lintegral_tsum (fun y => (hcm x y).const_mul _)]
        refine tsum_congr fun y => ?_
        exact lintegral_const_mul _ (measurable_const.mul (hXm x y))
    _ = (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (if x ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
        + ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (if y ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ := by
        calc ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
              ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
                ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ
            = ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
                ((if x ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ
                  + (if y ∈ W then (0 : ℝ≥0∞) else 1) *
                    ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) :=
              tsum_congr fun x => tsum_congr fun y => add_mul _ _ _
          _ = ∑' x : Fin d → ℤ,
                ((∑' y : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
                    ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
                  + ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) *
                    ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) :=
              tsum_congr fun x => ENNReal.tsum_add
          _ = _ := ENNReal.tsum_add
    _ ≤ (S.card : ℝ≥0∞) * (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x)
        + (S.card : ℝ≥0∞) * (∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) * g y) := by
        refine add_le_add ?_ ?_
        · calc (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
              (if x ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
              = ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
                  (∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) := by
                refine tsum_congr fun x => ?_
                rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * ((S.card : ℝ≥0∞) * g x) := by
                refine ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hfibY x)
            _ = (S.card : ℝ≥0∞) * (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) := by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun x => by ac_rfl
        · calc (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
              (if y ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
              = ∑' y : Fin d → ℤ, ∑' x : Fin d → ℤ,
                  (if y ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ :=
                ENNReal.tsum_comm
            _ = ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) *
                  (∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) := by
                refine tsum_congr fun y => ?_
                rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) * ((S.card : ℝ≥0∞) * g y) := by
                refine ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl (hfibX y)
            _ = (S.card : ℝ≥0∞) * (∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) * g y) := by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun y => by ac_rfl
    _ = 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) := by
        rw [← two_mul]

open Classical in
/-- **The tail bound with the two-point (one-cluster) weight.**

This is `lintegral_window_tail_le` with the vertex weight specialised to the two-point
function `x ↦ ∫⁻ ω, 1(x ∈ K_o)` (times a constant).  The hypothesis `hfac` is the *only* place
where the model is used: the pivotal crossing mass of a pair is at most `C` times the
probability that the root cluster reaches either endpoint, uniformly in the pair and in the
scale.  Given it, the finite-window tail of the cut-off pivotal series is at most
`2 C #S` times the `W`-exterior mass of the root cluster.

Nothing in a uniform bound on `E|K_o|^q` produces `hfac`: see the file's module documentation. -/
theorem lintegral_window_tail_le_of_factorization {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) → c (s(x, y)) = 0)
    (W : Finset (Fin d → ℤ)) (C : ℝ≥0∞)
    (hfac : ∀ x y : Fin d → ℤ,
      ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ,
          (if x ∈ W then (0 : ℝ≥0∞) else 1) *
            (C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)) := by
  refine lintegral_window_tail_le S hS μ o p c hcsupp W
    (fun x => C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) ?_ ?_
  · intro x y
    refine le_trans (hfac x y) ?_
    exact mul_le_mul' le_rfl (min_le_left _ _)
  · intro x y
    refine le_trans (hfac x y) ?_
    exact mul_le_mul' le_rfl (min_le_right _ _)

open Classical in
/-- **The small-tail premise in finite-window form.**

The conclusion has the shape of the `htail` hypothesis of
`hasDerivAt_integral_pow_binomial_of_root_succ_moment_of_small_tail` (an arbitrarily small tail
outside one *finite* set of pairs), with `ℝ≥0∞` in place of the real norm series and with the
finite set exhibited as `pairs(W × W)`.  The quantitative content is that the size of the tail is
`2 * #S` times the vertex mass outside the same window `W`. -/
theorem exists_window_tail_le {d : ℕ} {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) → c (s(x, y)) = 0)
    (W : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → ℝ≥0∞)
    (hx : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g x)
    (hy : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g y)
    (ε : ℝ≥0∞)
    (hε : 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x)
      ≤ ε) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ ε :=
  le_trans (lintegral_window_tail_le S hS μ o p c hcsupp W g hx hy) hε

end Window

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The vertex mass of the root cluster as a sum over vertices -/

open Classical in
/-- **Spatial first-moment identity for the cluster volume, for an arbitrary measure.**

`E|K_o| = ∑'_x μ{x ∈ K_o}`, exact in `ℝ≥0∞`: an infinite cluster contributes `⊤` on both
sides, so no a.e. finiteness of the cluster is assumed.  This is the measure-generic form of
`chi_eq_tsum_tau` (which is stated for the Bernoulli law only); the window bounds are stated for
an arbitrary `μ`, so this is the form they consume. -/
theorem lintegral_encard_cluster_eq_tsum_mass (μ : Measure (Config V)) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂μ
      = ∑' x : V, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
  classical
  have hpt : ∀ ω : Config V, ((cluster ω o).encard : ℝ≥0∞)
      = ∑' x : V, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) := by
    intro ω
    rw [encard_cluster_eq_tsum]
    exact tsum_congr fun x => by rw [Set.indicator_apply]; rfl
  calc ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂μ
      = ∫⁻ ω, (∑' x : V, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)) ∂μ :=
        lintegral_congr hpt
    _ = ∑' x : V, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ :=
        lintegral_tsum fun x =>
          (Measurable.ite (measurableSet_conn o x) measurable_const measurable_const).aemeasurable

/-! ### The first moment is dominated by the top moment -/

/-- A finite `k`-th moment dominates the first moment, in `ℝ≥0∞`, for every `k ≥ 1`. -/
theorem enat_coe_le_self_pow {a : ℕ∞} {k : ℕ} (hk : 1 ≤ k) :
    (a : ℝ≥0∞) ≤ (a : ℝ≥0∞) ^ k := by
  by_cases ha : a = ⊤
  · rw [ha, ENat.toENNReal_top]
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    rw [ENat.toENNReal_coe]
    cases n with
    | zero => simp [zero_pow (by omega : k ≠ 0)]
    | succ m =>
      have h1 : (1 : ℝ≥0∞) ≤ ((m + 1 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      simpa using pow_le_pow_right₀ h1 hk

omit [Countable V] in
/-- **The root first moment is bounded by the root `(p+1)`-moment.** -/
theorem lintegral_encard_cluster_le_of_pow_le {μ : Measure (Config V)} {o : V} {p : ℕ}
    {M : ℝ≥0∞}
    (h : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≤ M) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂μ ≤ M :=
  le_trans (lintegral_mono fun ω => enat_coe_le_self_pow (a := (cluster ω o).encard)
    (k := p + 1) (by omega)) h

/-! ### The complement mass of the vertex mass function vanishes -/

open Classical in
/-- **The root-cluster mass outside a growing finite window tends to `0`.**

Only finiteness of the first moment `E|K_o|` is used, never a bound on the total mass: the
limit is a statement about the *tail* `∑_{x ∉ W}` of the vertex mass function.  This is the
vertex-mass form that the finite-window edge bounds consume in their right-hand side
`∑' x, (if x ∈ W then 0 else 1) * g x`. -/
theorem tendsto_tsum_window_compl_atTop_zero (μ : Measure (Config V)) (o : V)
    (hχ : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂μ ≠ ⊤) :
    Tendsto (fun W : Finset V => ∑' x : V, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) atTop (𝓝 0) := by
  classical
  have hsub : Tendsto (fun W : Finset V => ∑' x : {x : V // x ∉ W},
      ∫⁻ ω, (if x.1 ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) atTop (𝓝 0) :=
    ENNReal.tendsto_tsum_compl_atTop_zero
      (f := fun x : V => ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
      (by rw [← lintegral_encard_cluster_eq_tsum_mass]; exact hχ)
  have hconv : ∀ W : Finset V, (∑' x : {x : V // x ∉ W},
      ∫⁻ ω, (if x.1 ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
      = ∑' x : V, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
        ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
    intro W
    set g : V → ℝ≥0∞ :=
      fun y => ∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ with hg
    have h1 : (∑' x : {x : V // x ∉ W}, g x)
        = ∑' x : ↥({x : V | x ∉ W} : Set V), g x := rfl
    rw [h1, tsum_subtype]
    refine tsum_congr fun x => ?_
    by_cases h : x ∈ W <;> simp [h, hg]
  exact hsub.congr' (Eventually.of_forall hconv)

open Classical in
/-- **The window tail of the vertex mass is arbitrarily small.** -/
theorem exists_window_mass_tail_le (μ : Measure (Config V)) (o : V)
    (hχ : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂μ ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset V, ∑' x : V, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≤ ε := by
  classical
  have hev : ∀ᶠ W : Finset V in atTop, ∑' x : V, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ < ε :=
    (tendsto_tsum_window_compl_atTop_zero μ o hχ).eventually (eventually_lt_nhds hε)
  obtain ⟨W, hW⟩ := hev.exists
  exact ⟨W, le_of_lt hW⟩

open Classical in
/-- **Window tail of the vertex mass from a finite root `(p+1)`-moment.** -/
theorem exists_window_mass_tail_le_of_root_succ_moment (μ : Measure (Config V)) (o : V)
    (p : ℕ) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hroot : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≤ M)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset V, ∑' x : V, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≤ ε :=
  exists_window_mass_tail_le μ o
    (ne_top_of_le_ne_top hM (lintegral_encard_cluster_le_of_pow_le hroot)) hε

/-! ### Monotonicity of the cut-off kernel in the cut-off radius -/

omit [Countable V] in
/-- **`r ↦ 1{N(x - y) < r}` is monotone.**  The cut-off radial kernel of the indicator profile
is increasing in the cut-off radius. -/
theorem radialKernel_indicator_mono {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {r r' : ℝ}
    (hrr' : r ≤ r') (e : Sym2 (Fin d → ℤ)) :
    PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0) e ≤
      PercLib.Models.LongRange.radialKernel N (fun s => if s < r' then 1 else 0) e := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [PercLib.Models.LongRange.radialKernel_of_ne hxy,
        PercLib.Models.LongRange.radialKernel_of_ne hxy]
      by_cases h : N (Int.cast ∘ (x - y)) < r
      · have h' : N (Int.cast ∘ (x - y)) < r' := lt_of_lt_of_le h hrr'
        simp [h, h']
      · simp [h]

omit [Countable V] in
/-- **On a corner-free interval the cut-off indicator is constant in the radius.**

If no lattice difference vector has norm strictly between `u` and `v`, then for `r, r' ∈ (u, v)`
the two cut-off kernels agree.  This is what makes a finite-window bound stated at one radius
hold verbatim at every radius of the interval, because the geometry, hence the finite fibre set
`S`, cannot change inside the interval. -/
theorem radialKernel_indicator_eq_of_corner {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {u v r r' : ℝ}
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Set.Ioo u v) (hr : r ∈ Set.Ioo u v)
    (hr' : r' ∈ Set.Ioo u v) (e : Sym2 (Fin d → ℤ)) :
    PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0) e =
      PercLib.Models.LongRange.radialKernel N (fun s => if s < r' then 1 else 0) e := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [PercLib.Models.LongRange.radialKernel_of_ne hxy,
        PercLib.Models.LongRange.radialKernel_of_ne hxy]
      have hiff : (N (Int.cast ∘ (x - y)) < r) ↔ (N (Int.cast ∘ (x - y)) < r') := by
        have hnot := hcorner (x - y)
        rcases not_and_or.1 hnot with h1 | h1
        · rw [not_lt] at h1
          exact ⟨fun _ => lt_of_le_of_lt h1 hr'.1, fun _ => lt_of_le_of_lt h1 hr.1⟩
        · rw [not_lt] at h1
          exact ⟨fun hc => absurd hc (not_lt.2 (le_trans hr.2.le h1)),
            fun hc => absurd hc (not_lt.2 (le_trans hr'.2.le h1))⟩
      by_cases h : N (Int.cast ∘ (x - y)) < r
      · have h' : N (Int.cast ∘ (x - y)) < r' := hiff.1 h
        simp [h, h']
      · have h' : ¬ (N (Int.cast ∘ (x - y)) < r') := fun hc => h (hiff.2 hc)
        simp [h, h']

omit [Countable V] in
/-- **The cut-off kernel converges pointwise to the full kernel as `r → ∞`.** -/
theorem eventually_radialKernel_indicator_eq_full {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    (e : Sym2 (Fin d → ℤ)) :
    ∀ᶠ r : ℝ in atTop,
      PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0) e =
        PercLib.Models.LongRange.radialKernel N (fun _ => (1 : ℝ)) e := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy; simp
    · filter_upwards [eventually_gt_atTop (N (Int.cast ∘ (x - y)))] with r hr
      rw [PercLib.Models.LongRange.radialKernel_of_ne hxy,
        PercLib.Models.LongRange.radialKernel_of_ne hxy]
      simp [hr]

/-! ### The two-point form for the Bernoulli law -/

open Classical in
/-- The vertex mass is the two-point function of the Bernoulli law. -/
theorem tau_eq_lintegral_cluster_indicator (q : Sym2 V → unitInterval) (o x : V) :
    tau q o x = ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂(law q) := by
  classical
  rw [tau]
  exact (lintegral_indicator_one (measurableSet_conn o x)).symm

open Classical in
/-- **Window tail of the two-point function.** -/
theorem exists_window_tau_tail_le (q : Sym2 V → unitInterval) (o : V)
    (hχ : chi q o ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset V, ∑' x : V, (if x ∈ W then (0 : ℝ≥0∞) else 1) * tau q o x ≤ ε := by
  classical
  obtain ⟨W, hW⟩ := exists_window_mass_tail_le (law q) o (by rwa [chi] at hχ) hε
  refine ⟨W, le_trans (ENNReal.tsum_le_tsum fun x => ?_) hW⟩
  rw [tau_eq_lintegral_cluster_indicator]

open Classical in
/-- **Modular composition: finite-window ENN tail from the factorization hypothesis and a bound
on the exterior vertex mass.**

The conclusion is the `ℝ≥0∞` form of the small-tail premise: the pivotal mass of pairs not both
inside the finite window `W` is at most `ε`.  The two numeric inputs are kept separate on purpose
— `hext` is the exterior vertex mass (supplied elsewhere from the root moment, e.g. by
`exists_window_mass_tail_le_of_root_succ_moment`) and `hεδ` is the arithmetic choice of `δ`; no
division is performed here, so no finiteness of `S.card` or `C` is needed.

This is a *finite-window* statement: `W` is a finite set of vertices and the excluded edge set is
`pairs(W × W)`.  It is not an infinite-lattice statement. -/
theorem window_tail_le_of_factorization_of_tau_tail {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) → c (s(x, y)) = 0)
    (W : Finset (Fin d → ℤ)) (C : ℝ≥0∞)
    (hfac : ∀ x y : Fin d → ℤ,
      ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ))
    {ε δ : ℝ≥0∞}
    (hext : ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≤ δ)
    (hεδ : 2 * ((S.card : ℝ≥0∞) * (C * δ)) ≤ ε) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ ε := by
  classical
  refine le_trans
    (lintegral_window_tail_le_of_factorization S hS μ o p c hcsupp W C hfac) ?_
  have hmass : (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
      (C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ))
      ≤ C * δ := by
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl hext)
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun x => mul_left_comm _ _ _
  exact le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hmass)) hεδ

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

open Classical in
/-- **Real-norm conversion of the finite-window `ℝ≥0∞` pivotal tail.**

Let `cw` be the cut-off derivative weight of a pair.  Assume the `ℝ≥0∞` window tail of the
radially truncated pivotal series is at most `B`.  Then the *real-norm* series of weighted pair
terms whose pairs are not both inside the window `W` is at most `|β J'(r)| * B.toReal`.

The identity behind the conversion is
`cw e * ∫ (pivotal) = β J'(r) * (radial weight e * ∫⁻ (pivotal))`, so the rate `β J'(r)`
factors out and is never inverted.  `B` is not required to be finite for the inequality to be
meaningful, but `B ≠ ⊤` is what makes the `ℝ≥0∞`/`ℝ` cast continuous, and it also gives the
summability of the real series. -/
theorem tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (r : ℝ) (o : Fin d → ℤ) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (W : Finset (Fin d → ℤ)) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hins : ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hwin : ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) *
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ B) :
    ∑' e : ↥((W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
        : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖
      ≤ |(β : ℝ) * -K' r| * B.toReal := by
  classical
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel (d := d) N K r) β)
  let F : Finset (Sym2 (Fin d → ℤ)) :=
    (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
  let rk : Sym2 (Fin d → ℤ) → ℝ≥0∞ :=
    fun e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)
  let w : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e => (if e ∈ F then 0 else 1) * rk e
  let Q : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e => ∫⁻ ω, (if e ∈ ω then 0 else
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p - ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
  have hQ : ∀ e, Q e ≠ ⊤ := by
    intro e
    refine ne_top_of_le_ne_top
      (lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top e o p (hins e)) ?_
    refine lintegral_mono fun ω => ?_
    by_cases he : e ∈ ω
    · simp [he]
    · rw [ite_eq_right he, Set.sdiff_singleton_eq_self he]
  have hfin : ∀ e : Sym2 (Fin d → ℤ), ∀ᵐ ω ∂μ,
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤ := by
    intro e
    exact ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_insert_coe e o) p hp
      (hins e)
  have hint : ∀ e : Sym2 (Fin d → ℤ), Integrable
      (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ p) μ := by
    intro e
    exact integrable_toReal_pow_encard_cluster_insert e o p (hins e)
  have hrke : ∀ e : Sym2 (Fin d → ℤ),
      (rk e).toReal = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) := by
    intro e
    simp only [rk]
    simp
  have hterm : ∀ e : Sym2 (Fin d → ℤ),
      ‖cw e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ‖ =
      |(β : ℝ) * -K' r| * (rk e * Q e).toReal := by
    intro e
    have hcoef := cutoff_weight_mul_integral_eq_rate_mul_closed_toReal
      (K := K) (K' := K') p β r o cw hcw hfin hint e
    rw [hcoef, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg (radialKernel N _ e).coe_nonneg ENNReal.toReal_nonneg),
      ENNReal.toReal_mul, hrke e]
  have hT : (∑' e, w e * Q e) ≤ B := by
    refine le_trans (le_of_eq ?_) hwin
    rw [tsum_lintegral_closed_pivotal μ p o w]
  have hTtop : (∑' e, w e * Q e) ≠ ⊤ := ne_top_of_le_ne_top hB hT
  have hsubeq : (∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ, w e.1 * Q e.1) =
      ∑' e, w e * Q e := by
    have h := ENNReal.sum_add_tsum_compl F (fun e => w e * Q e)
    have hzero : ∑ e ∈ F, w e * Q e = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      simp [w, he]
    rw [hzero, zero_add] at h
    exact h
  have hsub : (∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ, w e.1 * Q e.1) ≤ B := by
    rw [hsubeq]
    exact hT
  have hterm' : ∀ e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ‖ =
      |(β : ℝ) * -K' r| * (w e.1 * Q e.1).toReal := by
    intro e
    rw [hterm e.1]
    have hmem : ¬ (e.1 ∈ F) := by
      have h1 : e.1 ∉ (F : Set (Sym2 (Fin d → ℤ))) := e.2
      simpa using h1
    simp only [w]
    rw [ite_eq_right hmem, one_mul]
  have hsubt : (∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ, w e.1 * Q e.1) ≠ ⊤ :=
    ne_top_of_le_ne_top hB hsub
  have hsummable : Summable fun e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ => (w e.1 * Q e.1).toReal :=
    ENNReal.summable_toReal hsubt
  have hbound : ∀ S : Finset ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ∑ e ∈ S, ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ‖
      ≤ |(β : ℝ) * -K' r| * B.toReal := by
    intro S
    calc ∑ e ∈ S, ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ‖
        = ∑ e ∈ S, |(β : ℝ) * -K' r| * (w e.1 * Q e.1).toReal :=
          Finset.sum_congr rfl fun e _ => hterm' e
      _ = |(β : ℝ) * -K' r| * ∑ e ∈ S, (w e.1 * Q e.1).toReal :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ |(β : ℝ) * -K' r| * ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
            (w e.1 * Q e.1).toReal :=
          mul_le_mul_of_nonneg_left
            (hsummable.sum_le_tsum S fun _ _ => ENNReal.toReal_nonneg) (abs_nonneg _)
      _ = |(β : ℝ) * -K' r| *
            (∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ, w e.1 * Q e.1).toReal := by
          have hne : ∀ e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ, w e.1 * Q e.1 ≠ ⊤ := by
            intro e
            have hw : w e.1 ≠ ⊤ := by
              have h1 : (if e.1 ∈ F then (0 : ℝ≥0∞) else 1) ≠ ⊤ := by split_ifs <;> simp
              have h2 : rk e.1 ≠ ⊤ := by
                simp only [rk]
                simp
              simpa only [w] using ENNReal.mul_ne_top h1 h2
            exact ENNReal.mul_ne_top hw (hQ e.1)
          rw [ENNReal.tsum_toReal_eq hne]
      _ ≤ |(β : ℝ) * -K' r| * B.toReal := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact (ENNReal.toReal_le_toReal hsubt hB).2 hsub
  exact Real.tsum_le_of_sum_le (fun e => norm_nonneg _) hbound


open Classical in
/-- **The radial indicator on a far pair vanishes.**  This discharges the support hypothesis
`hcsupp` of `lintegral_window_tail_le_of_factorization` for the concrete weight
`e ↦ 1{N (e) < r}`, which is `radialKernel` of the indicator profile. -/
theorem radialKernel_indicator_hcsupp {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} :
    ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) →
      (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) = 0 := by
  intro x y hyx
  have hsymm : N (Int.cast ∘ (y - x)) = N (Int.cast ∘ (x - y)) := by
    rw [intCast_comp_sub, intCast_comp_sub, map_sub_rev]
  have h0 : (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ) = 0 :=
    radialKernel_indicator_eq_zero_of_not_lt (N := N) (r := r) (fun h => hyx (hsymm ▸ h))
  have h0' : radialKernel N (fun s => if s < r then 1 else 0) s(x, y) = 0 := by
    exact_mod_cast h0
  rw [h0']
  simp

open Classical in
/-- **The `htail`-shaped small-tail statement at one radius.**

This is `tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail` with the numeric bound
renamed.  Its hypothesis `hwin` is *literally* the conclusion of
`lintegral_window_tail_le_of_factorization` (with `c e = 1{N (e) < r}`), so composing the two
needs no further conversion.  The conclusion is the `htail` inequality
`∑' e : ↥Fᶜ, ‖cw r e * ∫ (pivotal)‖ ≤ ε` consumed by
`continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail`, with the finite pair set
`F = pairs (W × W)` exhibited. -/
theorem exists_window_htail_of_lintegral_window_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (r : ℝ) (o : Fin d → ℤ) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (W : Finset (Fin d → ℤ)) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hins : ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hwin : ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) *
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ B)
    (ε : ℝ) (hε : |(β : ℝ) * -K' r| * B.toReal ≤ ε) :
    ∑' e : ↥((W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
        : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε :=
  le_trans (tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail β p hp r o cw hcw W B hB
    hins hwin) hε

open Classical in
/-- **The `htail` shape uniformly on a parameter neighbourhood.**

For a family of weights `cw r` and a family of bounds `E r`, if the `ℝ≥0∞` window tail is at most
`E r` and `|β J'(r)| * (E r).toReal ≤ ε` for every `r ∈ U`, then the real-norm tail is at most
`ε` for every `r ∈ U`.  Taking `U = U₀ ∩ Ioo u v` with `U₀ ∈ 𝓝 r₀` (and `r₀ ∈ Ioo u v`) turns
this into the literal `htail` hypothesis of
`continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail`.

The scalar hypothesis `hε` is where the remaining analysis sits: `E r` is the
`W`-exterior root-cluster mass at scale `r` multiplied by `2 #S C`, and it is *not* supplied by a
uniform total mass bound — that is the content of `htail`, and this lemma only converts it. -/
theorem htail_of_uniform_lintegral_window_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (o : Fin d → ℤ) (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (W : Finset (Fin d → ℤ)) (U : Set ℝ) (ε : ℝ) (E : ℝ → ℝ≥0∞)
    (hEtop : ∀ r ∈ U, E r ≠ ⊤)
    (hins : ∀ r ∈ U, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hwin : ∀ r ∈ U, ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) *
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ E r)
    (hε : ∀ r ∈ U, |(β : ℝ) * -K' r| * (E r).toReal ≤ ε) :
    ∀ r ∈ U, ∑' e : ↥((W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
        : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε := by
  intro r hr
  exact le_trans (tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail β p hp r o (cw r)
    (hcw r) W (E r) (hEtop r hr) (hins r hr) (hwin r hr)) (hε r hr)

open Classical in
/-- **The zero-rate case.**  When `β J'(r) = 0` the cut-off derivative weight vanishes
identically, so no bound on the pivotal series is needed and no inverse of the rate appears
anywhere in this file. -/
theorem cw_eq_zero_of_rate_eq_zero {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    {β : ℝ≥0} {r : ℝ} {cw : Sym2 (Fin d → ℤ) → ℝ}
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (h0 : (β : ℝ) * -K' r = 0) (e : Sym2 (Fin d → ℤ)) : cw e = 0 := by
  rw [hcw e, h0]
  simp

open Classical in
/-- **The tail vanishes at zero rate.**  Consequence of `cw_eq_zero_of_rate_eq_zero`: the real
norm series is identically zero, so the `htail` estimate holds with `ε = 0`. -/
theorem tsum_norm_cutoff_flux_compl_eq_zero_of_rate_eq_zero {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (r : ℝ)
    (o : Fin d → ℤ) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (h0 : (β : ℝ) * -K' r = 0) (W : Finset (Fin d → ℤ)) :
    ∑' e : ↥((W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
        : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ = 0 := by
  refine (tsum_congr fun e => ?_).trans tsum_zero
  have h : cw e.1 = 0 := cw_eq_zero_of_rate_eq_zero (β := β) (r := r) hcw h0 e.1
  rw [h]
  simp
open Classical in
/-- **The literal `htail` premise of the derivative interface.**

Given the pointwise `ℝ≥0∞` window bounds `hwin` and the scalar smallness `hε` on
`U₀ ∩ Ioo u v`, this produces exactly the `htail` hypothesis of
`continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail`:

`∃ U ∈ 𝓝 r₀, ∃ F, ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥Fᶜ, ‖cw r e * ∫ (pivotal)‖ ≤ ε`

with the finite pair set `F = pairs (W × W)` and `U = U₀ ∩ Ioo u v`.  The neighbourhood
shrinking is only the interior point `r₀ ∈ Ioo u v`; no uniformity in `r` beyond `hwin`, `hε` is
asserted. -/
theorem exists_nhds_window_htail_of_uniform_lintegral_window_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (o : Fin d → ℤ) (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (W : Finset (Fin d → ℤ)) {u v r₀ : ℝ} (hr₀ : r₀ ∈ Ioo u v) (U₀ : Set ℝ)
    (hU₀ : U₀ ∈ 𝓝 r₀) (ε : ℝ) (E : ℝ → ℝ≥0∞)
    (hEtop : ∀ r ∈ U₀ ∩ Ioo u v, E r ≠ ⊤)
    (hins : ∀ r ∈ U₀ ∩ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hwin : ∀ r ∈ U₀ ∩ Ioo u v, ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) *
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ E r)
    (hε : ∀ r ∈ U₀ ∩ Ioo u v, |(β : ℝ) * -K' r| * (E r).toReal ≤ ε) :
    ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε := by
  refine ⟨U₀ ∩ Ioo u v, Filter.inter_mem hU₀ (isOpen_Ioo.mem_nhds hr₀),
    (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2)), fun r hr => ?_⟩
  exact htail_of_uniform_lintegral_window_tail β p hp o cw hcw W (U₀ ∩ Ioo u v) ε E hEtop
    hins hwin hε r (by simpa using hr)

open Classical in
/-- **The real-norm tail with the paper's explicit constant.**

`tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail` with
`B = 2 #S · ∑_{x ∉ W} C τ_r(x)`, i.e. the bound that `lintegral_window_tail_le_of_factorization`
supplies from `hfac`.  Feeding the latter lemma's conclusion into `hwin` therefore yields

`∑' e : ↥(pairs (W × W))ᶜ, ‖cw e * ∫ (closed pivotal)‖
   ≤ |β J'(r)| · (2 #S · ∑_{x ∉ W} C τ_r(x))`,

which is the pair-series form of the paper's `β|J'(r)|` weighted flux.  The extra `hB` is the
finiteness of that constraint mass: the `W`-exterior root-cluster mass must be finite, and this
is not a consequence of a uniform total mass bound. -/
theorem tsum_norm_cutoff_flux_compl_le_of_explicit_window_mass {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ} (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p)
    (r : ℝ) (o : Fin d → ℤ) (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (S : Finset (Fin d → ℤ)) (W : Finset (Fin d → ℤ)) (C : ℝ≥0∞)
    (hB : 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ,
        (if x ∈ W then (0 : ℝ≥0∞) else 1) *
          (C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))) ≠ ⊤)
    (hins : ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hwin : ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) *
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤
      2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ,
        (if x ∈ W then (0 : ℝ≥0∞) else 1) *
          (C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))))) :
    ∑' e : ↥((W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
        : Set (Sym2 (Fin d → ℤ)))ᶜ,
      ‖cw e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖
      ≤ |(β : ℝ) * -K' r| * (2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ,
          (if x ∈ W then (0 : ℝ≥0∞) else 1) *
            (C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
              ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))))).toReal :=
  tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail β p hp r o cw hcw W _ hB hins hwin

end PercLib.Models.LongRange

end

namespace PercLib.Percolation.Bond

open Classical in
/-- **Window tail from fibre-summed crossing hypotheses.**  Same conclusion as
`lintegral_window_tail_le`, but the per-pair bounds are replaced by the fibre sums over one
coordinate: `Σ_y (crossing mass)(x,y) ≤ #S * g x` and its transpose.  The pointwise `min`
factorization implies these (through `tsum_fibre_le`) but not conversely. -/
theorem lintegral_window_tail_le_of_fibre_factorization {d : ℕ}
    {_N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {_r : ℝ}
    (S : Finset (Fin d → ℤ))
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (W : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → ℝ≥0∞)
    (hfibx : ∀ x : Fin d → ℤ, ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ (S.card : ℝ≥0∞) * g x)
    (hfiby : ∀ y : Fin d → ℤ, ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ (S.card : ℝ≥0∞) * g y) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) := by
  classical
  set F : Finset (Sym2 (Fin d → ℤ)) :=
    (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2)) with hF
  set X : (Fin d → ℤ) → (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞ := fun x y ω =>
    (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
      ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) with hX
  -- measurability of the crossing integrand
  have hXm : ∀ x y : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) => X x y ω := by
    intro x y
    have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn o x) measurable_const measurable_const
    have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn o y) measurable_const measurable_const
    have h3 : Measurable fun ω : Config (Fin d → ℤ) =>
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p) :=
      ((measurable_encard_cluster_toENNReal o).add
        (measurable_encard_cluster_toENNReal y)).pow_const p |>.sub
        ((measurable_encard_cluster_toENNReal o).pow_const p)
    exact (h1.mul h2).mul h3
  have hcm : ∀ x y : Fin d → ℤ,
      AEMeasurable (fun ω : Config (Fin d → ℤ) => c (s(x, y)) * X x y ω) μ :=
    fun x y => (measurable_const.mul (hXm x y)).aemeasurable
  -- the pointwise crossing identity
  have hcross : ∀ ω : Config (Fin d → ℤ),
      (∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ F then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)))
      = ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y))) := by
    intro ω
    rw [tsum_pivotal_eq_tsum_crossing ω o p
      (fun e => (if e ∈ F then (0 : ℝ≥0∞) else 1) * c e)]
    refine tsum_congr fun x => tsum_congr fun y => ?_
    simp only [hX]
    ac_rfl
  -- pairs both of whose endpoints lie in the window are in `F`
  have hmemF : ∀ x y : Fin d → ℤ, x ∈ W → y ∈ W → s(x, y) ∈ F := by
    intro x y hxw hyw
    refine Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hxw, hyw⟩, rfl⟩
  have hIW : ∀ x y : Fin d → ℤ, (if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) ≤
      (if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1) := by
    intro x y
    by_cases hs : s(x, y) ∈ F
    · rw [ite_eq_left hs]
      exact zero_le
    · rw [ite_eq_right hs]
      by_cases hxw : x ∈ W
      · by_cases hyw : y ∈ W
        · exact absurd (hmemF x y hxw hyw) hs
        · simp [hxw, hyw]
      · simp [hxw]
  -- pointwise: the window-exterior pair mass is charged to the window-exterior vertices
  have hpt : ∀ ω : Config (Fin d → ℤ),
      (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y))))
      ≤ ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            (c (s(x, y)) * X x y ω) := by
    intro ω
    refine ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y => ?_
    have h := mul_le_mul (le_refl (X x y ω * c (s(x, y)))) (hIW x y)
      zero_le zero_le
    calc X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y)))
        = (X x y ω * c (s(x, y))) * (if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) := by ac_rfl
      _ ≤ (X x y ω * c (s(x, y))) *
            ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) := h
      _ = ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            (c (s(x, y)) * X x y ω) := by ac_rfl
  -- fibre hypothesis, in the second coordinate
  have hfibY : ∀ x : Fin d → ℤ,
      ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ ≤ (S.card : ℝ≥0∞) * g x := hfibx
  have hfibX : ∀ y : Fin d → ℤ,
      ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ ≤ (S.card : ℝ≥0∞) * g y := hfiby
  have hmeasT : ∀ x : Fin d → ℤ, AEMeasurable
      (fun ω : Config (Fin d → ℤ) => ∑' y : Fin d → ℤ,
        ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
          (c (s(x, y)) * X x y ω)) μ := by
    intro x
    refine AEMeasurable.tsum fun y => ?_
    exact (hcm x y).const_mul _
  calc ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ F then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      = ∫⁻ ω, ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          X x y ω * ((if s(x, y) ∈ F then (0 : ℝ≥0∞) else 1) * c (s(x, y))) ∂μ :=
        lintegral_congr hcross
    _ ≤ ∫⁻ ω, ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            (c (s(x, y)) * X x y ω) ∂μ := lintegral_mono hpt
    _ = ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
            ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ := by
        rw [lintegral_tsum hmeasT]
        refine tsum_congr fun x => ?_
        rw [lintegral_tsum (fun y => (hcm x y).const_mul _)]
        refine tsum_congr fun y => ?_
        exact lintegral_const_mul _ (measurable_const.mul (hXm x y))
    _ = (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (if x ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
        + ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (if y ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ := by
        calc ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
              ((if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1)) *
                ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ
            = ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
                ((if x ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ
                  + (if y ∈ W then (0 : ℝ≥0∞) else 1) *
                    ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) :=
              tsum_congr fun x => tsum_congr fun y => add_mul _ _ _
          _ = ∑' x : Fin d → ℤ,
                ((∑' y : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
                    ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
                  + ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) *
                    ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) :=
              tsum_congr fun x => ENNReal.tsum_add
          _ = _ := ENNReal.tsum_add
    _ ≤ (S.card : ℝ≥0∞) * (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x)
        + (S.card : ℝ≥0∞) * (∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) * g y) := by
        refine add_le_add ?_ ?_
        · calc (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
              (if x ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
              = ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
                  (∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) := by
                refine tsum_congr fun x => ?_
                rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * ((S.card : ℝ≥0∞) * g x) := by
                refine ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hfibY x)
            _ = (S.card : ℝ≥0∞) * (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) := by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun x => by ac_rfl
        · calc (∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
              (if y ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ)
              = ∑' y : Fin d → ℤ, ∑' x : Fin d → ℤ,
                  (if y ∈ W then (0 : ℝ≥0∞) else 1) * ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ :=
                ENNReal.tsum_comm
            _ = ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) *
                  (∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) * X x y ω ∂μ) := by
                refine tsum_congr fun y => ?_
                rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) * ((S.card : ℝ≥0∞) * g y) := by
                refine ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl (hfibX y)
            _ = (S.card : ℝ≥0∞) * (∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) * g y) := by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun y => by ac_rfl
    _ = 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) := by
        rw [← two_mul]


open Classical in
/-- **Pointwise pair bounds imply the fibre bounds** with the same `#S` factor.  This is the
direction that shows the fibre hypotheses above are implied by the pointwise `min` factorization
(and hence that the theorem above specialises to `lintegral_window_tail_le_of_factorization`). -/
theorem fibre_bound_of_pointwise {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) → c (s(x, y)) = 0)
    (g : (Fin d → ℤ) → ℝ≥0∞)
    (hx : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g x) :
    ∀ x : Fin d → ℤ, ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ (S.card : ℝ≥0∞) * g x := by
  intro x
  exact tsum_fibre_le S hS x (fun y => ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ) (g x)
    (fun y hy => by simp [hcsupp x y hy]) (fun y => hx x y)

open Classical in
/-- **Pointwise pair bounds imply the transposed fibre bounds.**  Same as
`fibre_bound_of_pointwise` but summing over the *first* coordinate; the support hypothesis has to
be stated in the transposed direction. -/
theorem fibre_bound_of_pointwise_transposed {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsuppT : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (x - y)) < r) → c (s(x, y)) = 0)
    (g : (Fin d → ℤ) → ℝ≥0∞)
    (hy : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g y) :
    ∀ y : Fin d → ℤ, ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ (S.card : ℝ≥0∞) * g y := by
  intro y
  exact tsum_fibre_le S hS y (fun x => ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ) (g y)
    (fun x hx => by simp [hcsuppT x y hx]) (fun x => hy x y)

open Classical in
/-- **The finite-window tail bound from the `min` factorization, via the fibre bounds.**

Same conclusion as `lintegral_window_tail_le_of_factorization`, obtained by first summing
the pointwise bound over one coordinate, so that only the summed form is used. -/
theorem lintegral_window_tail_le_of_factorization_via_fibre {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ (N (Int.cast ∘ (y - x)) < r) → c (s(x, y)) = 0)
    (W : Finset (Fin d → ℤ)) (C : ℝ≥0∞)
    (hfac : ∀ x y : Fin d → ℤ,
      ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ 2 * ((S.card : ℝ≥0∞) * ∑' x : Fin d → ℤ,
          (if x ∈ W then (0 : ℝ≥0∞) else 1) *
            (C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)) := by
  refine lintegral_window_tail_le_of_fibre_factorization (_N := N) (_r := r) S μ o p c W
    (fun x => C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) ?_ ?_
  · intro x
    exact fibre_bound_of_pointwise S hS μ o p c hcsupp
      (fun x => C * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
      (fun x y => le_trans (hfac x y) (mul_le_mul' le_rfl (min_le_left _ _))) x
  · have hcsuppT : ∀ x y : Fin d → ℤ,
        ¬ (N (Int.cast ∘ (x - y)) < r) → c (s(x, y)) = 0 := by
      intro x y hxy
      refine hcsupp x y ?_
      have heq : (Int.cast ∘ (y - x) : Fin d → ℝ) = -(Int.cast ∘ (x - y)) := by
        funext i
        simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply]
        push_cast
        ring
      rw [heq, map_neg_eq_map]
      exact hxy
    intro y
    exact fibre_bound_of_pointwise_transposed S hS μ o p c hcsuppT
      (fun y => C * ∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
      (fun x y => le_trans (hfac x y) (mul_le_mul' le_rfl (min_le_right _ _))) y

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- Superadditivity-type inequality for `ℝ≥0`: `r ^ n + 1 ≤ (r + 1) ^ n` for `n ≥ 1`. -/
theorem one_add_le_pow_one_add (r : ℝ≥0) (k : ℕ) : r ^ (k + 1) + 1 ≤ (r + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (r + 1) ^ (k + 1 + 1) = (r + 1) ^ (k + 1) * (r + 1) := pow_succ _ _
    have hmono : (r ^ (k + 1) + 1) * (r + 1) ≤ (r + 1) ^ (k + 1) * (r + 1) :=
      mul_le_mul_of_nonneg_right ih (by positivity)
    have hexp : (r ^ (k + 1) + 1) * (r + 1) = r ^ (k + 1 + 1) + r ^ (k + 1) + r + 1 := by
      rw [pow_succ]
      ring
    have hge : r ^ (k + 1 + 1) + 1 ≤ r ^ (k + 1 + 1) + r ^ (k + 1) + r + 1 := by
      have hX : r ^ (k + 1 + 1) ≤ r ^ (k + 1 + 1) + (r ^ (k + 1) + r) :=
        le_add_of_nonneg_right (by positivity)
      have := add_le_add_left hX 1
      simpa only [add_assoc] using this
    calc r ^ (k + 1 + 1) + 1 ≤ r ^ (k + 1 + 1) + r ^ (k + 1) + r + 1 := hge
      _ = (r ^ (k + 1) + 1) * (r + 1) := hexp.symm
      _ ≤ (r + 1) ^ (k + 1) * (r + 1) := hmono
      _ = (r + 1) ^ (k + 1 + 1) := hstep.symm

/-- **The crossing increment is at least one on finite clusters.**  If `|K_o| < ∞` and
`|K_y| ≥ 1` then `(|K_o| + |K_y|) ^ p - |K_o| ^ p ≥ 1` for `p ≥ 1`, in `ℝ≥0∞`. -/
theorem one_le_crossing_increment (p : ℕ) (hp : 1 ≤ p) {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : 1 ≤ b) :
    1 ≤ (a + b) ^ p - a ^ p := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  set r : ℝ≥0 := a.toNNReal with hr
  have har : (r : ℝ≥0∞) = a := ENNReal.coe_toNNReal ha
  have hb' : a + 1 ≤ a + b := by simpa [add_comm] using add_le_add_left hb a
  have hR1 : ((r ^ (k + 1) + 1 : ℝ≥0) : ℝ≥0∞) = a ^ (k + 1) + 1 := by
    push_cast
    rw [har]
  have hR2 : (((r + 1) ^ (k + 1) : ℝ≥0) : ℝ≥0∞) = (a + 1) ^ (k + 1) := by
    push_cast
    rw [har]
  have hone : a ^ (k + 1) + 1 ≤ (a + 1) ^ (k + 1) := by
    rw [← hR1, ← hR2]
    exact ENNReal.coe_le_coe.2 (one_add_le_pow_one_add r k)
  have htarget : a ^ (k + 1) + 1 ≤ (a + b) ^ (k + 1) :=
    le_trans hone (ENNReal.pow_le_pow_left hb')
  have htop : a ^ (k + 1) ≠ ⊤ := ne_of_lt (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 ha))
  have hle : a ^ (k + 1) ≤ (a + b) ^ (k + 1) := le_trans (le_add_right le_rfl) htarget
  rw [ENNReal.le_sub_iff_add_le_right htop hle]
  simpa [add_comm] using htarget

open Classical in
/-- **The factorization hypothesis forces two-point comparability.**

Under `hfac` with a pair weight `c`, on the event `{x ∈ K_o, y ∉ K_o}` the crossing increment
`(|K_o| + |K_y|) ^ p - |K_o| ^ p` is at least `1` whenever `|K_o|` is finite, so `hfac` implies

`c {x,y} * (P(x ∈ K_o) - P(y ∈ K_o)) ≤ C * min (P(x ∈ K_o)) (P(y ∈ K_o))`.

Equivalently: `P(x ∈ K_o) ≤ (1 + C / c {x,y}) * P(y ∈ K_o)` on every pair that carries weight.
This is a *necessary* condition on the two-point function; it is not a consequence of moment
bounds, and it is the part of `hfac` that a counterexample would have to attack. -/
theorem two_point_sub_le_of_factorization {μ : Measure (Config V)} {o : V} {p : ℕ}
    (hp : 1 ≤ p) (c : Sym2 V → ℝ≥0∞) {C : ℝ≥0∞}
    (hfin : μ {ω : Config V | ((cluster ω o).encard : ℝ≥0∞) = ⊤} = 0)
    (hfac : ∀ x y : V, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)) :
    ∀ x y : V, c (s(x, y)) *
        ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) -
         (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) := by
  intro x y
  set Sx : Set (Config V) := {ω | x ∈ cluster ω o} with hSxdef
  set Sy : Set (Config V) := {ω | y ∈ cluster ω o} with hSydef
  have hSxm : MeasurableSet Sx := by
    have h_eq : Sx = conn o x := by
      ext ω
      rw [hSxdef]
      exact mem_cluster_iff ω o x
    rw [h_eq]
    exact measurableSet_conn o x
  have hSym : MeasurableSet Sy := by
    have h_eq : Sy = conn o y := by
      ext ω
      rw [hSydef]
      exact mem_cluster_iff ω o y
    rw [h_eq]
    exact measurableSet_conn o y
  have hτx : ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ = μ Sx := by
    have hfun : (fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)) =
        Sx.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      simp [Set.indicator, hSxdef]
    rw [hfun, lintegral_indicator_const hSxm (1 : ℝ≥0∞), one_mul]
  have hτy : ∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ = μ Sy := by
    have hfun : (fun ω : Config V => (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0)) =
        Sy.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      simp [Set.indicator, hSydef]
    rw [hfun, lintegral_indicator_const hSym (1 : ℝ≥0∞), one_mul]
  have hsub : μ Sx ≤ μ (Sx ∩ Syᶜ) + μ Sy := by
    have hsubs : Sx ⊆ (Sx ∩ Syᶜ) ∪ Sy := by
      intro ω hω
      by_cases h : ω ∈ Sy
      · exact Or.inr h
      · exact Or.inl ⟨hω, h⟩
    calc μ Sx ≤ μ ((Sx ∩ Syᶜ) ∪ Sy) := measure_mono hsubs
      _ ≤ μ (Sx ∩ Syᶜ) + μ Sy := measure_union_le _ _
  have hkey : μ Sx - μ Sy ≤ μ (Sx ∩ Syᶜ) := by
    rw [tsub_le_iff_right]
    exact hsub
  have hae : ∀ᵐ ω ∂μ, ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤ := by
    rw [ae_iff]
    simpa using hfin
  have hmeasind : Measurable fun ω : Config V =>
      (Sx ∩ Syᶜ).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    measurable_const.indicator (hSxm.inter hSym.compl)
  have hpt : ∀ᵐ ω ∂μ, c (s(x, y)) * (Sx ∩ Syᶜ).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤
      c (s(x, y)) * ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) := by
    filter_upwards [hae] with ω hω
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hx : x ∈ cluster ω o
    · by_cases hy : y ∈ cluster ω o
      · have hnot : ω ∉ Sx ∩ Syᶜ := fun h => h.2 (by simpa [hSydef] using hy)
        simp [Set.indicator, hnot, hx, hy]
      · have hmem : ω ∈ Sx ∩ Syᶜ := by
          refine ⟨?_, ?_⟩
          · simpa [hSxdef] using hx
          · simpa [hSydef] using hy
        have hb : (1 : ℝ≥0∞) ≤ ((cluster ω y).encard : ℝ≥0∞) := by
          have h1 := Set.one_le_encard_iff_nonempty.2
            (⟨y, mem_cluster_self ω y⟩ : (cluster ω y).Nonempty)
          exact_mod_cast h1
        have hinc := one_le_crossing_increment p hp hω hb
        simp only [Set.indicator_of_mem hmem]
        simpa [hx, hy] using hinc
    · have hnot : ω ∉ Sx ∩ Syᶜ := fun h => hx (by simpa [hSxdef] using h.1)
      simp [Set.indicator, hnot, hx]
  have hInt : c (s(x, y)) * μ (Sx ∩ Syᶜ) ≤
      ∫⁻ ω, c (s(x, y)) * (Sx ∩ Syᶜ).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
    rw [lintegral_const_mul _ hmeasind,
      lintegral_indicator_const (hSxm.inter hSym.compl) (1 : ℝ≥0∞), one_mul]
  calc c (s(x, y)) * ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) -
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ))
      = c (s(x, y)) * (μ Sx - μ Sy) := by rw [hτx, hτy]
    _ ≤ c (s(x, y)) * μ (Sx ∩ Syᶜ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ ∫⁻ ω, c (s(x, y)) * (Sx ∩ Syᶜ).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := hInt
    _ ≤ ∫⁻ ω, c (s(x, y)) * ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ := lintegral_mono_ae hpt
    _ ≤ C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ)
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) := hfac x y

omit [Countable V] in
/-- At `p = 1` the crossing increment is the volume of the `y`-cluster, provided the root
cluster is finite.  This is the case in which `hfac` says precisely that the *two-point*
crossing mass is bounded by `C` times the smaller of the two connection probabilities. -/
theorem crossing_increment_eq_of_one {a b : ℝ≥0∞} (ha : a ≠ ⊤) :
    (a + b) ^ 1 - a ^ 1 = b := by
  rw [pow_one, pow_one, add_comm]
  exact ENNReal.add_sub_cancel_right ha

omit [Countable V] in
open Classical in
/-- **`hfac` at `p = 1` is a two-point crossing-mass bound.**  On the a.e.-finite root cluster
the `p = 1` left-hand side of `hfac` is the integral of the crossing indicator times `|K_y|`. -/
theorem lintegral_crossing_one_eq {μ : Measure (Config V)} {o : V}
    (c : Sym2 V → ℝ≥0∞) (x y : V)
    (hfin : μ {ω : Config V | ((cluster ω o).encard : ℝ≥0∞) = ⊤} = 0) :
    ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ 1 -
            ((cluster ω o).encard : ℝ≥0∞) ^ 1)) ∂μ =
      ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((cluster ω y).encard : ℝ≥0∞)) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [show ∀ᵐ ω ∂μ, ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤ from by
    rw [ae_iff]; simpa using hfin] with ω hω
  rw [crossing_increment_eq_of_one hω]

end PercLib.Percolation.Bond
