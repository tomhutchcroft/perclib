/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Mathematical reference: the restoration-map argument for
functionals of two distinct clusters in a countable independent product model, together with the
monotonicity of the cut-off family in its scale.

No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.RestorationWindow.Defs
public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Models.LongRange.PowerLawFluxAssembly

/-!
# One finite window for the whole restoration family on a scale interval

`PercLib.Percolation.Bond.RestorationFibreMajorant` discharges the two fibre hypotheses of the
pivotal window series at a *single* scale, with the explicit vertex weights

`gx x = ∑_{l<p} C(p,l) · #S · K · (B_l x · M_{p-l})`,
`gy y = ∑_{l<p} C(p,l) · (K · ∑_{z ∈ S} B_l (z+y)) · M_{p-l}`,

where `B_l x = ∫⁻ 1{x ∈ K_o} |K_o| ^ l` and `M_m = ∫⁻ |K_o| ^ m`.  Those weights depend on the
scale: `B_l`, `M_m` and the range set `S` all change with the cut-off radius.  The small-tail input
`hwin` of the cut-off moment derivative is however needed *uniformly* near a scale, with one finite
window `W` and one bound `E` for every radius of a neighbourhood.

This file proves that uniformity:

* `lintegral_root_monomial_cutoffKernel_mono`, `lintegral_root_pow_cutoffKernel_mono` — **scale
  monotonicity** of the vertex masses and of the root moments, from
  `lintegral_cutoffKernel_mono` (every increasing measurable functional of the configuration
  increases with the scale).  This is the only place cut-off monotonicity enters;
* `tsum_increment_fibre_le_left_uniform`, `tsum_increment_fibre_le_right_uniform` — the fibre
  weights at scale `r ≤ v` are dominated by their values at the *top* scale `v`, with the range set
  `S` read once at `v` and one root-moment majorant `M_p(v)`.  The whole `l < p` binomial sum, the
  `#S` factor and the dilated root-index translation are thereby frozen at `v`;
* `exists_window_uniform_hwin` — the exterior mass of the frozen weight `gx_top + gy_top` is
  summable and small outside one finite window, so **one** `W` works for every scale of the
  interval, with the scale-independent bound `E = ∑' x ∉ W, (gx_top x + gy_top x)`.

## What this file does and does not give

It gives `hwin` with a single `W` and a single `E` on `Iic v`, hence the literal `htail` premise of
the derivative interface and the continuity of the whole pivotal flux series.  Nothing here claims a
derivative identity, a critical or all-radius statement, or the paper's Lemma I.4.1 in full.  The
gap factorisation `hfac` is *not* used anywhere in this file: the restoration fibre bounds replace
it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Models.LongRange
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-! ### The cut-off vertex masses and root moments -/

/-! ### Scale monotonicity of the vertex masses and the root moments -/

open Classical in
/-- The configuration functional `1{x ∈ K_o} |K_o| ^ l` is monotone in the configuration. -/
theorem monotone_rootIndicatorPow (o x : Fin d → ℤ) (l : ℕ) :
    Monotone fun ω : Config (Fin d → ℤ) =>
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * ((cluster ω o).encard : ℝ≥0∞) ^ l := by
  intro ω ω' hω
  have hsub : cluster ω o ⊆ cluster ω' o := cluster_mono hω o
  have hcard : ((cluster ω o).encard : ℝ≥0∞) ≤ ((cluster ω' o).encard : ℝ≥0∞) :=
    ENat.toENNReal_mono (encard_le_encard hsub)
  change (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * ((cluster ω o).encard : ℝ≥0∞) ^ l ≤
    (if x ∈ cluster ω' o then (1 : ℝ≥0∞) else 0) * ((cluster ω' o).encard : ℝ≥0∞) ^ l
  by_cases hx : x ∈ cluster ω o
  · rw [ite_eq_left hx, ite_eq_left (hsub hx), one_mul, one_mul]
    exact pow_le_pow_left' hcard l
  · rw [ite_eq_right hx, zero_mul]
    exact zero_le

open Classical in
theorem measurable_rootIndicatorPow (o x : Fin d → ℤ) (l : ℕ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * ((cluster ω o).encard : ℝ≥0∞) ^ l :=
  (Measurable.ite (measurableSet_conn o x) measurable_const measurable_const).mul
    ((measurable_encard_cluster_toENNReal o).pow_const l)

theorem monotone_encardPow (o : Fin d → ℤ) (m : ℕ) :
    Monotone fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) ^ m := by
  intro ω ω' hω
  exact pow_le_pow_left' (ENat.toENNReal_mono (encard_le_encard (cluster_mono hω o))) m

/-- **The root vertex masses increase with the cut-off scale.** -/
theorem lintegral_root_monomial_cutoffKernel_mono {K : ℝ → ℝ} {N : Analysis.ModelNorm (Fin d → ℝ)}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {r ρ : ℝ} (hrρ : r ≤ ρ) (o : Fin d → ℤ) (l : ℕ)
    (x : Fin d → ℤ) :
    rootWeight (law (intensityProfile (cutoffKernel (d := d) N K r) β)) o l x ≤
      rootWeight (law (intensityProfile (cutoffKernel (d := d) N K ρ) β)) o l x := by
  simpa only [rootWeight] using
    lintegral_cutoffKernel_mono (N := N) (K := K) hK hrρ
      (measurable_rootIndicatorPow o x l) (monotone_rootIndicatorPow o x l)

/-- **The root volume moments increase with the cut-off scale.** -/
theorem lintegral_root_pow_cutoffKernel_mono {K : ℝ → ℝ} {N : Analysis.ModelNorm (Fin d → ℝ)}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {r ρ : ℝ} (hrρ : r ≤ ρ) (o : Fin d → ℤ) (m : ℕ) :
    rootMoment (law (intensityProfile (cutoffKernel (d := d) N K r) β)) o m ≤
      rootMoment (law (intensityProfile (cutoffKernel (d := d) N K ρ) β)) o m := by
  simpa only [rootMoment] using
    lintegral_cutoffKernel_mono (N := N) (K := K) hK hrρ
      ((measurable_encard_cluster_toENNReal o).pow_const m) (monotone_encardPow o m)

/-- A lower root moment is dominated by the `p`-th one: a cluster has at least one vertex. -/
theorem rootMoment_le_of_le (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) {m p : ℕ}
    (hmp : m ≤ p) : rootMoment μ o m ≤ rootMoment μ o p := by
  refine lintegral_mono fun ω => ?_
  have h1 : (1 : ℝ≥0∞) ≤ ((cluster ω o).encard : ℝ≥0∞) := by
    simpa using ENat.toENNReal_mono (one_le_encard_cluster ω o)
  exact pow_le_pow_right' h1 hmp

/-! ### The pair weight `1{N (·) < r}` is bounded by `1` -/

theorem radialKernel_indicator_coe_le_one {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ}
    (e : Sym2 (Fin d → ℤ)) :
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) ≤ 1 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [radialKernel_diag]
      simp
    · rw [radialKernel_of_ne hxy]
      split_ifs with h
      · rw [Real.toNNReal_one]; norm_num
      · rw [Real.toNNReal_zero]; simp

/-! ### Scale monotonicity of the dilated vertex mass -/

open Classical in
/-- **The dilated vertex masses increase with the cut-off scale.** -/
theorem dilatedRootWeight_mono {K : ℝ → ℝ} {N : Analysis.ModelNorm (Fin d → ℝ)}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {r ρ : ℝ} (hrρ : r ≤ ρ) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (l : ℕ) (y : Fin d → ℤ) :
    dilatedRootWeight (law (intensityProfile (cutoffKernel (d := d) N K r) β)) o S l y ≤
      dilatedRootWeight (law (intensityProfile (cutoffKernel (d := d) N K ρ) β)) o S l y := by
  refine Finset.sum_le_sum fun z _ => ?_
  simpa only [rootWeight] using
    lintegral_root_monomial_cutoffKernel_mono (N := N) (K := K) hK hrρ o l (z + y)

/-! ### The fibre weights, frozen at the top scale -/

open Classical in
/-- **The `x`-fibre hypothesis, uniformly for every scale below `v`.**

The truncated pivotal increment at scale `r ≤ v` is bounded by the frozen weight
`topWeightLeft μ_v o S p M_p(v)`, in which the `l < p` binomial sum, the `#S` factor, the pair
bound `1`, the range set `S` read at `v` and the root moment majorant `M_p(v)` are all
scale-independent. -/
theorem tsum_increment_fibre_le_left_uniform {N : Analysis.ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {v : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p) {r : ℝ} (hrv : r ≤ v)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (hKb : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ 1)
    (hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p ≠ ⊤)
    (x : Fin d → ℤ) :
    ∑' y : Fin d → ℤ, ∫⁻ ω,
        c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))
      ≤ topWeightLeft (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
          (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p) x := by
  have hSp : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S :=
    fun z hz => hS z (lt_of_lt_of_le hz hrv)
  have hroot := fun (m : ℕ) (y : Fin d → ℤ) =>
    lintegral_encard_pow_cutoffKernel_eq (N := N) (K := K) r β m y o
  have hmomr : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K r) β)) o p ≠ ⊤ :=
    ne_top_of_le_ne_top hmomv
      (lintegral_root_pow_cutoffKernel_mono (N := N) (K := K) hK hrv o p)
  have key := tsum_increment_fibre_le_left (N := N) (r := r) (S := S) hSp
    (q := intensityProfile (cutoffKernel (d := d) N K r) β) (o := o) (p := p) (hp := hp)
    (c := c) (hcsupp := hcsupp) (K := 1) (hK := hKb)
    (hroot := hroot) (hmom := hmomr) (x := x)
  refine le_trans key ?_
  refine Finset.sum_le_sum fun l _ =>
    mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
  refine mul_le_mul' (lintegral_root_monomial_cutoffKernel_mono (N := N) (K := K) hK hrv o l x) ?_
  exact le_trans (lintegral_root_pow_cutoffKernel_mono (N := N) (K := K) hK hrv o (p - l))
    (rootMoment_le_of_le _ o (Nat.sub_le p l))

open Classical in
/-- **The `y`-fibre hypothesis, uniformly for every scale below `v`.** -/
theorem tsum_increment_fibre_le_right_uniform {N : Analysis.ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {v : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p) {r : ℝ} (hrv : r ≤ v)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (hKb : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ 1)
    (hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p ≠ ⊤)
    (y : Fin d → ℤ) :
    ∑' x : Fin d → ℤ, ∫⁻ ω,
        c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))
      ≤ topWeightRight (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
          (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p) y := by
  have hSp : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S :=
    fun z hz => hS z (lt_of_lt_of_le hz hrv)
  have hroot := fun (m : ℕ) (y : Fin d → ℤ) =>
    lintegral_encard_pow_cutoffKernel_eq (N := N) (K := K) r β m y o
  have hmomr : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K r) β)) o p ≠ ⊤ :=
    ne_top_of_le_ne_top hmomv
      (lintegral_root_pow_cutoffKernel_mono (N := N) (K := K) hK hrv o p)
  have key := tsum_increment_fibre_le_right (N := N) (r := r) (S := S) hSp
    (q := intensityProfile (cutoffKernel (d := d) N K r) β) (o := o) (p := p) (hp := hp)
    (c := c) (hcsupp := hcsupp) (K := 1) (hK := hKb)
    (hroot := hroot) (hmom := hmomr) (y := y)
  refine le_trans key ?_
  refine Finset.sum_le_sum fun l _ =>
    mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl ?_) ?_)
  · exact dilatedRootWeight_mono (N := N) (K := K) hK hrv o S l y
  · exact le_trans (lintegral_root_pow_cutoffKernel_mono (N := N) (K := K) hK hrv o (p - l))
      (rootMoment_le_of_le _ o (Nat.sub_le p l))

/-! ### The frozen weights are spatially summable -/

open Classical in
/-- A finite sum of `ℝ≥0∞`-valued terms is not `⊤` as soon as each summand is not. -/
theorem finset_sum_ne_top {ι : Type*} (s : Finset ι) (g : ι → ℝ≥0∞)
    (h : ∀ i ∈ s, g i ≠ ⊤) : ∑ i ∈ s, g i ≠ ⊤ := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ENNReal.add_ne_top.2 ⟨h a (Finset.mem_insert_self a s),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

theorem indicatorPairWeight_def {N : Seminorm ℝ (Fin d → ℝ)} (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) :
    indicatorPairWeight (N := N) r e =
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞) := rfl

theorem indicatorPairWeight_hcsupp {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} :
    ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r →
      indicatorPairWeight (N := N) r (s(x, y)) = 0 :=
  radialKernel_indicator_hcsupp

theorem indicatorPairWeight_le_one {N : Seminorm ℝ (Fin d → ℝ)} {r : ℝ} :
    ∀ x y : Fin d → ℤ, indicatorPairWeight (N := N) r (s(x, y)) ≤ 1 :=
  fun _ _ => radialKernel_indicator_coe_le_one _

open Classical in
/-- The defining equation of the frozen `x`-weight. -/
theorem topWeightLeft_apply (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (Mt : ℝ≥0∞) (x : Fin d → ℤ) :
    topWeightLeft μ o S p Mt x =
      ∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
        ((S.card : ℝ≥0∞) * (1 * (rootWeight μ o l x * Mt))) := rfl

open Classical in
/-- The defining equation of the frozen `y`-weight. -/
theorem topWeightRight_apply (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (Mt : ℝ≥0∞) (y : Fin d → ℤ) :
    topWeightRight μ o S p Mt y =
      ∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
        ((1 * dilatedRootWeight μ o S l y) * Mt) := rfl

open Classical in
/-- **The frozen `x`-weight has finite total mass.**  Its `l`-th summand is a finite multiple of
`∑'_x B_l(x) · M_p(v)`, and `∑'_x B_l(x) = ∫⁻ |K_o| ^ (l+1)` is finite because `l + 1 ≤ p`. -/
theorem tsum_topWeightLeft_body_ne_top (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (hmom : rootMoment μ o p ≠ ⊤) :
    ∑' x : Fin d → ℤ, (∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
      ((S.card : ℝ≥0∞) * (1 * (rootWeight μ o l x * rootMoment μ o p)))) ≠ ⊤ := by
  have hterm : ∀ l ∈ Finset.range p,
      (∑' x : Fin d → ℤ, (p.choose l : ℝ≥0∞) *
        ((S.card : ℝ≥0∞) * (1 * (rootWeight μ o l x * rootMoment μ o p)))) ≠ ⊤ := by
    intro l hl
    have hl1 : l + 1 ≤ p := by have := Finset.mem_range.1 hl; omega
    have hB : ∑' x : Fin d → ℤ, rootWeight μ o l x ≠ ⊤ := by
      simpa only [rootWeight] using tsum_lintegral_root_monomial_ne_top μ o hl1 hmom
    have heq : (∑' x : Fin d → ℤ, (p.choose l : ℝ≥0∞) *
          ((S.card : ℝ≥0∞) * (1 * (rootWeight μ o l x * rootMoment μ o p)))) =
        (p.choose l : ℝ≥0∞) * ((S.card : ℝ≥0∞) *
          (1 * ((∑' x : Fin d → ℤ, rootWeight μ o l x) * rootMoment μ o p))) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [ENNReal.tsum_mul_right]
    rw [heq]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hB hmom)))
  rw [Summable.tsum_finsetSum (fun l _ => ENNReal.summable)]
  exact finset_sum_ne_top _ _ hterm

open Classical in
/-- The frozen `x`-weight is summable, phrased through its defining equation. -/
theorem tsum_topWeightLeft_ne_top (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (hmom : rootMoment μ o p ≠ ⊤) :
    ∑' x : Fin d → ℤ, topWeightLeft μ o S p (rootMoment μ o p) x ≠ ⊤ := by
  simpa only [topWeightLeft] using tsum_topWeightLeft_body_ne_top μ o S p hmom

open Classical in
/-- **The frozen `y`-weight (the dilated one) has finite total mass.**  Summed over `y`, the
dilated weight `∑_{z ∈ S} B_l(z+y)` is `#S` times the mass of `B_l`, by the translation bijection
of the lattice; this is `tsum_dilated_root_monomial_ne_top`. -/
theorem tsum_topWeightRight_body_ne_top (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (hmom : rootMoment μ o p ≠ ⊤) :
    ∑' y : Fin d → ℤ, (∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
      ((1 * dilatedRootWeight μ o S l y) * rootMoment μ o p)) ≠ ⊤ := by
  have hterm : ∀ l ∈ Finset.range p,
      (∑' y : Fin d → ℤ, (p.choose l : ℝ≥0∞) *
        ((1 * dilatedRootWeight μ o S l y) * rootMoment μ o p)) ≠ ⊤ := by
    intro l hl
    have hl1 : l + 1 ≤ p := by have := Finset.mem_range.1 hl; omega
    have hD : ∑' y : Fin d → ℤ, dilatedRootWeight μ o S l y ≠ ⊤ := by
      simpa only [dilatedRootWeight] using tsum_dilated_root_monomial_ne_top μ o S hl1 hmom
    have heq : (∑' y : Fin d → ℤ, (p.choose l : ℝ≥0∞) *
          ((1 * dilatedRootWeight μ o S l y) * rootMoment μ o p)) =
        (p.choose l : ℝ≥0∞) * ((1 * (∑' y : Fin d → ℤ, dilatedRootWeight μ o S l y)) *
          rootMoment μ o p) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [ENNReal.tsum_mul_right]
      congr 1
      rw [ENNReal.tsum_mul_left]
    rw [heq]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) hD) hmom)
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact finset_sum_ne_top _ _ hterm

open Classical in
/-- The frozen `y`-weight is summable, phrased through its defining equation. -/
theorem tsum_topWeightRight_ne_top (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) (p : ℕ) (hmom : rootMoment μ o p ≠ ⊤) :
    ∑' y : Fin d → ℤ, topWeightRight μ o S p (rootMoment μ o p) y ≠ ⊤ := by
  simpa only [topWeightRight] using tsum_topWeightRight_body_ne_top μ o S p hmom

/-! ### The uniform window-tail bound -/

open Classical in
/-- **`hwin` at every scale below `v` with one frozen weight.**

The pivotal window series at scale `r ≤ v` (the `ℝ≥0∞` quantity consumed as `hwin` by
`tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail`) is at most the exterior mass of the
*scale-independent* weight `gx_top + gy_top`, for every window `W`.  The two fibre hypotheses are
discharged by `tsum_increment_fibre_le_left_uniform` and `tsum_increment_fibre_le_right_uniform`, so
the binomial coefficients, the range set and the root moments are all read once, at `v`. -/
theorem lintegral_pivotal_window_tail_le_uniform {N : Analysis.ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {v : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p) {r : ℝ} (hrv : r ≤ v)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (hKb : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ 1)
    (hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p ≠ ⊤)
    (W : Finset (Fin d → ℤ)) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))
      ≤ (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
            topWeightLeft (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
              (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p) x)
        + ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) *
            topWeightRight (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
              (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p) y :=
  lintegral_pivotal_window_tail_le_of_fibre_majorant
    (μ := law (intensityProfile (cutoffKernel (d := d) N K r) β)) (o := o) (p := p)
    (c := c) (W := W)
    (gx := topWeightLeft (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
      (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p))
    (gy := topWeightRight (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
      (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p))
    (fun x => tsum_increment_fibre_le_left_uniform (N := N) (K := K) hK S hS o p hp hrv
      c hcsupp hKb hmomv x)
    (fun y => tsum_increment_fibre_le_right_uniform (N := N) (K := K) hK S hS o p hp hrv
      c hcsupp hKb hmomv y)

open Classical in
/-- **The uniform window-tail bound for the indicator pair weight.**  The concrete form of
`lintegral_pivotal_window_tail_le_uniform` at the radially truncated unit pair weight: the only
hypothesis on the pair weight (`hcsupp`, `hKb`) is discharged by the indicator profile. -/
theorem lintegral_pivotal_window_tail_indicator_le_uniform
    {N : Analysis.ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {v : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p) {r : ℝ} (hrv : r ≤ v)
    (hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p ≠ ⊤)
    (W : Finset (Fin d → ℤ)) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * indicatorPairWeight (N := N.toSeminorm) r e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))
      ≤ (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
            topWeightLeft (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
              (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p) x)
        + ∑' y : Fin d → ℤ, (if y ∈ W then (0 : ℝ≥0∞) else 1) *
            topWeightRight (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p
              (rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p) y :=
  lintegral_pivotal_window_tail_le_uniform (N := N) (K := K) hK S hS o p hp hrv
    (indicatorPairWeight (N := N.toSeminorm) r)
    indicatorPairWeight_hcsupp indicatorPairWeight_le_one hmomv W

open Classical in
/-- **One finite window gives `hwin` uniformly on `Iic v`.**

For every `δ > 0` there is a single finite vertex window `W` such that, for **every** scale
`r ≤ v`, the pivotal window series at `r` (with the pairs of `W × W` excluded) is at most `δ`.
No per-scale window, no gap factorisation and no additional smallness of the cut-off intensity is
used: the only inputs are the scale monotonicity of the cut-off family, the finite range set `S` at
`v`, and the finite `p`-th root moment at `v`. -/
theorem exists_window_uniform_hwin {N : Analysis.ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {v : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p ≠ ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ W : Finset (Fin d → ℤ), ∀ r ∈ Iic v,
      ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
          ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
            then (0 : ℝ≥0∞) else 1) * indicatorPairWeight (N := N.toSeminorm) r e) *
            (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤ δ := by
  set Mt : ℝ≥0∞ :=
    rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p with hMt
  set TL : (Fin d → ℤ) → ℝ≥0∞ :=
    topWeightLeft (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p Mt with hTL
  set TR : (Fin d → ℤ) → ℝ≥0∞ :=
    topWeightRight (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o S p Mt with hTR
  have hmomMt : Mt ≠ ⊤ := hmomv
  have hL : ∑' x : Fin d → ℤ, TL x ≠ ⊤ := by
    rw [hTL]; exact tsum_topWeightLeft_ne_top _ o S p hmomv
  have hR : ∑' x : Fin d → ℤ, TR x ≠ ⊤ := by
    rw [hTR]; exact tsum_topWeightRight_ne_top _ o S p hmomv
  have hsum : ∑' x : Fin d → ℤ, (TL x + TR x) ≠ ⊤ := by
    rw [ENNReal.tsum_add]; exact ENNReal.add_ne_top.2 ⟨hL, hR⟩
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le_of_tsum_ne_top
    (fun x : Fin d → ℤ => TL x + TR x) hsum hδ
  refine ⟨W, fun r hrv => ?_⟩
  refine le_trans (lintegral_pivotal_window_tail_indicator_le_uniform (N := N) (K := K) hK S hS
    o p hp hrv hmomv W) ?_
  rw [← hTL, ← hTR]
  refine le_trans (le_of_eq ?_) hW
  rw [← ENNReal.tsum_add, ← tsum_ite_mem_eq_tsum_compl W (fun x : Fin d → ℤ => TL x + TR x)]
  exact tsum_congr fun x => (mul_add _ _ _).symm

end PercLib.Percolation.Bond

/-! ## The power-law `htail` and flux continuity, from the restoration bound -/

open PercLib.Percolation.Bond
open PercLib.Analysis

namespace PercLib.Models.LongRange

/-! ## The local small-tail estimate, from the restoration fibre bounds -/

open Classical in
/-- **The `htail` premise at the sup-norm power law, from the restoration fibre bounds.**

For `1 ≤ d`, `α > 0`, the high-temperature row-sum condition `β M < 1`, every order `p ≥ 1`, every
root `o` and every `r₀ ∈ (5/4, 8/5)`, the real-norm tail of the cut-off pivotal series outside one
finite pair set is arbitrarily small on a neighbourhood of `r₀`.  Compared with
`exists_nhds_htail_powerLaw_of_factorization` the gap factorisation `hfac` and the gap constant `C`
are gone; the finite window comes from `exists_window_uniform_hwin`. -/
theorem exists_nhds_htail_powerLaw_of_restoration {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) (r₀ : ℝ)
    (hr₀ : r₀ ∈ Ioo (5 / 4 : ℝ) (8 / 5)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo (5 / 4 : ℝ) (8 / 5), ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖((radialKernel (normSeminorm ℝ (Fin d → ℝ))
              (fun s => if s < r then 1 else 0) e.1 : ℝ) *
            ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
                (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
              Real.exp (-(β : ℝ) *
                (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                  (powerLawProfile 1 ((d : ℝ) + α)) r e.1 : ℝ)))) *
          ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖ ≤ ε := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  have hK : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  obtain ⟨M, hM, hroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ o p
    (u := 5 / 4) (v := 8 / 5) (R := 8 / 5) (by norm_num) (by norm_num)
  have hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K (8 / 5)) β)) o p
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top hM (le_trans (rootMoment_le_of_le _ o (Nat.le_succ p)) ?_)
    simpa only [rootMoment, N, K, ModelNorm.toSeminorm_ofNorm] using hroot (8 / 5) (Or.inr rfl)
  obtain ⟨S, hS⟩ := exists_finset_powerLaw_ball d
  have hS' : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < 8 / 5 → z ∈ S := by
    intro z hz
    have hz' : N.toSeminorm (Int.cast ∘ z) < 8 / 5 := hz
    exact hS z (by simpa only [N, ModelNorm.toSeminorm_ofNorm] using hz')
  have hε'pos : 0 < ε / ((β : ℝ) * ((d : ℝ) + α) * (5 / 4 : ℝ) ^ (-((d : ℝ) + α) - 1) + 1) :=
    div_pos hε (by positivity)
  set Λ : ℝ := (β : ℝ) * ((d : ℝ) + α) * (5 / 4 : ℝ) ^ (-((d : ℝ) + α) - 1) with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  obtain ⟨W, hW⟩ := exists_window_uniform_hwin (N := N) (K := K) hK S hS' o p hp hmomv
    (δ := ENNReal.ofReal (ε / (Λ + 1))) (ENNReal.ofReal_pos.2 hε'pos)
  have hins : ∀ r ∈ Iio (8 / 5 : ℝ) ∩ Ioo (5 / 4 : ℝ) (8 / 5), ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
    intro r hr e
    have hrv : r ∈ Ioo (5 / 4 : ℝ) (8 / 5) := hr.2
    have h1 : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hM (le_trans (rootMoment_le_of_le _ o (Nat.le_succ p)) ?_)
      simpa only [rootMoment, N, K, ModelNorm.toSeminorm_ofNorm] using hroot r (Or.inl hrv)
    have h10 : (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
      have hrootind := lintegral_encard_pow_cutoffKernel_eq (d := d) (N := N.toSeminorm)
        (K := K) r β p o 0
      rw [← hrootind]
      exact h1
    have h3 : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ :=
      fun y => vertex_moment_ne_top_of_root_moment (N := N) (K := K) β r p y h10
    exact insert_moments_of_vertex_moments (N := N.toSeminorm) (K := K) β p r o h3 e
  refine exists_nhds_window_htail_of_uniform_lintegral_window_tail (N := N) (K := K) (K' := K')
    β p hp o _ (fun _ _ => rfl) W hr₀ (Iio (8 / 5)) (isOpen_Iio.mem_nhds hr₀.2) ε
    (fun _ => ENNReal.ofReal (ε / (Λ + 1))) ?_ hins ?_ ?_
  · intro r hr
    exact ENNReal.ofReal_ne_top
  · intro r hr
    have hrv : r ∈ Ioo (5 / 4 : ℝ) (8 / 5) := hr.2
    have h := hW r (le_of_lt hrv.2)
    simpa only [indicatorPairWeight_def, N, K, ModelNorm.toSeminorm_ofNorm] using h
  · intro r hr
    have hrv : r ∈ Ioo (5 / 4 : ℝ) (8 / 5) := hr.2
    have hle : |(β : ℝ) * -K' r| ≤ Λ := by
      rw [hΛdef]
      simpa only [K'] using exists_powerLaw_rate_bound (d := d) hα β r hrv
    have hE : (ENNReal.ofReal (ε / (Λ + 1))).toReal = ε / (Λ + 1) :=
      ENNReal.toReal_ofReal hε'pos.le
    rw [hE]
    calc |(β : ℝ) * -K' r| * (ε / (Λ + 1)) ≤ Λ * (ε / (Λ + 1)) :=
          mul_le_mul_of_nonneg_right hle hε'pos.le
      _ = ε * (Λ / (Λ + 1)) := by field_simp
      _ ≤ ε * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          exact (div_lt_one (by linarith : (0 : ℝ) < Λ + 1)).2 (by linarith) |>.le
      _ = ε := mul_one ε

open Classical in
/-- **Continuity of the whole pivotal flux series at the sup-norm power law, from the restoration
fibre bounds.**  On the corner-free window `(5/4, 8/5)`, at every order `p ≥ 1`, the flux series is
continuous in the cut-off radius, with no gap factorisation and no gap constant.

Every input of production's continuity interface
`continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail` is constructed here: the higher root
moment `M` at the top scale, the corner-free window, the derivative rate and the local small-tail
estimate `exists_nhds_htail_powerLaw_of_restoration`.  This is the `hflux_cont` hypothesis of
`hasDerivAt_uncappedMoment_powerLaw_of_flux` at any interior scale, in particular `r₀ = 3/2`.
The window does not contain `5/2`; the generalization to arbitrary valid corner-free intervals is
in `Models/LongRange/RestorationDerivativeGeneral`. -/
theorem continuousOn_flux_powerLaw_of_restoration {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) :
    ContinuousOn (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(β : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo (5 / 4 : ℝ) (8 / 5)) := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  obtain ⟨M, hM, hroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := 5 / 4) (v := 8 / 5) (R := 8 / 5) (by norm_num) (by norm_num)
  have hK : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t :=
    fun t ht => hasDerivAt_powerLawProfile_add 1 α ht
  have hK'c : ContinuousOn K' (Ioi 0) := continuousOn_powerLawProfile_deriv_add (d := d) 1 α
  have hcorner : ∀ z : Fin d → ℤ,
      normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) ∉ Ioo (5 / 4 : ℝ) (8 / 5) := by
    apply corner_free_of_forall_nat_notMem (d := d)
    intro m hm
    have h1 : (1 : ℝ) < (m : ℝ) := by linarith [hm.1]
    have h2 : (m : ℝ) < 2 := by linarith [hm.2]
    have h1' : 1 < m := by exact_mod_cast h1
    have h2' : m < 2 := by exact_mod_cast h2
    omega
  have hroot' : ∀ r ∈ (Ioo (5 / 4 : ℝ) (8 / 5) ∪ {(8 / 5 : ℝ)} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
    intro r hr
    simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot r hr
  exact continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail (N := N) (K := K) (K' := K')
    hK hK' hK'c β p hp M hM _ (fun _ _ => rfl) (u := 5 / 4) (v := 8 / 5) (R := 8 / 5)
    (by norm_num) le_rfl hcorner hroot'
    (fun r₀ hr₀ ε hε => exists_nhds_htail_powerLaw_of_restoration hd hα hβ p hp 0 r₀ hr₀ ε hε)

end PercLib.Models.LongRange
