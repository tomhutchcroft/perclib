/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Mathematical reference: the restoration-map argument for
functionals of two distinct clusters in a countable independent product model, extended to the
monomials of the truncated pivotal increment.
No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.WindowFibreMajorant
public import PercLib.Percolation.Bond.ClusterCorrelation.FunctionalChain
public import PercLib.Models.LongRange.RootIndependence

/-! # Fibre majorants for the truncated pivotal increment, from the restoration chain

`PercLib.Percolation.Bond.WindowFibreMajorant` reduces the window small-tail input of the cut-off
moment derivative to two *fibre* hypotheses — the sums over `y` and over `x` of the pivotal pair
masses, dominated by vertex weights `gx` and `gy` — and leaves them open.  This file produces them,
from the restoration chain `PercLib.Percolation.Bond.lintegral_indicator_compl_conn_mul_le_mul`
(`PercLib.Percolation.Bond.ClusterCorrelation.FunctionalChain`) and not from a per-pair gap
factorisation.

## The restoration step

`lintegral_monomial_compl_le_mul`: for the monomial `1{x ∈ K_o} 1{y ∉ K_o} |K_o| ^ l |K_y| ^ m`,

`∫⁻ 1{x∈K_o} 1{y∉K_o} (|K_o|^l |K_y|^m) ≤ (∫⁻ 1{x∈K_o} 1{y∉K_o} |K_o|^l) · (∫⁻ |K_y|^m)`.

It is `lintegral_indicator_compl_conn_mul_le_mul` applied with the arbitrary slot
`F = 1{o ∈ ·} 1{y ∉ ·} |·| ^ l` and the increasing slot `G = |·| ^ m`; `K_x = K_o` on `x ∈ K_o`
(`cluster_eq_of_mem_conn`) moves `F` from `K_x` to `K_o`, and the off-cluster indicator is
antisymmetric, so the two indicators on `{x ↮ y}` in the chain are redundant.  The result puts a
`tau`-type factor on **x** and only the constant root moment `∫⁻ |K_y| ^ m` on **y**.

## The two orientations

`tsum_monomial_fibre_le_left`: the `x`-fibre is at most `#S · K · B_l x · M_m`, with the vertex
weight `B_l x = ∫⁻ 1{x ∈ K_o} |K_o| ^ l` carried by `x` itself.
`tsum_monomial_fibre_le_right`: the `y`-fibre is at most `(K · ∑_{z ∈ S} B_l (z+y)) · M_m`, a
*dilated* weight: the chain gives no `tau`-type factor at `y`, so the surviving decay is that of
`B_l` on the finitely many neighbours `y + S`.  The two weights are different and neither dominates
the other vertexwise; this is the asymmetry the direction asked to identify.  No `min`, no per-pair
bound and no translation invariance of the pair weight is used — only its range and its bound.

## Assembly

`tsum_increment_fibre_le_left`, `tsum_increment_fibre_le_right`: the binomial split
`tsum_lintegral_pow_sub_le_sum_monomial` of the truncated increment (with the a.e. finiteness of the
root cluster from `ae_encard_cluster_ne_top_of_lintegral_pow_ne_top`) reduces the increment to the
monomials of exponents `< p`, and each monomial fibre is bounded above.  The resulting weights are

`gx x = ∑_{l<p} C(p,l) · #S · K · (B_l x · M_{p-l})`,
`gy y = ∑_{l<p} C(p,l) · (K · ∑_{z ∈ S} B_l (z+y)) · M_{p-l}`.

`lintegral_pivotal_series_le_of_restoration` feeds exactly these into
`lintegral_pivotal_series_le_of_fibre_majorant`: the pivotal window series of the `p`-th truncated
cluster moment at the pair weight `pwt · c` is at most `∑'_x w x · gx x + ∑'_y w y · gy y`.

## The weights are spatially summable

`lintegral_root_pow_le_of_le`, `tsum_lintegral_root_monomial_ne_top`,
`exists_window_exterior_root_weight_le`: `∑'_x B_l x = ∫⁻ |K_o| ^ (l+1) ≠ ⊤` and one finite window
makes the exterior mass small, whenever `l + 1 ≤ p` and `∫⁻ |K_o| ^ p ≠ ⊤`.
`tsum_dilated_root_monomial_ne_top`, `exists_window_exterior_dilated_le`: the same for the dilated
`y`-weight, by reindexing a translate of the lattice.  So both orientations give *finitely summable*
vertex weights with a small window exterior.

## Root independence at the cut-off family

`PercLib.Models.LongRange.lintegral_encard_pow_cutoffKernel_eq`: at the cut-off laws the root
volume moments do not depend on the base vertex (`cutoffKernel_map_add`), which discharges the only
hypothesis of the fibre bounds that is not about the pair weight.

## What this file does and does not give

It does not touch the per-pair gap factorisation, the small-tail premise `htail`, `hwin` or
sharpness, and it asserts no derivative identity.  The two fibre hypotheses are discharged; the
passage from the two exterior masses to `hwin` (choosing `W`, the constants `#S`, `K`, the binomial
coefficients and the finitely many root moments) is not performed here.  No conditional helper of
this file is applied to a paper theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-! ### The restoration step, specialised to a monomial of the increment -/

section Monomial

variable {V : Type*} [Countable V]

open Classical in
/-- **The restoration step for the monomial `1{x in K_o} 1{y notin K_o} |K_o| ^ l |K_y| ^ m`.**

`lintegral_indicator_compl_conn_mul_le_mul` with `F = 1{o in .} 1{y notin .} |.| ^ l` and
`G = |.| ^ m`; the off-cluster indicator and the volume power are moved across the two clusters
with `cluster_eq_of_mem_conn`, and the indicator on `{x not conn y}` in the restoration chain is
redundant because `F (K_x)` already vanishes on `{x conn y}`.

The conclusion keeps a `tau`-type factor on `x` (through `1{x in K_o}`) and only the constant root
moment on `y`; it is *not* a `min` of two vertex masses. -/
theorem lintegral_monomial_compl_le_mul (q : Sym2 V → unitInterval) (o x y : V) (l m : ℕ) :
    ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m) ∂(law q) ≤
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
        (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂(law q)) := by
  classical
  have hGmono : Monotone (fun S : Set V => (S.encard : ℝ≥0∞) ^ m) := fun S T hST =>
    ENNReal.pow_le_pow_left (ENat.toENNReal_mono (Set.encard_mono hST))
  have hFm : Measurable fun ω : Config V =>
      (if o ∈ cluster ω x then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω x then (0 : ℝ≥0∞) else 1) *
        ((cluster ω x).encard : ℝ≥0∞) ^ l := by
    have h1 : Measurable fun ω : Config V => (if o ∈ cluster ω x then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn x o) measurable_const measurable_const
    have h2 : Measurable fun ω : Config V => (if y ∈ cluster ω x then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn x y) measurable_const measurable_const
    exact (h1.mul h2).mul ((measurable_encard_cluster_toENNReal x).pow_const l)
  have hGm : Measurable fun ω : Config V => ((cluster ω y).encard : ℝ≥0∞) ^ m :=
    (measurable_encard_cluster_toENNReal y).pow_const m
  have hmain := lintegral_indicator_compl_conn_mul_le_mul q x y
    (fun S : Set V => (if o ∈ S then (1 : ℝ≥0∞) else 0) *
      (if y ∈ S then (0 : ℝ≥0∞) else 1) * (S.encard : ℝ≥0∞) ^ l)
    (fun S : Set V => (S.encard : ℝ≥0∞) ^ m) hGmono hFm hGm
  have hstep : ∀ ω : Config V,
      (if o ∈ cluster ω x then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω x then (0 : ℝ≥0∞) else 1) *
        ((cluster ω x).encard : ℝ≥0∞) ^ l =
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l := by
    intro ω
    by_cases hxo : x ∈ cluster ω o
    · have heq : cluster ω x = cluster ω o :=
        (cluster_eq_of_mem_conn (x := o) (y := x) hxo).symm
      rw [heq, ite_eq_left (mem_cluster_self ω o), ite_eq_left hxo, one_mul]
    · have hox : o ∉ cluster ω x := fun hc => hxo ((mem_cluster_comm ω x o).1 hc)
      rw [ite_eq_right hox, ite_eq_right hxo]
      simp
  have hzero : ∀ ω : Config V, ω ∈ conn x y →
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l = 0 := by
    intro ω hxy
    by_cases hxo : x ∈ cluster ω o
    · rw [ite_eq_left hxo, ite_eq_left (show y ∈ cluster ω o from conn_trans hxo hxy)]
      simp
    · rw [ite_eq_right hxo]
      simp
  have hind : ∀ ω : Config V,
      (conn x y)ᶜ.indicator (fun ω =>
        ((if o ∈ cluster ω x then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω x then (0 : ℝ≥0∞) else 1) *
          ((cluster ω x).encard : ℝ≥0∞) ^ l) * ((cluster ω y).encard : ℝ≥0∞) ^ m) ω =
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m) := by
    intro ω
    by_cases hxy : ω ∈ conn x y
    · rw [Set.indicator_of_notMem (by simpa using hxy), ← mul_assoc, hzero ω hxy, zero_mul]
    · rw [Set.indicator_of_mem (by simpa using hxy), hstep ω, mul_assoc]
  have hind2 : ∀ ω : Config V,
      (conn x y)ᶜ.indicator (fun ω => (if o ∈ cluster ω x then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω x then (0 : ℝ≥0∞) else 1) *
          ((cluster ω x).encard : ℝ≥0∞) ^ l) ω =
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((cluster ω o).encard : ℝ≥0∞) ^ l := by
    intro ω
    by_cases hxy : ω ∈ conn x y
    · rw [Set.indicator_of_notMem (by simpa using hxy), hzero ω hxy]
    · rw [Set.indicator_of_mem (by simpa using hxy), hstep ω]
  rw [lintegral_congr hind, lintegral_congr hind2] at hmain
  exact hmain

end Monomial
/-! ### The two orientations of the fibre sum -/

section Fibre

variable {d : ℕ}

open Classical in
/-- **The `x`-orientation of the monomial fibre bound.**

The fibre sum over `y` of the monomial mass, weighted by a pair weight `c` that is bounded by `K`
and vanishes outside the `r`-range, is at most `#S * K * (B_l x * M_m)`, where `B_l x` is the
`x`-vertex mass `∫⁻ 1{x ∈ K_o} |K_o| ^ l` and `M_m = ∫⁻ |K_o| ^ m` is the root `m`-th moment
(translation invariant, so the same at `y`).

This is the *first* orientation: the vertex weight is carried by `x` itself, and nothing is assumed
about the pair mass in `y` beyond the range of `c`. -/
theorem tsum_monomial_fibre_le_left {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (o : Fin d → ℤ) (l m : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (K : ℝ≥0∞) (hK : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ K)
    (hroot : ∀ y : Fin d → ℤ, ∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂(law q) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))
    (x : Fin d → ℤ) :
    ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m)) ∂(law q)
      ≤ (S.card : ℝ≥0∞) * (K * ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)))) := by
  classical
  have hmono : ∀ y : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) =>
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m) := by
    intro y
    have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn o x) measurable_const measurable_const
    have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn o y) measurable_const measurable_const
    exact (h1.mul h2).mul (((measurable_encard_cluster_toENNReal o).pow_const l).mul
      ((measurable_encard_cluster_toENNReal y).pow_const m))
  have hDLE : ∀ y : Fin d → ℤ,
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) ≤
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q) := by
    intro y
    refine lintegral_mono fun ω => ?_
    have h2 : (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) ≤ 1 := by
      split_ifs <;> simp
    calc (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) * ((cluster ω o).encard : ℝ≥0∞) ^ l
        ≤ ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * 1) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l :=
          mul_le_mul' (mul_le_mul' le_rfl h2) le_rfl
      _ = (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l := by rw [mul_one]
  have hfibre : ∀ y : Fin d → ℤ,
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m) ∂(law q)) ≤
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) := by
    intro y
    refine le_trans (lintegral_monomial_compl_le_mul q o x y l m) ?_
    exact mul_le_mul' (hDLE y) (le_of_eq (hroot y))
  calc ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m)) ∂(law q)
      = ∑' y : Fin d → ℤ, c (s(x, y)) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
            (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m)
              ∂(law q)) :=
        tsum_congr fun y => lintegral_const_mul _ (hmono y)
    _ ≤ ∑' y : Fin d → ℤ, c (s(x, y)) *
          ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
              ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
            (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))) :=
        ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl (hfibre y)
    _ ≤ (S.card : ℝ≥0∞) * (K * ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)))) :=
        tsum_fibre_le S hS x _ _
          (fun y hy => by rw [hcsupp x y hy]; simp)
          (fun y => mul_le_mul' (hK x y) le_rfl)

open Classical in
/-- **The `y`-orientation of the monomial fibre bound.**

The same monomial mass, now summed over `x` for a fixed `y`.  The vertex weight that comes out is
the *dilated* one: it is the sum of `B_l` over the finite range `y + S` of the pair weight, not
`B_l y`.  This asymmetry is exactly what the restoration chain gives: the chain produces the
`tau`-type factor on its first vertex and a constant on its second, so the surviving spatial decay
in the `y`-fibre is the decay of `B_l` on the finitely many neighbours `y + S` of `y`, not at `y`.

Only the range hypothesis on `c` is used; no translation invariance of `c` is needed (the finite
sum is reindexed by the injective map `z ↦ z + y`, not an infinite sum). -/
theorem tsum_monomial_fibre_le_right {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (o : Fin d → ℤ) (l m : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (K : ℝ≥0∞) (hK : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ K)
    (hroot : ∀ y : Fin d → ℤ, ∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂(law q) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))
    (y : Fin d → ℤ) :
    ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m)) ∂(law q)
      ≤ (K * ∑ z ∈ S, (∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) := by
  classical
  have hm : ∀ x : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) =>
      (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m) := by
    intro x
    have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn o x) measurable_const measurable_const
    have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn o y) measurable_const measurable_const
    exact (h1.mul h2).mul (((measurable_encard_cluster_toENNReal o).pow_const l).mul
      ((measurable_encard_cluster_toENNReal y).pow_const m))
  have hDLE : ∀ x : Fin d → ℤ,
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) ≤
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q) := by
    intro x
    refine lintegral_mono fun ω => ?_
    have h2 : (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) ≤ 1 := by
      split_ifs <;> simp
    calc (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) * ((cluster ω o).encard : ℝ≥0∞) ^ l
        ≤ ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * 1) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l :=
          mul_le_mul' (mul_le_mul' le_rfl h2) le_rfl
      _ = (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l := by rw [mul_one]
  have hfibre : ∀ x : Fin d → ℤ,
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m) ∂(law q)) ≤
      (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) := by
    intro x
    refine le_trans (lintegral_monomial_compl_le_mul q o x y l m) ?_
    exact mul_le_mul' (hDLE x) (le_of_eq (hroot y))
  -- only `x ∈ S.image (· + y)` contributes
  have hsupp : ∀ x : Fin d → ℤ, x ∉ S.image (fun z => z + y) →
      c (s(x, y)) * (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) = 0 := by
    intro x hx
    have hxr : ¬ N (Int.cast ∘ (y - x)) < r := by
      have heq : (Int.cast ∘ (y - x) : Fin d → ℝ) = -(Int.cast ∘ (x - y)) := by
        funext i
        simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply]
        push_cast
        ring
      rw [heq, map_neg_eq_map]
      intro hlt
      exact hx (Finset.mem_image.2 ⟨x - y, hS (x - y) hlt, by abel⟩)
    rw [hcsupp x y hxr, zero_mul]
  have hchain : ∑' x : Fin d → ℤ, c (s(x, y)) *
        (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))
      ≤ K * ∑ z ∈ S, (∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) := by
    rw [tsum_eq_sum hsupp]
    calc ∑ x ∈ S.image (fun z => z + y), c (s(x, y)) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))
        ≤ ∑ x ∈ S.image (fun z => z + y), K *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul' (hK x y) le_rfl
      _ = K * ∑ x ∈ S.image (fun z => z + y),
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) := (Finset.mul_sum _ _ _).symm
      _ = K * ∑ z ∈ S, (∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          simpa using hab
  have hassoc : ∑' x : Fin d → ℤ, c (s(x, y)) *
        ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)))
      = (∑' x : Fin d → ℤ, c (s(x, y)) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
        (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) := by
    rw [show (∑' x : Fin d → ℤ, c (s(x, y)) *
          ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
              ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
            (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))))
        = ∑' x : Fin d → ℤ, (c (s(x, y)) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) from
      tsum_congr fun x => (mul_assoc _ _ _).symm]
    rw [ENNReal.tsum_mul_right]
  calc ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m)) ∂(law q)
      = ∑' x : Fin d → ℤ, c (s(x, y)) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
            (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ m)
              ∂(law q)) :=
        tsum_congr fun x => lintegral_const_mul _ (hm x)
    _ ≤ ∑' x : Fin d → ℤ, c (s(x, y)) *
          ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
              ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
            (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hfibre x)
    _ = (∑' x : Fin d → ℤ, c (s(x, y)) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
        (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) := hassoc
    _ ≤ (K * ∑ z ∈ S, (∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
          (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q)) :=
        mul_le_mul' hchain le_rfl

end Fibre
/-! ### The fibre hypotheses of the pivotal series, discharged -/

section Assembly

variable {d : ℕ}

open Classical in
/-- **The `x`-fibre hypothesis of the pivotal series, discharged.**

The truncated increment of the `p`-th cluster moment is split into its mixed monomials by
`tsum_lintegral_pow_sub_le_sum_monomial` (which needs only the a.e. finiteness of the root cluster,
supplied by the finiteness of the `p`-th root moment), and each monomial is bounded by
`tsum_monomial_fibre_le_left`.  The result is the `hx` obligation of
`lintegral_pivotal_series_le_of_fibre_majorant` with the explicit vertex weight
`gx x = ∑_{l<p} C(p,l) · #S · K · (B_l x · M_{p-l})`.

No gap factorisation, no `min`, and no per-pair hypothesis is used; the only model inputs are the
range of `c` (`hcsupp`), its bound (`hK`), the finite `p`-th root moment (`hmom`) and the
translation invariance of the root volume moments (`hroot`). -/
theorem tsum_increment_fibre_le_left {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (K : ℝ≥0∞) (hK : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ K)
    (hroot : ∀ (m : ℕ) (y : Fin d → ℤ), ∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂(law q) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(law q) ≠ ⊤)
    (x : Fin d → ℤ) :
    ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂(law q)
      ≤ ∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
          ((S.card : ℝ≥0∞) * (K * ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
              ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
            (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p - l) ∂(law q))))) := by
  classical
  have hae : ∀ᵐ ω ∂(law q), ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [ae_encard_cluster_ne_top_of_lintegral_pow_ne_top (d := d)
      (μ := law q) (o := o) (by omega) hmom] with ω hω hcontra
    exact hω (ENat.toENNReal_eq_top.1 hcontra)
  have hu : ∀ y : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) =>
      c (s(x, y)) * ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1)) := by
    intro y
    have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn o x) measurable_const measurable_const
    have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn o y) measurable_const measurable_const
    exact measurable_const.mul (h1.mul h2)
  have hsplit := tsum_lintegral_pow_sub_le_sum_monomial (μ := law q)
    (fun y ω => c (s(x, y)) * ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1)))
    (fun ω => ((cluster ω o).encard : ℝ≥0∞)) (fun y ω => ((cluster ω y).encard : ℝ≥0∞))
    hu (measurable_encard_cluster_toENNReal o)
    (fun y => measurable_encard_cluster_toENNReal y) hae p
  -- reassociate the left-hand side into the shape the split produces
  have hL : ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂(law q)
      = ∑' y : Fin d → ℤ, ∫⁻ ω, (c (s(x, y)) *
          ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1))) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂(law q) :=
    tsum_congr fun y => lintegral_congr fun ω => (mul_assoc _ _ _).symm
  rw [hL]
  refine le_trans hsplit ?_
  refine Finset.sum_le_sum fun l _ => ?_
  refine mul_le_mul' le_rfl ?_
  rw [show (∑' y : Fin d → ℤ, ∫⁻ ω, (c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1))) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ (p - l))
          ∂(law q))
      = ∑' y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ (p - l)))
            ∂(law q) from
    tsum_congr fun y => lintegral_congr fun ω => mul_assoc _ _ _]
  exact tsum_monomial_fibre_le_left S hS q o l (p - l) c hcsupp K hK
    (fun y => hroot (p - l) y) x

open Classical in
/-- **The `y`-fibre hypothesis of the pivotal series, discharged.**

The same construction in the other orientation, through `tsum_monomial_fibre_le_right`.  The vertex
weight is the dilated one, `gy y = ∑_{l<p} C(p,l) · (K · ∑_{z ∈ S} B_l (z + y)) · M_{p-l}`: the
restoration chain leaves no `tau`-type factor at `y` itself. -/
theorem tsum_increment_fibre_le_right {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (K : ℝ≥0∞) (hK : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ K)
    (hroot : ∀ (m : ℕ) (y : Fin d → ℤ), ∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂(law q) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(law q) ≠ ⊤)
    (y : Fin d → ℤ) :
    ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂(law q)
      ≤ ∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
          ((K * ∑ z ∈ S, (∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
              ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
            (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p - l) ∂(law q))) := by
  classical
  have hae : ∀ᵐ ω ∂(law q), ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [ae_encard_cluster_ne_top_of_lintegral_pow_ne_top (d := d)
      (μ := law q) (o := o) (by omega) hmom] with ω hω hcontra
    exact hω (ENat.toENNReal_eq_top.1 hcontra)
  have hu : ∀ x : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) =>
      c (s(x, y)) * ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1)) := by
    intro x
    have h1 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_conn o x) measurable_const measurable_const
    have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
        (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) :=
      Measurable.ite (measurableSet_conn o y) measurable_const measurable_const
    exact measurable_const.mul (h1.mul h2)
  have hsplit := tsum_lintegral_pow_sub_le_sum_monomial (μ := law q)
    (fun x ω => c (s(x, y)) * ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1)))
    (fun ω => ((cluster ω o).encard : ℝ≥0∞)) (fun x ω => ((cluster ω y).encard : ℝ≥0∞))
    hu (measurable_encard_cluster_toENNReal o)
    (fun _ => measurable_encard_cluster_toENNReal y) hae p
  have hL : ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂(law q)
      = ∑' x : Fin d → ℤ, ∫⁻ ω, (c (s(x, y)) *
          ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1))) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂(law q) :=
    tsum_congr fun x => lintegral_congr fun ω => (mul_assoc _ _ _).symm
  rw [hL]
  refine le_trans hsplit ?_
  refine Finset.sum_le_sum fun l _ => ?_
  refine mul_le_mul' le_rfl ?_
  rw [show (∑' x : Fin d → ℤ, ∫⁻ ω, (c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1))) *
        (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ (p - l))
          ∂(law q))
      = ∑' x : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then (0 : ℝ≥0∞) else 1) *
          (((cluster ω o).encard : ℝ≥0∞) ^ l * ((cluster ω y).encard : ℝ≥0∞) ^ (p - l)))
            ∂(law q) from
    tsum_congr fun x => lintegral_congr fun ω => mul_assoc _ _ _]
  exact tsum_monomial_fibre_le_right S hS q o l (p - l) c hcsupp K hK
    (fun y => hroot (p - l) y) y

open Classical in
/-- **The pivotal window series at the cut-off family, without a root-independence input.**

`lintegral_pivotal_series_le_of_restoration` with `q` specialised to the cut-off law and the
hypothesis `hroot` discharged by `lintegral_encard_pow_cutoffKernel_eq`.  The surviving hypotheses
are exactly: a finite set `S` containing the `r`-ball, the vanishing of `c` outside it, a bound `K`
for `c`, the finite `p`-th root moment, and the window data `pwt`, `w`, `hpw`. -/
theorem lintegral_pivotal_series_le_of_restoration {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)}
    {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (o : Fin d → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (K : ℝ≥0∞) (hK : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ K)
    (hroot : ∀ (m : ℕ) (y : Fin d → ℤ), ∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂(law q) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂(law q))
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂(law q) ≠ ⊤)
    (pwt : Sym2 (Fin d → ℤ) → ℝ≥0∞) (w : (Fin d → ℤ) → ℝ≥0∞)
    (hpw : ∀ x y : Fin d → ℤ, pwt (s(x, y)) ≤ w x + w y) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        (pwt e * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂(law q)
      ≤ (∑' x : Fin d → ℤ, w x * (∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
            ((S.card : ℝ≥0∞) * (K * ((∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
                ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q)) *
              (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p - l) ∂(law q)))))))
        + ∑' y : Fin d → ℤ, w y * (∑ l ∈ Finset.range p, (p.choose l : ℝ≥0∞) *
            ((K * ∑ z ∈ S, (∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
                ((cluster ω o).encard : ℝ≥0∞) ^ l ∂(law q))) *
              (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p - l) ∂(law q)))) :=
  lintegral_pivotal_series_le_of_fibre_majorant (law q) o p c pwt w hpw _ _
    (fun x => tsum_increment_fibre_le_left S hS q o p hp c hcsupp K hK hroot hmom x)
    (fun y => tsum_increment_fibre_le_right S hS q o p hp c hcsupp K hK hroot hmom y)

end Assembly

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-- **Root independence of the cut-off volume moments.**  The cut-off kernel is translation
invariant at every scale (`cutoffKernel_map_add`), so the law is, and every cluster-volume moment
`∫⁻ F (|K_x|)` is independent of the base vertex.  This discharges the hypothesis `hroot` of the
restoration fibre bounds at the whole cut-off family, at every norm, profile, scale and
intensity. -/
theorem lintegral_encard_pow_cutoffKernel_eq {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ)
    (r : ℝ) (β : ℝ≥0) (m : ℕ) (x y : Fin d → ℤ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ m ∂
        (law (intensityProfile (cutoffKernel N K r) β)) =
      ∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ m ∂
        (law (intensityProfile (cutoffKernel N K r) β)) :=
  lintegral_encard_cluster_eq_of_translationInvariant
    (intensityProfile (cutoffKernel N K r) β)
    (intensityProfile_map_add (cutoffKernel_map_add N K r) β)
    (fun n => (n : ℝ≥0∞) ^ m) x y

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

/-! ### The spatial sums are finite

The weights produced above are not merely formal: the `x`-weight has finite total mass as soon as
the `p`-th root moment is finite, and a finite window then makes its exterior mass small.  This is
what makes the `x`-orientation usable in the window argument; for the `y`-weight the corresponding
statement is about the dilated sum, a sum of `#S` translates. -/

section Spatial

variable {d : ℕ}

/-- **A lower-exponent root volume moment is dominated by the `p`-th one.**  A cluster has at least
one vertex, so on the root-volume level `1 ≤ |K_o|` and the moment is monotone in the exponent. -/
theorem lintegral_root_pow_le_of_le (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    {l p : ℕ} (hlp : l + 1 ≤ p) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (l + 1) ∂μ ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ := by
  refine lintegral_mono fun ω => ?_
  have h1 : (1 : ℝ≥0∞) ≤ ((cluster ω o).encard : ℝ≥0∞) := by
    simpa using ENat.toENNReal_mono (one_le_encard_cluster ω o)
  exact pow_le_pow_right' h1 hlp

open Classical in
/-- **The vertex mass of a root monomial is summable.**  `∑'_x ∫⁻ 1{x ∈ K_o} |K_o| ^ l` is the
`(l+1)`-th root moment, hence finite as soon as the `p`-th moment is and `l + 1 ≤ p`. -/
theorem tsum_lintegral_root_monomial_ne_top (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    {l p : ℕ} (hlp : l + 1 ≤ p)
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ ≠ ⊤) :
    ∑' x : Fin d → ℤ, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ ≠ ⊤ := by
  have hcomm : ∑' x : Fin d → ℤ, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ =
      ∑' x : Fin d → ℤ, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ l *
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ :=
    tsum_congr fun x => lintegral_congr fun ω => mul_comm _ _
  rw [hcomm, tsum_lintegral_root_pow_indicator μ o l]
  exact ne_top_of_le_ne_top hmom (lintegral_root_pow_le_of_le μ o hlp)

open Classical in
/-- **A finite window makes the exterior vertex mass of a root monomial small.**  Same statement as
`exists_window_exterior_root_monomial_le` but with the exponent taken below the finite moment, so
that only `∫⁻ |K_o| ^ p ≠ ⊤` and `l + 1 ≤ p` are required. -/
theorem exists_window_exterior_root_weight_le (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    {l p : ℕ} (hlp : l + 1 ≤ p)
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset (Fin d → ℤ), ∑' x : Fin d → ℤ,
        (if x ∈ W then (0 : ℝ≥0∞) else 1) *
          (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ) ≤ ε := by
  classical
  have hsum : ∑' x : Fin d → ℤ, (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ) ≠ ⊤ :=
    tsum_lintegral_root_monomial_ne_top μ o hlp hmom
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le_of_tsum_ne_top
    (fun x : Fin d → ℤ => ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ) hsum hε
  exact ⟨W, le_of_eq_of_le (tsum_ite_mem_eq_tsum_compl W _) hW⟩

open Classical in
/-- **The dilated vertex mass is summable.**  The `y`-weight of the right orientation is the sum of
`B_l` over the finite range `y + S`; summed over `y` it is `#S` times the mass of `B_l`, because
translation is a bijection of the lattice.  Hence the `y`-orientation of the fibre bound also has a
*finitely summable* vertex weight, and a finite window makes its exterior mass small
(`exists_window_exterior_dilated_le`). -/
theorem tsum_dilated_root_monomial_ne_top (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) {l p : ℕ} (hlp : l + 1 ≤ p)
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ ≠ ⊤) :
    ∑' y : Fin d → ℤ, (∑ z ∈ S, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ) ≠ ⊤ := by
  classical
  have hsingle : ∀ z : Fin d → ℤ,
      (∑' y : Fin d → ℤ, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ)
      = ∑' y : Fin d → ℤ, ∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ := fun z => by
    rw [show (∑' y : Fin d → ℤ, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ)
        = ∑' y : Fin d → ℤ, ∫⁻ ω, (if y + z ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ from
      tsum_congr fun y => by rw [add_comm z]]
    exact Equiv.tsum_eq (Equiv.addRight z)
      (fun y : Fin d → ℤ => ∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ)
  rw [show (∑' y : Fin d → ℤ, (∑ z ∈ S, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ))
      = ∑ z ∈ S, ∑' y : Fin d → ℤ, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ from
    Summable.tsum_finsetSum (fun z _ => ENNReal.summable)]
  rw [show (∑ z ∈ S, ∑' y : Fin d → ℤ, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ)
      = ∑ _z ∈ S, (∑' y : Fin d → ℤ, ∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ) from
    Finset.sum_congr rfl fun z _ => hsingle z]
  rw [Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) (tsum_lintegral_root_monomial_ne_top μ o hlp hmom)

open Classical in
/-- **A finite window makes the exterior mass of the dilated weight small.** -/
theorem exists_window_exterior_dilated_le (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) {l p : ℕ} (hlp : l + 1 ≤ p)
    (hmom : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset (Fin d → ℤ), ∑' y : Fin d → ℤ,
        (if y ∈ W then (0 : ℝ≥0∞) else 1) *
          (∑ z ∈ S, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
            ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ) ≤ ε := by
  classical
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le_of_tsum_ne_top
    (fun y : Fin d → ℤ => ∑ z ∈ S, ∫⁻ ω, (if z + y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ l ∂μ)
    (tsum_dilated_root_monomial_ne_top μ o S hlp hmom) hε
  exact ⟨W, le_of_eq_of_le (tsum_ite_mem_eq_tsum_compl W _) hW⟩

end Spatial

end PercLib.Percolation.Bond
