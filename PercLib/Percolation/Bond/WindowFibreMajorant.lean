/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs written for the cut-off truncated moment derivative of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1.
No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Models.LongRange.TruncatedMoments
public import PercLib.Percolation.Bond.SmallTailMass

/-!
# Fibre-sum vertex majorants for the cut-off pivotal window tail

The finite-window small-tail input `hwin` of the cut-off moment-derivative interface is produced by
`PercLib.Models.LongRange.lintegral_window_tail_le` from a single vertex weight `g` obeying two
*per-pair* dominations, `∀ x y, (crossing mass at the pair) ≤ g x`, and the same with `g y`.
`lintegral_window_tail_le_of_factorization` specialises that to `g x = C * P(x ∈ K_o)`, which is the
gap factorisation `hfac` of `PercLib.Percolation.Bond.SmallTailMass`.

This file removes the per-pair requirement.  What the window argument actually uses is the
*sum over the fibre of one vertex*, and the two orientations need not be majorised by the same
weight:

* `lintegral_pair_series_le_of_fibre_majorant` — for an arbitrary pair integrand `F` on an
  arbitrary measured space, if the fibre sums `∑'_y ∫⁻ c x y * F x y` and `∑'_x ∫⁻ c x y * F x y`
  are dominated by vertex weights `gx`, `gy`, then the weighted pair series with weight
  `p x y ≤ w x + w y` is bounded by `∑'_x w x * gx x + ∑'_y w y * gy y`.  No per-pair bound, no
  factorisation, no `min`, and no restriction on the measure;
* `lintegral_pivotal_series_le_of_fibre_majorant` — the same for the crucial series itself,
  through the pointwise identity `tsum_pivotal_eq_tsum_crossing` and the arithmetic lemma
  `mul_radial_window_le`; the single-weight `min` of the library's route is gone, and the `#S`
  factor is replaced by the fibre hypotheses;
* `lintegral_pivotal_window_tail_le_of_fibre_majorant` — the window specialisation of the same
  statement, in the shape `lintegral_window_tail_le` produces, with
  `w x = 1{x ∉ W}` and `p e = 1{e ∉ pairs (W × W)}`;
* `ENNReal.pow_sub_pow_eq_sum_range_choose`, `ae_encard_cluster_ne_top_of_lintegral_pow_ne_top` —
  the binomial split of the truncated pivotal increment and the almost-sure finiteness of the root
  cluster that it needs, so that the residual input can be stated monomial by monomial.

## The residual input, exactly

For the long-range law the fibre hypotheses are the model-specific part, and they are *weaker*
than `hfac`: `hfac` gives both of them with `gx = gy = C * τ` and a per-pair inequality, while a
fibre sum may use any information about the other endpoint.  `hfac` is neither proved here nor
proved to be necessary, and no `Input` structure is introduced: the model-specific bound stays a
visible hypothesis.  Nothing here claims `hwin`, `htail`, `htail`-continuity or sharpness, and no
capped or uncapped derivative identity is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ENNReal

/-- **Binomial split of the truncated pivotal increment.**

For `a ≠ ⊤` (a finite root cluster) the truncated difference `(a + b) ^ p - a ^ p` in `ℝ≥0∞` is the
sum of the mixed monomials of `a` and `b`; the pure term `a ^ p` cancels. For `p ≥ 1` and
`b = ⊤` both sides are `⊤`. For `a = ⊤`, `b ≠ 0` and `p ≥ 1`, the truncated difference is `0`
while the right-hand side is `⊤`, so the root-finiteness hypothesis cannot be dropped. -/
theorem pow_sub_pow_eq_sum_range_choose {a b : ℝ≥0∞} {p : ℕ} (ha : a ≠ ⊤) :
    (a + b) ^ p - a ^ p =
      ∑ ℓ ∈ Finset.range p, a ^ ℓ * b ^ (p - ℓ) * (p.choose ℓ : ℝ≥0∞) := by
  rw [add_pow, Finset.sum_range_succ]
  have hlast : a ^ p * b ^ (p - p) * (p.choose p : ℝ≥0∞) = a ^ p := by simp
  rw [hlast]
  exact ENNReal.add_sub_cancel_right (ENNReal.pow_ne_top ha)

end ENNReal

namespace PercLib.Percolation.Bond

/-- **The window weight moves from the pair weight to the two endpoint weights.**

Purely arithmetic: if the pair weight `r` is to be replaced by `win`, the root-cluster factors `A`,
`B` and the increment `Δ` stay on the right.  Used with `r = 1{s(x,y) ∉ W × W}` and
`win = 1{x ∉ W} + 1{y ∉ W}`. -/
theorem mul_radial_window_le {A B r c win Δ : ℝ≥0∞} (h : r ≤ win) :
    (A * (r * c) * B) * Δ ≤ win * (c * ((A * B) * Δ)) := by
  calc (A * (r * c) * B) * Δ = ((A * B) * Δ * c) * r := by ac_rfl
    _ ≤ ((A * B) * Δ * c) * win := mul_le_mul' le_rfl h
    _ = win * (c * ((A * B) * Δ)) := by ac_rfl

variable {α : Type*} {δ : Type*}

/-- **The weighted pair series from fibre-sum vertex majorants.**

Let `c : α → α → ℝ≥0∞` be a pair weight, `F : α → α → δ → ℝ≥0∞` a pair integrand on a measured
space `δ`, `p` a pair weight bounded by `w x + w y`, and `gx`, `gy` vertex weights dominating the
fibre sums of the pair masses in the two coordinates.  Then the series weighted by `p` is bounded by
`∑'_x w x * gx x + ∑'_y w y * gy y`.

Compared with the per-pair form `lintegral_window_tail_le` this drops (i) the factor `#S` (the
fibre sums are hypotheses, not derived from a difference set), (ii) the requirement that the two
orientations share one weight, and (iii) any per-pair domination.  Nothing is assumed about `F`
beyond measurability, nothing about `μ`, and the window enters only through `p` and `w`. -/
theorem lintegral_pair_series_le_of_fibre_majorant [Countable α] [MeasurableSpace δ]
    {μ : Measure δ}
    (c : α → α → ℝ≥0∞) (F : α → α → δ → ℝ≥0∞) (hF : ∀ x y, Measurable (F x y))
    (p : α → α → ℝ≥0∞) (w : α → ℝ≥0∞) (hp : ∀ x y, p x y ≤ w x + w y)
    (gx gy : α → ℝ≥0∞)
    (hx : ∀ x, ∑' y, ∫⁻ ω, c x y * F x y ω ∂μ ≤ gx x)
    (hy : ∀ y, ∑' x, ∫⁻ ω, c x y * F x y ω ∂μ ≤ gy y) :
    ∫⁻ ω, ∑' x, ∑' y, p x y * (c x y * F x y ω) ∂μ
      ≤ (∑' x, w x * gx x) + ∑' y, w y * gy y := by
  have hpt : ∀ ω : δ, (∑' x, ∑' y, p x y * (c x y * F x y ω))
      ≤ ∑' x, ∑' y, (w x + w y) * (c x y * F x y ω) := fun ω =>
    ENNReal.tsum_le_tsum fun x =>
      ENNReal.tsum_le_tsum fun y => mul_le_mul' (hp x y) le_rfl
  refine le_trans (lintegral_mono hpt) ?_
  have hmeas' : ∀ x, AEMeasurable
      (fun ω : δ => ∑' y, (w x + w y) * (c x y * F x y ω)) μ :=
    fun x => AEMeasurable.tsum fun y =>
      (measurable_const.mul (hF x y)).aemeasurable.const_mul _
  calc ∫⁻ ω, ∑' x, ∑' y, (w x + w y) * (c x y * F x y ω) ∂μ
      = ∑' x, ∑' y, (w x + w y) * ∫⁻ ω, c x y * F x y ω ∂μ := by
        refine Eq.trans (lintegral_tsum hmeas') ?_
        refine tsum_congr fun x => ?_
        refine Eq.trans (lintegral_tsum ?_) ?_
        · exact fun y => (measurable_const.mul (hF x y)).aemeasurable.const_mul _
        · exact tsum_congr fun y => lintegral_const_mul _ (measurable_const.mul (hF x y))
    _ = (∑' x, ∑' y, w x * ∫⁻ ω, c x y * F x y ω ∂μ)
        + ∑' x, ∑' y, w y * ∫⁻ ω, c x y * F x y ω ∂μ := by
        calc ∑' x, ∑' y, (w x + w y) * ∫⁻ ω, c x y * F x y ω ∂μ
            = ∑' x, ∑' y, (w x * ∫⁻ ω, c x y * F x y ω ∂μ
                + w y * ∫⁻ ω, c x y * F x y ω ∂μ) :=
              tsum_congr fun x => tsum_congr fun y => add_mul _ _ _
          _ = ∑' x, ((∑' y : α, w x * ∫⁻ ω, c x y * F x y ω ∂μ)
                + ∑' y : α, w y * ∫⁻ ω, c x y * F x y ω ∂μ) :=
              tsum_congr fun x => ENNReal.tsum_add
          _ = _ := ENNReal.tsum_add
    _ ≤ (∑' x, w x * gx x) + ∑' y, w y * gy y := by
        refine add_le_add ?_ ?_
        · calc (∑' x, ∑' y, w x * ∫⁻ ω, c x y * F x y ω ∂μ)
              = ∑' x, w x * (∑' y, ∫⁻ ω, c x y * F x y ω ∂μ) := by
                refine tsum_congr fun x => ?_
                rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' x, w x * gx x :=
                ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hx x)
        · calc (∑' x, ∑' y, w y * ∫⁻ ω, c x y * F x y ω ∂μ)
              = ∑' y, ∑' x, w y * ∫⁻ ω, c x y * F x y ω ∂μ := ENNReal.tsum_comm
            _ = ∑' y, w y * (∑' x, ∫⁻ ω, c x y * F x y ω ∂μ) := by
                refine tsum_congr fun y => ?_
                rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' y, w y * gy y :=
                ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl (hy y)

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-- **A finite `k`-th root moment makes the root cluster finite almost surely.**

This is the hypothesis the binomial split `ENNReal.pow_sub_pow_eq_sum_range_choose` needs.  Note the
direction: `∫⁻ ↑|K_o| ^ k ≠ ⊤` is *not* implied by finiteness of the susceptibility, and it does not
imply any smallness of the exterior mass; it is exactly a.e.-finiteness of the cluster. -/
theorem ae_encard_cluster_ne_top_of_lintegral_pow_ne_top {d : ℕ}
    {μ : Measure (Config (Fin d → ℤ))} {o : Fin d → ℤ} {k : ℕ} (hk : 0 < k)
    (h : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂μ ≠ ⊤) :
    ∀ᵐ ω ∂μ, (cluster ω o).encard ≠ ⊤ := by
  have hlt : ∀ᵐ ω ∂μ, ((cluster ω o).encard : ℝ≥0∞) ^ k < ⊤ :=
    ae_lt_top ((measurable_encard_cluster_toENNReal o).pow_const k) h
  filter_upwards [hlt] with ω hω htop
  rw [htop, ENat.toENNReal_top] at hω
  exact absurd hω (by simp [hk.ne'])

open Classical in
/-- **The pivotal series from fibre-sum vertex majorants.**

`lintegral_pivotal_window_tail_le_of_fibre_majorant` without the window: `pwt` is an arbitrary pair
weight bounded by `w x + w y`.  The library's window estimates are the case
`pwt e = 1{e ∉ pairs (W × W)}`, `w x = 1{x ∉ W}`, and the single-weight form of
`lintegral_window_tail_le` is the further case `gx = gy = #S * g`, `w = 1{· ∉ W}`. -/
theorem lintegral_pivotal_series_le_of_fibre_majorant {d : ℕ}
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞) (pwt : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (w : (Fin d → ℤ) → ℝ≥0∞)
    (hpw : ∀ x y : Fin d → ℤ, pwt (s(x, y)) ≤ w x + w y)
    (gx gy : (Fin d → ℤ) → ℝ≥0∞)
    (hx : ∀ x, ∑' y, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ gx x)
    (hy : ∀ y, ∑' x, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ gy y) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        (pwt e * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ (∑' x, w x * gx x) + ∑' y, w y * gy y := by
  classical
  set X : (Fin d → ℤ) → (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞ := fun x y ω =>
    (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
      ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p) with hX
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
  have hpt : ∀ ω : Config (Fin d → ℤ),
      (∑' e : Sym2 (Fin d → ℤ),
        (pwt e * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)))
      ≤ ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (w x + w y) * (c (s(x, y)) * X x y ω) := by
    intro ω
    rw [tsum_pivotal_eq_tsum_crossing ω o p (fun e => pwt e * c e)]
    simp only [hX]
    refine ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y =>
      mul_radial_window_le (hpw x y)
  refine le_trans (lintegral_mono hpt) ?_
  exact lintegral_pair_series_le_of_fibre_majorant (fun x y => c (s(x, y))) X hXm
    (fun x y => w x + w y) w (fun _ _ => le_rfl) gx gy hx hy

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

open Classical in
/-- **The window form of the fibre-majorant bound.**

`lintegral_pivotal_series_le_of_fibre_majorant` with `pwt e = 1{e ∉ pairs (W × W)}` and
`w x = 1{x ∉ W}`; the hypothesis `hpw` is then exactly the arithmetic content of
`lintegral_window_tail_le`'s window step (`1{s(x,y) ∉ W × W} ≤ 1{x ∉ W} + 1{y ∉ W}`, which follows
from `(x, y) ∈ W × W` for `x, y ∈ W`).  The conclusion is the *same quantity* as the left-hand side
of `lintegral_window_tail_le`, but bounded through the two exterior masses of two independent vertex
weights `gx`, `gy` rather than through a single `2 * #S * ∑' g x`. -/
theorem lintegral_pivotal_window_tail_le_of_fibre_majorant {d : ℕ}
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (W : Finset (Fin d → ℤ)) (gx gy : (Fin d → ℤ) → ℝ≥0∞)
    (hx : ∀ x, ∑' y, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ gx x)
    (hy : ∀ y, ∑' x, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ gy y) :
    ∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) * c e) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ
      ≤ (∑' x, (if x ∈ W then (0 : ℝ≥0∞) else 1) * gx x)
        + ∑' y, (if y ∈ W then (0 : ℝ≥0∞) else 1) * gy y := by
  classical
  have hIW : ∀ x y : Fin d → ℤ,
      (if s(x, y) ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
        then (0 : ℝ≥0∞) else 1) ≤
        (if x ∈ W then (0 : ℝ≥0∞) else 1) + (if y ∈ W then (0 : ℝ≥0∞) else 1) := by
    intro x y
    by_cases hs : s(x, y) ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
    · rw [ite_eq_left hs]
      exact zero_le
    · rw [ite_eq_right hs]
      by_cases hxw : x ∈ W
      · by_cases hyw : y ∈ W
        · exact absurd (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hxw, hyw⟩, rfl⟩) hs
        · simp [hxw, hyw]
      · simp [hxw]
  exact lintegral_pivotal_series_le_of_fibre_majorant μ o p c
    (fun e => if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
      then (0 : ℝ≥0∞) else 1) (fun x => if x ∈ W then (0 : ℝ≥0∞) else 1) hIW gx gy hx hy

open Classical in
/-- **The root-cluster `(p+1)`-moment is the total mass of the vertex weights
`z ↦ |K_o| ^ p * 1{z ∈ K_o}`.**

Spatial first-moment identity with the extra root weight, in `ℝ≥0∞`: an infinite cluster contributes
`⊤` on both sides, so no a.e.-finiteness is assumed.  This is the bookkeeping behind the claim that
the *pure* monomial `|K_o| ^ p` of the crossing mass needs no gap factorisation. -/
theorem tsum_lintegral_root_pow_indicator {d : ℕ} (μ : Measure (Config (Fin d → ℤ)))
    (o : Fin d → ℤ) (p : ℕ) :
    ∑' z : Fin d → ℤ, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p *
        (if z ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ
      = ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂μ := by
  have hpt : ∀ ω : Config (Fin d → ℤ), ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
      = ∑' z : Fin d → ℤ, ((cluster ω o).encard : ℝ≥0∞) ^ p *
          (if z ∈ cluster ω o then (1 : ℝ≥0∞) else 0) := by
    intro ω
    have hA : (∑' y : Fin d → ℤ, (conn o y).indicator (fun _ => (1 : ℝ≥0∞)) ω)
        = ∑' i : Fin d → ℤ, (if i ∈ cluster ω o then (1 : ℝ≥0∞) else 0) :=
      tsum_congr fun z => by rw [Set.indicator_apply]; rfl
    rw [encard_cluster_eq_tsum, pow_succ, ENNReal.tsum_mul_left, hA]
  have hmeas : ∀ z : Fin d → ℤ, AEMeasurable (fun ω : Config (Fin d → ℤ) =>
      ((cluster ω o).encard : ℝ≥0∞) ^ p * (if z ∈ cluster ω o then (1 : ℝ≥0∞) else 0)) μ :=
    fun z => (((measurable_encard_cluster_toENNReal o).pow_const p).mul
      (Measurable.ite (measurableSet_conn o z) measurable_const
        measurable_const)).aemeasurable
  rw [← lintegral_tsum hmeas]
  exact lintegral_congr fun ω => (hpt ω).symm

open Classical in
/-- **A single window makes the pure root monomial's vertex mass small.**

The `W`-exterior mass of `z ↦ ∫⁻ 1{z ∈ K_o} |K_o| ^ p` is at most `δ` once a finite window is large
enough, from the single hypothesis `∫⁻ |K_o| ^ (p+1) ≠ ⊤` (and no factorisation, no susceptibility,
no monotonicity in the scale).  This is `exists_finset_tsum_compl_le_of_tsum_ne_top` applied to the
spatial identity `tsum_lintegral_root_pow_indicator`. -/
theorem exists_window_exterior_root_monomial_le {d : ℕ} (μ : Measure (Config (Fin d → ℤ)))
    (o : Fin d → ℤ) (p : ℕ)
    (h : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂μ ≠ ⊤) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ W : Finset (Fin d → ℤ), ∑' z : Fin d → ℤ,
        (if z ∈ W then (0 : ℝ≥0∞) else 1) *
          ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p *
            (if z ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≤ δ := by
  have hsum : ∑' z : Fin d → ℤ,
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p *
        (if z ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≠ ⊤ := by
    rw [tsum_lintegral_root_pow_indicator]
    exact h
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le_of_tsum_ne_top
    (fun z : Fin d → ℤ => ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p *
      (if z ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ) hsum hδ
  exact ⟨W, le_of_eq_of_le (tsum_ite_mem_eq_tsum_compl W _) hW⟩

open Classical in
/-- **The pure root monomial needs no gap factorisation in the `x`-orientation.**

For a pair weight `c` bounded by `K` and supported on `N(y - x) < r`, the `x`-fibre sum of the
*monomial* crossing mass `1{x ∈ K_o} 1{y ∉ K_o} |K_o| ^ p` (the `ℓ = p` term of the binomial split
`ENNReal.pow_sub_pow_eq_sum_range_choose`) is dominated by the vertex weight
`z ↦ #S * K * ∫⁻ 1{z ∈ K_o} |K_o| ^ p`, whose total mass is `#S * K * ∫⁻ |K_o| ^ (p+1)` by
`tsum_lintegral_root_pow_indicator` and whose window-exterior mass is small by
`exists_window_exterior_root_monomial_le`.  No property of the second endpoint beyond the finiteness
of the fibre (`S`) and the boundedness of `c` is used. -/
theorem tsum_lintegral_root_monomial_fibre_le {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (K : ℝ≥0∞) (hK : ∀ x y : Fin d → ℤ, c (s(x, y)) ≤ K) (x : Fin d → ℤ) :
    ∑' y, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ
      ≤ (S.card : ℝ≥0∞) * (K * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) := by
  refine tsum_fibre_le S hS x (fun y => ∫⁻ ω, c (s(x, y)) *
    ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
      ((cluster ω o).encard : ℝ≥0∞) ^ p) ∂μ)
    (K * ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
      ((cluster ω o).encard : ℝ≥0∞) ^ p ∂μ) ?_ ?_
  · intro y hy
    rw [hcsupp x y hy]
    simp
  · intro y
    have hmeas : Measurable fun ω : Config (Fin d → ℤ) =>
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * ((cluster ω o).encard : ℝ≥0∞) ^ p :=
      (Measurable.ite (measurableSet_conn o x) measurable_const measurable_const).mul
        ((measurable_encard_cluster_toENNReal o).pow_const p)
    refine le_trans (lintegral_mono fun ω => ?_)
      (le_of_eq (lintegral_const_mul K hmeas))
    refine mul_le_mul' (hK x y) ?_
    by_cases hy' : y ∈ cluster ω o
    · simp [hy']
    · simp [hy']

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

open Classical in
/-- **Binomial split at the level of one fibre sum.**

If `a` is finite almost surely, the fibre sum of the *truncated increment*
`(a + b y) ^ p - a ^ p` is at most the binomial-weighted sum of the fibre sums of the monomials
`a ^ ℓ * b y ^ (p - ℓ)`, `ℓ < p`.  This is the step that lets each monomial of the crossing mass be
majorised separately: no single weight has to dominate the whole increment. -/
theorem tsum_lintegral_pow_sub_le_sum_monomial {d : ℕ} {μ : Measure (Config (Fin d → ℤ))}
    (u : (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞)
    (a : Config (Fin d → ℤ) → ℝ≥0∞) (b : (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞)
    (hu : ∀ y, Measurable (u y)) (ha : Measurable a) (hb : ∀ y, Measurable (b y))
    (hae : ∀ᵐ ω ∂μ, a ω ≠ ⊤) (p : ℕ) :
    ∑' y, ∫⁻ ω, u y ω * ((a ω + b y ω) ^ p - a ω ^ p) ∂μ
      ≤ ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ∑' y, ∫⁻ ω, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) ∂μ := by
  have hmeasU : ∀ y, AEMeasurable (fun ω : Config (Fin d → ℤ) =>
      u y ω * ((a ω + b y ω) ^ p - a ω ^ p)) μ := fun y =>
    ((hu y).mul (((ha.add (hb y)).pow_const p).sub (ha.pow_const p))).aemeasurable
  have hmeasM : ∀ (ℓ : ℕ) (y), Measurable (fun ω : Config (Fin d → ℤ) =>
      u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ))) := fun ℓ y =>
    (hu y).mul ((ha.pow_const ℓ).mul ((hb y).pow_const (p - ℓ)))
  have hmeasSum : ∀ ℓ : ℕ, Measurable fun ω : Config (Fin d → ℤ) =>
      ∑' y : Fin d → ℤ, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) :=
    fun ℓ => Measurable.tsum (fun y => hmeasM ℓ y)
  have hpt : ∀ᵐ ω ∂μ, (∑' y : Fin d → ℤ, u y ω * ((a ω + b y ω) ^ p - a ω ^ p))
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ∑' y : Fin d → ℤ, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) := by
    filter_upwards [hae] with ω hω
    have hy : ∀ y : Fin d → ℤ, u y ω * ((a ω + b y ω) ^ p - a ω ^ p)
        = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
            (u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ))) := by
      intro y
      rw [ENNReal.pow_sub_pow_eq_sum_range_choose hω, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ac_rfl
    calc (∑' y : Fin d → ℤ, u y ω * ((a ω + b y ω) ^ p - a ω ^ p))
        = ∑' y : Fin d → ℤ, ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
            (u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ))) := tsum_congr hy
      _ = ∑ ℓ ∈ Finset.range p, ∑' y : Fin d → ℤ, (p.choose ℓ : ℝ≥0∞) *
            (u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ))) :=
          Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
      _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
            ∑' y : Fin d → ℤ, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [ENNReal.tsum_mul_left]
  rw [← lintegral_tsum hmeasU]
  refine le_of_eq ?_
  calc ∫⁻ ω, ∑' y : Fin d → ℤ, u y ω * ((a ω + b y ω) ^ p - a ω ^ p) ∂μ
      = ∫⁻ ω, ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ∑' y : Fin d → ℤ, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) ∂μ :=
        lintegral_congr_ae hpt
    _ = ∑ ℓ ∈ Finset.range p, ∫⁻ ω, (p.choose ℓ : ℝ≥0∞) *
          ∑' y : Fin d → ℤ, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) ∂μ := by
        exact lintegral_finsetSum _ fun ℓ _ => (hmeasSum ℓ).const_mul _
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ∫⁻ ω, ∑' y : Fin d → ℤ, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) ∂μ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [lintegral_const_mul _ (hmeasSum ℓ)]
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ∑' y, ∫⁻ ω, u y ω * (a ω ^ ℓ * b y ω ^ (p - ℓ)) ∂μ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [lintegral_tsum]
        exact fun y => (hmeasM ℓ y).aemeasurable

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

open Classical in
/-- **The per-pair single-weight hypothesis implies the fibre majorants.**

With `gx = gy = #S * g`, the per-pair hypothesis of `lintegral_window_tail_le` implies the fibre
hypotheses of `lintegral_pivotal_series_le_of_fibre_majorant`, hence also those of
`lintegral_pivotal_window_tail_le_of_fibre_majorant`.  So the fibre form is a *relaxation* of the
library's route, and `hfac` (`g = C * τ`) is one point of it.  The converse fails: a fibre sum may
use information about the other endpoint that no function of one vertex carries. -/
theorem tsum_fibre_majorant_of_pair_majorant {d : ℕ}
    {N : PercLib.Analysis.ModelNorm (Fin d → ℝ)} {r : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r → z ∈ S)
    (μ : Measure (Config (Fin d → ℤ))) (o : Fin d → ℤ) (p : ℕ)
    (c : Sym2 (Fin d → ℤ) → ℝ≥0∞)
    (hcsupp : ∀ x y : Fin d → ℤ, ¬ N (Int.cast ∘ (y - x)) < r → c (s(x, y)) = 0)
    (g : (Fin d → ℤ) → ℝ≥0∞)
    (hx : ∀ x y : Fin d → ℤ, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ g x) :
    ∀ x, ∑' y, ∫⁻ ω, c (s(x, y)) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ ≤ (S.card : ℝ≥0∞) * g x := by
  intro x
  refine tsum_fibre_le S hS x (fun y => ∫⁻ ω, c (s(x, y)) *
    ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
      ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p)) ∂μ) (g x) ?_ ?_
  · intro y hy
    rw [hcsupp x y hy]
    simp
  · intro y
    exact hx x y

end PercLib.Percolation.Bond
