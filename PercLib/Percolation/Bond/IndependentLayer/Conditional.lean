/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.Transport.Reindexing

/-!
# The omitted-edge ghost comparison (FJWB)

Let `q : Sym2 V → I` and a deterministic set `E₀` of retained pairs. The cut-off profile is
`q·1_{E₀}` and the omitted profile is `q·1_{E₀ᶜ}`; their independent union has profile `q`
(`union_cutoff_omitted`). With `X` the cut-off cluster volume of `o`, `M₀(h)` its ghost
transform, `M_v(h)` the ghost transform of the full law and `M* = ⨆ v, M_v`:

* `lintegral_ghost_cutoff_le` (**FJWB**): if `X < ⊤` a.s. and
  `δ ≥ sup_u ∑_{v ≠ u, s(u,v) ∉ E₀} q(u, v)`, then
  `M₀(h) ≤ M_o(h) ≤ M₀(h) + δ E[X e^{-hX}] M*(h)`;
* `lintegral_ghost_cutoff_le_of_transitive`: when the full profile is transitive,
  `M* = M_o`, so `M_o(h) ≤ M₀(h) + δ E[X e^{-hX}] M_o(h)` (the multiplicative form).

Both are derived from BEJT (`lintegral_ghost_le_union`, `lintegral_ghost_union_le`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- The cut-off profile and the omitted profile recombine to the full profile. -/
theorem union_cutoff_omitted (q : Sym2 V → I) (E₀ : Set (Sym2 V)) :
    (fun e => σ (σ (if e ∈ E₀ then q e else 0) * σ (if e ∈ E₀ then 0 else q e))) = q := by
  funext e
  by_cases he : e ∈ E₀
  · simp [he]
  · simp [he]

open Classical in
/-- The omitted row bound in the form used by `lintegral_ghost_le_layer`. -/
theorem omitted_row_le (q : Sym2 V → I) (E₀ : Set (Sym2 V)) {δ : ℝ≥0∞}
    (hδ : ∀ u, (∑' w, if w = u ∨ s(u, w) ∈ E₀ then 0 else
      (unitInterval.toNNReal (q s(u, w)) : ℝ≥0∞)) ≤ δ) (u : V) :
    rowSum (fun e => unitInterval.toENNReal (if e ∈ E₀ then 0 else q e)) u ≤ δ := by
  rw [rowSum_toENNReal]
  refine le_trans (le_of_eq (tsum_congr fun w => ?_)) (hδ u)
  by_cases hw : w = u
  · simp [hw]
  · by_cases hE : s(u, w) ∈ E₀
    · simp only [hw, hE, or_true, ↓reduceIte]
      rfl
    · simp [hw, hE]

open Classical in
/-- **Omitted-edge ghost comparison.** If the cut-off cluster `X` of `o` is finite almost surely and
the omitted rows are at most `δ`, then `M₀(h) ≤ M_o(h) ≤ M₀(h) + δ E[X e^{-hX}] M*(h)`. -/
theorem lintegral_ghost_cutoff_le [Countable V] (q : Sym2 V → I) (E₀ : Set (Sym2 V)) (o : V)
    {h : ℝ} (hh : 0 < h)
    (hfin : ∀ᵐ ω ∂(law fun e => if e ∈ E₀ then q e else 0), (cluster ω o).Finite)
    {δ : ℝ≥0∞} (hδ : ∀ u, (∑' w, if w = u ∨ s(u, w) ∈ E₀ then 0 else
      (unitInterval.toNNReal (q s(u, w)) : ℝ≥0∞)) ≤ δ) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => if e ∈ E₀ then q e else 0) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q) ∧
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law fun e => if e ∈ E₀ then q e else 0) +
        δ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))
            ∂(law fun e => if e ∈ E₀ then q e else 0)) *
        ⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
          ∂(law q) := by
  have hu := union_cutoff_omitted q E₀
  constructor
  · have := lintegral_ghost_le_union (fun e => if e ∈ E₀ then q e else 0)
      (fun e => if e ∈ E₀ then 0 else q e) o hh
    rwa [hu] at this
  · have := lintegral_ghost_union_le (fun e => if e ∈ E₀ then q e else 0)
      (fun e => if e ∈ E₀ then 0 else q e) o hh hfin (omitted_row_le q E₀ hδ)
      (G := ⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂(law q))
      (fun v => by rw [hu]; exact le_iSup (fun v => ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂(law q)) v)
    rwa [hu] at this

/-- Under a transitive profile, every vertex has the same ghost transform. -/
theorem lintegral_ghost_eq_of_transitive (q : Sym2 V → I)
    (hT : ∀ x y : V, ∃ τ : V ≃ V, τ x = y ∧ ∀ e, q (Sym2.map τ e) = q e) (h : ℝ) (x y : V) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω y).encard : ℝ≥0∞) : EReal))))
        ∂(law q) =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω x).encard : ℝ≥0∞) : EReal))))
        ∂(law q) := by
  obtain ⟨τ, hτx, hτ⟩ := hT x y
  have hlaw : (law q).map (fun ω => Sym2.map τ '' ω) = law q :=
    prodBernoulli_map_image_sym2_invariant q τ hτ
  rw [← hτx]
  conv_lhs => rw [← hlaw]
  rw [lintegral_map_image_sym2Map]
  simp_rw [encard_cluster_image]

open Classical in
/-- **Transitive form.** When the full profile is transitive, `M* = M_o` and
`M_o(h) ≤ M₀(h) + δ E[X e^{-hX}] M_o(h)`. -/
theorem lintegral_ghost_cutoff_le_of_transitive [Countable V] (q : Sym2 V → I)
    (hT : ∀ x y : V, ∃ τ : V ≃ V, τ x = y ∧ ∀ e, q (Sym2.map τ e) = q e)
    (E₀ : Set (Sym2 V)) (o : V) {h : ℝ} (hh : 0 < h)
    (hfin : ∀ᵐ ω ∂(law fun e => if e ∈ E₀ then q e else 0), (cluster ω o).Finite)
    {δ : ℝ≥0∞} (hδ : ∀ u, (∑' w, if w = u ∨ s(u, w) ∈ E₀ then 0 else
      (unitInterval.toNNReal (q s(u, w)) : ℝ≥0∞)) ≤ δ) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law fun e => if e ∈ E₀ then q e else 0) +
        δ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))
            ∂(law fun e => if e ∈ E₀ then q e else 0)) *
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law q) := by
  have h2 := (lintegral_ghost_cutoff_le q E₀ o hh hfin hδ).2
  have hsup : (⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
      (((cluster ω v).encard : ℝ≥0∞) : EReal)))) ∂(law q)) =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q) := by
    have : Nonempty V := ⟨o⟩
    simp_rw [lintegral_ghost_eq_of_transitive q hT h o]
    exact ciSup_const
  rwa [hsup] at h2

/-! ### Non-vacuity witnesses -/

open Classical in
/-- `lintegral_ghost_cutoff_le` on `ℤ` with the zero profile and `E₀ = ∅`: the cut-off cluster is
`{o}`, the omitted rows vanish, and the profile is transitive under translations. -/
example (h : ℝ) (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω (0 : ℤ)).encard : ℝ≥0∞) : EReal))))
        ∂(law fun _ : Sym2 ℤ => (0 : I)) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω (0 : ℤ)).encard : ℝ≥0∞) : EReal))))
          ∂(law fun e => if e ∈ (∅ : Set (Sym2 ℤ)) then (0 : I) else 0) +
        0 * (∫⁻ ω, ((cluster ω (0 : ℤ)).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω (0 : ℤ)).encard : ℝ≥0∞) : EReal)))
            ∂(law fun e => if e ∈ (∅ : Set (Sym2 ℤ)) then (0 : I) else 0)) *
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω (0 : ℤ)).encard : ℝ≥0∞) : EReal))))
          ∂(law fun _ : Sym2 ℤ => (0 : I)) := by
  have hfin : ∀ᵐ ω ∂(law fun _ : Sym2 ℤ => (0 : I)), (cluster ω (0 : ℤ)).Finite :=
    ae_cluster_finite_of_chi_lt_top (q := fun _ : Sym2 ℤ => (0 : I)) (v := 0)
      (by rw [chi_eq_one_of_offDiagonal_zero _ (fun _ _ _ => rfl)]; exact ENNReal.one_lt_top)
  convert lintegral_ghost_cutoff_le_of_transitive (fun _ : Sym2 ℤ => (0 : I))
    (fun x y => ⟨Equiv.addRight (y - x), by simp, fun _ => rfl⟩) ∅ (0 : ℤ) hh (δ := 0)
    (by simpa using hfin) (fun u => by
      simp only [mem_empty_iff_false, or_false, unitInterval.toNNReal, Icc.coe_zero,
        nonpos_iff_eq_zero, ENNReal.tsum_eq_zero, ite_eq_left_iff]
      intro _ _; rfl)

end PercLib.Percolation.Bond
