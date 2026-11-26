/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ConvolutionBound
public import PercLib.Percolation.Bond.FiniteVolumeRusso
public import PercLib.Percolation.Bond.ThetaSemicontinuity

/-! Correspondence wrappers for the finite-domain intensity Russo formula, the off-diagonal
convolution bound, and semicontinuity of the percolation probability.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond
variable {V : Type*}

open Classical in
/-- Diagonal pairs contribute nothing to the Russo sum of an internal connection event. -/
private theorem sum_sym2_russo_eq_filter (J : Sym2 V → ℝ≥0) (S : Finset V)
    (x y : (S : Set V)) (β : ℝ) :
    (∑ e ∈ S.sym2, ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}}) =
      ∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}} := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e.IsDiag
  · rw [ite_eq_right (fun h => absurd he h) , pivotal_eq_empty_of_isDiag (fun ω ω' h => by
      change ((openGraph ω).induce (S : Set V)).Reachable x y ↔
        ((openGraph ω').induce (S : Set V)).Reachable x y
      rw [h]) he, measureReal_empty, mul_zero]
  · rw [ite_eq_left he]

open Classical in
/-- Finite-domain Russo formula in the intensity: the derivative of `τ^S_β(x,y)` is the sum
over off-diagonal pairs of `S` of `J_e e^{-β J_e} P_β(e pivotal)` (from the right at zero,
two-sided for `β > 0`), it lies in `[0, L_S]`, and the derivative of `χ^S_β(x)` is the sum
of these over `y ∈ S`. -/
@[tag "6JBS"]
theorem finite_domain_intensity_russo (J : Sym2 V → ℝ≥0) (S : Finset V) (x : (S : Set V))
    {β : ℝ} (hβ : 0 ≤ β) :
    (∀ y : (S : Set V),
      HasDerivWithinAt
        (fun b => (law (intensityProfile J b.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y})
        (∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), ((J e : ℝ) * Real.exp (-β * J e)) *
          (law (intensityProfile J β.toNNReal)).real
            {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
              ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}})
        (Ici 0) β ∧
      (0 < β → HasDerivAt
        (fun b => (law (intensityProfile J b.toNNReal)).real
          {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y})
        (∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), ((J e : ℝ) * Real.exp (-β * J e)) *
          (law (intensityProfile J β.toNNReal)).real
            {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
              ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}})
        β) ∧
      0 ≤ (∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), ((J e : ℝ) * Real.exp (-β * J e)) *
          (law (intensityProfile J β.toNNReal)).real
            {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
              ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}}) ∧
      (∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), ((J e : ℝ) * Real.exp (-β * J e)) *
          (law (intensityProfile J β.toNNReal)).real
            {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
              ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}}) ≤
        ∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag), (J e : ℝ)) ∧
    HasDerivWithinAt
      (fun b => ∑ y : (S : Set V), (law (intensityProfile J b.toNNReal)).real
        {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y})
      (∑ y : (S : Set V), ∑ e ∈ S.sym2.filter (fun e => ¬ e.IsDiag),
        ((J e : ℝ) * Real.exp (-β * J e)) *
        (law (intensityProfile J β.toNNReal)).real
          {ω | insert e ω ∈ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} ∧
            ω \ {e} ∉ {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y}})
      (Ici 0) β := by
  refine ⟨fun y => ?_, ?_⟩
  · have hd := law_localConn_hasDerivWithinAt J S x y hβ
    rw [sum_sym2_russo_eq_filter J S x y β] at hd
    have hle := localConn_russo_le J S x y hβ
    rw [sum_sym2_russo_eq_filter J S x y β] at hle
    refine ⟨hd, fun hpos => hd.hasDerivAt (Ici_mem_nhds hpos),
      Finset.sum_nonneg fun e _ => by positivity, hle⟩
  · have hd := sum_law_localConn_hasDerivWithinAt J S x hβ
    simp_rw [sum_sym2_russo_eq_filter J S x _ β] at hd
    exact hd

open Classical in
/-- Off-diagonal convolution bound. For the walk weights `F_n(x,y)` of length-`n` sequences
from `x` ending at `y` with the diagonal removal `b` of `a`: `F_{n+1}(x,y) ≤ c_{n+1} a(x,y)`
for `x ≠ y`, `∑_n F_n(x,y) ≤ a(x,y) H(κ) H(m)`, and on countable `V` a profile dominated by
`a` off the diagonal has `τ(x,y) ≤ a(x,y) H(κ) H(m)`, where `H(t) = (1 - t)⁻¹`. -/
@[tag "9L60"]
theorem walk_weights_convolution_bound (a : V → V → ℝ≥0∞) (m K : ℝ≥0∞)
    (hrow : ∀ v, ∑' w, offDiagonal a v w ≤ m)
    (hconv : ∀ x y, x ≠ y → ∑' z, offDiagonal a x z * offDiagonal a z y ≤ K * a x y) :
    (∀ (n : ℕ) (x y : V), x ≠ y →
      (∑' p : Fin (n + 1) → V, if (List.ofFn p).getLastD x = y then
        walkWeight (offDiagonal a) x p else 0) ≤
        (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a x y) ∧
    (∀ x y : V, x ≠ y →
      ∑' n : ℕ, (∑' p : Fin n → V, if (List.ofFn p).getLastD x = y then
        walkWeight (offDiagonal a) x p else 0) ≤ a x y * ((1 - K)⁻¹ * (1 - m)⁻¹)) ∧
    (Countable V → ∀ q : Sym2 V → unitInterval,
      (∀ v w, v ≠ w → (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) ≤ a v w) →
      ∀ x y : V, x ≠ y → tau q x y ≤ a x y * ((1 - K)⁻¹ * (1 - m)⁻¹)) := by
  set b := offDiagonal a with hb
  have hbxy : ∀ u v, u ≠ v → b u v = a u v := fun u v huv => by
    simp [hb, offDiagonal_apply, huv.symm]
  have hconv' : ∀ u v, u ≠ v → ∑' z, b u z * b z v ≤ K * b u v := fun u v huv => by
    rw [hbxy u v huv]; exact hconv u v huv
  have hbound := le_sum_range_mul_of_convolution b m K hconv'
    (fun n z y => ∑' p : Fin n → V,
      if (List.ofFn p).getLastD z = y then walkWeight b z p else 0)
    (fun z y => tsum_walkWeight_end_zero b z y)
    (fun n x y => tsum_walkWeight_end_succ b n x y)
    (fun n y => (tsum_walkWeight_end_le_walkSum b n y y).trans
      (walkSum_masked_le_pow a m hrow n y))
  have h1 : ∀ (n : ℕ) (x y : V), x ≠ y →
      (∑' p : Fin (n + 1) → V, if (List.ofFn p).getLastD x = y then
        walkWeight b x p else 0) ≤ (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a x y := by
    intro n x y hxy
    rw [← hbxy x y hxy]
    exact hbound n x y hxy
  refine ⟨h1, fun x y hxy => ?_, fun _ q hqa x y hxy =>
    tau_le_of_convolution q a m K hqa hrow hconv hxy⟩
  rw [tsum_eq_zero_add' ENNReal.summable, tsum_walkWeight_end_zero, ite_eq_right hxy, zero_add]
  calc ∑' n : ℕ, (∑' p : Fin (n + 1) → V, if (List.ofFn p).getLastD x = y then
        walkWeight b x p else 0)
      ≤ ∑' n : ℕ, (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a x y :=
        ENNReal.tsum_le_tsum fun n => h1 n x y hxy
    _ = a x y * ((1 - K)⁻¹ * (1 - m)⁻¹) := by
        rw [ENNReal.tsum_mul_right, tsum_sum_range_pow_mul_pow, mul_comm]

/-- On a fixed locally finite host `G`, the percolation probability at `x` is upper
semicontinuous on the profiles vanishing off `G` (diagonal unrestricted), satisfies the
`limsup` inequality along coordinatewise convergent sequences of such profiles, and is
right-continuous along nondecreasing coordinatewise continuous families on a real
interval. -/
@[tag "Y5HD"]
theorem theta_upperSemicontinuous_host [Countable V] (G : SimpleGraph V) [G.LocallyFinite]
    (x : V) :
    UpperSemicontinuousOn (fun q : Sym2 V → unitInterval => law q {ω | (cluster ω x).Infinite})
      {q | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0} ∧
    (∀ (qs : ℕ → Sym2 V → unitInterval) (q : Sym2 V → unitInterval),
      (∀ n e, e ∉ G.edgeSet → ¬ e.IsDiag → qs n e = 0) →
      (∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0) →
      (∀ e, Tendsto (fun n => qs n e) atTop (𝓝 (q e))) →
      limsup (fun n => law (qs n) {ω | (cluster ω x).Infinite}) atTop ≤
        law q {ω | (cluster ω x).Infinite}) ∧
    (∀ (I : Set ℝ) (q : I → Sym2 V → unitInterval), Monotone q →
      (∀ e, Continuous (q · e)) → (∀ s e, e ∉ G.edgeSet → ¬ e.IsDiag → q s e = 0) →
      ∀ t : I, ContinuousWithinAt (fun s => law (q s) {ω | (cluster ω x).Infinite})
        (Ici t) t) := by
  have husc := upperSemicontinuousOn_law_cluster_infinite G x
  refine ⟨husc, fun qs q hqs hq hconv => ?_, fun I q hmono hcont hG t =>
    continuousWithinAt_law_cluster_infinite_Ici G hmono hcont hG x t⟩
  have hT : Tendsto qs atTop
      (𝓝[{q : Sym2 V → unitInterval | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0}] q) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 hconv, Eventually.of_forall hqs⟩
  have hw : UpperSemicontinuousWithinAt
      (fun q : Sym2 V → unitInterval => law q {ω | (cluster ω x).Infinite})
      {q : Sym2 V → unitInterval | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0} q := husc q hq
  exact (hT.limsup_comp_le_limsup
    (u := fun q : Sym2 V → unitInterval => law q {ω | (cluster ω x).Infinite})).trans
    hw.limsup_le

end PercLib.Percolation.Bond
