/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-14. No upstream proof is copied.
-/
module

public import PercLib.Models.TranslationInvariant
public import PercLib.Percolation.Bond.InfiniteDegree
public import PercLib.Models.HierarchicalCutoff

/-!
# Non-summable translation-invariant kernels percolate at every positive intensity

On a countable additive group with `J s(x, y) = k (y - x)`, the off-diagonal row of `J` is
`∑'_{z ≠ 0} k z` at every vertex (`rowSum_eq_of_translationInvariant`). If that sum is
infinite, both critical intensities vanish, at every root. This file adds no definition.
-/

@[expose] public section

open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {G : Type*} [AddGroup G]

open Classical in
/-- **A non-summable translation-invariant kernel has root critical intensity zero at
every vertex.** -/
theorem rootCriticalIntensity_eq_zero_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x))
    (hk : (∑' z, if z = 0 then 0 else (k z : ℝ≥0∞)) = ∞) (v : G) :
    rootCriticalIntensity J v = 0 :=
  rootCriticalIntensity_eq_zero_of_rowSum_eq_top J v
    (by rw [rowSum_eq_of_translationInvariant J k hJ v]; exact hk)

open Classical in
/-- **A non-summable translation-invariant kernel has global critical intensity zero.** -/
theorem globalCriticalIntensity_eq_zero_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x))
    (hk : (∑' z, if z = 0 then 0 else (k z : ℝ≥0∞)) = ∞) :
    globalCriticalIntensity J = 0 :=
  globalCriticalIntensity_eq_zero_of_rowSum_eq_top J 0
    (by rw [rowSum_eq_of_translationInvariant J k hJ 0]; exact hk)

/-! ### Non-vacuity: the constant kernel on `ℤ`. -/

open Classical in
example (v : ℤ) : rootCriticalIntensity (fun _ : Sym2 ℤ => 1) v = 0 ∧
    globalCriticalIntensity (fun _ : Sym2 ℤ => 1) = 0 := by
  refine ⟨rootCriticalIntensity_eq_zero_of_translationInvariant _ (fun _ => 1)
      (fun _ _ => rfl) ?_ v,
    globalCriticalIntensity_eq_zero_of_translationInvariant _ (fun _ => 1)
      (fun _ _ => rfl) ?_⟩ <;>
  convert tsum_ite_const_eq_top (V := ℤ) (c := ((1 : ℝ≥0) : ℝ≥0∞)) 0 (by simp)

end PercLib.Models

/-! ### Non-summable displacement kernels on general groups

On a countable group written multiplicatively, with `J s(x, y) = k (y * x⁻¹)` and
`∑'_{z ≠ 1} k z = ∞`, every positive intensity gives every vertex infinitely many open
neighbours almost surely, for any diagonal probabilities; both critical intensities vanish.
At intensity zero there are no open edges and every cluster is a singleton. -/

namespace PercLib.Models

section MulGroup

variable {G : Type*} [Group G]

open Classical in
/-- A non-summable displacement kernel has an infinite off-diagonal row at every vertex. -/
theorem rowSum_eq_top_of_mulTranslationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹))
    (hk : (∑' z, if z = 1 then 0 else (k z : ℝ≥0∞)) = ∞) (v : G) :
    rowSum (fun e => (J e : ℝ≥0∞)) v = ∞ := by
  rw [rowSum_eq_of_mulTranslationInvariant J k hJ v, hk]

variable [Countable G]

open Classical in
/-- **Infinite degree at every vertex.** For a non-summable displacement kernel and `β > 0`,
under independent bonds whose off-diagonal probabilities are those of
`intensityProfile J β` (the diagonal ones are arbitrary), almost surely every vertex has
infinitely many open neighbours. -/
theorem ae_forall_neighborSet_infinite_of_mulTranslationInvariant (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹))
    (hk : (∑' z, if z = 1 then 0 else (k z : ℝ≥0∞)) = ∞) {β : ℝ≥0} (hβ : 0 < β)
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y, x ≠ y → q s(x, y) = intensityProfile J β s(x, y)) :
    ∀ᵐ ω ∂law q, ∀ v, ((openGraph ω).neighborSet v).Infinite := by
  refine MeasureTheory.ae_all_iff.2 fun v => ae_infinite_neighbors_of_rowSum_eq_top q v ?_
  rw [rowSum_congr_offDiag (b := fun e => unitInterval.toENNReal (intensityProfile J β e))
    fun w hw => by rw [hq v w (Ne.symm hw)]]
  exact rowSum_intensityProfile_eq_top J v hβ
    (rowSum_eq_top_of_mulTranslationInvariant J k hJ hk v)

open Classical in
/-- **Infinite cluster at every vertex.** For a non-summable displacement kernel and `β > 0`,
with arbitrary diagonal probabilities, almost surely every cluster is infinite. -/
theorem ae_forall_cluster_infinite_of_mulTranslationInvariant (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹))
    (hk : (∑' z, if z = 1 then 0 else (k z : ℝ≥0∞)) = ∞) {β : ℝ≥0} (hβ : 0 < β)
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y, x ≠ y → q s(x, y) = intensityProfile J β s(x, y)) :
    ∀ᵐ ω ∂law q, ∀ v, (cluster ω v).Infinite := by
  filter_upwards [ae_forall_neighborSet_infinite_of_mulTranslationInvariant J k hJ hk hβ q hq]
    with ω hω v
  exact (hω v).mono fun w hw => SimpleGraph.Adj.reachable hw

open Classical in
/-- **A non-summable displacement kernel has root critical intensity zero at every
vertex.** -/
theorem rootCriticalIntensity_eq_zero_of_mulTranslationInvariant (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹))
    (hk : (∑' z, if z = 1 then 0 else (k z : ℝ≥0∞)) = ∞) (v : G) :
    rootCriticalIntensity J v = 0 :=
  rootCriticalIntensity_eq_zero_of_rowSum_eq_top J v
    (rowSum_eq_top_of_mulTranslationInvariant J k hJ hk v)

open Classical in
/-- **A non-summable displacement kernel has global critical intensity zero.** -/
theorem globalCriticalIntensity_eq_zero_of_mulTranslationInvariant (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹))
    (hk : (∑' z, if z = 1 then 0 else (k z : ℝ≥0∞)) = ∞) :
    globalCriticalIntensity J = 0 :=
  globalCriticalIntensity_eq_zero_of_rowSum_eq_top J 1
    (rowSum_eq_top_of_mulTranslationInvariant J k hJ hk 1)

end MulGroup

section Zero

variable {V : Type*} [Countable V]

/-- At intensity zero, whatever the diagonal probabilities, almost surely there is no open
edge. -/
theorem ae_openGraph_eq_bot_of_intensity_zero (J : Sym2 V → ℝ≥0) (q : Sym2 V → unitInterval)
    (hq : ∀ x y, x ≠ y → q s(x, y) = intensityProfile J 0 s(x, y)) :
    ∀ᵐ ω ∂law q, openGraph ω = ⊥ := by
  filter_upwards [ae_openGraph_le_of_offDiagonal ⊥ q fun x y h _ => by
    rw [hq x y h, intensityProfile_zero]] with ω hω
  exact le_bot_iff.1 hω

/-- At intensity zero, whatever the diagonal probabilities, almost surely every cluster is a
singleton. -/
theorem ae_cluster_eq_singleton_of_intensity_zero (J : Sym2 V → ℝ≥0)
    (q : Sym2 V → unitInterval)
    (hq : ∀ x y, x ≠ y → q s(x, y) = intensityProfile J 0 s(x, y)) :
    ∀ᵐ ω ∂law q, ∀ x, cluster ω x = {x} :=
  ae_cluster_eq_singleton_of_offDiagonal q fun x y h => by
    rw [hq x y h, intensityProfile_zero]

end Zero

/-! ### Non-vacuity: the constant kernel on `ℤ`, written multiplicatively -/

open Classical in
example (v : Multiplicative ℤ) :
    rootCriticalIntensity (fun _ : Sym2 (Multiplicative ℤ) => 1) v = 0 ∧
      globalCriticalIntensity (fun _ : Sym2 (Multiplicative ℤ) => 1) = 0 := by
  have : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
  refine ⟨rootCriticalIntensity_eq_zero_of_mulTranslationInvariant _ (fun _ => 1)
      (fun _ _ => rfl) ?_ v,
    globalCriticalIntensity_eq_zero_of_mulTranslationInvariant _ (fun _ => 1)
      (fun _ _ => rfl) ?_⟩ <;>
  convert tsum_ite_const_eq_top (V := Multiplicative ℤ) (c := ((1 : ℝ≥0) : ℝ≥0∞)) 1 (by simp)

end PercLib.Models
