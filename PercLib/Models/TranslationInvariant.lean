/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-14, from pinned mathlib's `Sym2.lift`, `Equiv.tsum_eq` and ENNReal
sums, and the row-sum theorems of `PercLib.Percolation.Bond.RowSum` and the intensity bounds of
`PercLib.Percolation.Bond.Intensity`. No upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity

/-! # Translation-invariant kernels on additive groups, and `ℤ^d`

On an additive group `G`, a pair intensity is translation invariant when `J s(x,y) = k (y - x)` for
a displacement kernel `k`. Such a `J` exists exactly when `k` is even, because pairs are unordered
(`exists_sym2_kernel`). For a kernel `J x y` on ordered pairs equal to `k (y - x)` off the
diagonal, no symmetry is needed: the off-diagonal row at every vertex is `∑'_{z ≠ 0} k z`
(`rowSum_eq_of_offDiagonal_translationInvariant`). Its unordered form
(`rowSum_eq_of_translationInvariant`) lets the row-sum and intensity bounds apply with `M` any
bound on `∑' z, k z`.

`ℤ^d` is `Fin d → ℤ`. The compiled witness at the end uses the nearest-neighbour kernel
along one coordinate axis; it is nonzero, its row sum is two, and at `β = 1/4` the
susceptibility is at most two at every vertex and both thresholds are at least `1/2`.

The kernel `k` is a hypothesis-bound function, so this file adds no definition.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {G : Type*} [AddGroup G]

/-- Every even displacement kernel is the kernel of a pair intensity on unordered
pairs. -/
theorem exists_sym2_kernel (k : G → ℝ≥0) (hk : ∀ z, k (-z) = k z) :
    ∃ J : Sym2 G → ℝ≥0, ∀ x y, J s(x,y) = k (y - x) :=
  ⟨Sym2.lift ⟨fun x y => k (y - x), fun x y => by
      change k (y - x) = k (x - y)
      rw [← hk, neg_sub]⟩,
    fun x y => Sym2.lift_mk _ x y⟩

open Classical in
/-- The off-diagonal row of a kernel on ordered pairs that equals a displacement kernel off
the diagonal is the kernel mass away from zero, whatever its diagonal values. No symmetry of
`k` is needed. -/
theorem rowSum_eq_of_offDiagonal_translationInvariant (J : G → G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J x y = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J v w : ℝ≥0∞)) =
      ∑' z, if z = 0 then 0 else (k z : ℝ≥0∞) := by
  rw [← (Equiv.addRight v).tsum_eq]
  refine tsum_congr fun z => ?_
  by_cases hz : z = 0
  · simp [hz]
  · have hne : v ≠ z + v := fun h => hz (by simpa using h.symm)
    simp [hz, hJ v (z + v) hne]

open Classical in
/-- The off-diagonal row of a kernel on ordered pairs that equals a displacement kernel off
the diagonal is at most the total kernel mass. -/
theorem rowSum_le_tsum_of_offDiagonal_translationInvariant (J : G → G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J x y = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J v w : ℝ≥0∞)) ≤ ∑' z, (k z : ℝ≥0∞) := by
  rw [rowSum_eq_of_offDiagonal_translationInvariant J k hJ v]
  exact ENNReal.tsum_le_tsum fun z => by split_ifs <;> simp

/-- A kernel identity `J(x,y) = k(y - x)` on distinct pairs forces `k` to be even. -/
theorem neg_eq_of_translationInvariant_of_ne (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = k (y - x)) (z : G) : k (-z) = k z := by
  by_cases hz : z = 0
  · rw [hz, neg_zero]
  · have h1 := hJ 0 z (Ne.symm hz)
    have h2 := hJ z 0 hz
    rw [Sym2.eq_swap, h2, sub_zero, zero_sub] at h1
    exact h1

open Classical in
/-- The off-diagonal row identity when the kernel identity is assumed on distinct pairs only
(the diagonal is arbitrary). -/
theorem rowSum_eq_of_translationInvariant_of_ne (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = k (y - x)) (v : G) :
    rowSum (fun e => (J e : ℝ≥0∞)) v =
      ∑' z, if z = 0 then 0 else (k z : ℝ≥0∞) := by
  rw [rowSum_def]
  exact rowSum_eq_of_offDiagonal_translationInvariant (fun x y => J s(x, y)) k hJ v

/-- The off-diagonal row bound when the kernel identity is assumed on distinct pairs only. -/
theorem rowSum_le_tsum_of_translationInvariant_of_ne (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = k (y - x)) (v : G) :
    rowSum (fun e => (J e : ℝ≥0∞)) v ≤ ∑' z, (k z : ℝ≥0∞) := by
  classical
  rw [rowSum_def]
  exact rowSum_le_tsum_of_offDiagonal_translationInvariant (fun x y => J s(x, y)) k hJ v

open Classical in
/-- A translation-invariant pair intensity has the same off-diagonal row at every vertex:
the sum of the kernel away from zero. -/
theorem rowSum_eq_of_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y - x)) (v : G) :
    rowSum (fun e => (J e : ℝ≥0∞)) v =
      ∑' z, if z = 0 then 0 else (k z : ℝ≥0∞) :=
  rowSum_eq_of_translationInvariant_of_ne J k (fun x y _ => hJ x y) v

/-- The off-diagonal row of a translation-invariant pair intensity is at most the total
mass of its kernel. -/
theorem rowSum_le_tsum_of_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y - x)) (v : G) :
    rowSum (fun e => (J e : ℝ≥0∞)) v ≤ ∑' z, (k z : ℝ≥0∞) :=
  rowSum_le_tsum_of_translationInvariant_of_ne J k (fun x y _ => hJ x y) v

open Classical in
/-- **Row-sum bound for translation-invariant profiles.** If `q s(x,y) = p (y - x)` and the
off-diagonal mass of `p` is at most `m < 1`, then `chi q x ≤ (1 - m)⁻¹`. -/
theorem chi_le_of_translationInvariant [Countable G] (q : Sym2 G → unitInterval)
    (p : G → unitInterval) (hq : ∀ x y, q s(x, y) = p (y - x)) (m : ℝ≥0∞)
    (hp : (∑' z, if z = 0 then 0 else (unitInterval.toNNReal (p z) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) (x : G) : chi q x ≤ (1 - m)⁻¹ :=
  chi_le_inv_one_sub_of_rowSum q m (fun v =>
    (rowSum_eq_of_translationInvariant (fun e => unitInterval.toNNReal (q e))
      (fun z => unitInterval.toNNReal (p z))
      (fun x y => congrArg unitInterval.toNNReal (hq x y)) v).le.trans hp) hm x

/-- **Intensity bound for translation-invariant intensities: susceptibility.** -/
theorem chi_intensity_le_of_translationInvariant [Countable G] (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x)) (M : ℝ≥0)
    (hk : ∑' z, (k z : ℝ≥0∞) ≤ M) (β : ℝ≥0) (hβ : (β : ℝ≥0∞) * M < 1) (x : G) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) * M)⁻¹ :=
  chi_intensity_le J M (fun v => (rowSum_le_tsum_of_translationInvariant J k hJ v).trans hk)
    β hβ x

/-- **Intensity bound for translation-invariant intensities: global threshold.** -/
theorem inv_le_globalCriticalIntensity_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x)) (M : ℝ≥0)
    (hk : ∑' z, (k z : ℝ≥0∞) ≤ M) :
    (M : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J :=
  inv_le_globalCriticalIntensity J M fun v =>
    (rowSum_le_tsum_of_translationInvariant J k hJ v).trans hk

/-- **Intensity bound for translation-invariant intensities: root threshold.** -/
theorem inv_le_rootCriticalIntensity_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x)) (M : ℝ≥0)
    (hk : ∑' z, (k z : ℝ≥0∞) ≤ M) (x : G) :
    (M : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x :=
  inv_le_rootCriticalIntensity J M (fun v =>
    (rowSum_le_tsum_of_translationInvariant J k hJ v).trans hk) x

/-! ### A two-point kernel -/

omit [AddGroup G] in
/-- A point mass sums to one. -/
theorem tsum_coe_ite_eq_one [DecidableEq G] (b : G) :
    (∑' z, (((if z = b then 1 else 0 : ℝ≥0)) : ℝ≥0∞)) = 1 := by
  rw [show (fun z => (((if z = b then 1 else 0 : ℝ≥0)) : ℝ≥0∞)) =
      fun z => if z = b then 1 else 0 from funext fun z => by split_ifs <;> simp]
  exact tsum_ite_eq b 1

/-- The kernel with unit mass at `a` and at `-a` has total mass two. -/
theorem tsum_twoPointKernel [DecidableEq G] (a : G) :
    (∑' z, ((((if z = a then 1 else 0) + (if z = -a then 1 else 0) : ℝ≥0)) : ℝ≥0∞)) = 2 := by
  simp_rw [ENNReal.coe_add]
  rw [ENNReal.tsum_add, tsum_coe_ite_eq_one a, tsum_coe_ite_eq_one (-a)]
  exact one_add_one_eq_two

/-- The kernel with unit mass at `a` and at `-a` is even. -/
theorem twoPointKernel_neg [DecidableEq G] (a z : G) :
    ((if -z = a then 1 else 0) + (if -z = -a then 1 else 0) : ℝ≥0) =
      (if z = a then 1 else 0) + (if z = -a then 1 else 0) := by
  rw [add_comm]
  congr 1 <;> simp [neg_eq_iff_eq_neg]

end PercLib.Models

/-! ### Non-vacuity on `ℤ^d` -/
section Witnesses

open PercLib.Models

/-- On `ℤ^d`, `d ≥ 1`, the nearest-neighbour kernel along the axis `i` gives a nonzero
translation-invariant intensity. At `β = 1/4` its susceptibility is at most two at every
vertex, and both thresholds are at least `1/2`. -/
example (d : ℕ) (i : Fin d) (x : Fin d → ℤ) :
    ∃ J : Sym2 (Fin d → ℤ) → ℝ≥0, J ≠ 0 ∧
      chi (intensityProfile J (1 / 4)) x ≤
        (1 - ((1 / 4 : ℝ≥0) : ℝ≥0∞) * ((2 : ℝ≥0) : ℝ≥0∞))⁻¹ ∧
      ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
      ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x := by
  set a : Fin d → ℤ := Pi.single i 1
  set k : (Fin d → ℤ) → ℝ≥0 := fun z => (if z = a then 1 else 0) + (if z = -a then 1 else 0)
  obtain ⟨J, hJ⟩ := exists_sym2_kernel k (twoPointKernel_neg a)
  have hk : ∑' z, (k z : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞) :=
    (tsum_twoPointKernel a).le.trans (by simp)
  refine ⟨J, ?_, chi_intensity_le_of_translationInvariant J k hJ 2 hk (1 / 4) ?_ x,
    inv_le_globalCriticalIntensity_of_translationInvariant J k hJ 2 hk,
    inv_le_rootCriticalIntensity_of_translationInvariant J k hJ 2 hk x⟩
  · intro h
    have h0 := congrFun h s(0, a)
    rw [hJ] at h0
    simp [k] at h0
  · rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    norm_num

end Witnesses

/-! ### Displacement kernels on general groups

On a group `G` written multiplicatively, the displacement convention is
`J s(x, y) = k (y * x⁻¹)`. The prescription is well defined on unordered pairs exactly when
`k` is inversion-even (`exists_sym2_kernel_mul_iff`); such a `J` is invariant under
simultaneous right translation (`apply_mk_mul_right_of_mulTranslationInvariant`), and under
simultaneous left translation exactly when `k` is conjugation invariant
(`forall_apply_mk_mul_left_iff_of_mulTranslationInvariant`). The additive statements above are
the case `Multiplicative G` of these (see the example after `exists_sym2_kernel_mul_iff`). -/

namespace PercLib.Models

section MulGroup

variable {G α : Type*} [Group G]

/-- A kernel identity `J s(x, y) = k (y * x⁻¹)` on unordered pairs forces `k` to be
inversion-even. -/
theorem inv_eq_of_mulTranslationInvariant {J : Sym2 G → α} {k : G → α}
    (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹)) (z : G) : k z⁻¹ = k z := by
  have h := hJ 1 z
  rw [Sym2.eq_swap, hJ z 1, inv_one, mul_one, one_mul] at h
  exact h

/-- Every inversion-even kernel is the displacement kernel `J s(x, y) = k (y * x⁻¹)` of a
function on unordered pairs, including the repeated pairs `s(x, x)`. -/
theorem exists_sym2_kernel_mul (k : G → α) (hk : ∀ z, k z⁻¹ = k z) :
    ∃ J : Sym2 G → α, ∀ x y, J s(x, y) = k (y * x⁻¹) :=
  ⟨Sym2.lift ⟨fun x y => k (y * x⁻¹), fun x y => by
      change k (y * x⁻¹) = k (x * y⁻¹)
      rw [← hk, mul_inv_rev, inv_inv]⟩,
    fun x y => Sym2.lift_mk _ x y⟩

/-- **Even displacement kernels.** The prescription `J s(x, y) = k (y * x⁻¹)` defines a
function on unordered pairs if and only if `k` is inversion-even. -/
theorem exists_sym2_kernel_mul_iff (k : G → α) :
    (∃ J : Sym2 G → α, ∀ x y, J s(x, y) = k (y * x⁻¹)) ↔ ∀ z, k z⁻¹ = k z :=
  ⟨fun ⟨_, hJ⟩ => inv_eq_of_mulTranslationInvariant hJ, exists_sym2_kernel_mul k⟩

/-- A displacement kernel `J s(x, y) = k (y * x⁻¹)` is invariant under simultaneous right
translation. -/
theorem apply_mk_mul_right_of_mulTranslationInvariant {J : Sym2 G → α} {k : G → α}
    (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹)) (g x y : G) :
    J s(x * g, y * g) = J s(x, y) := by
  rw [hJ, hJ, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

/-- A displacement kernel `J s(x, y) = k (y * x⁻¹)` is invariant under every simultaneous
left translation if and only if `k` is conjugation invariant. -/
theorem forall_apply_mk_mul_left_iff_of_mulTranslationInvariant {J : Sym2 G → α} {k : G → α}
    (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹)) :
    (∀ g x y, J s(g * x, g * y) = J s(x, y)) ↔ ∀ g z, k (g * z * g⁻¹) = k z := by
  have hconj : ∀ g x y, J s(g * x, g * y) = k (g * (y * x⁻¹) * g⁻¹) := fun g x y => by
    rw [hJ, mul_inv_rev, mul_assoc, mul_assoc, mul_assoc]
  constructor
  · intro h g z
    have := h g 1 z
    rwa [hconj, hJ, inv_one, mul_one] at this
  · intro h g x y
    rw [hconj, h, hJ]

/-- The additive statement `exists_sym2_kernel` is the case `Multiplicative G` of
`exists_sym2_kernel_mul_iff`. -/
example {A : Type*} [AddGroup A] (k : A → ℝ≥0) (hk : ∀ z, k (-z) = k z) :
    ∃ J : Sym2 A → ℝ≥0, ∀ x y, J s(x, y) = k (y - x) := by
  obtain ⟨J, hJ⟩ := (exists_sym2_kernel_mul_iff (G := Multiplicative A) (fun z => k z.toAdd)).2 hk
  exact ⟨J, fun x y => (hJ (.ofAdd x) (.ofAdd y)).trans (by simp [sub_eq_add_neg])⟩

open Classical in
/-- A displacement kernel `J s(x, y) = k (y * x⁻¹)` has the same off-diagonal row at every
vertex: the kernel mass away from the identity. This is the case `Additive G` of
`rowSum_eq_of_translationInvariant`. -/
theorem rowSum_eq_of_mulTranslationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹)) (v : G) :
    rowSum (fun e => (J e : ℝ≥0∞)) v =
      ∑' z, if z = 1 then 0 else (k z : ℝ≥0∞) :=
  rowSum_eq_of_translationInvariant (G := Additive G) J (fun z => k z.toMul)
    (fun x y => (hJ x.toMul y.toMul).trans (by rw [toMul_sub, div_eq_mul_inv])) v

end MulGroup

end PercLib.Models
