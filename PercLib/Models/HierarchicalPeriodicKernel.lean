/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs. Reference: T. Hutchcroft, *Critical cluster volumes in hierarchical percolation*,
arXiv:2211.05686 (the exact radial kernel and periodic boundary conditions on a block).
-/
module

public import PercLib.Models.HierarchicalBlockLayers
public import PercLib.Models.LongRange.OmittedLayer

/-! # The periodic block kernel of the hierarchical lattice

On `V = ℕ →₀ A` let `π_n` keep the coordinates below `n`, so that `block n 0` is the quotient
of `V` by the coordinates `≥ n`. The periodic kernel on `block n 0` sums the exact radial kernel
`J_∞` over the fibres of `π_n`. For the hierarchical lattice `A = Fin d → ZMod L`, `L ≥ 2`,
`s = d + α`, `α > 0` and `q = L^{-α}`, the fibre over `y` consists of `y` and, for every `k ≥ 1`,
of `(Q - 1) Q^{k-1}` points at level `n + k` from `x` (`Q = L^d`), and summing gives

  `J_n^per(x,y) = J_n(x,y) + q/(1 - q) L^{-sn}`,

with `J_n` the truncated kernel of the block. The extra constant is an independent
complete-graph layer: periodic percolation on `block n 0` is the truncated block law together
with one more coalescent stage, equivalently its last layer runs to time `β L^{-sn}/(1 - q)`.

## Main results

* `hasSum_projFibre_exactKernel`: the fibre sum converges to `J_n(x,y) + q/(1-q) L^{-sn}`.
* `periodicKernel_eq_add_completeKernel`: `J_n^per = J_n + q/(1-q) L^{-sn}` on `block n 0`.
* `periodicKernel_eq_sub_add_completeKernel`: `J_n^per` is the kernel of the layers below level
  `n` plus a complete-graph layer of weight `L^{-sn}/(1 - q)`.
* `law_periodicKernel_eq_map_union`, `law_periodicKernel_eq_map_union_lastLayer`: the
  corresponding decompositions of the periodic bond law into independent layers.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models.HierarchicalLayers

open PercLib.Percolation.Bond

section Fibre

variable {A : Type*} [AddCommGroup A]

/-- Shifting coordinates up by `n`: the value at `i + n` is the value at `i`. -/
theorem mapDomain_add_apply (n : ℕ) (w : ℕ →₀ A) (i : ℕ) :
    w.mapDomain (· + n) (i + n) = w i :=
  Finsupp.mapDomain_apply_of_injective (add_left_injective n) w i

/-- Shifting coordinates up by `n` leaves the coordinates below `n` zero. -/
theorem mapDomain_add_apply_of_lt {n j : ℕ} (w : ℕ →₀ A) (hj : j < n) :
    w.mapDomain (· + n) j = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨i, hi⟩; simp only at hi; omega)

/-- A vertex of `block n 0` vanishes at the coordinates `≥ n`. -/
theorem apply_eq_zero_of_mem_block {n j : ℕ} {y : ℕ →₀ A} (hy : y ∈ block n 0) (hj : n ≤ j) :
    y j = 0 := by
  by_contra h
  have hb := mem_block.mp hy
  rw [sub_zero] at hb
  have := (level_le_iff_support y n).mp hb j (Finsupp.mem_support_iff.mpr h)
  omega

theorem add_mapDomain_mem_projFibre {n : ℕ} {y : ℕ →₀ A} (hy : y ∈ block n 0) (w : ℕ →₀ A) :
    y + w.mapDomain (· + n) ∈ projFibre n y := by
  have h0 : (w.mapDomain (· + n)).filter (· < n) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    exact fun i hi => mapDomain_add_apply_of_lt w hi
  rw [mem_projFibre, Finsupp.filter_add, filter_eq_self_of_mem_block hy, h0, add_zero]

/-- The fibre of `π_n` over `y ∈ block n 0` is parametrised by `V` through
`w ↦ y + (w shifted up by n)`. -/
def projFibreEquiv {n : ℕ} {y : ℕ →₀ A} (hy : y ∈ block n 0) : (ℕ →₀ A) ≃ projFibre n y :=
  Equiv.ofBijective (fun w => ⟨y + w.mapDomain (· + n), add_mapDomain_mem_projFibre hy w⟩) <| by
    constructor
    · intro w w' h
      have h' : y + w.mapDomain (· + n) = y + w'.mapDomain (· + n) := congrArg Subtype.val h
      exact Finsupp.mapDomain_injective (add_left_injective n) (add_left_cancel h')
    · rintro ⟨z, hz⟩
      rw [mem_projFibre] at hz
      refine ⟨Finsupp.comapDomain (· + n) (z - y) (add_left_injective n).injOn, ?_⟩
      apply Subtype.ext
      change y + _ = z
      rw [← eq_sub_iff_add_eq']
      ext j
      by_cases hj : j < n
      · rw [mapDomain_add_apply_of_lt _ hj, Finsupp.sub_apply, ← hz, Finsupp.filter_apply,
          ite_eq_left hj, sub_self]
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + n := ⟨j - n, by omega⟩
        rw [mapDomain_add_apply, Finsupp.comapDomain_apply]

@[simp] theorem coe_projFibreEquiv_apply {n : ℕ} {y : ℕ →₀ A} (hy : y ∈ block n 0)
    (w : ℕ →₀ A) : (projFibreEquiv hy w : ℕ →₀ A) = y + w.mapDomain (· + n) := rfl

/-- For `x, y ∈ block n 0` and `w ≠ 0`, the point `y + (w shifted up by n)` is at level
`h(w) + n` from `x`. -/
theorem level_add_mapDomain_sub {n : ℕ} {x y : ℕ →₀ A} (hx : x ∈ block n 0)
    (hy : y ∈ block n 0) {w : ℕ →₀ A} (hw : w ≠ 0) :
    (y + w.mapDomain (· + n) - x).support.sup Nat.succ = w.support.sup Nat.succ + n := by
  have hval : ∀ i, (y + w.mapDomain (· + n) - x) (i + n) = w i := by
    intro i
    rw [Finsupp.sub_apply, Finsupp.add_apply, mapDomain_add_apply,
      apply_eq_zero_of_mem_block hx (by omega), apply_eq_zero_of_mem_block hy (by omega),
      zero_add, sub_zero]
  apply le_antisymm
  · apply (level_le_iff_support _ _).mpr
    intro j hj
    by_cases hjn : j < n
    · omega
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + n := ⟨j - n, by omega⟩
      rw [Finsupp.mem_support_iff, hval] at hj
      have := Finset.le_sup (f := Nat.succ) (Finsupp.mem_support_iff.mpr hj)
      omega
  · obtain ⟨i, hi, hsup⟩ :=
      Finset.exists_mem_eq_sup w.support (Finsupp.support_nonempty_iff.mpr hw) Nat.succ
    have hmem : i + n ∈ (y + w.mapDomain (· + n) - x).support := by
      rw [Finsupp.mem_support_iff, hval]
      exact Finsupp.mem_support_iff.mp hi
    have := Finset.le_sup (f := Nat.succ) hmem
    rw [hsup]
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega

/-- The condition defining the pairs of `block n x`, for a pair `s(y, z)`. -/
theorem mk_pair_mem_block_iff {n : ℕ} {x y z : ℕ →₀ A} :
    (¬ s(y, z).IsDiag ∧ ∀ v ∈ s(y, z), v ∈ block n x) ↔
      (y ≠ z ∧ y ∈ block n x ∧ z ∈ block n x) := by
  simp only [Sym2.mk_isDiag_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq, ne_eq]

end Fibre

/-! ### The fibre sum on the hierarchical lattice -/

section Lattice

variable {d L : ℕ}

/-- The fibre sum in `ℝ≥0∞`: `∑_{π_n z = y} J_∞(x,z) = J_∞(x,y) + r^n/(1-r) · (Q-1) r/(1-Qr)`
with `r = L^{-s}` and `Q = L^d`. -/
theorem tsum_projFibre_exactKernel [NeZero L] {s : ℝ} (hL : 1 < (L : ℝ)) (hs : 0 < s) {n : ℕ}
    {x y : ℕ →₀ (Fin d → ZMod L)} (hx : x ∈ block n 0) (hy : y ∈ block n 0) :
    ∑' z : projFibre n y, (exactKernel (L : ℝ) s s(x, z) : ℝ≥0∞) =
      (exactKernel (L : ℝ) s s(x, y) : ℝ≥0∞) +
        ENNReal.ofReal (((L : ℝ) ^ (-s)) ^ n / (1 - (L : ℝ) ^ (-s))) *
          ((((L ^ d - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((L : ℝ) ^ (-s))) *
            (1 - (L : ℝ≥0∞) ^ d * ENNReal.ofReal ((L : ℝ) ^ (-s)))⁻¹) := by
  classical
  set r : ℝ := (L : ℝ) ^ (-s) with hr
  have hr0 : 0 ≤ r := rpow_neg_nonneg hL
  have hr1 : r < 1 := rpow_neg_lt_one hL hs
  rw [← (projFibreEquiv hy).tsum_eq, ← tsum_geometricRadial_eq, ← ENNReal.tsum_mul_left]
  have hfun : (fun w : ℕ →₀ (Fin d → ZMod L) =>
      (exactKernel (L : ℝ) s s(x, (projFibreEquiv hy w : ℕ →₀ (Fin d → ZMod L))) : ℝ≥0∞)) =
      fun w => (if w = 0 then (exactKernel (L : ℝ) s s(x, y) : ℝ≥0∞) else 0) +
        ENNReal.ofReal (r ^ n / (1 - r)) *
          (if w = 0 then 0 else ENNReal.ofReal r ^ (w.support.sup Nat.succ)) := by
    funext w
    rw [coe_projFibreEquiv_apply]
    by_cases hw : w = 0
    · simp [hw]
    · have hlev := level_add_mapDomain_sub hx hy hw
      have hne : ¬ s(x, y + w.mapDomain (· + n)).IsDiag := by
        rw [Sym2.mk_isDiag_iff]
        intro h
        rw [← h, sub_self] at hlev
        have := (level_eq_zero_iff w).not.mpr hw
        simp at hlev
        omega
      rw [ite_eq_right hw, ite_eq_right hw, zero_add, exactKernel_of_not_isDiag hne, pairLevel_mk,
        hlev, exact_closed_form hL hs]
      change ENNReal.ofReal _ = _
      rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hr0 _)
        (sub_nonneg.mpr hr1.le)), pow_add]
      congr 1
      ring
  rw [hfun, ENNReal.tsum_add, tsum_ite_eq]

/-- `L^d L^{-(d+α)} = L^{-α}`. -/
theorem pow_mul_rpow_neg_add (hL : 0 < (L : ℝ)) (d : ℕ) (α : ℝ) :
    (L : ℝ) ^ d * (L : ℝ) ^ (-((d : ℝ) + α)) = (L : ℝ) ^ (-α) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hL]
  congr 1
  ring

/-- The fibre sum in closed form: for distinct `x, y ∈ block n 0`,
`∑_{π_n z = y} J_∞(x,z) = J_n(x,y) + q/(1-q) L^{-sn}` with `s = d + α`, `q = L^{-α}`. -/
theorem tsum_projFibre_exactKernel_eq_ofReal (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) {n : ℕ}
    {x y : ℕ →₀ (Fin d → ZMod L)} (hx : x ∈ block n 0) (hy : y ∈ block n 0) (hxy : x ≠ y) :
    ∑' z : projFibre n y, (exactKernel (L : ℝ) (d + α) s(x, z) : ℝ≥0∞) =
      ENNReal.ofReal ((truncatedKernel (L : ℝ) (d + α) n 0 s(x, y) : ℝ) +
        (L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-α)) * (L : ℝ) ^ (-((d + α) * n))) := by
  have : NeZero L := ⟨by omega⟩
  set s : ℝ := d + α with hs_def
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hs : 0 < s := by positivity
  set r : ℝ := (L : ℝ) ^ (-s) with hr
  set Q : ℝ := (L : ℝ) ^ d with hQ
  have hr0 : 0 ≤ r := rpow_neg_nonneg hL1
  have hr1 : r < 1 := rpow_neg_lt_one hL1 hs
  have hQr : Q * r = (L : ℝ) ^ (-α) := pow_mul_rpow_neg_add hL0 d α
  have hQr1 : Q * r < 1 := hQr ▸ rpow_neg_lt_one hL1 hα
  have hQ1 : (1 : ℝ) ≤ Q := one_le_pow₀ hL1.le
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hQm1 : (0 : ℝ) ≤ Q - 1 := by linarith
  have hA : 0 ≤ (Q - 1) * r := mul_nonneg hQm1 hr0
  have hB : 0 ≤ r ^ n / (1 - r) := div_nonneg (pow_nonneg hr0 _) (by linarith)
  have hC : 0 ≤ r ^ n / (1 - r) * ((Q - 1) * r * (1 - Q * r)⁻¹) :=
    mul_nonneg hB (mul_nonneg hA (inv_nonneg.mpr (by linarith)))
  have hJ0 : (0 : ℝ) ≤ exactKernel (L : ℝ) s s(x, y) := NNReal.coe_nonneg _
  have hQE : (L : ℝ≥0∞) ^ d = ENNReal.ofReal Q := by
    rw [hQ, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have e1 : ((L ^ d - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal r = ENNReal.ofReal ((Q - 1) * r) := by
    rw [ENNReal.ofReal_mul hQm1, ← ENNReal.ofReal_natCast]
    congr 2
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), hQ]
    push_cast
    ring
  have e2 : 1 - (L : ℝ≥0∞) ^ d * ENNReal.ofReal r = ENNReal.ofReal (1 - Q * r) := by
    rw [ENNReal.ofReal_sub _ (mul_nonneg hQ0 hr0), ENNReal.ofReal_one, ENNReal.ofReal_mul hQ0, hQE]
  have e3 : (ENNReal.ofReal (1 - Q * r))⁻¹ = ENNReal.ofReal ((1 - Q * r)⁻¹) :=
    (ENNReal.ofReal_inv_of_pos (by linarith)).symm
  rw [tsum_projFibre_exactKernel hL1 hs hx hy, e1, e2, e3, ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_coe_nnreal (p := exactKernel (L : ℝ) s s(x, y)),
    ← ENNReal.ofReal_add hJ0 hC]
  congr 1
  rw [coe_truncatedKernel_eq_sub hL1 hs hx hy hxy, ancestor_closed_form hL1 hs,
    rpow_neg_mul_natCast hL1, ← hr, ← hQr]
  have h1r : 1 - r ≠ 0 := by linarith
  have h1Qr : 1 - Q * r ≠ 0 := by linarith
  have h1rQ : 1 - r * Q ≠ 0 := by linarith
  field_simp
  ring

/-- **The periodic kernel converges.** For distinct `x, y ∈ block n 0` the fibre sum
`∑_{π_n z = y} J_∞(x,z)` converges to `J_n(x,y) + q/(1-q) L^{-sn}`, `s = d + α`, `q = L^{-α}`. -/
theorem hasSum_projFibre_exactKernel (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) {n : ℕ}
    {x y : ℕ →₀ (Fin d → ZMod L)} (hx : x ∈ block n 0) (hy : y ∈ block n 0) (hxy : x ≠ y) :
    HasSum (fun z : projFibre n y => (exactKernel (L : ℝ) (d + α) s(x, z) : ℝ))
      ((truncatedKernel (L : ℝ) (d + α) n 0 s(x, y) : ℝ) +
        (L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-α)) * (L : ℝ) ^ (-((d + α) * n))) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hq1 := rpow_neg_lt_one hL1 hα
  have hV0 : 0 ≤ (truncatedKernel (L : ℝ) (d + α) n 0 s(x, y) : ℝ) +
      (L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-α)) * (L : ℝ) ^ (-((d + α) * n)) :=
    add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (div_nonneg (rpow_neg_nonneg hL1)
      (by linarith)) (Real.rpow_nonneg (by linarith) _))
  have h := ENNReal.summable.hasSum
    (f := fun z : projFibre n y => (exactKernel (L : ℝ) (d + α) s(x, z) : ℝ≥0∞))
  rw [tsum_projFibre_exactKernel_eq_ofReal hL hα hx hy hxy] at h
  have h' := NNReal.hasSum_coe.mpr (ENNReal.hasSum_coe.mp h)
  rwa [Real.coe_toNNReal _ hV0] at h'

/-- The value of the periodic kernel on a pair of distinct vertices of `block n 0`. -/
theorem coe_periodicKernel_mk (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) {n : ℕ}
    {x y : ℕ →₀ (Fin d → ZMod L)} (hx : x ∈ block n 0) (hy : y ∈ block n 0) (hxy : x ≠ y) :
    (periodicKernel (L : ℝ) (d + α) n s(x, y) : ℝ) =
      (truncatedKernel (L : ℝ) (d + α) n 0 s(x, y) : ℝ) +
        (L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-α)) * (L : ℝ) ^ (-((d + α) * n)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hq1 := rpow_neg_lt_one hL1 hα
  rw [periodicKernel_mk_of_mem hxy hx hy, tsum_projFibre_exactKernel_eq_ofReal hL hα hx hy hxy,
    ENNReal.ofReal, ENNReal.toNNReal_coe]
  exact Real.coe_toNNReal _ (add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (div_nonneg
    (rpow_neg_nonneg hL1) (by linarith)) (Real.rpow_nonneg (by linarith) _)))

/-- **Periodizing adds a constant.** `J_n^per = J_n + q/(1-q) L^{-sn}` on the pairs of
`block n 0`, as kernels on all pairs. -/
theorem periodicKernel_eq_add_completeKernel (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) (n : ℕ) :
    periodicKernel (L : ℝ) (d + α) n (A := Fin d → ZMod L) =
      truncatedKernel (L : ℝ) (d + α) n 0 +
        completeKernel n 0
          ((L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-α)) * (L : ℝ) ^ (-((d + α) * n))).toNNReal := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hq1 := rpow_neg_lt_one hL1 hα
  funext e
  refine Sym2.ind (fun x y => ?_) e
  rw [Pi.add_apply]
  by_cases h : x ≠ y ∧ x ∈ block n 0 ∧ y ∈ block n 0
  · rw [completeKernel_of_mem (mk_pair_mem_block_iff.mpr h)]
    ext
    rw [NNReal.coe_add, coe_periodicKernel_mk hL hα h.2.1 h.2.2 h.1, Real.coe_toNNReal _
      (mul_nonneg (div_nonneg (rpow_neg_nonneg hL1) (by linarith))
        (Real.rpow_nonneg (by linarith) _))]
  · rw [periodicKernel_mk_of_not_mem h,
      truncatedKernel_of_not_mem (mt mk_pair_mem_block_iff.mp h),
      completeKernel_of_not_mem (mt mk_pair_mem_block_iff.mp h), add_zero]

/-- **The last coalescent stage runs longer.** The periodic kernel is the kernel of the layers
below level `n` (the truncated kernel minus its level-`n` layer `L^{-sn}`) plus a complete-graph
layer of weight `L^{-sn}/(1 - q)`. -/
theorem periodicKernel_eq_sub_add_completeKernel (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) (n : ℕ) :
    periodicKernel (L : ℝ) (d + α) n (A := Fin d → ZMod L) =
      (truncatedKernel (L : ℝ) (d + α) n 0 -
          completeKernel n 0 ((L : ℝ) ^ (-((d + α) * n))).toNNReal) +
        completeKernel n 0 ((L : ℝ) ^ (-((d + α) * n)) / (1 - (L : ℝ) ^ (-α))).toNNReal := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hq1 := rpow_neg_lt_one hL1 hα
  have hq0 : 0 ≤ (L : ℝ) ^ (-α) := rpow_neg_nonneg hL1
  have ha0 : 0 ≤ (L : ℝ) ^ (-((d + α) * n)) := Real.rpow_nonneg (by linarith) _
  rw [periodicKernel_eq_add_completeKernel hL hα n]
  funext e
  refine Sym2.ind (fun x y => ?_) e
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases h : x ≠ y ∧ x ∈ block n 0 ∧ y ∈ block n 0
  · have hm := mk_pair_mem_block_iff.mpr h
    rw [completeKernel_of_mem hm, completeKernel_of_mem hm, completeKernel_of_mem hm]
    have hle : ((L : ℝ) ^ (-((d + α) * n))).toNNReal ≤
        truncatedKernel (L : ℝ) (d + α) n 0 s(x, y) := by
      rw [truncatedKernel_of_mem hm]
      refine Real.toNNReal_le_toNNReal (Finset.single_le_sum (f := fun m : ℕ =>
        (L : ℝ) ^ (-((d + α) * m))) (fun m _ => Real.rpow_nonneg (by linarith) _) ?_)
      exact Finset.mem_Icc.mpr ⟨pairLevel_le_of_mem_block hm.2, le_rfl⟩
    ext
    rw [NNReal.coe_add, NNReal.coe_add, NNReal.coe_sub hle, Real.coe_toNNReal _ ha0,
      Real.coe_toNNReal _ (div_nonneg ha0 (by linarith)),
      Real.coe_toNNReal _ (mul_nonneg (div_nonneg hq0 (by linarith)) ha0)]
    have h1q : 1 - (L : ℝ) ^ (-α) ≠ 0 := by linarith
    field_simp
    ring
  · have hm := mt mk_pair_mem_block_iff.mp h
    rw [truncatedKernel_of_not_mem hm, completeKernel_of_not_mem hm, completeKernel_of_not_mem hm,
      completeKernel_of_not_mem hm]
    simp

/-- **Periodic percolation is the truncated block law plus an independent complete layer.** -/
theorem law_periodicKernel_eq_map_union (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) (n : ℕ) (β : ℝ≥0) :
    law (intensityProfile (periodicKernel (L : ℝ) (d + α) n (A := Fin d → ZMod L)) β) =
      ((law (intensityProfile (truncatedKernel (L : ℝ) (d + α) n 0) β)).prod
        (law (intensityProfile (completeKernel n 0
          ((L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-α)) * (L : ℝ) ^ (-((d + α) * n))).toNNReal) β))).map
        (fun ω => ω.1 ∪ ω.2) := by
  rw [periodicKernel_eq_add_completeKernel hL hα n]
  exact LongRange.law_intensityProfile_add_kernel _ _ β

/-- **Periodic percolation runs the last layer to time `β L^{-sn}/(1 - q)`.** Its law is that of
the union of the layers below level `n` with an independent complete-graph layer on `block n 0`
of intensity `β L^{-sn}/(1 - q)`. -/
theorem law_periodicKernel_eq_map_union_lastLayer (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) (n : ℕ)
    (β : ℝ≥0) :
    law (intensityProfile (periodicKernel (L : ℝ) (d + α) n (A := Fin d → ZMod L)) β) =
      ((law (intensityProfile (truncatedKernel (L : ℝ) (d + α) n 0 -
          completeKernel n 0 ((L : ℝ) ^ (-((d + α) * n))).toNNReal) β)).prod
        (law (intensityProfile (completeKernel n 0
          ((L : ℝ) ^ (-((d + α) * n)) / (1 - (L : ℝ) ^ (-α))).toNNReal) β))).map
        (fun ω => ω.1 ∪ ω.2) := by
  rw [periodicKernel_eq_sub_add_completeKernel hL hα n]
  exact LongRange.law_intensityProfile_add_kernel _ _ β

end Lattice

end PercLib.Models.HierarchicalLayers
