/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: finite susceptibility below the threshold for summable
translation-invariant kernels on countable additive groups and on `ℤ^d`, from the transitive
sharpness theorem of `Percolation/Bond/Sharpness.lean`. No upstream code is copied, no definition is
added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Models.Hierarchical
public import PercLib.Models.LongRange.PowerLaw

/-! # Finite susceptibility below the threshold on `ℤ^d`

Let `G` be a countable additive group, `k : G → ℝ≥0` with `∑' z, k z < ⊤`, and `J` a pair
intensity with `J s(x,y) = k (y - x)` (such a `J` exists exactly when `k` is even,
`exists_sym2_kernel`).

* `transitive_of_translationInvariant`, `summable_rows_of_translationInvariant` (item 1):
  translations are automorphisms of `J`, and the rows of `J` are summable.
* `chi_lt_top_of_lt_globalCriticalIntensity_of_translationInvariant` and
  `rootCriticalIntensity_eq_globalCriticalIntensity_of_translationInvariant` (item 2).
* `chi_lt_top_of_lt_globalCriticalIntensity_int` (item 3):
  the same on `ℤ^d = Fin d → ℤ`.
* `chi_lt_top_of_lt_globalCriticalIntensity_powerLaw` and
  `chi_lt_top_of_lt_globalCriticalIntensity_hierarchical` (item 4): the power law
  `‖z‖^(-(d+α))`, `α > 0`, on `ℤ^d` and the radial kernel on the hierarchical lattice.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

section Group

variable {G : Type*} [AddGroup G]

/-- **Item 1, transitivity.** Translations are automorphisms of a translation-invariant
pair intensity: `σ = Equiv.addRight (y - x)` maps `x` to `y`. -/
theorem transitive_of_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y - x)) :
    ∀ x y : G, ∃ σ : G ≃ G, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := by
  intro x y
  refine ⟨Equiv.addRight (-x + y), by simp, fun e => ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, hJ, hJ]
    simp only [Equiv.coe_addRight, add_sub_add_right_eq_sub]

/-- **Item 1, summable rows.** A kernel of finite total mass gives summable real rows. -/
theorem summable_rows_of_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y - x)) (hk : ∑' z, (k z : ℝ≥0∞) < ⊤) (u : G) :
    Summable fun v => (J s(u, v) : ℝ) := by
  have hs : Summable k := ENNReal.tsum_coe_ne_top_iff_summable.1 hk.ne
  simp_rw [hJ]
  exact NNReal.summable_coe.2 ((Equiv.subRight u).summable_iff.2 hs)

/-- **Item 2, threshold.** Every root threshold of a summable translation-invariant pair
intensity equals the global threshold. -/
theorem rootCriticalIntensity_eq_globalCriticalIntensity_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x)) (x : G) :
    rootCriticalIntensity J x = globalCriticalIntensity J :=
  rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive J
    (transitive_of_translationInvariant J k hJ) x

/-- **Item 2, finite susceptibility on countable groups.** For a summable translation-invariant pair
intensity, the susceptibility is finite at every vertex at every intensity below the threshold. -/
theorem chi_lt_top_of_lt_globalCriticalIntensity_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x))
    (hk : ∑' z, (k z : ℝ≥0∞) < ⊤) {β : ℝ≥0} (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J)
    (x : G) : chi (intensityProfile J β) x < ⊤ := by
  rw [← rootCriticalIntensity_eq_globalCriticalIntensity_of_translationInvariant J k hJ x] at hβ
  exact chi_lt_top_of_lt_rootCriticalIntensity J (transitive_of_translationInvariant J k hJ)
    (summable_rows_of_translationInvariant J k hJ hk) hβ

end Group

/-- **Finite susceptibility on `ℤ^d` (item 3).** On `ℤ^d`, for a summable translation-invariant pair
intensity `J s(x,y) = k (y - x)`, the susceptibility is finite at every vertex at every
intensity below the threshold, and the root and global thresholds agree. -/
theorem chi_lt_top_of_lt_globalCriticalIntensity_int {d : ℕ}
    (J : Sym2 (Fin d → ℤ) → ℝ≥0) (k : (Fin d → ℤ) → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x))
    (hk : ∑' z, (k z : ℝ≥0∞) < ⊤) :
    (∀ β : ℝ≥0, (β : ℝ≥0∞) < globalCriticalIntensity J →
      ∀ x, chi (intensityProfile J β) x < ⊤) ∧
    ∀ x, rootCriticalIntensity J x = globalCriticalIntensity J :=
  ⟨fun _ hβ x => chi_lt_top_of_lt_globalCriticalIntensity_of_translationInvariant J k hJ hk hβ x,
    rootCriticalIntensity_eq_globalCriticalIntensity_of_translationInvariant J k hJ⟩

/-- **Item 4(a), the power law on `ℤ^d`.** For `d ≥ 1`, `α > 0` and
`J s(x,y) = ‖y - x‖^(-(d+α))` off the diagonal, the susceptibility is finite below the
threshold, and the threshold is at least the inverse of the total mass of the kernel. -/
theorem chi_lt_top_of_lt_globalCriticalIntensity_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal
      (if y - x = 0 then 0 else ‖y - x‖ ^ (-((d : ℝ) + α)))) :
    (∀ β : ℝ≥0, (β : ℝ≥0∞) < globalCriticalIntensity J →
      ∀ x, chi (intensityProfile J β) x < ⊤) ∧
    (∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))))⁻¹ ≤
      globalCriticalIntensity J := by
  set k : (Fin d → ℤ) → ℝ≥0 := fun z =>
    Real.toNNReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α)))
  have hk : ∑' z, (k z : ℝ≥0∞) < ⊤ := (LongRange.tsum_ofReal_powerLaw_lt_top_iff hd α).2 hα
  refine ⟨(chi_lt_top_of_lt_globalCriticalIntensity_int J k hJ hk).1, ?_⟩
  have h := inv_le_globalCriticalIntensity_of_translationInvariant J k hJ
    (∑' z, (k z : ℝ≥0∞)).toNNReal (ENNReal.coe_toNNReal hk.ne).ge
  rwa [ENNReal.coe_toNNReal hk.ne] at h

/-- **Item 4(b), the hierarchical lattice.** For the radial kernel `C r^(level z)` with
`2 L^d r ≤ 1`, the susceptibility is finite at every vertex below the threshold. -/
theorem chi_lt_top_of_lt_globalCriticalIntensity_hierarchical {d L : ℕ} [NeZero L]
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) {β : ℝ≥0} (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J)
    (x : ℕ →₀ (Fin d → ZMod L)) : chi (intensityProfile J β) x < ⊤ :=
  chi_lt_top_of_lt_globalCriticalIntensity_of_translationInvariant J
    (fun z => C * r ^ (z.support.sup Nat.succ)) hJ
    ((tsum_geometricRadial_le C r hr).trans_lt ENNReal.coe_lt_top) hβ x

end PercLib.Models

/-! ### Non-vacuity -/
section Witnesses

open PercLib.Models

/-- `d = 1`: the nearest-neighbour kernel (unit mass at `±1`) satisfies every hypothesis of
the `ℤ^d` theorem; its threshold is at least `1/2` and the susceptibility is finite below
it. -/
example : ∃ J : Sym2 (Fin 1 → ℤ) → ℝ≥0, J ≠ 0 ∧ ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
    ∀ β : ℝ≥0, (β : ℝ≥0∞) < globalCriticalIntensity J →
      ∀ x, chi (intensityProfile J β) x < ⊤ := by
  set a : Fin 1 → ℤ := Pi.single 0 1
  set k : (Fin 1 → ℤ) → ℝ≥0 := fun z => (if z = a then 1 else 0) + (if z = -a then 1 else 0)
  obtain ⟨J, hJ⟩ := exists_sym2_kernel k (twoPointKernel_neg a)
  have hk2 : ∑' z, (k z : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞) :=
    (tsum_twoPointKernel a).le.trans (by simp)
  have hk : ∑' z, (k z : ℝ≥0∞) < ⊤ := hk2.trans_lt ENNReal.coe_lt_top
  refine ⟨J, ?_, inv_le_globalCriticalIntensity_of_translationInvariant J k hJ 2 hk2,
    (chi_lt_top_of_lt_globalCriticalIntensity_int J k hJ hk).1⟩
  intro h
  have h0 := congrFun h s(0, a)
  rw [hJ] at h0
  simp [k] at h0

/-- `d = 1`, `α = 1`: the kernel `|z|^(-2)` on `ℤ` satisfies every hypothesis of the power-law
theorem. -/
example : ∃ J : Sym2 (Fin 1 → ℤ) → ℝ≥0, J ≠ 0 ∧
    (∀ β : ℝ≥0, (β : ℝ≥0∞) < globalCriticalIntensity J →
      ∀ x, chi (intensityProfile J β) x < ⊤) ∧
    (∑' z : Fin 1 → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1))))⁻¹ ≤
      globalCriticalIntensity J := by
  obtain ⟨J, hJ⟩ := exists_sym2_kernel (fun z : Fin 1 → ℤ =>
    Real.toNNReal (if z = 0 then 0 else ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1))))
    fun z => by simp only [LongRange.powerLaw_neg]
  refine ⟨J, ?_, chi_lt_top_of_lt_globalCriticalIntensity_powerLaw le_rfl one_pos J hJ⟩
  intro h
  have h0 := congrFun h s(0, Pi.single 0 1)
  rw [hJ] at h0
  have hne : (Pi.single 0 1 : Fin 1 → ℤ) ≠ 0 := by simp
  simp only [sub_zero, hne, ↓reduceIte, Pi.zero_apply, Real.toNNReal_eq_zero] at h0
  exact absurd h0 (not_le.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 (by simp)) _))

/-- `d = 1`, `L = 2`: the radial kernel `4^(-level)` on the hierarchical lattice satisfies
every hypothesis of the hierarchical theorem, at every intensity below the threshold. -/
example (β : ℝ≥0) (x : ℕ →₀ (Fin 1 → ZMod 2)) : ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
    ((β : ℝ≥0∞) < globalCriticalIntensity J → chi (intensityProfile J β) x < ⊤) := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  exact ⟨J, fun hβ => chi_lt_top_of_lt_globalCriticalIntensity_hierarchical J 1 (1 / 4) hJ
    (by norm_num) hβ x⟩

end Witnesses
