/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions on this library's bond-percolation interface and hierarchical geometry, and
pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied.
Mathematical reference: T. Hutchcroft, *The critical two-point function for long-range
percolation on the hierarchical lattice*, arXiv:2103.17013v1 (off-critical estimates from
finite-ball boundary scales).
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.Intensity.Defs

/-!
# Boundary thresholds and length scales of hierarchical balls (definitions)

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ` and `Λ_n = {h ≤ n}`, as the
finset `(finite_level_ball n).toFinset`. For a kernel `J` and the profile `q_β = 1 - e^{-βJ}`
let `Φ_β(Λ_n) = boundaryFlux q_β Λ_n 0`.

## Main definitions

* `ballExitRate J n β`: the exit rate `r_n(β) = ∑_{h y > n} (1 - e^{-β J(0, y)})`.
* `boundaryThreshold J n`: `β_n`, the least `β` with `Φ_β(Λ_n) ≥ 1/2`.
* `maxBoundaryThreshold J n`: `b_n = max_{k ≤ n} β_k`.
* `boundaryScaleIndex J β`: `m(β) = min {n : β ≤ b_n} ∈ ℕ∞` (`⊤` if there is none).
* `boundaryLength J β`: `ξ(β) = L^{m(β)} ∈ ℝ≥0∞` (`⊤` if `m(β) = ⊤`).

## Main results

* `boundaryThreshold_le_maxBoundaryThreshold`, `monotone_maxBoundaryThreshold`,
  `exists_maxBoundaryThreshold_eq`: `b_n` is the running maximum, and it is attained.
* `boundaryScaleIndex_le_of_le`, `boundaryScaleIndex_eq_top_iff`,
  `le_maxBoundaryThreshold_of_boundaryScaleIndex_eq`: `m(β)` is the least index.
* `boundaryLength_eq_pow_of_boundaryScaleIndex_eq`,
  `boundaryLength_eq_top_of_boundaryScaleIndex_eq_top`: `ξ = L^m`.
* `coe_toFinset_level_ball`, `mem_toFinset_level_ball_finset`: the finset ball.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-! ### Definitions -/

/-- The exit rate of the ball `Λ_n` at intensity `β`:
`r_n(β) = ∑_{h y > n} (1 - e^{-β J(0, y)})`. -/
def ballExitRate (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (n : ℕ) (β : ℝ≥0) : ℝ≥0∞ :=
  ∑' y : ℕ →₀ (Fin d → ZMod L), if n < y.support.sup Nat.succ then
    (unitInterval.toNNReal (intensityProfile J β s(0, y)) : ℝ≥0∞) else 0

/-- The boundary threshold `β_n` of the ball `Λ_n`: the least intensity at which the boundary
flux `Φ_β(Λ_n)` reaches `1/2` (`0` if it never does). Under the hypotheses of
`boundaryFlux_boundaryThreshold` it is the unique solution of `Φ_β(Λ_n) = 1/2`. -/
def boundaryThreshold (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  sInf {β : ℝ≥0 | 2⁻¹ ≤ boundaryFlux (intensityProfile J β)
    (finite_level_ball (A := Fin d → ZMod L) n).toFinset 0}

/-- The running maximum `b_n = max_{k ≤ n} β_k` of the boundary thresholds. -/
def maxBoundaryThreshold (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (Finset.range (n + 1)).sup (boundaryThreshold J)

open Classical in
/-- The boundary scale index `m(β) = min {n : β ≤ b_n}`, and `⊤` if there is no such `n`. -/
def boundaryScaleIndex (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (β : ℝ≥0) : ℕ∞ :=
  if h : ∃ n, β ≤ maxBoundaryThreshold J n then (Nat.find h : ℕ∞) else ⊤

open Classical in
/-- The boundary length scale `ξ(β) = L^{m(β)}`, and `⊤` if `m(β) = ⊤`. -/
def boundaryLength (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (β : ℝ≥0) : ℝ≥0∞ :=
  if h : ∃ n, β ≤ maxBoundaryThreshold J n then (L : ℝ≥0∞) ^ Nat.find h else ⊤

/-! ### Basic API -/

section API

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)

theorem boundaryThreshold_le_maxBoundaryThreshold {k n : ℕ} (h : k ≤ n) :
    boundaryThreshold J k ≤ maxBoundaryThreshold J n :=
  Finset.le_sup (f := boundaryThreshold J) (Finset.mem_range.2 (Nat.lt_succ_of_le h))

theorem monotone_maxBoundaryThreshold : Monotone (maxBoundaryThreshold J) := fun _ _ h =>
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ h))

/-- The running maximum is attained. -/
theorem exists_maxBoundaryThreshold_eq (n : ℕ) :
    ∃ k ≤ n, maxBoundaryThreshold J n = boundaryThreshold J k := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup (Finset.range (n + 1))
    Finset.nonempty_range_add_one (boundaryThreshold J)
  exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), he⟩

theorem boundaryScaleIndex_le_of_le {β : ℝ≥0} {n : ℕ} (h : β ≤ maxBoundaryThreshold J n) :
    boundaryScaleIndex J β ≤ n := by
  have hex : ∃ n, β ≤ maxBoundaryThreshold J n := ⟨n, h⟩
  rw [boundaryScaleIndex, dite_eq_left hex]
  exact_mod_cast Nat.find_min' hex h

theorem boundaryScaleIndex_eq_top_iff {β : ℝ≥0} :
    boundaryScaleIndex J β = ⊤ ↔ ∀ n, maxBoundaryThreshold J n < β := by
  unfold boundaryScaleIndex
  split_ifs with h
  · simp only [ENat.natCast_ne_top, false_iff, not_forall, not_lt]
    exact h
  · simp only [true_iff]
    push Not at h
    exact h

theorem le_maxBoundaryThreshold_of_boundaryScaleIndex_eq {β : ℝ≥0} {k : ℕ}
    (h : boundaryScaleIndex J β = k) : β ≤ maxBoundaryThreshold J k := by
  unfold boundaryScaleIndex at h
  split_ifs at h with hex
  · obtain rfl := ENat.natCast_inj.1 h
    exact Nat.find_spec hex
  · exact absurd h (ENat.top_ne_natCast k)

theorem boundaryLength_eq_pow_of_boundaryScaleIndex_eq {β : ℝ≥0} {k : ℕ}
    (h : boundaryScaleIndex J β = k) : boundaryLength J β = (L : ℝ≥0∞) ^ k := by
  unfold boundaryScaleIndex at h
  unfold boundaryLength
  split_ifs at h ⊢ with hex
  · rw [ENat.natCast_inj.1 h]
  · exact absurd h (ENat.top_ne_natCast k)

theorem boundaryLength_eq_top_of_boundaryScaleIndex_eq_top {β : ℝ≥0}
    (h : boundaryScaleIndex J β = ⊤) : boundaryLength J β = ⊤ := by
  unfold boundaryScaleIndex at h
  unfold boundaryLength
  split_ifs at h ⊢ with hex
  · exact absurd h (ENat.natCast_ne_top _)
  · rfl

end API

section Ball

theorem coe_toFinset_level_ball (n : ℕ) :
    ((finite_level_ball (A := Fin d → ZMod L) n).toFinset : Set (ℕ →₀ (Fin d → ZMod L))) =
      {z | z.support.sup Nat.succ ≤ n} :=
  Set.Finite.coe_toFinset _

theorem mem_toFinset_level_ball_finset {n : ℕ} {z : ℕ →₀ (Fin d → ZMod L)} :
    z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset ↔ z.support.sup Nat.succ ≤ n := by
  rw [← Finset.mem_coe, coe_toFinset_level_ball]
  rfl

end Ball

end PercLib.Models
