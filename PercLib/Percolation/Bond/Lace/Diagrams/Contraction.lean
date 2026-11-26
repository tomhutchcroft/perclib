/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs of the nonnegative sum contractions for the refined lace
diagrams; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Basic

/-!
# Contraction of marked lace diagrams

## Main results

Tonelli rearrangements identify the six-arm successor and the terminal
three-arm factor with the pair-state transfer and terminal diagrams. The
identities hold in the extended nonnegative reals without summability or
countability assumptions.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

open scoped Classical in
/-- Contracting the two interior geometries gives precisely one pair-state
transfer, while retaining the outgoing deleted connection. -/
theorem marked_successor_contraction
    (q : Sym2 V → unitInterval) (f : V × V → ℝ≥0∞) (u a : V) (e : Sym2 V) :
    (∑' d : V × V, ∑' z, ∑' t, ∑' w,
      (∑' r, f (r, d.1) *
        law q {ω : Config V | ω \ {s(d.1, d.2)} ∈ conn r z}) *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
        d.1 d.2 *
      ((tau q t w * tau q w u) * (tau q t z * tau q z u) * tau q d.2 t +
        if w = t then 0 else
          (tau q d.2 w * tau q w t) * (tau q t z * tau q z u) * tau q t u) *
      law q {ω : Config V | ω \ {e} ∈ conn w a}) =
      ∑' w, (∑' p : V × V, f p * diagramTransfer q p (w, u)) *
        law q {ω : Config V | ω \ {e} ∈ conn w a} := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  let D : V → V → V → V → ℝ≥0∞ := fun b v r z =>
    law q {ω : Config V | ω \ {s(b, v)} ∈ conn r z}
  let H : V → V → V → V → ℝ≥0∞ := fun v z t w =>
    (tau q t w * tau q w u) * (tau q t z * tau q z u) * tau q v t +
      if w = t then 0 else
        (tau q v w * tau q w t) * (tau q t z * tau q z u) * tau q t u
  let K : V → ℝ≥0∞ := fun w => law q {ω : Config V | ω \ {e} ∈ conn w a}
  have hinterior (v z w : V) :
      (∑' t, tau q v t * diagramInterior q (z, t) (w, u)) = ∑' t, H v z t w := by
    simp only [diagramInterior, H, mul_add, ENNReal.tsum_add]
    congr 1
    · apply tsum_congr
      intro t
      rw [tau_comm q z t]
      ac_rfl
    · simp_rw [mul_ite, mul_zero]
      rw [tsum_ite_eq]
      simp_rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro t
      by_cases ht : t = w
      · simp [ht]
      · simp only [ite_eq_right ht, ite_eq_right (Ne.symm ht)]
        ac_rfl
  have htransfer (r b w : V) : diagramTransfer q (r, b) (w, u) =
      ∑' v, ∑' z, ∑' t, J b v * D b v r z * H v z t w := by
    unfold diagramTransfer diagramConnector
    rw [ENNReal.tsum_prod']
    change (∑' z, ∑' t, (∑' v, J b v * D b v r z * tau q v t) *
      diagramInterior q (z, t) (w, u)) = _
    calc
      _ = ∑' z, ∑' v, ∑' t,
          J b v * D b v r z * (tau q v t * diagramInterior q (z, t) (w, u)) := by
        simp_rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro z
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro v
        apply tsum_congr
        intro t
        ac_rfl
      _ = ∑' v, ∑' z, J b v * D b v r z *
          ∑' t, tau q v t * diagramInterior q (z, t) (w, u) := by
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro v
        apply tsum_congr
        intro z
        exact ENNReal.tsum_mul_left
      _ = _ := by simp_rw [hinterior, ← ENNReal.tsum_mul_left]
  change (∑' d : V × V, ∑' z, ∑' t, ∑' w,
    (∑' r, f (r, d.1) * D d.1 d.2 r z) * J d.1 d.2 * H d.2 z t w * K w) = _
  rw [ENNReal.tsum_prod']
  simp_rw [← ENNReal.tsum_mul_right]
  calc
    _ = ∑' w, ∑' r, ∑' b, ∑' v, ∑' z, ∑' t,
        f (r, b) * D b v r z * J b v * H v z t w * K w := by
      simpa only [ENNReal.tsum_prod'] using
        (ENNReal.tsum_comm (f := fun (p : V × V × V × V) (s : V × V) =>
          f (s.2, p.1) * D p.1 p.2.1 s.2 p.2.2.1 * J p.1 p.2.1 *
            H p.2.1 p.2.2.1 p.2.2.2 s.1 * K s.1))
    _ = _ := by
      apply tsum_congr
      intro w
      simp_rw [ENNReal.tsum_prod', htransfer,
        ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro r
      apply tsum_congr
      intro b
      apply tsum_congr
      intro v
      apply tsum_congr
      intro z
      apply tsum_congr
      intro t
      dsimp only [K]
      ac_rfl

/-- Contracting a marked row with the final three arms gives the terminal
diagram, retaining the connection with the outgoing bond deleted. -/
theorem marked_terminal_contraction
    (q : Sym2 V → unitInterval) (f : V × V → ℝ≥0∞) (y : V) :
    (∑' c : V × V, ∑' z, ∑' t,
      (∑' w, f (w, c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w z}) *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
        c.1 c.2 * tau q c.2 t * tau q t z * tau q t y * tau q z y) =
      ∑' p : V × V, f p * diagramTerminal q p y := by
  classical
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  let D : V → V → V → V → ℝ≥0∞ := fun b v w z =>
    law q {ω : Config V | ω \ {s(b, v)} ∈ conn w z}
  have hterminal (w b : V) : diagramTerminal q (w, b) y =
      ∑' v, ∑' z, ∑' t,
        J b v * D b v w z * tau q v t * tau q t z * tau q t y * tau q z y := by
    unfold diagramTerminal diagramConnector
    rw [ENNReal.tsum_prod']
    change (∑' z, ∑' t, (∑' v, J b v * D b v w z * tau q v t) *
      tau q z t * tau q z y * tau q t y) = _
    simp_rw [← ENNReal.tsum_mul_right]
    calc
      _ = ∑' v, ∑' z, ∑' t,
          J b v * D b v w z * tau q v t * tau q z t * tau q z y * tau q t y := by
        simpa only [ENNReal.tsum_prod'] using
          (ENNReal.tsum_comm (f := fun (p : V × V) v =>
            J b v * D b v w p.1 * tau q v p.2 * tau q p.1 p.2 *
              tau q p.1 y * tau q p.2 y))
      _ = _ := by
        apply tsum_congr
        intro v
        apply tsum_congr
        intro z
        apply tsum_congr
        intro t
        rw [tau_comm q z t]
        ac_rfl
  change (∑' c : V × V, ∑' z, ∑' t,
    (∑' w, f (w, c.1) * D c.1 c.2 w z) * J c.1 c.2 *
      tau q c.2 t * tau q t z * tau q t y * tau q z y) = _
  rw [ENNReal.tsum_prod']
  simp_rw [← ENNReal.tsum_mul_right]
  calc
    _ = ∑' w, ∑' b, ∑' v, ∑' z, ∑' t,
        f (w, b) * D b v w z * J b v * tau q v t * tau q t z * tau q t y *
          tau q z y := by
      simpa only [ENNReal.tsum_prod'] using
        (ENNReal.tsum_comm (f := fun (p : V × V × V × V) w =>
          f (w, p.1) * D p.1 p.2.1 w p.2.2.1 * J p.1 p.2.1 *
            tau q p.2.1 p.2.2.2 * tau q p.2.2.2 p.2.2.1 *
            tau q p.2.2.2 y * tau q p.2.2.1 y))
    _ = _ := by
      simp_rw [ENNReal.tsum_prod', hterminal, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro w
      apply tsum_congr
      intro b
      apply tsum_congr
      intro v
      apply tsum_congr
      intro z
      apply tsum_congr
      intro t
      ac_rfl

end PercLib.Percolation.Bond.Lace
