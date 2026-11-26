/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original auxiliary envelopes for the canonical lace diagrams;
no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Diagram envelopes retaining the ordered bond tuple

## Main results

The marked tuple diagram retains every earlier weighted bond while bounding
the last deleted-cluster marker. Its recursion uses the two actual interior
geometries, including the excluded zero-length joining arm. The coefficient
tuple diagram appends the outgoing bond weight and terminal four-arm factor.

These are auxiliary nonnegative envelopes, not additional lace coefficients.
The initial diagonal is handled by the existing initial diagram, and every
outgoing deleted connection is retained. No finiteness is built into the
definitions.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

open scoped Classical in
/-- The marked diagram before summing the ordered tuple of earlier bonds.
The specified outgoing pair `c` is deleted in the last marker but is not yet
weighted; its weight belongs to the next step. -/
def markedTupleDiagram (q : Sym2 V → unitInterval) (x : V) :
    (n : ℕ) → (Fin n → V × V) → (V × V) → V → ℝ≥0∞
  | 0, _, c, a => ∑' r, diagramInitial q x (r, c.1) *
      law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn r a}
  | n + 1, b, c, a =>
      let d := b (Fin.last n)
      ∑' z, ∑' t, ∑' w,
        markedTupleDiagram q x n (Fin.init b) d z *
          offDiagonal (fun u v : V =>
            (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) d.1 d.2 *
        ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
          if w = t then 0 else
            (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a}

/-- The positive-order diagram envelope for one complete ordered bond tuple.
The last bond is weighted here, followed by its actual terminal factor. -/
def coefficientTupleDiagram (q : Sym2 V → unitInterval) (x y : V) {n : ℕ}
    (b : Fin (n + 1) → V × V) : ℝ≥0∞ :=
  let c := b (Fin.last n)
  ∑' z, ∑' t, markedTupleDiagram q x n (Fin.init b) c z *
    offDiagonal (fun u v : V =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) c.1 c.2 *
    tau q c.2 t * tau q t z * tau q t y * tau q z y

@[simp] theorem markedTupleDiagram_zero (q : Sym2 V → unitInterval)
    (x : V) (b : Fin 0 → V × V) (c : V × V) (a : V) :
    markedTupleDiagram q x 0 b c a = ∑' r, diagramInitial q x (r, c.1) *
      law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn r a} := rfl

open scoped Classical in
@[simp] theorem markedTupleDiagram_snoc (q : Sym2 V → unitInterval)
    (x : V) {n : ℕ} (b : Fin n → V × V) (d c : V × V) (a : V) :
    markedTupleDiagram q x (n + 1) (Fin.snoc b d) c a =
      ∑' z, ∑' t, ∑' w, markedTupleDiagram q x n b d z *
        offDiagonal (fun u v : V =>
          (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) d.1 d.2 *
        ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
          if w = t then 0 else
            (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} := by
  simp only [markedTupleDiagram, Fin.init_snoc, Fin.snoc_last]

@[simp] theorem coefficientTupleDiagram_snoc (q : Sym2 V → unitInterval)
    (x y : V) {n : ℕ} (b : Fin n → V × V) (c : V × V) :
    coefficientTupleDiagram q x y (Fin.snoc b c) =
      ∑' z, ∑' t, markedTupleDiagram q x n b c z *
        offDiagonal (fun u v : V =>
          (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) c.1 c.2 *
        tau q c.2 t * tau q t z * tau q t y * tau q z y := by
  simp only [coefficientTupleDiagram, Fin.init_snoc, Fin.snoc_last]

@[simp] theorem markedTupleDiagram_succ_zero_profile (x : V) {n : ℕ}
    (b : Fin (n + 1) → V × V) (c : V × V) (a : V) :
    markedTupleDiagram (fun _ : Sym2 V => 0) x (n + 1) b c a = 0 := by
  classical
  simp [markedTupleDiagram, offDiagonal]

@[simp] theorem coefficientTupleDiagram_zero_profile (x y : V) {n : ℕ}
    (b : Fin (n + 1) → V × V) :
    coefficientTupleDiagram (fun _ : Sym2 V => 0) x y b = 0 := by
  classical
  simp [coefficientTupleDiagram, offDiagonal]

end PercLib.Percolation.Bond.Lace
