/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original definition of the primitive finite lace-diagram weight;
no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Primitive finite-chain weights

## Main definitions

`diagramPrimitiveChainWeight` is the product of the actual initial factor,
deleted connectors, interior factors and terminal triangle arms along a finite
chain. It is the explicit summand already used in the lace diagram expansion.

## Main results

The zero-order and `Fin.snoc` formulas expose the endpoints and the final layer.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The actual primitive chain has `n+1` deleted connectors and `n` interior
factors, with the initial row and the terminal triangle arms. -/
def diagramPrimitiveChainWeight (q : Sym2 V → unitInterval) (n : ℕ) (x y : V)
    (b s : Fin (n + 1) → V × V) : ℝ≥0∞ :=
  diagramInitial q x (b 0) *
    (∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc) *
      diagramInterior q (s i.castSucc) (b i.succ)) *
    (diagramConnector q (b (Fin.last n)) (s (Fin.last n)) *
      tau q (s (Fin.last n)).1 (s (Fin.last n)).2 *
        tau q (s (Fin.last n)).1 y * tau q (s (Fin.last n)).2 y)

@[simp] theorem diagramPrimitiveChainWeight_zero (q : Sym2 V → unitInterval) (x y : V)
    (b s : Fin 1 → V × V) :
    diagramPrimitiveChainWeight q 0 x y b s =
      diagramInitial q x (b 0) *
        (diagramConnector q (b 0) (s 0) * tau q (s 0).1 (s 0).2 *
          tau q (s 0).1 y * tau q (s 0).2 y) := by
  simp [diagramPrimitiveChainWeight]

/-- Appending a layer exposes its incoming interior factor and its terminal
connector, without cancelling any possibly zero triangle arm. -/
theorem diagramPrimitiveChainWeight_snoc (q : Sym2 V → unitInterval) (n : ℕ) (x y : V)
    (b s : Fin (n + 1) → V × V) (p t : V × V) :
    diagramPrimitiveChainWeight q (n + 1) x y (Fin.snoc b p) (Fin.snoc s t) =
      diagramInitial q x (b 0) *
        ((∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc) *
          diagramInterior q (s i.castSucc) (b i.succ)) *
            (diagramConnector q (b (Fin.last n)) (s (Fin.last n)) *
              diagramInterior q (s (Fin.last n)) p)) *
        (diagramConnector q p t * tau q t.1 t.2 * tau q t.1 y * tau q t.2 y) := by
  simp only [diagramPrimitiveChainWeight, Fin.prod_univ_castSucc,
    ← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_apply_zero, Fin.succ_last,
    Fin.snoc_last]

theorem diagramPrimitiveChainWeight_eq_zero_of_initial
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) (b s : Fin (n + 1) → V × V)
    (h : diagramInitial q x (b 0) = 0) :
    diagramPrimitiveChainWeight q n x y b s = 0 := by
  simp [diagramPrimitiveChainWeight, h]

end PercLib.Percolation.Bond.Lace
