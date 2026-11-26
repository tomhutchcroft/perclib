/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original finite-chain reindexing proofs; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Coefficients
public import PercLib.Percolation.Bond.Lace.Diagrams.Weighted
public import PercLib.Probability.SizeBias.ClusterMeasure
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact finite chains for the pair-state diagrams

## Main results

The existing recursive rows and coefficient diagrams are unrolled as sums over
finite tuples of pair states. Their factors are the actual initial, deleted
transfer and terminal diagrams. The identities hold for extended nonnegative
sums without countability or finiteness assumptions.
Exposing the connector states gives an alternating route with `2n+3`
primitive displacements for the coefficient of order `n+1`.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- An iterated diagram row is the sum of all length-`n` transfer chains
ending at the specified pair state. The case `n=0` is the initial row. -/
theorem diagramIterate_eq_tsum_chain (q : Sym2 V → unitInterval)
    (x : V) (n : ℕ) (p : V × V) :
    diagramIterate q x n p = ∑' b : Fin n → V × V,
      diagramInitial q x ((Fin.snoc b p : Fin (n + 1) → V × V) 0) *
        ∏ i : Fin n, diagramTransfer q (b i)
          ((Fin.snoc b p : Fin (n + 1) → V × V) i.succ) := by
  classical
  induction n generalizing p with
  | zero =>
    simp only [diagramIterate, Fin.prod_univ_zero, mul_one]
    rw [tsum_eq_single (fun i : Fin 0 => Fin.elim0 i)
      (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
    rfl
  | succ n ih =>
    rw [diagramIterate]
    simp_rw [ih, ← ENNReal.tsum_mul_right]
    symm
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => V × V)).tsum_eq,
      ENNReal.tsum_prod']
    apply tsum_congr
    intro r
    apply tsum_congr
    intro b
    change diagramInitial q x ((Fin.snoc (Fin.snoc b r) p : Fin (n + 2) → V × V) 0) *
        (∏ i : Fin (n + 1), diagramTransfer q ((Fin.snoc b r : Fin (n + 1) → V × V) i)
          ((Fin.snoc (Fin.snoc b r) p : Fin (n + 2) → V × V) i.succ)) =
      (diagramInitial q x ((Fin.snoc b r : Fin (n + 1) → V × V) 0) *
        ∏ i : Fin n, diagramTransfer q (b i)
          ((Fin.snoc b r : Fin (n + 1) → V × V) i.succ)) *
          diagramTransfer q r p
    rw [Fin.snoc_apply_zero, Fin.prod_univ_castSucc]
    simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
    ac_rfl

/-- A coefficient diagram has `n+1` pair states, `n` interior transfers,
and one separate terminal factor. -/
theorem laceDiagram_eq_tsum_chain (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) :
    laceDiagram q n x y = ∑' b : Fin (n + 1) → V × V,
      diagramInitial q x (b 0) *
        (∏ i : Fin n, diagramTransfer q (b i.castSucc) (b i.succ)) *
          diagramTerminal q (b (Fin.last n)) y := by
  classical
  unfold laceDiagram
  simp_rw [diagramIterate_eq_tsum_chain, ← ENNReal.tsum_mul_right]
  symm
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => V × V)).tsum_eq,
    ENNReal.tsum_prod']
  apply tsum_congr
  intro p
  apply tsum_congr
  intro b
  change diagramInitial q x ((Fin.snoc b p : Fin (n + 1) → V × V) 0) *
      (∏ i : Fin n, diagramTransfer q ((Fin.snoc b p : Fin (n + 1) → V × V) i.castSucc)
        ((Fin.snoc b p : Fin (n + 1) → V × V) i.succ)) *
          diagramTerminal q ((Fin.snoc b p : Fin (n + 1) → V × V) (Fin.last n)) y = _
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The actual coefficient is bounded by the explicit finite chain of
proved diagram factors, with no assumed chain comparison. -/
theorem laceCoefficient_succ_le_tsum_chain [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) :
    laceCoefficient q (n + 1) x y ≤ ∑' b : Fin (n + 1) → V × V,
      diagramInitial q x (b 0) *
        (∏ i : Fin n, diagramTransfer q (b i.castSucc) (b i.succ)) *
          diagramTerminal q (b (Fin.last n)) y :=
  (laceCoefficient_succ_le_laceDiagram q n x y).trans_eq
    (laceDiagram_eq_tsum_chain q n x y)

/-- Exposing one connector state per layer unrolls the actual transfer and
terminal factors, without dropping any deleted-bond restriction. -/
theorem prod_diagramTransfer_mul_terminal_eq_tsum (q : Sym2 V → unitInterval)
    {n : ℕ} (b : Fin (n + 1) → V × V) (y : V) :
    (∏ i : Fin n, diagramTransfer q (b i.castSucc) (b i.succ)) *
        diagramTerminal q (b (Fin.last n)) y =
      ∑' s : Fin (n + 1) → V × V,
        (∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc) *
          diagramInterior q (s i.castSucc) (b i.succ)) *
        (diagramConnector q (b (Fin.last n)) (s (Fin.last n)) *
          tau q (s (Fin.last n)).1 (s (Fin.last n)).2 *
            tau q (s (Fin.last n)).1 y * tau q (s (Fin.last n)).2 y) := by
  classical
  let f : Fin (n + 1) → (V × V) → ℝ≥0∞ := Fin.lastCases
    (fun s => diagramConnector q (b (Fin.last n)) s * tau q s.1 s.2 *
      tau q s.1 y * tau q s.2 y)
    (fun i s => diagramConnector q (b i.castSucc) s * diagramInterior q s (b i.succ))
  simpa only [Fin.prod_univ_castSucc, f, Fin.lastCases_castSucc, Fin.lastCases_last,
    diagramTransfer, diagramTerminal] using Probability.prod_tsum_eq_tsum_prod f

/-- The full primitive chain retains both pair-state tuples, including the
separate connector in the terminal layer. -/
theorem laceDiagram_eq_tsum_primitive_chain (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) :
    laceDiagram q n x y =
      ∑' b : Fin (n + 1) → V × V, ∑' s : Fin (n + 1) → V × V,
        diagramInitial q x (b 0) *
          (∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc) *
            diagramInterior q (s i.castSucc) (b i.succ)) *
          (diagramConnector q (b (Fin.last n)) (s (Fin.last n)) *
            tau q (s (Fin.last n)).1 (s (Fin.last n)).2 *
              tau q (s (Fin.last n)).1 y * tau q (s (Fin.last n)).2 y) := by
  classical
  rw [laceDiagram_eq_tsum_chain]
  apply tsum_congr
  intro b
  rw [mul_assoc, prod_diagramTransfer_mul_terminal_eq_tsum, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro s
  ac_rfl

section CharacterRoute

variable {G : Type*} [AddCommGroup G]

/-- A chain with two end segments, `n+1` connector segments and `n` joining
segments has route constant `2n+3`. The vertex choices can later alternate. -/
theorem character_weight_chain_route_le (ψ : AddChar G Circle) (n : ℕ)
    (x y : G) (b s : Fin (n + 1) → G) :
    ENNReal.ofReal (1 - (ψ (y - x) : ℂ).re) ≤
      ((2 * n + 3 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (1 - (ψ (b 0 - x) : ℂ).re) +
          (∑ i : Fin (n + 1), ENNReal.ofReal (1 - (ψ (s i - b i) : ℂ).re)) +
          (∑ i : Fin n, ENNReal.ofReal (1 - (ψ (b i.succ - s i.castSucc) : ℂ).re)) +
          ENNReal.ofReal (1 - (ψ (y - s (Fin.last n)) : ℂ).re)) := by
  classical
  let I := Unit ⊕ Fin (n + 1) ⊕ Fin n ⊕ Unit
  let d : I → G := Sum.elim (fun _ => b 0 - x)
    (Sum.elim (fun i => s i - b i)
      (Sum.elim (fun i => b i.succ - s i.castSucc) (fun _ => y - s (Fin.last n))))
  have hsum : (∑ i : I, d i) = y - x := by
    simp only [I, d, Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl,
      Sum.elim_inr, Finset.sum_sub_distrib]
    rw [Fin.sum_univ_succ b, Fin.sum_univ_castSucc s]
    abel
  have hcard : Fintype.card I = 2 * n + 3 := by
    simp only [I, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    omega
  have h := character_weight_sum_le ψ (Finset.univ : Finset I) d
  rw [hsum, Finset.card_univ, hcard] at h
  simpa only [I, d, Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl,
    Sum.elim_inr, add_assoc] using h

/-- The actual coefficient admits an explicit sum of single marks along an
alternating primitive route. The constant is linear in the order; the deleted
connectors and the two interior geometries are retained in each summand. -/
theorem laceCoefficient_succ_character_weight_le_primitive_chain [Countable G]
    (q : Sym2 G → unitInterval) (ψ : AddChar G Circle) (n : ℕ) (x y : G) :
    let c : Fin (n + 1) → (G × G) → G := fun i p => if Even i.val then p.2 else p.1
    let h : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    h (y - x) * laceCoefficient q (n + 1) x y ≤
      ((2 * n + 3 : ℕ) : ℝ≥0∞) *
        ∑' b : Fin (n + 1) → G × G, ∑' s : Fin (n + 1) → G × G,
          (h (c 0 (b 0) - x) +
            (∑ i : Fin (n + 1), h (c i (s i) - c i (b i))) +
            (∑ i : Fin n, h (c i.succ (b i.succ) - c i.castSucc (s i.castSucc))) +
            h (y - c (Fin.last n) (s (Fin.last n)))) *
          (diagramInitial q x (b 0) *
            (∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc) *
              diagramInterior q (s i.castSucc) (b i.succ)) *
            (diagramConnector q (b (Fin.last n)) (s (Fin.last n)) *
              tau q (s (Fin.last n)).1 (s (Fin.last n)).2 *
                tau q (s (Fin.last n)).1 y * tau q (s (Fin.last n)).2 y)) := by
  classical
  dsimp only
  refine (mul_le_mul' le_rfl (laceCoefficient_succ_le_laceDiagram q n x y)).trans ?_
  rw [laceDiagram_eq_tsum_primitive_chain]
  simp_rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro b
  apply ENNReal.tsum_le_tsum
  intro s
  have h := character_weight_chain_route_le ψ n x y
    (fun i => if Even i.val then (b i).2 else (b i).1)
    (fun i => if Even i.val then (s i).2 else (s i).1)
  exact (mul_le_mul' h le_rfl).trans_eq (mul_assoc _ _ _)

end CharacterRoute

end PercLib.Percolation.Bond.Lace
