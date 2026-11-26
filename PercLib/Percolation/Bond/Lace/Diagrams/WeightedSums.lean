/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original assembly of marked iterated cuts for the deleted lace diagrams;
no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedEnds

/-!
# Weighted sums of marked iterated cuts

## Main results

Exact translation identities isolate the initial, joining and terminal cores
in actual forward/backward cuts. Their bounds retain separate forward and
backward geometric factors. The second joining norm is the supremum of the
defined actual diagram. These are estimates of marked iterated cuts; identifying
their finite-position sum with the primitive finite-chain route remains separate.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

private theorem tsum_forward_kernel_reverse_eq
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (f : (G × G) → (G × G) → ℝ≥0∞) (x : G) (i j : ℕ) :
    (∑' y, ∑' p, ∑' s, diagramIterate q x i p * f p s * diagramReverseIterate q y j s) =
      ∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r *
        (∑' y, f p (r.1 + y, r.2 + y)) := by
  classical
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro p
  calc
    _ = ∑' y, ∑' r : G × G, diagramIterate q x i p *
        f p (r.1 + y, r.2 + y) * diagramReverseIterate q 0 j r := by
      apply tsum_congr
      intro y
      rw [← (Equiv.prodCongr (Equiv.addRight y) (Equiv.addRight y)).tsum_eq]
      apply tsum_congr
      intro r
      change diagramIterate q x i p * f p (r.1 + y, r.2 + y) *
        diagramReverseIterate q y j (r.1 + y, r.2 + y) = _
      have hG := diagramReverseIterate_add_right q hq 0 j r y
      simp only [zero_add] at hG
      rw [hG]
    _ = _ := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro r
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y
      ac_rfl

/-- Exact initial marked cut, with the second-coordinate mark of the primitive route. -/
theorem markedInitial_mass_eq_tsum_core
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (x : G) (n : ℕ) :
    (∑' y, ∑' p, ∑' s, diagramInitial q x p *
      (w (p.2 - x) * diagramConnector q p s) * diagramReverseIterate q y n s) =
      ∑' r, diagramReverseIterate q 0 n r * diagramMarkedInitialCore q w x r := by
  classical
  change (∑' y, ∑' p, ∑' s, diagramIterate q x 0 p *
    (w (p.2 - x) * diagramConnector q p s) * diagramReverseIterate q y n s) = _
  rw [tsum_forward_kernel_reverse_eq q hq]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro r
  simp only [diagramIterate, diagramMarkedInitialCore]
  simp_rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro y
  ac_rfl

/-- Exposing one backward step gives the actual joining cut with `i` forward
and `j` backward steps outside its two adjacent connectors. -/
theorem markedJoining_mass_eq_tsum_core
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (ε : Bool) (x : G) (i j : ℕ) :
    (∑' y, ∑' p, ∑' v, diagramIterate q x i p *
      (∑' s, ∑' t, diagramConnector q p s * diagramInterior q s t *
        diagramConnector q t v * w (if ε then t.1 - s.2 else t.2 - s.1)) *
          diagramReverseIterate q y j v) =
      ∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r *
        diagramMarkedJoiningCore q w ε p r := by
  classical
  rw [tsum_forward_kernel_reverse_eq q hq]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro r
  congr 1
  unfold diagramMarkedJoiningCore
  simpa only [ENNReal.tsum_prod'] using
    (ENNReal.tsum_comm (f := fun y (st : (G × G) × (G × G)) =>
      diagramConnector q p st.1 * diagramInterior q st.1 st.2 *
        diagramConnector q st.2 (r.1 + y, r.2 + y) *
          w (if ε then st.2.1 - st.1.2 else st.2.2 - st.1.1)))

/-- The connector cut identity holds for arbitrary nonnegative weights. -/
theorem markedConnector_mass_eq_tsum_core_of_weight
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (ε : Bool) (x : G) (i j : ℕ) :
    (∑' y, ∑' p, ∑' s, diagramIterate q x i p *
      (w ((if ε then s.2 else s.1) - (if ε then p.2 else p.1)) *
        diagramConnector q p s) * diagramReverseIterate q y j s) =
      ∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r *
        diagramMarkedConnectorCore q w ε p r := by
  rw [tsum_forward_kernel_reverse_eq q hq]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro r
  congr 1
  unfold diagramMarkedConnectorCore
  apply tsum_congr
  intro y
  cases ε <;> rfl

/-- The terminal marked cut contracts with the actual terminal core. -/
theorem markedTerminal_mass_eq_tsum_core
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) (ε : Bool) (x : G) (n : ℕ) :
    (∑' y, ∑' p, ∑' s, diagramIterate q x n p * diagramConnector q p s *
      tau q s.1 s.2 * tau q s.1 y * tau q s.2 y *
        w (y - (if ε then s.2 else s.1))) =
      ∑' p, diagramIterate q x n p * diagramMarkedTerminalCore q w ε p := by
  classical
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro p
  rw [ENNReal.tsum_comm]
  simp only [diagramMarkedTerminalCore]
  simp_rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro s
  apply tsum_congr
  intro y
  ac_rfl

/-- The exact initial core gives a backward geometric factor and the reverse
deleted mass bound, with constant one. -/
theorem tsum_reverse_mul_markedInitial_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (x : G) (n : ℕ) (σ Mr : ℝ≥0∞)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    (∑' r, diagramReverseIterate q 0 n r * diagramMarkedInitialCore q w x r) ≤
      (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * σ ^ n * Mr *
        ⨆ a, diagramWeightedPair q w a := by
  calc
    _ ≤ ∑' r, diagramReverseIterate q 0 n r *
        (Mr * (⨆ a, diagramWeightedPair q w a)) :=
      ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl
        ((diagramMarkedInitialCore_le_reverse_deleted_mass q hq w hw x r).trans
          (mul_le_mul' (hMr r) le_rfl))
    _ = (∑' r, diagramReverseIterate q 0 n r) *
        (Mr * (⨆ a, diagramWeightedPair q w a)) := ENNReal.tsum_mul_right
    _ ≤ ((∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * σ ^ n) *
        (Mr * (⨆ a, diagramWeightedPair q w a)) :=
      mul_le_mul' (diagramReverseIterate_mass_le_geometric q 0 σ hσ n) le_rfl
    _ = _ := by ac_rfl

/-- The terminal core gives a forward geometric factor and the forward
deleted mass bound for either coordinate. -/
theorem tsum_iterate_mul_markedTerminal_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (x : G) (n : ℕ) (ρ Md : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md) :
    (∑' p, diagramIterate q x n p * diagramMarkedTerminalCore q w ε p) ≤
      (∑' p, diagramInitial q x p) * ρ ^ n * Md * ⨆ a, diagramWeightedPair q w a := by
  calc
    _ ≤ ∑' p, diagramIterate q x n p * (Md * (⨆ a, diagramWeightedPair q w a)) :=
      ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl
        ((diagramMarkedTerminalCore_le_deleted_mass q hq w hw ε p).trans
          (mul_le_mul' (hMd p) le_rfl))
    _ = (∑' p, diagramIterate q x n p) * (Md * (⨆ a, diagramWeightedPair q w a)) :=
      ENNReal.tsum_mul_right
    _ ≤ ((∑' p, diagramInitial q x p) * ρ ^ n) *
        (Md * (⨆ a, diagramWeightedPair q w a)) :=
      mul_le_mul' (diagramIterate_mass_le_geometric q x ρ hρ n) le_rfl
    _ = _ := by ac_rfl

private theorem tsum_iterate_reverse_mul_le
    (q : Sym2 G → unitInterval) (x : G) (i j : ℕ) (ρ σ m : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (f : (G × G) → (G × G) → ℝ≥0∞) (hf : ∀ p r, f p r ≤ m) :
    (∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r * f p r) ≤
      (∑' p, diagramInitial q x p) *
        (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * ρ ^ i * σ ^ j * m := by
  calc
    _ ≤ ∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r * m :=
      ENNReal.tsum_le_tsum fun p => ENNReal.tsum_le_tsum fun r =>
        mul_le_mul' le_rfl (hf p r)
    _ = (∑' p, diagramIterate q x i p) * (∑' r, diagramReverseIterate q 0 j r) * m := by
      simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ ≤ ((∑' p, diagramInitial q x p) * ρ ^ i) *
        ((∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * σ ^ j) * m :=
      mul_le_mul' (mul_le_mul' (diagramIterate_mass_le_geometric q x ρ hρ i)
        (diagramReverseIterate_mass_le_geometric q 0 σ hσ j)) le_rfl
    _ = _ := by ac_rfl

/-- The connector contraction uses the proved weighted-pair bound: the
second coordinate costs one and the first coordinate costs the step mass. -/
theorem tsum_iterate_reverse_mul_markedConnector_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (x : G) (i j : ℕ) (ρ σ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ) :
    (∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r *
      diagramMarkedConnectorCore q w ε p r) ≤
      (∑' p, diagramInitial q x p) *
        (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * ρ ^ i * σ ^ j *
          ((if ε then 1 else ∑' v, offDiagonal (fun a b : G =>
            (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) *
              ⨆ a, diagramWeightedPair q w a) := by
  apply tsum_iterate_reverse_mul_le q x i j ρ σ _ hρ hσ
  intro p r
  cases ε
  · exact diagramMarkedConnectorCore_false_le_step_mass_mul_iSup q hq w hw p r
  · simpa only [↓reduceIte, one_mul] using
      diagramMarkedConnectorCore_true_le_iSup q hq w p r

/-- The joining contraction retains the forward and reverse deleted masses
separately. The residual is the supremum of the defined second geometry and
is charged only to the first-to-second coordinate mark. -/
theorem tsum_iterate_reverse_mul_markedJoining_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (ε : Bool) (x : G) (i j : ℕ)
    (ρ σ Md Mr : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    (∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r *
      diagramMarkedJoiningCore q w ε p r) ≤
      (∑' p, diagramInitial q x p) *
        (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * ρ ^ i * σ ^ j *
          (Md * Mr * (⨆ a, diagramWeightedPair q w a) +
            if ε then 0 else ⨆ p, ⨆ r, diagramMarkedJoiningSecondCore q w p r) := by
  apply tsum_iterate_reverse_mul_le q x i j ρ σ _ hρ hσ
  intro p r
  refine (diagramMarkedJoiningCore_le_deleted_masses q hq w hw ε p r).trans ?_
  apply add_le_add
  · exact mul_le_mul' (mul_le_mul' (hMd p) (hMr r)) le_rfl
  · cases ε
    · exact le_iSup_of_le p (le_iSup (fun r => diagramMarkedJoiningSecondCore q w p r) r)
    · exact le_rfl

/-- Summing all contracted positions keeps the independent forward/backward
powers and the alternating coordinate. This bounds the displayed iterated
cuts; the identity with a primitive finite-chain route is a separate statement. -/
theorem sum_marked_cuts_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (hw : w 0 = 0) (x : G) (n : ℕ) (ρ σ Md Mr : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    let α := ∑' p, diagramInitial q x p
    let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
    let W := ⨆ a, diagramWeightedPair q w a
    let J := ∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v
    let H := ⨆ p, ⨆ r, diagramMarkedJoiningSecondCore q w p r
    (∑' r, diagramReverseIterate q 0 n r * diagramMarkedInitialCore q w x r) +
      (∑' p, diagramIterate q x n p *
        diagramMarkedTerminalCore q w (decide (Even n)) p) +
      (∑ i : Fin (n + 1), ∑' p, ∑' r,
        diagramIterate q x i.val p * diagramReverseIterate q 0 (n - i.val) r *
          diagramMarkedConnectorCore q w (decide (Even i.val)) p r) +
      (∑ i : Fin n, ∑' p, ∑' r,
        diagramIterate q x i.val p * diagramReverseIterate q 0 (n - 1 - i.val) r *
          diagramMarkedJoiningCore q w (decide (Even i.val)) p r) ≤
      Δ * σ ^ n * Mr * W + α * ρ ^ n * Md * W +
      (∑ i : Fin (n + 1), α * Δ * ρ ^ i.val * σ ^ (n - i.val) *
        ((if Even i.val then 1 else J) * W)) +
      (∑ i : Fin n, α * Δ * ρ ^ i.val * σ ^ (n - 1 - i.val) *
        (Md * Mr * W + if Even i.val then 0 else H)) := by
  dsimp only
  apply add_le_add
  · apply add_le_add
    · exact add_le_add
        (tsum_reverse_mul_markedInitial_le q hq w hw x n σ Mr hσ hMr)
        (tsum_iterate_mul_markedTerminal_le q hq w hw _ x n ρ Md hρ hMd)
    · apply Finset.sum_le_sum
      intro i _
      simpa only [decide_eq_true_eq] using
        tsum_iterate_reverse_mul_markedConnector_le q hq w hw (decide (Even i.val))
          x i.val (n - i.val) ρ σ hρ hσ
  · apply Finset.sum_le_sum
    intro i _
    simpa only [decide_eq_true_eq] using
      tsum_iterate_reverse_mul_markedJoining_le q hq w hw (decide (Even i.val))
        x i.val (n - 1 - i.val) ρ σ Md Mr hρ hσ hMd hMr

end PercLib.Percolation.Bond.Lace
