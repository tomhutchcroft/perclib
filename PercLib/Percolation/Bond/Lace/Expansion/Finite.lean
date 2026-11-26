/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Basic
public import PercLib.Percolation.Bond.Lace.Expansion.Convolution
public import PercLib.Percolation.Bond.Lace.InitialExpansion
public import PercLib.Percolation.Bond.Lace.Remainder.Recurrence
public import PercLib.Percolation.Bond.Lace.Remainder.Telescoping

/-!
# Finite signed expansion of the canonical coefficients

## Main results

The finite identity follows from the proved nonnegative remainder recurrence.
Finiteness is explicit before converting to real numbers; no subtraction of
infinite extended-real quantities is used.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

open scoped Classical in
/-- The canonical signed finite expansion, with each continuation term kept
as the real value of its nonnegative sum. Analytic linearity can subsequently
combine the finite coefficient sum with the continuation kernel. -/
theorem finite_lace_expansion_expanded (q : Sym2 V → unitInterval)
    (N : ℕ) (x y : V)
    (hfin : ∀ a u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite)
    (hR : ∀ n ≤ N, laceRemainder q n x y ≠ ⊤)
    (hπ : ∀ n ≤ N, laceCoefficient q n x y ≠ ⊤)
    (hS : ∀ n ≤ N, (∑' u, ∑' v, laceCoefficient q n x u *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≠ ⊤)
    (hJ : (∑' v, offDiagonal (fun a b : V =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y) ≠ ⊤) :
    (tau q x y).toReal = (if x = y then 1 else 0) +
      (∑' v, offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y).toReal +
      (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n *
        ((laceCoefficient q n x y).toReal +
          (∑' u, ∑' v, laceCoefficient q n x u *
            offDiagonal (fun a b : V =>
              (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v y).toReal)) +
      signedLaceRemainder q N x y := by
  let S : ℕ → ℝ≥0∞ := fun n => ∑' u, ∑' v, laceCoefficient q n x u *
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v y
  let J : ℝ≥0∞ := ∑' v, offDiagonal (fun a b : V =>
    (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y
  have hzero : (tau q x y).toReal + (laceRemainder q 0 x y).toReal =
      ((if x = y then 1 else 0) + J.toReal) +
        ((laceCoefficient q 0 x y).toReal + (S 0).toReal) := by
    have hs : (∑' u, ∑' v, piZero q x u *
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y) ≠ ⊤ := by simpa only [laceCoefficient_zero] using hS 0 (Nat.zero_le N)
    have h := congrArg ENNReal.toReal
      (tau_add_laceRemainder_zero_eq_indicator_add_piZero q x y (hfin x))
    have hd : (if x = y then (1 : ℝ≥0∞) else 0) ≠ ⊤ := by split_ifs <;> simp
    rw [ENNReal.toReal_add
      (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q x y))
      (hR 0 (Nat.zero_le N))] at h
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨
      ENNReal.add_ne_top.mpr ⟨hd, piZero_ne_top q x y⟩, hJ⟩) hs,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hd, piZero_ne_top q x y⟩) hJ,
      ENNReal.toReal_add hd (piZero_ne_top q x y)] at h
    have hdreal : (if x = y then (1 : ℝ≥0∞) else 0).toReal =
        (if x = y then (1 : ℝ) else 0) := by split_ifs <;> simp
    rw [hdreal] at h
    simpa only [S, J, laceCoefficient_zero, add_assoc, add_left_comm, add_comm] using h
  have hnext : ∀ n < N,
      (laceRemainder q n x y).toReal + (laceRemainder q (n + 1) x y).toReal =
        (laceCoefficient q (n + 1) x y).toReal + (S (n + 1)).toReal := by
    intro n hn
    have h := congrArg ENNReal.toReal
      (laceRemainder_add_succ_eq_laceCoefficient_add_step q n x y hfin)
    rw [ENNReal.toReal_add (hR n (Nat.le_of_lt hn)) (hR (n + 1) hn),
      ENNReal.toReal_add (hπ (n + 1) hn) (hS (n + 1) hn)] at h
    exact h
  exact finite_alternating_identity
    (fun n => (laceCoefficient q n x y).toReal + (S n).toReal)
    (fun n => (laceRemainder q n x y).toReal) (tau q x y).toReal
    ((if x = y then 1 else 0) + J.toReal) hzero N hnext

private theorem finite_expansion_rearrange (N : ℕ) (f g : ℕ → ℝ)
    (a b B S r t : ℝ) (hb : b = B)
    (hS : (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * g n) = S)
    (h : t = a + b +
      (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * (f n + g n)) + r) :
    t = a + (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * f n) + B + S + r := by
  simp only [mul_add, Finset.sum_add_distrib, hb, hS] at h
  simpa only [add_assoc, add_left_comm, add_comm] using h

open scoped Classical in
/-- The finite signed lace expansion with the actual alternating coefficient
kernel and convolution. Finite coefficient row masses and a finite continuation
bound justify every conversion and interchange in the identity. -/
@[tag "XMUG"]
theorem finite_lace_expansion (q : Sym2 V → unitInterval)
    (N : ℕ) (x y : V)
    (hfin : ∀ a u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : ∀ n ≤ N, (∑' u, laceCoefficient q n x u) ≠ ⊤) :
    (tau q x y).toReal = (if x = y then 1 else 0) + partialLaceSum q N x y +
      (∑' v, (offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
      (∑' u, ∑' v, partialLaceSum q N x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal) +
      signedLaceRemainder q N x y := by
  have hJ := ne_top_of_le_ne_top hCfinite (hC x)
  have h := finite_lace_expansion_expanded q N x y hfin
    (fun n hn => laceRemainder_ne_top_of_mass_ne_top q n x y C hCfinite hC (hmass n hn))
    (fun n hn => laceCoefficient_ne_top_of_mass_ne_top q n x y (hmass n hn))
    (fun n hn => laceCoefficient_step_ne_top q n x y C hCfinite hC (hmass n hn)) hJ
  have hJreal :
      (∑' v, offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v * tau q v y).toReal =
      ∑' v, (offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal := by
    rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hJ)]
    simp only [ENNReal.toReal_mul]
  exact finite_expansion_rearrange N
    (fun n => (laceCoefficient q n x y).toReal)
    (fun n => (∑' u, ∑' v, laceCoefficient q n x u *
      offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v y).toReal)
    _ _ _ _ _ _ hJreal
    (partialLaceSum_step_eq_tsum q N x y C hCfinite hC hmass) h

end PercLib.Percolation.Bond.Lace
