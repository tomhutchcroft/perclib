/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Basic
public import PercLib.Percolation.Bond.Lace.InitialExpansion
public import PercLib.Percolation.Bond.Lace.Remainder.Convergence

/-!
# Finiteness and convolution for the finite signed expansion

Finite coefficient row masses and a finite continuation bound justify taking
real values and interchanging the finite alternating sum with the convolution.
The order-zero remainder retains the diagonal double-connection contribution.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Finiteness of a coefficient row mass implies pointwise finiteness. -/
theorem laceCoefficient_ne_top_of_mass_ne_top (q : Sym2 V → unitInterval)
    (n : ℕ) (x u : V) (hmass : (∑' z, laceCoefficient q n x z) ≠ ⊤) :
    laceCoefficient q n x u ≠ ⊤ :=
  ne_top_of_le_ne_top hmass (ENNReal.le_tsum u)

/-- A finite continuation bound controls the coefficient convolution with the
same constant at every order, including order zero. -/
theorem laceCoefficient_step_le_mass_mul (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) (C : ℝ≥0∞)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C) :
    (∑' u, ∑' v, laceCoefficient q n x u *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ (∑' u, laceCoefficient q n x u) * C := by
  calc
    _ = ∑' u, laceCoefficient q n x u * (∑' v,
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y) := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u, laceCoefficient q n x u * C :=
      ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hC u) _
    _ = _ := ENNReal.tsum_mul_right

/-- Coefficient mass finiteness and a finite continuation bound imply
finiteness of the full coefficient convolution. -/
theorem laceCoefficient_step_ne_top (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : (∑' u, laceCoefficient q n x u) ≠ ⊤) :
    (∑' u, ∑' v, laceCoefficient q n x u *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hmass hCfinite)
    (laceCoefficient_step_le_mass_mul q n x y C hC)

/-- At order zero the diagonal contribution gives the exact mass factor
`1 + Σ π₀`. This bound does not require finite clusters. -/
theorem laceRemainder_zero_le_one_add_mass_mul [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (C : ℝ≥0∞)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C) :
    laceRemainder q 0 x y ≤ (1 + ∑' u, laceCoefficient q 0 x u) * C := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  have hprob (u v : V) :
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ doubleConn x u ∧
        p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y} ≤
      law q (doubleConn x u) * tau q v y := by
    calc
      _ ≤ ((law q).prod (law q)) (doubleConn x u ×ˢ conn v y) :=
        measure_mono fun _ hp => ⟨hp.1, hp.2.1⟩
      _ = _ := Measure.prod_prod _ _
  have hmass : (∑' u, law q (doubleConn x u)) =
      1 + ∑' u, laceCoefficient q 0 x u := by
    simp_rw [law_doubleConn_eq_indicator_add_piZero, ENNReal.tsum_add]
    change (∑' u, if x = u then (1 : ℝ≥0∞) else 0) + (∑' u, piZero q x u) = _
    rw [tsum_eq_single x (fun u hu => by simp [Ne.symm hu])]
    simp [laceCoefficient]
  rw [laceRemainder_zero_eq_tsum_prod]
  calc
    _ ≤ ∑' u, ∑' v, law q (doubleConn x u) * J u v * tau q v y := by
      apply ENNReal.tsum_le_tsum
      intro u
      apply ENNReal.tsum_le_tsum
      intro v
      calc
        _ ≤ J u v * (law q (doubleConn x u) * tau q v y) :=
          mul_le_mul' le_rfl (hprob u v)
        _ = _ := by ac_rfl
    _ = ∑' u, law q (doubleConn x u) * (∑' v, J u v * tau q v y) := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u, law q (doubleConn x u) * C :=
      ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hC u) _
    _ = _ := by rw [ENNReal.tsum_mul_right, hmass]

/-- The coefficient mass at the same order suffices for finiteness of the
nonnegative remainder, including its exceptional order-zero diagonal term. -/
theorem laceRemainder_ne_top_of_mass_ne_top [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : (∑' u, laceCoefficient q n x u) ≠ ⊤) :
    laceRemainder q n x y ≠ ⊤ := by
  cases n with
  | zero =>
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hmass⟩) hCfinite)
        (laceRemainder_zero_le_one_add_mass_mul q x y C hC)
  | succ n =>
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hmass hCfinite)
        (laceRemainder_succ_le_mass_mul q n x y C hC)

/-- Real convolution commutes with the finite alternating coefficient sum once
the nonnegative coefficient row masses and continuation bound are finite. -/
theorem partialLaceSum_step_eq_tsum (q : Sym2 V → unitInterval)
    (N : ℕ) (x y : V) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hmass : ∀ n ≤ N, (∑' u, laceCoefficient q n x u) ≠ ⊤) :
    (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n *
      (∑' u, ∑' v, laceCoefficient q n x u *
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y).toReal) =
      ∑' u, ∑' v, partialLaceSum q N x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  let F : ℕ → V × V → ℝ≥0∞ := fun n p =>
    laceCoefficient q n x p.1 * J p.1 p.2 * tau q p.2 y
  let f : ℕ → V × V → ℝ := fun n p => (F n p).toReal
  have hF (n : ℕ) (hn : n ∈ Finset.range (N + 1)) : (∑' p, F n p) ≠ ⊤ := by
    rw [ENNReal.tsum_prod']
    exact laceCoefficient_step_ne_top q n x y C hCfinite hC
      (hmass n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
  have hs (n : ℕ) (hn : n ∈ Finset.range (N + 1)) : Summable (f n) :=
    ENNReal.summable_toReal (hF n hn)
  have ht (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      (∑' u, ∑' v, laceCoefficient q n x u * J u v * tau q v y).toReal =
        ∑' p, f n p := by
    change (∑' u, ∑' v, F n (u, v)).toReal = _
    rw [← ENNReal.tsum_prod', ENNReal.tsum_toReal_eq
      (ENNReal.ne_top_of_tsum_ne_top (hF n hn))]
  have hsSum : Summable (fun p : V × V =>
      ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * f n p) :=
    summable_sum fun n hn => (hs n hn).mul_left ((-1 : ℝ) ^ n)
  calc
    _ = ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * (∑' p, f n p) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ht n hn]
    _ = ∑ n ∈ Finset.range (N + 1), ∑' p, (-1 : ℝ) ^ n * f n p := by
      simp_rw [tsum_mul_left]
    _ = ∑' p : V × V, ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * f n p :=
      (Summable.tsum_finsetSum fun n hn => (hs n hn).mul_left ((-1 : ℝ) ^ n)).symm
    _ = ∑' u, ∑' v, ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * f n (u, v) :=
      hsSum.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      simp only [f, F, J, ENNReal.toReal_mul, partialLaceSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      ring

end PercLib.Percolation.Bond.Lace
