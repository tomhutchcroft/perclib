/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original summation of the proved weighted coefficient bounds;
no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.FirstWeighted
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exact sums of the weighted lace coefficient bounds

## Main results

The positive-order weighted coefficient series retains the improved first-order
term, distinct forward and backward transfer constants, and the parity of the
connector and joining marks. All geometric factors are evaluated as nonnegative
extended-real expressions, so no subtraction of divergent series is used.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

private theorem tsum_fin_nat_sub (f : ℕ → ℕ → ℝ≥0∞) :
    (∑' n : ℕ, ∑ i : Fin (n + 1), f i.val (n - i.val)) = ∑' i, ∑' j, f i j := by
  classical
  calc
    _ = ∑' n : ℕ, ∑ p ∈ Finset.antidiagonal n, f p.1 p.2 := by
      apply tsum_congr
      intro n
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
      exact Fin.sum_univ_eq_sum_range (fun i => f i (n - i)) (n + 1)
    _ = ∑' n : ℕ, ∑' p : Finset.antidiagonal n, f p.1.1 p.1.2 := by
      apply tsum_congr
      intro n
      rw [tsum_fintype]
      exact (Finset.sum_coe_sort (Finset.antidiagonal n)
        (fun p : ℕ × ℕ => f p.1 p.2)).symm
    _ = ∑' p : (Σ n : ℕ, Finset.antidiagonal n), f p.2.1.1 p.2.1.2 := by
      rw [ENNReal.tsum_sigma']
    _ = ∑' p : ℕ × ℕ, f p.1 p.2 :=
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (fun p => f p.1 p.2)
    _ = _ := ENNReal.tsum_prod'

private theorem tsum_fin_nat_sub_tail (f : ℕ → ℕ → ℝ≥0∞) :
    (∑' n : ℕ, ∑ i : Fin (n + 2), f i.val (n + 1 - i.val)) =
      (∑' j, f 0 (j + 1)) + ∑' i, ∑' j, f (i + 1) j := by
  have h (n : ℕ) :
      (∑ i : Fin (n + 2), f i.val (n + 1 - i.val)) =
        f 0 (n + 1) + ∑ i : Fin (n + 1), f (i.val + 1) (n - i.val) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
  simp_rw [h, ENNReal.tsum_add]
  rw [tsum_fin_nat_sub (fun i j => f (i + 1) j)]

private theorem tsum_nat_mul_pow (r : ℝ≥0∞) :
    (∑' n : ℕ, (n : ℝ≥0∞) * r ^ n) = r * (1 - r)⁻¹ ^ 2 := by
  have h := tsum_fin_nat_sub (fun i j => r ^ (i + j))
  have hleft (n : ℕ) :
      (∑ i : Fin (n + 1), r ^ (i.val + (n - i.val))) = (n + 1) * r ^ n := by
    have he (i : Fin (n + 1)) : i.val + (n - i.val) = n := by omega
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
  simp_rw [hleft, pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric] at h
  calc
    _ = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * r ^ (n + 1) := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp
    _ = r * (∑' n : ℕ, (n + 1) * r ^ n) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      push_cast
      rw [pow_succ]
      ring
    _ = _ := by rw [h]; ring

private theorem tsum_affine_geometric (r a b : ℝ≥0∞) :
    (∑' n : ℕ, (a * n + b) * r ^ n) =
      a * r * (1 - r)⁻¹ ^ 2 + b * (1 - r)⁻¹ := by
  simp_rw [add_mul, mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [tsum_nat_mul_pow, ENNReal.tsum_geometric]

private theorem tsum_route_geometric_tail (r : ℝ≥0∞) :
    (∑' n : ℕ, ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * r ^ (n + 1)) =
      5 * r * (1 - r)⁻¹ + 2 * r ^ 2 * (1 - r)⁻¹ ^ 2 := by
  have he (n : ℕ) : ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * r ^ (n + 1) =
      r * ((2 * n + 5) * r ^ n) := by push_cast; rw [pow_succ]; ring
  simp_rw [he]
  rw [ENNReal.tsum_mul_left, tsum_affine_geometric]
  ring

private theorem tsum_affine_double_geometric (r s a b c : ℝ≥0∞) :
    (∑' i : ℕ, ∑' j : ℕ, (a * i + b * j + c) * r ^ i * s ^ j) =
      (1 - r)⁻¹ * (1 - s)⁻¹ *
        (c + a * r * (1 - r)⁻¹ + b * s * (1 - s)⁻¹) := by
  have he (i j : ℕ) : (a * i + b * j + c) * r ^ i * s ^ j =
      a * (((i : ℝ≥0∞) * r ^ i) * s ^ j) +
        b * (r ^ i * ((j : ℝ≥0∞) * s ^ j)) + c * (r ^ i * s ^ j) := by ring
  simp_rw [he, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    tsum_nat_mul_pow, ENNReal.tsum_geometric]
  ring

private theorem tsum_parity_affine_double_geometric
    (r s a b c u v : ℝ≥0∞) :
    (∑' i : ℕ, ∑' j : ℕ,
      (a * i + b * j + c) * r ^ i * s ^ j * (if Even i then u else v)) =
      u * (1 - r ^ 2)⁻¹ * (1 - s)⁻¹ *
        (c + 2 * a * r ^ 2 * (1 - r ^ 2)⁻¹ + b * s * (1 - s)⁻¹) +
      v * r * (1 - r ^ 2)⁻¹ * (1 - s)⁻¹ *
        (a + c + 2 * a * r ^ 2 * (1 - r ^ 2)⁻¹ + b * s * (1 - s)⁻¹) := by
  classical
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  have he (i j : ℕ) :
      (a * (2 * i : ℕ) + b * j + c) * r ^ (2 * i) * s ^ j *
          (if Even (2 * i) then u else v) =
        u * (((2 * a) * i + b * j + c) * (r ^ 2) ^ i * s ^ j) := by
    simp only [even_two, Even.mul_right, ite_true, pow_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have ho (i j : ℕ) :
      (a * (2 * i + 1 : ℕ) + b * j + c) * r ^ (2 * i + 1) * s ^ j *
          (if Even (2 * i + 1) then u else v) =
        (v * r) * (((2 * a) * i + b * j + (a + c)) * (r ^ 2) ^ i * s ^ j) := by
    simp only [Nat.even_add_one, even_two, Even.mul_right, not_true_eq_false, ite_false,
      pow_add, pow_mul, pow_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  simp_rw [he, ho, ENNReal.tsum_mul_left, tsum_affine_double_geometric]
  ring

private theorem tsum_connector_route_tail (r s J : ℝ≥0∞) :
    (∑' n : ℕ, ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
      ∑ i : Fin (n + 2), r ^ i.val * s ^ (n + 1 - i.val) *
        (if Even i.val then 1 else J)) =
      (5 * s * (1 - s)⁻¹ + 2 * s ^ 2 * (1 - s)⁻¹ ^ 2) +
      r ^ 2 * (1 - r ^ 2)⁻¹ * (1 - s)⁻¹ *
        (7 + 4 * r ^ 2 * (1 - r ^ 2)⁻¹ + 2 * s * (1 - s)⁻¹) +
      J * r * (1 - r ^ 2)⁻¹ * (1 - s)⁻¹ *
        (5 + 4 * r ^ 2 * (1 - r ^ 2)⁻¹ + 2 * s * (1 - s)⁻¹) := by
  classical
  let f : ℕ → ℕ → ℝ≥0∞ := fun i j =>
    (2 * i + 2 * j + 3) * r ^ i * s ^ j * (if Even i then 1 else J)
  have hindex (n : ℕ) :
      ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
          (∑ i : Fin (n + 2), r ^ i.val * s ^ (n + 1 - i.val) *
            (if Even i.val then 1 else J)) =
        ∑ i : Fin (n + 2), f i.val (n + 1 - i.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2 * i.val + 2 * (n + 1 - i.val) + 3 = 2 * (n + 1) + 3 := by omega
    have hi' : ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) =
        2 * (i.val : ℝ≥0∞) + 2 * ((n + 1 - i.val : ℕ) : ℝ≥0∞) + 3 := by
      exact_mod_cast hi.symm
    dsimp only [f]
    rw [hi']
    ring
  simp_rw [hindex]
  rw [tsum_fin_nat_sub_tail]
  have hzero (j : ℕ) : f 0 (j + 1) =
      ((2 * (j + 1) + 3 : ℕ) : ℝ≥0∞) * s ^ (j + 1) := by simp [f]
  have hs (i j : ℕ) : f (i + 1) j =
      r * ((2 * i + 2 * j + 5) * r ^ i * s ^ j *
        (if Even i then J else 1)) := by
    simp only [f, Nat.even_add_one, ite_not, pow_succ, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [hzero, hs, tsum_route_geometric_tail, ENNReal.tsum_mul_left,
    tsum_parity_affine_double_geometric]
  ring

private theorem tsum_joining_route_tail (r s M H : ℝ≥0∞) :
    (∑' n : ℕ, ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
      ∑ i : Fin (n + 1), r ^ i.val * s ^ (n - i.val) *
        (M + if Even i.val then 0 else H)) =
      M * (1 - r)⁻¹ * (1 - s)⁻¹ *
        (5 + 2 * r * (1 - r)⁻¹ + 2 * s * (1 - s)⁻¹) +
      H * r * (1 - r ^ 2)⁻¹ * (1 - s)⁻¹ *
        (7 + 4 * r ^ 2 * (1 - r ^ 2)⁻¹ + 2 * s * (1 - s)⁻¹) := by
  classical
  let f : ℕ → ℕ → ℝ≥0∞ := fun i j =>
    (2 * i + 2 * j + 5) * r ^ i * s ^ j * (M + if Even i then 0 else H)
  have hindex (n : ℕ) :
      ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
          (∑ i : Fin (n + 1), r ^ i.val * s ^ (n - i.val) *
            (M + if Even i.val then 0 else H)) =
        ∑ i : Fin (n + 1), f i.val (n - i.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2 * i.val + 2 * (n - i.val) + 5 = 2 * (n + 1) + 3 := by omega
    have hi' : ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) =
        2 * (i.val : ℝ≥0∞) + 2 * ((n - i.val : ℕ) : ℝ≥0∞) + 5 := by
      exact_mod_cast hi.symm
    dsimp only [f]
    rw [hi']
    ring
  simp_rw [hindex]
  rw [tsum_fin_nat_sub]
  have he (i j : ℕ) : f i j =
      M * ((2 * i + 2 * j + 5) * r ^ i * s ^ j) +
      (2 * i + 2 * j + 5) * r ^ i * s ^ j * (if Even i then 0 else H) := by
    dsimp only [f]
    ring
  simp_rw [he, ENNReal.tsum_add, ENNReal.tsum_mul_left,
    tsum_affine_double_geometric, tsum_parity_affine_double_geometric]
  ring

private theorem tsum_weighted_route_tail
    (r s α Δ Md Mr W H J : ℝ≥0∞) :
    let R := (1 - r)⁻¹
    let S := (1 - s)⁻¹
    let E := (1 - r ^ 2)⁻¹
    let A : ℝ≥0∞ → ℝ≥0∞ := fun t =>
      5 * t * (1 - t)⁻¹ + 2 * t ^ 2 * (1 - t)⁻¹ ^ 2
    let B := R * S * (5 + 2 * r * R + 2 * s * S)
    let C := A s + r ^ 2 * E * S * (7 + 4 * r ^ 2 * E + 2 * s * S) +
      J * r * E * S * (5 + 4 * r ^ 2 * E + 2 * s * S)
    let O := r * E * S * (7 + 4 * r ^ 2 * E + 2 * s * S)
    (∑' n : ℕ, ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
      (Δ * s ^ (n + 1) * Mr * W + α * r ^ (n + 1) * Md * W +
        (∑ i : Fin (n + 2), α * Δ * r ^ i.val * s ^ (n + 1 - i.val) *
          ((if Even i.val then 1 else J) * W)) +
        (∑ i : Fin (n + 1), α * Δ * r ^ i.val * s ^ (n - i.val) *
          (Md * Mr * W + if Even i.val then 0 else H)))) =
      (Δ * Mr * A s + α * Md * A r + α * Δ * C + α * Δ * Md * Mr * B) * W +
        α * Δ * H * O := by
  classical
  dsimp only
  have hC (n : ℕ) :
      (∑ i : Fin (n + 2), α * Δ * r ^ i.val * s ^ (n + 1 - i.val) *
        ((if Even i.val then 1 else J) * W)) =
      (α * Δ * W) * ∑ i : Fin (n + 2),
        r ^ i.val * s ^ (n + 1 - i.val) * (if Even i.val then 1 else J) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hJ (n : ℕ) :
      (∑ i : Fin (n + 1), α * Δ * r ^ i.val * s ^ (n - i.val) *
        (Md * Mr * W + if Even i.val then 0 else H)) =
      (α * Δ) * ∑ i : Fin (n + 1),
        r ^ i.val * s ^ (n - i.val) * (Md * Mr * W + if Even i.val then 0 else H) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hC, hJ]
  have hI (n : ℕ) :
      ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * (Δ * s ^ (n + 1) * Mr * W) =
        (Δ * Mr * W) * (((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * s ^ (n + 1)) := by ring
  have hT (n : ℕ) :
      ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * (α * r ^ (n + 1) * Md * W) =
        (α * Md * W) * (((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * r ^ (n + 1)) := by ring
  have hC' (n : ℕ) :
      ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * ((α * Δ * W) *
        ∑ i : Fin (n + 2), r ^ i.val * s ^ (n + 1 - i.val) *
          (if Even i.val then 1 else J)) =
      (α * Δ * W) * (((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
        ∑ i : Fin (n + 2), r ^ i.val * s ^ (n + 1 - i.val) *
          (if Even i.val then 1 else J)) := by ring
  have hJ' (n : ℕ) :
      ((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) * ((α * Δ) *
        ∑ i : Fin (n + 1), r ^ i.val * s ^ (n - i.val) *
          (Md * Mr * W + if Even i.val then 0 else H)) =
      (α * Δ) * (((2 * (n + 1) + 3 : ℕ) : ℝ≥0∞) *
        ∑ i : Fin (n + 1), r ^ i.val * s ^ (n - i.val) *
          (Md * Mr * W + if Even i.val then 0 else H)) := by ring
  have hsplit (k i t c j : ℝ≥0∞) :
      k * (i + t + c + j) = k * i + k * t + k * c + k * j := by ring
  simp_rw [hsplit, ENNReal.tsum_add, hI, hT, hC', hJ', ENNReal.tsum_mul_left]
  rw [tsum_route_geometric_tail, tsum_route_geometric_tail,
    tsum_connector_route_tail, tsum_joining_route_tail]
  ring

variable {G : Type*} [AddCommGroup G] [Countable G]

open scoped Classical in
/-- The exact rational sum of the proved positive-order character-weighted
coefficient bounds. The first coefficient retains its collapsed term `W0`,
the nontrivial initial mass `a`, and the rooted deleted mass `Md0`.
The distinct transfer constants and the alternating joining marks are preserved.
The inequality is valid in extended reals, even when its upper bound is infinite. -/
theorem tsum_laceCoefficient_positive_character_weight_mass_le
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (ρ σ Md Mr : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let α := ∑' p, diagramInitial q 0 p
    let a := ∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p
    let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
    let Γ := ∑' p : G × G, if p = (0, 0) then 0 else
      tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0
    let Md0 := ∑' s : G × G, diagramConnector q (0, 0) s * tau q s.1 s.2
    let W0 := diagramWeightedPair q w 0
    let W := ⨆ z, diagramWeightedPair q w z
    let J := ∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v
    let H := ⨆ p, ⨆ r, diagramMarkedJoiningSecondCore q w p r
    let R := (1 - ρ)⁻¹
    let S := (1 - σ)⁻¹
    let E := (1 - ρ ^ 2)⁻¹
    let A : ℝ≥0∞ → ℝ≥0∞ := fun t =>
      5 * t * (1 - t)⁻¹ + 2 * t ^ 2 * (1 - t)⁻¹ ^ 2
    let B := R * S * (5 + 2 * ρ * R + 2 * σ * S)
    let C := A σ + ρ ^ 2 * E * S * (7 + 4 * ρ ^ 2 * E + 2 * σ * S) +
      J * ρ * E * S * (5 + 4 * ρ ^ 2 * E + 2 * σ * S)
    let O := ρ * E * S * (7 + 4 * ρ ^ 2 * E + 2 * σ * S)
    (∑' n : ℕ, ∑' y, w y * laceCoefficient q (n + 1) 0 y) ≤
      W0 + (3 * (Δ * Mr + a * Δ + a * Md) + 2 * (Γ + Md0) +
        Δ * Mr * A σ + α * Md * A ρ + α * Δ * C + α * Δ * Md * Mr * B) * W +
          α * Δ * H * O := by
  classical
  dsimp only
  let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
  have hfirst := laceCoefficient_one_character_weight_mass_le q hq ψ Md Mr hMd hMr
  have htail := ENNReal.tsum_le_tsum fun n : ℕ =>
    laceCoefficient_succ_character_weight_mass_le q hq ψ 0 (n + 1)
      ρ σ Md Mr hρ hσ hMd hMr
  simp only [sub_zero, Nat.add_sub_cancel, Nat.add_assoc] at htail
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [zero_add]
  refine (add_le_add hfirst htail).trans_eq ?_
  rw [tsum_weighted_route_tail]
  ring

omit [Countable G] in
/-- The zeroth weighted coefficient is exactly the weighted `piZero` row;
all remaining orders form the positive-order series bounded above. -/
theorem tsum_laceCoefficient_character_weight_eq_piZero_add
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) :
    (∑' n : ℕ, ∑' y, w y * laceCoefficient q n 0 y) =
      (∑' y, w y * piZero q 0 y) +
        ∑' n : ℕ, ∑' y, w y * laceCoefficient q (n + 1) 0 y := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [laceCoefficient_zero]

end PercLib.Percolation.Bond.Lace
