/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface and the hierarchical geometry of
`PercLib.Models.HierarchicalGeometry`. The statements follow the wiki tags V4QQ and YWTU
(hierarchical two-point function), in conditional form. No source text or code is copied.
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.ClusterMoments
public import PercLib.Percolation.Bond.LocalConnectivity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ball sums from two-sided pointwise bounds on the hierarchical lattice

On `V = ℕ →₀ (Fin d → ZMod L)` write `h(z) = z.support.sup Nat.succ` for the level and
`B(x, n) = {y | h(y - x) ≤ n}` for the ball. Let `f : V → V → ℝ≥0∞` with `f x x ≤ 1` and,
for `x ≠ y` with `k = h(y - x)`, `a L^{-k(d-α)} ≤ f x y ≤ A L^{-k(d-α)}`. With `L ≥ 2`
and `α > 0`:

* `tsum_levelBall_le`: `∑_{y ∈ B(x,n)} f x y ≤ (1 + A L^α / (L^α - 1)) L^{αn}` for every `n`
  (the lower bound on `f` is not needed);
* `le_tsum_levelBall`: `(a/2) L^{αn} ≤ ∑_{y ∈ B(x,n)} f x y` for every `n ≥ 1`, when `d ≥ 1`
  (the upper bound on `f` is not needed). For `n = 0` the sum is `f x x`, which may be `0`,
  so no positive lower bound holds there in general;
* `lintegral_encard_cluster_inter_ball`: `E|K_x ∩ B(x,n)| = ∑_{y ∈ B(x,n)} τ(x,y)`;
* `lintegral_encard_cluster_inter_ball_bounds` (V4QQ/YWTU, conditional on the bounds for
  `τ`): `(a/2) L^{αn} ≤ E|K_x ∩ B(x,n)| ≤ c₂ L^{αn}` for `n ≥ 1`;
* `localConn_ball_bounds` (conditional on the bounds for the connection probability inside
  the smallest common ball): the same two-sided bound for the expected number of `y ∈ B(x,n)`
  joined to `x` inside `B(x, h(y - x))`, and the lower bound for `E|K_x ∩ B(x,n)|`.

The bounds on `τ` or on the local connection probability (W498) are hypotheses here, not an
`Input`.
-/

@[expose] public section
noncomputable section

open MeasureTheory PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

variable {d L : ℕ}

/-! ### Real arithmetic of the shells -/

/-- `L^{-m(d-α)} N^m = L^{αm}` with `N = L^d`. -/
theorem rpow_neg_mul_pow_pow {α : ℝ} (hL : 0 < L) (m : ℕ) :
    (L : ℝ) ^ (-(m : ℝ) * ((d : ℝ) - α)) * ((L : ℝ) ^ d) ^ m = (L : ℝ) ^ (α * m) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hL']
  congr 1
  push_cast
  ring

/-- Geometric sum of `ρ^{k+1}` over `k < n`, bounded by `ρ^{n+1} / (ρ - 1)` for `ρ > 1`. -/
theorem sum_range_pow_succ_le {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ρ ^ (k + 1) ≤ ρ / (ρ - 1) * ρ ^ n := by
  have hρ1 : 0 < ρ - 1 := by linarith
  have hgeom : ∑ k ∈ Finset.range n, ρ ^ (k + 1) = ρ * ((ρ ^ n - 1) / (ρ - 1)) := by
    rw [← geom_sum_eq hρ.ne', Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => pow_succ' ρ k
  rw [hgeom, div_mul_eq_mul_div, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  rw [div_le_div_iff_of_pos_right hρ1]
  linarith

/-! ### Radial reduction -/

/-- Shift a ball sum to the origin. -/
theorem tsum_levelBall_eq_tsum_level (f : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞)
    (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ) :
    ∑' y, (if (y - x).support.sup Nat.succ ≤ n then f x y else 0) =
      ∑' z : ℕ →₀ (Fin d → ZMod L), (if z.support.sup Nat.succ ≤ n then f x (x + z) else 0) := by
  rw [← (Equiv.addLeft x).tsum_eq]
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]

/-- **Item 1, upper bound.** If `f x x ≤ 1` and `f x y ≤ A L^{-h(y-x)(d-α)}` off the
diagonal, then `∑_{y ∈ B(x,n)} f x y ≤ (1 + A L^α / (L^α - 1)) L^{αn}`. -/
theorem tsum_levelBall_le (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α) {A : ℝ} (hA : 0 ≤ A)
    (f : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞)
    (hdiag : ∀ x, f x x ≤ 1)
    (hup : ∀ x y, x ≠ y → f x y ≤ ENNReal.ofReal
      (A * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))))
    (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ) :
    ∑' y, (if (y - x).support.sup Nat.succ ≤ n then f x y else 0) ≤
      ENNReal.ofReal ((1 + A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) * (L : ℝ) ^ (α * n)) := by
  have : NeZero L := ⟨by omega⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  set ρ := (L : ℝ) ^ α with hρ
  have hρ1 : 1 < ρ := Real.one_lt_rpow hL1 hα
  have hρn : ∀ m : ℕ, (L : ℝ) ^ (α * m) = ρ ^ m := fun m => Real.rpow_mul_natCast hL0.le α m
  let g : ℕ → ℝ≥0∞ := fun k => if k ≤ n then
    (if k = 0 then 1 else ENNReal.ofReal (A * (L : ℝ) ^ (-(k : ℝ) * ((d : ℝ) - α)))) else 0
  rw [tsum_levelBall_eq_tsum_level]
  calc ∑' z : ℕ →₀ (Fin d → ZMod L), (if z.support.sup Nat.succ ≤ n then f x (x + z) else 0)
      ≤ ∑' z : ℕ →₀ (Fin d → ZMod L), g (z.support.sup Nat.succ) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        simp only [g]
        split_ifs with h1 h2
        · rw [level_eq_zero_iff] at h2
          subst h2
          simpa using hdiag x
        · have hz : x ≠ x + z := by
            intro h
            apply h2
            rw [level_eq_zero_iff]
            simpa using h.symm
          simpa only [add_sub_cancel_left] using hup x (x + z) hz
        · exact le_rfl
    _ = 1 + ∑ k ∈ Finset.range n, (((L ^ d) ^ (k + 1) - (L ^ d) ^ k : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (A * (L : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * ((d : ℝ) - α))) := by
        rw [tsum_radial_eq, show g 0 = 1 by simp [g]]
        congr 1
        rw [tsum_eq_sum (s := Finset.range n)]
        · refine Finset.sum_congr rfl fun k hk => ?_
          have hk := Finset.mem_range.1 hk
          simp only [g, show k + 1 ≤ n by omega, ite_true, Nat.add_one_ne_zero, ite_false]
        · intro k hk
          have hk : n ≤ k := by simpa using hk
          simp only [g, show ¬ k + 1 ≤ n by omega, ite_false, mul_zero]
    _ ≤ 1 + ∑ k ∈ Finset.range n, ENNReal.ofReal (A * ρ ^ (k + 1)) := by
        gcongr with k hk
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have hcard : (((L ^ d) ^ (k + 1) - (L ^ d) ^ k : ℕ) : ℝ) ≤ ((L : ℝ) ^ d) ^ (k + 1) := by
          exact_mod_cast Nat.sub_le _ _
        have h := rpow_neg_mul_pow_pow (d := d) (α := α) (by omega : 0 < L) (k + 1)
        rw [hρn] at h
        calc (((L ^ d) ^ (k + 1) - (L ^ d) ^ k : ℕ) : ℝ) *
              (A * (L : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * ((d : ℝ) - α)))
            ≤ ((L : ℝ) ^ d) ^ (k + 1) * (A * (L : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * ((d : ℝ) - α))) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = A * ρ ^ (k + 1) := by rw [← h]; ring
    _ = ENNReal.ofReal (1 + A * ∑ k ∈ Finset.range n, ρ ^ (k + 1)) := by
        have hρ0 : 0 ≤ ρ := by linarith
        rw [ENNReal.ofReal_add zero_le_one
            (mul_nonneg hA (Finset.sum_nonneg fun k _ => pow_nonneg hρ0 _)), ENNReal.ofReal_one,
          Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hA (pow_nonneg hρ0 _))]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hρn]
        have hs := sum_range_pow_succ_le hρ1 n
        have hn1 : 1 ≤ ρ ^ n := one_le_pow₀ hρ1.le
        have : A * ∑ k ∈ Finset.range n, ρ ^ (k + 1) ≤ A * (ρ / (ρ - 1) * ρ ^ n) :=
          mul_le_mul_of_nonneg_left hs hA
        calc 1 + A * ∑ k ∈ Finset.range n, ρ ^ (k + 1) ≤ ρ ^ n + A * (ρ / (ρ - 1) * ρ ^ n) := by
              linarith
          _ = (1 + A * ρ / (ρ - 1)) * ρ ^ n := by ring

/-- **Item 1, lower bound.** If `d ≥ 1` and `a L^{-h(y-x)(d-α)} ≤ f x y` off the diagonal,
then `(a/2) L^{αn} ≤ ∑_{y ∈ B(x,n)} f x y` for every `n ≥ 1`. -/
theorem le_tsum_levelBall (hL : 2 ≤ L) (hd : 1 ≤ d) {α : ℝ} {a : ℝ} (ha : 0 ≤ a)
    (f : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞)
    (hlow : ∀ x y, x ≠ y → ENNReal.ofReal
      (a * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) ≤ f x y)
    (x : ℕ →₀ (Fin d → ZMod L)) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (a / 2 * (L : ℝ) ^ (α * n)) ≤
      ∑' y, (if (y - x).support.sup Nat.succ ≤ n then f x y else 0) := by
  have : NeZero L := ⟨by omega⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let g : ℕ → ℝ≥0∞ := fun k => if k = m + 1 then
    ENNReal.ofReal (a * (L : ℝ) ^ (-((m + 1 : ℕ) : ℝ) * ((d : ℝ) - α))) else 0
  rw [tsum_levelBall_eq_tsum_level]
  calc ENNReal.ofReal (a / 2 * (L : ℝ) ^ (α * ((m + 1 : ℕ) : ℝ)))
      ≤ (((L ^ d) ^ (m + 1) - (L ^ d) ^ m : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (a * (L : ℝ) ^ (-((m + 1 : ℕ) : ℝ) * ((d : ℝ) - α))) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hN : 2 ≤ L ^ d := le_trans hL (Nat.le_self_pow (by omega) L)
        have hcard : ((L : ℝ) ^ d) ^ (m + 1) / 2 ≤ (((L ^ d) ^ (m + 1) - (L ^ d) ^ m : ℕ) : ℝ) := by
          have hle : (L ^ d) ^ m ≤ (L ^ d) ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.cast_sub hle]
          push_cast
          have hN' : (2 : ℝ) ≤ (L : ℝ) ^ d := by exact_mod_cast hN
          have hpos : (0 : ℝ) ≤ ((L : ℝ) ^ d) ^ m := by positivity
          rw [pow_succ]
          nlinarith
        have h := rpow_neg_mul_pow_pow (d := d) (α := α) (by omega : 0 < L) (m + 1)
        calc a / 2 * (L : ℝ) ^ (α * ((m + 1 : ℕ) : ℝ))
            = ((L : ℝ) ^ d) ^ (m + 1) / 2 *
                (a * (L : ℝ) ^ (-((m + 1 : ℕ) : ℝ) * ((d : ℝ) - α))) := by rw [← h]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑' z : ℕ →₀ (Fin d → ZMod L), g (z.support.sup Nat.succ) := by
        rw [tsum_radial_eq, tsum_eq_single m]
        · simp [g]
        · intro k hk
          simp [g, hk]
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        simp only [g]
        split_ifs with h1 h2
        · have hz : x ≠ x + z := by
            intro h
            have : z = 0 := by simpa using h.symm
            rw [this, (level_eq_zero_iff 0).2 rfl] at h1
            omega
          have := hlow x (x + z) hz
          rwa [add_sub_cancel_left, h1] at this
        · omega
        · exact bot_le
        · exact le_rfl

/-! ### The cluster in a ball -/

/-- `E|K_x ∩ B(x,n)| = ∑_{y ∈ B(x,n)} τ(x,y)`. -/
theorem lintegral_encard_cluster_inter_ball [NeZero L]
    (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval) (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ) :
    ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞) ∂law q =
      ∑' y, (if (y - x).support.sup Nat.succ ≤ n then tau q x y else 0) := by
  have hfin : {y : ℕ →₀ (Fin d → ZMod L) | (y - x).support.sup Nat.succ ≤ n}.Finite := by
    rw [level_ball_eq_translate]
    exact (finite_level_ball n).image _
  set F := hfin.toFinset
  have hF : (F : Set (ℕ →₀ (Fin d → ZMod L))) = {y | (y - x).support.sup Nat.succ ≤ n} :=
    hfin.coe_toFinset
  rw [← hF]
  simp_rw [encard_cluster_inter_finset_eq_sum]
  rw [lintegral_finsetSum F (fun y _ => measurable_const.indicator (measurableSet_conn x y))]
  rw [tsum_eq_sum (s := F) (fun y hy => by simp [F, Set.Finite.mem_toFinset] at hy; simp [hy])]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' : (y - x).support.sup Nat.succ ≤ n := by simpa [F] using hy
  rw [lintegral_indicator_const (measurableSet_conn x y), one_mul]
  simp only [hy', ↓reduceIte, tau]

/-- **Ball sums, conditional on two-sided bounds for `τ`.** If
`a L^{-h(y-x)(d-α)} ≤ τ(x,y) ≤ A L^{-h(y-x)(d-α)}` for `x ≠ y`, then for every `n ≥ 1`,
`(a/2) L^{αn} ≤ E|K_x ∩ B(x,n)| ≤ (1 + A L^α / (L^α - 1)) L^{αn}`. -/
theorem lintegral_encard_cluster_inter_ball_bounds (hL : 2 ≤ L) (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval)
    (hlow : ∀ x y, x ≠ y → ENNReal.ofReal
      (a * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) ≤ tau q x y)
    (hup : ∀ x y, x ≠ y → tau q x y ≤ ENNReal.ofReal
      (A * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))))
    (x : ℕ →₀ (Fin d → ZMod L)) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (a / 2 * (L : ℝ) ^ (α * n)) ≤
        ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞) ∂law q ∧
      ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞) ∂law q ≤
        ENNReal.ofReal ((1 + A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) * (L : ℝ) ^ (α * n)) := by
  have : NeZero L := ⟨by omega⟩
  rw [lintegral_encard_cluster_inter_ball]
  exact ⟨le_tsum_levelBall hL hd ha (tau q) hlow x hn,
    tsum_levelBall_le hL hα hA (tau q) (fun x => (tau_self q x).le) hup x n⟩

/-- **Ball sums, conditional on two-sided bounds for the connection probability inside the smallest
common ball.** Write `P(x,y)` for the probability that `x` and `y` are joined by an open path inside
`B(x, h(y-x))`. If `a L^{-h(y-x)(d-α)} ≤ P(x,y) ≤ A L^{-h(y-x)(d-α)}` for `x ≠ y`, then for every
`n ≥ 1` the expected number `∑_{y ∈ B(x,n)} P(x,y)` lies between `(a/2) L^{αn}` and
`(1 + A L^α / (L^α - 1)) L^{αn}`, and `(a/2) L^{αn} ≤ E|K_x ∩ B(x,n)|`. -/
theorem localConn_ball_bounds (hL : 2 ≤ L) (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval)
    (hlow : ∀ x y, x ≠ y → ENNReal.ofReal
      (a * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) ≤
        law q {ω | ((openGraph ω).induce
          {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
            ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩})
    (hup : ∀ x y, x ≠ y → law q {ω | ((openGraph ω).induce
          {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
            ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} ≤ ENNReal.ofReal
      (A * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))))
    (x : ℕ →₀ (Fin d → ZMod L)) {n : ℕ} (hn : 1 ≤ n) :
    (ENNReal.ofReal (a / 2 * (L : ℝ) ^ (α * n)) ≤
        ∑' y, (if (y - x).support.sup Nat.succ ≤ n then law q {ω | ((openGraph ω).induce
          {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
            ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} else 0) ∧
      ∑' y, (if (y - x).support.sup Nat.succ ≤ n then law q {ω | ((openGraph ω).induce
          {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
            ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} else 0) ≤
        ENNReal.ofReal ((1 + A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) * (L : ℝ) ^ (α * n))) ∧
      ENNReal.ofReal (a / 2 * (L : ℝ) ^ (α * n)) ≤
        ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞) ∂law q := by
  have : NeZero L := ⟨by omega⟩
  set P : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun x y =>
    law q {ω | ((openGraph ω).induce
      {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
        ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} with hP
  have hPτ : ∀ x y, P x y ≤ tau q x y := fun x y =>
    measure_mono fun ω hω => conn_of_localConn ω _ _ _ hω
  have hPd : ∀ x, P x x ≤ 1 := fun x => (hPτ x x).trans (tau_self q x).le
  have hlowP := le_tsum_levelBall hL hd ha P hlow x hn
  refine ⟨⟨hlowP, tsum_levelBall_le hL hα hA P hPd hup x n⟩, ?_⟩
  rw [lintegral_encard_cluster_inter_ball]
  exact hlowP.trans (ENNReal.tsum_le_tsum fun y => by
    split_ifs
    · exact hPτ x y
    · exact le_rfl)

/-! ### Non-vacuity -/

/-- Non-vacuity: `f x y = L^{-h(y-x)(d-α)}` satisfies both bounds with `a = A = 1` and `f x x = 1`
(here `L = 2`, `d = 1`, `α = 1/2`), so item 1 applies. -/
example (x : ℕ →₀ (Fin 1 → ZMod 2)) (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (1 / 2 * (2 : ℝ) ^ ((1 / 2 : ℝ) * n)) ≤
        ∑' y : ℕ →₀ (Fin 1 → ZMod 2), (if (y - x).support.sup Nat.succ ≤ n then
          ENNReal.ofReal ((2 : ℝ) ^
            (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((1 : ℝ) - 1 / 2))) else 0) ∧
      ∑' y : ℕ →₀ (Fin 1 → ZMod 2), (if (y - x).support.sup Nat.succ ≤ n then
          ENNReal.ofReal ((2 : ℝ) ^
            (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((1 : ℝ) - 1 / 2))) else 0) ≤
        ENNReal.ofReal ((1 + 1 * (2 : ℝ) ^ (1 / 2 : ℝ) / ((2 : ℝ) ^ (1 / 2 : ℝ) - 1)) *
          (2 : ℝ) ^ ((1 / 2 : ℝ) * n)) := by
  let f : (ℕ →₀ (Fin 1 → ZMod 2)) → (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal ((2 : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((1 : ℝ) - 1 / 2)))
  have hf : ∀ x y, x ≠ y → f x y = ENNReal.ofReal (1 * ((2 : ℕ) : ℝ) ^
      (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1 / 2))) := by
    intro x y _; simp [f]
  have hdiag : ∀ x, f x x ≤ 1 := fun x => by simp [f]
  constructor
  · have := le_tsum_levelBall (d := 1) (L := 2) le_rfl le_rfl (α := 1 / 2) zero_le_one f
      (fun x y h => (hf x y h).ge) x hn
    simpa [f] using this
  · have := tsum_levelBall_le (d := 1) (L := 2) le_rfl (by norm_num : (0 : ℝ) < 1 / 2) zero_le_one f
      hdiag (fun x y h => (hf x y h).le) x n
    simpa [f] using this

end PercLib.Models
