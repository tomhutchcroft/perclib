/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's averaged two-point theorem, its averaged-to-pointwise and
ball-sum theorems, and pinned mathlib's ENNReal arithmetic. No upstream code is copied and no
definition is added. Mathematical reference: T. Hutchcroft, *The critical two-point function for
long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1, Corollary 1.2.
-/
module

public import PercLib.Models.HierarchicalTwoPointAveraged
public import PercLib.Models.HierarchicalAveragedToPointwise
public import PercLib.Models.HierarchicalPowerKernel

/-! # Pointwise critical two-point bounds for radial hierarchical kernels

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}` and
`β_c = rootCriticalIntensity J 0`. For a radial kernel `J s(x,y) = f (h (y - x))` with
`c L^{-(d+α) h} ≤ J ≤ C L^{-(d+α) h}` off the diagonal, the averaged bounds of Theorem 1.1
(`hierarchicalTwoPointAveraged`) become pointwise bounds by the shell average: the connection
probabilities from `0`, inside `Λ_n` or in the whole lattice, are constant on the shell
`{h = n}` (level isometries preserve a radial law), and the shell has at least half the points
of `Λ_n`. The diagonal `x = y` is covered by taking the lower constant at most `1` and the
upper constant at least `1`. Positivity of `β_c` is the row-sum bound
`(L^α - 1)/(C (1 - L^{-d})) ≤ β_c`.

## Main results

* `hierarchicalTwoPointRadial`: Corollary 1.2, `HierarchicalTwoPointRadial d L α c C`.
* `exists_lintegral_encard_cluster_inter_ball_bounds_rootCriticalIntensity`: the expected size
  of the critical cluster inside the ball `B(x,n)` is between `a L^{αn}` and `A L^{αn}` for
  `n ≥ 1`, with `a, A > 0` depending only on `d, L, α, c, C`.
* `exists_localConn_ball_bounds_rootCriticalIntensity`: the same two-sided bound for the
  expected number of `y ∈ B(x,n)` joined to `x` inside the smallest ball containing `x` and `y`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- A radial kernel `J s(x,y) = f (h (y - x))` is translation invariant. -/
theorem translationInvariant_of_radial {d L : ℕ} (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (f : ℕ → ℝ≥0) (hJ : ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ))
    (x u v : ℕ →₀ (Fin d → ZMod L)) : J s(u + x, v + x) = J s(u, v) := by
  rw [hJ, hJ, add_sub_add_right_eq_sub]

/-- **Corollary 1.2 of arXiv:2103.17013v1 (pointwise critical two-point bounds for radial
kernels).** For `d ≥ 1`, `L ≥ 2`, `0 < α < d` and `0 < c ≤ C` there are `a, A > 0`, depending
only on `d, L, α, c, C`, such that every radial kernel with
`c L^{-(d+α) h(v-u)} ≤ J(u,v) ≤ C L^{-(d+α) h(v-u)}` off the diagonal has `0 < β_c < ∞` and,
for all `x, y`,
`a L^{-h(y-x)(d-α)} ≤ P_{β_c}(x ↔ y inside Λ(x,y)) ≤ τ_{β_c}(x,y) ≤ A L^{-h(y-x)(d-α)}`. -/
@[tag "W498"]
theorem hierarchicalTwoPointRadial (d L : ℕ) (α c C : ℝ) :
    HierarchicalTwoPointRadial d L α c C := by
  intro hd hL hα hαd hc hcC
  have : NeZero L := ⟨by omega⟩
  obtain ⟨a, A, ha, hA, H⟩ := hierarchicalTwoPointAveraged d L α c C hd hL hα hαd hc
  refine ⟨min a 1, max (2 * A) 1, lt_min ha one_pos, lt_max_of_lt_right one_pos,
    fun J ⟨f, hf⟩ hJl hJu => ?_⟩
  intro q
  obtain ⟨htop, hn⟩ := H J (translationInvariant_of_radial J f hf) hJl hJu
  have hC : 0 < C := hc.trans_le hcC
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hpos : 0 < rootCriticalIntensity J 0 := by
    have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
    have hLd : 0 < 1 - (L : ℝ) ^ (-(d : ℝ)) :=
      sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg hL1
        (neg_lt_zero.2 (by exact_mod_cast (show 0 < d by omega))))
    refine lt_of_lt_of_le ?_ (ofReal_le_rootCriticalIntensity_of_powerLaw hL hα J hJu 0)
    exact ENNReal.ofReal_pos.2 (by positivity)
  have hcard : ∀ n : ℕ, (((L ^ d) ^ n : ℕ) : ℝ≥0∞) = (L : ℝ≥0∞) ^ (d * n) := by
    intro n; push_cast; rw [pow_mul]
  have hexp : ∀ n : ℕ, -((d : ℝ) - α) * n = -(n : ℝ) * ((d : ℝ) - α) := fun n => by ring
  have hlow : ∀ n : ℕ, 1 ≤ n → ENNReal.ofReal (a * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        if x.support.sup Nat.succ = n then law q
          (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 x) else 0 := by
    intro n hn1
    rw [hcard, ← hexp]
    exact (hn n hn1).1
  have hup : ∀ n : ℕ, 1 ≤ n → (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        (if x.support.sup Nat.succ ≤ n then tau q 0 x else 0) ≤
      ENNReal.ofReal (A * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))) := by
    intro n hn1
    rw [hcard, ← hexp]
    exact (hn n hn1).2.2
  exact ⟨hpos, htop, localConn_ball_and_tau_bounds_of_averaged J f hf hL hd _ hlow hup⟩

/-- **Ball susceptibility of the critical cluster (wiki V4QQ).** For `d ≥ 1`, `L ≥ 2`,
`0 < α < d` and `0 < c ≤ C` there are `a, A > 0`, depending only on `d, L, α, c, C`, such that
for every radial kernel with `c L^{-(d+α) h} ≤ J ≤ C L^{-(d+α) h}` off the diagonal, every
vertex `x` and every `n ≥ 1`,
`a L^{αn} ≤ E_{β_c}|K_x ∩ B(x,n)| ≤ A L^{αn}`, where `B(x,n) = {y | h(y - x) ≤ n}`. -/
theorem exists_lintegral_encard_cluster_inter_ball_bounds_rootCriticalIntensity {d L : ℕ}
    {α c C : ℝ} (hd : 1 ≤ d) (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    (hcC : c ≤ C) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
        (∃ f : ℕ → ℝ≥0, ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) →
        (∀ u v, u ≠ v →
          c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
            (J s(u, v) : ℝ)) →
        (∀ u v, u ≠ v →
          (J s(u, v) : ℝ) ≤
            C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
        ∀ (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ), 1 ≤ n →
          ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) ≤
              ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
                ∂law (intensityProfile J (rootCriticalIntensity J 0).toNNReal) ∧
            ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
                ∂law (intensityProfile J (rootCriticalIntensity J 0).toNNReal) ≤
              ENNReal.ofReal (A * (L : ℝ) ^ (α * n)) := by
  obtain ⟨a, A, ha, hA, H⟩ := hierarchicalTwoPointRadial d L α c C hd hL hα hαd hc hcC
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
  have hρ : 0 < (L : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
  refine ⟨a / 2, 1 + A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1), by positivity, by positivity,
    fun J hf hJl hJu x n hn => ?_⟩
  obtain ⟨-, -, hP⟩ := H J hf hJl hJu
  exact lintegral_encard_cluster_inter_ball_bounds hL hd hα ha.le hA.le _
    (fun x y _ => (hP x y).1.trans (hP x y).2.1) (fun x y _ => (hP x y).2.2) x hn

/-- **Ball sums of internal connections at criticality (wiki YWTU).** For `d ≥ 1`, `L ≥ 2`,
`0 < α < d` and `0 < c ≤ C` there are `a, A > 0`, depending only on `d, L, α, c, C`, such that
for every radial kernel with `c L^{-(d+α) h} ≤ J ≤ C L^{-(d+α) h}` off the diagonal, every
vertex `x` and every `n ≥ 1`, the expected number of `y ∈ B(x,n)` joined to `x` at `β_c` inside
the smallest ball `B(x, h(y - x))` containing both lies between `a L^{αn}` and `A L^{αn}`, and
`a L^{αn} ≤ E_{β_c}|K_x ∩ B(x,n)|`. -/
theorem exists_localConn_ball_bounds_rootCriticalIntensity {d L : ℕ} {α c C : ℝ}
    (hd : 1 ≤ d) (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c) (hcC : c ≤ C) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
        (∃ f : ℕ → ℝ≥0, ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) →
        (∀ u v, u ≠ v →
          c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
            (J s(u, v) : ℝ)) →
        (∀ u v, u ≠ v →
          (J s(u, v) : ℝ) ≤
            C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
        ∀ (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ), 1 ≤ n →
          (ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) ≤
              ∑' y, (if (y - x).support.sup Nat.succ ≤ n then
                law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
                  {ω | ((openGraph ω).induce
                    {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
                      ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} else 0) ∧
            ∑' y, (if (y - x).support.sup Nat.succ ≤ n then
                law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
                  {ω | ((openGraph ω).induce
                    {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
                      ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} else 0) ≤
              ENNReal.ofReal (A * (L : ℝ) ^ (α * n))) ∧
          ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) ≤
            ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
              ∂law (intensityProfile J (rootCriticalIntensity J 0).toNNReal) := by
  obtain ⟨a, A, ha, hA, H⟩ := hierarchicalTwoPointRadial d L α c C hd hL hα hαd hc hcC
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
  have hρ : 0 < (L : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
  refine ⟨a / 2, 1 + A * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1), by positivity, by positivity,
    fun J hf hJl hJu x n hn => ?_⟩
  obtain ⟨-, -, hP⟩ := H J hf hJl hJu
  exact localConn_ball_bounds hL hd hα ha.le hA.le _
    (fun x y _ => (hP x y).1) (fun x y _ => (hP x y).2.1.trans (hP x y).2.2) x hn

end PercLib.Models
