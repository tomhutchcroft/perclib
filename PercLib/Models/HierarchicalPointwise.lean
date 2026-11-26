/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, from this library's sibling-block, translation and averaged
two-point theorems, and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code
is copied and no definition is added. Mathematical reference: T. Hutchcroft, *The critical
two-point function for long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1,
Lemma 2.8 and Proposition 2.10.
-/
module

public import PercLib.Models.HierarchicalSibling
public import PercLib.Models.HierarchicalTwoPointAveraged

/-!
# Pointwise sibling and outer-shell bounds for hierarchical kernels

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_m = {h ≤ m}`,
`q = intensityProfile J β`, `q_m` for `q` restricted to the pairs inside `Λ_m`,
`a_m = E_{q_m} |K_0 ∩ Λ_m|` and `τ_m(0, x) = P_{q_m}(0 ↔ x)`. The kernel `J` is translation
invariant but need not be radial. The library has the shell-summed forms of the two estimates
below (`sum_shell_tau_ge`, `law_localConn_ball_succ_le_of_translationInvariant`); here they are
proved for a single target point `x` of the outer shell `h x = m + 1`.

## Main results

* `law_localConn_ball_succ_le_add_of_translationInvariant`: the first-exit bound
  `P(0 ↔ x in Λ_{m+1}) ≤ P(0 ↔ x in Λ_m) + β K(m+1) μ_m μ_{m+1}` for every `x ∈ Λ_{m+1}`
  (`μ_m = ∑' z, P(0 ↔ z in Λ_m)`), under an antitone envelope `J(u, v) ≤ K(h(v - u))`.
* `tau_restrict_level_ball_succ_le_of_level_eq` (outer-shell upper bound): for `h x = m + 1`,
  `τ_{m+1}(0, x) ≤ β K(m+1) a_m a_{m+1}`, with no additive term.
* `ofReal_mul_sq_le_tau_of_level_eq` (pointwise sibling lower bound): under the hypotheses of
  `sum_shell_tau_ge`, for `h x = n + 1`,
  `k' β L^{-(d+α)(n+1)} a_n² ≤ τ_{n+1}(0, x)` with `k' = (c/4) e^{-T}`,
  `T = c A 99² L^{-(d+α)}`, from the sibling-pair step
  `ofReal_mul_div_two_sq_le_tau_of_level_eq_succ` (in `HierarchicalSibling`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models

open PercLib.Percolation.Bond

variable {d L : ℕ} [NeZero L]

/-! ### The outer-shell upper bound -/

/-- **First exit between consecutive balls, for any target in the larger ball.** If
`J s(u,v) ≤ K (h (v - u))` for `u ≠ v` with `K` antitone and `J` translation invariant, then for
every `x ∈ Λ_{m+1}`, `P(0 ↔ x in Λ_{m+1}) ≤ P(0 ↔ x in Λ_m) + β K(m+1) μ_m μ_{m+1}`, where
`μ_k = ∑' z, P(0 ↔ z in Λ_k)`. This extends `law_localConn_ball_succ_le_of_translationInvariant`
from `x ∈ Λ_m` to `x ∈ Λ_{m+1}`. -/
theorem law_localConn_ball_succ_le_add_of_translationInvariant
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (K : ℕ → ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤ K ((v - u).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ ≤ m + 1) :
    law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 x) ≤
      law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 x) +
        β * K (m + 1) *
          (∑' z, law (intensityProfile J β)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z)) *
          (∑' z, law (intensityProfile J β)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 z)) := by
  set q := intensityProfile J β
  set Bm : Set (ℕ →₀ (Fin d → ZMod L)) := {z | z.support.sup Nat.succ ≤ m} with hBm
  set A : Set (ℕ →₀ (Fin d → ZMod L)) := {z | z.support.sup Nat.succ ≤ m + 1} with hA
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball m).toFinset with hS
  have hSc : (S : Set (ℕ →₀ (Fin d → ZMod L))) = Bm := Set.Finite.coe_toFinset _
  have hmemS : ∀ v, v ∈ S ↔ v.support.sup Nat.succ ≤ m := fun v => Set.Finite.mem_toFinset _
  have h0S : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ S := (hmemS 0).2 (by simp)
  have h1 := law_reach_not_localConn_le_firstExit q S A {x} h0S
  rw [hSc] at h1
  set τ : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun a => law q (localConn Bm 0 a) with hτ
  set P : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun y => law q {ω | ∃ b ∈ ({x} : Set _),
    ω ∈ localConn A y b} with hP
  have hcover : localConn A 0 x ⊆
      localConn Bm 0 x ∪
      {ω | ∃ b ∈ ({x} : Set _), (ω ∈ localConn A 0 b) ∧ ¬ ω ∈ localConn Bm 0 b} := by
    intro ω hω
    by_cases h' : ω ∈ localConn Bm 0 x
    · exact Or.inl h'
    · exact Or.inr ⟨x, rfl, hω, h'⟩
  have hq : ∀ a y, a ∈ S → y ∉ S →
      (unitInterval.toNNReal (q s(a, y)) : ℝ≥0∞) ≤ β * K (m + 1) := by
    intro a y ha hy
    have hlev : m + 1 ≤ (y - a).support.sup Nat.succ := by
      by_contra hlt
      rw [not_le, Nat.lt_succ_iff] at hlt
      exact hy ((hmemS y).2 ((level_le_iff_level_sub_le ((hmemS a).1 ha)).2 hlt))
    have hay : a ≠ y := by
      rintro rfl
      exact hy ha
    calc (unitInterval.toNNReal (q s(a, y)) : ℝ≥0∞) ≤ ((β * J s(a, y) : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β _)
      _ = β * (J s(a, y) : ℝ≥0∞) := by rw [ENNReal.coe_mul]
      _ ≤ β * K (m + 1) := mul_le_mul' le_rfl ((hK a y hay).trans (hKa hlev))
  -- the returns sum to `μ_{m+1}`: this is where `x ∈ Λ_{m+1}` is used
  have hPsum : ∑' y, P y = ∑' z, law q (localConn A 0 z) := by
    rw [← tsum_localConn_ball_eq_of_translationInvariant J hJt β hx]
    refine tsum_congr fun y => ?_
    simp only [hP, mem_singleton_iff, exists_eq_left, ofPred_mem_eq]
    rw [localConn_comm]
  have hτsum : ∑ a ∈ S, τ a ≤ ∑' a, τ a := ENNReal.sum_le_tsum S
  calc _ ≤ τ x + law q {ω | ∃ b ∈ ({x} : Set _),
        (ω ∈ localConn A 0 b) ∧ ¬ ω ∈ localConn Bm 0 b} :=
        (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ τ x + ∑ a ∈ S, τ a * (β * K (m + 1)) * ∑' y, P y := by
        refine add_le_add le_rfl (h1.trans (Finset.sum_le_sum fun a ha => ?_))
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun y => ?_
        split_ifs with hy
        · exact zero_le
        · exact mul_le_mul' (mul_le_mul' le_rfl (hq a y ha hy)) le_rfl
    _ = τ x + (∑ a ∈ S, τ a) * (β * K (m + 1)) * ∑' y, P y := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ τ x + β * K (m + 1) * (∑' a, τ a) * ∑' y, P y := by
        refine add_le_add le_rfl ?_
        calc (∑ a ∈ S, τ a) * (β * K (m + 1)) * ∑' y, P y
            ≤ (∑' a, τ a) * (β * K (m + 1)) * ∑' y, P y :=
              mul_le_mul' (mul_le_mul' hτsum le_rfl) le_rfl
          _ = β * K (m + 1) * (∑' a, τ a) * ∑' y, P y := by ring
    _ = _ := by rw [hPsum]

/-- **Outer-shell first exit, connection-inside-a-ball form.** Under the hypotheses of
`law_localConn_ball_succ_le_add_of_translationInvariant`, for `h x = m + 1`,
`P(0 ↔ x in Λ_{m+1}) ≤ β K(m+1) μ_m μ_{m+1}`: the internal term vanishes since `x ∉ Λ_m`. -/
theorem law_localConn_ball_succ_le_of_level_eq
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (K : ℕ → ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤ K ((v - u).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ = m + 1) :
    law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 x) ≤
      β * K (m + 1) *
        (∑' z, law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z)) *
        (∑' z, law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 z)) := by
  have h := law_localConn_ball_succ_le_add_of_translationInvariant J hJt K hK hKa β m hx.le
  have hx0 : x ∉ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} := by
    simp only [mem_ofPred_eq, hx]; omega
  rwa [localConn_of_notMem_right hx0, measure_empty, zero_add] at h

open Classical in
/-- **Outer-shell upper bound** (pointwise form of Hutchcroft, arXiv:2103.17013v1,
Prop. 2.10, first exit). Let `J` be translation invariant with `J(u, v) ≤ K(h(v - u))` for
`u ≠ v`, `K` antitone. For every `x` with `h x = m + 1`,

`τ_{m+1}(0, x) ≤ β K(m+1) a_m a_{m+1}`,

where `τ_{m+1}` is the two-point function of `q_{m+1}` and `a_k = E_{q_k} |K_0 ∩ Λ_k|`. -/
theorem tau_restrict_level_ball_succ_le_of_level_eq
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (K : ℕ → ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤ K ((v - u).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ = m + 1) :
    tau (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ m + 1}.sym2 then intensityProfile J β e else 0) 0 x ≤
      β * K (m + 1) *
        (∫⁻ ω, (clusterIntersection (finite_level_ball m).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0)) *
        (∫⁻ ω, (clusterIntersection (finite_level_ball (m + 1)).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ m + 1}.sym2 then intensityProfile J β e else 0)) := by
  rw [tau_restrict_eq_law_localConn _ _ (by simp), ← tsum_law_localConn_level_ball_eq_lintegral,
    ← tsum_law_localConn_level_ball_eq_lintegral]
  exact law_localConn_ball_succ_le_of_level_eq J hJt K hK hKa β m hx

/-! ### The pointwise sibling lower bound -/

open Classical in
/-- **Pointwise sibling lower bound** (pointwise form of Hutchcroft, arXiv:2103.17013v1,
Lemma 2.8). Under the hypotheses of `sum_shell_tau_ge` (`L ≥ 1`, `c > 0`, `α ≥ 0`, `J`
translation invariant with `J(u, v) ≥ c L^{-(d+α) h(v-u)}` for `u ≠ v`, and
`M_n(β)² ≤ (A/β) L^{(d+α)n}` with `β > 0`), for every `x` with `h x = n + 1`,

`k' β L^{-(d+α)(n+1)} a_n(β)² ≤ τ_{n+1}(0, x)`

with `k' = (c/4) e^{-T}` and `T = c A 99² L^{-(d+α)}`, depending only on `d, L, α, c, A`.
The proof is the sibling-pair step `ofReal_mul_div_two_sq_le_tau_of_level_eq_succ` with
`r = β c L^{-(d+α)(n+1)}`; summing it over the `≥ L^{dn}` points of the shell is
`sum_shell_tau_ge`. -/
theorem ofReal_mul_sq_le_tau_of_level_eq (hL : 1 ≤ L) {α c A : ℝ} (hα : 0 ≤ α)
    (hc : 0 < c) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {β : ℝ≥0} (hβ : 0 < β) (n : ℕ)
    (hM : (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤ A / β * (L : ℝ) ^ (((d : ℝ) + α) * n))
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = n + 1) :
    ENNReal.ofReal (c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) * β *
        (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1)))) *
      (∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)) ^ 2 ≤
      tau (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n + 1}.sym2 then intensityProfile J β e else 0) 0 x := by
  set a := ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
    ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0) with ha
  set M := tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
    z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
    (finite_level_ball n).toFinset with hM_def
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hda : (0 : ℝ) ≤ (d : ℝ) + α := by positivity
  set r : ℝ := (β : ℝ) * (c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1)))) with hr_def
  set T0 : ℝ := c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)) with hT0
  have hr0 : 0 ≤ r := by positivity
  have hrt : r * ((99 * M : ℕ) : ℝ) ^ 2 ≤ T0 := by
    have hcomb : (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) *
        (L : ℝ) ^ (((d : ℝ) + α) * n) = (L : ℝ) ^ (-((d : ℝ) + α)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    calc r * ((99 * M : ℕ) : ℝ) ^ 2
        = ((β : ℝ) * c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) * 99 ^ 2) *
            (M : ℝ) ^ 2 := by rw [hr_def]; push_cast; ring
      _ ≤ ((β : ℝ) * c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) * 99 ^ 2) *
            (A / β * (L : ℝ) ^ (((d : ℝ) + α) * n)) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
      _ = c * A * 99 ^ 2 * ((L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) *
            (L : ℝ) ^ (((d : ℝ) + α) * n)) := by
          have hβ0 : (β : ℝ) ≠ 0 := by exact_mod_cast hβ.ne'
          field_simp
      _ = T0 := by rw [hcomb]
  have hrJ : ∀ u v, u.support.sup Nat.succ ≤ n → (v - x).support.sup Nat.succ ≤ n →
      r ≤ (β : ℝ) * (J s(u, v) : ℝ) := by
    intro u v hu hv
    have hu1 : u.support.sup Nat.succ ≤ n + 1 := hu.trans (Nat.le_succ n)
    have hv1 : v.support.sup Nat.succ ≤ n + 1 := by
      have h := level_add_le_max (v - x) x
      rw [sub_add_cancel] at h
      exact h.trans (max_le (hv.trans (Nat.le_succ n)) hx.le)
    have huv : u ≠ v := by
      rintro rfl
      have := level_sub_le_of_mem_level_ball hv hu
      rw [sub_sub_cancel] at this
      omega
    have hlev : (((v - u).support.sup Nat.succ : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast level_sub_le_of_mem_level_ball hu1 hv1
    have hpow : (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) ≤
        (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hpow hc.le).trans
      (hJ u v huv)) β.coe_nonneg
  have hstep := ofReal_mul_div_two_sq_le_tau_of_level_eq_succ J hJt β n hx hr0 hrJ hrt
  have ha2 : a ^ 2 = (a / 2) ^ 2 * 4 := by
    have h2 : a / 2 * 2 = a := ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    conv_lhs => rw [← h2]
    rw [mul_pow]; norm_num
  refine le_trans (le_of_eq ?_) hstep
  have hk : r * Real.exp (-T0) = 4 * (c / 4 * Real.exp (-T0) * β *
      (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1)))) := by
    rw [hr_def]; ring
  rw [hk, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num), ENNReal.ofReal_ofNat, ha2]
  ring

end PercLib.Models
