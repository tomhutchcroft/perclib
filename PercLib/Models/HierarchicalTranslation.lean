/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-20: the upper two-point bound on the hierarchical lattice from bounds
on the block means, for kernels that are translation invariant with an antitone radial upper
envelope (not necessarily radial). Adapted from `PercLib/Models/HierarchicalTwoPointUpper.lean` of
this library (same licence), where the radial hypothesis is replaced by translation invariance plus
the envelope. No upstream code is copied, no definition is added and no Input is introduced; the
block-mean bound is an ordinary hypothesis.
-/
module

public import PercLib.Models.HierarchicalTwoPointUpper

/-! # Upper two-point bound for translation-invariant hierarchical kernels

`V = ℕ →₀ (Fin d → ZMod L)`, `h z = z.support.sup Nat.succ`, `B_n = {z | h z ≤ n}`. The pair
intensity is translation invariant, `J s(u + x, v + x) = J s(u, v)`, and has an antitone
radial upper envelope, `J s(u, v) ≤ K (h (v - u))` for `u ≠ v`. Write `τ_n(x,y)` for the
probability that `x` and `y` are joined inside `B_n` and `μ_n = ∑' z, τ_n(0,z)`.

* `tsum_localConn_ball_eq_of_translationInvariant`: `∑' y, τ_n(x,y) = μ_n` for `x ∈ B_n`.
* `law_localConn_ball_succ_le_of_translationInvariant` (R11):
  `τ_{m+1}(0,x) ≤ τ_m(0,x) + β K(m+1) μ_m μ_{m+1}` for `x ∈ B_m`.
* `tau_le_localConn_ball_add_of_translationInvariant` (R12, general).
* `tau_le_localConn_ball_add_powerLaw_of_translationInvariant` (R12): with `μ_m ≤ A L^{αm}`,
  `τ(0,x) ≤ τ_n(0,x) + D L^{-(d-α) n}`, `D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹`.
* `tsum_tau_ball_le_powerLaw_of_translationInvariant` (summed form) and
  `tsum_tau_ball_le_of_translationInvariant` (Prop 2.10 reduction):
  `∑_{x ∈ B_N} τ(0,x) ≤ A L^{αN} + D L^{αN}`.
* `powerLaw_const_ne_top`: `D < ∞` when `α < d`, `L ≥ 2` and `C₀, A < ∞`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
  (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))

omit [NeZero L] in
include hJt in
/-- A translation-invariant kernel is invariant under every translation. -/
theorem map_addRight_eq_of_translationInvariant (x : ℕ →₀ (Fin d → ZMod L)) :
    ∀ e, J (Sym2.map (Equiv.addRight x) e) = J e := by
  intro e
  induction e using Sym2.ind with
  | _ a b => rw [Sym2.map_mk]; exact hJt x a b

include hJt in
/-- **Translation.** For `x ∈ B_n`, `∑' y, τ_n(x,y) = μ_n`. -/
theorem tsum_localConn_ball_eq_of_translationInvariant (β : ℝ≥0) {n : ℕ}
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    ∑' y, law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} x y) =
      ∑' z, law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) := by
  rw [← (Equiv.addRight x).tsum_eq]
  refine tsum_congr fun z => ?_
  have h := law_localConn_eq_of_image J (Equiv.addRight x)
    (map_addRight_eq_of_translationInvariant J hJt x) β
    (S := {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n})
    (T := {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n})
    (fun v => by
      simp only [mem_ofPred_eq, Equiv.addRight_symm, Equiv.coe_addRight, ← sub_eq_add_neg]
      exact level_le_iff_level_sub_le hx) 0 z
  rw [show (Equiv.addRight x) 0 = x from zero_add x] at h
  exact h

include hJt in
/-- **R11, first exit between consecutive balls.** If `J s(u,v) ≤ K (h (v - u))` for `u ≠ v`
with `K` antitone, then for `x ∈ B_m`, `τ_{m+1}(0,x) ≤ τ_m(0,x) + β K(m+1) μ_m μ_{m+1}`. -/
theorem law_localConn_ball_succ_le_of_translationInvariant (K : ℕ → ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤ K ((v - u).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ ≤ m) :
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
  -- The connection is internal to `B_m` or exits it.
  have hcover : localConn A 0 x ⊆
      localConn Bm 0 x ∪
      {ω | ∃ b ∈ ({x} : Set _), (ω ∈ localConn A 0 b) ∧
        ¬ ω ∈ localConn Bm 0 b} := by
    intro ω hω
    by_cases h' : ω ∈ localConn Bm 0 x
    · exact Or.inl h'
    · exact Or.inr ⟨x, rfl, hω, h'⟩
  -- Bound on the exit pairs: the envelope replaces radiality.
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
  -- The sum of the returns is `μ_{m+1}`.
  have hPsum : ∑' y, P y = ∑' z, law q (localConn A 0 z) := by
    rw [← tsum_localConn_ball_eq_of_translationInvariant J hJt β (hx.trans (Nat.le_succ m))]
    refine tsum_congr fun y => ?_
    simp only [hP, mem_singleton_iff, exists_eq_left, ofPred_mem_eq]
    rw [localConn_comm]
  have hτsum : ∑ a ∈ S, τ a ≤ ∑' a, τ a := ENNReal.sum_le_tsum S
  calc _ ≤ τ x + law q {ω | ∃ b ∈ ({x} : Set _),
        (ω ∈ localConn A 0 b) ∧
        ¬ ω ∈ localConn Bm 0 b} :=
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

include hJt in
/-- **R12, general form.** If `J s(u,v) ≤ K (h (v - u))` for `u ≠ v` with `K` antitone and
`μ_m ≤ g m` for every `m`, then for `x ∈ B_n`,
`τ(0,x) ≤ τ_n(0,x) + β ∑'_k K(n+k+1) g(n+k) g(n+k+1)`. -/
theorem tau_le_localConn_ball_add_of_translationInvariant (K : ℕ → ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤ K ((v - u).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (g : ℕ → ℝ≥0∞)
    (hg : ∀ m, ∑' z, law (intensityProfile J β)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤ g m)
    {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    tau (intensityProfile J β) 0 x ≤
      law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) +
        β * ∑' k, K (n + k + 1) * g (n + k) * g (n + k + 1) := by
  set B : ℕ → Set (ℕ →₀ (Fin d → ZMod L)) := fun N => {z | z.support.sup Nat.succ ≤ N}
    with hB
  set P : ℕ → ℝ≥0∞ := fun N => law (intensityProfile J β)
    (localConn (B N) 0 x) with hP
  have hmono : Monotone B := fun a b hab z hz => le_trans hz hab
  have hPmono : Monotone P := fun a b hab => measure_mono fun ω h => localConn_mono_set
    (hmono hab) _ _ h
  have step : ∀ M, P (n + M) ≤ P n + β * ∑ k ∈ Finset.range M,
      K (n + k + 1) * g (n + k) * g (n + k + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have h := law_localConn_ball_succ_le_of_translationInvariant J hJt K hK hKa β (n + M)
        (hx.trans (Nat.le_add_right n M))
      calc P (n + (M + 1)) ≤ P (n + M) + β * K (n + M + 1) * g (n + M) * g (n + M + 1) :=
            h.trans (add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl (hg _)) (hg _)))
        _ ≤ P n + β * ∑ k ∈ Finset.range M, K (n + k + 1) * g (n + k) * g (n + k + 1) +
            β * K (n + M + 1) * g (n + M) * g (n + M + 1) := add_le_add ih le_rfl
        _ = _ := by rw [Finset.sum_range_succ, mul_add, add_assoc]; ring
  rw [tau_eq_iSup_localConn _ hmono (fun v => ⟨_, le_refl (v.support.sup Nat.succ)⟩)]
  refine iSup_le fun N => ?_
  calc P N ≤ P (n + N) := hPmono (Nat.le_add_left N n)
    _ ≤ _ := (step N).trans (add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)))

/-! ### Power-law envelopes -/

omit [NeZero L] in
/-- **`D < ∞`.** For `L ≥ 2`, `α < d` and finite `C₀, A`, the constant
`D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹` is finite. -/
theorem powerLaw_const_ne_top (hL : 2 ≤ L) {α : ℝ} (hαd : α < d) (β : ℝ≥0) {C₀ A : ℝ≥0∞}
    (hC₀ : C₀ ≠ ⊤) (hA : A ≠ ⊤) :
    (β : ℝ≥0∞) * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) *
      (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ ≠ ⊤ := by
  have h1 : (1 : ℝ≥0∞) < L := by exact_mod_cast (show 1 < L by omega)
  have h2 : (L : ℝ≥0∞) ^ (-((d : ℝ) - α)) < 1 :=
    ENNReal.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
  have hD := ENNReal.inv_ne_top.2 (tsub_pos_of_lt h2).ne'
  have hLd : (L : ℝ≥0∞) ^ (-(d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast (show L ≠ 0 by omega))
      (ENNReal.natCast_ne_top L)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.coe_ne_top hC₀) (ENNReal.pow_ne_top hA)) hLd) hD

include hJt in
/-- **R11, power-law form.** If `J s(u,v) ≤ C₀ L^{-(d+α) h(v-u)}` for `u ≠ v`, then for
`x ∈ B_m`, `τ_{m+1}(0,x) ≤ τ_m(0,x) + β C₀ L^{-(d+α)(m+1)} μ_m μ_{m+1}`. -/
theorem law_localConn_ball_succ_le_powerLaw_of_translationInvariant (hL : 1 ≤ L) {α : ℝ}
    (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤
      C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℕ)))
    (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ m) :
    law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 x) ≤
      law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 x) +
        β * (C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) *
          (∑' z, law (intensityProfile J β)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z)) *
          (∑' z, law (intensityProfile J β)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 z)) :=
  law_localConn_ball_succ_le_of_translationInvariant J hJt
    (fun j : ℕ => C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j)) hK
    (antitone_powerLaw_level hL (by positivity) C₀) β m hx

include hJt in
/-- **R12.** If `J s(u,v) ≤ C₀ L^{-(d+α) h(v-u)}` for `u ≠ v` and `μ_m ≤ A L^{αm}` for every
`m`, then for `x ∈ B_n`, `τ(0,x) ≤ τ_n(0,x) + D L^{-(d-α) n}` with
`D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹` (finite when `α < d`, `powerLaw_const_ne_top`). -/
theorem tau_le_localConn_ball_add_powerLaw_of_translationInvariant (hL : 1 ≤ L) {α : ℝ}
    (hα : 0 < α) (_hαd : α < d) (C₀ : ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤
      C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℕ)))
    (β : ℝ≥0) (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤
        A * (L : ℝ≥0∞) ^ (α * m))
    {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    tau (intensityProfile J β) 0 x ≤
      law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * n) := by
  refine (tau_le_localConn_ball_add_of_translationInvariant J hJt
    (fun j : ℕ => C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j)) hK
    (antitone_powerLaw_level hL (by positivity) C₀)
    β (fun m => A * (L : ℝ≥0∞) ^ (α * m)) hμ hx).trans (add_le_add le_rfl (le_of_eq ?_))
  have hterm : ∀ k : ℕ, C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((n + k + 1 : ℕ) : ℝ)) *
      (A * (L : ℝ≥0∞) ^ (α * ((n + k : ℕ) : ℝ))) *
      (A * (L : ℝ≥0∞) ^ (α * ((n + k + 1 : ℕ) : ℝ))) =
      (C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * n)) *
        ((L : ℝ≥0∞) ^ (-((d : ℝ) - α))) ^ k := by
    intro k
    calc C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((n + k + 1 : ℕ) : ℝ)) *
          (A * (L : ℝ≥0∞) ^ (α * ((n + k : ℕ) : ℝ))) *
          (A * (L : ℝ≥0∞) ^ (α * ((n + k + 1 : ℕ) : ℝ)))
        = C₀ * A ^ 2 * ((L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((n + k + 1 : ℕ) : ℝ)) *
          (L : ℝ≥0∞) ^ (α * ((n + k : ℕ) : ℝ)) *
          (L : ℝ≥0∞) ^ (α * ((n + k + 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [rpow_powerLaw_mul_eq hL α n k]; ring
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  ring

include hJt in
/-- **Summed form.** Under the hypotheses of R12,
`∑_{x ∈ B_N} τ(0,x) ≤ ∑_{x ∈ B_N} τ_N(0,x) + D L^{αN}`, with the same `D`. -/
theorem tsum_tau_ball_le_powerLaw_of_translationInvariant (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α)
    (hαd : α < d) (C₀ : ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤
      C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℕ)))
    (β : ℝ≥0) (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤
        A * (L : ℝ≥0∞) ^ (α * m)) (N : ℕ) :
    ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N},
        tau (intensityProfile J β) 0 x ≤
      ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N},
          law (intensityProfile J β)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N} 0 x) +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (α * N) := by
  have hfin : Finite {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N} :=
    (finite_level_ball N).to_subtype
  refine (ENNReal.tsum_le_tsum fun x =>
    tau_le_localConn_ball_add_powerLaw_of_translationInvariant J hJt hL hα hαd C₀ hK β A hμ
      x.2).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe,
    card_ball]
  refine add_le_add le_rfl (le_of_eq ?_)
  have h0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have ht : (L : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top L
  have e : (((L ^ d) ^ N : ℕ) : ℝ≥0∞) * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * N) =
      (L : ℝ≥0∞) ^ (α * N) := by
    rw [← pow_mul, Nat.cast_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ h0 ht]
    congr 1
    push_cast
    ring
  rw [mul_comm, mul_assoc, mul_comm _ (((L ^ d) ^ N : ℕ) : ℝ≥0∞), e]

include hJt in
/-- **Prop 2.10 reduction (U1).** If `J` is translation invariant with
`J s(u,v) ≤ C₀ L^{-(d+α) h(v-u)}` for `u ≠ v`, `0 < α < d`, and `a_m(β) = μ_m ≤ A L^{αm}` for
every `m`, then `∑_{h x ≤ N} τ(0,x) ≤ A L^{αN} + β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹ L^{αN}`. -/
theorem tsum_tau_ball_le_of_translationInvariant (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α)
    (hαd : α < d) (C₀ : ℝ≥0∞)
    (hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤
      C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℕ)))
    (β : ℝ≥0) (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤
        A * (L : ℝ≥0∞) ^ (α * m)) (N : ℕ) :
    ∑' x, (if x.support.sup Nat.succ ≤ N then tau (intensityProfile J β) 0 x else 0) ≤
      A * (L : ℝ≥0∞) ^ (α * N) +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (α * N) := by
  set B : Set (ℕ →₀ (Fin d → ZMod L)) := {z | z.support.sup Nat.succ ≤ N} with hB
  have hif : ∀ F : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞,
      ∑' x, (if x.support.sup Nat.succ ≤ N then F x else 0) =
        ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N}, F x := fun F => by
    refine Eq.trans ?_ (tsum_subtype B F).symm
    refine tsum_congr fun x => ?_
    by_cases hx : x.support.sup Nat.succ ≤ N
    · rw [ite_eq_left hx, Set.indicator_of_mem (show x ∈ B from hx)]
    · rw [ite_eq_right hx, Set.indicator_of_notMem (show x ∉ B from hx)]
  rw [hif]
  refine (tsum_tau_ball_le_powerLaw_of_translationInvariant J hJt hL hα hαd C₀ hK β A hμ
    N).trans (add_le_add ?_ le_rfl)
  exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans (hμ N)

end PercLib.Models
