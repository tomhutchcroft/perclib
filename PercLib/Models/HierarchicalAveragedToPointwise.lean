/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the bond-percolation interface of this library, from its hierarchical
symmetry, geometry and ball-sum theorems and pinned mathlib's ENNReal arithmetic.
Mathematical reference: arXiv 2103.17013v1, the deduction of Corollary 1.2 from Theorem 1.1.
No source text or code is copied.
-/
module

public import PercLib.Models.HierarchicalSymmetry
public import PercLib.Models.HierarchicalBallSums

/-! # From averaged to pointwise two-point bounds on the hierarchical lattice

`V = ℕ →₀ (Fin d → ZMod L)`, `h z = z.support.sup Nat.succ`, `Λ_n = {z | h z ≤ n}`. The pair
intensity is radial, `J s(x,y) = f (h (y - x))`, and `q = intensityProfile J β`. Write
`P_n(0,x)` for the probability that `0` and `x` are joined by an open path inside `Λ_n`.

## Main results

* `law_localConn_ball_eq_of_level_eq_level`: `P_n(0,x) = P_n(0,z)` when `h x = h z = n`.
* `localConn_ball_eq_inv_card_mul_tsum_shell`: for `h x = n`, `P_n(0,x)` is the average of
  `P_n(0,·)` over the shell `{h = n}`; `localConn_ball_eq_inv_card_mul_tsum_shell_succ` is the
  form with the shell count `L^{d(m+1)} - L^{dm}`.
* `localConn_ball_and_tau_bounds_of_averaged` (averaged ⇒ pointwise): if for every `n ≥ 1`
  `a L^{-n(d-α)} ≤ L^{-dn} ∑_{h x = n} P_n(0,x)` and `L^{-dn} ∑_{h x ≤ n} τ(0,x) ≤ A L^{-n(d-α)}`,
  then for all `x y`, with `k = h (y - x)`,
  `min a 1 · L^{-k(d-α)} ≤ P(x ↔ y inside {z | h (z - x) ≤ k}) ≤ τ(x,y) ≤ max (2A) 1 · L^{-k(d-α)}`.
  The `min`/`max` with `1` are needed only on the diagonal `x = y`, where both probabilities
  are `1` and `L^{-k(d-α)} = 1`.
* `lintegral_encard_cluster_inter_ball_bounds_of_averaged`,
  `localConn_ball_bounds_of_averaged`: the ball-susceptibility bounds of
  `PercLib.Models.HierarchicalBallSums` from the averaged hypotheses alone.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- Joining inside `S` written with membership proofs as existentials. -/
theorem setOf_localConn_eq_exists {W : Type*} (S : Set W) {a b : W} (ha : a ∈ S) (hb : b ∈ S) :
    {ω : Config W | ((openGraph ω).induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩} =
      localConn S a b := by
  ext ω
  exact ⟨fun h => ⟨ha, hb, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- A sum over a subtype as a sum with an `if`. -/
theorem tsum_subtype_eq_tsum_ite {W M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (P : W → Prop) [DecidablePred P] (g : W → M) :
    ∑' z : {z // P z}, g z = ∑' z, if P z then g z else 0 :=
  (tsum_subtype {z | P z} g).trans (tsum_congr fun z => by simp [Set.indicator_apply])

variable {d L : ℕ} [NeZero L]
variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (f : ℕ → ℝ≥0)
  (hJ : ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ))

/-! ### The restricted shell average -/

include hJ in
/-- The connection probability from `0` inside `Λ_n` is the same at every point of the shell
`{h = n}`. -/
theorem law_localConn_ball_eq_of_level_eq_level (β : ℝ≥0) {n : ℕ}
    {x z : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = n)
    (hz : z.support.sup Nat.succ = n) :
    law (intensityProfile J β)
        (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 x) =
      law (intensityProfile J β)
        (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 z) := by
  have h := law_localConn_ball_eq_of_level_eq J f hJ β (x := 0) (y := x) (x' := 0) (y' := z)
    (by rw [sub_zero, sub_zero, hx, hz])
  have e1 : {c : ℕ →₀ (Fin d → ZMod L) |
      (c - 0).support.sup Nat.succ ≤ (x - 0).support.sup Nat.succ} =
      {c | c.support.sup Nat.succ ≤ n} := by
    ext c; simp [hx]
  have e2 : {c : ℕ →₀ (Fin d → ZMod L) |
      (c - 0).support.sup Nat.succ ≤ (z - 0).support.sup Nat.succ} =
      {c | c.support.sup Nat.succ ≤ n} := by
    ext c; simp [hz]
  rw [e1, e2] at h
  exact h

include hJ in
/-- **Restricted shell average.** For `h x = n`, the probability that `0` and `x` are joined
inside `Λ_n` is the average of the same probability over the shell `{h = n}`. -/
theorem localConn_ball_eq_inv_card_mul_tsum_shell (β : ℝ≥0) {n : ℕ}
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = n) :
    law (intensityProfile J β)
        (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 x) =
      (Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} : ℝ≥0∞)⁻¹ *
        ∑' z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n},
          law (intensityProfile J β)
            (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 z) := by
  have hfin : Finite {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} :=
    (finite_level_shell n).to_subtype
  have hpos : (Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} : ℝ≥0∞)
      ≠ 0 := by
    have : Nonempty {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} := ⟨⟨x, hx⟩⟩
    simp [Nat.card_pos.ne']
  have hconst := fun z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} =>
    law_localConn_ball_eq_of_level_eq_level J f hJ β z.2 hx
  simp_rw [hconst]
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe, ← mul_assoc,
    ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _), one_mul]

include hJ in
/-- **Restricted shell average, explicit count.** For `h x = m + 1`, the probability that `0`
and `x` are joined inside `Λ_{m+1}` is the average over the shell of level `m + 1`, which has
`L^{d(m+1)} - L^{dm}` points. -/
theorem localConn_ball_eq_inv_card_mul_tsum_shell_succ (β : ℝ≥0) {m : ℕ}
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = m + 1) :
    law (intensityProfile J β)
        (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ m + 1} 0 x) =
      (((L ^ d) ^ (m + 1) - (L ^ d) ^ m : ℕ) : ℝ≥0∞)⁻¹ *
        ∑' z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1},
          law (intensityProfile J β)
            (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ m + 1} 0 z) := by
  rw [← card_shell_succ]
  exact localConn_ball_eq_inv_card_mul_tsum_shell J f hJ β hx

/-! ### Averaged bounds give pointwise bounds -/

omit [NeZero L] in
/-- The shell of level `m + 1` has at least half the points of the ball of level `m + 1` when
`L^d ≥ 2`. -/
theorem pow_succ_le_two_mul_card_shell (hL : 2 ≤ L) (hd : 1 ≤ d) (m : ℕ) :
    (L ^ d) ^ (m + 1) ≤ 2 * ((L ^ d) ^ (m + 1) - (L ^ d) ^ m) := by
  have hN : 2 ≤ L ^ d := le_trans hL (Nat.le_self_pow (by omega) L)
  have h2 : 2 * (L ^ d) ^ m ≤ L ^ d * (L ^ d) ^ m := Nat.mul_le_mul_right _ hN
  rw [pow_succ']
  generalize L ^ d * (L ^ d) ^ m = Q at *
  omega

include hJ in
/-- **Averaged ⇒ pointwise.** Suppose that for every `n ≥ 1`
`a L^{-n(d-α)} ≤ L^{-dn} ∑_{h x = n} P_n(0,x)` and `L^{-dn} ∑_{h x ≤ n} τ(0,x) ≤ A L^{-n(d-α)}`.
Then for all `x y`, with `k = h (y - x)` and `P(x,y)` the probability that `x` and `y` are
joined inside `{z | h (z - x) ≤ k}`,
`min a 1 · L^{-k(d-α)} ≤ P(x,y) ≤ τ(x,y) ≤ max (2A) 1 · L^{-k(d-α)}`. -/
theorem localConn_ball_and_tau_bounds_of_averaged (hL : 2 ≤ L) (hd : 1 ≤ d) {α a A : ℝ}
    (β : ℝ≥0)
    (hlow : ∀ n : ℕ, 1 ≤ n → ENNReal.ofReal (a * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        if x.support.sup Nat.succ = n then law (intensityProfile J β)
          (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 x) else 0)
    (hup : ∀ n : ℕ, 1 ≤ n → (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        (if x.support.sup Nat.succ ≤ n then tau (intensityProfile J β) 0 x else 0) ≤
      ENNReal.ofReal (A * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))))
    (x y : ℕ →₀ (Fin d → ZMod L)) :
    ENNReal.ofReal (min a 1 *
        (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) ≤
        law (intensityProfile J β) {ω | ((openGraph ω).induce
          {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
            ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} ∧
      law (intensityProfile J β) {ω | ((openGraph ω).induce
          {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
            ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} ≤
        tau (intensityProfile J β) x y ∧
      tau (intensityProfile J β) x y ≤ ENNReal.ofReal (max (2 * A) 1 *
        (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) := by
  set q := intensityProfile J β with hq
  have hmid : law q {ω | ((openGraph ω).induce
      {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
        ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} ≤ tau q x y :=
    measure_mono fun ω hω => conn_of_localConn ω _ _ _ hω
  refine ⟨?_, hmid, ?_⟩
  all_goals
    rcases Nat.eq_zero_or_eq_succ_pred ((y - x).support.sup Nat.succ) with h0 | hm
  -- Diagonal, lower bound.
  · have hxy : x = y := (level_sub_eq_zero_iff x y).1 h0
    subst hxy
    have huniv : {ω : Config (ℕ →₀ (Fin d → ZMod L)) | ((openGraph ω).induce
        {z | (z - x).support.sup Nat.succ ≤ (x - x).support.sup Nat.succ}).Reachable
          ⟨x, by simp⟩ ⟨x, le_refl ((x - x).support.sup Nat.succ)⟩} = univ :=
      eq_univ_of_forall fun ω => SimpleGraph.Reachable.refl _
    rw [huniv, measure_univ, h0]
    apply ENNReal.ofReal_le_one.2
    simp
  -- Off the diagonal, lower bound.
  · set m := ((y - x).support.sup Nat.succ).pred
    have hz : (y - x).support.sup Nat.succ = m + 1 := hm
    -- Translate to `(0, y - x)` and to the ball `Λ_{m+1}`.
    have htr := law_localConn_ball_eq_of_level_eq J f hJ β (x := x) (y := y) (x' := 0)
      (y' := y - x) (by rw [sub_zero])
    have e1 : {c : ℕ →₀ (Fin d → ZMod L) |
        (c - 0).support.sup Nat.succ ≤ (y - x - 0).support.sup Nat.succ} =
        {c | c.support.sup Nat.succ ≤ m + 1} := by
      ext c; simp [hz]
    rw [e1] at htr
    rw [setOf_localConn_eq_exists, htr,
      localConn_ball_eq_inv_card_mul_tsum_shell_succ J f hJ β hz]
    have hh := hlow (m + 1) (by omega)
    rw [← tsum_subtype_eq_tsum_ite] at hh
    rw [hz]
    refine le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left a 1)
      (by positivity))) (hh.trans ?_)
    gcongr
    exact Nat.sub_le _ _
  -- Diagonal, upper bound.
  · have hxy : x = y := (level_sub_eq_zero_iff x y).1 h0
    subst hxy
    rw [tau_self, h0]
    apply ENNReal.one_le_ofReal.2
    simp
  -- Off the diagonal, upper bound.
  · set m := ((y - x).support.sup Nat.succ).pred
    have hz : (y - x).support.sup Nat.succ = m + 1 := hm
    have htr := tau_eq_of_level_eq J f hJ β (x := x) (y := y) (x' := 0) (y' := y - x)
      (by rw [sub_zero])
    rw [htr, tau_eq_inv_card_mul_tsum_shell J f hJ β hz, hz]
    set N : ℝ≥0∞ := (((L ^ d) ^ (m + 1) : ℕ) : ℝ≥0∞)
    set c : ℝ≥0∞ := (((L ^ d) ^ (m + 1) - (L ^ d) ^ m : ℕ) : ℝ≥0∞)
    set r : ℝ := (L : ℝ) ^ (-((m + 1 : ℕ) : ℝ) * ((d : ℝ) - α))
    have hN0 : N ≠ 0 := by simp [N, NeZero.ne L]
    have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
    have hc0 : c ≠ 0 := by
      have := pow_succ_le_two_mul_card_shell hL hd m
      have : 0 < (L ^ d) ^ (m + 1) := by positivity
      simp only [c, ne_eq, Nat.cast_eq_zero]
      omega
    have hct : c ≠ ⊤ := ENNReal.natCast_ne_top _
    have hNc : N ≤ 2 * c := by
      simp only [N, c]
      exact_mod_cast pow_succ_le_two_mul_card_shell hL hd m
    have hsum : ∑' z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1},
        tau q 0 z ≤ ∑' z : ℕ →₀ (Fin d → ZMod L),
          (if z.support.sup Nat.succ ≤ m + 1 then tau q 0 z else 0) := by
      simp only [tsum_subtype_eq_tsum_ite
        (fun z : ℕ →₀ (Fin d → ZMod L) => z.support.sup Nat.succ = m + 1)]
      refine ENNReal.tsum_le_tsum fun z => ?_
      split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | omega
    have hS := (ENNReal.inv_mul_le_iff hN0 hNt).1 (hup (m + 1) (by omega))
    calc c⁻¹ * ∑' z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1},
          tau q 0 z
        ≤ c⁻¹ * (N * ENNReal.ofReal (A * r)) := by gcongr; exact hsum.trans hS
      _ ≤ 2 * ENNReal.ofReal (A * r) := by
        rw [← mul_assoc]
        gcongr
        exact (ENNReal.inv_mul_le_iff hc0 hct).2 (mul_comm c 2 ▸ hNc)
      _ ≤ ENNReal.ofReal (max (2 * A) 1 * r) := by
        have hr : 0 ≤ r := by positivity
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)

/-! ### Ball sums from the averaged bounds -/

include hJ in
/-- **V4QQ / YWTU from the averaged bounds, cluster form.** Under the averaged hypotheses of
`localConn_ball_and_tau_bounds_of_averaged`, with `0 ≤ a` and `0 < α`, for every `n ≥ 1`,
`(min a 1 / 2) L^{αn} ≤ E|K_x ∩ B(x,n)| ≤ (1 + max (2A) 1 · L^α / (L^α - 1)) L^{αn}`. -/
theorem lintegral_encard_cluster_inter_ball_bounds_of_averaged (hL : 2 ≤ L) (hd : 1 ≤ d)
    {α a A : ℝ} (hα : 0 < α) (ha : 0 ≤ a) (β : ℝ≥0)
    (hlow : ∀ n : ℕ, 1 ≤ n → ENNReal.ofReal (a * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        if x.support.sup Nat.succ = n then law (intensityProfile J β)
          (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 x) else 0)
    (hup : ∀ n : ℕ, 1 ≤ n → (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        (if x.support.sup Nat.succ ≤ n then tau (intensityProfile J β) 0 x else 0) ≤
      ENNReal.ofReal (A * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))))
    (x : ℕ →₀ (Fin d → ZMod L)) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (min a 1 / 2 * (L : ℝ) ^ (α * n)) ≤
        ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
          ∂law (intensityProfile J β) ∧
      ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
          ∂law (intensityProfile J β) ≤
        ENNReal.ofReal ((1 + max (2 * A) 1 * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) *
          (L : ℝ) ^ (α * n)) :=
  lintegral_encard_cluster_inter_ball_bounds hL hd hα (le_min ha zero_le_one)
    (zero_le_one.trans (le_max_right _ _)) (intensityProfile J β)
    (fun x y _ => (localConn_ball_and_tau_bounds_of_averaged J f hJ hL hd β hlow hup x y).1.trans
      (localConn_ball_and_tau_bounds_of_averaged J f hJ hL hd β hlow hup x y).2.1)
    (fun x y _ => (localConn_ball_and_tau_bounds_of_averaged J f hJ hL hd β hlow hup x y).2.2)
    x hn

include hJ in
/-- **V4QQ / YWTU from the averaged bounds, local form.** Under the averaged hypotheses of
`localConn_ball_and_tau_bounds_of_averaged`, with `0 ≤ a` and `0 < α`, for every `n ≥ 1` the
expected number of `y ∈ B(x,n)` joined to `x` inside `B(x, h(y - x))` lies between
`(min a 1 / 2) L^{αn}` and `(1 + max (2A) 1 · L^α / (L^α - 1)) L^{αn}`, and
`(min a 1 / 2) L^{αn} ≤ E|K_x ∩ B(x,n)|`. -/
theorem localConn_ball_bounds_of_averaged (hL : 2 ≤ L) (hd : 1 ≤ d)
    {α a A : ℝ} (hα : 0 < α) (ha : 0 ≤ a) (β : ℝ≥0)
    (hlow : ∀ n : ℕ, 1 ≤ n → ENNReal.ofReal (a * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        if x.support.sup Nat.succ = n then law (intensityProfile J β)
          (localConn {c : ℕ →₀ (Fin d → ZMod L) | c.support.sup Nat.succ ≤ n} 0 x) else 0)
    (hup : ∀ n : ℕ, 1 ≤ n → (((L ^ d) ^ n : ℕ) : ℝ≥0∞)⁻¹ * ∑' x : ℕ →₀ (Fin d → ZMod L),
        (if x.support.sup Nat.succ ≤ n then tau (intensityProfile J β) 0 x else 0) ≤
      ENNReal.ofReal (A * (L : ℝ) ^ (-(n : ℝ) * ((d : ℝ) - α))))
    (x : ℕ →₀ (Fin d → ZMod L)) {n : ℕ} (hn : 1 ≤ n) :
    (ENNReal.ofReal (min a 1 / 2 * (L : ℝ) ^ (α * n)) ≤
        ∑' y, (if (y - x).support.sup Nat.succ ≤ n then law (intensityProfile J β)
          {ω | ((openGraph ω).induce
            {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
              ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} else 0) ∧
      ∑' y, (if (y - x).support.sup Nat.succ ≤ n then law (intensityProfile J β)
          {ω | ((openGraph ω).induce
            {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
              ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} else 0) ≤
        ENNReal.ofReal ((1 + max (2 * A) 1 * (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) *
          (L : ℝ) ^ (α * n))) ∧
      ENNReal.ofReal (min a 1 / 2 * (L : ℝ) ^ (α * n)) ≤
        ∫⁻ ω, ((cluster ω x ∩ {y | (y - x).support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
          ∂law (intensityProfile J β) :=
  localConn_ball_bounds hL hd hα (le_min ha zero_le_one)
    (zero_le_one.trans (le_max_right _ _)) (intensityProfile J β)
    (fun x y _ => (localConn_ball_and_tau_bounds_of_averaged J f hJ hL hd β hlow hup x y).1)
    (fun x y _ => (localConn_ball_and_tau_bounds_of_averaged J f hJ hL hd β hlow hup x y).2.1.trans
      (localConn_ball_and_tau_bounds_of_averaged J f hJ hL hd β hlow hup x y).2.2)
    x hn

end PercLib.Models
