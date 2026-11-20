/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs for issue 601 (Q-173, F-1 leaves R11 and R12, conditional form), written on
2026-11-16 by PROVER-G: the upper two-point bound on the hierarchical lattice from bounds
on the block means. From the first-exit inequality and the hierarchical symmetries of this
library and pinned mathlib's ENNReal powers and geometric series. No upstream code is
copied, no definition is added and no Input is introduced; the block-mean bound is an
ordinary hypothesis.
-/
module

public import PercLib.Models.HierarchicalSymmetry
public import PercLib.Percolation.Bond.BoundaryContraction
public import PercLib.Percolation.Bond.LocalConnectivity

/-! # The upper two-point bound on the hierarchical lattice from block means (R11, R12)

`V = ℕ →₀ (Fin d → ZMod L)`, `h z = z.support.sup Nat.succ`, `B_n = {z | h z ≤ n}`. The pair
intensity is radial, `J s(x,y) = f (h (y - x))`, and `q = intensityProfile J β`. Write
`τ_n(x,y)` for the probability that `x` and `y` are joined inside `B_n` (in the spelling of
`law_reach_le_firstExit`) and `μ_n = ∑' z, τ_n(0,z)` (the terms vanish off `B_n`).

* `tsum_localConn_ball_eq` (translation): `∑' y, τ_n(x,y) = μ_n` for `x ∈ B_n`.
* `law_localConn_ball_succ_le` (R11): if `f j ≤ K j` with `K` antitone, then for `x ∈ B_m`,
  `τ_{m+1}(0,x) ≤ τ_m(0,x) + β K(m+1) μ_m μ_{m+1}`. The power-law form is
  `law_localConn_ball_succ_le_powerLaw`, with `K j = C₀ L^{-(d+α) j}`.
* `tau_le_localConn_ball_add` (R12, general): if `μ_m ≤ g m` for all `m`, then for
  `x ∈ B_n`, `τ(0,x) ≤ τ_n(0,x) + β ∑'_k K(n+k+1) g(n+k) g(n+k+1)`.
* `tau_le_localConn_ball_add_powerLaw` (R12): with `μ_m ≤ A L^{αm}`,
  `τ(0,x) ≤ τ_n(0,x) + D L^{-(d-α) n}`, `D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹`.
* `tsum_tau_ball_le_powerLaw` (summed form): `∑_{x ∈ B_N} τ(0,x) ≤ ∑_{x ∈ B_N} τ_N(0,x) + D L^{αN}`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Classical
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- Balls are balls around each of their points. -/
theorem level_le_iff_level_sub_le {A : Type*} [AddCommGroup A] {x y : ℕ →₀ A} {n : ℕ}
    (hx : x.support.sup Nat.succ ≤ n) :
    y.support.sup Nat.succ ≤ n ↔ (y - x).support.sup Nat.succ ≤ n := by
  constructor
  · intro hy
    rw [sub_eq_add_neg]
    exact (level_add_le_max y (-x)).trans (max_le hy (by rwa [Finsupp.support_neg]))
  · intro hyx
    have h := level_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le hyx hx)

variable {d L : ℕ} [NeZero L]

/-- Joining inside a domain is symmetric. -/
theorem setOf_localConn_comm {W : Type*} (D : Set W) (a b : W) :
    {ω : Config W | ∃ ha : a ∈ D, ∃ hb : b ∈ D, ((openGraph ω).induce D).Reachable ⟨a, ha⟩ ⟨b, hb⟩} =
      {ω | ∃ hb : b ∈ D, ∃ ha : a ∈ D, ((openGraph ω).induce D).Reachable ⟨b, hb⟩ ⟨a, ha⟩} := by
  ext ω
  exact ⟨fun ⟨ha, hb, r⟩ => ⟨hb, ha, r.symm⟩, fun ⟨hb, ha, r⟩ => ⟨ha, hb, r.symm⟩⟩

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
  (hshift : ∀ (g : ℕ →₀ (Fin d → ZMod L)) e, J (Sym2.map (Equiv.addRight g) e) = J e)

include hshift in
/-- **Translation.** For `x ∈ B_n`, `∑' y, τ_n(x,y) = μ_n`. -/
theorem tsum_localConn_ball_eq_of_translation (β : ℝ≥0) {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ ≤ n) :
    ∑' y, law (intensityProfile J β)
        {ω | ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ∃ hy : y ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
            ⟨x, hx'⟩ ⟨y, hy⟩} =
      ∑' z, law (intensityProfile J β)
        {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
            ⟨0, h0⟩ ⟨z, hz⟩} := by
  rw [← (Equiv.addRight x).tsum_eq]
  refine tsum_congr fun z => ?_
  have h := law_localConn_eq_of_image J (Equiv.addRight x)
    (hshift x) β
    (S := {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n})
    (T := {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n})
    (fun v => by
      simp only [mem_ofPred_eq, Equiv.addRight_symm, Equiv.coe_addRight, ← sub_eq_add_neg]
      exact level_le_iff_level_sub_le hx) 0 z
  rw [show (Equiv.addRight x) 0 = x from zero_add x] at h
  exact h

include hshift in
/-- **R11, first exit between consecutive balls.** If the kernel has a radial majorant `K` with `K` antitone, then for
`x ∈ B_m`, `τ_{m+1}(0,x) ≤ τ_m(0,x) + β K(m+1) μ_m μ_{m+1}`. -/
theorem law_localConn_ball_succ_le_of_translation (K : ℕ → ℝ≥0∞) (hK : ∀ a y, a ≠ y → (J s(a,y) : ℝ≥0∞) ≤ K ((y-a).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ ≤ m) :
    law (intensityProfile J β)
        {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ((openGraph ω).induce
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
            ⟨0, h0⟩ ⟨x, hx'⟩} ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * K (m + 1) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) := by
  set q := intensityProfile J β
  set Bm : Set (ℕ →₀ (Fin d → ZMod L)) := {z | z.support.sup Nat.succ ≤ m} with hBm
  set A : Set (ℕ →₀ (Fin d → ZMod L)) := {z | z.support.sup Nat.succ ≤ m + 1} with hA
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball m).toFinset with hS
  have hSc : (S : Set (ℕ →₀ (Fin d → ZMod L))) = Bm := Set.Finite.coe_toFinset _
  have hmemS : ∀ v, v ∈ S ↔ v.support.sup Nat.succ ≤ m := fun v => Set.Finite.mem_toFinset _
  have h0S : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ S := (hmemS 0).2 (by simp)
  have h1 := law_reach_not_localConn_le_firstExit q S A {x} h0S
  rw [hSc] at h1
  set τ : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun a => law q {ω | ∃ h0 : 0 ∈ Bm, ∃ ha : a ∈ Bm,
    ((openGraph ω).induce Bm).Reachable ⟨0, h0⟩ ⟨a, ha⟩} with hτ
  set P : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun y => law q {ω | ∃ b ∈ ({x} : Set _),
    ∃ hy : y ∈ A, ∃ hb : b ∈ A, ((openGraph ω).induce A).Reachable ⟨y, hy⟩ ⟨b, hb⟩} with hP
  -- The connection is internal to `B_m` or exits it.
  have hcover : {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ A, ∃ hx' : x ∈ A,
      ((openGraph ω).induce A).Reachable ⟨0, h0⟩ ⟨x, hx'⟩} ⊆
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ Bm, ∃ hx' : x ∈ Bm,
        ((openGraph ω).induce Bm).Reachable ⟨0, h0⟩ ⟨x, hx'⟩} ∪
      {ω | ∃ b ∈ ({x} : Set _), (∃ hu : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ A, ∃ hb : b ∈ A,
        ((openGraph ω).induce A).Reachable ⟨0, hu⟩ ⟨b, hb⟩) ∧
        ¬ ∃ hu : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ Bm, ∃ hb : b ∈ Bm,
          ((openGraph ω).induce Bm).Reachable ⟨0, hu⟩ ⟨b, hb⟩} := by
    intro ω hω
    by_cases h' : ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ Bm, ∃ hx' : x ∈ Bm,
        ((openGraph ω).induce Bm).Reachable ⟨0, h0⟩ ⟨x, hx'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨x, rfl, hω, h'⟩
  -- Bound on the exit pairs.
  have hq : ∀ a y, a ∈ S → y ∉ S →
      (unitInterval.toNNReal (q s(a, y)) : ℝ≥0∞) ≤ β * K (m + 1) := by
    intro a y ha hy
    have hlev : m + 1 ≤ (y - a).support.sup Nat.succ := by
      by_contra hlt
      rw [not_le, Nat.lt_succ_iff] at hlt
      exact hy ((hmemS y).2 ((level_le_iff_level_sub_le ((hmemS a).1 ha)).2 hlt))
    calc (unitInterval.toNNReal (q s(a, y)) : ℝ≥0∞) ≤ ((β * J s(a, y) : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β _)
      _ = β * (J s(a,y) : ℝ≥0∞) := ENNReal.coe_mul _ _
      _ ≤ β * K (m + 1) := mul_le_mul' le_rfl ((hK a y (fun e => hy (e ▸ ha))).trans (hKa hlev))
  -- The sum of the returns is `μ_{m+1}`.
  have hPsum : ∑' y, P y = ∑' z, law q {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ A,
      ∃ hz : z ∈ A, ((openGraph ω).induce A).Reachable ⟨0, h0⟩ ⟨z, hz⟩} := by
    rw [← tsum_localConn_ball_eq_of_translation J hshift β (hx.trans (Nat.le_succ m))]
    refine tsum_congr fun y => ?_
    simp only [hP, mem_singleton_iff, exists_eq_left]
    rw [setOf_localConn_comm]
  have hτsum : ∑ a ∈ S, τ a ≤ ∑' a, τ a := ENNReal.sum_le_tsum S
  calc _ ≤ τ x + law q {ω | ∃ b ∈ ({x} : Set _),
        (∃ hu : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ A, ∃ hb : b ∈ A,
          ((openGraph ω).induce A).Reachable ⟨0, hu⟩ ⟨b, hb⟩) ∧
        ¬ ∃ hu : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ Bm, ∃ hb : b ∈ Bm,
          ((openGraph ω).induce Bm).Reachable ⟨0, hu⟩ ⟨b, hb⟩} :=
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

include hshift in
/-- **R12, general form.** If the kernel has a radial majorant `K` with `K` antitone and `μ_m ≤ g m` for every `m`, then
for `x ∈ B_n`, `τ(0,x) ≤ τ_n(0,x) + β ∑'_k K(n+k+1) g(n+k) g(n+k+1)`. -/
theorem tau_le_localConn_ball_add_of_translation (K : ℕ → ℝ≥0∞) (hK : ∀ a y, a ≠ y → (J s(a,y) : ℝ≥0∞) ≤ K ((y-a).support.sup Nat.succ))
    (hKa : Antitone K) (β : ℝ≥0) (g : ℕ → ℝ≥0∞)
    (hg : ∀ m, ∑' z, law (intensityProfile J β)
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
          {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
          ⟨0, h0⟩ ⟨z, hz⟩} ≤ g m)
    {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    tau (intensityProfile J β) 0 x ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * ∑' k, K (n + k + 1) * g (n + k) * g (n + k + 1) := by
  set B : ℕ → Set (ℕ →₀ (Fin d → ZMod L)) := fun N => {z | z.support.sup Nat.succ ≤ N}
    with hB
  set P : ℕ → ℝ≥0∞ := fun N => law (intensityProfile J β)
    {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ B N, ∃ hx' : x ∈ B N,
      ((openGraph ω).induce (B N)).Reachable ⟨0, h0⟩ ⟨x, hx'⟩} with hP
  have hmono : Monotone B := fun a b hab z hz => le_trans hz hab
  have hPmono : Monotone P := fun a b hab => measure_mono fun ω h => exists_localConn_mono
    (hmono hab) h
  have step : ∀ M, P (n + M) ≤ P n + β * ∑ k ∈ Finset.range M,
      K (n + k + 1) * g (n + k) * g (n + k + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have h := law_localConn_ball_succ_le_of_translation J hshift K hK hKa β (n + M)
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

/-! ### Power-law kernels -/

omit [NeZero L] in
/-- The power-law profile `C₀ L^{-(d+α) j}` is antitone in `j` for `L ≥ 1` and `α ≥ -d`. -/
theorem antitone_powerLaw_level (hL : 1 ≤ L) {α : ℝ} (hα : 0 ≤ (d : ℝ) + α) (C₀ : ℝ≥0∞) :
    Antitone fun j : ℕ => C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j) := by
  intro a b hab
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) ?_)
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith

omit [NeZero L] in
/-- The exponent bookkeeping of R12. -/
theorem rpow_powerLaw_mul_eq (hL : 1 ≤ L) (α : ℝ) (n k : ℕ) :
    (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((n + k + 1 : ℕ) : ℝ)) * (L : ℝ≥0∞) ^ (α * ((n + k : ℕ) : ℝ)) *
        (L : ℝ≥0∞) ^ (α * ((n + k + 1 : ℕ) : ℝ)) =
      (L : ℝ≥0∞) ^ (-(d : ℝ)) * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * n) *
        ((L : ℝ≥0∞) ^ (-((d : ℝ) - α))) ^ k := by
  have h0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have ht : (L : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top L
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ h0 ht,
    ← ENNReal.rpow_add _ _ h0 ht, ← ENNReal.rpow_add _ _ h0 ht, ← ENNReal.rpow_add _ _ h0 ht]
  congr 1
  push_cast
  ring

include hshift in
/-- **R11, power-law form.** Under a radial power-law majorant then for `x ∈ B_m`,
`τ_{m+1}(0,x) ≤ τ_m(0,x) + β C₀ L^{-(d+α)(m+1)} μ_m μ_{m+1}`. -/
theorem law_localConn_ball_succ_le_powerLaw_of_translation (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hf : ∀ a y, a ≠ y → (J s(a,y) : ℝ≥0∞) ≤ C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((y-a).support.sup Nat.succ : ℕ))) (β : ℝ≥0) (m : ℕ)
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ m) :
    law (intensityProfile J β)
        {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ((openGraph ω).induce
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
            ⟨0, h0⟩ ⟨x, hx'⟩} ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * (C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) :=
  law_localConn_ball_succ_le_of_translation J hshift _ hf (antitone_powerLaw_level hL (by positivity) C₀) β m hx

include hshift in
/-- **R12.** Under a radial power-law majorant and `μ_m ≤ A L^{αm}` for every `m`, then for `x ∈ B_n`
(in particular `h x = n`), `τ(0,x) ≤ τ_n(0,x) + D L^{-(d-α) n}` with
`D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹`. -/
theorem tau_le_localConn_ball_add_powerLaw_of_translation (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hf : ∀ a y, a ≠ y → (J s(a,y) : ℝ≥0∞) ≤ C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((y-a).support.sup Nat.succ : ℕ))) (β : ℝ≥0)
    (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
          {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
          ⟨0, h0⟩ ⟨z, hz⟩} ≤ A * (L : ℝ≥0∞) ^ (α * m))
    {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    tau (intensityProfile J β) 0 x ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * n) := by
  refine (tau_le_localConn_ball_add_of_translation J hshift _ hf (antitone_powerLaw_level hL (by positivity) C₀)
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

include hshift in
/-- **Summed form.** Under the hypotheses of R12,
`∑_{x ∈ B_N} τ(0,x) ≤ ∑_{x ∈ B_N} τ_N(0,x) + D L^{αN}`, with the same `D`. -/
theorem tsum_tau_ball_le_powerLaw_of_translation (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hf : ∀ a y, a ≠ y → (J s(a,y) : ℝ≥0∞) ≤ C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((y-a).support.sup Nat.succ : ℕ))) (β : ℝ≥0)
    (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
          {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
          ⟨0, h0⟩ ⟨z, hz⟩} ≤ A * (L : ℝ≥0∞) ^ (α * m)) (N : ℕ) :
    ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N},
        tau (intensityProfile J β) 0 x ≤
      ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N},
          law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N},
              ∃ hx' : (x : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N}).Reachable
                ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (α * N) := by
  set D := β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹
  have hfin : Finite {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N} :=
    (finite_level_ball N).to_subtype
  refine (ENNReal.tsum_le_tsum fun x =>
    tau_le_localConn_ball_add_powerLaw_of_translation J hshift hL hα C₀ hf β A hμ x.2).trans ?_
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

variable (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (f : ℕ → ℝ≥0)
  (hJ : ∀ x y, J s(x,y) = f ((y - x).support.sup Nat.succ))

include hJ in
/-- **Translation.** For `x ∈ B_n`, `∑' y, τ_n(x,y) = μ_n`. -/
theorem tsum_localConn_ball_eq (β : ℝ≥0) {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ ≤ n) :
    ∑' y, law (intensityProfile J β)
        {ω | ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ∃ hy : y ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
            ⟨x, hx'⟩ ⟨y, hy⟩} =
      ∑' z, law (intensityProfile J β)
        {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
          ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
            ⟨0, h0⟩ ⟨z, hz⟩} :=
  tsum_localConn_ball_eq_of_translation J
    (fun g => radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) β hx

include hJ in
/-- **R11, first exit between consecutive balls.** If `f j ≤ K j` with `K` antitone, then for
`x ∈ B_m`, `τ_{m+1}(0,x) ≤ τ_m(0,x) + β K(m+1) μ_m μ_{m+1}`. -/
theorem law_localConn_ball_succ_le (K : ℕ → ℝ≥0∞) (hK : ∀ j, (f j : ℝ≥0∞) ≤ K j)
    (hKa : Antitone K) (β : ℝ≥0) (m : ℕ) {x : ℕ →₀ (Fin d → ZMod L)}
    (hx : x.support.sup Nat.succ ≤ m) :
    law (intensityProfile J β)
        {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ((openGraph ω).induce
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
            ⟨0, h0⟩ ⟨x, hx'⟩} ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * K (m + 1) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) :=
  law_localConn_ball_succ_le_of_translation J
    (fun g => radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) K (fun a y _ => by rw [hJ]; exact hK _) hKa β m hx

include hJ in
/-- **R12, general form.** If `f j ≤ K j` with `K` antitone and `μ_m ≤ g m` for every `m`, then
for `x ∈ B_n`, `τ(0,x) ≤ τ_n(0,x) + β ∑'_k K(n+k+1) g(n+k) g(n+k+1)`. -/
theorem tau_le_localConn_ball_add (K : ℕ → ℝ≥0∞) (hK : ∀ j, (f j : ℝ≥0∞) ≤ K j)
    (hKa : Antitone K) (β : ℝ≥0) (g : ℕ → ℝ≥0∞)
    (hg : ∀ m, ∑' z, law (intensityProfile J β)
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
          {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
          ⟨0, h0⟩ ⟨z, hz⟩} ≤ g m)
    {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    tau (intensityProfile J β) 0 x ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * ∑' k, K (n + k + 1) * g (n + k) * g (n + k + 1) :=
  tau_le_localConn_ball_add_of_translation J
    (fun g => radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) K (fun a y _ => by rw [hJ]; exact hK _) hKa β g hg hx

include hJ in
/-- **R11, power-law form.** If `f j ≤ C₀ L^{-(d+α) j}` then for `x ∈ B_m`,
`τ_{m+1}(0,x) ≤ τ_m(0,x) + β C₀ L^{-(d+α)(m+1)} μ_m μ_{m+1}`. -/
theorem law_localConn_ball_succ_le_powerLaw (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hf : ∀ j : ℕ, (f j : ℝ≥0∞) ≤ C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j)) (β : ℝ≥0) (m : ℕ)
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ m) :
    law (intensityProfile J β)
        {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
          ((openGraph ω).induce
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
            ⟨0, h0⟩ ⟨x, hx'⟩} ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * (C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) *
          (∑' z, law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1}).Reachable
                ⟨0, h0⟩ ⟨z, hz⟩}) :=
  law_localConn_ball_succ_le_powerLaw_of_translation J
    (fun g => radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) hL hα C₀ (fun a y _ => by rw [hJ]; exact hf _) β m hx

include hJ in
/-- **R12.** If `f j ≤ C₀ L^{-(d+α) j}` and `μ_m ≤ A L^{αm}` for every `m`, then for `x ∈ B_n`
(in particular `h x = n`), `τ(0,x) ≤ τ_n(0,x) + D L^{-(d-α) n}` with
`D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹`. -/
theorem tau_le_localConn_ball_add_powerLaw (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hf : ∀ j : ℕ, (f j : ℝ≥0∞) ≤ C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j)) (β : ℝ≥0)
    (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
          {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
          ⟨0, h0⟩ ⟨z, hz⟩} ≤ A * (L : ℝ≥0∞) ^ (α * m))
    {n : ℕ} {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    tau (intensityProfile J β) 0 x ≤
      law (intensityProfile J β)
          {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ∃ hx' : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
            ((openGraph ω).induce
              {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
              ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * n) :=
  tau_le_localConn_ball_add_powerLaw_of_translation J
    (fun g => radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) hL hα C₀ (fun a y _ => by rw [hJ]; exact hf _) β A hμ hx

include hJ in
/-- **Summed form.** Under the hypotheses of R12,
`∑_{x ∈ B_N} τ(0,x) ≤ ∑_{x ∈ B_N} τ_N(0,x) + D L^{αN}`, with the same `D`. -/
theorem tsum_tau_ball_le_powerLaw (hL : 1 ≤ L) {α : ℝ} (hα : 0 < α) (C₀ : ℝ≥0∞)
    (hf : ∀ j : ℕ, (f j : ℝ≥0∞) ≤ C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j)) (β : ℝ≥0)
    (A : ℝ≥0∞)
    (hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
      {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
          {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ∃ hz : z ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m},
        ((openGraph ω).induce {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}).Reachable
          ⟨0, h0⟩ ⟨z, hz⟩} ≤ A * (L : ℝ≥0∞) ^ (α * m)) (N : ℕ) :
    ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N},
        tau (intensityProfile J β) 0 x ≤
      ∑' x : {x : ℕ →₀ (Fin d → ZMod L) // x.support.sup Nat.succ ≤ N},
          law (intensityProfile J β)
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N},
              ∃ hx' : (x : ℕ →₀ (Fin d → ZMod L)) ∈
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ N}).Reachable
                ⟨0, h0⟩ ⟨x, hx'⟩} +
        β * C₀ * A ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ *
          (L : ℝ≥0∞) ^ (α * N) :=
  tsum_tau_ball_le_powerLaw_of_translation J
    (fun g => radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) hL hα C₀ (fun a y _ => by rw [hJ]; exact hf _) β A hμ N

/-! ### Non-vacuity (D-5): `d = 1`, `L = 2`, `f j = 4^(-j)`, `α = 1`, `β = 1/8` -/

/-- The block means are bounded by the susceptibility. -/
theorem tsum_localConn_le_chi {W : Type*} [Countable W] (q : Sym2 W → unitInterval) (D : Set W)
    (x : W) :
    ∑' z, law q {ω | ∃ hx : x ∈ D, ∃ hz : z ∈ D, ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨z, hz⟩} ≤
      chi q x := by
  rw [chi_eq_tsum_tau]
  exact ENNReal.tsum_le_tsum fun z => measure_mono fun ω ⟨hx, hz, r⟩ =>
    conn_of_localConn ω D ⟨x, hx⟩ ⟨z, hz⟩ r

/-- `4^(-j) = 2^(-(1+1) j)`. -/
theorem quarter_pow_eq_two_rpow (j : ℕ) :
    (((1 : ℝ≥0) * (1 / 4) ^ j : ℝ≥0) : ℝ≥0∞) =
      1 * ((2 : ℕ) : ℝ≥0∞) ^ (-(((1 : ℕ) : ℝ) + 1) * j) := by
  rw [one_mul, one_mul, ENNReal.rpow_mul, ENNReal.rpow_natCast, ENNReal.coe_pow]
  congr 1
  rw [show -(((1 : ℕ) : ℝ) + 1) = -(2 : ℝ) by norm_num, ENNReal.rpow_neg, ENNReal.rpow_two]
  push_cast
  norm_num

/-- For `d = 1`, `L = 2`, `α = 1/2` (so `0 < α < d`) and the radial kernel `4^(-level)` at
`β = 1/8` (where `2 β M < 1`): the kernel is at most `2^{-(1+1/2) j}` (`C₀ = 1`), the block means
are at most `χ ≤ (1 - 1/4)⁻¹ =: A ≤ A 2^{m/2}`, so every hypothesis of R12 holds, R12 bounds
`τ(0,x)` for every `x ∈ B_n`, and the constant `D = β C₀ A² L^{-d} (1 - L^{-(d-α)})⁻¹` is
finite. -/
example (n : ℕ) (x : ℕ →₀ (Fin 1 → ZMod 2)) (hx : x.support.sup Nat.succ ≤ n) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
      tau (intensityProfile J (1 / 8)) 0 x ≤
        law (intensityProfile J (1 / 8))
            {ω | ∃ h0 : (0 : ℕ →₀ (Fin 1 → ZMod 2)) ∈
                {z : ℕ →₀ (Fin 1 → ZMod 2) | z.support.sup Nat.succ ≤ n},
              ∃ hx' : x ∈ {z : ℕ →₀ (Fin 1 → ZMod 2) | z.support.sup Nat.succ ≤ n},
              ((openGraph ω).induce
                {z : ℕ →₀ (Fin 1 → ZMod 2) | z.support.sup Nat.succ ≤ n}).Reachable
                ⟨0, h0⟩ ⟨x, hx'⟩} +
          ((1 / 8 : ℝ≥0) : ℝ≥0∞) * 1 *
            (1 - ((1 / 8 : ℝ≥0) : ℝ≥0∞) * ((2 * 1 : ℝ≥0) : ℝ≥0∞))⁻¹ ^ 2 *
            ((2 : ℕ) : ℝ≥0∞) ^ (-((1 : ℕ) : ℝ)) *
            (1 - ((2 : ℕ) : ℝ≥0∞) ^ (-(((1 : ℕ) : ℝ) - 1 / 2)))⁻¹ *
            ((2 : ℕ) : ℝ≥0∞) ^ (-(((1 : ℕ) : ℝ) - 1 / 2) * n) ∧
      ((1 / 8 : ℝ≥0) : ℝ≥0∞) * 1 *
            (1 - ((1 / 8 : ℝ≥0) : ℝ≥0∞) * ((2 * 1 : ℝ≥0) : ℝ≥0∞))⁻¹ ^ 2 *
            ((2 : ℕ) : ℝ≥0∞) ^ (-((1 : ℕ) : ℝ)) *
            (1 - ((2 : ℕ) : ℝ≥0∞) ^ (-(((1 : ℕ) : ℝ) - 1 / 2)))⁻¹ ≠ ⊤ := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  have hr : ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4) * 2 ≤ 1 := by norm_num
  have hβ : ((1 / 8 : ℝ≥0) : ℝ≥0∞) * ((2 * 1 : ℝ≥0) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    norm_num
  have hf : ∀ j : ℕ, (((1 : ℝ≥0) * (1 / 4) ^ j : ℝ≥0) : ℝ≥0∞) ≤
      1 * ((2 : ℕ) : ℝ≥0∞) ^ (-(((1 : ℕ) : ℝ) + 1 / 2) * j) := fun j => by
    rw [quarter_pow_eq_two_rpow j]
    refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    push_cast
    nlinarith
  have h2 : ((2 : ℕ) : ℝ≥0∞) ^ (-(((1 : ℕ) : ℝ) - 1 / 2)) < 1 :=
    ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine ⟨J, tau_le_localConn_ball_add_powerLaw J (fun j => 1 * (1 / 4) ^ j) hJ
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) 1 hf (1 / 8) _ (fun m => ?_) hx, ?_⟩
  · refine (tsum_localConn_le_chi _ _ 0).trans ((chi_intensity_le_hierarchical J 1 (1 / 4) hJ hr
      (1 / 8) hβ 0).trans (le_mul_of_one_le_right' ?_))
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · exact ENNReal.one_le_rpow (by norm_num) (by positivity)
  · have hA := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hβ).ne'
    have hD := ENNReal.inv_ne_top.2 (tsub_pos_of_lt h2).ne'
    have hL : ((2 : ℕ) : ℝ≥0∞) ^ (-((1 : ℕ) : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg' (by norm_num) (ENNReal.natCast_ne_top 2)
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ENNReal.coe_ne_top ENNReal.one_ne_top) (ENNReal.pow_ne_top hA)) hL) hD

end PercLib.Models
