/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The constant mode of the triangle diagram on a finite transitive graph, and the exact triangle
on the complete graph. New for this project; no upstream proof is copied. Mathematical
reference: M. Heydenreich and R. van der Hofstad, *Progress in High-Dimensional Percolation and
Random Graphs* (Springer, 2017), the finite triangle condition.
-/
module

public import PercLib.Percolation.Bond.ConnectionKernel
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The finite triangle and its constant mode

On a finite vertex type `V` with `N = |V|`, write `T(x,y) = τ(x,y)` (as a real number),
`χ = ∑_y T(x,y)` and `Δ(x,y) = ∑_{u,v} T(x,u) T(u,v) T(v,y)` (the triangle diagram, the
`(x,y)` entry of `T³`). Matrix powers are written out as finite sums; no new definition is
introduced.

## Main results

* `two_mul_triangle_toReal_le`: for any finite measure on bond configurations,
  `2 Δ(x,y) ≤ Δ(x,x) + Δ(y,y)`, from positive semidefiniteness of the connection kernel.
* `sum_triangle_eq_toReal_chi_pow_three`: under a transitive law, `∑_y Δ(x,y) = χ³`.
* `triangle_le_triangle_self` and `toReal_chi_pow_three_div_card_le_triangle_self`: under a
  transitive law, `Δ(x,y) ≤ Δ(x,x)` and `χ³ / N ≤ Δ(x,x)`.
* `toReal_chi_pow_three_sub_one_div_card_le_of_triangle_le`: a bound
  `Δ(x,y) ≤ 1_{x=y} + a₀` for all `y` forces `a₀ ≥ (χ³ - 1) / N`.
* `triangle_const_eq`, `triangle_const_le` and `triangle_const_le_of_chi_eq`: on the complete
  graph (constant bond probability `p`), with `a = (χ - 1)/(N - 1)`,
  `Δ(x,y) = (1-a)³ 1_{x=y} + (χ³ - (1-a)³)/N ≤ 1_{x=y} + χ³/N`, and `χ = λ N^{1/3}` gives
  `Δ(x,y) ≤ 1_{x=y} + λ³`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Fintype V]

/-! ### Positive semidefiniteness and the diagonal -/

/-- For any finite measure on bond configurations of a finite vertex type, the triangle
diagram satisfies `2 Δ(x,y) ≤ Δ(x,x) + Δ(y,y)`. -/
theorem two_mul_triangle_toReal_le (μ : Measure (Config V)) [IsFiniteMeasure μ] (x y : V) :
    2 * ∑ u, ∑ v, (connProb μ x u).toReal * (connProb μ u v).toReal *
        (connProb μ v y).toReal ≤
      ∑ u, ∑ v, (connProb μ x u).toReal * (connProb μ u v).toReal *
          (connProb μ v x).toReal +
        ∑ u, ∑ v, (connProb μ y u).toReal * (connProb μ u v).toReal *
          (connProb μ v y).toReal := by
  have h := sum_mul_connProb_nonneg μ (id : V → V)
    (fun u => (connProb μ u x).toReal - (connProb μ u y).toReal)
  simp only [id] at h
  set T : V → V → ℝ := fun a b => (connProb μ a b).toReal with hT
  have hsymm : ∀ a b, T a b = T b a := fun a b => by simp only [hT, connProb_comm]
  have hyx : ∑ u, ∑ v, T y u * T u v * T v x = ∑ u, ∑ v, T x u * T u v * T v y := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    rw [hsymm y v, hsymm u x, hsymm v u]
    ring
  have hexp : ∑ u, ∑ v, (T u x - T u y) * (T v x - T v y) * T u v =
      ∑ u, ∑ v, T x u * T u v * T v x - ∑ u, ∑ v, T x u * T u v * T v y
        - ∑ u, ∑ v, T y u * T u v * T v x + ∑ u, ∑ v, T y u * T u v * T v y := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    rw [hsymm u x, hsymm u y]
    ring
  change 0 ≤ ∑ u, ∑ v, (T u x - T u y) * (T v x - T v y) * T u v at h
  linarith

/-! ### Transitive laws -/

variable (q : Sym2 V → unitInterval)

/-- On a finite vertex type, `χ(x) = ∑_y τ(x,y)` as real numbers. -/
theorem toReal_chi_eq_sum (x : V) : (chi q x).toReal = ∑ y, (tau q x y).toReal := by
  rw [chi_eq_tsum_tau, tsum_fintype, ENNReal.toReal_sum fun y _ =>
    (show tau q x y ≠ ⊤ from connProb_ne_top (law q) x y)]

/-- The triangle diagram is invariant under a law-preserving vertex bijection. -/
theorem triangle_apply_eq_of_map_law_eq (σ : V ≃ V)
    (h : (law q).map (fun ω => Sym2.map σ '' ω) = law q) (x y : V) :
    ∑ u, ∑ v, (tau q (σ x) u).toReal * (tau q u v).toReal * (tau q v (σ y)).toReal =
      ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal := by
  symm
  refine Fintype.sum_equiv σ _ _ fun u => ?_
  refine Fintype.sum_equiv σ _ _ fun v => ?_
  simp only [tau_apply_eq_of_map_law_eq σ h]

variable {q}

/-- Under a transitive law, `∑_y Δ(x,y) = χ³`. -/
theorem sum_triangle_eq_toReal_chi_pow_three
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (x : V) :
    ∑ y, ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal =
      (chi q x).toReal ^ 3 := by
  set χ := (chi q x).toReal
  have hrow : ∀ v, ∑ y, (tau q v y).toReal = χ := fun v => by
    obtain ⟨σ, hσ, h⟩ := hT x v
    rw [← toReal_chi_eq_sum, ← hσ, chi_apply_eq_of_map_law_eq σ h]
  calc ∑ y, ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal
      = ∑ u, ∑ v, ∑ y, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ u, (tau q x u).toReal * ∑ v, (tau q u v).toReal * χ := by
        refine sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun v _ => ?_
        rw [← hrow v, Finset.mul_sum, Finset.mul_sum]
        exact sum_congr rfl fun y _ => by ring
    _ = χ ^ 3 := by
        have hin : ∀ u, ∑ v, (tau q u v).toReal * χ = χ * χ := fun u => by
          rw [← Finset.sum_mul, hrow]
        simp_rw [hin]
        rw [← Finset.sum_mul, hrow]
        ring

/-- Under a transitive law, every entry of the triangle diagram is at most the diagonal entry:
`Δ(x,y) ≤ Δ(x,x)`. -/
theorem triangle_le_triangle_self
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (x y : V) :
    ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal ≤
      ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v x).toReal := by
  have h := two_mul_triangle_toReal_le (law q) x y
  simp only [connProb_law] at h
  obtain ⟨σ, hσ, hm⟩ := hT x y
  have hd := triangle_apply_eq_of_map_law_eq q σ hm x x
  rw [hσ] at hd
  linarith

/-- Under a transitive law, `χ³ / N ≤ Δ(x,x)`. -/
theorem toReal_chi_pow_three_div_card_le_triangle_self
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (x : V) :
    (chi q x).toReal ^ 3 / Fintype.card V ≤
      ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v x).toReal := by
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x⟩)
  rw [div_le_iff₀ hN, ← sum_triangle_eq_toReal_chi_pow_three hT x]
  calc _ ≤ ∑ _y : V, ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v x).toReal :=
        sum_le_sum fun y _ => triangle_le_triangle_self hT x y
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- Under a transitive law, a bound `Δ(x,y) ≤ 1_{x=y} + a₀` for every `y` forces
`(χ³ - 1) / N ≤ a₀`. -/
theorem toReal_chi_pow_three_sub_one_div_card_le_of_triangle_le [DecidableEq V]
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q)
    (x : V) {a₀ : ℝ}
    (hb : ∀ y, ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal ≤
      (if x = y then 1 else 0) + a₀) :
    ((chi q x).toReal ^ 3 - 1) / Fintype.card V ≤ a₀ := by
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x⟩)
  have h := sum_le_sum fun y (_ : y ∈ univ) => hb y
  rw [sum_triangle_eq_toReal_chi_pow_three hT x, Finset.sum_add_distrib,
    Finset.sum_ite_eq_of_mem _ _ _ (mem_univ x), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  rw [div_le_iff₀ hN]
  linarith

/-! ### The complete graph -/

/-- A sum of products of two affine functions of indicators. -/
theorem sum_mul_ite_add [DecidableEq V] (α β γ ε : ℝ) (u y : V) :
    ∑ v, (α * (if u = v then 1 else 0) + β) * (γ * (if v = y then 1 else 0) + ε) =
      α * γ * (if u = y then 1 else 0) + α * ε + β * γ + Fintype.card V * β * ε := by
  have : ∀ v, (α * (if u = v then 1 else 0) + β) * (γ * (if v = y then 1 else 0) + ε) =
      (if u = v then α * γ * (if v = y then 1 else 0) + α * ε else 0) +
        (β * γ * (if v = y then 1 else 0) + β * ε) := fun v => by
    split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq_of_mem _ _ _ (mem_univ u), Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_ite_eq_of_mem' _ _ _ (mem_univ y), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

variable (p : unitInterval)

omit [Fintype V] in
/-- On the complete graph every vertex bijection preserves the law. -/
theorem law_const_map_image (σ : V ≃ V) :
    (law (fun _ : Sym2 V => p)).map (fun ω => Sym2.map σ '' ω) = law fun _ => p :=
  law_map_image_of_invariant σ fun _ => rfl

omit [Fintype V] in
/-- On the complete graph all off-diagonal two-point probabilities agree. -/
theorem tau_const_eq_of_ne [DecidableEq V] {x y x' y' : V} (hxy : x ≠ y) (hxy' : x' ≠ y') :
    tau (fun _ => p) x y = tau (fun _ => p) x' y' := by
  set y₁ := Equiv.swap x x' y
  have h1 : tau (fun _ => p) x y = tau (fun _ => p) x' y₁ := by
    rw [← tau_apply_eq_of_map_law_eq (Equiv.swap x x') (law_const_map_image p _) x y,
      Equiv.swap_apply_left]
  have hy₁ : x' ≠ y₁ := fun h => hxy ((Equiv.swap x x').injective
    (by rw [Equiv.swap_apply_left]; exact h))
  rw [h1, ← tau_apply_eq_of_map_law_eq (Equiv.swap y₁ y') (law_const_map_image p _) x' y₁,
    Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hy₁ hxy']

/-- On the complete graph, `τ(u,v) = (1 - a) 1_{u=v} + a` with `a = (χ - 1)/(N - 1) ∈ [0,1]`. -/
theorem exists_tau_const_eq [DecidableEq V] (x : V) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧
      (∀ u v : V, (tau (fun _ => p) u v).toReal = (1 - b) * (if u = v then 1 else 0) + b) ∧
      ((chi (fun _ => p) x).toReal - 1) / (Fintype.card V - 1) = b := by
  have hrow : ∀ b : ℝ,
      (∀ u v : V, (tau (fun _ => p) u v).toReal = (1 - b) * (if u = v then 1 else 0) + b) →
      (chi (fun _ => p) x).toReal = 1 - b + Fintype.card V * b := fun b hb => by
    rw [toReal_chi_eq_sum]
    simp_rw [hb x]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq_of_mem _ _ _ (mem_univ x),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  by_cases hN : 1 < Fintype.card V
  · obtain ⟨x₀, y₀, hne⟩ := Fintype.exists_pair_of_one_lt_card hN
    set b := (tau (fun _ => p) x₀ y₀).toReal
    have hb : ∀ u v : V, (tau (fun _ => p) u v).toReal = (1 - b) * (if u = v then 1 else 0) + b :=
      fun u v => by
        by_cases huv : u = v
        · subst huv; simp [tau_self]
        · rw [tau_const_eq_of_ne p huv hne]; simp [huv, b]
    refine ⟨b, ENNReal.toReal_nonneg, ?_, hb, ?_⟩
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using tau_le_one _ x₀ y₀)
    · have h1 : (1 : ℝ) < Fintype.card V := by exact_mod_cast hN
      rw [hrow b hb, div_eq_iff (by linarith)]
      ring
  · have hsub : Subsingleton V :=
      Fintype.card_le_one_iff_subsingleton.mp (Nat.le_of_not_lt hN)
    have hb : ∀ u v : V, (tau (fun _ => p) u v).toReal = (1 - 0) * (if u = v then 1 else 0) + 0 :=
      fun u v => by rw [Subsingleton.elim u v]; simp [tau_self]
    refine ⟨0, le_rfl, zero_le_one, hb, ?_⟩
    rw [hrow 0 hb]
    simp

/-- **Exact triangle on the complete graph.** With `a = (χ - 1)/(N - 1)`,
`Δ(x,y) = (1 - a)³ 1_{x=y} + (χ³ - (1 - a)³)/N`. -/
theorem triangle_const_eq [DecidableEq V] (x y : V) :
    ∑ u, ∑ v, (tau (fun _ => p) x u).toReal * (tau (fun _ => p) u v).toReal *
        (tau (fun _ => p) v y).toReal =
      (1 - ((chi (fun _ => p) x).toReal - 1) / (Fintype.card V - 1)) ^ 3 *
          (if x = y then 1 else 0) +
        ((chi (fun _ => p) x).toReal ^ 3 -
            (1 - ((chi (fun _ => p) x).toReal - 1) / (Fintype.card V - 1)) ^ 3) /
          Fintype.card V := by
  obtain ⟨b, -, -, hb, ha⟩ := exists_tau_const_eq p x
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x⟩)
  have hχ : (chi (fun _ => p) x).toReal = 1 - b + Fintype.card V * b := by
    rw [toReal_chi_eq_sum]
    simp_rw [hb x]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq_of_mem _ _ _ (mem_univ x),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [ha]
  simp_rw [hb]
  have hin : ∀ u, ∑ v, ((1 - b) * (if x = u then 1 else 0) + b) *
      ((1 - b) * (if u = v then 1 else 0) + b) * ((1 - b) * (if v = y then 1 else 0) + b) =
      ((1 - b) * (if x = u then 1 else 0) + b) * ((1 - b) * (1 - b) * (if u = y then 1 else 0) +
        ((1 - b) * b + b * (1 - b) + Fintype.card V * b * b)) := fun u => by
    calc _ = ((1 - b) * (if x = u then 1 else 0) + b) * ∑ v,
          ((1 - b) * (if u = v then 1 else 0) + b) * ((1 - b) * (if v = y then 1 else 0) + b) := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun v _ => by ring
      _ = _ := by rw [sum_mul_ite_add]; ring
  simp_rw [hin]
  rw [sum_mul_ite_add, hχ]
  field_simp
  ring

/-- On the complete graph, `Δ(x,y) ≤ 1_{x=y} + χ³/N`. -/
theorem triangle_const_le [DecidableEq V] (x y : V) :
    ∑ u, ∑ v, (tau (fun _ => p) x u).toReal * (tau (fun _ => p) u v).toReal *
        (tau (fun _ => p) v y).toReal ≤
      (if x = y then 1 else 0) + (chi (fun _ => p) x).toReal ^ 3 / Fintype.card V := by
  obtain ⟨b, hb0, hb1, -, ha⟩ := exists_tau_const_eq p x
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x⟩)
  rw [triangle_const_eq, ha, sub_div]
  have hc0 : 0 ≤ (1 - b) ^ 3 := pow_nonneg (by linarith) 3
  have hc1 : (1 - b) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hd : 0 ≤ (1 - b) ^ 3 / Fintype.card V := div_nonneg hc0 hN.le
  have hi0 : (0 : ℝ) ≤ if x = y then 1 else 0 := by split_ifs <;> norm_num
  have hi1 : (if x = y then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  nlinarith

/-- On the complete graph, if `χ = λ N^{1/3}` then `Δ(x,y) ≤ 1_{x=y} + λ³`. -/
theorem triangle_const_le_of_chi_eq [DecidableEq V] (x y : V) {lam : ℝ}
    (hlam : (chi (fun _ => p) x).toReal = lam * (Fintype.card V : ℝ) ^ (1 / 3 : ℝ)) :
    ∑ u, ∑ v, (tau (fun _ => p) x u).toReal * (tau (fun _ => p) u v).toReal *
        (tau (fun _ => p) v y).toReal ≤ (if x = y then 1 else 0) + lam ^ 3 := by
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x⟩)
  have h3 : ((Fintype.card V : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = Fintype.card V := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  refine (triangle_const_le p x y).trans_eq ?_
  rw [hlam, mul_pow, h3, mul_div_assoc, div_self hN.ne', mul_one]

end PercLib.Percolation.Bond
