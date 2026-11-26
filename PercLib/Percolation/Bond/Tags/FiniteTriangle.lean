/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project, written on 2026-11-21. A restatement of library lemmas; no upstream
code is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.FiniteTriangle

/-!
# Correspondence wrapper for the finite triangle

Tagged restatement of the constant-mode bounds for the triangle diagram
`Δ(x,y) = ∑_{u,v} τ(x,u) τ(u,v) τ(v,y)` on a finite vertex type with `N` vertices, and of the
exact triangle on the complete graph. All mathematical inputs are proved in
`PercLib.Percolation.Bond.FiniteTriangle`.

## Main results

* `sum_triangle_eq_chi_pow_three_and_triangle_const_eq`: under a transitive law,
  `∑_y Δ(x,y) = χ³` and `Δ(x,x) ≥ χ³/N`, so a bound `Δ(x,y) ≤ 1_{x=y} + a₀` forces
  `a₀ ≥ (χ³ - 1)/N`; on the complete graph, with `a = (χ - 1)/(N - 1)`,
  `Δ(x,y) = (1-a)³ 1_{x=y} + (χ³ - (1-a)³)/N ≤ 1_{x=y} + χ³/N`, and `χ = λ N^{1/3}` gives
  `Δ(x,y) ≤ 1_{x=y} + λ³`.
-/

@[expose] public section
noncomputable section

namespace PercLib.Percolation.Bond

/-- On a finite vertex type with `N` vertices and a transitive law, with
`Δ(x,y) = ∑_{u,v} τ(x,u) τ(u,v) τ(v,y)` and `χ = χ(x)`: `∑_y Δ(x,y) = χ³` and
`Δ(x,x) ≥ χ³/N`, so a bound `Δ(y,z) ≤ 1_{y=z} + a₀` for all `y, z` requires
`a₀ ≥ (χ³ - 1)/N`. On the complete graph (every bond open with probability `p`), with
`a = (χ - 1)/(N - 1)`, `Δ(x,y) = (1-a)³ 1_{x=y} + (χ³ - (1-a)³)/N ≤ 1_{x=y} + χ³/N`; in
particular `χ = λ N^{1/3}` gives `Δ(x,y) ≤ 1_{x=y} + λ³`. -/
@[tag "R2Y7"]
theorem sum_triangle_eq_chi_pow_three_and_triangle_const_eq {V : Type*} [Fintype V]
    [DecidableEq V] :
    (∀ q : Sym2 V → unitInterval,
      (∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q) →
      ∀ x : V,
        ∑ y, ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v y).toReal =
            (chi q x).toReal ^ 3 ∧
          (chi q x).toReal ^ 3 / Fintype.card V ≤
            ∑ u, ∑ v, (tau q x u).toReal * (tau q u v).toReal * (tau q v x).toReal ∧
          ∀ a₀ : ℝ,
            (∀ y z : V,
              ∑ u, ∑ v, (tau q y u).toReal * (tau q u v).toReal * (tau q v z).toReal ≤
                (if y = z then 1 else 0) + a₀) →
            ((chi q x).toReal ^ 3 - 1) / Fintype.card V ≤ a₀) ∧
    ∀ (p : unitInterval) (x y : V),
      (∑ u, ∑ v, (tau (fun _ => p) x u).toReal * (tau (fun _ => p) u v).toReal *
            (tau (fun _ => p) v y).toReal =
          (1 - ((chi (fun _ => p) x).toReal - 1) / (Fintype.card V - 1)) ^ 3 *
              (if x = y then 1 else 0) +
            ((chi (fun _ => p) x).toReal ^ 3 -
                (1 - ((chi (fun _ => p) x).toReal - 1) / (Fintype.card V - 1)) ^ 3) /
              Fintype.card V ∧
        ∑ u, ∑ v, (tau (fun _ => p) x u).toReal * (tau (fun _ => p) u v).toReal *
            (tau (fun _ => p) v y).toReal ≤
          (if x = y then 1 else 0) + (chi (fun _ => p) x).toReal ^ 3 / Fintype.card V) ∧
      ∀ lam : ℝ, (chi (fun _ => p) x).toReal = lam * (Fintype.card V : ℝ) ^ (1 / 3 : ℝ) →
        ∑ u, ∑ v, (tau (fun _ => p) x u).toReal * (tau (fun _ => p) u v).toReal *
            (tau (fun _ => p) v y).toReal ≤ (if x = y then 1 else 0) + lam ^ 3 :=
  ⟨fun _q hT x => ⟨sum_triangle_eq_toReal_chi_pow_three hT x,
      toReal_chi_pow_three_div_card_le_triangle_self hT x,
      fun _a₀ hb => toReal_chi_pow_three_sub_one_div_card_le_of_triangle_le hT x (hb x)⟩,
    fun p x y => ⟨⟨triangle_const_eq p x y, triangle_const_le p x y⟩,
      fun _lam hlam => triangle_const_le_of_chi_eq p x y hlam⟩⟩

end PercLib.Percolation.Bond
