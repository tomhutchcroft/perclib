/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's hierarchical triangle-sum theorems. No upstream code is
copied and no definition is added. Mathematical reference: T. Hutchcroft, *Critical cluster
volumes in hierarchical percolation*, arXiv:2211.05686v1.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalTriangle

/-!
# Hierarchical triangle threshold (tagged statement)

Every statement is assembled from lemmas proved in the imported module; no new mathematics.

## Main results

* `triangle_increment_bounds_and_threshold`: for `c L^{-(d-α)h(x)} ≤ f(x) ≤ C L^{-(d-α)h(x)}`,
  the increments of `Δ_N = ∑_{x,y ∈ Λ_N} f(x) f(y-x) f(y)` are `≍ L^{(3α-d)n}`, the full sum
  converges iff `3α < d`, `Δ_N ≍ N + 1` at `3α = d` and `Δ_N ≍ L^{(3α-d)N}` for `3α > d`.
-/

@[expose] public section
noncomputable section

namespace PercLib.Models

variable {d L : ℕ}

/-- **Hierarchical triangle threshold from two-sided kernel bounds.** On the hierarchical
lattice with `L ≥ 2`, `0 < α < d` and `0 < c ≤ C`, let `f` satisfy
`c ⟨x⟩^{-(d-α)} ≤ f(x) ≤ C ⟨x⟩^{-(d-α)}` with `⟨x⟩ = L^{h(x)}`, and
`Δ_N = ∑_{x,y ∈ Λ_N} f(x) f(y-x) f(y)`. There are `a, A > 0` depending only on `c, C, L, d, α`
with `a L^{(3α-d)n} ≤ Δ_n - Δ_{n-1} ≤ A L^{(3α-d)n}` for `n ≥ 1`; the full triangle sum is
finite exactly when `3α < d`; `Δ_N ≍ N + 1` when `3α = d`; `Δ_N ≍ L^{(3α-d)N}` when
`3α > d`. -/
@[tag "MS6M"]
theorem triangle_increment_bounds_and_threshold [NeZero L] (hL : 2 ≤ L) {α c C : ℝ}
    (hα : 0 < α) (hαd : α < d) (hc : 0 < c) (hcC : c ≤ C) :
    (∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      ∀ n : ℕ, 1 ≤ n →
        a * (L : ℝ) ^ ((3 * α - d) * (n : ℝ)) ≤
          (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
              f x * f (y - x) * f y) -
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
              f x * f (y - x) * f y ∧
        (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
              f x * f (y - x) * f y) -
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
              f x * f (y - x) * f y ≤ A * (L : ℝ) ^ ((3 * α - d) * (n : ℝ))) ∧
    (∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      (Summable (fun p : (ℕ →₀ (Fin d → ZMod L)) × (ℕ →₀ (Fin d → ZMod L)) =>
        f p.1 * f (p.2 - p.1) * f p.2) ↔ 3 * α < d)) ∧
    (3 * α = d → ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      ∀ N : ℕ, k * (N + 1) ≤
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ∧
        ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ≤
          K * (N + 1)) ∧
    (d < 3 * α → ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      ∀ N : ℕ, k * (L : ℝ) ^ ((3 * α - d) * (N : ℝ)) ≤
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ∧
        ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ≤
          K * (L : ℝ) ^ ((3 * α - d) * (N : ℝ))) :=
  ⟨exists_triangle_increment_bounds hL hα hαd hc hcC,
    fun _ hf => summable_triangle_iff hL hα hαd hc hf,
    exists_triangle_linear_bounds hL hα hαd hc hcC,
    exists_triangle_geometric_bounds hL hα hαd hc hcC⟩

end PercLib.Models
