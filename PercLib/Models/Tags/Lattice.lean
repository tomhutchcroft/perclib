/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the lattice-path-growth article (the graph `ℤ^d`, self-avoiding
path counts and the connective constant).
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.Lattice
public import PercLib.Models.ConnectiveConstant

/-!
# The lattice `ℤ^d`, self-avoiding paths and the connective constant: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `zdGraph_properties`
* `card_paths_properties`
* `connectiveConstant_properties`
-/

@[expose] public section
noncomputable section
open SimpleGraph Filter Topology

namespace PercLib.Models.Site

/-- The nearest-neighbour graph of `ℤ^d` (every `d ≥ 0`) has degree `2d`, is connected, has
graph distance `‖y - x‖₁` and finite balls, `|B_n| = 2n+1` when `d = 1`, and translations,
coordinate permutations and sign changes are automorphisms. -/
@[tag "8QCR"]
theorem zdGraph_properties :
    (∀ (d : ℕ) (x : Fin d → ℤ) [Fintype ((zdGraph d).neighborSet x)],
      (zdGraph d).degree x = 2 * d) ∧
    (∀ d : ℕ, (zdGraph d).Connected) ∧
    (∀ (d : ℕ) (x y : Fin d → ℤ), (zdGraph d).dist x y = ∑ i, (y i - x i).natAbs) ∧
    (∀ (d : ℕ) (x : Fin d → ℤ) (n : ℕ), {y | (zdGraph d).dist x y ≤ n}.Finite) ∧
    (∀ (x : Fin 1 → ℤ) (n : ℕ), {y | (zdGraph 1).dist x y ≤ n}.ncard = 2 * n + 1) ∧
    (∀ (d : ℕ) (g : Fin d → ℤ), ∃ φ : zdGraph d ≃g zdGraph d, ∀ x, φ x = x + g) ∧
    (∀ (d : ℕ) (σ : Equiv.Perm (Fin d)), ∃ φ : zdGraph d ≃g zdGraph d, ∀ x, φ x = x ∘ σ) ∧
    (∀ (d : ℕ) (s : Fin d → Bool), ∃ φ : zdGraph d ≃g zdGraph d,
      ∀ x i, φ x i = if s i then -x i else x i) :=
  ⟨fun d x _ => zdGraph_degree d x, zdGraph_connected, zdGraph_dist,
    fun _ x n => zdGraph_ball_finite x n, zdGraph_one_ball_ncard,
    fun _ g => exists_zdGraph_iso_add g, fun _ σ => exists_zdGraph_iso_perm σ,
    fun _ s => exists_zdGraph_iso_neg s⟩

/-- Self-avoiding path counts `c_n(x)` on `ℤ^d`: finite, `c_0 = 1`, independent of the start,
submultiplicative; for `d ≥ 1`, `c_n ≥ 1` and `c_{n+1} ≤ 2d(2d-1)^n`; for `d = 0`,
`c_{n+1} = 0`. -/
@[tag "7DGG"]
theorem card_paths_properties :
    (∀ (d k : ℕ) (x : Fin d → ℤ),
      Finite {p : Σ y, (zdGraph d).Path x y // p.2.1.length = k}) ∧
    (∀ d : ℕ, Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = 0} = 1) ∧
    (∀ (d k : ℕ) (x : Fin d → ℤ),
      Nat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = k} =
        Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = k}) ∧
    (∀ d n m : ℕ,
      Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n + m} ≤
        Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} *
          Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = m}) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ n : ℕ,
      1 ≤ Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n}) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ n : ℕ,
      Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n + 1} ≤
        2 * d * (2 * d - 1) ^ n) ∧
    (∀ n : ℕ, Nat.card {p : Σ y, (zdGraph 0).Path 0 y // p.2.1.length = n + 1} = 0) :=
  ⟨finite_paths_length, card_paths_length_zero, fun _ k x => card_paths_eq_card_paths_zero k x,
    card_paths_add_le, fun _ hd n => one_le_card_paths hd n,
    fun d _ n => card_paths_succ_le d n, card_paths_dim_zero_succ⟩

/-- The connective constant: for `d ≥ 1`, `μ_d = lim c_n^{1/n} = inf_{n ≥ 1} c_n^{1/n}` exists
and `1 ≤ μ_d ≤ 2d - 1`; and `μ_1 = 1`. -/
@[tag "F3YB"]
theorem connectiveConstant_properties :
    (∀ d : ℕ, 1 ≤ d → ∃ μ : ℝ,
      Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
        p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧
      μ = ⨅ n : {n : ℕ // 1 ≤ n}, (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
        p.2.1.length = n.1} : ℝ) ^ ((n.1 : ℝ)⁻¹) ∧
      1 ≤ μ ∧ μ ≤ 2 * d - 1) ∧
    (∀ μ : ℝ, Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph 1).Path 0 y //
        p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) → μ = 1) :=
  ⟨fun _ hd => exists_tendsto_card_paths_rpow_eq_iInf hd,
    fun _ hμ => eq_one_of_tendsto_card_paths_rpow_one hμ⟩

end PercLib.Models.Site
