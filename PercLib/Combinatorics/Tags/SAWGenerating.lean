/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the uniform fixed-length self-avoiding walk on `ℤ^d` and its
generating functions, proved from `SAWGenerating.lean`. Mathematical reference: N. Madras and
G. Slade, *The Self-Avoiding Walk* (1993), §1.2. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.SAWGenerating

/-!
# Uniform fixed-length self-avoiding walk and its generating functions: statement form

The tagged theorem restates, as one conjunction, results proved under their own names in
`PercLib.Combinatorics.SAWGenerating` and `PercLib.Models.Lattice`. A self-avoiding walk of
length `n` from the origin is a path of `zdGraph d` of length `n`; `c_n(x)` is
`Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n}` and `c_n` is
`Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n}`; laws on walks are `PMF`s on
`Σ y, (zdGraph d).Walk 0 y`.

## Main results

* `uniformSAW_properties`
-/

@[expose] public section

open SimpleGraph
open scoped ENNReal

namespace PercLib.Models.Site

/-- Nearest-neighbour steps of `ℤ^d` are `ℓ¹` steps of length one; `c_0(x) = 1_{x = 0}`;
`c_n = ∑_x c_n(x)`; `∑_x S_z(x) = ∑_n c_n z^n` with `S_z(x) = ∑_n c_n(x) z^n`, in `[0, ∞]`;
there are `(2d)^n` nearest-neighbour walks of length `n`. For `d ≥ 1`: simple random walk at
horizon `n` (each walk of length `n` has probability `(2d)^{-n}`) and the uniform law on the
`c_n` self-avoiding walks of length `n` exist, and the first conditioned on self-avoidance is
the second. Under the uniform law at horizon `n`, the first `k` steps have the law giving a
prefix `c_n⁻¹` times its number of self-avoiding continuations; in `ℤ^2` at horizon `8` this
weight is not constant on self-avoiding prefixes of length `7`. -/
@[tag "C69U"]
theorem uniformSAW_properties :
    (∀ (d : ℕ) (x y : Fin d → ℤ), (zdGraph d).Adj x y ↔ ∑ i, (y i - x i).natAbs = 1) ∧
    (∀ (d : ℕ) (x : Fin d → ℤ),
      Nat.card {q : (zdGraph d).Path 0 x // q.1.length = 0} = if x = 0 then 1 else 0) ∧
    (∀ d n : ℕ, (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞) =
      ∑' x, (Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n} : ℝ≥0∞)) ∧
    (∀ (d : ℕ) (z : ℝ≥0∞),
      ∑' x, ∑' n, (Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n} : ℝ≥0∞) * z ^ n =
        ∑' n, (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞) *
          z ^ n) ∧
    (∀ d n : ℕ, Nat.card {w : Σ y, (zdGraph d).Walk 0 y // w.2.length = n} = (2 * d) ^ n) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, ∃ Q : PMF (Σ y, (zdGraph d).Walk 0 y),
      ∀ w, Q w = if w.2.length = n then ((2 * d : ℝ≥0∞) ^ n)⁻¹ else 0) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, ∃ P : PMF (Σ y, (zdGraph d).Walk 0 y),
      ∀ w, P w = if w.2.IsPath ∧ w.2.length = n then
        ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹ else 0) ∧
    (∀ (d n : ℕ) (Q : PMF (Σ y, (zdGraph d).Walk 0 y)),
      (∀ w, Q w = if w.2.length = n then ((2 * d : ℝ≥0∞) ^ n)⁻¹ else 0) →
      ∀ (h : ∃ w ∈ {w : Σ y, (zdGraph d).Walk 0 y | w.2.IsPath}, w ∈ Q.support) w,
        Q.filter {w | w.2.IsPath} h w = if w.2.IsPath ∧ w.2.length = n then
          ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹
          else 0) ∧
    (∀ (d n : ℕ) (P : PMF (Σ y, (zdGraph d).Walk 0 y)),
      (∀ w, P w = if w.2.IsPath ∧ w.2.length = n then
        ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹ else 0) →
      ∀ (k : ℕ) (p : Σ y, (zdGraph d).Walk 0 y),
        P.map (fun w => ⟨w.2.getVert k, w.2.take k⟩) p =
          (Nat.card {w : Σ y, (zdGraph d).Walk 0 y //
            (w.2.IsPath ∧ w.2.length = n) ∧ (⟨w.2.getVert k, w.2.take k⟩ :
              Σ y, (zdGraph d).Walk 0 y) = p} : ℝ≥0∞) *
          ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹) ∧
    (∃ p₁ p₂ : Σ y, (zdGraph 2).Walk 0 y,
      (p₁.2.IsPath ∧ p₁.2.length = 7) ∧ (p₂.2.IsPath ∧ p₂.2.length = 7) ∧
      ∀ P : PMF (Σ y, (zdGraph 2).Walk 0 y),
        (∀ w, P w = if w.2.IsPath ∧ w.2.length = 8 then
          ((Nat.card {p : Σ y, (zdGraph 2).Path 0 y // p.2.1.length = 8} : ℝ≥0∞))⁻¹
          else 0) →
        P.map (fun w => ⟨w.2.getVert 7, w.2.take 7⟩) p₁ = 0 ∧
          P.map (fun w => ⟨w.2.getVert 7, w.2.take 7⟩) p₂ ≠ 0) :=
  ⟨fun _ => zdGraph_adj_iff_l1, fun _ => card_paths_to_length_zero,
    fun _ => card_paths_eq_tsum, fun _ => tsum_tsum_card_paths_to_mul_pow,
    card_walks_length, fun _ hd => exists_pmf_walk_eq_ite hd,
    fun _ hd => exists_pmf_path_eq_ite hd, fun _ _ _ hQ h w => filter_isPath_apply hQ h w,
    fun _ _ _ hP => map_take_apply hP, exists_map_take_ne⟩

end PercLib.Models.Site
