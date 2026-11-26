/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project, written on 2026-11-22. A restatement of library lemmas; no upstream
code is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.SusceptibilityLevel

/-!
# Correspondence wrapper for susceptibility levels on a finite connected graph

Tagged restatement of the facts that, on a finite connected graph with `N ≥ 2` vertices, the
susceptibility `p ↦ χ_v(p)` of bond percolation with parameter `p` on the edges is a
polynomial, continuous and strictly increasing on `[0, 1]` from `1` to `N`, so that each level
in `[1, N]` is attained at exactly one parameter and no other level is attained. All
mathematical inputs are proved in `PercLib.Percolation.Bond.SusceptibilityLevel`.

## Main results

* `existsUnique_toReal_chi_edgeSet_eq_and_strictMono`: the conjunction above, together with:
  the parameter at level `λ N^{1/3}` lies in `(0, 1)` exactly when `1 < λ N^{1/3} < N`, and
  for fixed `λ > 0` this holds for all large `N`.
-/

@[expose] public section
noncomputable section

open Polynomial

namespace PercLib.Percolation.Bond

/-- Let `G` be a connected graph on a finite vertex type with `N ≥ 2` vertices, and let
`χ_v(p)` be the susceptibility at `v` of bond percolation with parameter `p` on the edges of
`G`. Then `χ_v` is a polynomial in `p`, continuous and strictly increasing on `[0, 1]`, with
`χ_v(0) = 1` and `χ_v(1) = N`; each `c ∈ [1, N]` equals `χ_v(p)` for exactly one `p`, and every
value of `χ_v` lies in `[1, N]`. A parameter `p` with `χ_v(p) = λ N^{1/3}` lies in `(0, 1)`
exactly when `1 < λ N^{1/3} < N`, and for fixed `λ > 0` this range condition holds for all
sufficiently large `N`. -/
@[tag "6JZB"]
theorem existsUnique_toReal_chi_edgeSet_eq_and_strictMono {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hN : 2 ≤ Fintype.card V)
    (v : V) :
    (∃ P : ℝ[X], ∀ p : unitInterval,
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal = P.eval (p : ℝ)) ∧
    Continuous (fun p : unitInterval =>
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal) ∧
    StrictMono (fun p : unitInterval =>
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal) ∧
    (chi (fun e => if e ∈ G.edgeSet then (0 : unitInterval) else 0) v).toReal = 1 ∧
    (chi (fun e => if e ∈ G.edgeSet then (1 : unitInterval) else 0) v).toReal =
      Fintype.card V ∧
    (∀ c : ℝ, c ∈ Set.Icc (1 : ℝ) (Fintype.card V) →
      ∃! p : unitInterval, (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal = c) ∧
    (∀ p : unitInterval,
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal ∈
        Set.Icc (1 : ℝ) (Fintype.card V)) ∧
    (∀ (lam : ℝ) (p : unitInterval),
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal =
          lam * (Fintype.card V : ℝ) ^ (1 / 3 : ℝ) →
        ((0 < p ∧ p < 1) ↔
          (1 < lam * (Fintype.card V : ℝ) ^ (1 / 3 : ℝ) ∧
            lam * (Fintype.card V : ℝ) ^ (1 / 3 : ℝ) < Fintype.card V))) ∧
    ∀ lam : ℝ, 0 < lam → ∀ᶠ N : ℕ in Filter.atTop,
      1 < lam * (N : ℝ) ^ (1 / 3 : ℝ) ∧ lam * (N : ℝ) ^ (1 / 3 : ℝ) < N :=
  ⟨exists_polynomial_toReal_chi_edgeSet G v, continuous_toReal_chi_edgeSet G v,
    strictMono_toReal_chi_edgeSet_of_connected hG hN v, toReal_chi_edgeSet_zero G v,
    toReal_chi_edgeSet_one hG v, fun _ hc => existsUnique_toReal_chi_edgeSet_eq hG hN v hc,
    toReal_chi_edgeSet_mem_Icc hG hN v,
    fun _ p hp => hp ▸ pos_and_lt_one_iff_of_toReal_chi_edgeSet hG hN v p,
    fun _ hlam => eventually_one_lt_mul_rpow_and_lt hlam⟩

end PercLib.Percolation.Bond
