/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements written on 2026-11-20: Theorem 1.1 and Corollary 1.2 of T. Hutchcroft, *The critical
two-point function for long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1, on
the bond interface. New statements; no upstream code is copied and no new notion is introduced
(lattice, level, balls, `intensityProfile`, `rootCriticalIntensity`, `law`, `tau` and `openGraph`
are the library's).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Intensity.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Critical two-point bounds on the hierarchical lattice (statements)

Conventions, as in `PercLib.Models.Hierarchical` and `PercLib.Models.HierarchicalGeometry`:
the lattice is `V = ℕ →₀ (Fin d → ZMod L)`, the level of `z` is `h z = z.support.sup Nat.succ`
(so the source's norm is `‖z‖ = L ^ h z` for `z ≠ 0` and `‖0‖ = 0`, hence
`⟨z⟩ = max(1, ‖z‖) = L ^ h z` for every `z`),
the ball of level `n` is `Λ_n = {z | h z ≤ n}` (it has `L ^ (d n)` points, `card_ball`) and the
shell `Λ_n \ Λ_{n-1}` is `{z | h z = n}`. A kernel is `J : Sym2 V → ℝ≥0`, so it is symmetric by
construction; the source's `J(x - y)` is a function on the group, which here is translation
invariance `J s(u + x, v + x) = J s(u, v)`. Bond probabilities at intensity `β` are
`intensityProfile J β`, and `β_c = rootCriticalIntensity J 0 : ℝ≥0∞`. The source's β_c is
the global threshold (positive probability of some infinite cluster, p. 3). For
translation-invariant `J` it equals the root threshold by
`rootCriticalIntensity_eq_globalCriticalIntensity_of_translationInvariant`
(`PercLib.Models.LongRange.FiniteSusceptibility`). Since
`intensityProfile` takes a finite intensity, the critical law is evaluated at
`β_c.toNNReal`; both statements also assert `β_c < ⊤`, so this is the law at `β_c` itself.
Joining `x` and `y` inside a set `S` is `((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩`.
Probabilities are in `ℝ≥0∞`, and real bounds enter through `ENNReal.ofReal`.

* `HierarchicalTwoPointAveraged` (Theorem 1.1, wiki J98J).
* `HierarchicalTwoPointRadial` (Corollary 1.2, wiki W498).
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- **Theorem 1.1 of arXiv:2103.17013v1 (J98J: averaged critical two-point bounds).** Let
`d ≥ 1`, `L ≥ 2`, `0 < α < d`, `0 < c` and `C : ℝ`. There are constants `a, A > 0`, depending
only on `d, L, α, c, C` (they are chosen before `J`), such that for every translation-invariant
kernel `J` on `V = ℕ →₀ (Fin d → ZMod L)` with
`c L^{-(d+α) h(v-u)} ≤ J(u,v) ≤ C L^{-(d+α) h(v-u)}` for `u ≠ v`, the critical intensity
`β_c = rootCriticalIntensity J 0` is finite and, for every `n ≥ 1`,
`a L^{-(d-α)n} ≤ |Λ_n|^{-1} ∑_{h x = n} P_{β_c}(0 ↔ x inside Λ_n)
  ≤ |Λ_n|^{-1} ∑_{h x ≤ n} τ_{β_c}(0,x) ≤ A L^{-(d-α)n}`,
with `|Λ_n| = L^{dn}`. The shell sum is normalised by the volume of the whole ball, as in the
source. The law is `law (intensityProfile J β_c.toNNReal)`; this is the law at `β_c` because
`β_c < ⊤` is part of the conclusion. The conjunct `β_c < ⊤` follows from the bounds themselves
(if `β_c = ⊤` the law is the `β = 0` law and the lower bound fails), so including it does not
strengthen the source. The source assumes `c, C > 0` only: `0 < C` and `c ≤ C` hold whenever
some kernel satisfies both bounds (there is a pair `u ≠ v`), so they are not assumed. -/
@[tag "J98J"]
def HierarchicalTwoPointAveraged (d L : ℕ) (α c C : ℝ) : Prop :=
  1 ≤ d → 2 ≤ L → 0 < α → α < d → 0 < c →
  ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
      (∀ x u v, J s(u + x, v + x) = J s(u, v)) →
      (∀ u v, u ≠ v →
        c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
          (J s(u, v) : ℝ)) →
      (∀ u v, u ≠ v →
        (J s(u, v) : ℝ) ≤
          C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
      let q := intensityProfile J (rootCriticalIntensity J 0).toNNReal
      rootCriticalIntensity J 0 < ⊤ ∧
      ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (a * (L : ℝ) ^ (-((d : ℝ) - α) * n)) ≤
            ((L : ℝ≥0∞) ^ (d * n))⁻¹ *
              ∑' x : ℕ →₀ (Fin d → ZMod L),
                (if x.support.sup Nat.succ = n then
                  law q {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                      {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
                    ∃ hx : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
                    ((openGraph ω).induce
                      {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
                      ⟨0, h0⟩ ⟨x, hx⟩}
                else 0) ∧
          ((L : ℝ≥0∞) ^ (d * n))⁻¹ *
              ∑' x : ℕ →₀ (Fin d → ZMod L),
                (if x.support.sup Nat.succ = n then
                  law q {ω | ∃ h0 : (0 : ℕ →₀ (Fin d → ZMod L)) ∈
                      {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
                    ∃ hx : x ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n},
                    ((openGraph ω).induce
                      {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).Reachable
                      ⟨0, h0⟩ ⟨x, hx⟩}
                else 0) ≤
            ((L : ℝ≥0∞) ^ (d * n))⁻¹ *
              ∑' x : ℕ →₀ (Fin d → ZMod L),
                (if x.support.sup Nat.succ ≤ n then tau q 0 x else 0) ∧
          ((L : ℝ≥0∞) ^ (d * n))⁻¹ *
              ∑' x : ℕ →₀ (Fin d → ZMod L),
                (if x.support.sup Nat.succ ≤ n then tau q 0 x else 0) ≤
            ENNReal.ofReal (A * (L : ℝ) ^ (-((d : ℝ) - α) * n))

/-- **Corollary 1.2 of arXiv:2103.17013v1 (W498: pointwise critical two-point bounds for radial
kernels).** Let `d ≥ 1`, `L ≥ 2`, `0 < α < d` and `0 < c ≤ C`. There are constants `a, A > 0`,
depending only on `d, L, α, c, C` (they are chosen before `J`), such that for every radial
kernel `J` on `V = ℕ →₀ (Fin d → ZMod L)` (`J(x,y) = f(h(y-x))` for some `f`, so `J` depends
only on the hierarchical distance) with `c L^{-(d+α) h(v-u)} ≤ J(u,v) ≤ C L^{-(d+α) h(v-u)}`
for `u ≠ v`, the critical intensity `β_c = rootCriticalIntensity J 0` satisfies
`0 < β_c < ∞` and, for all `x, y`,
`a ⟨x-y⟩^{-(d-α)} ≤ P_{β_c}(x ↔ y inside Λ(x,y)) ≤ τ_{β_c}(x,y) ≤ A ⟨x-y⟩^{-(d-α)}`.
Here `⟨x-y⟩ = L^{h(y-x)}` (`h(y-x) = h(x-y)`, and `⟨0⟩ = 1`), and
`Λ(x,y) = {z | h(z-x) ≤ h(y-x)}` is the smallest hierarchical ball containing `x` and `y`.
The law is `law (intensityProfile J β_c.toNNReal)`; this is the law at `β_c` because
`β_c < ⊤` is part of the conclusion. The conjuncts `0 < β_c` (as in W498) and `β_c < ⊤` follow
from the bounds themselves (if `β_c = 0` or `β_c = ⊤` the law is the `β = 0` law, under which
`τ(x,y) = 0` for `x ≠ y`, contradicting the lower bound), so including them does not strengthen
the source. -/
@[tag "W498"]
def HierarchicalTwoPointRadial (d L : ℕ) (α c C : ℝ) : Prop :=
  1 ≤ d → 2 ≤ L → 0 < α → α < d → 0 < c → c ≤ C →
  ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
      (∃ f : ℕ → ℝ≥0, ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) →
      (∀ u v, u ≠ v →
        c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
          (J s(u, v) : ℝ)) →
      (∀ u v, u ≠ v →
        (J s(u, v) : ℝ) ≤
          C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
      let q := intensityProfile J (rootCriticalIntensity J 0).toNNReal
      0 < rootCriticalIntensity J 0 ∧ rootCriticalIntensity J 0 < ⊤ ∧
      ∀ x y : ℕ →₀ (Fin d → ZMod L),
        ENNReal.ofReal
            (a * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α))) ≤
          law q {ω | ((openGraph ω).induce
            {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
              ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} ∧
        law q {ω | ((openGraph ω).induce
            {z | (z - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ}).Reachable
              ⟨x, by simp⟩ ⟨y, le_refl ((y - x).support.sup Nat.succ)⟩} ≤ tau q x y ∧
        tau q x y ≤ ENNReal.ofReal
            (A * (L : ℝ) ^ (-(((y - x).support.sup Nat.succ : ℕ) : ℝ) * ((d : ℝ) - α)))

end PercLib.Models
