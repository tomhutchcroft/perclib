/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the energy and exit-time bounds on the lazy return kernel, proved
in `PercLib/Probability/LazyReturnKernel.lean`. No new definitions. Mathematical reference:
Barlow, Járai, Kumagai and Slade, Comm. Math. Phys. 278 (2008), Section 2.1.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.LazyReturnKernel

/-!
# Energy and exit-time bounds for the lazy return kernel: correspondence

Wiki correspondence for the upper (energy) and lower (exit-time) bounds on the return kernel
of lazy simple random walk on an infinite connected locally finite graph.

## Main results

* `lazy_return_le_energy_and_ge_exitTime`
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Probability

/-- **KGNK.** Let `G` be an infinite connected locally finite simple graph with unit
conductances and a vertex `o`; write `π(x) = deg x`, `B(r) = {x : d(o,x) ≤ r}`,
`V(r) = ∑_{x ∈ B(r)} π(x)` and `D_r = B(r - 1)`. Let `p n x y = P_x(Y_n = y)` be the `n`-step
transition probabilities of the lazy walk `Y` with operator `Q = (I + P)/2`, given by the
first-step recursion `p (n+1) x y = p n x y / 2 + (∑_{z ∼ x} p n z y) / (2 deg x)`, so that
`q̂_n(x, y) = p n x y / π(y)`. For `r ≥ 1` let `S r n x = P_x(Y_0, …, Y_n ∈ D_r)`, given by its
first-step recursion; for `x ∈ D_r` this is `P_x(T̂_r > n)`, where `T̂_r` is the hitting time of
`S(r)`. Thus `u_r = E_o T̂_r = ∑ₙ S r n o` and `M_r = sup_{x ∈ D_r} E_x T̂_r` (in `ℝ≥0∞`).
Then for all integers `n, r ≥ 1`,
`q̂_n(o, o) ≤ 2 / V(r) + 2r / (n + 1)` and `q̂_{2n}(o, o) ≥ (u_r - n)₊² / (M_r² V(r - 1))`. -/
@[tag "KGNK"]
theorem lazy_return_le_energy_and_ge_exitTime {V : Type*} [Infinite V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected) (o : V)
    (p : ℕ → V → V → ℝ)
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (S : ℕ → ℕ → V → ℝ≥0∞)
    (hS0 : ∀ r x, S r 0 x = if G.dist o x ≤ r - 1 then 1 else 0)
    (hSs : ∀ r n x, S r (n + 1) x = if G.dist o x ≤ r - 1 then
      S r n x / 2 + (∑ z ∈ G.neighborFinset x, S r n z) / (2 * G.degree x) else 0)
    (n r : ℕ) (_hn : 1 ≤ n) (_hr : 1 ≤ r) :
    p n o o / G.degree o ≤
        2 / ∑ᶠ x ∈ {x | G.dist o x ≤ r}, (G.degree x : ℝ) + 2 * r / (n + 1) ∧
      (∑' k, S r k o - n) ^ 2 /
          ((⨆ x, ⨆ (_ : G.dist o x ≤ r - 1), ∑' k, S r k x) ^ 2 *
            ENNReal.ofReal (∑ᶠ x ∈ {x | G.dist o x ≤ r - 1}, (G.degree x : ℝ))) ≤
        ENNReal.ofReal (p (2 * n) o o / G.degree o) := by
  have hdeg : ∀ x, 0 < G.degree x := fun x => hG.preconnected.degree_pos_of_nontrivial x
  rw [finsum_mem_eq_finite_toFinset_sum _ (hG.finite_setOf_dist_le o r),
    finsum_mem_eq_finite_toFinset_sum _ (hG.finite_setOf_dist_le o (r - 1))]
  set Q : (V → ℝ) → V → ℝ := fun f x =>
    f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x)
  exact ⟨lazy_return_le Q p hG o hdeg (fun _ _ => rfl) hp0 hps n r,
    lazy_return_ge Q p hG o (r - 1) (S r) hdeg (fun _ _ => rfl) hp0 hps (hS0 r) (hSs r) n⟩

end PercLib.Probability
