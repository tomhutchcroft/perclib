/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/BFSProduct.lean`; added at source revision
`b4ea9ce13d15b85d2ffa5c7544656693d8e7f59a`, supplied under its Apache-2.0 header. This is a
proof-only module. Its reviewed
interfaces contain all the corresponding definitions. The canonical BFS namespace prefix is
`PercLib.Percolation.Bond.Exploration.BFS`. Forbidden build-option and source task-label commands
were not imported.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.BFSProduct.Defs
public import PercLib.Probability.Exploration.AdaptedReveal.PGF

/-!
# Adapted Bernoulli factorization for BFS

Fresh disjointness at a reachable finite state and the three BFS instantiations of the
adapted product/PGF factorization. The construction uses the real `prodBernoulli` on bond
configurations. Finite fresh-coordinate products are separated from possibly infinite histories;
the countable-state fallback `none` forces an empty fresh set rather than a fabricated bound.
The state-countability scope is local to declarations that actually use it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*} [Countable V]

/-- At a reachable finite state, `E(A k, U k)` is disjoint from `R k`. -/
theorem disjoint_queried_revealFin_of_some {ω : Config V} {o : V} {k : ℕ} {Q T : Finset V}
    (h : finState ω o k = some (Q, T)) :
    Disjoint (queried ω o k) (revealFin (some (Q, T))) := by
  obtain ⟨hQ, -⟩ := finState_eq_some_iff.mp h
  rw [show revealFin (some (Q, T)) = revealed ω o k from by
    ext e
    simp only [revealed, revealFin, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, hve⟩
      exact ⟨v, hQ ▸ hv, hve⟩
    · rintro ⟨v, hv, hve⟩
      exact ⟨v, hQ ▸ hv, hve⟩]
  exact (disjoint_revealed_queried ω o k).symm

/-- **Direction 1's factorization at the BFS countable state.**  This is
`PercLib.Probability.AdaptedReveal.lintegral_adapted_prod` applied to
`finRevealData o k`.  The state is the pair `(P k, A k)` when both are finite and
`none` otherwise; the fresh set `S σ` must be a finite set of edges disjoint from
the revealed set of state `σ` (for `σ = none` this forces `S none = ∅`, since
`revealFin none = univ`). -/
theorem lintegral_bfs_adapted_prod (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (f : Sym2 V → Prop → ℝ≥0∞) :
    ∫⁻ ω, G ω * ∏ e ∈ S (finState ω o k), f e (e ∈ ω) ∂(prodBernoulli p) =
      ∑' σ : FinState V, (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
          * ∏ e ∈ S σ, ∫⁻ ω, f e (e ∈ ω) ∂(prodBernoulli p) :=
  lintegral_adapted_prod p (finRevealData o k) G H hH hG S hS f

/-- **The Bernoulli pgf form of the BFS factorization.** -/
theorem lintegral_bfs_adapted_pgf (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (t : ℝ≥0∞) :
    ∫⁻ ω, G ω * t ^ openCount (S (finState ω o k)) ω ∂(prodBernoulli p) =
      ∑' σ : FinState V, (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
          * ∏ e ∈ S σ, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
              + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞))) :=
  lintegral_adapted_pgf p (finRevealData o k) G H hH hG S hS t

/-- **The bounded Bernoulli pgf form at the BFS state**, the one-step estimate
consumed by the generation induction. -/
theorem lintegral_bfs_adapted_pgf_le (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (t : ℝ≥0∞) (B : FinState V → ℝ≥0∞)
    (hB : ∀ σ : FinState V, (∏ e ∈ S σ, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)))) ≤ B σ) :
    ∫⁻ ω, G ω * t ^ openCount (S (finState ω o k)) ω ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V, (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p)) * B σ :=
  lintegral_adapted_pgf_le p (finRevealData o k) G H hH hG S hS t B hB


end PercLib.Percolation.Bond.Exploration.BFS
