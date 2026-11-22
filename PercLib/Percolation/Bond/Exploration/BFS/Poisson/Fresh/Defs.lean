/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Poisson/Fresh/Defs.lean`; added at source revision
`a1dd3fd7178264bb1dfc2c71abc2cdca25da9d48`,
supplied under its Apache-2.0 header. This is a reviewed definitions/constructor interface on the
canonical bond configuration. No alternative configuration model is introduced.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Poisson.Rows.Defs

/-!
# Fresh-coordinate PGF bounds at a BFS state

`finStateCard` records a finite frontier's size and is zero at `none`. `freshEdgeSet` records
permitted fresh coordinates, disjoint from revelation by construction, and is empty at `none`.
These definitions are distinct from `freshEdges`. The estimate uses an explicit finite `Finset`;
it does not assert a finite-frontier or infinite-generation moment bound on the fallback state.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond Finset
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- Number of frontier vertices encoded by a `FinState` (`0` for `none`, where no finiteness is
known). -/
def finStateCard : FinState V → ℕ
  | none => 0
  | some (_, T) => T.card

/-- The edges a state may legitimately query: for `some (Q,T)` the edges from the frontier `T`
into the undiscovered set `(Q ∪ T)ᶜ` that have not already been revealed, and `∅` for `none`.
Cutting out `revealFin σ` makes the fresh set automatically disjoint from the revealed set, so
the adapted-revelation factorization applies at every state, reachable or not. -/
def freshEdgeSet : FinState V → Set (Sym2 V)
  | none => ∅
  | some (Q, T) => edgeSet (T : Set V) ((Q : Set V) ∪ (T : Set V))ᶜ \ revealFin (some (Q, T))

/-- The fresh edge set of any state is disjoint from its revealed edge set. -/
theorem disjoint_freshEdgeSet_revealFin (σ : FinState V) :
    Disjoint (freshEdgeSet σ) (revealFin σ) := by
  cases σ with
  | none => simp [freshEdgeSet]
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      rw [Set.disjoint_left]
      intro e he he'
      exact he.2 he'

/-- The frontier `T` is disjoint from the undiscovered set `(Q ∪ T)ᶜ`. -/
theorem disjoint_fresh (Q T : Finset V) :
    Disjoint (T : Set V) ((Q : Set V) ∪ (T : Set V))ᶜ := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hx' (Or.inr hx)

/-- The budget supplied by the row-sum hypothesis at a finite state. -/
theorem sum_le_finStateCard_mul (p : Sym2 V → unitInterval) (Q T : Finset V)
    (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, e ∈ freshEdgeSet (some (Q, T)))
    {M : ℝ} (hM : UniformRowBound p M) :
    ∑ e ∈ S, (p e : ℝ) ≤ (finStateCard (some (Q, T)) : ℝ) * M :=
  sum_le_card_mul_of_subset_edgeSet p (disjoint_fresh Q T) S
    (fun e he => (hS e he).1) hM

/-- **The one-step fresh-moment estimate from uniform row sums.**  For a finite fresh edge set
`S σ` contained in the querying set of the state `σ`, the unconditional integral of
`G · t^{#open(S σ)}` is bounded by the history sum with budget `|T_σ| · M`.

This is `Lemma 4.4` in the unconditional (history-multiplier) form: the only probabilistic input
is the committed adapted-revelation factorization, and the only deterministic input is the
row-sum charging.  No finiteness of `A k`, `P k`, `U k` or of the queried set is assumed beyond
what the state already encodes, and the statement is finite-fresh-set only. -/
theorem lintegral_bfs_adapted_pgf_le_rowBound [Countable V] (p : Sym2 V → unitInterval)
    (o : V) (k : ℕ) (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (hSq : ∀ σ, ∀ e ∈ S σ, e ∈ freshEdgeSet σ)
    (t : ℝ≥0∞) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) {M : ℝ} (hM : UniformRowBound p M) :
    ∫⁻ ω, G ω * t ^ openCount (S (finState ω o k)) ω ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * ENNReal.ofReal (Real.exp ((t.toReal - 1) * ((finStateCard σ : ℝ) * M))) := by
  classical
  refine lintegral_bfs_adapted_pgf_le_of_budget p o k G H hH hG S hS t ht ht_top
    (fun σ => (finStateCard σ : ℝ) * M) ?_
  intro σ
  cases σ with
  | none =>
      have hempty : S none = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        exact hSq none e he
      rw [hempty]
      simp [finStateCard]
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      exact sum_le_finStateCard_mul p Q T (S (some (Q, T))) (hSq (some (Q, T))) hM

end PercLib.Percolation.Bond.Exploration.BFS
