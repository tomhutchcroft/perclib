/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/HighTemperature/FiniteHorizon.lean`; added at source revision
`c873e4ed349df275ed90c207de553a8a34f98101`, supplied under its Apache-2.0 header. This is a
proof-only module, with `PercLib.Percolation.Bond.Exploration.BFS` in place of the original source
prefix. Section countability is
explicit on each theorem instead of suppressed by a forbidden option. Raw audit commands and
source task labels were omitted.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Generation.Step
public import PercLib.Percolation.Bond.Exploration.BFS.Poisson.Assemble
public import PercLib.Percolation.Bond.LocalFiniteness

/-!
# Almost-sure finiteness at each fixed BFS horizon

A finite real row bound makes off-diagonal intensity summable. Borel-Cantelli then makes every
finite-radius open-graph ball almost surely finite, and hence makes the processed set and frontier
at each fixed horizon almost surely finite. This proves finiteness per fixed horizon; it does not
claim that the full cluster is finite. `RowSum` also charges the diagonal while
`UniformRowBound` excludes it; diagonal probabilities cannot change the open graph on distinct
vertices anyway.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-! ### A row sum bounds the off-diagonal edge intensity sum -/

open Classical in
/-- The `ℝ≥0∞`-valued off-diagonal intensity sum at a vertex is finite under the genuine
finite-partial row bound `UniformRowBound` (which excludes the diagonal).

This is the `ℝ≥0∞`-summability input of the first Borel–Cantelli lemma: the real `tsum` form
would be junk for non-summable families, so the finite-partial-sum hypothesis is the honest
one.  The diagonal term `p (s(x,x))` is *not* charged: it never matters for the open graph. -/
theorem tsum_offdiag_lt_top [Countable V] {p : Sym2 V → unitInterval} {m : ℝ} (hrow :
UniformRowBound p m)
    (x : V) :
    (∑' w : V, (if w = x then 0 else (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞))) < ⊤ := by
  classical
  have hcoe : ∀ w : V, (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞)
      = ENNReal.ofReal ((p (s(x, w)) : ℝ)) := fun w => unitInterval_toNNReal_coe p (s(x, w))
  have hmain : (∑' w : V, (if w = x then 0 else (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞)))
      ≤ ENNReal.ofReal m := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun t => ?_)
    have hsum : ∑ w ∈ t, (if w = x then 0 else (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞))
        = ∑ w ∈ t.erase x,
            (if w = x then 0 else (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞)) := by
      by_cases hx : x ∈ t
      · rw [← Finset.sum_erase_add t (fun w => (if w = x then 0 else
          (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞))) hx]
        rw [ite_eq_left rfl, add_zero]
      · rw [Finset.erase_eq_of_notMem hx]
    rw [hsum]
    have hxh : x ∉ t.erase x := Finset.notMem_erase x t
    have hstep : ∑ w ∈ t.erase x,
        (if w = x then 0 else (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞))
        = ∑ w ∈ t.erase x, (unitInterval.toNNReal (p (s(x, w))) : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun w hw => by
        refine ite_eq_right ?_
        intro h
        exact hxh (h ▸ hw))
    rw [hstep, Finset.sum_congr rfl (fun w _ => hcoe w),
      ← ENNReal.ofReal_sum_of_nonneg (fun w _ => (p (s(x, w))).2.1)]
    exact ENNReal.ofReal_le_ofReal (hrow x _ hxh)
  exact lt_of_le_of_lt hmain ENNReal.ofReal_lt_top

/-- `RowSum` (which also charges the diagonal) implies `UniformRowBound`. -/
theorem uniformRowBound_of_rowSum [Countable V] {p : Sym2 V → unitInterval} {m : ℝ} (hrow : RowSum
p m) :
    UniformRowBound p m :=
  fun x t _ => hrow x t

/-- **Almost-sure local finiteness**: every finite-radius ball of the open graph is almost
surely finite under `UniformRowBound`. -/
theorem ae_ball_finite_of_uniformRowBound [Countable V] {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) :
    ∀ᵐ ω ∂(prodBernoulli p), ∀ (v : V) (n : ℕ), ((openGraph ω).ball v n).Finite :=
  ae_finite_balls_of_rowSum_lt_top p (fun v => tsum_offdiag_lt_top hrow v)

/-! ### The frontier and the processed set lie in a finite ball -/

/-- Every vertex of the frontier `A k` is joined to the root by an open walk of length at
most `k`. -/
theorem A_subset_walk [Countable V] (ω : Config V) (o : V) (k : ℕ) :
    A ω o k ⊆ {w : V | ∃ p : (openGraph ω).Walk o w, p.length ≤ k} := by
  induction k with
  | zero =>
      intro y hy
      rw [A_zero, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨SimpleGraph.Walk.nil, Nat.zero_le 0⟩
  | succ k ih =>
      intro y hy
      rw [A_succ] at hy
      obtain ⟨hyU, x, hxA, hxy⟩ := hy
      obtain ⟨p, hp⟩ := ih hxA
      have hne : x ≠ y := fun h => not_mem_U_of_mem_A (h ▸ hxA) hyU
      refine ⟨p.concat ((openGraph_adj_iff ω x y).2 ⟨hxy, hne⟩), ?_⟩
      rw [SimpleGraph.Walk.length_concat]
      exact Nat.succ_le_succ hp

/-- Every vertex of the processed set `P k` is joined to the root by an open walk of length
at most `k`. -/
theorem P_subset_walk [Countable V] (ω : Config V) (o : V) (k : ℕ) :
    P ω o k ⊆ {w : V | ∃ p : (openGraph ω).Walk o w, p.length ≤ k} := by
  intro x hx
  rw [P_eq_iUnion] at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨p, hp⟩ := A_subset_walk ω o j.1 hj
  exact ⟨p, le_trans hp (by exact_mod_cast Nat.le_of_lt j.2)⟩

/-- The finite-horizon discovered set lies in the ball of radius `k+1`. -/
theorem horizon_subset_ball [Countable V] (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o k ⊆ (openGraph ω).ball o (k + 1) := by
  intro x hx
  rw [horizon_eq, Set.mem_union] at hx
  have hex : ∃ p : (openGraph ω).Walk o x, p.length ≤ k := by
    rcases hx with hx | hx
    · exact P_subset_walk ω o k hx
    · exact A_subset_walk ω o k hx
  obtain ⟨p, hp⟩ := hex
  have hp' : (p.length : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hp
  have h1 : (openGraph ω).edist x o ≤ (k : ℕ∞) := by
    rw [SimpleGraph.edist_comm]
    exact le_trans (SimpleGraph.Walk.edist_le p) hp'
  rw [SimpleGraph.mem_ball]
  exact lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self k)

/-- **The horizon is almost surely finite**. -/
theorem ae_horizon_finite [Countable V] {p : Sym2 V → unitInterval} {m : ℝ} (hrow :
UniformRowBound p m) (o : V)
    (k : ℕ) : ∀ᵐ ω ∂(prodBernoulli p), (horizon ω o k).Finite := by
  filter_upwards [ae_ball_finite_of_uniformRowBound (p := p) hrow] with ω hω
  exact (hω o (k + 1)).subset (horizon_subset_ball ω o k)

/-- **The BFS state is almost surely finite at every fixed horizon.**

This discharges the hypothesis `hfin` of `lintegral_bfs_epow_gen_envelopeStep` and of
`lintegral_bfs_epow_gen_le_rowBound`.  It is *per horizon*: the union over `k` of the
generations, i.e. the cluster, need not be finite. -/
theorem ae_finState_ne_none [Countable V] {p : Sym2 V → unitInterval} {m : ℝ} (hrow :
UniformRowBound p m)
    (o : V)
    (k : ℕ) : ∀ᵐ ω ∂(prodBernoulli p), finState ω o k ≠ none := by
  filter_upwards [ae_horizon_finite hrow o k] with ω hω hnone
  have hP : (P ω o k).Finite := hω.subset Set.subset_union_left
  have hA : (A ω o k).Finite := hω.subset Set.subset_union_right
  unfold finState at hnone
  rw [dite_eq_left ⟨hP, hA⟩] at hnone
  exact absurd hnone (by simp)

/-- Consequence used by the induction: the `ℕ∞`-cardinality of the frontier is almost
surely finite, so `epow` of it is a genuine finite power. -/
theorem ae_encard_A_ne_top [Countable V] {p : Sym2 V → unitInterval} {m : ℝ} (hrow :
UniformRowBound p m)
    (o : V)
    (k : ℕ) : ∀ᵐ ω ∂(prodBernoulli p), (A ω o k).encard ≠ ⊤ := by
  filter_upwards [ae_horizon_finite hrow o k] with ω hω
  exact Set.encard_ne_top_iff.mpr (hω.subset Set.subset_union_right)


end PercLib.Percolation.Bond.Exploration.BFS
