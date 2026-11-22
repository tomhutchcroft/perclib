/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Generation/Fresh.lean`; added at source revision
`81ff4de74a4eae0fd87ce59ebb2b09933fd9da95`, supplied under its Apache-2.0 header.
Definitions have moved to separately reviewed `Defs` modules. This is a proof-only module with
canonical prefix `PercLib.Percolation.Bond.Exploration.BFS`; explicit countability scoping keeps
the source premises while removing
forbidden section-option commands. Mathematical reference: the exploration outline, §4–§5.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Generation.Fresh.Defs
public import PercLib.Percolation.Bond.Exploration.BFS.Generation.Arithmetic

/-!
# Finite-fresh exhaustion of BFS generations

Fresh queries on a finite compressed state are disjoint from revelation. The finite-subset
supremum controls the full generation in extended powers, while the outer over-approximating
query set depends only on the state, not the configuration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration.BFS
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators Topology

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

theorem queried_subset_freshEdges [Countable V] (ω : Config V) (o : V) (k : ℕ) :
    queried ω o k ⊆ freshEdges (finState ω o k) := by
  classical
  set σ := finState ω o k with hσ
  cases h : σ with
  | none => exact Set.subset_univ _
  | some QT =>
    obtain ⟨Q, T⟩ := QT
    obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp h
    have hU : U ω o k = (((Q : Set V) ∪ (T : Set V))ᶜ) := by
      rw [U_eq_compl, hQ, hT]
    change queried ω o k ⊆ freshEdges (some (Q, T))
    rw [freshEdges, queried, hU, hT]

/-- The queried set is disjoint from the revealed set of the same state.  At a finite
state this is the state-level form of `disjoint_revealed_queried`. -/
theorem freshEdges_disjoint_reveal [Countable V] (Q T : Finset V)
    (hQT : Disjoint (Q : Set V) (T : Set V)) :
    Disjoint (freshEdges (some (Q, T))) (revealFin (some (Q, T))) := by
  classical
  rw [Set.disjoint_left]
  rintro e ⟨x, hxT, y, hyU, rfl⟩ ⟨v, hvQ, hve⟩
  have hxQ : x ∉ (Q : Set V) := fun hxQ => (Set.disjoint_left.mp hQT) hxQ hxT
  rw [Sym2.mem_iff] at hve
  rcases hve with h | h
  · exact hxQ (h ▸ hvQ)
  · exact hyU (Or.inl (h ▸ hvQ))

/-! ### The finite-fresh supremum -/

/-- **Finite-fresh domination.**  The generation cardinality is dominated, in `epow`, by
the supremum of the finite open counts over finite subsets of any set containing the open
queried edges.  This is the monotone-convergence input of the one-step estimate; the
index type is the subtype of finite subsets of the *fixed* set `s`, so it does not depend
on the configuration. -/
theorem gen_epow_le_iSup_openCount [Countable V] {s : Set (Sym2 V)} {τ : ℝ} (hτ : 1 ≤ τ)
    {o : V} {k : ℕ} {ω : Config V} (hs : queried ω o k ∩ ω ⊆ s) :
    epow (ENNReal.ofReal τ) ((gen ω o k).encard) ≤
      ⨆ (F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆ s}),
        (ENNReal.ofReal τ) ^ openCount F.1 ω := by
  classical
  have hgen : (gen ω o k).encard ≤ (queried ω o k ∩ ω).encard := gen_encard_le_queried ω o k
  refine le_trans (epow_mono (ENNReal.ofReal τ) (by simpa using ENNReal.ofReal_le_ofReal hτ)
    hgen) ?_
  rw [epow]
  refine iSup_le (fun k' => ?_)
  have hex : ∃ t : Finset (Sym2 V), (t : Set (Sym2 V)) ⊆ s ∧
      openCount t ω = ((queried ω o k ∩ ω).encard ⊓ (k' : ℕ∞)).toNat := by
    have hb : (((queried ω o k ∩ ω).encard ⊓ (k' : ℕ∞)).toNat : ℕ∞) ≤
        (queried ω o k ∩ ω).encard :=
      le_trans (ENat.natCast_toNat_le_self _) inf_le_left
    obtain ⟨t, ht, htc⟩ := exists_finset_card_le_encard (s := queried ω o k ∩ ω)
      (n := ((queried ω o k ∩ ω).encard ⊓ (k' : ℕ∞)).toNat) hb
    refine ⟨t, ht.trans hs, ?_⟩
    have hfil : t.filter (fun e => e ∈ ω) = t := by
      refine Finset.filter_eq_self.mpr (fun e he => ?_)
      exact (ht (by simpa using he)).2
    rw [openCount, hfil, htc]
  obtain ⟨t, hts, htoc⟩ := hex
  rw [← htoc, ENNReal.rpow_natCast]
  exact le_iSup (fun F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆ s} =>
    (ENNReal.ofReal τ) ^ openCount F.1 ω) ⟨t, hts⟩

end PercLib.Percolation.Bond.Exploration.BFS
