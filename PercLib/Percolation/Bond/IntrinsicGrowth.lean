/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.IntrinsicBalls
public import PercLib.Percolation.Bond.RowSum

/-!
# Intrinsic balls: the path-counting upper bound (R5XZ, part 1)

Write `B_ω(o,r) = {y | edist ≤ r}` for the ball of the open graph (mathlib's
`SimpleGraph.edist`, as in `IntrinsicBalls.lean`). If every off-diagonal row sum of `q` is at
most `D`, then `E|B_ω(o,r)| ≤ ∑_{j ≤ r} D^j` (`lintegral_encard_ball_le_of_rowSum`): a vertex
at intrinsic distance at most `r` is the end of an open simple path of length at most `r`
(`edist_le_subset_iUnion_path`), and the weights of such paths are summed by `walkSum`.

`lintegral_encard_ball_le_of_transitive` is the transitive form: for a transitive profile
the bound holds with `D = ∑'_{v ≠ o} q s(o,v)`. It needs neither `D < ⊤` nor `χ = ⊤`.
The lower bounds are in `IntrinsicRenewal.lean`. This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- A vertex at intrinsic distance at most `r` is the end of an open simple path of length at
most `r`. -/
theorem edist_le_subset_iUnion_path (o y : V) (r : ℕ) :
    {ω : Config V | (openGraph ω).edist o y ≤ r} ⊆
      ⋃ p : {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r},
        {ω : Config V | (p.1.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
  intro ω hω
  have hne : (openGraph ω).edist o y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top r) hω
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hlen : w.bypass.length ≤ r := by
    have h1 := w.length_bypass_le_length
    have h2 : (w.length : ℕ∞) ≤ r := hw ▸ hω
    exact h1.trans (by exact_mod_cast h2)
  refine mem_iUnion.2 ⟨⟨⟨w.bypass.mapLe le_top, (w.bypass_isPath).mapLe le_top⟩, by
    simpa using hlen⟩, ?_⟩
  intro e he
  have he1 : e ∈ w.bypass.edges := by simpa using he
  have he' : e ∈ (openGraph ω).edgeSet := w.bypass.edges_subset_edgeSet he1
  exact (show e ∈ ω \ Sym2.diagSet by
    simpa [openGraph, SimpleGraph.edgeSet_fromEdgeSet] using he').1

open Classical in
/-- The ball probability is at most the weight of the simple paths of length at most `r`. -/
theorem law_edist_le_le_tsum_paths [Countable V] (q : Sym2 V → unitInterval) (o y : V)
    (r : ℕ) :
    law q {ω | (openGraph ω).edist o y ≤ r} ≤
      ∑' p : {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r},
        ∏ e ∈ p.1.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
  let : Countable ((⊤ : SimpleGraph V).Walk o y) :=
    Function.Injective.countable SimpleGraph.Walk.support_injective
  calc law q {ω | (openGraph ω).edist o y ≤ r}
      ≤ law q (⋃ p : {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r},
          {ω : Config V | (p.1.1.edges.toFinset : Set (Sym2 V)) ⊆ ω}) :=
        measure_mono (edist_le_subset_iUnion_path o y r)
    _ ≤ ∑' p : {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r},
          law q {ω : Config V | (p.1.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} :=
        measure_iUnion_le _
    _ = _ := by simp only [law, prodBernoulli_subset]

open Classical in
/-- **Upper bound.** If every off-diagonal row sum of `q` is at most `D`, then
`E|B_ω(o,r)| ≤ ∑_{j ≤ r} D^j`. -/
theorem lintegral_encard_ball_le_of_rowSum [Countable V] (q : Sym2 V → unitInterval)
    (D : ℝ≥0∞)
    (hrow : ∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v ≤ D) (o : V) (r : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂law q ≤
      ∑ j ∈ Finset.range (r + 1), D ^ j := by
  set a := offDiagonal (fun v w : V => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))
  set f : List V → ℝ≥0∞ := fun l => if l.length ≤ r then walkWeight a o l.get else 0
  have hinj : Function.Injective
      (fun p : Σ y, {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r} =>
        p.2.1.1.support.tail) := by
    intro p p' h
    have := path_tail_injective o (a₁ := ⟨p.1, p.2.1⟩) (a₂ := ⟨p'.1, p'.2.1⟩) h
    obtain ⟨y, p, hp⟩ := p
    obtain ⟨y', p', hp'⟩ := p'
    simp only [Sigma.mk.injEq] at this
    obtain ⟨rfl, h2⟩ := this
    simp only [heq_eq_eq] at h2
    subst h2
    rfl
  calc ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂law q
      = ∑' y, law q {ω | (openGraph ω).edist o y ≤ r} := lintegral_encard_ball _ o r
    _ ≤ ∑' y, ∑' p : {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r},
          ∏ e ∈ p.1.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun y => law_edist_le_le_tsum_paths q o y r
    _ = ∑' p : Σ y, {p : (⊤ : SimpleGraph V).Path o y // p.1.length ≤ r},
          f p.2.1.1.support.tail := by
        rw [ENNReal.tsum_sigma']
        refine tsum_congr fun y => tsum_congr fun p => ?_
        have hl : p.1.1.support.tail.length ≤ r := by
          rw [List.length_tail, SimpleGraph.Walk.length_support]; simpa using p.2
        simp only [f, hl, ite_true]
        exact path_prod_eq_weight q p.1
    _ ≤ ∑' l : List V, f l := ENNReal.tsum_comp_le_tsum_of_injective hinj f
    _ = ∑' t : Σ n, Fin n → V, (if t.1 ≤ r then walkWeight a o t.2 else 0) :=
        List.equivSigmaTuple.tsum_eq
          (fun t : Σ n, Fin n → V => if t.1 ≤ r then walkWeight a o t.2 else 0)
    _ = ∑' n : ℕ, if n ≤ r then walkSum a n o else 0 := by
        rw [ENNReal.tsum_sigma']
        refine tsum_congr fun n => ?_
        split_ifs with hn
        · rw [walkSum_eq_tsum_walkWeight]
        · simp
    _ = ∑ n ∈ Finset.range (r + 1), walkSum a n o := by
        rw [tsum_eq_sum (s := Finset.range (r + 1)) fun n hn => by
          rw [Finset.mem_range, not_lt] at hn
          simp [show ¬ n ≤ r by omega]]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_range] at hn
        simp [show n ≤ r by omega]
    _ ≤ ∑ j ∈ Finset.range (r + 1), D ^ j :=
        Finset.sum_le_sum fun n _ => walkSum_masked_le_pow _ D hrow n o

open Classical in
/-- Under transitivity of `q` every off-diagonal row sum equals the one at `o`. -/
theorem rowSum_eq_of_transitive_profile (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o v : V) :
    rowSum (fun e => unitInterval.toENNReal (q e)) v =
      rowSum (fun e => unitInterval.toENNReal (q e)) o := by
  obtain ⟨σ, rfl, hσ⟩ := hq o v
  rw [rowSum_toENNReal, rowSum_toENNReal, ← σ.tsum_eq]
  refine tsum_congr fun w => ?_
  simp only [σ.injective.eq_iff]
  congr 3
  rw [← hσ s(o, w), Sym2.map_mk]

/-- **Upper bound, transitive form.** For a transitive profile with
`D = ∑'_{v ≠ o} q s(o,v)`, `E|B_ω(o,r)| ≤ ∑_{j ≤ r} D^j`. -/
theorem lintegral_encard_ball_le_of_transitive [Countable V] (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V) (r : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂law q ≤
      ∑ j ∈ Finset.range (r + 1),
        rowSum (fun e => unitInterval.toENNReal (q e)) o ^ j :=
  lintegral_encard_ball_le_of_rowSum q _
    (fun v => (rowSum_eq_of_transitive_profile q hq o v).le) o r

/-! ### Non-vacuity -/

open Classical in
/-- The nearest-neighbour profile on `ℤ` (open probability `1` on `s(a, a+1)`) is
transitive, so the bound applies with `D = 2`. -/
example (r : ℕ) := lintegral_encard_ball_le_of_transitive
  (fun e : Sym2 ℤ => if ∃ a, e = s(a, a + 1) then (1 : unitInterval) else 0)
  (fun x y => ⟨Equiv.addRight (y - x), by simp, fun e => by
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Equiv.coe_addRight]
      congr 1
      apply propext
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨c - (y - x), ?_⟩
        rcases Sym2.eq_iff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [Sym2.eq_iff]; left; constructor <;> omega
        · rw [Sym2.eq_iff]; right; constructor <;> omega
      · rintro ⟨c, hc⟩
        refine ⟨c + (y - x), ?_⟩
        rcases Sym2.eq_iff.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [Sym2.eq_iff]; left; constructor <;> omega
        · rw [Sym2.eq_iff]; right; constructor <;> omega⟩) 0 r

end PercLib.Percolation.Bond

end
