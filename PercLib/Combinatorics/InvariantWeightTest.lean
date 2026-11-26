/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, using mathlib's orbits of a group action, `ℝ≥0∞`-valued sums and the finite
Cauchy–Schwarz inequality. Mathematical reference: the optimization over invariant edge weights
in the proof of Theorem 3.1 of arXiv:2008.11197v2. No source text or code is copied.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Invariant weighted tests for a square sum

Let a group `Γ` act on a type `X`, let `E` be an invariant set and `S ⊆ E` a set meeting every
orbit in a finite set, and let `a : X → ℝ≥0∞` be invariant on `E`. Then
`∑_{x ∈ S} a x ^ 2 ≤ B ^ 2` if and only if `∑_{x ∈ S} √(w x) a x ≤ B` for every nonnegative
invariant weight `w` supported on finitely many orbits with `∑_{x ∈ S} w x = 1`. The forward
direction is Cauchy–Schwarz; the converse tests the weights `1 / m` on one orbit (to see that
`a` is finite on `S`) and `w ∝ a ^ 2` on finite unions of orbits.

For a graph, `X = Sym2 V`, `E` the edge set and `S` the edges at a root. In `ℝ≥0∞` one has
`0 * ⊤ = 0`, so terms with `w x = 0` contribute nothing to the test sum, whatever `a x` is.

## Main results

* `PercLib.tsum_sq_le_sq_iff_forall_invariant_weight`: the characterization for a group action.
* `SimpleGraph.tsum_incidenceSet_sq_le_sq_iff_forall_invariant_weight`: the same for the edges
  at a root of a simple graph on which `Γ` acts by automorphisms.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal
open MulAction

namespace PercLib

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

/-- A sum over a set `S` of a function vanishing on `S \ T`, for a finite `T ⊆ S`, is the
finite sum over `T`. -/
theorem tsum_subtype_eq_sum_of_eq_zero {S : Set X} {T : Finset X} (hTS : ↑T ⊆ S)
    {h : X → ℝ≥0∞} (h0 : ∀ x ∈ S, x ∉ T → h x = 0) :
    ∑' x : S, h x = ∑ x ∈ T, h x := by
  rw [tsum_subtype S h, tsum_eq_sum (s := T)]
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hTS hx) h
  · intro x hx
    by_cases hS : x ∈ S
    · rw [Set.indicator_of_mem hS]; exact h0 x hS hx
    · exact Set.indicator_of_notMem hS h

/-- A finite set `T ⊆ S` that is closed under passing to points of `S` in the same orbit gives
an admissible test weight `c / ∑_T c` for every coefficient `c` invariant on `E`. -/
theorem sum_sqrt_div_mul_le_of_forall_invariant_weight {E S : Set X}
    (hE : ∀ g : Γ, ∀ x ∈ E, g • x ∈ E) (hSE : S ⊆ E) {a : X → ℝ≥0∞} {B : ℝ≥0}
    (hT : ∀ w : X → ℝ≥0, (∀ g : Γ, ∀ x ∈ E, w (g • x) = w x) →
        (∃ F : Finset X, ↑F ⊆ E ∧ ∀ x ∈ E, w x ≠ 0 → ∃ f ∈ F, x ∈ orbit Γ f) →
        ∑' x : S, (w x : ℝ≥0∞) = 1 →
        ∑' x : S, (NNReal.sqrt (w x) : ℝ≥0∞) * a x ≤ B)
    (T : Finset X) (hTS : ↑T ⊆ S) (hcl : ∀ t ∈ T, ∀ x ∈ S, x ∈ orbit Γ t → x ∈ T)
    (c : X → ℝ≥0) (hc : ∀ g : Γ, ∀ x ∈ E, c (g • x) = c x) (hZ : ∑ t ∈ T, c t ≠ 0) :
    ∑ t ∈ T, (NNReal.sqrt (c t / ∑ s ∈ T, c s) : ℝ≥0∞) * a t ≤ B := by
  classical
  set Z := ∑ s ∈ T, c s
  let w : X → ℝ≥0 := fun y => if y ∈ E ∧ ∃ t ∈ T, y ∈ orbit Γ t then c y / Z else 0
  have hwS : ∀ x ∈ S, w x = if x ∈ T then c x / Z else 0 := by
    intro x hx
    by_cases hxT : x ∈ T
    · have hc : x ∈ E ∧ ∃ t ∈ T, x ∈ orbit Γ t := ⟨hSE hx, x, hxT, mem_orbit_self x⟩
      simp only [w, hxT, ↓reduceIte]
      exact ite_eq_left_iff.2 fun h => absurd hc h
    · have hc : ¬ (x ∈ E ∧ ∃ t ∈ T, x ∈ orbit Γ t) := by
        rintro ⟨-, t, ht, hxt⟩
        exact hxT (hcl t ht x hx hxt)
      simp only [w, hxT, ↓reduceIte]
      exact ite_eq_right_iff.2 fun h => absurd h hc
  have hw := hT w ?_ ?_ ?_
  · rwa [tsum_subtype_eq_sum_of_eq_zero (h := fun x => (NNReal.sqrt (w x) : ℝ≥0∞) * a x) hTS,
      Finset.sum_congr rfl] at hw
    · intro t ht; simp [hwS t (hTS ht), ht]
    · intro x hx hxT; simp [hwS x hx, hxT]
  · intro g y hy
    have hmem : (∃ t ∈ T, g • y ∈ orbit Γ t) ↔ ∃ t ∈ T, y ∈ orbit Γ t := by
      simp only [← orbit_eq_iff, orbit_smul]
    simp only [w, hmem, hE g y hy, hy, true_and, hc g y hy]
  · refine ⟨T, (hTS.trans hSE), fun y hy hne => ?_⟩
    by_contra hno
    have hc : ¬ (y ∈ E ∧ ∃ t ∈ T, y ∈ orbit Γ t) := fun h => hno h.2
    exact hne (ite_eq_right_iff.2 fun h => absurd h hc)
  · rw [tsum_subtype_eq_sum_of_eq_zero (h := fun x => (w x : ℝ≥0∞)) hTS]
    · rw [Finset.sum_congr rfl (g := fun t => ((c t / Z : ℝ≥0) : ℝ≥0∞))
          (fun t ht => by simp [hwS t (hTS ht), ht]),
        ← ENNReal.ofNNReal_finsetSum, ← Finset.sum_div, div_self hZ, ENNReal.coe_one]
    · intro x hx hxT; simp [hwS x hx, hxT]

/-- Points of `S` in the orbits of the points of a finite set form a finite set, closed under
passing to points of `S` in the same orbit. -/
theorem exists_finset_orbit_closed {S : Set X} (hfin : ∀ x ∈ S, (orbit Γ x ∩ S).Finite)
    (s : Finset X) (hs : ↑s ⊆ S) :
    ∃ T : Finset X, s ⊆ T ∧ ↑T ⊆ S ∧ ∀ t ∈ T, ∀ x ∈ S, x ∈ orbit Γ t → x ∈ T := by
  classical
  let U : X → Finset X := fun x => if hx : x ∈ S then (hfin x hx).toFinset else ∅
  refine ⟨s.biUnion U, fun x hx => Finset.mem_biUnion.2 ⟨x, hx, ?_⟩, ?_, ?_⟩
  · simp only [U, hs hx, ↓reduceDIte, Set.Finite.mem_toFinset]
    exact ⟨mem_orbit_self x, hs hx⟩
  · intro y hy
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.1 hy
    simp only [U, hs hx, ↓reduceDIte, Set.Finite.mem_toFinset] at hy
    exact hy.2
  · intro t ht y hy hyt
    obtain ⟨x, hx, ht⟩ := Finset.mem_biUnion.1 ht
    refine Finset.mem_biUnion.2 ⟨x, hx, ?_⟩
    simp only [U, hs hx, ↓reduceDIte, Set.Finite.mem_toFinset] at ht ⊢
    exact ⟨(orbit_eq_iff.2 ht.1) ▸ hyt, hy⟩

/-- **Invariant weighted tests characterize a square sum.** Let `Γ` act on `X`, let `E` be
invariant and `S ⊆ E` meet each orbit of its points in a finite set, and let `a` be invariant on
`E`. Then `∑_{x ∈ S} a x ^ 2 ≤ B ^ 2` if and only if `∑_{x ∈ S} √(w x) a x ≤ B` for every
nonnegative weight `w`, invariant on `E` and supported on finitely many orbits of points of `E`,
with `∑_{x ∈ S} w x = 1`. -/
theorem tsum_sq_le_sq_iff_forall_invariant_weight {E S : Set X}
    (hE : ∀ g : Γ, ∀ x ∈ E, g • x ∈ E) (hSE : S ⊆ E)
    (hfin : ∀ x ∈ S, (orbit Γ x ∩ S).Finite)
    {a : X → ℝ≥0∞} (ha : ∀ g : Γ, ∀ x ∈ E, a (g • x) = a x) (B : ℝ≥0) :
    ∑' x : S, a x ^ 2 ≤ (B : ℝ≥0∞) ^ 2 ↔
      ∀ w : X → ℝ≥0, (∀ g : Γ, ∀ x ∈ E, w (g • x) = w x) →
        (∃ F : Finset X, ↑F ⊆ E ∧ ∀ x ∈ E, w x ≠ 0 → ∃ f ∈ F, x ∈ orbit Γ f) →
        ∑' x : S, (w x : ℝ≥0∞) = 1 →
        ∑' x : S, (NNReal.sqrt (w x) : ℝ≥0∞) * a x ≤ B := by
  classical
  constructor
  · intro h w _ _ hw
    have hB : ((B : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
    have hfa : ∀ x : S, a x ≠ ⊤ := fun x hx => by
      have := (ENNReal.le_tsum (f := fun x : S => a x ^ 2) x).trans h
      rw [hx] at this; simp at this
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hsw : ∑ x ∈ s, w x ≤ 1 := by
      rw [← ENNReal.coe_le_coe, ENNReal.ofNNReal_finsetSum, ENNReal.coe_one, ← hw]
      exact ENNReal.sum_le_tsum s
    have hsa : ∑ x ∈ s, (a x).toNNReal ^ 2 ≤ B ^ 2 := by
      rw [← ENNReal.coe_le_coe, ENNReal.ofNNReal_finsetSum, ENNReal.coe_pow]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
        ((ENNReal.sum_le_tsum s).trans h)
      rw [ENNReal.coe_pow, ENNReal.coe_toNNReal (hfa x)]
    have hcs :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun x => NNReal.sqrt (w x)) (fun x => (a x).toNNReal)
    simp only [NNReal.sq_sqrt] at hcs
    have key : ∑ x ∈ s, NNReal.sqrt (w x) * (a x).toNNReal ≤ B := by
      refine le_of_pow_le_pow_left₀ two_ne_zero zero_le (hcs.trans ?_)
      simpa using mul_le_mul' hsw hsa
    calc ∑ x ∈ s, (NNReal.sqrt (w x) : ℝ≥0∞) * a x
        = ((∑ x ∈ s, NNReal.sqrt (w x) * (a x).toNNReal : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.ofNNReal_finsetSum]
          exact Finset.sum_congr rfl fun x _ => by
            rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (hfa x)]
      _ ≤ B := ENNReal.coe_le_coe.2 key
  · intro hT
    have hTest := sum_sqrt_div_mul_le_of_forall_invariant_weight hE hSE hT
    -- every coefficient on `S` is finite: test the uniform weight on one orbit
    have hfa : ∀ x ∈ S, a x ≠ ⊤ := by
      intro x hx htop
      obtain ⟨T, hsT, hTS, hcl⟩ := exists_finset_orbit_closed hfin {x} (by simpa using hx)
      have hxT : x ∈ T := hsT (Finset.mem_singleton_self x)
      have hZ : ∑ t ∈ T, (1 : ℝ≥0) ≠ 0 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hxT)
      have h1 := hTest T hTS hcl (fun _ => 1) (fun _ _ _ => rfl) hZ
      have h2 := (Finset.single_le_sum (f := fun t => (NNReal.sqrt
        (1 / ∑ s ∈ T, (1 : ℝ≥0)) : ℝ≥0∞) * a t) (fun _ _ => zero_le) hxT).trans h1
      rw [htop, ENNReal.mul_top] at h2
      · exact ENNReal.coe_ne_top (top_le_iff.1 h2)
      · simpa using hZ
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    obtain ⟨T, hsT, hTS, hcl⟩ := exists_finset_orbit_closed hfin (s.map (Function.Embedding.subtype
      _)) (by intro y hy; obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hy; exact x.2)
    let c : X → ℝ≥0 := fun y => (a y).toNNReal ^ 2
    have hcT : ∀ t ∈ T, (c t : ℝ≥0∞) = a t ^ 2 := fun t ht => by
      simp only [c, ENNReal.coe_pow, ENNReal.coe_toNNReal (hfa t (hTS ht))]
    have hsum : ∑ x ∈ s, a x ^ 2 ≤ ((∑ t ∈ T, c t : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofNNReal_finsetSum, Finset.sum_congr rfl hcT]
      calc ∑ x ∈ s, a x ^ 2 = ∑ y ∈ s.map (Function.Embedding.subtype _), a y ^ 2 := by
            rw [Finset.sum_map]; rfl
        _ ≤ _ := Finset.sum_le_sum_of_subset hsT
    refine hsum.trans ?_
    rcases eq_or_ne (∑ t ∈ T, c t) 0 with hZ | hZ
    · rw [hZ]; simp
    have h1 := hTest T hTS hcl c (fun g y hy => by simp only [c, ha g y hy]) hZ
    set Z := ∑ t ∈ T, c t with hZdef
    have hval : ∑ t ∈ T, (NNReal.sqrt (c t / Z) : ℝ≥0∞) * a t = (NNReal.sqrt Z : ℝ≥0∞) := by
      have hsZ : NNReal.sqrt Z ≠ 0 := by simpa using hZ
      have hdiv : Z / NNReal.sqrt Z = NNReal.sqrt Z := by
        rw [div_eq_iff hsZ, ← sq, NNReal.sq_sqrt]
      rw [← hdiv, show Z / NNReal.sqrt Z = ∑ t ∈ T, c t / NNReal.sqrt Z from
        Finset.sum_div _ _ _, ENNReal.ofNNReal_finsetSum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [← ENNReal.coe_toNNReal (hfa t (hTS ht)), ← ENNReal.coe_mul, ENNReal.coe_inj,
        NNReal.sqrt_div, show c t = (a t).toNNReal ^ 2 from rfl, NNReal.sqrt_sq,
        div_mul_eq_mul_div, ← sq]
    rw [hval] at h1
    have h2 : NNReal.sqrt Z ≤ B := ENNReal.coe_le_coe.1 h1
    rw [← ENNReal.coe_pow, ENNReal.coe_le_coe]
    exact NNReal.sqrt_le_iff_le_sq.1 h2

end PercLib

namespace SimpleGraph

variable {V Γ : Type*} [Group Γ] [MulAction Γ V]

/-- **Invariant weighted tests characterize the root-edge square sum.** Let `Γ` act on the
vertices of a simple graph `G` by automorphisms, fix a root `o`, and suppose each edge orbit
meets the set of edges at `o` in a finite set. For `a : Sym2 V → ℝ≥0∞` invariant on edges and
`B : ℝ≥0`, `∑_{e ∋ o} a e ^ 2 ≤ B ^ 2` if and only if `∑_{e ∋ o} √(w e) a e ≤ B` for every
nonnegative weight `w`, invariant on edges and supported on finitely many edge orbits, with
`∑_{e ∋ o} w e = 1`. Terms with `w e = 0` vanish in `ℝ≥0∞` since `0 * ⊤ = 0`. Neither
transitivity nor countability is needed. -/
theorem tsum_incidenceSet_sq_le_sq_iff_forall_invariant_weight (G : SimpleGraph V)
    (hG : ∀ (g : Γ) (x y : V), G.Adj (g • x) (g • y) ↔ G.Adj x y) (o : V)
    (hfin : ∀ e ∈ G.edgeSet,
      {f ∈ G.incidenceSet o | ∃ g : Γ, Sym2.map (g • ·) e = f}.Finite)
    {a : Sym2 V → ℝ≥0∞} (ha : ∀ g : Γ, ∀ e ∈ G.edgeSet, a (Sym2.map (g • ·) e) = a e)
    (B : ℝ≥0) :
    ∑' e : G.incidenceSet o, a e ^ 2 ≤ (B : ℝ≥0∞) ^ 2 ↔
      ∀ w : Sym2 V → ℝ≥0, (∀ g : Γ, ∀ e ∈ G.edgeSet, w (Sym2.map (g • ·) e) = w e) →
        (∃ F : Finset (Sym2 V), ↑F ⊆ G.edgeSet ∧
          ∀ e ∈ G.edgeSet, w e ≠ 0 → ∃ f ∈ F, ∃ g : Γ, Sym2.map (g • ·) f = e) →
        ∑' e : G.incidenceSet o, (w e : ℝ≥0∞) = 1 →
        ∑' e : G.incidenceSet o, (NNReal.sqrt (w e) : ℝ≥0∞) * a e ≤ B := by
  let _ : MulAction Γ (Sym2 V) :=
    { smul := fun g => Sym2.map (g • ·)
      one_smul := fun e => by
        change Sym2.map _ e = e
        simp only [one_smul, Sym2.map_id', id]
      mul_smul := fun g h e => by
        change Sym2.map _ e = Sym2.map _ (Sym2.map _ e)
        rw [Sym2.map_map]; congr 1; funext x; exact mul_smul g h x }
  have hE : ∀ g : Γ, ∀ e ∈ G.edgeSet, g • e ∈ G.edgeSet := by
    intro g e he
    induction e using Sym2.ind with
    | _ x y =>
      change Sym2.map _ s(x, y) ∈ G.edgeSet
      simpa [hG] using he
  have hfin' : ∀ e ∈ G.incidenceSet o, (MulAction.orbit Γ e ∩ G.incidenceSet o).Finite :=
    fun e he => (hfin e he.1).subset fun f hf => ⟨hf.2, hf.1⟩
  exact PercLib.tsum_sq_le_sq_iff_forall_invariant_weight hE (fun e he => he.1) hfin' ha B

end SimpleGraph
