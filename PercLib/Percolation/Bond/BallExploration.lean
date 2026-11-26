/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.IntrinsicBalls
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Percolation.Bond.IntrinsicGrowth

/-!
# Ball exploration and the spatial Markov property

Intrinsic distance is `SimpleGraph.edist (openGraph ω)`. For `A ⊆ V`, the pairs touching `A`
are `{e | ∃ a ∈ A, a ∈ e}` and the configuration outside `A` is `ω ∩ {e | ∀ a ∈ A, a ∉ e}`.

1. `ball_iff_of_inter_eq` (**ball exploration**): if `B_ω(o, r) ⊆ A` and `ω`, `ω'` agree on the
   pairs touching `A`, they have the same balls of radius `≤ r + 1`. Hence the events
   `{B_ω(o, r) = A}` and `{B_ω(o, r) = A, edist o x = r + 1}` are determined by those pairs
   (`determined_ball_eq`, `determined_ball_eq_sphere`).
2. `ball_covering` (**pointwise covering**): on `{B_ω(o, r) = A}`, every `y` within distance
   `r + 1 + k` of `o` is within `r + 1`, or within `k` of some `x` at distance `r + 1`, in the
   configuration outside `A`.
3. `law_inter_outside_eq` (**spatial Markov property**): the event of 1 is independent of every
   event of the configuration outside `A`.
4. `renewal_ball` (**renewal inequality**): if `B_ω(o, r)` is finite almost surely and every
   ball of radius `k` has mean at most `b`, then
   `E|B(o, r+1+k)| ≤ E|B(o, r+1)| + E|S(o, r+1)| · b`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### 1. Ball exploration -/

/-- Pairs touching `A`. -/
theorem mem_touching_iff (A : Set V) (a b : V) :
    s(a, b) ∈ {e : Sym2 V | ∃ c ∈ A, c ∈ e} ↔ a ∈ A ∨ b ∈ A := by
  simp only [Set.mem_ofPred_eq, Sym2.mem_iff]
  constructor
  · rintro ⟨c, hc, rfl | rfl⟩
    · exact Or.inl hc
    · exact Or.inr hc
  · rintro (h | h)
    · exact ⟨a, h, Or.inl rfl⟩
    · exact ⟨b, h, Or.inr rfl⟩

/-- **Ball exploration.** If `B_ω(o, r) ⊆ A` and `ω`, `ω'` agree on the pairs touching `A`, then
the balls of radius `k ≤ r + 1` of `ω` and `ω'` agree. -/
theorem ball_iff_of_inter_eq {A : Set V} {ω ω' : Config V}
    (h : ω ∩ {e | ∃ a ∈ A, a ∈ e} = ω' ∩ {e | ∃ a ∈ A, a ∈ e}) (o : V) {r : ℕ}
    (hA : ∀ y, (openGraph ω).edist o y ≤ r → y ∈ A) :
    ∀ k : ℕ, k ≤ r + 1 → ∀ y, (openGraph ω).edist o y ≤ k ↔ (openGraph ω').edist o y ≤ k := by
  -- adjacency at a vertex of `A`
  have hadj : ∀ z y, z ∈ A → ((openGraph ω).Adj z y ↔ (openGraph ω').Adj z y) := by
    intro z y hz
    rw [openGraph_adj_iff, openGraph_adj_iff]
    have hmem : s(z, y) ∈ {e : Sym2 V | ∃ a ∈ A, a ∈ e} := (mem_touching_iff A z y).2 (Or.inl hz)
    have : s(z, y) ∈ ω ↔ s(z, y) ∈ ω' := by
      constructor
      · intro hz'
        have : s(z, y) ∈ ω ∩ {e | ∃ a ∈ A, a ∈ e} := ⟨hz', hmem⟩
        rw [h] at this; exact this.1
      · intro hz'
        have : s(z, y) ∈ ω' ∩ {e | ∃ a ∈ A, a ∈ e} := ⟨hz', hmem⟩
        rw [← h] at this; exact this.1
    rw [this]
  intro k
  induction k with
  | zero =>
    intro _ y
    simp only [Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff]
  | succ k ih =>
    intro hk y
    have ih' := ih (by omega)
    rw [edist_le_succ_iff, edist_le_succ_iff]
    refine or_congr Iff.rfl ⟨fun ⟨z, hzy, hz⟩ => ⟨z, ?_, (ih' z).1 hz⟩,
      fun ⟨z, hzy, hz⟩ => ⟨z, ?_, (ih' z).2 hz⟩⟩
    · exact (hadj z y (hA z (hz.trans (by exact_mod_cast (show k ≤ r by omega))))).1 hzy
    · have hz' := (ih' z).2 hz
      exact (hadj z y (hA z (hz'.trans (by exact_mod_cast (show k ≤ r by omega))))).2 hzy

/-- `edist = r + 1` as a difference of balls. -/
theorem edist_eq_succ_iff (G : SimpleGraph V) (o x : V) (r : ℕ) :
    G.edist o x = ((r + 1 : ℕ) : ℕ∞) ↔ G.edist o x ≤ ((r + 1 : ℕ) : ℕ∞) ∧
      ¬ G.edist o x ≤ (r : ℕ∞) := by
  constructor
  · intro h
    rw [h]
    exact ⟨le_rfl, by norm_cast; omega⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    rw [not_le] at h2
    have := Order.add_one_le_of_lt h2
    exact_mod_cast this

/-- **Determinism of the exploration.** The event `{B_ω(o, r) = A}` is determined by the pairs
touching `A`. -/
theorem determined_ball_eq (A : Set V) (o : V) (r : ℕ) :
    ∀ ω ω' : Config V, ω ∩ {e | ∃ a ∈ A, a ∈ e} = ω' ∩ {e | ∃ a ∈ A, a ∈ e} →
      (ω ∈ {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A} ↔
        ω' ∈ {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A}) := by
  have key : ∀ ω ω' : Config V, ω ∩ {e | ∃ a ∈ A, a ∈ e} = ω' ∩ {e | ∃ a ∈ A, a ∈ e} →
      {y | (openGraph ω).edist o y ≤ r} = A → {y | (openGraph ω').edist o y ≤ r} = A := by
    intro ω ω' h hω
    have hA : ∀ y, (openGraph ω).edist o y ≤ r → y ∈ A := fun y hy => hω ▸ hy
    rw [← hω]
    ext y
    exact ((ball_iff_of_inter_eq h o hA r (by omega) y)).symm
  intro ω ω' h
  exact ⟨key ω ω' h, key ω' ω h.symm⟩

/-- **Determinism of the exploration, with the next sphere.** The event
`{B_ω(o, r) = A, edist o x = r + 1}` is determined by the pairs touching `A`. -/
theorem determined_ball_eq_sphere (A : Set V) (o x : V) (r : ℕ) :
    ∀ ω ω' : Config V, ω ∩ {e | ∃ a ∈ A, a ∈ e} = ω' ∩ {e | ∃ a ∈ A, a ∈ e} →
      (ω ∈ {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A ∧
          (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} ↔
        ω' ∈ {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A ∧
          (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)}) := by
  have key : ∀ ω ω' : Config V, ω ∩ {e | ∃ a ∈ A, a ∈ e} = ω' ∩ {e | ∃ a ∈ A, a ∈ e} →
      ({y | (openGraph ω).edist o y ≤ r} = A ∧ (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)) →
      ({y | (openGraph ω').edist o y ≤ r} = A ∧
        (openGraph ω').edist o x = ((r + 1 : ℕ) : ℕ∞)) := by
    intro ω ω' h ⟨hω, hx⟩
    have hA : ∀ y, (openGraph ω).edist o y ≤ r → y ∈ A := fun y hy => hω ▸ hy
    have hb := ball_iff_of_inter_eq h o hA
    refine ⟨(determined_ball_eq A o r ω ω' h).1 hω, ?_⟩
    rw [edist_eq_succ_iff] at hx ⊢
    have h1 := hb (r + 1) le_rfl x
    have h2 := hb r (by omega) x
    push_cast at h1 hx ⊢
    exact ⟨h1.1 hx.1, fun h' => hx.2 (h2.2 h')⟩
  intro ω ω' h
  exact ⟨key ω ω' h, key ω' ω h.symm⟩

/-! ### 2. Pointwise covering -/

/-- **Pointwise covering.** If `B_ω(o, r) = A`, every vertex within distance `r + 1 + k` of `o`
is within `r + 1`, or within `k` of some vertex at distance `r + 1` in the configuration
outside `A`. -/
theorem ball_covering {ω : Config V} {o : V} {r : ℕ} {A : Set V}
    (hω : {y | (openGraph ω).edist o y ≤ r} = A) :
    ∀ k : ℕ, ∀ y, (openGraph ω).edist o y ≤ ((r + 1 + k : ℕ) : ℕ∞) →
      (openGraph ω).edist o y ≤ ((r + 1 : ℕ) : ℕ∞) ∨
      ∃ x, (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞) ∧
        (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist x y ≤ k := by
  have hmemA : ∀ z, z ∈ A ↔ (openGraph ω).edist o z ≤ r := fun z => by rw [← hω]; rfl
  -- an open edge `z y` with both ends outside `A` is open outside `A`
  have hout : ∀ z y, (openGraph ω).Adj z y → z ∉ A → y ∉ A →
      (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).Adj z y := by
    intro z y hzy hz hy
    rw [openGraph_adj_iff] at hzy ⊢
    refine ⟨⟨hzy.1, fun a ha hae => ?_⟩, hzy.2⟩
    rcases Sym2.mem_iff.1 hae with rfl | rfl
    · exact hz ha
    · exact hy ha
  -- an adjacent vertex is at most one step further
  have hstep : ∀ z y, (openGraph ω).Adj z y → (openGraph ω).edist o z ≤ r →
      (openGraph ω).edist o y ≤ ((r + 1 : ℕ) : ℕ∞) := by
    intro z y hzy hz
    calc (openGraph ω).edist o y ≤ (openGraph ω).edist o z + (openGraph ω).edist z y :=
          SimpleGraph.edist_triangle
      _ ≤ r + 1 := add_le_add hz (SimpleGraph.edist_eq_one_iff_adj.2 hzy).le
      _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  intro k
  induction k with
  | zero => intro y hy; exact Or.inl (by simpa using hy)
  | succ k ih =>
    intro y hy
    by_cases hyr : (openGraph ω).edist o y ≤ ((r + 1 : ℕ) : ℕ∞)
    · exact Or.inl hyr
    right
    have hyA : y ∉ A := fun h => hyr (((hmemA y).1 h).trans (by exact_mod_cast Nat.le_succ r))
    rw [show r + 1 + (k + 1) = (r + 1 + k) + 1 by ring, edist_le_succ_iff] at hy
    rcases hy with rfl | ⟨z, hzy, hz⟩
    · exact absurd (by simp) hyr
    have hzA : z ∉ A := fun h => hyr (hstep z y hzy ((hmemA z).1 h))
    rcases ih z hz with hz1 | ⟨x, hx, hxz⟩
    · -- `z` is at distance exactly `r + 1`
      refine ⟨z, ?_, ?_⟩
      · rw [edist_eq_succ_iff]
        exact ⟨hz1, fun h => hzA ((hmemA z).2 h)⟩
      · calc (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist z y = 1 :=
            SimpleGraph.edist_eq_one_iff_adj.2 (hout z y hzy hzA hyA)
          _ ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left 1 k
    · refine ⟨x, hx, ?_⟩
      calc (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist x y
          ≤ (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist x z +
            (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist z y := SimpleGraph.edist_triangle
        _ ≤ k + 1 := add_le_add hxz
            (SimpleGraph.edist_eq_one_iff_adj.2 (hout z y hzy hzA hyA)).le
        _ = ((k + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-! ### 3. The spatial Markov property -/

section Markov

variable [Countable V]

theorem measurableSet_edist_eq_succ (o x : V) (r : ℕ) :
    MeasurableSet {ω : Config V | (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} := by
  have : {ω : Config V | (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} =
      {ω | (openGraph ω).edist o x ≤ (r + 1 : ℕ)} \ {ω | (openGraph ω).edist o x ≤ r} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, edist_eq_succ_iff]
  rw [this]
  exact (measurableSet_edist_le o x (r + 1)).diff (measurableSet_edist_le o x r)

theorem measurableSet_ball_eq (A : Set V) (o : V) (r : ℕ) :
    MeasurableSet {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A} := by
  have : {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A} =
      ⋂ y, {ω | (openGraph ω).edist o y ≤ r ↔ y ∈ A} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.ext_iff]
  rw [this]
  refine MeasurableSet.iInter fun y => ?_
  by_cases hy : y ∈ A
  · simp only [hy, iff_true]; exact measurableSet_edist_le o y r
  · simp only [hy, iff_false]; exact (measurableSet_edist_le o y r).compl

theorem measurableSet_edist_outside (A : Set V) (u y : V) (k : ℕ) :
    MeasurableSet {ω : Config V |
      (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist u y ≤ k} :=
  (measurableSet_edist_le u y k).preimage
    (by fun_prop : Measurable fun ω : Config V => ω ∩ {e | ∀ a ∈ A, a ∉ e})

/-- **Spatial Markov property.** The exploration event `{B_ω(o, r) = A, edist o x = r + 1}` is
independent of every distance event of the configuration outside `A`. -/
theorem law_inter_outside_eq (q : Sym2 V → unitInterval) (A : Set V) (o x u y : V)
    (r k : ℕ) :
    law q ({ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A ∧
        (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} ∩
      {ω | (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist u y ≤ k}) =
    law q {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A ∧
        (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} *
      law q {ω | (openGraph (ω ∩ {e | ∀ a ∈ A, a ∉ e})).edist u y ≤ k} := by
  refine PercLib.Probability.prodBernoulli_inter_of_determined q
    (P := {e | ∃ a ∈ A, a ∈ e}) (Q := {e | ∀ a ∈ A, a ∉ e}) ?_ ?_
    (measurableSet_edist_outside A u y k) (determined_ball_eq_sphere A o x r) ?_
  · rw [Set.disjoint_left]
    rintro e ⟨a, ha, hae⟩ h
    exact h a ha hae
  · have : {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = A ∧
        (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} =
        {ω | {y | (openGraph ω).edist o y ≤ r} = A} ∩
          {ω | (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} := rfl
    rw [this]
    exact (measurableSet_ball_eq A o r).inter (measurableSet_edist_eq_succ o x r)
  · intro ω ω' h
    simp only [Set.mem_ofPred_eq, h]

/-! ### 4. The renewal inequality -/

/-- The expected sphere volume is the sum of the sphere probabilities. -/
theorem lintegral_encard_sphere (μ : Measure (Config V)) (o : V) (r : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y = ((r + 1 : ℕ) : ℕ∞)} : Set V).encard : ℝ≥0∞) ∂μ =
      ∑' y, μ {ω | (openGraph ω).edist o y = ((r + 1 : ℕ) : ℕ∞)} := by
  have hpt : ∀ ω : Config V,
      (({y | (openGraph ω).edist o y = ((r + 1 : ℕ) : ℕ∞)} : Set V).encard : ℝ≥0∞) =
      ∑' y, {ω' : Config V | (openGraph ω').edist o y = ((r + 1 : ℕ) : ℕ∞)}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    classical
    rw [← ENNReal.tsum_set_one, tsum_subtype ({y | (openGraph ω).edist o y =
      ((r + 1 : ℕ) : ℕ∞)} : Set V) (fun _ => (1 : ℝ≥0∞))]
    congr 1
  simp_rw [hpt]
  rw [lintegral_tsum fun y =>
    (measurable_const.indicator (measurableSet_edist_eq_succ o y r)).aemeasurable]
  exact tsum_congr fun y => lintegral_indicator_one (measurableSet_edist_eq_succ o y r)

/-- **Renewal inequality.** If `B_ω(o, r)` is finite almost surely and every ball of radius `k`
has mean at most `b`, then `E|B(o, r+1+k)| ≤ E|B(o, r+1)| + E|S(o, r+1)| · b`. -/
theorem renewal_ball (q : Sym2 V → unitInterval) (o : V) (r k : ℕ)
    (hfin : ∀ᵐ ω ∂law q, ({y | (openGraph ω).edist o y ≤ r} : Set V).Finite) {b : ℝ≥0∞}
    (hb : ∀ x, ∫⁻ ω, (({y | (openGraph ω).edist x y ≤ k} : Set V).encard : ℝ≥0∞) ∂law q ≤ b) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ (r + 1 + k : ℕ)} : Set V).encard : ℝ≥0∞) ∂law q ≤
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} : Set V).encard : ℝ≥0∞) ∂law q +
        (∫⁻ ω, (({y | (openGraph ω).edist o y = ((r + 1 : ℕ) : ℕ∞)} : Set V).encard : ℝ≥0∞)
          ∂law q) * b := by
  classical
  set F : Finset V → V → Set (Config V) := fun A x =>
    {ω : Config V | {y | (openGraph ω).edist o y ≤ r} = (A : Set V) ∧
      (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} with hF
  set Out : Finset V → V → V → Set (Config V) := fun A x y =>
    {ω | (openGraph (ω ∩ {e | ∀ a ∈ (A : Set V), a ∉ e})).edist x y ≤ k} with hOut
  -- the covering, almost surely
  have hcov : ∀ y, {ω : Config V | (openGraph ω).edist o y ≤ (r + 1 + k : ℕ)} ≤ᵐ[law q]
      ({ω | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} ∪
        ⋃ A : Finset V, ⋃ x : V, (F A x ∩ Out A x y) : Set (Config V)) := by
    intro y
    filter_upwards [hfin] with ω hω hy
    have hA : {z | (openGraph ω).edist o z ≤ r} = ((hω.toFinset : Finset V) : Set V) := by
      simp
    rcases ball_covering hA k y hy with h | ⟨x, hx, hxy⟩
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.2 ⟨hω.toFinset, Set.mem_iUnion.2 ⟨x, ⟨hA, hx⟩, hxy⟩⟩)
  -- the bound for each `y`
  have hy : ∀ y, law q {ω : Config V | (openGraph ω).edist o y ≤ (r + 1 + k : ℕ)} ≤
      law q {ω | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} +
        ∑' A : Finset V, ∑' x : V, law q (F A x) *
          law q {ω | (openGraph ω).edist x y ≤ k} := by
    intro y
    refine (measure_mono_ae (hcov y)).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun A => ?_)
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun x => ?_)
    rw [hF, hOut, law_inter_outside_eq]
    refine mul_le_mul' le_rfl (measure_mono fun ω hω => ?_)
    exact (SimpleGraph.edist_anti (fun a b hab => by
      rw [openGraph_adj_iff] at hab ⊢
      exact ⟨hab.1.1, hab.2⟩)).trans hω
  -- sum over `y`
  rw [lintegral_encard_ball, lintegral_encard_ball, lintegral_encard_sphere]
  calc ∑' y, law q {ω : Config V | (openGraph ω).edist o y ≤ (r + 1 + k : ℕ)}
      ≤ ∑' y, (law q {ω | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} +
        ∑' A : Finset V, ∑' x : V, law q (F A x) *
          law q {ω | (openGraph ω).edist x y ≤ k}) := ENNReal.tsum_le_tsum hy
    _ = ∑' y, law q {ω | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} +
        ∑' x : V, ∑' A : Finset V, law q (F A x) *
          ∑' y, law q {ω | (openGraph ω).edist x y ≤ k} := by
        rw [ENNReal.tsum_add]
        congr 1
        calc ∑' y, ∑' A : Finset V, ∑' x : V, law q (F A x) *
              law q {ω | (openGraph ω).edist x y ≤ k}
            = ∑' y, ∑' x : V, ∑' A : Finset V, law q (F A x) *
              law q {ω | (openGraph ω).edist x y ≤ k} := tsum_congr fun y => ENNReal.tsum_comm
          _ = ∑' x : V, ∑' y, ∑' A : Finset V, law q (F A x) *
              law q {ω | (openGraph ω).edist x y ≤ k} := ENNReal.tsum_comm
          _ = ∑' x : V, ∑' A : Finset V, ∑' y, law q (F A x) *
              law q {ω | (openGraph ω).edist x y ≤ k} := tsum_congr fun x => ENNReal.tsum_comm
          _ = _ := tsum_congr fun x => tsum_congr fun A => ENNReal.tsum_mul_left
    _ ≤ ∑' y, law q {ω | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} +
        ∑' x : V, law q {ω | (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} * b := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun x => ?_)
        calc ∑' A : Finset V, law q (F A x) * ∑' y, law q {ω | (openGraph ω).edist x y ≤ k}
            ≤ ∑' A : Finset V, law q (F A x) * b := ENNReal.tsum_le_tsum fun A =>
              mul_le_mul' le_rfl (by rw [← lintegral_encard_ball]; exact hb x)
          _ = (∑' A : Finset V, law q (F A x)) * b := ENNReal.tsum_mul_right
          _ ≤ law q {ω | (openGraph ω).edist o x = ((r + 1 : ℕ) : ℕ∞)} * b := by
              refine mul_le_mul' ?_ le_rfl
              refine (tsum_meas_le_meas_iUnion_of_disjoint _ (fun A =>
                (measurableSet_ball_eq _ o r).inter (measurableSet_edist_eq_succ o x r))
                fun A A' hAA' => ?_).trans (measure_mono ?_)
              · rw [Function.onFun, Set.disjoint_left]
                rintro ω ⟨h1, -⟩ ⟨h2, -⟩
                exact hAA' (Finset.coe_injective (h1.symm.trans h2))
              · exact Set.iUnion_subset fun A ω hω => hω.2
    _ = _ := by rw [ENNReal.tsum_mul_right]

end Markov

/-! ### Non-vacuity witness -/

open Classical in
/-- Balls of a profile with finite row sums are finite almost surely. -/
theorem ae_finite_ball_of_rowSum [Countable V] (q : Sym2 V → unitInterval) {D : ℝ≥0∞}
    (hD : D < ⊤) (hrow : ∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v ≤ D) (o : V)
    (r : ℕ) :
    ∀ᵐ ω ∂law q, ({y | (openGraph ω).edist o y ≤ r} : Set V).Finite := by
  have hlt : ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂law q < ⊤ :=
    (lintegral_encard_ball_le_of_rowSum q D hrow o r).trans_lt
      (ENNReal.sum_lt_top.2 fun j _ => ENNReal.pow_lt_top hD)
  filter_upwards [ae_lt_top (measurable_encard_ball o r) hlt.ne] with ω hω
  exact Set.encard_lt_top_iff.1 (ENat.toENNReal_lt_top.1 hω)

open Classical in
/-- The renewal inequality for the zero profile (on any countable vertex set, e.g. `ℤ`): every
hypothesis holds with `b = 1`. -/
example {W : Type*} [Countable W] (o : W) (r k : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ (r + 1 + k : ℕ)} : Set W).encard : ℝ≥0∞)
        ∂law (fun _ => (0 : unitInterval)) ≤
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} : Set W).encard : ℝ≥0∞)
          ∂law (fun _ => (0 : unitInterval)) +
        (∫⁻ ω, (({y | (openGraph ω).edist o y = ((r + 1 : ℕ) : ℕ∞)} : Set W).encard : ℝ≥0∞)
          ∂law (fun _ => (0 : unitInterval))) * 1 := by
  have hrow : ∀ v : W, rowSum (fun e => unitInterval.toENNReal
      ((fun _ : Sym2 W => (0 : unitInterval)) e)) v ≤ 0 := by
    intro v
    rw [rowSum_toENNReal]
    refine le_of_eq (ENNReal.tsum_eq_zero.2 fun w => ?_)
    split_ifs
    · rfl
    · simp [unitInterval.toNNReal]; rfl
  refine renewal_ball _ o r k (ae_finite_ball_of_rowSum _ ENNReal.zero_lt_top hrow o r)
    fun x => ?_
  refine (lintegral_encard_ball_le_of_rowSum _ 0 hrow x k).trans (le_of_eq ?_)
  rw [Finset.sum_range_succ']
  simp

end PercLib.Percolation.Bond
