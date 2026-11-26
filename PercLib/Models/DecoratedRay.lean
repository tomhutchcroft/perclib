/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface and the intensity family `intensityProfile`. The
construction (a ray with pendant paths of length `2^k` and intensity `k^2`) follows the wiki article
on the infinite-cluster zero-one law (tag SA9P). No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Cylinder
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A decorated ray: susceptibility diverges at `log 2` but nothing percolates

Vertices are pairs `(k, j) : ℕ × ℕ`. The *backbone* is `(k, 0)`, `k ∈ ℕ`, with the
edges `s((k, 0), (k + 1, 0))` of intensity `1`; the root is `o = (0, 0)`. At `(k, 0)`,
`k ≥ 1`, hangs a *pendant path* `(k, 0) - (k, 1) - ⋯ - (k, 2^k)` whose edges have intensity
`k^2`. All other pairs have intensity `0`. The intensity is fixed by the hypothesis
`hJ` below (no new definition); `exists_J` shows it is realised.

* `ae_forall_cluster_finite`: for every finite `β`, almost surely every cluster is finite;
  hence `rootCriticalIntensity J o = ⊤` and `globalCriticalIntensity J = ⊤`.
* `chi_lt_top_iff`: `χ_β(o) < ∞ ↔ β < log 2`.
* `exists_decoratedRay`: the existential statement, with the host graph (the comb on
  `ℕ × ℕ`), which is connected and has maximum degree at most three. The host edges
  `s((k, j), (k, j + 1))` with `j ≥ 2^k` or `k = 0` carry intensity `0`.
* `chi_zero`: at `β = 0` the susceptibility is `1`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.DecoratedRay

/-! ### The intensity -/

/-- The four facts about the intensity used below. -/
theorem J_facts (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ : ∀ u v : ℕ × ℕ, J s(u, v) =
      (if u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1 then 1 else 0) +
      (if v.1 = u.1 ∧ 1 ≤ u.1 ∧ v.2 = u.2 + 1 ∧ v.2 ≤ 2 ^ u.1 then (u.1 : ℝ≥0) ^ 2 else 0) +
      (if v.2 = 0 ∧ u.2 = 0 ∧ u.1 = v.1 + 1 then 1 else 0) +
      (if u.1 = v.1 ∧ 1 ≤ v.1 ∧ u.2 = v.2 + 1 ∧ u.2 ≤ 2 ^ v.1 then (v.1 : ℝ≥0) ^ 2 else 0)) :
    (∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1) ∧
    (∀ a b : ℕ, 1 ≤ a → b + 1 ≤ 2 ^ a → J s((a, b), (a, b + 1)) = (a : ℝ≥0) ^ 2) ∧
    (∀ a b : ℕ, ¬ (1 ≤ a ∧ b + 1 ≤ 2 ^ a) → J s((a, b), (a, b + 1)) = 0) ∧
    (∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1))) := by
  refine ⟨fun i => ?_, fun a b ha hb => ?_, fun a b h => ?_, fun e he => ?_⟩
  · rw [hJ]; simp; omega
  · rw [hJ]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.left_eq_add, and_self,
      ↓reduceIte, ha, hb, zero_add, add_zero, true_and, add_eq_left, ite_eq_right_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, and_imp]
    intros; omega
  · rw [hJ]; simp; omega
  · revert he
    refine Sym2.ind (fun u v => ?_) e
    intro he
    rw [hJ] at he
    obtain ⟨a, b⟩ := u
    obtain ⟨c, d⟩ := v
    simp only at he
    by_cases h1 : b = 0 ∧ d = 0 ∧ c = a + 1
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl ⟨a, rfl⟩
    by_cases h2 : c = a ∧ 1 ≤ a ∧ d = b + 1 ∧ d ≤ 2 ^ a
    · obtain ⟨rfl, ha, rfl, hd⟩ := h2
      exact Or.inr ⟨c, b, ha, hd, rfl⟩
    by_cases h3 : d = 0 ∧ b = 0 ∧ a = c + 1
    · obtain ⟨rfl, rfl, rfl⟩ := h3
      exact Or.inl ⟨c, Sym2.eq_swap⟩
    by_cases h4 : a = c ∧ 1 ≤ c ∧ b = d + 1 ∧ b ≤ 2 ^ c
    · obtain ⟨rfl, hc, rfl, hb⟩ := h4
      exact Or.inr ⟨a, d, hc, hb, Sym2.eq_swap⟩
    simp [h1, h2, h3, h4] at he

/-! ### The profile -/

private theorem q_coe (J : Sym2 (ℕ × ℕ) → ℝ≥0) (β : ℝ≥0) (e : Sym2 (ℕ × ℕ)) :
    ((intensityProfile J β e : unitInterval) : ℝ) = 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) :=
  rfl

private theorem toNNReal_q (J : Sym2 (ℕ × ℕ) → ℝ≥0) (β : ℝ≥0) (e : Sym2 (ℕ × ℕ)) :
    (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) =
      ENNReal.ofReal (1 - Real.exp (-(β : ℝ) * (J e : ℝ))) := by
  rw [← q_coe, ENNReal.ofReal_eq_coe_nnreal (intensityProfile J β e).2.1]; rfl

private theorem J_pos_of_q_pos (J : Sym2 (ℕ × ℕ) → ℝ≥0) (β : ℝ≥0) {e : Sym2 (ℕ × ℕ)}
    (h : 0 < intensityProfile J β e) : 0 < J e := by
  rw [pos_iff_ne_zero]
  intro hJ0
  have : ((intensityProfile J β e : unitInterval) : ℝ) = 0 := by
    rw [q_coe, hJ0]; simp
  exact h.ne' (Subtype.ext (this.trans rfl))

/-- Almost surely every open pair has positive intensity. -/
theorem ae_subset_J_pos (J : Sym2 (ℕ × ℕ) → ℝ≥0) (β : ℝ≥0) :
    ∀ᵐ ω ∂law (intensityProfile J β), ω ⊆ {e | 0 < J e} := by
  filter_upwards [ae_config_subset_positive (intensityProfile J β)] with ω hω e he
  exact J_pos_of_q_pos J β (hω he)

/-! ### Deterministic structure -/

/-- A set closed under open adjacency contains the clusters of its points. -/
theorem cluster_subset_of_closed {V : Type*} {ω : Config V} {S : Set V}
    (hS : ∀ u ∈ S, ∀ v, s(u, v) ∈ ω → v ∈ S) {x : V} (hx : x ∈ S) : cluster ω x ⊆ S := by
  intro y hy
  have hy' : (openGraph ω).Reachable x y := hy
  clear hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy'
  induction hy' with
  | refl => exact hx
  | tail _ hadj ih => exact hS _ ih _ ((openGraph_adj_iff ω _ _).1 hadj).1

/-- **Connections to the root.** For a configuration of positive-intensity pairs, the root
is joined to `(k, j)` exactly when the backbone up to `k` and the pendant path up to `j`
are open. -/
theorem reachable_root_iff (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1)))
    {ω : Config (ℕ × ℕ)} (hω : ω ⊆ {e | 0 < J e}) (k j : ℕ) :
    (openGraph ω).Reachable (0, 0) (k, j) ↔
      (∀ i < k, s(((i : ℕ), (0 : ℕ)), (i + 1, 0)) ∈ ω) ∧ (∀ i < j, s((k, i), (k, i + 1)) ∈ ω) := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    -- the invariant along the way
    suffices H : ∀ v : ℕ × ℕ, Relation.ReflTransGen (openGraph ω).Adj (0, 0) v →
        (∀ i < v.1, s(((i : ℕ), (0 : ℕ)), (i + 1, 0)) ∈ ω) ∧
          (∀ i < v.2, s((v.1, i), (v.1, i + 1)) ∈ ω) from H _ h
    intro v hv
    induction hv with
    | refl => exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | @tail u w _ hadj ih =>
      obtain ⟨hmem, hne⟩ := (openGraph_adj_iff ω u w).1 hadj
      obtain ⟨ihb, iht⟩ := ih
      rcases hJ4 _ (hω hmem) with ⟨i, he⟩ | ⟨a, b, -, -, he⟩
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨fun i' hi' => ?_, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact ihb i' hi'
          · exact hmem
        · exact ⟨fun i' hi' => ihb i' (by simp at hi' ⊢; omega),
            fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨ihb, fun i' hi' => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact iht i' hi'
          · exact hmem
        · exact ⟨ihb, fun i' hi' => iht i' (by simp at hi' ⊢; omega)⟩
  · rintro ⟨hb, ht⟩
    have hback : ∀ m ≤ k, (openGraph ω).Reachable (0, 0) (m, 0) := by
      intro m hm
      induction m with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ m ih =>
        refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        exact (openGraph_adj_iff ω _ _).2 ⟨hb m (by omega), by simp⟩
    have htooth : ∀ m ≤ j, (openGraph ω).Reachable (0, 0) (k, m) := by
      intro m hm
      induction m with
      | zero => exact hback k le_rfl
      | succ m ih =>
        refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        exact (openGraph_adj_iff ω _ _).2 ⟨ht m (by omega), by simp⟩
    exact htooth j le_rfl

/-! ### The two-point function of the root -/

/-- **The two-point function of the root** as a product over the path to `(k, j)`. -/
theorem tau_root_eq (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1)))
    (β : ℝ≥0) (k j : ℕ) :
    tau (intensityProfile J β) (0, 0) (k, j) =
      ∏ e ∈ (Finset.range k).image (fun i => s(((i : ℕ), (0 : ℕ)), (i + 1, 0))) ∪
          (Finset.range j).image (fun i => s((k, i), (k, i + 1))),
        (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) := by
  classical
  rw [← prodBernoulli_subset]
  change law _ (conn _ _) = _
  refine measure_congr ?_
  filter_upwards [ae_subset_J_pos J β] with ω hω
  refine propext ?_
  change (openGraph ω).Reachable (0, 0) (k, j) ↔ _ ⊆ ω
  rw [reachable_root_iff J hJ4 hω]
  simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.union_subset_iff,
    Set.image_subset_iff]
  constructor
  · rintro ⟨hb, ht⟩
    exact ⟨fun i hi => hb i hi, fun i hi => ht i hi⟩
  · rintro ⟨hb, ht⟩
    exact ⟨fun i hi => hb (show i ∈ Set.Iio k from hi), fun i hi => ht (show i ∈ Set.Iio j from hi)⟩

/-! ### Every cluster is finite -/

/-- Infinitely many backbone edges are closed, almost surely. -/
theorem law_eventually_backbone_open (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1) (β : ℝ≥0) :
    law (intensityProfile J β)
      {ω | ∃ N₀ : ℕ, ∀ N ≥ N₀, s(((N : ℕ), (0 : ℕ)), (N + 1, 0)) ∈ ω} = 0 := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-(β : ℝ))) with hp
  have hp1 : p < 1 := by
    rw [hp, ENNReal.ofReal_lt_one]
    linarith [Real.exp_pos (-(β : ℝ))]
  have hset : {ω : Config (ℕ × ℕ) | ∃ N₀ : ℕ, ∀ N ≥ N₀, s(((N : ℕ), (0 : ℕ)), (N + 1, 0)) ∈ ω} =
      ⋃ N₀ : ℕ, {ω | ∀ N ≥ N₀, s(((N : ℕ), (0 : ℕ)), (N + 1, 0)) ∈ ω} := by
    ext ω; simp
  rw [hset]
  refine measure_iUnion_null fun N₀ => ?_
  have hle : ∀ M : ℕ, law (intensityProfile J β)
      {ω : Config (ℕ × ℕ) | ∀ N ≥ N₀, s(((N : ℕ), (0 : ℕ)), (N + 1, 0)) ∈ ω} ≤ p ^ M := by
    intro M
    set F : Finset (Sym2 (ℕ × ℕ)) :=
      (Finset.range M).image fun i => s(((N₀ + i : ℕ), (0 : ℕ)), (N₀ + i + 1, 0)) with hF
    calc law (intensityProfile J β)
          {ω : Config (ℕ × ℕ) | ∀ N ≥ N₀, s(((N : ℕ), (0 : ℕ)), (N + 1, 0)) ∈ ω}
        ≤ law (intensityProfile J β) {ω : Config (ℕ × ℕ) | (F : Set _) ⊆ ω} := by
          refine measure_mono fun ω hω e he => ?_
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
          exact hω (N₀ + i) (by omega)
      _ = p ^ M := by
          change prodBernoulli _ _ = _
          rw [prodBernoulli_subset, hF, Finset.prod_image]
          · rw [Finset.prod_congr rfl fun i _ => by rw [toNNReal_q, hJ1]]
            simp [hp]
          · intro a _ b _ hab
            rcases Sym2.eq_iff.1 hab with ⟨h, -⟩ | ⟨h, h'⟩
            · simpa using h
            · have := congrArg Prod.fst h
              have := congrArg Prod.fst h'
              simp at *; omega
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp1) hle)
    zero_le

/-- **Every cluster is finite**, almost surely, at every finite intensity. -/
theorem ae_forall_cluster_finite (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1)))
    (β : ℝ≥0) :
    ∀ᵐ ω ∂law (intensityProfile J β), ∀ x, (cluster ω x).Finite := by
  have hbad := law_eventually_backbone_open J hJ1 β
  rw [measure_eq_zero_iff_ae_notMem] at hbad
  filter_upwards [hbad, ae_subset_J_pos J β] with ω hbad hω
  simp only [not_exists, not_forall] at hbad
  rintro ⟨k, j⟩
  -- the edges of positive intensity at a vertex
  have hstep : ∀ u v : ℕ × ℕ, s(u, v) ∈ ω →
      (u.2 = 0 ∧ v.2 = 0 ∧ (v.1 = u.1 + 1 ∨ u.1 = v.1 + 1)) ∨
        (u.1 = v.1 ∧ 1 ≤ u.1 ∧ ((v.2 = u.2 + 1 ∧ v.2 ≤ 2 ^ u.1) ∨
          (u.2 = v.2 + 1 ∧ u.2 ≤ 2 ^ u.1))) := by
    intro u v huv
    rcases hJ4 _ (hω huv) with ⟨i, he⟩ | ⟨a, b, ha, hb, he⟩
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, Or.inl rfl⟩
      · exact Or.inl ⟨rfl, rfl, Or.inr rfl⟩
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, ha, Or.inl ⟨rfl, hb⟩⟩
      · exact Or.inr ⟨rfl, ha, Or.inr ⟨rfl, hb⟩⟩
  by_cases hj : j ≤ 2 ^ k
  · obtain ⟨N, hNk, hNclosed⟩ := hbad k
    refine (Set.Finite.subset ((Finset.range (N + 1) ×ˢ Finset.range (2 ^ N + 1)).finite_toSet)
      ?_)
    refine cluster_subset_of_closed (S := {v : ℕ × ℕ | v.1 ≤ N ∧ v.2 ≤ 2 ^ v.1}) ?_ ?_ |>.trans ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ huv
      dsimp only at ha hb
      change c ≤ N ∧ d ≤ 2 ^ c
      rcases hstep _ _ huv with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
      · dsimp only at h1 h2 h3
        subst h1 h2 h3
        refine ⟨?_, Nat.zero_le _⟩
        by_contra hlt
        have haN : a = N := by omega
        subst haN
        exact hNclosed huv
      · dsimp only at h1 h2 h3
        subst h2
        exact ⟨by omega, Nat.zero_le _⟩
      · dsimp only at h1 h2 h3 h4
        subst h1
        exact ⟨ha, h4⟩
      · dsimp only at h1 h2 h3 h4
        subst h1
        exact ⟨ha, by omega⟩
    · exact ⟨hNk, hj⟩
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      dsimp only at ha hb
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
      refine ⟨by omega, ?_⟩
      have : 2 ^ a ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) ha
      omega
  · refine (Set.finite_singleton (k, j)).subset (cluster_subset_of_closed ?_ rfl)
    rintro ⟨a, b⟩ hab ⟨c, d⟩ huv
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exfalso
    rcases hstep _ _ huv with ⟨h1, -⟩ | ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
    · dsimp only at h1; subst h1; simp at hj
    · dsimp only at h1 h3 h4; omega
    · dsimp only at h1 h3 h4; omega

/-- **No percolation at any finite intensity**: the root critical intensity is `⊤`. -/
theorem rootCriticalIntensity_eq_top (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1)))
    (x : ℕ × ℕ) : rootCriticalIntensity J x = ⊤ := by
  apply top_le_iff.mp
  apply le_sInf
  rintro b ⟨β, rfl, hpos⟩
  have hz : law (intensityProfile J β) {ω | (cluster ω x).Infinite} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_forall_cluster_finite J hJ1 hJ4 β] with ω hω h
    exact h (hω x)
  exact (hpos.ne' hz).elim

/-- **No infinite cluster at any finite intensity**: the global critical intensity is `⊤`. -/
theorem globalCriticalIntensity_eq_top (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1))) :
    globalCriticalIntensity J = ⊤ := by
  apply top_le_iff.mp
  apply le_sInf
  rintro b ⟨β, rfl, hpos⟩
  have hz : law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_forall_cluster_finite J hJ1 hJ4 β] with ω hω ⟨x, h⟩
    exact h (hω x)
  exact (hpos.ne' hz).elim

/-! ### The susceptibility -/

private theorem prod_le_backbone (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1) (β : ℝ≥0) (k j : ℕ) :
    ∏ e ∈ (Finset.range k).image (fun i => s(((i : ℕ), (0 : ℕ)), (i + 1, 0))) ∪
        (Finset.range j).image (fun i => s((k, i), (k, i + 1))),
      (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 - Real.exp (-(β : ℝ))) ^ k := by
  classical
  set A := (Finset.range k).image (fun i => s(((i : ℕ), (0 : ℕ)), (i + 1, 0)))
  set B := (Finset.range j).image (fun i => s((k, i), (k, i + 1)))
  have hA : ∏ e ∈ A, (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) =
      ENNReal.ofReal (1 - Real.exp (-(β : ℝ))) ^ k := by
    rw [Finset.prod_image]
    · rw [Finset.prod_congr rfl fun i _ => by rw [toNNReal_q, hJ1]]
      simp
    · intro a _ b _ hab
      rcases Sym2.eq_iff.1 hab with ⟨h, -⟩ | ⟨h, h'⟩
      · simpa using h
      · have := congrArg Prod.fst h
        have := congrArg Prod.fst h'
        simp at *; omega
  rw [← Finset.prod_sdiff (Finset.subset_union_left (s₂ := B)), hA]
  calc (∏ e ∈ (A ∪ B) \ A, (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞)) *
        ENNReal.ofReal (1 - Real.exp (-(β : ℝ))) ^ k
      ≤ 1 * ENNReal.ofReal (1 - Real.exp (-(β : ℝ))) ^ k := by
        gcongr
        exact Finset.prod_le_one fun e _ => by exact_mod_cast unitInterval.le_one _
    _ = _ := one_mul _

private theorem prod_eq_zero_of_gt (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ3 : ∀ a b : ℕ, ¬ (1 ≤ a ∧ b + 1 ≤ 2 ^ a) → J s((a, b), (a, b + 1)) = 0)
    (β : ℝ≥0) {k j : ℕ} (hj : 2 ^ k < j) :
    ∏ e ∈ (Finset.range k).image (fun i => s(((i : ℕ), (0 : ℕ)), (i + 1, 0))) ∪
        (Finset.range j).image (fun i => s((k, i), (k, i + 1))),
      (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) = 0 := by
  classical
  have h2k : 0 < 2 ^ k := by positivity
  refine Finset.prod_eq_zero (i := s((k, j - 1), (k, j - 1 + 1))) ?_ ?_
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j - 1, Finset.mem_range.2 (by omega),
      rfl⟩)
  · rw [toNNReal_q, hJ3 k (j - 1) (by omega)]
    simp

private theorem prod_eq_of_le (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1)
    (hJ2 : ∀ a b : ℕ, 1 ≤ a → b + 1 ≤ 2 ^ a → J s((a, b), (a, b + 1)) = (a : ℝ≥0) ^ 2)
    (β : ℝ≥0) {k j : ℕ} (hk : 1 ≤ k) (hj : j ≤ 2 ^ k) :
    ∏ e ∈ (Finset.range k).image (fun i => s(((i : ℕ), (0 : ℕ)), (i + 1, 0))) ∪
        (Finset.range j).image (fun i => s((k, i), (k, i + 1))),
      (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) =
      ENNReal.ofReal (1 - Real.exp (-(β : ℝ))) ^ k *
        ENNReal.ofReal (1 - Real.exp (-(β : ℝ) * (k : ℝ) ^ 2)) ^ j := by
  classical
  rw [Finset.prod_union]
  · rw [Finset.prod_image, Finset.prod_image]
    · rw [Finset.prod_congr rfl (g := fun _ => ENNReal.ofReal (1 - Real.exp (-(β : ℝ))))
          fun i _ => by rw [toNNReal_q, hJ1]; simp,
        Finset.prod_congr (s₁ := Finset.range j) rfl (g := fun _ => ENNReal.ofReal
          (1 - Real.exp (-(β : ℝ) * (k : ℝ) ^ 2))) fun i hi => by
          rw [toNNReal_q, hJ2 k i hk (by simp at hi; omega)]; simp]
      simp
    · intro a _ b _ hab
      rcases Sym2.eq_iff.1 hab with ⟨h, -⟩ | ⟨h, h'⟩
      · simpa using h
      · have := congrArg Prod.snd h
        have := congrArg Prod.snd h'
        simp at *; omega
    · intro a _ b _ hab
      rcases Sym2.eq_iff.1 hab with ⟨h, -⟩ | ⟨h, h'⟩
      · simpa using h
      · have := congrArg Prod.fst h
        have := congrArg Prod.fst h'
        simp at *; omega
  · rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨i', -, h⟩ := Finset.mem_image.1 he'
    rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
    · have := congrArg Prod.snd h; simp at this
    · have := congrArg Prod.snd h; simp at this

/-- **The susceptibility threshold**: `χ_β(o) < ∞ ↔ β < log 2`. -/
theorem chi_lt_top_iff (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ1 : ∀ i : ℕ, J s((i, 0), (i + 1, 0)) = 1)
    (hJ2 : ∀ a b : ℕ, 1 ≤ a → b + 1 ≤ 2 ^ a → J s((a, b), (a, b + 1)) = (a : ℝ≥0) ^ 2)
    (hJ3 : ∀ a b : ℕ, ¬ (1 ≤ a ∧ b + 1 ≤ 2 ^ a) → J s((a, b), (a, b + 1)) = 0)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1)))
    (β : ℝ≥0) :
    chi (intensityProfile J β) (0, 0) < ⊤ ↔ (β : ℝ) < Real.log 2 := by
  classical
  set p : ℝ := 1 - Real.exp (-(β : ℝ)) with hpdef
  have hp0 : 0 ≤ p := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 β.coe_nonneg); linarith
  have hp1 : p < 1 := by linarith [Real.exp_pos (-(β : ℝ))]
  have hchi : chi (intensityProfile J β) (0, 0) =
      ∑' k : ℕ, ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j) := by
    rw [chi_eq_tsum_tau, ENNReal.tsum_prod']
  -- `β < log 2 ↔ 2 p < 1`
  have hlog : (β : ℝ) < Real.log 2 ↔ 2 * p < 1 := by
    rw [hpdef]
    constructor
    · intro h
      have : Real.exp (-(β : ℝ)) > Real.exp (-Real.log 2) := Real.exp_lt_exp.2 (by linarith)
      rw [Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)] at this
      norm_num at this
      linarith
    · intro h
      by_contra hb
      push Not at hb
      have : Real.exp (-(β : ℝ)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      rw [Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)] at this
      norm_num at this
      linarith
  rw [hlog, hchi]
  constructor
  · -- divergence when `2 p ≥ 1`
    intro hfin
    by_contra h2p
    push Not at h2p
    have hβ : Real.exp (-(β : ℝ)) ≤ 1 / 2 := by linarith
    have hterm : ∀ k : ℕ, 2 ≤ k →
        (1 / 2 : ℝ≥0∞) ≤ ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j) := by
      intro k hk
      set r : ℝ := 1 - Real.exp (-(β : ℝ) * (k : ℝ) ^ 2) with hr
      have hr0 : 0 ≤ r := by
        have := Real.exp_le_one_iff.2 (by
          have : (0 : ℝ) ≤ (β : ℝ) * (k : ℝ) ^ 2 := by positivity
          linarith : -(β : ℝ) * (k : ℝ) ^ 2 ≤ 0)
        linarith
      -- `r^(2^k) ≥ 3/4`
      have hexp : Real.exp (-(β : ℝ) * (k : ℝ) ^ 2) ≤ (1 / 2) ^ (k ^ 2) := by
        rw [show -(β : ℝ) * (k : ℝ) ^ 2 = ((k ^ 2 : ℕ) : ℝ) * (-(β : ℝ)) by push_cast; ring,
          Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_pos _).le hβ _
      have hsmall : (2 : ℝ) ^ k * (1 / 2) ^ (k ^ 2) ≤ 1 / 4 := by
        have h1 : ((1 : ℝ) / 2) ^ (k ^ 2) ≤ ((1 / 2) ^ k) ^ 2 := by
          rw [← pow_mul, sq]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left k hk)
        have h2 : (2 : ℝ) ^ k * ((1 / 2) ^ k) ^ 2 = (1 / 2) ^ k := by
          rw [sq, ← mul_assoc, ← mul_pow]; norm_num
        have h3 : ((1 : ℝ) / 2) ^ k ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        calc (2 : ℝ) ^ k * (1 / 2) ^ (k ^ 2) ≤ (2 : ℝ) ^ k * ((1 / 2) ^ k) ^ 2 := by gcongr
          _ = (1 / 2) ^ k := h2
          _ ≤ (1 / 2) ^ 2 := h3
          _ = 1 / 4 := by norm_num
      have hbern : 3 / 4 ≤ r ^ (2 ^ k) := by
        have h := one_add_mul_le_pow (a := -Real.exp (-(β : ℝ) * (k : ℝ) ^ 2))
          (by linarith [Real.exp_le_one_iff.2 (show -(β : ℝ) * (k : ℝ) ^ 2 ≤ 0 by
            have : (0 : ℝ) ≤ (β : ℝ) * (k : ℝ) ^ 2 := by positivity
            linarith)]) (2 ^ k)
        have hpow : ((2 ^ k : ℕ) : ℝ) * Real.exp (-(β : ℝ) * (k : ℝ) ^ 2) ≤ 1 / 4 := by
          push_cast
          calc (2 : ℝ) ^ k * Real.exp (-(β : ℝ) * (k : ℝ) ^ 2) ≤ 2 ^ k * (1 / 2) ^ (k ^ 2) := by
                gcongr
            _ ≤ 1 / 4 := hsmall
        have h' : 1 - ((2 ^ k : ℕ) : ℝ) * Real.exp (-(β : ℝ) * (k : ℝ) ^ 2) ≤
            (1 - Real.exp (-(β : ℝ) * (k : ℝ) ^ 2)) ^ (2 ^ k) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, ← mul_neg]; exact h
        rw [hr]
        linarith
      -- `(2 p)^k ≥ 1`
      have h2pk : (1 : ℝ) ≤ (2 * p) ^ k := one_le_pow₀ h2p
      -- each `j ∈ [1, 2^k]` contributes at least `p^k r^(2^k)`
      have hj : ∀ j ∈ Finset.Icc 1 (2 ^ k), ENNReal.ofReal (p ^ k * r ^ (2 ^ k)) ≤
          tau (intensityProfile J β) (0, 0) (k, j) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
        rw [tau_root_eq J hJ4 β k j, prod_eq_of_le J hJ1 hJ2 β (by omega) hj2,
          ← ENNReal.ofReal_pow hp0, ← ENNReal.ofReal_pow hr0,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
        have hr1 : r ≤ 1 := by linarith [Real.exp_pos (-(β : ℝ) * (k : ℝ) ^ 2)]
        exact pow_le_pow_of_le_one hr0 hr1 hj2
      calc (1 / 2 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ k * (p ^ k * r ^ (2 ^ k))) := by
            rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
              rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
            refine ENNReal.ofReal_le_ofReal ?_
            have : (2 : ℝ) ^ k * (p ^ k * r ^ (2 ^ k)) = (2 * p) ^ k * r ^ (2 ^ k) := by
              rw [mul_pow]; ring
            rw [this]
            nlinarith
        _ = ∑ _j ∈ Finset.Icc 1 (2 ^ k), ENNReal.ofReal (p ^ k * r ^ (2 ^ k)) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_pow (by norm_num)]
            simp
        _ ≤ ∑ j ∈ Finset.Icc 1 (2 ^ k), tau (intensityProfile J β) (0, 0) (k, j) :=
            Finset.sum_le_sum hj
        _ ≤ ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j) := ENNReal.sum_le_tsum _
    have htop : ∑' k : ℕ, ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j) = ⊤ := by
      refine top_unique ?_
      calc (⊤ : ℝ≥0∞) = ∑' _k : ℕ, (1 / 2 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)).symm
        _ ≤ ∑' k : ℕ, ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k + 2, j) :=
            ENNReal.tsum_le_tsum fun k => hterm (k + 2) (by omega)
        _ ≤ ∑' k : ℕ, ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j) :=
            ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 2)
              (fun k => ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j))
    exact (lt_irrefl _ (htop ▸ hfin))
  · -- finiteness when `2 p < 1`
    intro h2p
    set P : ℝ≥0∞ := ENNReal.ofReal p with hP
    have hrow : ∀ k : ℕ, ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j) ≤
        (2 * P) ^ k + P ^ k := by
      intro k
      calc ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j)
          ≤ ∑' j : ℕ, (if j ≤ 2 ^ k then P ^ k else 0) := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            rw [tau_root_eq J hJ4 β k j]
            split_ifs with hj
            · exact prod_le_backbone J hJ1 β k j
            · exact le_of_eq (prod_eq_zero_of_gt J hJ3 β (by omega))
        _ = ∑ j ∈ Finset.range (2 ^ k + 1), P ^ k := by
            rw [tsum_eq_sum (s := Finset.range (2 ^ k + 1)) fun j hj => by
              rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp at hj; omega))]]
            exact Finset.sum_congr rfl fun j hj => by
              rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp at hj; omega))]
        _ = (2 * P) ^ k + P ^ k := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow]
            push_cast
            ring
    have h2P : 2 * P < 1 := by
      rw [hP, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_lt_one]
      exact h2p
    have hP1 : P < 1 := by rw [hP, ENNReal.ofReal_lt_one]; exact hp1
    calc ∑' k : ℕ, ∑' j : ℕ, tau (intensityProfile J β) (0, 0) (k, j)
        ≤ ∑' k : ℕ, ((2 * P) ^ k + P ^ k) := ENNReal.tsum_le_tsum hrow
      _ = (1 - 2 * P)⁻¹ + (1 - P)⁻¹ := by
          rw [ENNReal.tsum_add, ENNReal.tsum_geometric, ENNReal.tsum_geometric]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.inv_lt_top.2 (tsub_pos_of_lt h2P),
          ENNReal.inv_lt_top.2 (tsub_pos_of_lt hP1)⟩

/-- At `β = 0` every pair is closed and the susceptibility is `1`. -/
theorem chi_zero (J : Sym2 (ℕ × ℕ) → ℝ≥0)
    (hJ4 : ∀ e, 0 < J e → (∃ i : ℕ, e = s((i, 0), (i + 1, 0))) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ b + 1 ≤ 2 ^ a ∧ e = s((a, b), (a, b + 1))) :
    chi (intensityProfile J 0) (0, 0) = 1 := by
  classical
  rw [chi_eq_tsum_tau, tsum_eq_single ((0 : ℕ), (0 : ℕ))]
  · exact tau_self _ _
  · rintro ⟨k, j⟩ hkj
    rw [tau_root_eq J hJ4 0 k j]
    have hne : ((Finset.range k).image (fun i => s(((i : ℕ), (0 : ℕ)), (i + 1, 0))) ∪
        (Finset.range j).image (fun i => s((k, i), (k, i + 1)))).Nonempty := by
      by_cases hk : k = 0
      · subst hk
        have hj : j ≠ 0 := fun h => hkj (by rw [h])
        exact ⟨_, Finset.mem_union_right _ (Finset.mem_image.2 ⟨0, Finset.mem_range.2
          (Nat.pos_of_ne_zero hj), rfl⟩)⟩
      · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_range.2
          (Nat.pos_of_ne_zero hk), rfl⟩)⟩
    obtain ⟨e, he⟩ := hne
    refine Finset.prod_eq_zero he ?_
    rw [toNNReal_q]
    simp

/-! ### The intensity exists -/

/-- The intensity of the decorated ray exists (non-vacuity of `hJ`). -/
theorem exists_J : ∃ J : Sym2 (ℕ × ℕ) → ℝ≥0, ∀ u v : ℕ × ℕ, J s(u, v) =
      (if u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1 then 1 else 0) +
      (if v.1 = u.1 ∧ 1 ≤ u.1 ∧ v.2 = u.2 + 1 ∧ v.2 ≤ 2 ^ u.1 then (u.1 : ℝ≥0) ^ 2 else 0) +
      (if v.2 = 0 ∧ u.2 = 0 ∧ u.1 = v.1 + 1 then 1 else 0) +
      (if u.1 = v.1 ∧ 1 ≤ v.1 ∧ u.2 = v.2 + 1 ∧ u.2 ≤ 2 ^ v.1 then (v.1 : ℝ≥0) ^ 2 else 0) := by
  classical
  set f : ℕ × ℕ → ℕ × ℕ → ℝ≥0 := fun u v =>
    (if u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1 then 1 else 0) +
      (if v.1 = u.1 ∧ 1 ≤ u.1 ∧ v.2 = u.2 + 1 ∧ v.2 ≤ 2 ^ u.1 then (u.1 : ℝ≥0) ^ 2 else 0)
    with hf
  refine ⟨Sym2.lift ⟨fun u v => f u v + f v u, fun u v => add_comm _ _⟩, fun u v => ?_⟩
  simp only [Sym2.lift_mk, hf]
  ring

/-- At `β = 0` the model has `χ(o) = 1`. -/
example : ∃ J : Sym2 (ℕ × ℕ) → ℝ≥0, chi (intensityProfile J 0) (0, 0) = 1 ∧
    ∀ β : ℝ≥0, chi (intensityProfile J β) (0, 0) < ⊤ ↔ (β : ℝ) < Real.log 2 := by
  obtain ⟨J, hJ⟩ := exists_J
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := J_facts J hJ
  exact ⟨J, chi_zero J hJ4, chi_lt_top_iff J hJ1 hJ2 hJ3 hJ4⟩

/-! ### The existential statement -/

/-- **A degree-3 example**: there is a connected countable host graph of
maximum degree at most three, with finite nonnegative intensities supported on its edges,
such that at every finite intensity every cluster is almost surely finite (so the root and
global critical intensities are `⊤`), while the susceptibility of the root is finite exactly
for `β < log 2`. The model is the decorated ray of this file. -/
theorem exists_decoratedRay :
    ∃ (G : SimpleGraph (ℕ × ℕ)) (J : Sym2 (ℕ × ℕ) → ℝ≥0) (o : ℕ × ℕ),
      G.Connected ∧ (∀ v, (G.neighborSet v).encard ≤ 3) ∧
      (∀ e, J e ≠ 0 → e ∈ G.edgeSet) ∧
      (∀ β : ℝ≥0, ∀ᵐ ω ∂law (intensityProfile J β), ∀ x, (cluster ω x).Finite) ∧
      (∀ x, rootCriticalIntensity J x = ⊤) ∧ globalCriticalIntensity J = ⊤ ∧
      (∀ β : ℝ≥0, chi (intensityProfile J β) o < ⊤ ↔ (β : ℝ) < Real.log 2) := by
  classical
  set f : ℕ × ℕ → ℕ × ℕ → ℝ≥0 := fun u v =>
    (if u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1 then 1 else 0) +
      (if v.1 = u.1 ∧ 1 ≤ u.1 ∧ v.2 = u.2 + 1 ∧ v.2 ≤ 2 ^ u.1 then (u.1 : ℝ≥0) ^ 2 else 0)
    with hf
  set J : Sym2 (ℕ × ℕ) → ℝ≥0 := Sym2.lift ⟨fun u v => f u v + f v u, fun u v => add_comm _ _⟩
    with hJdef
  have hJ : ∀ u v : ℕ × ℕ, J s(u, v) =
      (if u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1 then 1 else 0) +
      (if v.1 = u.1 ∧ 1 ≤ u.1 ∧ v.2 = u.2 + 1 ∧ v.2 ≤ 2 ^ u.1 then (u.1 : ℝ≥0) ^ 2 else 0) +
      (if v.2 = 0 ∧ u.2 = 0 ∧ u.1 = v.1 + 1 then 1 else 0) +
      (if u.1 = v.1 ∧ 1 ≤ v.1 ∧ u.2 = v.2 + 1 ∧ u.2 ≤ 2 ^ v.1 then (v.1 : ℝ≥0) ^ 2 else 0) := by
    intro u v
    simp only [hJdef, Sym2.lift_mk, hf]
    ring
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := J_facts J hJ
  set G : SimpleGraph (ℕ × ℕ) := SimpleGraph.fromRel fun u v : ℕ × ℕ =>
    (u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1) with hG
  have hadj : ∀ u v : ℕ × ℕ, G.Adj u v ↔ u ≠ v ∧
      (((u.2 = 0 ∧ v.2 = 0 ∧ v.1 = u.1 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)) ∨
        ((v.2 = 0 ∧ u.2 = 0 ∧ u.1 = v.1 + 1) ∨ (u.1 = v.1 ∧ u.2 = v.2 + 1))) := by
    intro u v; rw [hG, SimpleGraph.fromRel_adj]
  refine ⟨G, J, (0, 0), ?_, ?_, ?_, ae_forall_cluster_finite J hJ1 hJ4,
    rootCriticalIntensity_eq_top J hJ1 hJ4, globalCriticalIntensity_eq_top J hJ1 hJ4,
    chi_lt_top_iff J hJ1 hJ2 hJ3 hJ4⟩
  · -- connected
    have hreach : ∀ k j : ℕ, G.Reachable (0, 0) (k, j) := by
      intro k j
      have hback : ∀ m : ℕ, G.Reachable (0, 0) (m, 0) := by
        intro m
        induction m with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ m ih =>
          refine ih.trans (SimpleGraph.Adj.reachable ?_)
          rw [hadj]; exact ⟨by simp, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      induction j with
      | zero => exact hback k
      | succ j ih =>
        refine ih.trans (SimpleGraph.Adj.reachable ?_)
        rw [hadj]; exact ⟨by simp, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    have : Nonempty (ℕ × ℕ) := ⟨(0, 0)⟩
    exact ⟨fun u v => (hreach u.1 u.2).symm.trans (hreach v.1 v.2)⟩
  · -- degree at most three
    rintro ⟨a, b⟩
    by_cases hb : b = 0
    · subst hb
      have hsub : G.neighborSet (a, 0) ⊆ {(a + 1, 0), (a - 1, 0), (a, 1)} := by
        rintro ⟨c, d⟩ h
        rw [SimpleGraph.mem_neighborSet, hadj] at h
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        obtain ⟨-, h⟩ := h
        omega
      refine (Set.encard_le_encard hsub).trans ?_
      refine (Set.encard_insert_le _ _).trans ?_
      refine (add_le_add (Set.encard_insert_le _ _) le_rfl).trans ?_
      rw [Set.encard_singleton]
      norm_num
    · have hsub : G.neighborSet (a, b) ⊆ {(a, b + 1), (a, b - 1)} := by
        rintro ⟨c, d⟩ h
        rw [SimpleGraph.mem_neighborSet, hadj] at h
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        obtain ⟨-, h⟩ := h
        omega
      refine (Set.encard_le_encard hsub).trans ?_
      refine (Set.encard_insert_le _ _).trans ?_
      rw [Set.encard_singleton]
      norm_num
  · -- intensities live on host edges
    intro e he
    rcases hJ4 e (pos_iff_ne_zero.2 he) with ⟨i, rfl⟩ | ⟨a, b, -, -, rfl⟩
    · rw [SimpleGraph.mem_edgeSet, hadj]
      exact ⟨by simp, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · rw [SimpleGraph.mem_edgeSet, hadj]
      exact ⟨by simp, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩

/-- If the root susceptibility is finite exactly for `β < a` (with `a ≥ 0`), the infimum of the
parameters with infinite root susceptibility is `a`. -/
theorem sInf_setOf_chi_eq_top_eq {V : Type*} (J : Sym2 V → ℝ≥0) (o : V) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ β : ℝ≥0, chi (intensityProfile J β) o < ⊤ ↔ (β : ℝ) < a) :
    ((sInf {β : ℝ≥0 | chi (intensityProfile J β) o = ⊤} : ℝ≥0) : ℝ) = a := by
  have hset : {β : ℝ≥0 | chi (intensityProfile J β) o = ⊤} = Set.Ici (Real.toNNReal a) := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, Real.toNNReal_le_iff_le_coe]
    rw [← not_lt, ← h, lt_top_iff_ne_top, not_not]
  rw [hset, csInf_Ici, Real.coe_toNNReal _ ha]

end PercLib.Models.DecoratedRay
