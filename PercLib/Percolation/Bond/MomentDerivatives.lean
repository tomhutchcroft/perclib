/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Probability.Russo
public import PercLib.Probability.CovarianceRusso
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.ZeroOne
public import PercLib.Percolation.Bond.ClusterPartition
public import PercLib.Percolation.Bond.FiniteSetCriterion

/-!
# Cluster-moment derivatives in finite transitive intensity models (C9Y8, exact formula)

On a finite vertex set, bonds are independent with probability `1 - e^{-λ_t(e)}`
(`intensityProfile (λ t) 1`), and `w(e) = ∂_t λ_t(e)`.

* `hasDerivAt_integral_intensityProfile` (**Russo with the closed indicator kept**): for every
  functional `F` of the configuration,
  `d/dt E_t F = ∑_e w(e) E_t[1{e closed} (F(ω ∪ {e}) - F(ω))]`.
* `cluster_insert_of_mem`, `cluster_insert_of_not_mem`: opening `s(a, b)` merges `K_a` and
  `K_b` and leaves every other cluster unchanged.
* `sum_cluster_pow_insert_sub`: opening `s(a, b)` changes `∑_v |K_v|^k` by
  `1{a ↮ b} ((A + B)^{k+1} - A^{k+1} - B^{k+1})`, `A = |K_a|`, `B = |K_b|`.
* `hasDerivAt_integral_sum_cluster_pow`: the derivative of `E_t ∑_v |K_v|^k` as a sum over
  ordered pairs.
* `hasDerivAt_moment_of_transitive` (**C9Y8, exact formula**): for a transitive family,
  `m_k'(t) = (1/2) ∑_{y ≠ o} w(o, y) E_t[1{o ↮ y} ∑_{j=1}^k C(k+1, j) |K_o|^j |K_y|^{k+1-j}]`,
  and `0 ≤ m_k'` when `w ≥ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Russo's formula with the closed indicator kept -/

open PercLib.Probability PercLib.Probability.FiniteProfile in
open Classical in
/-- Closing a coordinate: `(1 - p_e) E[h(ω ∪ {e}) - h(ω \ {e})] = E[1{e ∉ ω}(h(ω ∪ {e}) - h ω)]`. -/
theorem one_sub_mul_integral_insert_sub {E : Type*} [Fintype E] (p : E → unitInterval)
    (e : E) (h : Set E → ℝ) :
    (1 - (p e : ℝ)) * ∫ ω, (h (insert e ω) - h (ω \ {e})) ∂prodBernoulli p =
      ∫ ω, (if e ∈ ω then 0 else h (insert e ω) - h ω) ∂prodBernoulli p := by
  classical
  rw [integral_prodBernoulli_eq_expectation, integral_prodBernoulli_eq_expectation,
    expectation_split _ e (fun ω => if e ∈ toSet ω then 0 else h (insert e (toSet ω)) -
        h (toSet ω))]
  have h1 : ∀ ω : E → Bool, e ∈ toSet (force e true ω) := fun ω => by
    simp [toSet, force]
  have h0 : ∀ ω : E → Bool, e ∉ toSet (force e false ω) := fun ω => by
    simp [toSet, force]
  simp only [h1, h0, ite_true, ite_false]
  have hz : expectation (fun e => (p e : ℝ)) (fun _ => (0 : ℝ)) = 0 := by
    simp [expectation]
  rw [hz, mul_zero, zero_add]
  congr 1
  congr 1
  funext ω
  simp only [toSet_force_false, Set.insert_sdiff_singleton]

open Classical in
/-- **Russo's formula for intensity families, closed indicator kept.** On a finite vertex
set, for intensities `λ_u(e) ≥ 0` differentiable at `t` with derivatives `w(e)` and every real
functional `F`,
`d/dt E_t F = ∑_e w(e) E_t[1{e ∉ ω}(F(ω ∪ {e}) - F(ω))]`. -/
theorem hasDerivAt_integral_intensityProfile [Fintype V] [DecidableEq V]
    (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (F : Config V → ℝ) :
    HasDerivAt (fun u => ∫ ω, F ω ∂law (intensityProfile (lam u) 1))
      (∑ e, w e * ∫ ω, (if e ∈ ω then 0 else F (insert e ω) - F ω)
        ∂law (intensityProfile (lam t) 1)) t := by
  have hq : ∀ e, HasDerivAt (fun u => 1 - Real.exp (-(lam u e : ℝ)))
      (w e * Real.exp (-(lam t e : ℝ))) t := by
    intro e
    convert ((hlam e).neg.exp.const_sub 1) using 1
    simp only [Pi.neg_apply]
    ring
  have hp : ∀ u e, ((intensityProfile (lam u) 1 e : unitInterval) : ℝ) =
      1 - Real.exp (-(lam u e : ℝ)) := by
    intro u e
    simp [intensityProfile]
  have h := PercLib.Probability.FiniteProfile.integral_hasDerivWithinAt (E := Sym2 V)
    (fun e u => 1 - Real.exp (-(lam u e : ℝ))) (fun e => w e * Real.exp (-(lam t e : ℝ))) t hq
    (fun u => intensityProfile (lam u) 1) Set.univ (hp t) (fun u _ => hp u) F
  rw [hasDerivWithinAt_univ] at h
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_assoc]
  congr 1
  simp only [law]
  rw [← one_sub_mul_integral_insert_sub, hp]
  ring

/-! ### Opening one pair -/

/-- Opening `s(a, b)`: the new cluster of a vertex of `K_a ∪ K_b` is `K_a ∪ K_b`. -/
theorem cluster_insert_of_mem (ω : Config V) (a b x : V)
    (hx : x ∈ cluster ω a ∪ cluster ω b) :
    cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b := by
  have hab : (insert s(a, b) ω) ∈ conn a b := by
    by_cases h : a = b
    · subst h; exact SimpleGraph.Reachable.refl _
    · exact mem_conn_of_mem h (mem_insert _ _)
  have hmono : ∀ y z, ω ∈ conn y z → insert s(a, b) ω ∈ conn y z :=
    fun y z h => conn_mono (subset_insert _ _) h
  apply Subset.antisymm
  · intro y hy
    rcases cluster_insert_subset ω a b x hy with (h | h) | h
    · rcases hx with hx | hx
      · exact Or.inl (conn_trans hx h)
      · exact Or.inr (conn_trans hx h)
    · exact Or.inl h
    · exact Or.inr h
  · have hxa : insert s(a, b) ω ∈ conn x a := by
      rcases hx with hx | hx
      · rw [conn_symm]; exact hmono _ _ hx
      · rw [conn_symm] at hab
        exact conn_trans (by rw [conn_symm]; exact hmono _ _ hx) hab
    rintro y (hy | hy)
    · exact conn_trans hxa (hmono _ _ hy)
    · exact conn_trans (conn_trans hxa hab) (hmono _ _ hy)

/-- Opening `s(a, b)` does not change the cluster of a vertex outside `K_a ∪ K_b`. -/
theorem cluster_insert_of_not_mem (ω : Config V) (a b x : V)
    (hx : x ∉ cluster ω a ∪ cluster ω b) :
    cluster (insert s(a, b) ω) x = cluster ω x := by
  refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) x)
  intro y hy
  change (openGraph (insert s(a, b) ω)).Reachable x y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact mem_cluster_self ω x
  | @tail z u _ hadj ih =>
    rw [openGraph_adj_iff, mem_insert_iff] at hadj
    obtain ⟨he | he, hne⟩ := hadj
    · exfalso
      apply hx
      rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact Or.inl (h1 ▸ (mem_cluster_comm ω x z).1 ih)
      · exact Or.inr (h2 ▸ (mem_cluster_comm ω x z).1 ih)
    · exact conn_trans ih (SimpleGraph.Adj.reachable ((openGraph_adj_iff ω z u).2 ⟨he, hne⟩))

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
open Classical in
/-- **Opening one pair** changes `∑_v |K_v|^k` by `(A + B)^{k+1} - A^{k+1} - B^{k+1}` when
`a ↮ b`, where `A = |K_a|`, `B = |K_b|`, and not at all when `a ↔ b`. -/
theorem sum_cluster_pow_insert_sub (ω : Config V) (a b : V) (k : ℕ) :
    ∑ v, ((cluster (insert s(a, b) ω) v).ncard : ℝ) ^ k - ∑ v, ((cluster ω v).ncard : ℝ) ^ k =
      if ω ∈ conn a b then 0 else
        (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) ^ (k + 1) -
          ((cluster ω a).ncard : ℝ) ^ (k + 1) - ((cluster ω b).ncard : ℝ) ^ (k + 1) := by
  classical
  have hceq : ∀ {a x : V}, x ∈ cluster ω a → cluster ω x = cluster ω a := fun hx =>
    (cluster_eq_iff_conn ω _ _).2 ((mem_cluster_comm ω _ _).1 hx)
  set A := ((cluster ω a).ncard : ℝ)
  set B := ((cluster ω b).ncard : ℝ)
  rw [← Finset.sum_sub_distrib]
  split_ifs with hab
  · refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v ∈ cluster ω a ∪ cluster ω b
    · rw [cluster_insert_of_mem ω a b v hv]
      have hba : cluster ω b = cluster ω a := hceq hab
      rw [hba, union_self]
      rcases hv with hv | hv
      · rw [hceq hv, sub_self]
      · rw [hba] at hv; rw [hceq hv, sub_self]
    · rw [cluster_insert_of_not_mem ω a b v hv, sub_self]
  · have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
      refine Set.disjoint_left.2 fun y hya hyb => hab ?_
      exact conn_trans hya (by rw [conn_symm]; exact hyb)
    have hfin : ∀ x, (cluster ω x).Finite := fun x => Set.toFinite _
    have hAB : ((cluster ω a ∪ cluster ω b).ncard : ℝ) = A + B := by
      rw [Set.ncard_union_eq hdisj (hfin a) (hfin b)]; push_cast; rfl
    have hterm : ∀ v, ((cluster (insert s(a, b) ω) v).ncard : ℝ) ^ k -
        ((cluster ω v).ncard : ℝ) ^ k =
        (if v ∈ cluster ω a then (A + B) ^ k - A ^ k else 0) +
          (if v ∈ cluster ω b then (A + B) ^ k - B ^ k else 0) := by
      intro v
      by_cases hva : v ∈ cluster ω a
      · have hvb : v ∉ cluster ω b := Set.disjoint_left.1 hdisj hva
        rw [cluster_insert_of_mem ω a b v (Or.inl hva), hAB, hceq hva]
        simp [hva, hvb, A]
      · by_cases hvb : v ∈ cluster ω b
        · rw [cluster_insert_of_mem ω a b v (Or.inr hvb), hAB, hceq hvb]
          simp [hva, hvb, B]
        · rw [cluster_insert_of_not_mem ω a b v (fun h => h.elim hva hvb)]
          simp [hva, hvb]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero,
      Finset.sum_const_zero, add_zero, add_zero, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    have hca : ((Finset.univ.filter fun v => v ∈ cluster ω a).card : ℝ) = A := by
      simp only [A, ← Set.ncard_coe_finset]
      congr 2
      ext v; simp
    have hcb : ((Finset.univ.filter fun v => v ∈ cluster ω b).card : ℝ) = B := by
      simp only [B, ← Set.ncard_coe_finset]
      congr 2
      ext v; simp
    rw [hca, hcb]
    ring

/-! ### Unordered and ordered pairs -/

omit [Fintype V] in
/-- The two ordered pairs over a pair `s(a, b)`. -/
theorem filter_mk_eq [Fintype V] (a b : V) :
    (Finset.univ : Finset (V × V)).filter (fun p => s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]

/-- A function of unordered pairs vanishing on the diagonal: the sum over ordered pairs is
twice the sum over unordered pairs. -/
theorem sum_sum_mk_eq_two_mul {M : Type*} [AddCommMonoid M] (f : Sym2 V → M)
    (hf : ∀ a, f s(a, a) = 0) :
    ∑ a, ∑ b, f s(a, b) = 2 • ∑ e, f e := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Finset.smul_sum]
  rw [Finset.sum_comp (fun e => f e) (fun p : V × V => s(p.1, p.2))]
  have himg : (Finset.univ : Finset (V × V)).image (fun p => s(p.1, p.2)) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun e => ?_
    induction e using Sym2.ind with
    | _ a b => exact Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, rfl⟩
  rw [himg]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    rw [filter_mk_eq]
    by_cases hab : a = b
    · subst hab; simp [hf]
    · rw [Finset.card_pair (by simp [hab])]

/-! ### The derivative of `E ∑_v |K_v|^k` -/

open Classical in
/-- The derivative of `E_t ∑_v |K_v|^k` as a sum over ordered pairs:
`(1/2) ∑_a ∑_b w(a, b) E_t[1{a ↮ b} ((A + B)^{k+1} - A^{k+1} - B^{k+1})]`. -/
theorem hasDerivAt_integral_sum_cluster_pow (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ)
    (t : ℝ) (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (k : ℕ) :
    HasDerivAt (fun u => ∫ ω, ∑ v, ((cluster ω v).ncard : ℝ) ^ k
        ∂law (intensityProfile (lam u) 1))
      ((1 / 2) * ∑ a, ∑ b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
        (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) ^ (k + 1) -
          ((cluster ω a).ncard : ℝ) ^ (k + 1) - ((cluster ω b).ncard : ℝ) ^ (k + 1))
        ∂law (intensityProfile (lam t) 1)) t := by
  have h := hasDerivAt_integral_intensityProfile lam w t hlam
    (fun ω => ∑ v, ((cluster ω v).ncard : ℝ) ^ k)
  convert h using 1
  set g : Sym2 V → ℝ := fun e => w e * ∫ ω, (if e ∈ ω then 0 else
      ∑ v, ((cluster (insert e ω) v).ncard : ℝ) ^ k - ∑ v, ((cluster ω v).ncard : ℝ) ^ k)
      ∂law (intensityProfile (lam t) 1) with hg
  have hpair : ∀ a b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) ^ (k + 1) -
        ((cluster ω a).ncard : ℝ) ^ (k + 1) - ((cluster ω b).ncard : ℝ) ^ (k + 1))
      ∂law (intensityProfile (lam t) 1) = g s(a, b) := by
    intro a b
    rw [hg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← sum_cluster_pow_insert_sub]
    by_cases he : s(a, b) ∈ ω
    · have hc : ω ∈ conn a b := by
        by_cases hab : a = b
        · subst hab; exact SimpleGraph.Reachable.refl _
        · exact mem_conn_of_mem hab he
      simp only [he, ite_true, insert_eq_of_mem he, sub_self]
    · simp only [he, ite_false]
  simp_rw [hpair]
  have hdiag : ∀ a, g s(a, a) = 0 := by
    intro a
    rw [← hpair]
    simp [conn_self]
  rw [sum_sum_mk_eq_two_mul g hdiag, nsmul_eq_mul]
  push_cast
  ring

/-! ### Transitive families -/

omit [Fintype V] [DecidableEq V] in
/-- An automorphism of the kernel leaves every expectation unchanged. -/
theorem integral_image_sym2Map_of_invariant (J : Sym2 V → ℝ≥0) (σ : V ≃ V)
    (hσ : ∀ e, J (Sym2.map σ e) = J e) (Ψ : Config V → ℝ) :
    ∫ ω, Ψ (Sym2.map σ '' ω) ∂law (intensityProfile J 1) =
      ∫ ω, Ψ ω ∂law (intensityProfile J 1) := by
  obtain ⟨E, hE⟩ := exists_measurableEquiv_image_sym2Map σ
  conv_rhs => rw [← law_intensityProfile_map_eq J σ hσ 1, ← hE]
  rw [integral_map_equiv, hE]

omit [DecidableEq V] in
/-- `(A + B)^{k+1} - A^{k+1} - B^{k+1} = ∑_{j=1}^k C(k+1, j) A^j B^{k+1-j}`. -/
theorem add_pow_succ_sub_pow_sub_pow (A B : ℝ) (k : ℕ) :
    (A + B) ^ (k + 1) - A ^ (k + 1) - B ^ (k + 1) =
      ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * A ^ j * B ^ (k + 1 - j) := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, Nat.choose_zero_right,
    one_mul, Nat.sub_zero, pow_zero]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have h : ∀ i ∈ Finset.range k, A ^ (i + 1) * B ^ (k + 1 - (i + 1)) *
      ((k + 1).choose (i + 1) : ℝ) =
      ((k + 1).choose (1 + i) : ℝ) * A ^ (1 + i) * B ^ (k + 1 - (1 + i)) := by
    intro i _
    rw [add_comm 1 i]
    ring
  rw [Finset.sum_congr rfl h]
  ring

open Classical in
/-- **Exact formula.** Let `V` be finite and the intensities `λ_u` invariant under a
group acting transitively (`∀ x y, ∃ σ, σ x = y` preserving every `λ_u`), with derivatives
`w` at `t`. Then for every `k ≥ 0`, `m_k(u) = E_u |K_o|^k` satisfies
`m_k'(t) = (1/2) ∑_{y ≠ o} w(o, y) E_t[1{o ↮ y} ∑_{j=1}^k C(k+1, j) |K_o|^j |K_y|^{k+1-j}]`. -/
theorem hasDerivAt_moment_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (k : ℕ) :
    HasDerivAt (fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1))
      ((1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
          ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) ∂law (intensityProfile (lam t) 1)) t := by
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨o⟩
  -- transport of clusters and connections
  have hncard : ∀ (σ : V ≃ V) (ω : Config V) (x : V),
      (cluster (Sym2.map σ '' ω) (σ x)).ncard = (cluster ω x).ncard := by
    intro σ ω x
    rw [cluster_image, Set.ncard_image_of_injective _ σ.injective]
  -- root independence of the moments
  have hroot : ∀ u (a : V), ∫ ω, ((cluster ω a).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1) =
      ∫ ω, ((cluster ω o).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1) := by
    intro u a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← integral_image_sym2Map_of_invariant (lam u) σ (hσ u)
      (fun ω => ((cluster ω o).ncard : ℝ) ^ k)]
    congr 1
    funext ω
    rw [← hσa, hncard]
  have hsum : ∀ u, ∫ ω, ∑ v, ((cluster ω v).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1) =
      Fintype.card V * ∫ ω, ((cluster ω o).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1) := by
    intro u
    rw [integral_finsetSum _ fun v _ => Integrable.of_finite]
    simp_rw [hroot u]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfun : (fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1)) =
      fun u => (Fintype.card V : ℝ)⁻¹ *
        ∫ ω, ∑ v, ((cluster ω v).ncard : ℝ) ^ k ∂law (intensityProfile (lam u) 1) := by
    funext u
    rw [hsum u, ← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]
  rw [hfun]
  refine ((hasDerivAt_integral_sum_cluster_pow lam w t hlam k).const_mul _).congr_deriv ?_
  -- the pair term, and its invariance
  set g : V → V → ℝ := fun a b => w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) ^ (k + 1) -
        ((cluster ω a).ncard : ℝ) ^ (k + 1) - ((cluster ω b).ncard : ℝ) ^ (k + 1))
      ∂law (intensityProfile (lam t) 1) with hg
  have hw : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ e, w (Sym2.map σ e) = w e := by
    intro σ hσ e
    have h1 := hlam (Sym2.map σ e)
    simp_rw [hσ] at h1
    exact h1.unique (hlam e)
  have hginv : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ a b, g (σ a) (σ b) = g a b := by
    intro σ hσ a b
    simp only [hg]
    have hwe := hw σ hσ s(a, b)
    rw [Sym2.map_mk] at hwe
    rw [hwe]
    congr 1
    rw [← integral_image_sym2Map_of_invariant (lam t) σ (hσ t)]
    congr 1
    funext ω
    simp only [image_mem_conn_iff, hncard]
  have hrow : ∀ a, ∑ b, g a b = ∑ b, g o b := by
    intro a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← hσa, ← Equiv.sum_comp σ (g (σ a))]
    exact Finset.sum_congr rfl fun b _ => (hginv σ hσ a b).symm
  have hgo : g o o = 0 := by simp [hg, conn_self]
  change (Fintype.card V : ℝ)⁻¹ * ((1 / 2) * ∑ a, ∑ b, g a b) = _
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.add_sum_erase _ _
    (Finset.mem_univ o), hgo, zero_add]
  have hcongr : ∀ y ∈ Finset.univ.erase o, g o y = w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
      ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
        ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) ∂law (intensityProfile (lam t) 1) := by
    intro y _
    simp only [hg, add_pow_succ_sub_pow_sub_pow]
  rw [Finset.sum_congr rfl hcongr]
  field_simp

open Classical in
/-- **Sign.** For nondecreasing intensities (`w ≥ 0`) the derivative in
`hasDerivAt_moment_of_transitive` is nonnegative. -/
theorem moment_derivative_nonneg (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (q : Sym2 V → unitInterval) (o : V) (k : ℕ) :
    0 ≤ (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
          ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) ∂law q := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => mul_nonneg (hw _) ?_)
  refine integral_nonneg fun ω => ?_
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun j _ => by positivity

/-! ### Non-vacuity witness -/

open Classical in
/-- **Non-vacuity witness.** On `ZMod 2` with `λ_u = u⁺` on every pair (so `λ_u = u` near `t = 1`),
the hypotheses of `hasDerivAt_moment_of_transitive` hold, with `w = 1` and the translations
of `ZMod 2` as the transitive group. -/
example (k : ℕ) :
    HasDerivAt (fun u : ℝ => ∫ ω, ((cluster ω (0 : ZMod 2)).ncard : ℝ) ^ k
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => u.toNNReal) 1))
      ((1 / 2) * ∑ y ∈ Finset.univ.erase (0 : ZMod 2), (fun _ : Sym2 (ZMod 2) => (1 : ℝ)) s(0, y) *
        ∫ ω, (if ω ∈ conn 0 y then 0 else
          ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω 0).ncard : ℝ) ^ j *
            ((cluster ω y).ncard : ℝ) ^ (k + 1 - j))
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1)) 1 := by
  refine hasDerivAt_moment_of_transitive (fun (u : ℝ) _ => u.toNNReal) (fun _ => 1) 1 ?_ ?_ 0 k
  · intro e
    refine (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
    simp [Real.coe_toNNReal _ hu.le]
  · intro x y
    exact ⟨Equiv.addRight (y - x), by simp, fun _ _ => rfl⟩

end PercLib.Percolation.Bond
