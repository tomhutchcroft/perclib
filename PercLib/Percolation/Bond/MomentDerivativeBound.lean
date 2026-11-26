/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.MomentDerivatives
public import PercLib.Probability.CountableBK

/-!
# The BK bound for cluster-moment derivatives (C9Y8, bound)

On a finite vertex set:

* `cluster_inter_sym2_cluster`: the cluster of `o` is already the cluster of `o` in the
  configuration of its own internal open pairs (the BK witness).
* `law_not_conn_le_le_le` (**BK for disjoint clusters**):
  `P(o ↮ y, |K_o| ≥ a, |K_y| ≥ b) ≤ P(|K_o| ≥ a) P(|K_y| ≥ b)`.
* `integral_not_conn_mul_le`: for nondecreasing `f, g : ℕ → ℝ` vanishing at `0`,
  `E[1{o ↮ y} f(|K_o|) g(|K_y|)] ≤ E f(|K_o|) E g(|K_y|)`.
* `moment_derivative_le_of_transitive` (**C9Y8, bound**): for a transitive family with
  `w ≥ 0`, the derivative of `hasDerivAt_moment_of_transitive` is at most
  `(a(t)/2) ∑_{j=1}^k C(k+1, j) m_j m_{k+1-j}`, `a(t) = ∑_{y ≠ o} w(o, y)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The BK witness of a cluster -/

/-- The cluster of `o` in the configuration of the open pairs inside it is the same cluster. -/
theorem cluster_inter_sym2_cluster (ω : Config V) (o : V) :
    cluster (ω ∩ (cluster ω o).sym2) o = cluster ω o := by
  refine Subset.antisymm (cluster_mono inter_subset_left o) ?_
  intro v hv
  change (openGraph ω).Reachable o v at hv
  rw [SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact mem_cluster_self _ o
  | @tail z u hz hadj ih =>
    have hzK : z ∈ cluster ω o := (SimpleGraph.reachable_iff_reflTransGen _ _).2 hz
    have huK : u ∈ cluster ω o := conn_trans hzK (SimpleGraph.Adj.reachable hadj)
    rw [openGraph_adj_iff] at hadj
    exact conn_trans ih (SimpleGraph.Adj.reachable ((openGraph_adj_iff _ z u).2
      ⟨⟨hadj.1, Set.mk_mem_sym2_iff.2 ⟨hzK, huK⟩⟩, hadj.2⟩))

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Events `a ≤ |K_x|` are increasing. -/
theorem isUpperSet_le_ncard_cluster (x : V) (a : ℕ) :
    IsUpperSet {ω : Config V | a ≤ (cluster ω x).ncard} := fun _ _ h hω =>
  hω.trans (Set.ncard_le_ncard (cluster_mono h x) (Set.toFinite _))

omit [DecidableEq V] in
/-- **BK for disjoint clusters.**
`P(o ↮ y, |K_o| ≥ a, |K_y| ≥ b) ≤ P(|K_o| ≥ a) P(|K_y| ≥ b)`. -/
theorem law_not_conn_le_le_le (q : Sym2 V → unitInterval) (o y : V) (a b : ℕ) :
    law q {ω | ω ∉ conn o y ∧ a ≤ (cluster ω o).ncard ∧ b ≤ (cluster ω y).ncard} ≤
      law q {ω | a ≤ (cluster ω o).ncard} * law q {ω | b ≤ (cluster ω y).ncard} := by
  refine le_trans (measure_mono ?_) (countable_profile_bk q (isUpperSet_le_ncard_cluster o a)
    (isUpperSet_le_ncard_cluster y b))
  rintro ω ⟨hc, ha, hb⟩
  rw [mem_disjointOccurrence_iff_open (isUpperSet_le_ncard_cluster o a)
    (isUpperSet_le_ncard_cluster y b)]
  refine ⟨ω ∩ (cluster ω o).sym2, ω ∩ (cluster ω y).sym2, Set.toFinite _, Set.toFinite _, ?_,
    inter_subset_left, inter_subset_left, ?_, ?_⟩
  · refine Set.disjoint_left.2 fun e he1 he2 => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have hu1 := (Set.mk_mem_sym2_iff.1 he1.2).1
      have hu2 := (Set.mk_mem_sym2_iff.1 he2.2).1
      exact hc (conn_trans hu1 (by rw [conn_symm]; exact hu2))
  · change a ≤ _
    rw [cluster_inter_sym2_cluster]
    exact ha
  · change b ≤ _
    rw [cluster_inter_sym2_cluster]
    exact hb

omit [DecidableEq V] in
/-- A nondecreasing `f : ℕ → ℝ` with `f 0 = 0`, evaluated at `n ≤ N`, is the sum of its
increments over the levels `a < N` with `a + 1 ≤ n`. -/
theorem eq_sum_increments {f : ℕ → ℝ} (hf0 : f 0 = 0) {n N : ℕ} (hn : n ≤ N) :
    f n = ∑ a ∈ Finset.range N, (f (a + 1) - f a) * (if a + 1 ≤ n then 1 else 0) := by
  have h : ∀ a ∈ Finset.range N, (f (a + 1) - f a) * (if a + 1 ≤ n then (1 : ℝ) else 0) =
      if a ∈ Finset.range n then f (a + 1) - f a else 0 := by
    intro a _
    by_cases ha : a + 1 ≤ n
    · simp [ha, show a < n by omega]
    · simp [ha, show ¬ a < n by omega]
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter,
    show (Finset.range N).filter (· ∈ Finset.range n) = Finset.range n by
      ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega,
    Finset.sum_range_sub (f := f), hf0, sub_zero]

omit [DecidableEq V] in
open Classical in
/-- **BK for functionals of disjoint clusters.** For nondecreasing `f, g : ℕ → ℝ` with
`f 0 = g 0 = 0`, `E[1{o ↮ y} f(|K_o|) g(|K_y|)] ≤ E f(|K_o|) E g(|K_y|)`. -/
theorem integral_not_conn_mul_le (q : Sym2 V → unitInterval) (o y : V) {f g : ℕ → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    ∫ ω, (if ω ∈ conn o y then 0 else f (cluster ω o).ncard * g (cluster ω y).ncard)
        ∂law q ≤
      (∫ ω, f (cluster ω o).ncard ∂law q) * ∫ ω, g (cluster ω y).ncard ∂law q := by
  set N := Fintype.card V + 1
  have hle : ∀ (ω : Config V) x, (cluster ω x).ncard ≤ N := fun ω x =>
    (Set.ncard_le_card _).trans (by simp [N])
  have hdf : ∀ a, 0 ≤ f (a + 1) - f a := fun a => sub_nonneg.2 (hf (Nat.le_succ a))
  have hdg : ∀ b, 0 ≤ g (b + 1) - g b := fun b => sub_nonneg.2 (hg (Nat.le_succ b))
  -- indicator integrals as probabilities
  have hind : ∀ (A : Set (Config V)), ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂law q =
      (law q).real A := fun A => by
    rw [integral_indicator_const _ (Set.toFinite A).measurableSet, smul_eq_mul, mul_one]
  -- expand all three integrands
  have hL : ∀ ω : Config V, (if ω ∈ conn o y then 0 else
      f (cluster ω o).ncard * g (cluster ω y).ncard) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, (f (a + 1) - f a) * (g (b + 1) - g b) *
        {ω' : Config V | ω' ∉ conn o y ∧ a + 1 ≤ (cluster ω' o).ncard ∧
          b + 1 ≤ (cluster ω' y).ncard}.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hc : ω ∈ conn o y
    · simp [hc]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), eq_sum_increments hf0 (hle ω o),
        eq_sum_increments hg0 (hle ω y),
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases ha : a < (cluster ω o).ncard <;> by_cases hb : b < (cluster ω y).ncard <;>
        simp [indicator, ha, hb, hc]
  have hX : ∀ ω : Config V, f (cluster ω o).ncard = ∑ a ∈ Finset.range N, (f (a + 1) - f a) *
      {ω' : Config V | a + 1 ≤ (cluster ω' o).ncard}.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    rw [eq_sum_increments hf0 (hle ω o)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a < (cluster ω o).ncard <;> simp [indicator, ha]
  have hY : ∀ ω : Config V, g (cluster ω y).ncard = ∑ b ∈ Finset.range N, (g (b + 1) - g b) *
      {ω' : Config V | b + 1 ≤ (cluster ω' y).ncard}.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    rw [eq_sum_increments hg0 (hle ω y)]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b < (cluster ω y).ncard <;> simp [indicator, hb]
  simp_rw [hL, hX, hY]
  rw [integral_finsetSum _ fun a _ => Integrable.of_finite,
    integral_finsetSum _ fun a _ => Integrable.of_finite,
    integral_finsetSum _ fun a _ => Integrable.of_finite, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => Integrable.of_finite]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_const_mul, hind, hind, hind]
  have hbk := countable_profile_bk_real q (isUpperSet_le_ncard_cluster o (a + 1))
    (isUpperSet_le_ncard_cluster y (b + 1))
  have hsub : (law q).real {ω' : Config V | ω' ∉ conn o y ∧ a + 1 ≤ (cluster ω' o).ncard ∧
      b + 1 ≤ (cluster ω' y).ncard} ≤ (law q).real {ω | a + 1 ≤ (cluster ω o).ncard} *
        (law q).real {ω | b + 1 ≤ (cluster ω y).ncard} := by
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (law_not_conn_le_le_le q o y (a + 1) (b + 1))
  calc (f (a + 1) - f a) * (g (b + 1) - g b) * (law q).real {ω' : Config V | ω' ∉ conn o y ∧
        a + 1 ≤ (cluster ω' o).ncard ∧ b + 1 ≤ (cluster ω' y).ncard}
      ≤ (f (a + 1) - f a) * (g (b + 1) - g b) * ((law q).real {ω | a + 1 ≤ (cluster ω o).ncard} *
        (law q).real {ω | b + 1 ≤ (cluster ω y).ncard}) :=
        mul_le_mul_of_nonneg_left hsub (mul_nonneg (hdf a) (hdg b))
    _ = _ := by ring

/-! ### The bound for the moment derivative -/

omit [Fintype V] [DecidableEq V] in
/-- Under transitivity of `J`, the moments `E|K_x|^l` do not depend on the root. -/
theorem integral_ncard_pow_eq_of_transitive (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (x o : V) (l : ℕ) :
    ∫ ω, ((cluster ω x).ncard : ℝ) ^ l ∂law (intensityProfile J 1) =
      ∫ ω, ((cluster ω o).ncard : ℝ) ^ l ∂law (intensityProfile J 1) := by
  obtain ⟨σ, hσx, hσ⟩ := hT x o
  rw [← integral_image_sym2Map_of_invariant J σ hσ (fun ω => ((cluster ω o).ncard : ℝ) ^ l)]
  congr 1
  funext ω
  rw [← hσx, cluster_image, Set.ncard_image_of_injective _ σ.injective]

open Classical in
/-- **Bound.** For a transitive family with `w ≥ 0`, the derivative
`m_k'(t)` of `hasDerivAt_moment_of_transitive` satisfies
`m_k'(t) ≤ (a(t)/2) ∑_{j=1}^k C(k+1, j) m_j(t) m_{k+1-j}(t)`, where
`a(t) = ∑_{y ≠ o} w(o, y)` and `m_j(t) = E_t|K_o|^j`. -/
theorem moment_derivative_le_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (k : ℕ) :
    (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
          ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) ∂law (intensityProfile (lam t) 1) ≤
      (1 / 2) * (∑ y ∈ Finset.univ.erase o, w s(o, y)) *
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) *
          (∫ ω, ((cluster ω o).ncard : ℝ) ^ j ∂law (intensityProfile (lam t) 1)) *
          ∫ ω, ((cluster ω o).ncard : ℝ) ^ (k + 1 - j) ∂law (intensityProfile (lam t) 1) := by
  set μ := law (intensityProfile (lam t) 1)
  have hTt : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, lam t (Sym2.map σ e) = lam t e :=
    fun x y => (hT x y).imp fun σ h => ⟨h.1, h.2 t⟩
  have hy : ∀ y, ∫ ω, (if ω ∈ conn o y then 0 else
      ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
        ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) ∂μ ≤
      ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) *
        (∫ ω, ((cluster ω o).ncard : ℝ) ^ j ∂μ) *
        ∫ ω, ((cluster ω o).ncard : ℝ) ^ (k + 1 - j) ∂μ := by
    intro y
    have hsplit : ∀ ω : Config V, (if ω ∈ conn o y then 0 else
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
          ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) =
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * (if ω ∈ conn o y then 0 else
          ((cluster ω o).ncard : ℝ) ^ j * ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) := by
      intro ω
      split_ifs
      · simp
      · exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hsplit]
    rw [integral_finsetSum _ fun j _ => Integrable.of_finite]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
    rw [integral_const_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h := integral_not_conn_mul_le (intensityProfile (lam t) 1) o y
      (f := fun n : ℕ => (n : ℝ) ^ j) (g := fun n : ℕ => (n : ℝ) ^ (k + 1 - j))
      (fun a b hab => pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.2 hab) _)
      (fun a b hab => pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.2 hab) _)
      (by simp; omega) (by simp; omega)
    rw [integral_ncard_pow_eq_of_transitive (lam t) hTt y o] at h
    exact h
  calc (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω o).ncard : ℝ) ^ j *
          ((cluster ω y).ncard : ℝ) ^ (k + 1 - j)) ∂μ
      ≤ (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) *
          ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) *
            (∫ ω, ((cluster ω o).ncard : ℝ) ^ j ∂μ) *
            ∫ ω, ((cluster ω o).ncard : ℝ) ^ (k + 1 - j) ∂μ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by norm_num)
        exact mul_le_mul_of_nonneg_left (hy y) (hw _)
    _ = _ := by rw [mul_assoc (1 / 2 : ℝ), Finset.sum_mul]

/-! ### Non-vacuity witness -/

open Classical in
/-- **Non-vacuity witness.** On `ZMod 2` with `λ_u = u⁺` and `w = 1`, the hypotheses of
`moment_derivative_le_of_transitive` hold, for every `k`. -/
example (k : ℕ) :
    (1 / 2) * ∑ y ∈ Finset.univ.erase (0 : ZMod 2), (fun _ : Sym2 (ZMod 2) => (1 : ℝ)) s(0, y) *
        ∫ ω, (if ω ∈ conn 0 y then 0 else
          ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) * ((cluster ω 0).ncard : ℝ) ^ j *
            ((cluster ω y).ncard : ℝ) ^ (k + 1 - j))
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1) ≤
      (1 / 2) * (∑ y ∈ Finset.univ.erase (0 : ZMod 2),
          (fun _ : Sym2 (ZMod 2) => (1 : ℝ)) s(0, y)) *
        ∑ j ∈ Finset.Icc 1 k, ((k + 1).choose j : ℝ) *
          (∫ ω, ((cluster ω 0).ncard : ℝ) ^ j
            ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1)) *
          ∫ ω, ((cluster ω 0).ncard : ℝ) ^ (k + 1 - j)
            ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1) :=
  moment_derivative_le_of_transitive (fun (u : ℝ) _ => u.toNNReal) (fun _ => 1) 1
    (fun _ => zero_le_one) (fun x y => ⟨Equiv.addRight (y - x), by simp, fun _ _ => rfl⟩) 0 k

end PercLib.Percolation.Bond
