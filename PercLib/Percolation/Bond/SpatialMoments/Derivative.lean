/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. Statements from the wiki article `spatial-cutoff-moments` (tags
57RX, 1K61); source T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.4.1
and §I.5.1. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.MomentDerivatives

/-!
# Derivatives of spatial moments in finite volume (57RX, 1K61)

On a finite vertex set (for instance a box `Λ ⊆ ℤ^d`, with `λ_t(s(x, y)) = k_t(y - x)`),
bonds are independent with probability `1 - e^{-λ_t(e)}` and `w(e) = ∂_t λ_t(e)`.

* `hasDerivAt_integral_cluster_functional`: for every functional `F` of the cluster of `o`,
  `d/dt E_t F(K_o) = ∑_{x, y} w(x, y) E_t[1{x ∈ K_o, y ∉ K_o} (F(K_o ∪ K_y) - F(K_o))]`
  (Russo with the closed indicator kept; opening a pair with exactly one endpoint in `K_o`
  adds `K_y`).
* **57RX, finite volume** (`hasDerivAt_integral_sum_cluster`): for a weight `g`, in particular
  `g(z) = ⟨z - o, u⟩²`,
  `d/dt E_t[∑_{z ∈ K_o} g(z)] = ∑_{x, y} w(x, y) E_t[1{x ∈ K_o, y ∉ K_o} ∑_{z ∈ K_y} g(z)]`.
* **1K61, finite volume** (`hasDerivAt_integral_prod_sum_cluster`): for
  `F(A) = ∏_i ∑_{z ∈ A} P_i(z)`,
  `d/dt E_t F(K_o) = ∑_{x, y} w(x, y) E_t[1{x ∈ K_o, y ∉ K_o}
    ∑_{∅ ≠ I} (∏_{i ∉ I} ∑_{K_o} P_i)(∏_{i ∈ I} ∑_{K_y} P_i)]`.

The diagonal terms `x = y` vanish, since `x ∈ K_o` and `x ∉ K_o` cannot both hold.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- **Opening one pair, seen from `o`.** The change of `F(K_o)` when `s(x, y)` is opened
(counted only when it was closed) is the sum of the two one-sided terms
`1{x ∈ K_o, y ∉ K_o}(F(K_o ∪ K_y) - F(K_o))` and the same with `x, y` exchanged. -/
theorem insert_sub_eq_add (ω : Config V) (o x y : V) (F : Set V → ℝ) :
    (if s(x, y) ∈ ω then 0 else F (cluster (insert s(x, y) ω) o) - F (cluster ω o)) =
      (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
          F (cluster ω o ∪ cluster ω y) - F (cluster ω o) else 0) +
        (if y ∈ cluster ω o ∧ x ∉ cluster ω o then
          F (cluster ω o ∪ cluster ω x) - F (cluster ω o) else 0) := by
  have hceq : ∀ {a z : V}, z ∈ cluster ω a → cluster ω z = cluster ω a := fun hz =>
    (cluster_eq_iff_conn ω _ _).2 ((mem_cluster_comm ω _ _).1 hz)
  by_cases hx : x ∈ cluster ω o <;> by_cases hy : y ∈ cluster ω o
  · -- both endpoints in `K_o`: nothing changes
    have hKx := hceq hx
    have hKy := hceq hy
    simp only [hx, hy, not_true_eq_false, and_false, ite_false, add_zero]
    split_ifs
    · rfl
    · rw [cluster_insert_of_mem ω x y o (Or.inl ((mem_cluster_comm ω _ _).1 hx)), hKx, hKy,
        union_self, sub_self]
  · -- `x ∈ K_o`, `y ∉ K_o`
    have hKx := hceq hx
    have he : s(x, y) ∉ ω := fun he => hy (by
      by_cases hxy : x = y
      · exact hxy ▸ hx
      · exact conn_trans hx (mem_conn_of_mem hxy he))
    rw [cluster_insert_of_mem ω x y o (Or.inl ((mem_cluster_comm ω _ _).1 hx)), hKx]
    simp [hx, hy, he]
  · -- `y ∈ K_o`, `x ∉ K_o`
    have hKy := hceq hy
    have he : s(x, y) ∉ ω := fun he => hx (by
      by_cases hxy : x = y
      · exact hxy ▸ hy
      · exact conn_trans hy (mem_conn_of_mem (Ne.symm hxy) (by rw [Sym2.eq_swap]; exact he)))
    rw [cluster_insert_of_mem ω x y o (Or.inr ((mem_cluster_comm ω _ _).1 hy)), hKy,
      union_comm]
    simp [hx, hy, he]
  · -- neither endpoint in `K_o`: nothing changes
    have ho : o ∉ cluster ω x ∪ cluster ω y := by
      rintro (h | h)
      · exact hx ((mem_cluster_comm ω _ _).1 h)
      · exact hy ((mem_cluster_comm ω _ _).1 h)
    simp only [hx, hy, false_and, ite_false, add_zero]
    split_ifs
    · rfl
    · rw [cluster_insert_of_not_mem ω x y o ho, sub_self]

open Classical in
/-- **Derivative of a cluster functional.** For every `F : Set V → ℝ`,
`d/dt E_t F(K_o) = ∑_{x, y} w(x, y) E_t[1{x ∈ K_o, y ∉ K_o}(F(K_o ∪ K_y) - F(K_o))]`. -/
theorem hasDerivAt_integral_cluster_functional (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ)
    (t : ℝ) (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (o : V)
    (F : Set V → ℝ) :
    HasDerivAt (fun u => ∫ ω, F (cluster ω o) ∂law (intensityProfile (lam u) 1))
      (∑ x, ∑ y, w s(x, y) * ∫ ω, (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
        F (cluster ω o ∪ cluster ω y) - F (cluster ω o) else 0)
        ∂law (intensityProfile (lam t) 1)) t := by
  refine (hasDerivAt_integral_intensityProfile lam w t hlam (fun ω => F (cluster ω o))).congr_deriv
    ?_
  set μ := law (intensityProfile (lam t) 1)
  set h : V → V → ℝ := fun x y => w s(x, y) * ∫ ω, (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
      F (cluster ω o ∪ cluster ω y) - F (cluster ω o) else 0) ∂μ with hh
  set D : Sym2 V → ℝ := fun e => w e * ∫ ω, (if e ∈ ω then 0 else
      F (cluster (insert e ω) o) - F (cluster ω o)) ∂μ with hD
  have hDxy : ∀ x y, D s(x, y) = h x y + h y x := by
    intro x y
    simp only [hD, hh]
    simp_rw [insert_sub_eq_add]
    rw [integral_add Integrable.of_finite Integrable.of_finite, mul_add, Sym2.eq_swap]
  have hdiag : ∀ a, D s(a, a) = 0 := by
    intro a
    rw [hDxy]
    simp [hh]
  have h2 := sum_sum_mk_eq_two_mul D hdiag
  simp_rw [hDxy, Finset.sum_add_distrib] at h2
  rw [Finset.sum_comm (f := fun x y => h y x)] at h2
  simp only [nsmul_eq_mul] at h2
  change ∑ e, D e = ∑ x, ∑ y, h x y
  push_cast at h2
  linarith

open Classical in
/-- **Finite volume.** For every weight `g : V → ℝ` (for instance
`g(z) = ⟨z - o, u⟩²` on a box of `ℤ^d`),
`d/dt E_t[∑_{z ∈ K_o} g(z)] = ∑_{x, y} w(x, y) E_t[1{x ∈ K_o, y ∉ K_o} ∑_{z ∈ K_y} g(z)]`. -/
theorem hasDerivAt_integral_sum_cluster (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (o : V) (g : V → ℝ) :
    HasDerivAt (fun u => ∫ ω, ∑ z, (cluster ω o).indicator g z
        ∂law (intensityProfile (lam u) 1))
      (∑ x, ∑ y, w s(x, y) * ∫ ω, (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
        ∑ z, (cluster ω y).indicator g z else 0) ∂law (intensityProfile (lam t) 1)) t := by
  refine (hasDerivAt_integral_cluster_functional lam w t hlam o
    (fun A => ∑ z, A.indicator g z)).congr_deriv ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  split_ifs with hxy
  · have hdisj : Disjoint (cluster ω o) (cluster ω y) := by
      refine Set.disjoint_left.2 fun z hzo hzy => hxy.2 ?_
      exact conn_trans hzo (by rw [conn_symm]; exact hzy)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [indicator_union_of_disjoint hdisj, add_sub_cancel_left]
  · rfl

/-- `∏_i (a_i + b_i) - ∏_i a_i = ∑_{∅ ≠ I} (∏_{i ∉ I} a_i)(∏_{i ∈ I} b_i)`. -/
theorem prod_add_sub_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) :
    ∏ i, (a i + b i) - ∏ i, a i =
      ∑ I ∈ (Finset.univ : Finset ι).powerset.erase ∅,
        (∏ i ∈ Finset.univ \ I, a i) * ∏ i ∈ I, b i := by
  have h := Finset.prod_add (s := (Finset.univ : Finset ι)) b a
  simp_rw [add_comm (a _) (b _)]
  rw [h, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

open Classical in
/-- **Finite volume.** For polynomial functionals `F(A) = ∏_i ∑_{z ∈ A} P_i(z)`,
`d/dt E_t F(K_o) = ∑_{x, y} w(x, y) E_t[1{x ∈ K_o, y ∉ K_o}
  ∑_{∅ ≠ I} (∏_{i ∉ I} ∑_{K_o} P_i)(∏_{i ∈ I} ∑_{K_y} P_i)]`. -/
theorem hasDerivAt_integral_prod_sum_cluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (o : V) (P : ι → V → ℝ) :
    HasDerivAt (fun u => ∫ ω, ∏ i, ∑ z, (cluster ω o).indicator (P i) z
        ∂law (intensityProfile (lam u) 1))
      (∑ x, ∑ y, w s(x, y) * ∫ ω, (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
        ∑ I ∈ (Finset.univ : Finset ι).powerset.erase ∅,
          (∏ i ∈ Finset.univ \ I, ∑ z, (cluster ω o).indicator (P i) z) *
            ∏ i ∈ I, ∑ z, (cluster ω y).indicator (P i) z else 0)
        ∂law (intensityProfile (lam t) 1)) t := by
  refine (hasDerivAt_integral_cluster_functional lam w t hlam o
    (fun A => ∏ i, ∑ z, A.indicator (P i) z)).congr_deriv ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  split_ifs with hxy
  · have hdisj : Disjoint (cluster ω o) (cluster ω y) := by
      refine Set.disjoint_left.2 fun z hzo hzy => hxy.2 ?_
      exact conn_trans hzo (by rw [conn_symm]; exact hzy)
    have hsplit : ∀ i, ∑ z, (cluster ω o ∪ cluster ω y).indicator (P i) z =
        ∑ z, (cluster ω o).indicator (P i) z + ∑ z, (cluster ω y).indicator (P i) z := by
      intro i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => congrFun (indicator_union_of_disjoint hdisj _) z
    simp_rw [hsplit]
    exact prod_add_sub_prod _ _
  · rfl

/-! ### Non-vacuity witness -/

open Classical in
/-- **Non-vacuity witness.** Two points (`Bool`), `λ_u = u⁺` on the pair (`= u` near `t = 1`), and
the weight `g = 1{·= true}`: the hypotheses of `hasDerivAt_integral_sum_cluster` hold. -/
example :
    HasDerivAt (fun u : ℝ => ∫ ω, ∑ z, (cluster ω false).indicator
        (fun z : Bool => if z then (1 : ℝ) else 0) z
        ∂law (intensityProfile (fun _ : Sym2 Bool => u.toNNReal) 1))
      (∑ x, ∑ y, (fun _ : Sym2 Bool => (1 : ℝ)) s(x, y) * ∫ ω,
        (if x ∈ cluster ω false ∧ y ∉ cluster ω false then
          ∑ z, (cluster ω y).indicator (fun z : Bool => if z then (1 : ℝ) else 0) z else 0)
        ∂law (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ).toNNReal) 1)) 1 := by
  refine hasDerivAt_integral_sum_cluster (fun (u : ℝ) _ => u.toNNReal) (fun _ => 1) 1 ?_ false _
  intro e
  refine (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
  simp [Real.coe_toNNReal _ hu.le]

end PercLib.Percolation.Bond
