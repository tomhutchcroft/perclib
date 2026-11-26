/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.MomentDerivativeBound
public import PercLib.Analysis.ReciprocalODE

/-!
# The truncated-moment derivative (MIJ7)

On a finite vertex set with transitive intensities `λ_u` (bonds `1 - e^{-λ_u}`, derivatives
`w = ∂_t λ_t`), and for every function `h`, the expectation `E_u h(|K_o|)` has derivative
`(1/2) ∑_{y ≠ o} w(o, y) E_t[1{o ↮ y} Φ_h(|K_o|, |K_y|)]` with
`Φ_h(A, B) = A (h(A + B) - h(A)) + B (h(A + B) - h(B))`, the change of `∑_v h(|K_v|)` when
clusters of sizes `A` and `B` merge (`hasDerivAt_integral_fun_of_transitive`).

**MIJ7** (`hasDerivAt_truncated_moment`): for real `m > 0`, `T_m(u) = E_u min(|K_o|, m)` is
differentiable at `t` with `0 ≤ T_m'(t) ≤ a(t) T_m(t)²`, `a(t) = ∑_{y ≠ o} w(o, y)`, when
`w ≥ 0`. The bound uses `A (min(A + B, m) - min(A, m)) ≤ min(A, m) min(B, m)` and BK for the
two disjoint clusters (`integral_not_conn_mul_le`); the first inequality is
`PercLib.Analysis.mul_min_add_sub_min_le`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
open Classical in
/-- **Opening one pair** changes `∑_v h(|K_v|)` by
`1{a ↮ b} (A (h(A + B) - h(A)) + B (h(A + B) - h(B)))`, `A = |K_a|`, `B = |K_b|`. -/
theorem sum_cluster_fun_insert_sub (ω : Config V) (a b : V) (h : ℝ → ℝ) :
    ∑ v, h ((cluster (insert s(a, b) ω) v).ncard) - ∑ v, h ((cluster ω v).ncard) =
      if ω ∈ conn a b then 0 else
        ((cluster ω a).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
            h ((cluster ω a).ncard)) +
          ((cluster ω b).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
            h ((cluster ω b).ncard)) := by
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
    have hterm : ∀ v, h ((cluster (insert s(a, b) ω) v).ncard) - h ((cluster ω v).ncard) =
        (if v ∈ cluster ω a then h (A + B) - h A else 0) +
          (if v ∈ cluster ω b then h (A + B) - h B else 0) := by
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

open Classical in
/-- The derivative of `E_t ∑_v h(|K_v|)` as a sum over ordered pairs:
`(1/2) ∑_a ∑_b w(a, b) E_t[1{a ↮ b} Φ_h(|K_a|, |K_b|)]`. -/
theorem hasDerivAt_integral_sum_cluster_fun (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ)
    (t : ℝ) (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (h : ℝ → ℝ) :
    HasDerivAt (fun u => ∫ ω, ∑ v, h ((cluster ω v).ncard) ∂law (intensityProfile (lam u) 1))
      ((1 / 2) * ∑ a, ∑ b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
        ((cluster ω a).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
            h ((cluster ω a).ncard)) +
          ((cluster ω b).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
            h ((cluster ω b).ncard)))
        ∂law (intensityProfile (lam t) 1)) t := by
  refine (hasDerivAt_integral_intensityProfile lam w t hlam
    (fun ω => ∑ v, h ((cluster ω v).ncard))).congr_deriv ?_
  set g : Sym2 V → ℝ := fun e => w e * ∫ ω, (if e ∈ ω then 0 else
      ∑ v, h ((cluster (insert e ω) v).ncard) - ∑ v, h ((cluster ω v).ncard))
      ∂law (intensityProfile (lam t) 1) with hg
  have hpair : ∀ a b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
          h ((cluster ω a).ncard)) +
        ((cluster ω b).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
          h ((cluster ω b).ncard)))
      ∂law (intensityProfile (lam t) 1) = g s(a, b) := by
    intro a b
    rw [hg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← sum_cluster_fun_insert_sub]
    by_cases he : s(a, b) ∈ ω
    · simp only [he, ite_true, insert_eq_of_mem he, sub_self]
    · simp only [he, ite_false]
  simp_rw [hpair]
  have hdiag : ∀ a, g s(a, a) = 0 := by
    intro a
    rw [← hpair]
    simp [conn_self]
  rw [sum_sum_mk_eq_two_mul g hdiag, nsmul_eq_mul]
  push_cast
  ring

open Classical in
/-- **Derivative of `E h(|K_o|)` under transitivity.**
`d/dt E_t h(|K_o|) = (1/2) ∑_{y ≠ o} w(o, y) E_t[1{o ↮ y} Φ_h(|K_o|, |K_y|)]`. -/
theorem hasDerivAt_integral_fun_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ)
    (t : ℝ) (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (h : ℝ → ℝ) :
    HasDerivAt (fun u => ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1))
      ((1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard)) +
          ((cluster ω y).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω y).ncard)))
        ∂law (intensityProfile (lam t) 1)) t := by
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨o⟩
  have hncard : ∀ (σ : V ≃ V) (ω : Config V) (x : V),
      (cluster (Sym2.map σ '' ω) (σ x)).ncard = (cluster ω x).ncard := by
    intro σ ω x
    rw [cluster_image, Set.ncard_image_of_injective _ σ.injective]
  have hroot : ∀ u (a : V), ∫ ω, h ((cluster ω a).ncard) ∂law (intensityProfile (lam u) 1) =
      ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1) := by
    intro u a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← integral_image_sym2Map_of_invariant (lam u) σ (hσ u)
      (fun ω => h ((cluster ω o).ncard))]
    congr 1
    funext ω
    rw [← hσa, hncard]
  have hfun : (fun u => ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1)) =
      fun u => (Fintype.card V : ℝ)⁻¹ *
        ∫ ω, ∑ v, h ((cluster ω v).ncard) ∂law (intensityProfile (lam u) 1) := by
    funext u
    rw [integral_finsetSum _ fun v _ => Integrable.of_finite]
    simp_rw [hroot u]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hV.ne', one_mul]
  rw [hfun]
  refine ((hasDerivAt_integral_sum_cluster_fun lam w t hlam h).const_mul _).congr_deriv ?_
  set g : V → V → ℝ := fun a b => w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
          h ((cluster ω a).ncard)) +
        ((cluster ω b).ncard : ℝ) * (h ((cluster ω a).ncard + (cluster ω b).ncard) -
          h ((cluster ω b).ncard)))
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
  field_simp
  rfl

/-! ### MIJ7 -/

open Classical in
/-- **Derivative of the truncated moment.** Let `V` be finite with intensities `λ_u` invariant under
a transitively acting group, differentiable at `t` with derivatives `w ≥ 0`. For every real `m > 0`,
`T_m(u) = E_u min(|K_o|, m)` is differentiable at `t`, and its derivative satisfies
`0 ≤ T_m'(t) ≤ a(t) T_m(t)²`, where `a(t) = ∑_{y ≠ o} w(o, y)`. -/
theorem hasDerivAt_truncated_moment (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t) (hw : ∀ e, 0 ≤ w e)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) {m : ℝ} (hm : 0 < m) :
    ∃ D : ℝ, HasDerivAt (fun u => ∫ ω, min ((cluster ω o).ncard : ℝ) m
        ∂law (intensityProfile (lam u) 1)) D t ∧ 0 ≤ D ∧
      D ≤ (∑ y ∈ Finset.univ.erase o, w s(o, y)) *
        (∫ ω, min ((cluster ω o).ncard : ℝ) m ∂law (intensityProfile (lam t) 1)) ^ 2 := by
  set μ := law (intensityProfile (lam t) 1)
  have hd := hasDerivAt_integral_fun_of_transitive lam w t hlam hT o (fun x => min x m)
  -- pointwise bounds on `Φ`
  have hΦ : ∀ ω : Config V, ∀ y : V,
      0 ≤ (((cluster ω o).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
          min ((cluster ω o).ncard : ℝ) m) +
        ((cluster ω y).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
          min ((cluster ω y).ncard : ℝ) m)) ∧
      (((cluster ω o).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
          min ((cluster ω o).ncard : ℝ) m) +
        ((cluster ω y).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
          min ((cluster ω y).ncard : ℝ) m)) ≤
        2 * (min ((cluster ω o).ncard : ℝ) m * min ((cluster ω y).ncard : ℝ) m) := by
    intro ω y
    have hA : (1 : ℝ) ≤ (cluster ω o).ncard :=
      Nat.one_le_cast.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨o, mem_cluster_self ω o⟩)
    have hB : (1 : ℝ) ≤ (cluster ω y).ncard :=
      Nat.one_le_cast.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨y, mem_cluster_self ω y⟩)
    have h1 := PercLib.Analysis.mul_min_add_sub_min_le (by linarith : (0 : ℝ) ≤ (cluster ω o).ncard)
      (by linarith : (0 : ℝ) ≤ (cluster ω y).ncard) hm.le
    have h2 := PercLib.Analysis.mul_min_add_sub_min_le (by linarith : (0 : ℝ) ≤ (cluster ω y).ncard)
      (by linarith : (0 : ℝ) ≤ (cluster ω o).ncard) hm.le
    rw [add_comm ((cluster ω y).ncard : ℝ)] at h2
    have hm1 : min ((cluster ω o).ncard : ℝ) m ≤ min (((cluster ω o).ncard : ℝ) +
        (cluster ω y).ncard) m := min_le_min_right _ (by linarith)
    have hm2 : min ((cluster ω y).ncard : ℝ) m ≤ min (((cluster ω o).ncard : ℝ) +
        (cluster ω y).ncard) m := min_le_min_right _ (by linarith)
    refine ⟨add_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith)), ?_⟩
    nlinarith [mul_comm (min ((cluster ω o).ncard : ℝ) m) (min ((cluster ω y).ncard : ℝ) m)]
  refine ⟨_, hd, ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => mul_nonneg (hw _) ?_)
    refine integral_nonneg fun ω => ?_
    split_ifs
    · exact le_rfl
    · exact (hΦ ω y).1
  · -- BK for the two clusters and root independence
    have hTt : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, lam t (Sym2.map σ e) = lam t e :=
      fun x y => (hT x y).imp fun σ h => ⟨h.1, h.2 t⟩
    have hy : ∀ y, ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
            min ((cluster ω o).ncard : ℝ) m) +
          ((cluster ω y).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
            min ((cluster ω y).ncard : ℝ) m)) ∂μ ≤
        2 * (∫ ω, min ((cluster ω o).ncard : ℝ) m ∂μ) ^ 2 := by
      intro y
      have hbk := integral_not_conn_mul_le (intensityProfile (lam t) 1) o y
        (f := fun n : ℕ => min (n : ℝ) m) (g := fun n : ℕ => min (n : ℝ) m)
        (fun a b hab => min_le_min_right _ (Nat.cast_le.2 hab))
        (fun a b hab => min_le_min_right _ (Nat.cast_le.2 hab))
        (by simp [hm.le]) (by simp [hm.le])
      have hroot : ∫ ω, min ((cluster ω y).ncard : ℝ) m ∂μ =
          ∫ ω, min ((cluster ω o).ncard : ℝ) m ∂μ := by
        obtain ⟨σ, hσa, hσ⟩ := hTt y o
        rw [← integral_image_sym2Map_of_invariant (lam t) σ hσ
          (fun ω => min ((cluster ω o).ncard : ℝ) m)]
        congr 1
        funext ω
        rw [← hσa, cluster_image, Set.ncard_image_of_injective _ σ.injective]
      rw [hroot] at hbk
      calc ∫ ω, (if ω ∈ conn o y then 0 else
            ((cluster ω o).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
                min ((cluster ω o).ncard : ℝ) m) +
              ((cluster ω y).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) +
                (cluster ω y).ncard) m - min ((cluster ω y).ncard : ℝ) m)) ∂μ
          ≤ ∫ ω, 2 * (if ω ∈ conn o y then 0 else
              min ((cluster ω o).ncard : ℝ) m * min ((cluster ω y).ncard : ℝ) m) ∂μ := by
            refine integral_mono Integrable.of_finite Integrable.of_finite fun ω => ?_
            simp only
            split_ifs
            · simp
            · exact (hΦ ω y).2
        _ = 2 * ∫ ω, (if ω ∈ conn o y then 0 else
              min ((cluster ω o).ncard : ℝ) m * min ((cluster ω y).ncard : ℝ) m) ∂μ :=
            integral_const_mul _ _
        _ ≤ 2 * (∫ ω, min ((cluster ω o).ncard : ℝ) m ∂μ) ^ 2 := by
            rw [sq]; linarith
    calc (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
          ((cluster ω o).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
              min ((cluster ω o).ncard : ℝ) m) +
            ((cluster ω y).ncard : ℝ) * (min (((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) m -
              min ((cluster ω y).ncard : ℝ) m)) ∂μ
        ≤ (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) *
            (2 * (∫ ω, min ((cluster ω o).ncard : ℝ) m ∂μ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by norm_num)
          exact mul_le_mul_of_nonneg_left (hy y) (hw _)
      _ = _ := by rw [← Finset.sum_mul]; ring

/-! ### Non-vacuity witness -/

/-- **Non-vacuity witness.** On `ZMod 2` with `λ_u = u⁺` (`= u` near `t = 1`), `w = 1` and `m = 1/2`
(below one), the hypotheses of `hasDerivAt_truncated_moment` hold. -/
example : ∃ D : ℝ, HasDerivAt (fun u : ℝ => ∫ ω, min ((cluster ω (0 : ZMod 2)).ncard : ℝ) (1 / 2)
      ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => u.toNNReal) 1)) D 1 ∧ 0 ≤ D ∧
    D ≤ (∑ y ∈ Finset.univ.erase (0 : ZMod 2), (fun _ : Sym2 (ZMod 2) => (1 : ℝ)) s(0, y)) *
      (∫ ω, min ((cluster ω (0 : ZMod 2)).ncard : ℝ) (1 / 2)
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1)) ^ 2 := by
  refine hasDerivAt_truncated_moment (fun (u : ℝ) _ => u.toNNReal) (fun _ => 1) 1 ?_
    (fun _ => zero_le_one) (fun x y => ⟨Equiv.addRight (y - x), by simp, fun _ _ => rfl⟩) 0
    (by norm_num)
  intro e
  refine (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
  simp [Real.coe_toNNReal _ hu.le]

end PercLib.Percolation.Bond
