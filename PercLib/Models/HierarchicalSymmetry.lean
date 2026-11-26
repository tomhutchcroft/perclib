/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: translations and ultrametric isometries of the hierarchical
lattice preserve radial percolation laws. From the hierarchical geometry and transport theorems of
this library and pinned mathlib's finitely supported functions. No upstream code is copied, no
definition is added and no Input is introduced.
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.Susceptibility

/-! # Symmetries of the hierarchical lattice

On `ℕ →₀ A` the level of `z` is `h z = z.support.sup Nat.succ`, and `h (a - b) ≤ k` exactly
when `a` and `b` agree at every index `≥ k` (`level_sub_le_iff_forall`). A pair intensity is
radial when `J s(x,y) = f (h (y - x))`.

* G3 (`exists_levelIsometry`): if `h (y - x) = h (y' - x')` there is a bijection `φ` with
  `h (φ a - φ b) = h (a - b)` for all `a b`, `φ x = x'` and `φ y = y'`. For level `m + 1` it is
  `a ↦ F (a - x) + x'`, where `F` translates the level-`m` ball of `y - x` onto that of
  `y' - x'` and back (`exists_levelIsometry_swap`).
* Every level isometry preserves a radial `J` (`radial_map_eq_of_levelIsometry`), hence its law.
* G2: translations preserve the two-point function, the susceptibility, the law of the cluster
  volume and internal connection in balls.
* G3 consequences: `tau q x y` and the internal connection probability in the ball of level
  `h (y - x)` depend only on `h (y - x)`; the corollary
  `tau_eq_inv_card_mul_tsum_shell` writes `tau q 0 x` as the shell average.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

section Isometry

variable {A : Type*} [AddCommGroup A]

/-- `h (a - b) ≤ k` exactly when `a` and `b` agree at every index `≥ k`. -/
theorem level_sub_le_iff_forall (a b : ℕ →₀ A) (k : ℕ) :
    (a - b).support.sup Nat.succ ≤ k ↔ ∀ i, k ≤ i → a i = b i := by
  rw [level_le_iff_support]
  constructor
  · intro h i hi
    by_contra hne
    have := h i (Finsupp.mem_support_iff.2 (by simpa [sub_eq_zero] using hne))
    omega
  · intro h i hi
    by_contra hk
    exact Finsupp.mem_support_iff.1 hi (by simp [h i (not_lt.1 hk)])

/-- A vector of level `m + 1` vanishes above `m` and not at `m`. -/
theorem apply_ne_zero_of_level_eq_succ {u : ℕ →₀ A} {m : ℕ}
    (hu : u.support.sup Nat.succ = m + 1) : u m ≠ 0 ∧ ∀ i, m < i → u i = 0 := by
  refine ⟨fun h0 => ?_, fun i hi => ?_⟩
  · have : u.support.sup Nat.succ ≤ m := by
      rw [level_le_iff_support]
      intro i hi
      have hi' := (level_le_iff_support u (m + 1)).1 hu.le i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
      · exact h
      · subst h
        exact absurd h0 (Finsupp.mem_support_iff.1 hi)
    omega
  · by_contra hne
    have := (level_le_iff_support u (m + 1)).1 hu.le i (Finsupp.mem_support_iff.2 hne)
    omega

/-- Two maps with the same value of `h` on every difference. -/
theorem level_sub_eq_of_forall_iff {a b a' b' : ℕ →₀ A}
    (h : ∀ k, (∀ i, k ≤ i → a i = b i) ↔ (∀ i, k ≤ i → a' i = b' i)) :
    (a - b).support.sup Nat.succ = (a' - b').support.sup Nat.succ := by
  refine le_antisymm ?_ ?_
  · rw [level_sub_le_iff_forall]
    exact (h _).2 ((level_sub_le_iff_forall _ _ _).1 le_rfl)
  · rw [level_sub_le_iff_forall]
    exact (h _).1 ((level_sub_le_iff_forall _ _ _).1 le_rfl)

open Classical in
/-- **The ball swap.** If `u` and `v` agree above `m`, there is a level isometry that acts as
`a ↦ a - u + v` on the level-`m` ball of `u` (the `a` agreeing with `u` at every index `≥ m`)
and fixes every `a` outside the level-`m` balls of `u` and `v`. -/
theorem exists_levelIsometry_swap (m : ℕ) (u v : ℕ →₀ A) (huv : ∀ i, m < i → u i = v i) :
    ∃ φ : (ℕ →₀ A) ≃ (ℕ →₀ A),
      (∀ a b, (φ a - φ b).support.sup Nat.succ = (a - b).support.sup Nat.succ) ∧
      (∀ a, (∀ i, m ≤ i → a i = u i) → φ a = a - u + v) ∧
      (∀ a, (¬ ∀ i, m ≤ i → a i = u i) → (¬ ∀ i, m ≤ i → a i = v i) → φ a = a) := by
  let F : (ℕ →₀ A) → (ℕ →₀ A) → (ℕ →₀ A) → (ℕ →₀ A) := fun u v a =>
    if ∀ i, m ≤ i → a i = u i then a - u + v
    else if ∀ i, m ≤ i → a i = v i then a - v + u else a
  -- Above `m` nothing moves.
  have P1 : ∀ u v : ℕ →₀ A, (∀ i, m < i → u i = v i) → ∀ a i, m < i → F u v a i = a i := by
    intro u v huv a i hi
    simp only [F]
    split_ifs <;> simp [huv i hi]
  -- On a ball of level `m`, `F` is one translation.
  have P2 : ∀ u v a b, (∀ i, m ≤ i → a i = b i) → F u v a - F u v b = a - b := by
    intro u v a b hab
    have hu : (∀ i, m ≤ i → a i = u i) ↔ (∀ i, m ≤ i → b i = u i) :=
      ⟨fun h i hi => (hab i hi).symm.trans (h i hi), fun h i hi => (hab i hi).trans (h i hi)⟩
    have hv : (∀ i, m ≤ i → a i = v i) ↔ (∀ i, m ≤ i → b i = v i) :=
      ⟨fun h i hi => (hab i hi).symm.trans (h i hi), fun h i hi => (hab i hi).trans (h i hi)⟩
    simp only [F]
    by_cases h1 : ∀ i, m ≤ i → a i = u i
    · rw [ite_eq_left h1, ite_eq_left (hu.1 h1)]; abel
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hu.2 h))]
      by_cases h2 : ∀ i, m ≤ i → a i = v i
      · rw [ite_eq_left h2, ite_eq_left (hv.1 h2)]; abel
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (hv.2 h))]
  -- Agreement above any `k` is preserved.
  have P3 : ∀ u v : ℕ →₀ A, (∀ i, m < i → u i = v i) → ∀ a b k,
      (∀ i, k ≤ i → a i = b i) → ∀ i, k ≤ i → F u v a i = F u v b i := by
    intro u v huv a b k hab i hi
    rcases lt_or_ge m k with hk | hk
    · rw [P1 u v huv a i (hk.trans_le hi), P1 u v huv b i (hk.trans_le hi)]
      exact hab i hi
    · have h := congrArg (· i) (P2 u v a b fun j hj => hab j (hk.trans hj))
      simp only [Finsupp.coe_sub, Pi.sub_apply] at h
      rw [← sub_eq_zero, h, hab i hi, sub_self]
  -- `F v u` inverts `F u v`.
  have P4 : ∀ u v a, F v u (F u v a) = a := by
    intro u v a
    simp only [F]
    by_cases h1 : ∀ i, m ≤ i → a i = u i
    · have hb : ∀ i, m ≤ i → (a - u + v) i = v i := fun i hi => by simp [h1 i hi]
      rw [ite_eq_left h1, ite_eq_left hb]; abel
    · rw [ite_eq_right h1]
      by_cases h2 : ∀ i, m ≤ i → a i = v i
      · have hb : ∀ i, m ≤ i → (a - v + u) i = u i := fun i hi => by simp [h2 i hi]
        have hb' : ¬ ∀ i, m ≤ i → (a - v + u) i = v i := fun h =>
          h1 fun i hi => (h2 i hi).trans ((hb i hi).symm.trans (h i hi)).symm
        rw [ite_eq_left h2, ite_eq_right hb', ite_eq_left hb]; abel
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
  have hvu : ∀ i, m < i → v i = u i := fun i hi => (huv i hi).symm
  let φ : (ℕ →₀ A) ≃ (ℕ →₀ A) :=
    { toFun := F u v, invFun := F v u, left_inv := P4 u v, right_inv := P4 v u }
  refine ⟨φ, fun a b => ?_, fun a ha => ?_, fun a ha hb => ?_⟩
  · change (F u v a - F u v b).support.sup Nat.succ = _
    refine level_sub_eq_of_forall_iff fun k => ⟨fun h => ?_, P3 u v huv a b k⟩
    have := P3 v u hvu (F u v a) (F u v b) k h
    rwa [P4, P4] at this
  · change F u v a = _
    simp only [F, ite_eq_left ha]
  · change F u v a = _
    simp only [F, ite_eq_right ha, ite_eq_right hb]

/-- **G3, isometries.** If `h (y - x) = h (y' - x')`, some bijection preserving `h` on every
difference maps `x` to `x'` and `y` to `y'`. -/
theorem exists_levelIsometry (x y x' y' : ℕ →₀ A)
    (hxy : (y - x).support.sup Nat.succ = (y' - x').support.sup Nat.succ) :
    ∃ φ : (ℕ →₀ A) ≃ (ℕ →₀ A),
      (∀ a b, (φ a - φ b).support.sup Nat.succ = (a - b).support.sup Nat.succ) ∧
      φ x = x' ∧ φ y = y' := by
  rcases Nat.eq_zero_or_eq_succ_pred ((y - x).support.sup Nat.succ) with h0 | hm
  · rw [h0, eq_comm, level_sub_eq_zero_iff] at hxy
    rw [level_sub_eq_zero_iff] at h0
    subst h0 hxy
    refine ⟨Equiv.addRight (x' - x), fun a b => ?_, by simp, by simp⟩
    simp [add_sub_add_right_eq_sub]
  · set m := ((y - x).support.sup Nat.succ).pred
    have hu := apply_ne_zero_of_level_eq_succ hm
    have hv := apply_ne_zero_of_level_eq_succ (hxy.symm.trans hm)
    obtain ⟨F, hFiso, hFu, hFo⟩ := exists_levelIsometry_swap m (y - x) (y' - x')
      fun i hi => (hu.2 i hi).trans (hv.2 i hi).symm
    have hF0 : F 0 = 0 := hFo 0 (fun h => hu.1 (by simpa using (h m le_rfl).symm))
      (fun h => hv.1 (by simpa using (h m le_rfl).symm))
    refine ⟨((Equiv.subRight x).trans F).trans (Equiv.addRight x'), fun a b => ?_, ?_, ?_⟩
    · change (F (a - x) + x' - (F (b - x) + x')).support.sup Nat.succ = _
      rw [add_sub_add_right_eq_sub, hFiso, sub_sub_sub_cancel_right]
    · simp [hF0]
    · simp [hFu (y - x) fun i _ => rfl]

end Isometry

/-! ### Radial laws -/

section Radial

variable {A : Type*} [AddCommGroup A]

/-- A level isometry preserves a radial pair intensity. -/
theorem radial_map_eq_of_levelIsometry (J : Sym2 (ℕ →₀ A) → ℝ≥0) (f : ℕ → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) (φ : (ℕ →₀ A) ≃ (ℕ →₀ A))
    (hφ : ∀ a b, (φ a - φ b).support.sup Nat.succ = (a - b).support.sup Nat.succ) :
    ∀ e, J (Sym2.map φ e) = J e := by
  intro e
  induction e using Sym2.ind with
  | _ a b => rw [Sym2.map_mk, hJ, hJ, hφ]

/-- Translations are level isometries. -/
theorem level_addRight (g : ℕ →₀ A) (a b : ℕ →₀ A) :
    (Equiv.addRight g a - Equiv.addRight g b).support.sup Nat.succ =
      (a - b).support.sup Nat.succ := by
  simp [add_sub_add_right_eq_sub]

/-- The law of a radial intensity is preserved by every level isometry. -/
theorem law_map_eq_of_levelIsometry (J : Sym2 (ℕ →₀ A) → ℝ≥0) (f : ℕ → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) (φ : (ℕ →₀ A) ≃ (ℕ →₀ A))
    (hφ : ∀ a b, (φ a - φ b).support.sup Nat.succ = (a - b).support.sup Nat.succ) (β : ℝ≥0) :
    (law (intensityProfile J β)).map (fun ω => Sym2.map φ '' ω) = law (intensityProfile J β) :=
  law_intensityProfile_map_eq J φ (radial_map_eq_of_levelIsometry J f hJ φ hφ) β

/-- Internal connection in `S` is carried to internal connection in `T` by a law-preserving
bijection mapping `S` onto `T`. -/
theorem law_localConn_eq_of_image [Countable (ℕ →₀ A)] (J : Sym2 (ℕ →₀ A) → ℝ≥0)
    (φ : (ℕ →₀ A) ≃ (ℕ →₀ A)) (hφ : ∀ e, J (Sym2.map φ e) = J e) (β : ℝ≥0)
    {S T : Set (ℕ →₀ A)} (hST : ∀ v, v ∈ T ↔ φ.symm v ∈ S) (a b : ℕ →₀ A) :
    law (intensityProfile J β) (localConn T (φ a) (φ b)) =
      law (intensityProfile J β) (localConn S a b) := by
  refine le_antisymm (law_localConn_image_le J φ hφ β (fun v hv => (hST v).1 hv) a b) ?_
  have hφ' : ∀ e, J (Sym2.map φ.symm e) = J e := fun e => by
    rw [← hφ (Sym2.map φ.symm e), Sym2.map_map]
    simp
  have h := law_localConn_image_le J φ.symm hφ' β (S := T) (T := S)
    (fun v hv => by rw [Equiv.symm_symm, hST, Equiv.symm_apply_apply]; exact hv) (φ a) (φ b)
  simp only [Equiv.symm_apply_apply] at h
  exact h

variable (J : Sym2 (ℕ →₀ A) → ℝ≥0) (f : ℕ → ℝ≥0)
  (hJ : ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ))
include hJ

/-! #### G2: translations -/

/-- **G2.** Translations preserve the two-point function of a radial intensity. -/
theorem tau_add_right_of_radial (β : ℝ≥0) (g x y : ℕ →₀ A) :
    tau (intensityProfile J β) (x + g) (y + g) = tau (intensityProfile J β) x y :=
  tau_apply_eq_of_map_law_eq (Equiv.addRight g)
    (law_map_eq_of_levelIsometry J f hJ _ (level_addRight g) β) x y

/-- **G2.** The susceptibility of a radial intensity does not depend on the vertex. -/
theorem chi_eq_chi_zero_of_radial (β : ℝ≥0) (x : ℕ →₀ A) :
    chi (intensityProfile J β) x = chi (intensityProfile J β) 0 := by
  have h := chi_apply_eq_of_map_law_eq (Equiv.addRight x)
    (law_map_eq_of_levelIsometry J f hJ _ (level_addRight x) β) 0
  simpa using h

/-- **G2.** The law of the cluster volume does not depend on the vertex. -/
theorem map_encard_cluster_eq_of_radial [Countable A] (β : ℝ≥0) (x : ℕ →₀ A) :
    (law (intensityProfile J β)).map (fun ω => (cluster ω x).encard) =
      (law (intensityProfile J β)).map (fun ω => (cluster ω 0).encard) := by
  have hm := law_map_eq_of_levelIsometry J f hJ _ (level_addRight x) β
  ext s hs
  rw [Measure.map_apply (measurable_encard_cluster x) hs,
    Measure.map_apply (measurable_encard_cluster 0) hs]
  conv_lhs => rw [← hm]
  rw [map_image_sym2Map_apply]
  congr 1
  ext ω
  simp only [mem_preimage]
  have := encard_cluster_image (Equiv.addRight x) ω 0
  rw [show (Equiv.addRight x) 0 = x by simp] at this
  rw [this]

/-- **G2.** Internal connection in the ball `B(x,n) = {a | h (a - x) ≤ n}` translates to
internal connection in `B(x + g, n)`. -/
theorem law_localConn_ball_add_right_of_radial [Countable A] (β : ℝ≥0) (g x a b : ℕ →₀ A)
    (n : ℕ) :
    law (intensityProfile J β) (localConn {c | (c - (x + g)).support.sup Nat.succ ≤ n}
      (a + g) (b + g)) =
      law (intensityProfile J β) (localConn {c | (c - x).support.sup Nat.succ ≤ n} a b) :=
  law_localConn_eq_of_image J (Equiv.addRight g)
    (radial_map_eq_of_levelIsometry J f hJ _ (level_addRight g)) β
    (fun v => by
      simp only [mem_ofPred_eq, Equiv.addRight_symm, Equiv.coe_addRight]
      rw [show v + -g - x = v - (x + g) by abel]) a b

/-! #### G3: dependence on the level only -/

/-- **G3.** The two-point function of a radial intensity depends only on `h (y - x)`. -/
theorem tau_eq_of_level_eq (β : ℝ≥0) {x y x' y' : ℕ →₀ A}
    (hxy : (y - x).support.sup Nat.succ = (y' - x').support.sup Nat.succ) :
    tau (intensityProfile J β) x y = tau (intensityProfile J β) x' y' := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_levelIsometry x y x' y' hxy
  rw [← hx, ← hy]
  exact (tau_apply_eq_of_map_law_eq φ (law_map_eq_of_levelIsometry J f hJ φ hφ β) x y).symm

/-- **G3.** The probability that `x` and `y` are joined inside the ball of level `h (y - x)`
around `x` (which contains both) depends only on `h (y - x)`. -/
theorem law_localConn_ball_eq_of_level_eq [Countable A] (β : ℝ≥0) {x y x' y' : ℕ →₀ A}
    (hxy : (y - x).support.sup Nat.succ = (y' - x').support.sup Nat.succ) :
    law (intensityProfile J β)
        (localConn {c | (c - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ} x y) =
      law (intensityProfile J β)
        (localConn {c | (c - x').support.sup Nat.succ ≤ (y' - x').support.sup Nat.succ} x' y') := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_levelIsometry x y x' y' hxy
  have h := law_localConn_eq_of_image J φ (radial_map_eq_of_levelIsometry J f hJ φ hφ) β
    (S := {c | (c - x).support.sup Nat.succ ≤ (y - x).support.sup Nat.succ})
    (T := {c | (c - x').support.sup Nat.succ ≤ (y' - x').support.sup Nat.succ})
    (fun v => by
      simp only [mem_ofPred_eq]
      rw [← hxy, ← hφ (φ.symm v) x, Equiv.apply_symm_apply, hx]) x y
  rw [hx, hy] at h
  exact h.symm

end Radial

/-! ### The shell average (item 3) -/

/-- **Corollary.** For a radial intensity on `ℕ →₀ (Fin d → ZMod L)` and `h x = m + 1`, the
two-point function `tau q 0 x` is the average of `tau q 0` over the shell of level `m + 1`,
which has `L^{d(m+1)} - L^{dm}` points. -/
theorem tau_eq_inv_card_mul_tsum_shell {d L : ℕ} [NeZero L]
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (f : ℕ → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = f ((y - x).support.sup Nat.succ)) (β : ℝ≥0) {m : ℕ}
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = m + 1) :
    tau (intensityProfile J β) 0 x =
      (((L ^ d) ^ (m + 1) - (L ^ d) ^ m : ℕ) : ℝ≥0∞)⁻¹ *
        ∑' z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1},
          tau (intensityProfile J β) 0 z := by
  have hfin : Finite {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1} :=
    (finite_level_shell (m + 1)).to_subtype
  have hconst : ∀ z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1},
      tau (intensityProfile J β) 0 z = tau (intensityProfile J β) 0 x := fun z =>
    tau_eq_of_level_eq J f hJ β (by rw [sub_zero, sub_zero, z.2, hx])
  have hcard := card_shell_succ (d := d) (L := L) m
  have hpos : (Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1} : ℝ≥0∞)
      ≠ 0 := by
    have : Nonempty {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = m + 1} := ⟨⟨x, hx⟩⟩
    simp [Nat.card_pos.ne']
  simp_rw [hconst]
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe, ← hcard, ← mul_assoc,
      ENNReal.inv_mul_cancel hpos
    (ENNReal.natCast_ne_top _), one_mul]

end PercLib.Models

/-! ### Non-vacuity: `d = 1`, `L = 2`, `f n = 4^(-n)` -/
section Witnesses

open PercLib.Models

/-- Two pairs at level `2` in `ℕ →₀ (Fin 1 → ZMod 2)`: `(0, δ₁)` and `(δ₀, δ₀ + δ₁)`, where
`δᵢ` is the unit vector at index `i`. A level isometry maps the first onto the second. -/
example : ∃ φ : (ℕ →₀ (Fin 1 → ZMod 2)) ≃ (ℕ →₀ (Fin 1 → ZMod 2)),
    (∀ a b, (φ a - φ b).support.sup Nat.succ = (a - b).support.sup Nat.succ) ∧
    φ 0 = Finsupp.single 0 1 ∧ φ (Finsupp.single 1 1) = Finsupp.single 0 1 + Finsupp.single 1 1 :=
  exists_levelIsometry _ _ _ _ (by
    simp)

/-- Item 3 at `n = 1` for the radial kernel `4^(-level)`: `tau q 0 δ₀` is the shell average
over the `2 - 1 = 1` point of level one. -/
example (β : ℝ≥0) : ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
    tau (intensityProfile J β) 0 (Finsupp.single 0 1) =
      (((2 ^ 1) ^ (0 + 1) - (2 ^ 1) ^ 0 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑' z : {z : ℕ →₀ (Fin 1 → ZMod 2) // z.support.sup Nat.succ = 0 + 1},
          tau (intensityProfile J β) 0 z := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  exact ⟨J, tau_eq_inv_card_mul_tsum_shell J (fun n => 1 * (1 / 4) ^ n) hJ β
    (by simp)⟩

end Witnesses
