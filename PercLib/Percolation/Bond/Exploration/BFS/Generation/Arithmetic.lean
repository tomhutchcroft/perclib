/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Generation/Arithmetic.lean`; added at source revision
`81ff4de74a4eae0fd87ce59ebb2b09933fd9da95`, supplied under its Apache-2.0 header.
Definitions have moved to separately reviewed `Defs` modules. This is a proof-only module with
canonical prefix `PercLib.Percolation.Bond.Exploration.BFS`; explicit countability scoping keeps
the source premises while removing
forbidden section-option commands. Mathematical reference: the exploration outline, §4–§5.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Generation.RowCharge

/-!
# Extended-power arithmetic for generation moments

Extended powers respect addition of extended-natural cardinalities and finite powers. These
are used with genuinely infinite generational counts, not truncated cardinalities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration.BFS
open scoped ENNReal BigOperators Topology

namespace PercLib.Percolation.Bond.Exploration.BFS

/-! ### `epow` arithmetic -/

theorem epow_one {lam : ℝ≥0∞} (hlam : 1 ≤ lam) : epow lam 1 = lam := by
  have h : epow lam 1 = epow lam ((1 : ℕ) : ℕ∞) := rfl
  rw [h, epow_natCast lam hlam 1, ENNReal.rpow_natCast, pow_one]

/-- Subadditivity of `epow` in the exponent. -/
theorem epow_add_le {lam : ℝ≥0∞} (hlam : 1 ≤ lam) (h0 : lam ≠ 0) (htop : lam ≠ ⊤)
    (a b : ℕ∞) : epow lam (a + b) ≤ epow lam a * epow lam b := by
  conv_lhs => rw [epow]
  refine iSup_le (fun k => ?_)
  set ka : ℕ∞ := a ⊓ (k : ℕ∞) with hka
  set kb : ℕ∞ := b ⊓ (k : ℕ∞) with hkb
  have hka_top : ka ≠ ⊤ := ne_top_of_le_ne_top (by simp) inf_le_right
  have hkb_top : kb ≠ ⊤ := ne_top_of_le_ne_top (by simp) inf_le_right
  have hkab_top : ka + kb ≠ ⊤ := by
    simp [hka_top, hkb_top]
  have h1 : ((a + b) ⊓ (k : ℕ∞)) ≤ ka + kb := by
    rw [hka, hkb]
    by_cases h : (k : ℕ∞) ≤ a
    · rw [show a ⊓ (k : ℕ∞) = (k : ℕ∞) from inf_eq_right.mpr h]
      exact inf_le_right.trans (le_add_of_nonneg_right (by simp : (0:ℕ∞) ≤ b ⊓ (k:ℕ∞)))
    · rw [show a ⊓ (k : ℕ∞) = a from inf_eq_left.mpr (lt_of_not_ge h).le]
      by_cases h2 : (k : ℕ∞) ≤ b
      · rw [show b ⊓ (k : ℕ∞) = (k : ℕ∞) from inf_eq_right.mpr h2]
        exact inf_le_right.trans (le_add_of_nonneg_left (by simp : (0:ℕ∞) ≤ a))
      · rw [show b ⊓ (k : ℕ∞) = b from inf_eq_left.mpr (lt_of_not_ge h2).le]
        exact inf_le_left
  have h2 : ((a + b) ⊓ (k : ℕ∞)).toNat ≤ (ka + kb).toNat :=
    ENat.toNat_le_toNat h1 hkab_top
  have h3 : (ka + kb).toNat = ka.toNat + kb.toNat :=
    ENat.toNat_add hka_top hkb_top
  calc lam ^ ((((a + b) ⊓ (k : ℕ∞))).toNat : ℝ)
      ≤ lam ^ (((ka + kb).toNat) : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le hlam (by exact_mod_cast h2)
    _ = lam ^ (((ka.toNat : ℝ) + (kb.toNat : ℝ))) := by rw [h3]; push_cast; ring_nf
    _ = lam ^ (ka.toNat : ℝ) * lam ^ (kb.toNat : ℝ) := ENNReal.rpow_add _ _ h0 htop
    _ ≤ epow lam a * epow lam b := by
        rw [epow, epow]
        exact mul_le_mul' (le_iSup (fun m : ℕ => lam ^ ((a ⊓ (m : ℕ∞)).toNat : ℝ)) k)
          (le_iSup (fun m : ℕ => lam ^ ((b ⊓ (m : ℕ∞)).toNat : ℝ)) k)

/-- Monotonicity of `epow` in the base, for bases at least one. -/
theorem epow_le_epow_base {x y : ℝ≥0∞} (hxy : x ≤ y) (n : ℕ∞) : epow x n ≤ epow y n := by
  rw [epow, epow]
  refine iSup_le (fun k => ?_)
  exact le_iSup_of_le k (ENNReal.rpow_le_rpow hxy (by positivity))

/-- Multiplicativity of `epow` in the base, as an inequality in the direction the
generation induction needs. -/
theorem epow_mul_le {x y : ℝ≥0∞} (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hxt : x ≠ ⊤) (hyt : y ≠ ⊤)
    (n : ℕ∞) : epow x n * epow y n ≤ epow (x * y) n := by
  rcases eq_or_ne n ⊤ with h | h
  · subst h
    rcases eq_or_lt_of_le hx1 with hx | hx
    · rw [← hx, epow_one_top, one_mul, one_mul]
    · rcases eq_or_lt_of_le hy1 with hy | hy
      · rw [← hy, epow_one_top, mul_one, mul_one]
      · rw [epow_top_of_one_lt x hx, epow_top_of_one_lt y hy,
          epow_top_of_one_lt (x * y) (one_lt_mul'' hx hy)]
        exact le_top
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (ENat.natCast_toNat h).symm⟩
    rw [epow_natCast x hx1 m, epow_natCast y hy1 m,
      epow_natCast (x * y) (one_le_mul hx1 hy1) m]
    rw [← ENNReal.mul_rpow_of_ne_top hxt hyt]

/-- `epow` on a finite cluster cardinality, in real form. -/
theorem epow_ofReal_pow {τ : ℝ} (hτ : 1 ≤ τ) (n : ℕ) :
    epow (ENNReal.ofReal τ) (n : ℕ∞) = ENNReal.ofReal (τ ^ n) := by
  rw [epow_natCast _ (by simpa using ENNReal.ofReal_le_ofReal hτ) n]
  rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by positivity), Real.rpow_natCast]

/-! ### Finite subsets of a set with prescribed cardinality -/

/-- A set of extended cardinality at least `n` has a finite subset of cardinality `n`.
This is mathlib's `Set.exists_subset_encard_eq`, transported to `Finset`. -/
theorem exists_finset_card_le_encard {α : Type*} :
    ∀ {s : Set α} {n : ℕ}, (n : ℕ∞) ≤ s.encard →
      ∃ t : Finset α, (t : Set α) ⊆ s ∧ t.card = n := by
  intro s n h
  obtain ⟨u, hus, hue⟩ := Set.exists_subset_encard_eq h
  have hfin : u.Finite := Set.finite_of_encard_eq_coe hue
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact hus
  · have h2 : (hfin.toFinset.card : ℕ∞) = (n : ℕ∞) := by
      rw [← hfin.encard_eq_coe_toFinset_card, hue]
    exact_mod_cast h2

end PercLib.Percolation.Bond.Exploration.BFS
