/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the three-vertex counterexample showing that the lower bound for
the boundary functional of the wiki page boundary-susceptibility (tag 67GX) needs the positive part
(tag JTBG). No upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The positive part in the boundary-susceptibility bound is needed

Take the path `0 - 1 - 2` on `Fin 3` with `J(0,1) = 99/100`, `J(1,2) = 1/100`, `J(0,2) = 0`,
`β = 1` and `q = intensityProfile J 1`. Write `p = 1 - e^{-99/100}`, `t = 1 - e^{-1/100}`
and `S = {0, 1}`. Then

* `τ(0,1) = p`, `τ(1,2) = t`, `τ(0,2) = p t` (`tau_three_path`);
* `χ(0) = 1 + p + p t`, `χ(1) = 1 + p + t`, `χ(2) = 1 + t + p t`, so
  `χ_min = 1 + t + p t` and `χ_max = 1 + p + t` (`chi_three_path`, `iInf_chi_three_path`,
  `iSup_chi_three_path`);
* `Q(S) = ∑_{u ∈ S} (∑_{v ∈ S} τ(u,v))² = 2 (1 + p)²` and
  `Φ_1(S) = ∑_{v ∈ S} ∑_{z ∉ S} J(v,z) χ_{Sᶜ}(z) = 1/100`;
* the unsigned square `(χ_min |S| - ∑_{u,v ∈ S} τ(u,v))² / (χ_max Q(S))` exceeds
  `841/10050 > 1/100` (`not_boundary_bound_unsigned`).

So `Φ_β(S) ≥ (χ_min |S| - ∑ τ)² / (β² χ_max Q(S))` fails without the positive part. The
numerical bounds `3/5 < p` and `0 < t < 1/100` come from the series bounds for `exp`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-! ### Numerical bounds -/

/-- `3/5 < 1 - e^{-99/100}`, from `1 + x + x²/2 + x³/6 ≤ e^x`. -/
theorem three_fifths_lt_one_sub_exp : (3 / 5 : ℝ) < 1 - Real.exp (-(99 / 100)) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 99 / 100 by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial,
      Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one, Nat.succ_eq_add_one,
      zero_add, mul_one, div_one, Nat.reduceAdd, Nat.cast_ofNat, Nat.reduceMul] at h
  have hpos := Real.exp_pos (99 / 100 : ℝ)
  have hinv : Real.exp (-(99 / 100)) = (Real.exp (99 / 100))⁻¹ := Real.exp_neg _
  rw [hinv]
  have : (Real.exp (99 / 100))⁻¹ < 2 / 5 := by
    rw [inv_lt_comm₀ hpos (by norm_num)]
    norm_num at h ⊢
    linarith
  linarith

/-- `0 < 1 - e^{-1/100} < 1/100`. -/
theorem one_sub_exp_hundredth_mem :
    0 < 1 - Real.exp (-(1 / 100 : ℝ)) ∧ 1 - Real.exp (-(1 / 100 : ℝ)) < 1 / 100 := by
  constructor
  · have := Real.exp_lt_one_iff.2 (show -(1 / 100 : ℝ) < 0 by norm_num)
    linarith
  · have := Real.add_one_lt_exp (show -(1 / 100 : ℝ) ≠ 0 by norm_num)
    linarith

/-! ### The model -/

section Model

variable {J : Sym2 (Fin 3) → ℝ≥0}

theorem intensityProfile_one_coe (J : Sym2 (Fin 3) → ℝ≥0) (e : Sym2 (Fin 3)) :
    (intensityProfile J 1 e : ℝ) = 1 - Real.exp (-(J e : ℝ)) := by
  simp [intensityProfile]

/-- Off the path, the pair `s(0,2)` is almost surely closed, so the open graph lies in the
path `0 - 1 - 2`. -/
theorem ae_openGraph_le_pathGraph_three (h02 : J s(0, 2) = 0) :
    ∀ᵐ ω ∂law (intensityProfile J 1), openGraph ω ≤ SimpleGraph.pathGraph 3 := by
  have hq02 : (intensityProfile J 1 s(0, 2) : ℝ) = 0 := by
    rw [intensityProfile_one_coe, h02]
    simp
  filter_upwards [ae_config_subset_positive _] with ω hω
  intro x y hxy
  obtain ⟨he, hne⟩ := (openGraph_adj_iff ω x y).1 hxy
  have hpos : (0 : ℝ) < intensityProfile J 1 s(x, y) := hω he
  rw [SimpleGraph.pathGraph_adj]
  fin_cases x <;> fin_cases y <;> simp_all [Sym2.eq_swap]

/-- The connection probabilities along the path: `τ(0,1) = p`, `τ(1,2) = t`,
`τ(0,2) = p t`. -/
theorem tau_three_path (h01 : J s(0, 1) = 99 / 100) (h12 : J s(1, 2) = 1 / 100)
    (h02 : J s(0, 2) = 0) :
    tau (intensityProfile J 1) 0 1 = ENNReal.ofReal (1 - Real.exp (-(99 / 100))) ∧
      tau (intensityProfile J 1) 1 2 = ENNReal.ofReal (1 - Real.exp (-(1 / 100))) ∧
      tau (intensityProfile J 1) 0 2 = ENNReal.ofReal
        ((1 - Real.exp (-(99 / 100))) * (1 - Real.exp (-(1 / 100)))) := by
  have hG := SimpleGraph.isAcyclic_pathGraph 3
  have hhost := ae_openGraph_le_pathGraph_three h02
  have a01 : (SimpleGraph.pathGraph 3).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]
  have a12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by simp [SimpleGraph.pathGraph_adj]
  have hq : ∀ e : Sym2 (Fin 3), ((unitInterval.toNNReal (intensityProfile J 1 e) : ℝ≥0∞)) =
      ENNReal.ofReal (1 - Real.exp (-(J e : ℝ))) := by
    intro e
    rw [← intensityProfile_one_coe, ← ENNReal.ofReal_coe_nnreal]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [tau_eq_prod_of_ae_le_acyclic _ hG hhost
      ⟨SimpleGraph.Walk.cons a01 .nil, by simp [SimpleGraph.Walk.isPath_def]⟩]
    simp [hq, h01]
  · rw [tau_eq_prod_of_ae_le_acyclic _ hG hhost
      ⟨SimpleGraph.Walk.cons a12 .nil, by simp [SimpleGraph.Walk.isPath_def]⟩]
    simp [hq, h12]
  · rw [tau_eq_prod_of_ae_le_acyclic _ hG hhost
      ⟨SimpleGraph.Walk.cons a01 (SimpleGraph.Walk.cons a12 .nil),
        by simp [SimpleGraph.Walk.isPath_def]⟩]
    simp only [Fin.isValue, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.toFinset_cons, List.toFinset_nil, insert_empty_eq, hq, Finset.mem_singleton, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, zero_ne_one, Fin.reduceEq, and_self, Prod.swap_prod_mk,
        and_true, or_self, not_false_eq_true, Finset.prod_insert, h01, NNReal.coe_div,
        NNReal.coe_ofNat, Finset.prod_singleton, h12, one_div, NNReal.coe_inv]
    rw [ENNReal.ofReal_mul (sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num)))]

/-- The three susceptibilities. -/
theorem chi_three_path (h01 : J s(0, 1) = 99 / 100) (h12 : J s(1, 2) = 1 / 100)
    (h02 : J s(0, 2) = 0) :
    chi (intensityProfile J 1) 0 = ENNReal.ofReal (1 + (1 - Real.exp (-(99 / 100))) +
        (1 - Real.exp (-(99 / 100))) * (1 - Real.exp (-(1 / 100)))) ∧
      chi (intensityProfile J 1) 1 = ENNReal.ofReal (1 + (1 - Real.exp (-(99 / 100))) +
        (1 - Real.exp (-(1 / 100)))) ∧
      chi (intensityProfile J 1) 2 = ENNReal.ofReal (1 + (1 - Real.exp (-(1 / 100))) +
        (1 - Real.exp (-(99 / 100))) * (1 - Real.exp (-(1 / 100)))) := by
  obtain ⟨t01, t12, t02⟩ := tau_three_path h01 h12 h02
  have hp := three_fifths_lt_one_sub_exp
  have ht := one_sub_exp_hundredth_mem
  have hp0 : 0 ≤ 1 - Real.exp (-(99 / 100) : ℝ) := by linarith
  have hpt : 0 ≤ (1 - Real.exp (-(99 / 100) : ℝ)) * (1 - Real.exp (-(1 / 100))) :=
    mul_nonneg hp0 ht.1.le
  simp only [chi_eq_tsum_tau, tsum_fintype, Fin.sum_univ_three, Fin.isValue]
  rw [tau_comm _ 1 0, tau_comm _ 2 0, tau_comm _ 2 1]
  simp only [tau_self, t01, t12, t02]
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
  all_goals congr 1; ring

/-- `χ_min = χ(2) = 1 + t + p t` and `χ_max = χ(1) = 1 + p + t`. -/
theorem iInf_iSup_chi_three_path (h01 : J s(0, 1) = 99 / 100) (h12 : J s(1, 2) = 1 / 100)
    (h02 : J s(0, 2) = 0) :
    (⨅ u, chi (intensityProfile J 1) u).toReal = 1 + (1 - Real.exp (-(1 / 100))) +
        (1 - Real.exp (-(99 / 100))) * (1 - Real.exp (-(1 / 100))) ∧
      (⨆ u, chi (intensityProfile J 1) u).toReal = 1 + (1 - Real.exp (-(99 / 100))) +
        (1 - Real.exp (-(1 / 100))) := by
  obtain ⟨c0, c1, c2⟩ := chi_three_path h01 h12 h02
  have hp := three_fifths_lt_one_sub_exp
  have ht := one_sub_exp_hundredth_mem
  have hp1 : 1 - Real.exp (-(99 / 100) : ℝ) ≤ 1 := by linarith [Real.exp_pos (-(99 / 100) : ℝ)]
  set p := 1 - Real.exp (-(99 / 100) : ℝ)
  set t := 1 - Real.exp (-(1 / 100) : ℝ)
  have hpt : p * t ≤ t := mul_le_of_le_one_left ht.1.le hp1
  have hpt' : p * t ≤ p := mul_le_of_le_one_right (by linarith) (by linarith)
  have hinf : (⨅ u, chi (intensityProfile J 1) u) = chi (intensityProfile J 1) 2 := by
    refine le_antisymm (iInf_le _ 2) (le_iInf fun u => ?_)
    fin_cases u <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, c0, c1, c2] <;>
      exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsup : (⨆ u, chi (intensityProfile J 1) u) = chi (intensityProfile J 1) 1 := by
    refine le_antisymm (iSup_le fun u => ?_) (le_iSup _ 1)
    fin_cases u <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, c0, c1, c2] <;>
      exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [hinf, hsup, c1, c2, ENNReal.toReal_ofReal (by nlinarith),
    ENNReal.toReal_ofReal (by linarith)]
  exact ⟨rfl, rfl⟩

/-- For `S = {0, 1}`: `∑_{u,v ∈ S} τ(u,v) = 2 (1 + p)` and
`Q(S) = ∑_{u ∈ S} (∑_{v ∈ S} τ(u,v))² = 2 (1 + p)²`. -/
theorem sum_tau_pair_three_path (h01 : J s(0, 1) = 99 / 100) (h12 : J s(1, 2) = 1 / 100)
    (h02 : J s(0, 2) = 0) :
    ∑ u ∈ ({0, 1} : Finset (Fin 3)), ∑ v ∈ ({0, 1} : Finset (Fin 3)),
        (tau (intensityProfile J 1) u v).toReal = 2 * (1 + (1 - Real.exp (-(99 / 100)))) ∧
      ∑ u ∈ ({0, 1} : Finset (Fin 3)),
          (∑ v ∈ ({0, 1} : Finset (Fin 3)), (tau (intensityProfile J 1) u v).toReal) ^ 2 =
        2 * (1 + (1 - Real.exp (-(99 / 100)))) ^ 2 := by
  obtain ⟨t01, -, -⟩ := tau_three_path h01 h12 h02
  have hp := three_fifths_lt_one_sub_exp
  have h10 := tau_comm (intensityProfile J 1) 1 0
  simp only [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide), tau_self, h10, t01,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - Real.exp (-(99 / 100) : ℝ) by linarith),
    ENNReal.toReal_one]
  constructor <;> ring

/-- For `S = {0, 1}`, `Φ_1(S) = ∑_{v ∈ S} ∑_{z ∉ S} J(v,z) χ_{Sᶜ}(z) = 1/100`, where
`χ_{Sᶜ}(z) = ∑_{w ∉ S} τ^S(z,w)` and `τ^S` is connection in the open graph on `Sᶜ`. -/
theorem boundary_functional_three_path (h12 : J s(1, 2) = 1 / 100) (h02 : J s(0, 2) = 0) :
    ∑ v ∈ ({0, 1} : Finset (Fin 3)), ∑' z,
        (if z ∈ ({0, 1} : Finset (Fin 3)) then 0 else (J s(v, z) : ℝ)) *
          ∑' w, (law (intensityProfile J 1)).real
            (localConn ((({0, 1} : Finset (Fin 3)) : Set (Fin 3))ᶜ) z w) = 1 / 100 := by
  simp only [tsum_fintype, Fin.sum_univ_three]
  rw [Finset.sum_pair (by decide)]
  simp [h12, h02, localConn]

/-- The unsigned square `(χ_min |S| - ∑_{u,v ∈ S} τ(u,v))² / (β² χ_max Q(S))` at `β = 1`,
`S = {0, 1}` exceeds `841/10050`. -/
theorem unsigned_square_three_path_gt (h01 : J s(0, 1) = 99 / 100)
    (h12 : J s(1, 2) = 1 / 100) (h02 : J s(0, 2) = 0) :
    (841 / 10050 : ℝ) <
      ((⨅ u, chi (intensityProfile J 1) u).toReal * (({0, 1} : Finset (Fin 3)).card : ℝ) -
          ∑ u ∈ ({0, 1} : Finset (Fin 3)), ∑ v ∈ ({0, 1} : Finset (Fin 3)),
            (tau (intensityProfile J 1) u v).toReal) ^ 2 /
        ((1 : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J 1) u).toReal *
          ∑ u ∈ ({0, 1} : Finset (Fin 3)),
            (∑ v ∈ ({0, 1} : Finset (Fin 3)), (tau (intensityProfile J 1) u v).toReal) ^ 2) := by
  obtain ⟨hinf, hsup⟩ := iInf_iSup_chi_three_path h01 h12 h02
  obtain ⟨hT, hQ⟩ := sum_tau_pair_three_path h01 h12 h02
  have hp := three_fifths_lt_one_sub_exp
  have ht := one_sub_exp_hundredth_mem
  have hp1 : 1 - Real.exp (-(99 / 100) : ℝ) < 1 := by linarith [Real.exp_pos (-(99 / 100) : ℝ)]
  rw [hinf, hsup, hT, hQ, Finset.card_pair (by decide)]
  set p := 1 - Real.exp (-(99 / 100) : ℝ)
  set t := 1 - Real.exp (-(1 / 100) : ℝ)
  have ha : (29 / 50 : ℝ) < p - t - p * t := by nlinarith
  have hN : (2 * (29 / 50 : ℝ)) ^ 2 < ((1 + t + p * t) * (2 : ℕ) - 2 * (1 + p)) ^ 2 := by
    have : (1 + t + p * t) * ((2 : ℕ) : ℝ) - 2 * (1 + p) = -(2 * (p - t - p * t)) := by
      push_cast
      ring
    rw [this, neg_sq]
    exact pow_lt_pow_left₀ (by linarith) (by norm_num) two_ne_zero
  have hD0 : 0 < (1 : ℝ) ^ 2 * (1 + p + t) * (2 * (1 + p) ^ 2) := by
    have : 0 < 1 + p + t := by linarith
    positivity
  have hD : (1 : ℝ) ^ 2 * (1 + p + t) * (2 * (1 + p) ^ 2) < 201 / 100 * 8 := by
    have h1 : (1 + p) ^ 2 < 4 := by nlinarith
    have h2 : 1 + p + t < 201 / 100 := by linarith
    nlinarith
  rw [lt_div_iff₀ hD0]
  nlinarith

/-- **The positive part is needed.** In the three-vertex model at `β = 1` with `S = {0, 1}`, the
boundary functional `Φ_1(S) = 1/100` is smaller than the unsigned square
`(χ_min |S| - ∑_{u,v ∈ S} τ(u,v))² / (β² χ_max Q(S))`. So the lower bound of
`boundary_susceptibility_bound` fails if the positive part is dropped. -/
theorem not_boundary_bound_unsigned (h01 : J s(0, 1) = 99 / 100)
    (h12 : J s(1, 2) = 1 / 100) (h02 : J s(0, 2) = 0) :
    ¬ (((⨅ u, chi (intensityProfile J 1) u).toReal * (({0, 1} : Finset (Fin 3)).card : ℝ) -
          ∑ u ∈ ({0, 1} : Finset (Fin 3)), ∑ v ∈ ({0, 1} : Finset (Fin 3)),
            (tau (intensityProfile J 1) u v).toReal) ^ 2 /
        ((1 : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J 1) u).toReal *
          ∑ u ∈ ({0, 1} : Finset (Fin 3)),
            (∑ v ∈ ({0, 1} : Finset (Fin 3)), (tau (intensityProfile J 1) u v).toReal) ^ 2) ≤
      ∑ v ∈ ({0, 1} : Finset (Fin 3)), ∑' z,
        (if z ∈ ({0, 1} : Finset (Fin 3)) then 0 else (J s(v, z) : ℝ)) *
          ∑' w, (law (intensityProfile J 1)).real
            (localConn ((({0, 1} : Finset (Fin 3)) : Set (Fin 3))ᶜ) z w)) := by
  rw [boundary_functional_three_path h12 h02, not_le]
  exact lt_trans (by norm_num) (unsigned_square_three_path_gt h01 h12 h02)

end Model

/-! ### Non-vacuity -/

/-- The three-vertex kernel satisfies the three hypotheses, so the failing inequality
`not_boundary_bound_unsigned` holds for an actual model. -/
example := not_boundary_bound_unsigned (J := fun e : Sym2 (Fin 3) =>
    if e = s(0, 1) then 99 / 100 else if e = s(1, 2) then 1 / 100 else 0)
  (by simp) (by simp) (by simp)

end PercLib.Percolation.Bond
