/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Models.FiniteRangeDecay
public import PercLib.Percolation.Bond.ChemicalMoments
public import PercLib.Percolation.Bond.SpatialMoments.Defs

/-!
# Second spatial moments for finite-range percolation

An open path with steps of sup-length at most `R` bounds spatial displacement by
`R` times chemical distance. The existing chemical-distance moment estimate therefore
gives a second spatial moment at most `2 R² M³` when every susceptibility is at most `M`.
The bound is valid with infinite values; finite susceptibility under a transitive law
makes the spatial moment finite.

## Main results

* `norm_sub_le_dist_mul_of_mem_cluster`: the deterministic comparison with chemical distance.
* `spatialMoment_sq_le_of_finiteRange`: the uniform-susceptibility bound `2 R² M³`.
* `spatialMoment_sq_le_of_finiteRange_of_transitive`: the bound `2 R² χ(o)³`.
* `spatialMoment_sq_lt_top_of_finiteRange_of_transitive`: finiteness from finite susceptibility.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

open PercLib.Models.Site

variable {d : ℕ}

/-- With open steps of length at most `R`, a connected vertex has displacement at most
`R` times its chemical distance from the root. -/
theorem norm_sub_le_dist_mul_of_mem_cluster {ω : Config (LatticeSite d)} {R : ℝ}
    (hω : ∀ x y, (openGraph ω).Adj x y → ‖x - y‖ ≤ R)
    {o x : LatticeSite d} (hx : x ∈ cluster ω o) :
    ‖x - o‖ ≤ (openGraph ω).dist o x * R := by
  obtain ⟨p, hp⟩ := hx.exists_walk_length_eq_dist
  simpa only [hp] using PercLib.Models.norm_sub_le_length_mul hω p

/-- The second spatial moment is bounded by `R²` times the second chemical-distance
moment. No assumption on the size of clusters is needed. -/
theorem spatialMoment_sq_le_mul_lintegral_dist_sq
    (q : Sym2 (LatticeSite d) → unitInterval) (o : LatticeSite d) {R : ℝ}
    (hR : 0 ≤ R) (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0) :
    spatialMoment q o (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≤
      ENNReal.ofReal (R ^ 2) * ∫⁻ ω, ∑' x,
        (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ 2) x ∂law q := by
  rw [spatialMoment_def, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_config_subset_positive q] with ω hω
  have hadj : ∀ x y, (openGraph ω).Adj x y → ‖x - y‖ ≤ R := by
    intro x y h
    by_contra hlt
    have hpos : 0 < q s(x, y) := hω ((openGraph_adj_iff ω x y).1 h).1
    rw [hq x y (not_le.1 hlt)] at hpos
    exact lt_irrefl _ hpos
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ cluster ω o
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    have hdist := norm_sub_le_dist_mul_of_mem_cluster hadj hx
    calc
      ENNReal.ofReal (‖x - o‖ ^ 2) ≤
          ENNReal.ofReal (((openGraph ω).dist o x : ℝ) * R) ^ 2 := by
            rw [← ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) hR)]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hdist 2)
      _ = ENNReal.ofReal (R ^ 2) * ((openGraph ω).dist o x : ℝ≥0∞) ^ 2 := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
              mul_pow, ENNReal.ofReal_pow hR, mul_comm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- For a finite-range profile with all susceptibilities bounded by `M`, the second
spatial moment is at most `2 R² M³`, also when `M = ∞`. -/
theorem spatialMoment_sq_le_of_finiteRange
    (q : Sym2 (LatticeSite d) → unitInterval) (o : LatticeSite d) {R : ℝ} {M : ℝ≥0∞}
    (hR : 0 ≤ R) (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0)
    (hM : ∀ x, chi q x ≤ M) :
    spatialMoment q o (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≤
      2 * ENNReal.ofReal (R ^ 2) * M ^ 3 := by
  refine (spatialMoment_sq_le_mul_lintegral_dist_sq q o hR hq).trans ?_
  have hchem := lintegral_tsum_indicator_cluster_dist_pow_le q hM o 2
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hchem
  calc
    _ ≤ ENNReal.ofReal (R ^ 2) * (2 * M ^ 3) := mul_le_mul' le_rfl hchem
    _ = _ := by ac_rfl

/-- Under a transitive law, the bound is `2 R² χ(o)³`. -/
theorem spatialMoment_sq_le_of_finiteRange_of_transitive
    (q : Sym2 (LatticeSite d) → unitInterval) (o : LatticeSite d) {R : ℝ}
    (hR : 0 ≤ R) (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0)
    (htrans : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) :
    spatialMoment q o (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≤
      2 * ENNReal.ofReal (R ^ 2) * chi q o ^ 3 := by
  exact spatialMoment_sq_le_of_finiteRange q o hR hq fun x =>
    (PercLib.Models.LongRange.lintegral_encard_cluster_eq_of_transitive q htrans
      (fun n => (n : ℝ≥0∞)) x o).le

/-- Finite susceptibility under a transitive finite-range law implies a finite second
spatial moment. -/
theorem spatialMoment_sq_lt_top_of_finiteRange_of_transitive
    (q : Sym2 (LatticeSite d) → unitInterval) (o : LatticeSite d) {R : ℝ}
    (hR : 0 ≤ R) (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0)
    (htrans : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e)
    (hchi : chi q o ≠ ⊤) :
    spatialMoment q o (fun z => ENNReal.ofReal (‖z‖ ^ 2)) < ⊤ := by
  exact (spatialMoment_sq_le_of_finiteRange_of_transitive q o hR hq htrans).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
      (ENNReal.pow_lt_top hchi.lt_top))

/-- With every edge closed the second spatial moment vanishes, including in dimension zero. -/
example (o : LatticeSite d) :
    spatialMoment (fun _ => 0) o (fun z => ENNReal.ofReal (‖z‖ ^ 2)) = 0 := by
  simp [spatialMoment_zero]

end PercLib.Percolation.Bond
