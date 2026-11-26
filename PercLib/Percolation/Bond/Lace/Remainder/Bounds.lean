/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Coefficients.Recursion

/-!
# A coefficient bound for the nonnegative lace remainder

## Main results

Replacing the last through-set event by connection bounds the remainder of
order `n+1` by the positive coefficient of order `n+1`, followed by one bond
and a connection. The constant is one. No finiteness or summability assumption
is needed for this extended nonnegative real inequality.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The final through-set test is bounded by ordinary connection after the
previous independent layers have been integrated. -/
theorem remainderEvent_snoc_probability_le [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (c : V × V) :
    (Measure.pi (fun _ : Fin (n + 3) => law q)) (remainderEvent x y (Fin.snoc b c)) ≤
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x c.1 b) *
        tau q c.2 y := by
  classical
  rw [remainderEvent_snoc_probability_eq_lintegral]
  calc
    _ ≤ ∫⁻ ω : Fin (n + 2) → Config V,
        (coefficientEvent x c.1 b).indicator (fun _ => tau q c.2 y) ω
        ∂(Measure.pi (fun _ : Fin (n + 2) => law q)) := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ coefficientEvent x c.1 b
      · simpa only [Set.indicator_of_mem hω] using
          law_throughSet_le_tau q
            (cluster (ω (Fin.last (n + 1)) \ {s(c.1, c.2)}) (b (Fin.last n)).2) c.2 y
      · simp only [Set.indicator_of_notMem hω, le_refl]
    _ = _ := by
      rw [lintegral_indicator_const (measurableSet_coefficientEvent x c.1 b)]
      exact mul_comm _ _

/-- At every positive order the nonnegative remainder is bounded by the
coefficient followed by one open bond and an ordinary connection. The
explicit off-diagonal weight makes the statement independent of loop
probabilities. -/
@[tag "LVRG"]
theorem laceRemainder_succ_le_tsum_laceCoefficient_mul_tau [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) :
    laceRemainder q (n + 1) x y ≤ ∑' u, ∑' v,
      laceCoefficient q (n + 1) x u *
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y := by
  classical
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  have hsplit : laceRemainder q (n + 1) x y =
      ∑' c : V × V, ∑' b : Fin (n + 1) → V × V,
        (∏ i, J (b i).1 (b i).2) * J c.1 c.2 *
          (Measure.pi (fun _ : Fin (n + 3) => law q))
            (remainderEvent x y (Fin.snoc b c)) := by
    unfold laceRemainder
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => V × V)).tsum_eq]
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro c
    apply tsum_congr
    intro b
    change (∏ i, J ((Fin.snoc b c : Fin (n + 2) → V × V) i).1
        ((Fin.snoc b c : Fin (n + 2) → V × V) i).2) * _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.snocEquiv, Equiv.coe_fn_mk]
  rw [hsplit]
  change _ ≤ ∑' u, ∑' v, laceCoefficient q (n + 1) x u * J u v * tau q v y
  calc
    _ ≤ ∑' c : V × V, ∑' b : Fin (n + 1) → V × V,
        (∏ i, J (b i).1 (b i).2) * J c.1 c.2 *
          ((Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x c.1 b) *
            tau q c.2 y) := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply ENNReal.tsum_le_tsum
      intro b
      exact mul_le_mul' le_rfl (remainderEvent_snoc_probability_le q x y b c)
    _ = ∑' c : V × V, laceCoefficient q (n + 1) x c.1 * J c.1 c.2 * tau q c.2 y := by
      apply tsum_congr
      intro c
      calc
        _ = (∑' b : Fin (n + 1) → V × V,
            (∏ i, J (b i).1 (b i).2) *
              (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x c.1 b)) *
                (J c.1 c.2 * tau q c.2 y) := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro b
          ac_rfl
        _ = _ := by
          change laceCoefficient q (n + 1) x c.1 * (J c.1 c.2 * tau q c.2 y) = _
          rw [mul_assoc]
    _ = _ := ENNReal.tsum_prod'

end PercLib.Percolation.Bond.Lace
