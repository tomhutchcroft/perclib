/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the uniform-susceptibility volume bounds and the finite-range exit
bound of the exponential-moments article. Every statement is assembled from lemmas proved in the
imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.FiniteRangeDecay

/-!
# Uniform susceptibility: volume tails and finite-range exit, statement forms

Each theorem restates results proved under their own names in the imported modules.

## Main results

* `exponential_bounds_of_iSup_chi_ne_top`
* `law_exit_le_of_finite_range_of_iSup_chi_ne_top`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Real PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models

/-- Independent bond percolation on a countable vertex set with `M = ⨆ x, χ(x) < ∞`. For every
root `o`: `E[|K_o| e^{s|K_o|}] ≤ χ(o)/√(1 − 2sM²)` for `0 ≤ s < (2M²)⁻¹`;
`E e^{s|K_o|} ≤ 1 + (χ(o)/M²)(1 − √(1 − 2sM²))` for `0 ≤ s ≤ (2M²)⁻¹`; for every real `n > 0`,
`P(|K_o| ≥ n) ≤ min{1, (√2 χ(o)/n) e^{−n/(4M²)}, (1 + χ(o)/M²) e^{−n/(2M²)}}`; and
`P(|K_o| ≥ n) ≤ e^{−n/(4M²)}` whenever `n ≥ 4M² log(1 + χ(o)/M²)`. The cluster volume in the
moments is read in `ℝ` through `ℕ∞.toNat`, which agrees with `|K_o|` almost surely. -/
@[tag "XLWI"]
theorem exponential_bounds_of_iSup_chi_ne_top {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) (hM : (⨆ x, chi q x) ≠ ⊤) (o : V) :
    (∀ s : ℝ, 0 ≤ s → s < (2 * (⨆ x, chi q x).toReal ^ 2)⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) *
          exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law q ≤
        ENNReal.ofReal ((chi q o).toReal / sqrt (1 - 2 * s * (⨆ x, chi q x).toReal ^ 2))) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ (2 * (⨆ x, chi q x).toReal ^ 2)⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law q ≤
        ENNReal.ofReal (1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2 *
          (1 - sqrt (1 - 2 * s * (⨆ x, chi q x).toReal ^ 2)))) ∧
    (∀ n : ℝ, 0 < n →
      law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
        ENNReal.ofReal (min 1 (min (sqrt 2 * (chi q o).toReal / n *
            exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2))))
          ((1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2) *
            exp (-(n / (2 * (⨆ x, chi q x).toReal ^ 2))))))) ∧
    (∀ n : ℝ, 4 * (⨆ x, chi q x).toReal ^ 2 *
        log (1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2) ≤ n →
      law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
        ENNReal.ofReal (exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2))))) :=
  ⟨fun _ hs hs1 => lintegral_mul_exp_encard_cluster_le q o hM hs hs1,
    fun _ hs hs1 => lintegral_exp_encard_cluster_le q o hM hs hs1,
    fun _ hn => law_encard_cluster_ge_le_min q o hM hn,
    fun _ hn => law_encard_cluster_ge_le_exp q o hM hn⟩

/-- Independent bonds on `ℤ^d` with probability zero on pairs at sup distance `> R`, `R > 0`,
and `M = ⨆ x, χ(x) < ∞`. Then for every real `r` (in particular every `r ≥ 0`),
`P(o ↔ ℤ^d ∖ (o + [-r,r]^d)) ≤ √2 χ(o) e^{−r/(4RM²)}`. -/
@[tag "YVJT"]
theorem law_exit_le_of_finite_range_of_iSup_chi_ne_top {d : ℕ}
    (q : Sym2 (LatticeSite d) → unitInterval) {R : ℝ} (hR : 0 < R)
    (hq : ∀ x y : LatticeSite d, R < ‖x - y‖ → q s(x, y) = 0)
    (hM : (⨆ x, chi q x) ≠ ⊤) (o : LatticeSite d) (r : ℝ) :
    law q {ω | ∃ y, (openGraph ω).Reachable o y ∧ r < ‖y - o‖} ≤
      ENNReal.ofReal (√2 * (chi q o).toReal *
        exp (-(r / (4 * R * (⨆ x, chi q x).toReal ^ 2)))) :=
  law_exit_le_of_iSup_chi_ne_top q hR hq hM o r

end PercLib.Models
