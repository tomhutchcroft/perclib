/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the conversion of a weighted coordinate-covariance lower bound into a
lower bound on the intensity derivative of the probability of an increasing event. Every
statement is assembled from lemmas proved in the imported modules; no new definition is
introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.RevealmentDerivative

/-!
# Covariance bound to intensity derivative: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Probability.RevealmentDerivative`.

## Main results

* `revealment_derivative_conversion`
-/

@[expose] public section
noncomputable section

namespace PercLib.Probability.FiniteProfile
variable {E : Type*} [Fintype E]

/-- Conditional conversion of a weighted covariance bound into a derivative bound. For an
increasing event `A`, intensity profile `q_β(e) = 1 - e^{-βJₑ}`, numbers `C ≥ 0` and
`δₑ ∈ [0,1]` with `C ≤ ∑ₑ δₑ Cov_β(1_A, Xₑ)`, and `R = sup_{Jₑ > 0} δₑ / cₑ` with
`cₑ = Jₑ/(1 - e^{-βJₑ})` (zero when no weight is positive): if `R > 0` then
`C / R ≤ F'(β)` for `F(b) = P_b(A)`; if `R = 0` then `C = 0`; and if `0 < D ≤ 1` bounds every
`δₑ` with `Jₑ > 0`, then `C / (βD) ≤ F'(β)`. -/
@[tag "8IGH"]
theorem revealment_derivative_conversion (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e) {β : ℝ} (hβ : 0 < β)
    {A : Set (E → Bool)} (hA : IsUpperSet A) {C : ℝ} (hC0 : 0 ≤ C) {δ : E → ℝ}
    (_hδ : ∀ e, δ e ∈ Set.Icc (0 : ℝ) 1)
    (hC : C ≤ ∑ e, δ e * (expectation (fun j => 1 - Real.exp (-β * J j))
        (fun ω => A.indicator (1 : (E → Bool) → ℝ) ω * if ω e then 1 else 0) -
      expectation (fun j => 1 - Real.exp (-β * J j)) (A.indicator 1) *
        expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0))) :
    (0 < ⨆ e : {e // 0 < J e}, δ e / (J e / (1 - Real.exp (-β * J e))) →
      C / (⨆ e : {e // 0 < J e}, δ e / (J e / (1 - Real.exp (-β * J e)))) ≤
        deriv (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) (A.indicator 1)) β) ∧
    ((⨆ e : {e // 0 < J e}, δ e / (J e / (1 - Real.exp (-β * J e)))) = 0 → C = 0) ∧
    (∀ D : ℝ, 0 < D → D ≤ 1 → (∀ e, 0 < J e → δ e ≤ D) →
      C / (β * D) ≤
        deriv (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) (A.indicator 1)) β) :=
  have hf := hA.monotone_indicator monotone_const fun _ => zero_le_one
  ⟨fun hR => div_iSup_le_deriv_expectation_of_le_sum_covariance J hJ hβ hf hC hR,
    fun hR => eq_zero_of_iSup_eq_zero_of_le_sum_covariance J hJ hβ hf hC0 hC hR,
    fun _ hD _ hδD => div_mul_le_deriv_expectation_of_le_sum_covariance J hJ hβ hf hD hδD hC⟩

end PercLib.Probability.FiniteProfile
