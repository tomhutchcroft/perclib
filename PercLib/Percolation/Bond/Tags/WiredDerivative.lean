/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.WiredDerivativeFormula

/-!
# Escape derivative from a finite domain: correspondence

Correspondence wrapper for the exact derivative of the escape probability from a finite domain
and the finite-size differential inequality, from
`PercLib/Percolation/Bond/WiredDerivativeFormula.lean`. No new definitions.

## Main results

* `hasDerivAt_law_escape_and_deriv_ge`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

open Classical in
/-- **Exact wired boundary derivative and finite-size differential inequality.** Let `J` have
summable rows, `Λ` be finite with `o ∈ Λ`, and `f(β) = P_β(K_o ⊄ Λ)` at bond probabilities
`1 - e^{-βJ}`. Write `S = {v ∈ Λ | K_v ⊆ Λ}` and `τ_{T,β}` for the internal connection
probability in `T`. Then
`f'(β) = ∑_{T ⊆ Λ, o ∈ T} P_β(S = T) ∑_{u ∈ T} τ_{T,β}(o,u) ∑_{v ∉ T} J(u,v)` for `β > 0`, the
same formula at `β = 0` is the right derivative, and for `β > 0`
`f'(β) ≥ (1 - f(β))/β · min_{T ⊆ Λ, o ∈ T} ∑_{u ∈ T} τ_{T,β}(o,u) ∑_{v ∉ T} (1 - e^{-βJ(u,v)})`.
-/
@[tag "HATE"]
theorem hasDerivAt_law_escape_and_deriv_ge (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (Λ : Finset V) {o : V} (ho : o ∈ Λ) :
    (∀ β : ℝ, 0 < β →
      HasDerivAt
        (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ})
        (∑ T ∈ Λ.powerset.filter (fun T => o ∈ T),
          (law (intensityProfile J β.toNNReal)).real
              {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} *
            ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
                (localConn (T : Set V) o u) *
              ∑' v, if v ∈ T then 0 else (J s(u, v) : ℝ)) β) ∧
    HasDerivWithinAt
      (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ})
      (∑ T ∈ Λ.powerset.filter (fun T => o ∈ T),
        (law (intensityProfile J (0 : ℝ).toNNReal)).real
            {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} *
          ∑ u ∈ T, (law (intensityProfile J (0 : ℝ).toNNReal)).real
              (localConn (T : Set V) o u) *
            ∑' v, if v ∈ T then 0 else (J s(u, v) : ℝ))
      (Ici 0) 0 ∧
    ∀ β : ℝ, 0 < β →
      (1 - (law (intensityProfile J β.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ}) / β *
          (Λ.powerset.filter (fun T => o ∈ T)).inf'
            ⟨{o}, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 ho),
              Finset.mem_singleton_self o⟩⟩
            (fun T => ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
              (localConn (T : Set V) o u) *
              ∑' v, if v ∈ T then 0 else (intensityProfile J β.toNNReal s(u, v) : ℝ)) ≤
        deriv (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real
          {ω | ¬ cluster ω o ⊆ Λ}) β :=
  ⟨fun _ hβ => hasDerivAt_law_escape J hJ Λ ho hβ,
    hasDerivWithinAt_law_escape J hJ Λ ho le_rfl,
    fun _ hβ => deriv_law_escape_ge J hJ Λ ho hβ⟩

end PercLib.Percolation.Bond
