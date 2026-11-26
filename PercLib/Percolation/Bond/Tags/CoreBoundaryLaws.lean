/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.BoundaryContraction
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.IntrinsicBalls
public import Mathlib.Probability.ConditionalProbability

/-! Correspondence wrappers for boundary contraction, the exterior law given a cluster, the
critical boundary flux, and intrinsic balls.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

open Classical in
/-- Boundary contraction: finite sets `S_x ∋ x` with internal mass at most `B` and boundary
flux at most `a < 1` give `χ(x) ≤ B/(1-a)`, almost surely finite clusters when `B < ∞`, and
the choice `B = N` when `|S_x| ≤ N`. -/
@[tag "YLZV"]
theorem boundary_contraction_bounds [Countable V] (q : Sym2 V → unitInterval)
    (Sx : V → Finset V) (hSx : ∀ x, x ∈ Sx x) {a : ℝ≥0∞} (ha : a < 1)
    (hΦ : ∀ x, boundaryFlux q (Sx x) x ≤ a) :
    (∀ B : ℝ≥0∞, (∀ x, ∑ u ∈ Sx x, law q (localConn (Sx x : Set V) x u) ≤ B) →
      ∀ x, chi q x ≤ B * (1 - a)⁻¹) ∧
    (∀ B : ℝ≥0∞, B < ∞ → (∀ x, ∑ u ∈ Sx x, law q (localConn (Sx x : Set V) x u) ≤ B) →
      ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite) ∧
    (∀ N : ℕ, (∀ x, (Sx x).card ≤ N) → ∀ x, chi q x ≤ N * (1 - a)⁻¹) :=
  ⟨fun _ hB x => chi_le_of_boundary_contraction q Sx hSx ha hB hΦ x,
    fun _ hBtop hB => ae_cluster_finite_of_boundary_contraction q Sx hSx hBtop ha hB hΦ,
    fun _ hN x => chi_le_of_boundary_contraction_card q Sx hSx hN ha hΦ x⟩

/-- Given `K(x) = C`, measurable events determined by the pairs outside `C` are
independent of the cluster event; when the cluster event has positive probability the
conditional law of such events is the unconditional one, in particular for connections in
`V \ C`. -/
@[tag "E7R2"]
theorem exterior_law_given_cluster [Countable V] (q : Sym2 V → unitInterval) (x : V)
    (C : Finset V) (hx : x ∈ C) :
    (∀ B : Set (Config V), MeasurableSet B →
      (∀ ω ω', (∀ a ∉ C, ∀ b ∉ C, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) → (ω ∈ B ↔ ω' ∈ B)) →
      law q ({ω | cluster ω x = C} ∩ B) = law q {ω | cluster ω x = C} * law q B) ∧
    (0 < law q {ω | cluster ω x = C} → ∀ B : Set (Config V), MeasurableSet B →
      (∀ ω ω', (∀ a ∉ C, ∀ b ∉ C, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) → (ω ∈ B ↔ ω' ∈ B)) →
      ProbabilityTheory.cond (law q) {ω | cluster ω x = C} B = law q B) ∧
    (0 < law q {ω | cluster ω x = C} → ∀ y z : ((C : Set V)ᶜ : Set V),
      ProbabilityTheory.cond (law q) {ω | cluster ω x = C}
        {ω | ((openGraph ω).induce ((C : Set V)ᶜ)).Reachable y z} =
      law q {ω | ((openGraph ω).induce ((C : Set V)ᶜ)).Reachable y z}) := by
  have hmeas := measurableSet_cluster_eq_finset (V := V) x C hx
  have hcancel : ∀ {R : ℝ≥0∞}, 0 < law q {ω | cluster ω x = C} →
      (law q {ω | cluster ω x = C})⁻¹ * (law q {ω | cluster ω x = C} * R) = R := by
    intro R hP
    rw [← mul_assoc, ENNReal.inv_mul_cancel hP.ne' (measure_ne_top _ _), one_mul]
  refine ⟨fun B hB hdet => law_cluster_eq_inter q x C hx hB hdet,
    fun hpos B hB hdet => ?_, fun hpos y z => ?_⟩
  · rw [cond_apply hmeas, law_cluster_eq_inter q x C hx hB hdet]
    exact hcancel hpos
  · rw [cond_apply hmeas, law_cluster_eq_inter_localConn_compl q x C hx y z]
    exact hcancel hpos

open Classical in
/-- For a transitive kernel with finite rows and finite global critical intensity `β_c`,
every finite `S ∋ o` has boundary flux at least one at `β_c`, bounded by
`β_c ∑_{u ∈ S} τ_S(o,u) ∑_{v ∉ S} J(u,v)`. -/
@[tag "R84Z"]
theorem one_le_boundaryFlux_at_globalCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ∞) {o : V}
    (hc : globalCriticalIntensity J < ⊤) (S : Finset V) (hoS : o ∈ S) :
    1 ≤ boundaryFlux (intensityProfile J (globalCriticalIntensity J).toNNReal) S o ∧
    boundaryFlux (intensityProfile J (globalCriticalIntensity J).toNNReal) S o ≤
    globalCriticalIntensity J * ∑ u ∈ S,
      law (intensityProfile J (globalCriticalIntensity J).toNNReal)
        (localConn (S : Set V) o u) *
      ∑' v, (if v ∈ S then 0 else (J s(u, v) : ℝ≥0∞)) := by
  have h := rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive J hT o
  have key := one_le_boundaryFlux_at_rootCriticalIntensity J hT hrow (h ▸ hc) S hoS
  rw [h] at key
  exact key

/-- Intrinsic balls under the exponential intensity profile: for `0 < α ≤ β`, the
probability of intrinsic distance at most `r` and the expected closed ball volume are
bounded by `(β/α)^r` times the corresponding quantities at `α`; a susceptibility bound
`χ(b-ε) ≤ C/ε` for small `ε` gives linear growth `(eC/b)(r+1)` of the expected ball volume
at `b` for large `r`. -/
@[tag "PI11"]
theorem intrinsic_ball_bounds [Countable V] (J : Sym2 V → ℝ≥0) :
    (∀ {α β : ℝ≥0}, 0 < α → α ≤ β → ∀ (o x : V) (r : ℕ),
      law (intensityProfile J β) {ω | (openGraph ω).edist o x ≤ r} ≤
        ((β : ℝ≥0∞) / α) ^ r * tau (intensityProfile J α) o x) ∧
    (∀ {α β : ℝ≥0}, 0 < α → α ≤ β → ∀ (o : V) (r : ℕ),
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)
          ∂law (intensityProfile J β) ≤
        ((β : ℝ≥0∞) / α) ^ r * chi (intensityProfile J α) o) ∧
    (∀ (o : V) {b : ℝ≥0}, 0 < b → ∀ (C : ℝ≥0∞) {ε₀ : ℝ≥0}, 0 < ε₀ →
      (∀ ε : ℝ≥0, 0 < ε → ε < ε₀ → chi (intensityProfile J (b - ε)) o ≤ C / ε) →
      ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
        ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)
            ∂law (intensityProfile J b) ≤
          ENNReal.ofReal (Real.exp 1) * C / b * (r + 1)) :=
  ⟨fun hα hαβ o x r => law_edist_le_le J hα hαβ o x r,
    fun hα hαβ o r => lintegral_ball_le J hα hαβ o r,
    fun o _ hb C _ hε₀ hχ => eventually_lintegral_ball_le J o hb C hε₀ hχ⟩

end PercLib.Percolation.Bond
