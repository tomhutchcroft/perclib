/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.ThroughExpansion

/-!
# Integrating the through-set expansion over earlier layers

The vertex set may depend measurably on arbitrary earlier data. Retaining a
measurable event on those data and integrating the exact fixed-set identity
gives the product-layer identity needed by the lace remainder recurrence.
Tonelli's theorem applies to nonnegative terms, without summability assumptions.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V Ω : Type*} [MeasurableSpace Ω]

/-- Exact expansion after arbitrary measurable earlier layers have been
integrated. The residual uses two fresh independent configurations. -/
theorem prod_throughSet_add_remainder_eq_prod_laceEPrime_add_step [Countable V]
    (q : Sym2 V → unitInterval) (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (A : Ω → Set V) (hA : Measurable A) (a y : V)
    (hfin : ∀ u v : V, ∀ᵐ η ∂law q, (cluster (η \ {s(u, v)}) a).Finite) :
    (μ.prod (law q)) {p : Ω × Config V | p.1 ∈ E ∧ p.2 ∈ throughSet (A p.1) a y} +
      (∑' u, ∑' v,
        offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞)) u v *
          (μ.prod ((law q).prod (law q))) {p : Ω × (Config V × Config V) |
            p.1 ∈ E ∧ p.2.1 ∈ laceEPrime (A p.1) a u ∧
            p.2.2 ∈ throughSet (cluster (p.2.1 \ {s(u, v)}) a) v y}) =
      (μ.prod (law q)) {p : Ω × Config V | p.1 ∈ E ∧ p.2 ∈ laceEPrime (A p.1) a y} +
        ∑' u, ∑' v,
          (μ.prod (law q)) {p : Ω × Config V | p.1 ∈ E ∧ p.2 ∈ laceEPrime (A p.1) a u} *
            offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞)) u v *
            tau q v y := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞))
  let T : V → Set (Ω × Config V) := fun z =>
    {p | p.1 ∈ E ∧ p.2 ∈ throughSet (A p.1) a z}
  let P : V → Set (Ω × Config V) := fun z =>
    {p | p.1 ∈ E ∧ p.2 ∈ laceEPrime (A p.1) a z}
  let R : V → V → Set (Ω × (Config V × Config V)) := fun u v =>
    {p | p.1 ∈ E ∧ p.2.1 ∈ laceEPrime (A p.1) a u ∧
      p.2.2 ∈ throughSet (cluster (p.2.1 \ {s(u, v)}) a) v y}
  have hmT (z : V) : MeasurableSet (T z) := (hE.preimage measurable_fst).inter
    (measurableSet_throughSet_of_measurable (hA.comp measurable_fst) measurable_snd a z)
  have hmP (z : V) : MeasurableSet (P z) := (hE.preimage measurable_fst).inter
    (measurableSet_laceEPrime_of_measurable (hA.comp measurable_fst) measurable_snd a z)
  have hmR (u v : V) : MeasurableSet (R u v) := (hE.preimage measurable_fst).inter
    ((measurableSet_laceEPrime_of_measurable (hA.comp measurable_fst)
      (measurable_fst.comp measurable_snd) a u).inter
      (measurableSet_throughSet_of_measurable
        ((measurable_deleted_cluster s(u, v) a).comp (measurable_fst.comp measurable_snd))
        (measurable_snd.comp measurable_snd) v y))
  let t : V → Ω → ℝ≥0∞ := fun z ω => law q (Prod.mk ω ⁻¹' T z)
  let p : V → Ω → ℝ≥0∞ := fun z ω => law q (Prod.mk ω ⁻¹' P z)
  let r : V → V → Ω → ℝ≥0∞ := fun u v ω =>
    ((law q).prod (law q)) (Prod.mk ω ⁻¹' R u v)
  have ht (z : V) : Measurable (t z) := measurable_measure_prodMk_left (hmT z)
  have hp (z : V) : Measurable (p z) := measurable_measure_prodMk_left (hmP z)
  have hr (u v : V) : Measurable (r u v) := measurable_measure_prodMk_left (hmR u v)
  have hpoint (ω : Ω) : t y ω + (∑' u, ∑' v, J u v * r u v ω) =
      p y ω + ∑' u, ∑' v, p u ω * J u v * tau q v y := by
    by_cases hω : ω ∈ E
    · simpa [t, p, r, T, P, R, hω, J] using
        law_throughSet_add_remainder_eq_laceEPrime_add_step q (A ω) a y hfin
    · simp [t, p, r, T, P, R, hω]
  have hsumR : (∫⁻ ω, ∑' u, ∑' v, J u v * r u v ω ∂μ) =
      ∑' u, ∑' v, J u v * (μ.prod ((law q).prod (law q))) (R u v) := by
    rw [lintegral_tsum (fun u => (Measurable.tsum
      (fun v => (hr u v).const_mul (J u v))).aemeasurable)]
    apply tsum_congr
    intro u
    rw [lintegral_tsum (fun v => ((hr u v).const_mul (J u v)).aemeasurable)]
    apply tsum_congr
    intro v
    rw [lintegral_const_mul _ (hr u v)]
    congr 1
    exact (Measure.prod_apply (hmR u v)).symm
  have hsumP : (∫⁻ ω, ∑' u, ∑' v, p u ω * J u v * tau q v y ∂μ) =
      ∑' u, ∑' v, (μ.prod (law q)) (P u) * J u v * tau q v y := by
    rw [lintegral_tsum (fun u => (Measurable.tsum
      (fun v => ((hp u).mul_const (J u v)).mul_const (tau q v y))).aemeasurable)]
    apply tsum_congr
    intro u
    rw [lintegral_tsum (fun v =>
      (((hp u).mul_const (J u v)).mul_const (tau q v y)).aemeasurable)]
    apply tsum_congr
    intro v
    rw [lintegral_mul_const _ ((hp u).mul_const (J u v)), lintegral_mul_const _ (hp u)]
    congr 2
    exact (Measure.prod_apply (hmP u)).symm
  have hi := lintegral_congr (μ := μ) hpoint
  rw [lintegral_add_left (ht y), lintegral_add_left (hp y), hsumR, hsumP] at hi
  have hiT : (∫⁻ ω, t y ω ∂μ) = (μ.prod (law q)) (T y) :=
    (Measure.prod_apply (hmT y)).symm
  have hiP : (∫⁻ ω, p y ω ∂μ) = (μ.prod (law q)) (P y) :=
    (Measure.prod_apply (hmP y)).symm
  rw [hiT, hiP] at hi
  exact hi

end PercLib.Percolation.Bond.Lace
