/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Bounds
public import PercLib.Percolation.Bond.Lace.LayerIntegration

/-!
# The nonnegative lace recurrence

The fixed-set through-connection expansion is integrated over all earlier
independent configurations. All identities are in the extended nonnegative
reals, so no summability of the coefficients is assumed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem measurePreserving_snoc_layers (q : Sym2 V → unitInterval) (n : ℕ) :
    MeasurePreserving
      (fun p : (Fin n → Config V) × Config V => (Fin.snoc p.1 p.2 : Fin (n + 1) → Config V))
      ((Measure.pi (fun _ : Fin n => law q)).prod (law q))
      (Measure.pi (fun _ : Fin (n + 1) => law q)) := by
  have h := ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => law q) (Fin.last n)).symm).comp
      Measure.measurePreserving_swap
  convert h using 1
  funext p
  exact (Fin.insertNth_last' p.2 p.1).symm

/-- Finite independent configurations split into their prefix and final layer. -/
theorem measure_layers_eq_prod_snoc (q : Sym2 V → unitInterval) {n : ℕ}
    {S : Set (Fin (n + 1) → Config V)} (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin (n + 1) => law q)) S =
      ((Measure.pi (fun _ : Fin n => law q)).prod (law q))
        {p | Fin.snoc p.1 p.2 ∈ S} :=
  ((measurePreserving_snoc_layers q n).measure_preimage hS.nullMeasurableSet).symm

/-- Split off two configurations, retaining their original order. -/
theorem measure_layers_eq_prod_snoc_snoc (q : Sym2 V → unitInterval) {n : ℕ}
    {S : Set (Fin (n + 2) → Config V)} (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin (n + 2) => law q)) S =
      ((Measure.pi (fun _ : Fin n => law q)).prod ((law q).prod (law q)))
        {p | Fin.snoc (Fin.snoc p.1 p.2.1) p.2.2 ∈ S} := by
  have h := (measurePreserving_snoc_layers q (n + 1)).comp
    (((measurePreserving_snoc_layers q n).prod (MeasurePreserving.id (law q))).comp
      ((measurePreserving_prodAssoc (Measure.pi (fun _ : Fin n => law q))
        (law q) (law q)).symm))
  exact (h.measure_preimage hS.nullMeasurableSet).symm

set_option maxHeartbeats 800000 in
/-- The last sections of the coefficient and remainder share the same
measurable event on the earlier layers. This includes order zero, where that
event is the full double-connection event. -/
theorem coefficient_remainder_last_sections [Countable V] {n : ℕ}
    (x : V) (b : Fin (n + 1) → V × V) :
    ∃ E : Set (Fin (n + 1) → Config V), MeasurableSet E ∧
      ∀ (y : V) (ω : Fin (n + 1) → Config V) (η : Config V),
        (Fin.snoc ω η ∈ coefficientEvent x y b ↔
          ω ∈ E ∧ η ∈ laceEPrime
            (cluster (ω (Fin.last n) \ {s((b (Fin.last n)).1, (b (Fin.last n)).2)})
              (Fin.cases x (fun j => (b j).2) (Fin.last n).castSucc))
            (b (Fin.last n)).2 y) ∧
        (Fin.snoc ω η ∈ remainderEvent x y b ↔
          ω ∈ E ∧ η ∈ throughSet
            (cluster (ω (Fin.last n) \ {s((b (Fin.last n)).1, (b (Fin.last n)).2)})
              (Fin.cases x (fun j => (b j).2) (Fin.last n).castSucc))
            (b (Fin.last n)).2 y) := by
  let E : Set (Fin (n + 1) → Config V) := {ω |
    ω 0 ∈ doubleConn x (b 0).1 ∧ ∀ i : Fin n,
      ω i.succ ∈ laceEPrime
        (cluster (ω i.castSucc \ {s((b i.castSucc).1, (b i.castSucc).2)})
          (Fin.cases x (fun j => (b j).2) i.castSucc.castSucc))
        (b i.castSucc).2 (b i.succ).1}
  have hmE : MeasurableSet E := by
    unfold E
    simp only [ofPred_and, ofPred_forall]
    refine ((measurableSet_doubleConn x (b 0).1).preimage (measurable_pi_apply 0)).inter
      (MeasurableSet.iInter fun i => ?_)
    generalize (Fin.cases x (fun j => (b j).2) i.castSucc.castSucc : V) = a
    exact measurableSet_laceEPrime_of_measurable
      ((measurable_deleted_cluster s((b i.castSucc).1, (b i.castSucc).2) a).comp
        (measurable_pi_apply i.castSucc)) (measurable_pi_apply i.succ) _ _
  have hout (y : V) (i : Fin n) :
      (Fin.lastCases y (fun j => (b j).1) i.castSucc.succ : V) = (b i.succ).1 := by
    rw [← Fin.castSucc_succ, Fin.lastCases_castSucc]
  refine ⟨E, hmE, fun y ω η => ?_⟩
  have hω (i : Fin n) :
      (Fin.snoc ω η : Fin (n + 2) → Config V) i.castSucc.succ = ω i.succ := by
    rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
  have hn (i : Fin n) : (i.castSucc : Fin (n + 1)).val ≠ n := Nat.ne_of_lt i.isLt
  constructor
  · constructor
    · rintro ⟨h0, h⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [Fin.snoc_apply_zero] using h0
      · intro i
        simpa only [hω, Fin.snoc_castSucc, hout] using h i.castSucc
      · simpa only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc,
          Fin.lastCases_last] using h (Fin.last n)
    · rintro ⟨⟨h0, h⟩, hη⟩
      refine ⟨?_, ?_⟩
      · simpa only [Fin.snoc_apply_zero] using h0
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc,
            Fin.lastCases_last] using hη
        · simpa only [hω, Fin.snoc_castSucc, hout] using h j
  · constructor
    · rintro ⟨h0, h⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [Fin.snoc_apply_zero] using h0
      · intro i
        simpa only [hn, ite_false, hω, Fin.snoc_castSucc, hout] using h i.castSucc
      · simpa only [Fin.val_last, ite_eq_left, Fin.succ_last, Fin.snoc_last,
          Fin.snoc_castSucc, Fin.lastCases_last] using h (Fin.last n)
    · rintro ⟨⟨h0, h⟩, hη⟩
      refine ⟨?_, ?_⟩
      · simpa only [Fin.snoc_apply_zero] using h0
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.val_last, ite_eq_left, Fin.succ_last, Fin.snoc_last,
            Fin.snoc_castSucc, Fin.lastCases_last] using hη
        · simpa only [hn, ite_false, hω, Fin.snoc_castSucc, hout] using h j

/-- One exact expansion step for a fixed sequence of preceding oriented bonds. -/
theorem remainderEvent_add_tsum_snoc_eq_coefficientEvent_add_step [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V)
    (hfin : ∀ a u v : V, ∀ᵐ η ∂law q, (cluster (η \ {s(u, v)}) a).Finite) :
    (Measure.pi (fun _ : Fin (n + 2) => law q)) (remainderEvent x y b) +
      (∑' u, ∑' v,
        offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞)) u v *
          (Measure.pi (fun _ : Fin (n + 3) => law q))
            (remainderEvent x y (Fin.snoc b (u, v)))) =
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b) +
        ∑' u, ∑' v,
          (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x u b) *
            offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞)) u v *
              tau q v y := by
  obtain ⟨E, hE, hsections⟩ := coefficient_remainder_last_sections x b
  let μ := Measure.pi (fun _ : Fin (n + 1) => law q)
  let a := (b (Fin.last n)).2
  let A : (Fin (n + 1) → Config V) → Set V := fun ω =>
    cluster (ω (Fin.last n) \ {s((b (Fin.last n)).1, (b (Fin.last n)).2)})
      (Fin.cases x (fun j => (b j).2) (Fin.last n).castSucc)
  have hA : Measurable A :=
    (measurable_deleted_cluster s((b (Fin.last n)).1, (b (Fin.last n)).2)
      (Fin.cases x (fun j => (b j).2) (Fin.last n).castSucc)).comp
      (measurable_pi_apply (Fin.last n))
  have hC (z : V) :
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x z b) =
        (μ.prod (law q)) {p | p.1 ∈ E ∧ p.2 ∈ laceEPrime (A p.1) a z} := by
    rw [measure_layers_eq_prod_snoc q (measurableSet_coefficientEvent x z b)]
    congr 1
    ext p
    exact (hsections z p.1 p.2).1
  have hR (z : V) :
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (remainderEvent x z b) =
        (μ.prod (law q)) {p | p.1 ∈ E ∧ p.2 ∈ throughSet (A p.1) a z} := by
    rw [measure_layers_eq_prod_snoc q (measurableSet_remainderEvent x z b)]
    congr 1
    ext p
    exact (hsections z p.1 p.2).2
  have hApp (u v : V) :
      (Measure.pi (fun _ : Fin (n + 3) => law q))
        (remainderEvent x y (Fin.snoc b (u, v))) =
      (μ.prod ((law q).prod (law q))) {p | p.1 ∈ E ∧
        p.2.1 ∈ laceEPrime (A p.1) a u ∧
        p.2.2 ∈ throughSet (cluster (p.2.1 \ {s(u, v)}) a) v y} := by
    rw [measure_layers_eq_prod_snoc_snoc q
      (measurableSet_remainderEvent x y (Fin.snoc b (u, v)))]
    congr 1
    ext p
    change (Fin.snoc (Fin.snoc p.1 p.2.1) p.2.2 ∈
      remainderEvent x y (Fin.snoc b (u, v))) ↔ _
    rw [mem_remainderEvent_snoc_iff, (hsections u p.1 p.2.1).1]
    simp only [Fin.snoc_last, and_assoc, Set.mem_ofPred_eq, A, a]
  simpa only [← hC, ← hR, ← hApp] using
    prod_throughSet_add_remainder_eq_prod_laceEPrime_add_step
      q μ E hE A hA a y (hfin a)

/-- The exact nonnegative lace recurrence at every order. The finiteness
hypothesis is the cutting-factorization hypothesis, uniform over the root and
the deleted bond; no finiteness of coefficients or remainders is assumed. -/
@[tag "G1IE"]
theorem laceRemainder_add_succ_eq_laceCoefficient_add_step [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V)
    (hfin : ∀ a u v : V, ∀ᵐ η ∂law q, (cluster (η \ {s(u, v)}) a).Finite) :
    laceRemainder q n x y + laceRemainder q (n + 1) x y =
      laceCoefficient q (n + 1) x y + ∑' u, ∑' v,
        laceCoefficient q (n + 1) x u *
          offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞)) u v *
            tau q v y := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun c d : V => (unitInterval.toNNReal (q s(c, d)) : ℝ≥0∞))
  let W : (Fin (n + 1) → V × V) → ℝ≥0∞ := fun b => ∏ i, J (b i).1 (b i).2
  have hrem : laceRemainder q (n + 1) x y =
      ∑' b : Fin (n + 1) → V × V, W b * (∑' u, ∑' v,
        J u v * (Measure.pi (fun _ : Fin (n + 3) => law q))
          (remainderEvent x y (Fin.snoc b (u, v)))) := by
    calc
      _ = ∑' c : V × V, ∑' b : Fin (n + 1) → V × V,
          W b * J c.1 c.2 * (Measure.pi (fun _ : Fin (n + 3) => law q))
            (remainderEvent x y (Fin.snoc b c)) := by
        unfold laceRemainder
        rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => V × V)).tsum_eq,
          ENNReal.tsum_prod']
        apply tsum_congr
        intro c
        apply tsum_congr
        intro b
        change (∏ i, J ((Fin.snoc b c : Fin (n + 2) → V × V) i).1
          ((Fin.snoc b c : Fin (n + 2) → V × V) i).2) * _ = _
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.snocEquiv, Equiv.coe_fn_mk]
        rfl
      _ = ∑' b : Fin (n + 1) → V × V, ∑' c : V × V,
          W b * J c.1 c.2 * (Measure.pi (fun _ : Fin (n + 3) => law q))
            (remainderEvent x y (Fin.snoc b c)) := ENNReal.tsum_comm
      _ = _ := by
        apply tsum_congr
        intro b
        rw [ENNReal.tsum_prod']
        simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  have hstep :
      (∑' b : Fin (n + 1) → V × V, W b * (∑' u, ∑' v,
        (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x u b) *
          J u v * tau q v y)) =
      ∑' u, ∑' v, laceCoefficient q (n + 1) x u * J u v * tau q v y := by
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro u
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro v
    calc
      _ = (∑' b : Fin (n + 1) → V × V, W b *
          (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x u b)) *
            J u v * tau q v y := by
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      _ = _ := rfl
  have hsum := tsum_congr (L := SummationFilter.unconditional _) (fun b : Fin (n + 1) → V × V =>
    congrArg (fun z : ℝ≥0∞ => W b * z)
      (remainderEvent_add_tsum_snoc_eq_coefficientEvent_add_step q x y b hfin))
  simp_rw [mul_add, ENNReal.tsum_add] at hsum
  rw [← hrem, hstep] at hsum
  exact hsum

end PercLib.Percolation.Bond.Lace
