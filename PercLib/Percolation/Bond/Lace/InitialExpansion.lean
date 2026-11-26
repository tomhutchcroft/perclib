/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
This is the zeroth expansion step of Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2.
The remainder is written as its nonnegative magnitude: its sign in the usual
expansion identity is negative.
-/
module

public import PercLib.Percolation.Bond.Lace.FirstPivotal
public import PercLib.Percolation.Bond.Lace.CuttingFactorization
public import PercLib.Percolation.Bond.Lace.JointMeasurability
public import PercLib.Percolation.Bond.Lace.Remainder.Remainder
public import PercLib.Percolation.Bond.WalkSum

/-!
# The first lace-expansion identity

The first-pivotal partition and cutting-bond factorization give an exact
identity with a nonnegative remainder. Writing the remainder on the left
avoids subtraction of infinite extended-real sums. Every bond weight is the
existing off-diagonal kernel, so arbitrary loop probabilities contribute zero.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- In two independent layers, unrestricted continuation splits exactly into
continuation avoiding the deleted first-layer cluster and continuation through it. -/
theorem prod_doubleConn_tau_eq_avoiding_add_through [Countable V]
    (q : Sym2 V → unitInterval) (x y u v : V) :
    law q (doubleConn x u) * tau q v y =
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ doubleConn x u ∧
        ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
          ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
            ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
              ⟨v, hv⟩ ⟨y, hy⟩} +
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ doubleConn x u ∧
        p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y} := by
  let B : Set (Config V × Config V) := {p |
    p.1 ∈ doubleConn x u ∧
    ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
      ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
        ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
          ⟨v, hv⟩ ⟨y, hy⟩}
  let T : Set (Config V × Config V) := {p | p.1 ∈ doubleConn x u ∧
    p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y}
  have hmT : MeasurableSet T :=
    ((measurableSet_doubleConn x u).preimage measurable_fst).inter
      (measurableSet_throughSet_of_measurable
        ((measurable_deleted_cluster s(u, v) x).comp measurable_fst) measurable_snd v y)
  have hD : Disjoint B T := Set.disjoint_left.mpr fun _ hb ht => ht.2.2 hb.2
  have hdec : doubleConn x u ×ˢ conn v y = B ∪ T := by
    ext p
    constructor
    · rintro ⟨hd, hc⟩
      by_cases ha : ∃ hv : v ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
          ∃ hy : y ∈ (cluster (p.1 \ {s(u, v)}) x)ᶜ,
            ((openGraph p.2).induce (cluster (p.1 \ {s(u, v)}) x)ᶜ).Reachable
              ⟨v, hv⟩ ⟨y, hy⟩
      · exact Or.inl ⟨hd, ha⟩
      · exact Or.inr ⟨hd, hc, ha⟩
    · rintro (⟨hd, hv, hy, hc⟩ | ⟨hd, ht⟩)
      · exact ⟨hd, conn_of_localConn _ _ _ _ hc⟩
      · exact ⟨hd, ht.1⟩
  change law q (doubleConn x u) * law q (conn v y) = _
  rw [← Measure.prod_prod, hdec, measure_union hD hmT]

/-- For one oriented pair, the cutting term plus the through-cluster
remainder is exactly the unrestricted continuation. Diagonal pairs vanish. -/
theorem firstPivotal_add_remainder_eq_step [Countable V]
    (q : Sym2 V → unitInterval) (x y u v : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    law q (cuttingEvent univ x y u v) +
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        ((law q).prod (law q)) {p : Config V × Config V |
          p.1 ∈ doubleConn x u ∧
          p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y} =
      law q (doubleConn x u) *
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y := by
  by_cases huv : u = v
  · subst v
    simp [cuttingEvent_diag, offDiagonal_self]
  · simp only [offDiagonal_apply, Ne.symm huv, ite_false]
    rw [law_cuttingEvent_eq_prod_laceEPrime q univ x y u v hfin]
    simp only [laceEPrime_univ]
    rw [← mul_add, ← prod_doubleConn_tau_eq_avoiding_add_through q x y u v]
    ac_rfl

/-- The zeroth lace-expansion identity, with the nonnegative remainder on
the left. No summability assumption or subtraction of infinities is used. -/
theorem tau_add_initialRemainder_eq_doubleConn_add_step [Countable V]
    (q : Sym2 V → unitInterval) (x y : V)
    (hfin : ∀ u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    tau q x y +
      (∑' u, ∑' v,
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          ((law q).prod (law q)) {p : Config V × Config V |
            p.1 ∈ doubleConn x u ∧
            p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y}) =
      law q (doubleConn x y) +
        ∑' u, ∑' v, law q (doubleConn x u) *
          offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y := by
  have ht : tau q x y = law q (doubleConn x y) +
      ∑' u, ∑' v, law q (cuttingEvent univ x y u v) := by
    simpa only [throughSet_univ, laceEPrime_univ, tau] using
      law_throughSet_eq_add_tsum_cuttingEvent q univ x y
  rw [ht, add_assoc, ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro u
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun v => firstPivotal_add_remainder_eq_step q x y u v (hfin u v)

/-- The same first expansion step in the diagonal-subtracted coefficient
convention `law(doubleConn) = δ + π₀`. -/
theorem tau_add_initialRemainder_eq_indicator_add_piZero_step [Countable V]
    (q : Sym2 V → unitInterval) (x y : V)
    (hfin : ∀ u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    tau q x y +
      (∑' u, ∑' v,
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          ((law q).prod (law q)) {p : Config V × Config V |
            p.1 ∈ doubleConn x u ∧
            p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y}) =
      (if x = y then 1 else 0) + piZero q x y +
        ∑' u, ∑' v, ((if x = u then 1 else 0) + piZero q x u) *
          offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y := by
  simpa only [law_doubleConn_eq_indicator_add_piZero] using
    tau_add_initialRemainder_eq_doubleConn_add_step q x y hfin

/-- At order zero, the canonical finite product of layers is precisely the
two-layer product used in the cutting-bond identity. -/
theorem remainderEvent_zero_probability_eq_prod [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (b : Fin 1 → V × V) :
    (Measure.pi (fun _ : Fin 2 => law q)) (remainderEvent x y b) =
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ doubleConn x (b 0).1 ∧
        p.2 ∈ throughSet (cluster (p.1 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y} := by
  let T : Set (Config V × Config V) := {p | p.1 ∈ doubleConn x (b 0).1 ∧
    p.2 ∈ throughSet (cluster (p.1 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y}
  have hm : MeasurableSet T :=
    ((measurableSet_doubleConn x (b 0).1).preimage measurable_fst).inter
      (measurableSet_throughSet_of_measurable
        ((measurable_deleted_cluster s((b 0).1, (b 0).2) x).comp measurable_fst)
        measurable_snd (b 0).2 y)
  have hpre : MeasurableEquiv.finTwoArrow ⁻¹' T = remainderEvent x y b := by
    ext ω
    change (ω 0 ∈ doubleConn x (b 0).1 ∧
      ω 1 ∈ throughSet (cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y) ↔ _
    exact (mem_remainderEvent_zero_iff x y b ω).symm
  rw [← hpre]
  exact (measurePreserving_finTwoArrow (law q)).measure_preimage hm.nullMeasurableSet

/-- The canonical order-zero remainder is the directed-bond sum appearing
in the initial expansion step. -/
theorem laceRemainder_zero_eq_tsum_prod [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    laceRemainder q 0 x y =
      ∑' u, ∑' v,
        offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          ((law q).prod (law q)) {p : Config V × Config V |
            p.1 ∈ doubleConn x u ∧
            p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y} := by
  rw [laceRemainder]
  change (∑' b : Fin 1 → V × V,
      (∏ i : Fin 1, offDiagonal
        (fun a c : V => (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞)) (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin 2 => law q)) (remainderEvent x y b)) = _
  simp only [Fin.prod_univ_one, remainderEvent_zero_probability_eq_prod]
  rw [← (Equiv.funUnique (Fin 1) (V × V)).symm.tsum_eq]
  change (∑' b : V × V,
      offDiagonal (fun a c : V => (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞)) b.1 b.2 *
        ((law q).prod (law q)) {p : Config V × Config V |
          p.1 ∈ doubleConn x b.1 ∧
          p.2 ∈ throughSet (cluster (p.1 \ {s(b.1, b.2)}) x) b.2 y}) = _
  exact ENNReal.tsum_prod (f := fun u v =>
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
      ((law q).prod (law q)) {p : Config V × Config V |
        p.1 ∈ doubleConn x u ∧
        p.2 ∈ throughSet (cluster (p.1 \ {s(u, v)}) x) v y})

/-- The zeroth lace expansion with the canonical nonnegative remainder. -/
theorem tau_add_laceRemainder_zero_eq_doubleConn_add_step [Countable V]
    (q : Sym2 V → unitInterval) (x y : V)
    (hfin : ∀ u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    tau q x y + laceRemainder q 0 x y =
      law q (doubleConn x y) +
        ∑' u, ∑' v, law q (doubleConn x u) *
          offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y := by
  rw [laceRemainder_zero_eq_tsum_prod]
  exact tau_add_initialRemainder_eq_doubleConn_add_step q x y hfin

/-- In the standard coefficient convention, the first expansion reads
`τ + r₀ = δ + π₀ + Jτ + π₀Jτ`. The signed remainder is therefore `-r₀`. -/
theorem tau_add_laceRemainder_zero_eq_indicator_add_piZero [Countable V]
    (q : Sym2 V → unitInterval) (x y : V)
    (hfin : ∀ u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) x).Finite) :
    tau q x y + laceRemainder q 0 x y =
      (if x = y then 1 else 0) + piZero q x y +
        (∑' v, offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v *
          tau q v y) +
        ∑' u, ∑' v, piZero q x u *
          offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
          tau q v y := by
  rw [tau_add_laceRemainder_zero_eq_doubleConn_add_step q x y hfin]
  simp_rw [law_doubleConn_eq_indicator_add_piZero, add_mul, ENNReal.tsum_add]
  have hi : (∑' u, ∑' v, (if x = u then (1 : ℝ≥0∞) else 0) *
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
      tau q v y) =
      ∑' v, offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v *
        tau q v y := by
    rw [tsum_eq_single x (fun u hu => by simp [Ne.symm hu])]
    simp
  rw [hi]
  ac_rfl

end PercLib.Percolation.Bond.Lace
