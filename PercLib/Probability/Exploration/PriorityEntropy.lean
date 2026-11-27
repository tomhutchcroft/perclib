/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original assembly of finite-transcript entropy for the canonical stopped
priority exploration. Uses mathlib's KL chain rule and the library's actual
Bernoulli conditional laws, divergence bounds, and weighted revealment bound.
-/
module

public import PercLib.Probability.Exploration.PriorityTranscript
public import PercLib.Probability.Exploration.WeightedRevealment
public import PercLib.Probability.DiscreteEntropy
public import PercLib.Probability.BernoulliDivergence
public import PercLib.Percolation.Bond.Intensity.Defs

/-!
# Relative entropy of finite stopped-exploration transcripts

## Main results

The relative entropy of the actual finite answer transcript is exactly the
expected sum of the relative entropies of its queried Bernoulli coordinates.
The cemetery answer contributes zero. The identity allows arbitrary profiles,
including endpoint probabilities and infinite relative entropy.

For positive intensity parameters the bound retains the exact Poisson
relative-entropy factor and the coefficient-one weighted revealment estimate.
No independence of the random queried set, absolute continuity, or finite
susceptibility is assumed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory ProbabilityTheory InformationTheory PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}
variable [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)]

/-- The actual next-answer law is a finite-prefix Markov kernel. The supplied
prefix function represents the deterministic actual query, not an independence
assumption. The kernel is specified even at null or unrealizable prefixes. -/
theorem exists_priorityAnswer_prefix_next_kernel (G : SimpleGraph V)
    (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ)
    (next : (Fin m → Option Bool) → Option G.edgeSet)
    (hnext : ∀ ω : Config V, priorityQuery G ι o n ω m =
      next (fun s => priorityAnswer G ι o n ω s))
    (q : Sym2 V → unitInterval) :
    ∃ κ : Kernel (Fin m → Option Bool) (Option Bool), IsMarkovKernel κ ∧
      (∀ a, κ a = (next a).elim (Measure.dirac none)
        (fun e => bernoulliMeasure (some true : Option Bool) (some false)
          (q (e : Sym2 V)))) ∧
      (law q).map (fun ω : Config V =>
        ((fun s : Fin m => priorityAnswer G ι o n ω s), priorityAnswer G ι o n ω m)) =
        ((law q).map (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) ⊗ₘ κ := by
  classical
  let A (ω : Config V) (s : Fin m) := priorityAnswer G ι o n ω s
  let κ : Kernel (Fin m → Option Bool) (Option Bool) :=
    ⟨fun a => (next a).elim (Measure.dirac none)
      (fun e => bernoulliMeasure (some true : Option Bool) (some false)
        (q (e : Sym2 V))), measurable_of_finite _⟩
  have hκ (a) : κ a = (next a).elim (Measure.dirac none)
      (fun e => bernoulliMeasure (some true : Option Bool) (some false)
        (q (e : Sym2 V))) := rfl
  have : IsMarkovKernel κ := ⟨fun a => by
    rw [hκ]
    cases next a <;> dsimp <;> infer_instance⟩
  refine ⟨κ, inferInstance, hκ, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  have hAm : Measurable A := measurable_priorityAnswer_prefix G ι o n m
  rw [Measure.map_apply (hAm.prodMk (measurable_priorityAnswer G ι o n m))
    (measurableSet_singleton _)]
  conv_rhs =>
    rw [show ({(a, b)} : Set ((Fin m → Option Bool) × Option Bool)) = {a} ×ˢ {b} by simp,
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      lintegral_singleton, Measure.map_apply hAm (measurableSet_singleton _)]
  by_cases ha : ∃ ω₀ : Config V, A ω₀ = a
  · obtain ⟨ω₀, rfl⟩ := ha
    have h := law_priorityAnswer_prefix_inter_next G ι o n m q ω₀ b
    simp only [Set.preimage, mem_singleton_iff, Prod.mk.injEq]
    rw [hκ, ← hnext ω₀]
    cases he : priorityQuery G ι o n ω₀ m <;>
      simpa only [A, he, Option.elim_none, Option.elim_some, mul_comm] using h
  · have hpre : A ⁻¹' {a} = ∅ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun h => ha ⟨ω, h⟩
    have hjoint : (fun ω : Config V => (A ω, priorityAnswer G ι o n ω m)) ⁻¹' {(a, b)} = ∅ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_empty_iff_false,
        iff_false, not_and]
      exact fun h => (ha ⟨ω, h⟩).elim
    rw [hjoint, hpre]
    simp

/-- The exact one-step entropy increment of the actual stopped exploration. -/
theorem klDiv_priorityAnswer_prefix_succ (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ)
    (o : V) (n m : ℕ) (p q : Sym2 V → unitInterval) :
    klDiv
      ((law p).map (fun (ω : Config V) (s : Fin (m + 1)) => priorityAnswer G ι o n ω s))
      ((law q).map (fun (ω : Config V) (s : Fin (m + 1)) => priorityAnswer G ι o n ω s)) =
    klDiv
      ((law p).map (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s))
      ((law q).map (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) +
    ∫⁻ ω, (priorityQuery G ι o n ω m).elim 0 (fun e =>
      klDiv (bernoulliMeasure (some true : Option Bool) (some false) (p (e : Sym2 V)))
        (bernoulliMeasure (some true : Option Bool) (some false) (q (e : Sym2 V)))) ∂law p := by
  classical
  let A (ω : Config V) (s : Fin m) := priorityAnswer G ι o n ω s
  let B (ω : Config V) (s : Fin (m + 1)) := priorityAnswer G ι o n ω s
  let L (ω : Config V) := (A ω, priorityAnswer G ι o n ω m)
  let split (a : Fin (m + 1) → Option Bool) := (fun s : Fin m => a s.castSucc, a (Fin.last m))
  let join (a : (Fin m → Option Bool) × Option Bool) : Fin (m + 1) → Option Bool :=
    Fin.snoc a.1 a.2
  have hAm : Measurable A := measurable_priorityAnswer_prefix G ι o n m
  have hBm : Measurable B := measurable_priorityAnswer_prefix G ι o n (m + 1)
  have hLm : Measurable L := hAm.prodMk (measurable_priorityAnswer G ι o n m)
  have hs (r : Sym2 V → unitInterval) : ((law r).map B).map split = (law r).map L := by
    rw [Measure.map_map (measurable_of_finite _) hBm]
    rfl
  have hj (r : Sym2 V → unitInterval) : ((law r).map L).map join = (law r).map B := by
    rw [Measure.map_map (measurable_of_finite _) hLm]
    congr 1
    funext ω
    exact Fin.snoc_init_self (B ω)
  have hKL : klDiv ((law p).map B) ((law q).map B) =
      klDiv ((law p).map L) ((law q).map L) := by
    apply le_antisymm
    · simpa only [hj] using klDiv_map_le ((law p).map L) ((law q).map L)
        (measurable_of_finite join)
    · simpa only [hs] using klDiv_map_le ((law p).map B) ((law q).map B)
        (measurable_of_finite split)
  obtain ⟨next, hnext⟩ := exists_priorityQuery_eq_prefix G ι o n m
  obtain ⟨κ, hκm, hκ, hkp⟩ := exists_priorityAnswer_prefix_next_kernel G ι o n m next hnext p
  obtain ⟨η, hηm, hη, hkq⟩ := exists_priorityAnswer_prefix_next_kernel G ι o n m next hnext q
  let : IsMarkovKernel κ := hκm
  let : IsMarkovKernel η := hηm
  change klDiv ((law p).map B) ((law q).map B) = _
  rw [hKL, hkp, hkq, klDiv_compProd_eq_add, klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_of_finite _) hAm]
  congr 1
  apply lintegral_congr
  intro ω
  rw [hκ, hη, ← hnext ω]
  cases priorityQuery G ι o n ω m <;> simp

/-- Exact finite-transcript entropy: queried coordinates contribute their
Bernoulli relative entropy, while cemetery steps contribute zero. No absolute
continuity or endpoint-positivity hypothesis is needed. -/
theorem klDiv_priorityAnswer_prefix_eq_lintegral_sum (G : SimpleGraph V)
    (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ) (p q : Sym2 V → unitInterval) :
    klDiv
      ((law p).map (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s))
      ((law q).map (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) =
      ∫⁻ ω, ∑ s : Fin m,
        (priorityQuery G ι o n ω s).elim 0 (fun e =>
          klDiv (bernoulliMeasure (some true : Option Bool) (some false) (p (e : Sym2 V)))
            (bernoulliMeasure (some true : Option Bool) (some false) (q (e : Sym2 V)))) ∂law p := by
  induction m with
  | zero =>
    have hmap (r : Sym2 V → unitInterval) :
        (law r).map (fun (ω : Config V) (s : Fin 0) => priorityAnswer G ι o n ω s) =
          Measure.dirac (fun s : Fin 0 => Fin.elim0 s) := by
      have hf : (fun (ω : Config V) (s : Fin 0) => priorityAnswer G ι o n ω s) =
          (fun _ : Config V => fun s : Fin 0 => Fin.elim0 s) := by
        funext ω s
        exact Fin.elim0 s
      rw [hf, Measure.map_const]
      simp
    simp [hmap]
  | succ m ih =>
    rw [klDiv_priorityAnswer_prefix_succ, ih]
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [lintegral_add_right]
    exact measurable_priorityQuery_elim G ι o n m 0 _

/-- The actual one-bond intensity divergence is bounded by its weight times
the exact Poisson divergence factor, including bonds of intensity zero. -/
theorem klDiv_bernoulliMeasure_intensity_le (J : Sym2 V → ℝ≥0)
    (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂) (e : Sym2 V) :
    klDiv
      (bernoulliMeasure (some true : Option Bool) (some false) (intensityProfile J β₁ e))
      (bernoulliMeasure (some true : Option Bool) (some false) (intensityProfile J β₂ e)) ≤
      (J e : ℝ≥0∞) * ENNReal.ofReal
        ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) := by
  have h₁r : 0 < (β₁ : ℝ) := by exact_mod_cast h₁
  have h₂r : 0 < (β₂ : ℝ) := by exact_mod_cast h₂
  by_cases he : J e = 0
  · have hz (β : ℝ≥0) : intensityProfile J β e = 0 := by
      apply Subtype.ext
      simp [intensityProfile, he]
    rw [hz, hz, klDiv_self, he]
    simp
  · have hepos : 0 < (J e : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr he)
    have hq0 : 0 < (intensityProfile J β₂ e : ℝ) := by
      change 0 < 1 - Real.exp (-(β₂ : ℝ) * (J e : ℝ))
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos h₂r) hepos))
    have hq1 : (intensityProfile J β₂ e : ℝ) < 1 := by
      change 1 - Real.exp (-(β₂ : ℝ) * (J e : ℝ)) < 1
      exact sub_lt_self _ (Real.exp_pos _)
    rw [klDiv_bernoulliMeasure_eq_ofReal (by decide) _ _ hq0 hq1]
    have hb := ENNReal.ofReal_le_ofReal
      (bernoulliDivergence_exp_le_of_nonneg (J e).coe_nonneg h₁r h₂r)
    simpa only [intensityProfile, neg_mul, ENNReal.ofReal_mul (J e).coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using hb

/-- Finite-transcript intensity entropy is bounded by the exact Poisson
factor times the actual expected truncated cluster volume, with coefficient
one. Parameters specify the exploration, two laws and a row cap; the only
additional assumptions are positive intensities, a positive threshold and
the displayed row bound. -/
theorem klDiv_priorityAnswer_prefix_intensity_le [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0∞) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    klDiv
      ((law (intensityProfile J β₁)).map
        (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s))
      ((law (intensityProfile J β₂)).map
        (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) ≤
      ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) * M *
        ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
          ∂law (intensityProfile J β₁) := by
  let Φ := ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂)
  let C (ω : Config V) (t : ℕ) : ℝ≥0∞ :=
    (priorityQuery G ι o n ω t).elim 0 (fun e => (J (e : Sym2 V) : ℝ≥0∞))
  have hCm (t : ℕ) : Measurable (fun ω : Config V => C ω t) :=
    measurable_priorityQuery_elim G ι o n t 0 _
  rw [klDiv_priorityAnswer_prefix_eq_lintegral_sum]
  calc
    _ ≤ ∫⁻ ω, Φ * ∑' t : ℕ, C ω t ∂law (intensityProfile J β₁) := by
      apply lintegral_mono
      intro ω
      calc
        _ ≤ ∑ s : Fin m, Φ * C ω s := by
          apply Finset.sum_le_sum
          intro s _
          cases he : priorityQuery G ι o n ω s with
          | none => simp [C, he]
          | some e =>
            simpa only [C, he, Option.elim_some, mul_comm] using
              klDiv_bernoulliMeasure_intensity_le J β₁ β₂ h₁ h₂ (e : Sym2 V)
        _ = Φ * ∑ s : Fin m, C ω s := (Finset.mul_sum _ _ _).symm
        _ ≤ Φ * ∑' t : ℕ, C ω t := mul_le_mul_right
          (by simpa only [tsum_fintype] using
            ENNReal.tsum_comp_le_tsum_of_injective (Fin.val_injective (n := m)) (C ω)) Φ
    _ = Φ * ∫⁻ ω, ∑' t : ℕ, C ω t ∂law (intensityProfile J β₁) :=
      lintegral_const_mul Φ (Measurable.tsum hCm)
    _ ≤ Φ * (M * ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
        ∂law (intensityProfile J β₁)) := mul_le_mul_right
      (lintegral_tsum_priorityQuery_weight_le G ι o n hn (intensityProfile J β₁)
        (fun e => (J e : ℝ≥0∞)) M hrow) Φ
    _ = _ := (mul_assoc _ _ _).symm

/-- The exact intensity factor times the susceptibility truncated at the
stopping threshold bounds every finite transcript, uniformly in its horizon. -/
theorem klDiv_priorityAnswer_prefix_intensity_le_min_chi [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0∞) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    klDiv
      ((law (intensityProfile J β₁)).map
        (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s))
      ((law (intensityProfile J β₂)).map
        (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) ≤
      ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) * M *
        min (chi (intensityProfile J β₁) o) (n : ℝ≥0∞) :=
  (klDiv_priorityAnswer_prefix_intensity_le G ι o n m hn J β₁ β₂ h₁ h₂ M hrow).trans
    (mul_le_mul_right
      (lintegral_truncated_restricted_cluster_le_min_chi G (intensityProfile J β₁) o n) _)

/-- A finite intensity row cap makes the actual finite-transcript entropy
finite, even when the unrestricted susceptibility is infinite. -/
theorem klDiv_priorityAnswer_prefix_intensity_ne_top [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    klDiv
      ((law (intensityProfile J β₁)).map
        (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s))
      ((law (intensityProfile J β₂)).map
        (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _
    (klDiv_priorityAnswer_prefix_intensity_le_min_chi G ι o n m hn J β₁ β₂ h₁ h₂ M hrow)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
    (ne_top_of_le_ne_top (by simp) (min_le_right _ _))

end PercLib.Percolation.Bond
