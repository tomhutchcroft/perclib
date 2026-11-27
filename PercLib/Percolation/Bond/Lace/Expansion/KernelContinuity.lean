/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original continuity consequences of the canonical coefficient events and their
proved diagram envelopes. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.ZeroContinuity
public import PercLib.Percolation.Bond.Lace.Expansion.CoefficientContinuity
public import PercLib.Percolation.Bond.Lace.Diagrams.Convergence
public import PercLib.Analysis.CharacterSeries
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Spatial continuity of the signed lace kernel

## Main results

Contracting upper-profile diagram bounds and almost surely finite upper-profile
clusters give joint `ℓ¹` continuity of all canonical coefficient orders and
endpoints. Consequently, the signed lace kernel is continuous in spatial `ℓ¹`,
its signed row mass is continuous, and its character transform converges
uniformly over all unitary characters. Finite susceptibility is not assumed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology PercLib.Analysis
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- An upper-profile tuple envelope also bounds each positive coefficient at
every smaller profile, without monotonicity of coefficient events. -/
theorem laceCoefficient_succ_le_upper_laceDiagram [Countable V]
    {q q₀ : Sym2 V → unitInterval} (hq : q ≤ q₀) (n : ℕ) (x y : V) :
    laceCoefficient q (n + 1) x y ≤ laceDiagram q₀ n x y := by
  rw [← tsum_coefficientTupleDiagram q₀ n x y]
  exact ENNReal.tsum_le_tsum fun b =>
    weighted_coefficientEvent_probability_le_upper_coefficientTupleDiagram hq x y b

/-- Contracting diagram bounds at one profile imply finite total coefficient
mass at every smaller profile, including the zeroth order. -/
theorem tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds [Countable V]
    {q q₀ : Sym2 V → unitInterval} (hq : q ≤ q₀) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤) :
    (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤ := by
  have hzero : (∑' y, piZero q x y) ≠ ⊤ :=
    ne_top_of_le_ne_top hinitial
      ((ENNReal.tsum_le_tsum fun y => piZero_mono hq x y).trans
        (tsum_piZero_le_diagramInitial q₀ x))
  have hpositive : (∑' n : ℕ, ∑' y, laceCoefficient q (n + 1) x y) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (tsum_laceDiagram_mass_ne_top q₀ x ρ κ hρone hκfinite hρ hκ hinitial)
      (ENNReal.tsum_le_tsum fun n =>
        ENNReal.tsum_le_tsum fun y => laceCoefficient_succ_le_upper_laceDiagram hq n x y)
  rw [tsum_eq_zero_add' ENNReal.summable]
  exact ENNReal.add_ne_top.mpr ⟨hzero, hpositive⟩

/-- Finite total coefficient mass gives joint real summability in the order
and endpoint. -/
theorem summable_laceCoefficient_toReal (q : Sym2 V → unitInterval) (x : V)
    (hq : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤) :
    Summable (fun p : ℕ × V => (laceCoefficient q p.1 x p.2).toReal) := by
  apply ENNReal.summable_toReal
  simpa only [ENNReal.tsum_prod'] using hq

/-- Finite total coefficient masses make their absolute difference summable
jointly in the order and endpoint. -/
theorem summable_abs_laceCoefficient_sub
    (q q' : Sym2 V → unitInterval) (x : V)
    (hq : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤)
    (hq' : (∑' n : ℕ, ∑' y, laceCoefficient q' n x y) ≠ ⊤) :
    Summable (fun p : ℕ × V =>
      |(laceCoefficient q p.1 x p.2).toReal - (laceCoefficient q' p.1 x p.2).toReal|) :=
  ((summable_laceCoefficient_toReal q x hq).sub
    (summable_laceCoefficient_toReal q' x hq')).abs

/-- The signed spatial kernel difference is bounded by the joint coefficient
difference with constant one. -/
theorem tsum_abs_laceSum_sub_le
    (q q' : Sym2 V → unitInterval) (x : V)
    (hq : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤)
    (hq' : (∑' n : ℕ, ∑' y, laceCoefficient q' n x y) ≠ ⊤) :
    (∑' y, |laceSum q x y - laceSum q' x y|) ≤
      ∑' n : ℕ, ∑' y,
        |(laceCoefficient q n x y).toReal - (laceCoefficient q' n x y).toReal| := by
  have hd := summable_abs_laceCoefficient_sub q q' x hq hq'
  have hrow (y : V) : |laceSum q x y - laceSum q' x y| ≤
      ∑' n : ℕ, |(laceCoefficient q n x y).toReal -
        (laceCoefficient q' n x y).toReal| := by
    have hnorm : Summable (fun n : ℕ =>
        ‖(-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal -
          (-1 : ℝ) ^ n * (laceCoefficient q' n x y).toReal‖) := by
      simpa only [← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, Real.norm_eq_abs, Prod.swap_prod_mk] using hd.prod_symm.prod_factor y
    rw [laceSum, laceSum, ← (summable_signed_laceCoefficient q x y hq).tsum_sub
      (summable_signed_laceCoefficient q' x y hq')]
    simpa only [← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  calc
    _ ≤ ∑' y, ∑' n : ℕ, |(laceCoefficient q n x y).toReal -
        (laceCoefficient q' n x y).toReal| :=
      (hd.prod_symm.prod.of_nonneg_of_le (fun _ => abs_nonneg _) hrow).tsum_le_tsum
        hrow hd.prod_symm.prod
    _ = _ := hd.tsum_comm

/-- All orders and endpoints of the actual coefficients converge jointly in
`ℓ¹` from below under the upper-profile diagram criterion. -/
theorem tendsto_tsum_abs_laceCoefficient_sub_Iic_of_diagram_bounds [Countable V]
    (q₀ : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤)
    (hfin : ∀ a : V, ∀ᵐ ω ∂law q₀, (cluster ω a).Finite) :
    Tendsto (fun q : Sym2 V → unitInterval => ∑' n : ℕ, ∑' y : V,
      |(laceCoefficient q n x y).toReal - (laceCoefficient q₀ n x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 0) := by
  have hz := tendsto_tsum_abs_piZero_sub_Iic q₀ x
    (ne_top_of_le_ne_top hinitial (tsum_piZero_le_diagramInitial q₀ x))
  have hp := tendsto_tsum_abs_laceCoefficient_succ_sub_Iic_of_diagram_bounds
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial hfin
  have hmass := tsum_laceCoefficient_all_mass_ne_top_of_diagram
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial
  apply (show Tendsto (fun q : Sym2 V → unitInterval =>
      (∑' y, |(piZero q x y).toReal - (piZero q₀ x y).toReal|) +
        ∑' n : ℕ, ∑' y, |(laceCoefficient q (n + 1) x y).toReal -
          (laceCoefficient q₀ (n + 1) x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 0) from by simpa only [add_zero] using hz.add hp).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hd := summable_abs_laceCoefficient_sub q q₀ x
    (tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds
      hq x ρ κ hρone hκfinite hρ hκ hinitial) hmass
  exact hd.prod.tsum_eq_zero_add.symm

/-- Every bounded real endpoint weight has a continuous all-order coefficient
moment from smaller profiles. The comparison constant is the weight bound itself. -/
theorem continuousWithinAt_tsum_mul_laceCoefficient_toReal_Iic_of_diagram_bounds
    [Countable V] (q₀ : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤)
    (hfin : ∀ a : V, ∀ᵐ ω ∂law q₀, (cluster ω a).Finite)
    (w : V → ℝ) (C : ℝ) (hw : ∀ y, |w y| ≤ C) :
    ContinuousWithinAt (fun q : Sym2 V → unitInterval =>
      ∑' n : ℕ, ∑' y, w y * (laceCoefficient q n x y).toReal) (Iic q₀) q₀ := by
  have hlim := (tendsto_tsum_abs_laceCoefficient_sub_Iic_of_diagram_bounds
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial hfin).const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [mul_zero] using hlim)
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hmass := tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds
    hq x ρ κ hρone hκfinite hρ hκ hinitial
  have hmass₀ := tsum_laceCoefficient_all_mass_ne_top_of_diagram
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial
  have hs (r : Sym2 V → unitInterval)
      (hr : (∑' n : ℕ, ∑' y, laceCoefficient r n x y) ≠ ⊤) :
      Summable (fun p : ℕ × V => w p.2 * (laceCoefficient r p.1 x p.2).toReal) := by
    apply ((summable_laceCoefficient_toReal r x hr).norm.mul_left C).of_norm_bounded
    intro p
    rw [norm_mul, Real.norm_eq_abs (w p.2)]
    exact mul_le_mul_of_nonneg_right (hw p.2) (norm_nonneg _)
  have hd := summable_abs_laceCoefficient_sub q q₀ x hmass hmass₀
  rw [← (hs q hmass).tsum_prod, ← (hs q₀ hmass₀).tsum_prod,
    ← (hs q hmass).tsum_sub (hs q₀ hmass₀)]
  calc
    _ ≤ ∑' p : ℕ × V, ‖w p.2 * (laceCoefficient q p.1 x p.2).toReal -
        w p.2 * (laceCoefficient q₀ p.1 x p.2).toReal‖ :=
      norm_tsum_le_tsum_norm ((hs q hmass).sub (hs q₀ hmass₀)).norm
    _ ≤ ∑' p : ℕ × V, C * |(laceCoefficient q p.1 x p.2).toReal -
        (laceCoefficient q₀ p.1 x p.2).toReal| := by
      apply Summable.tsum_le_tsum _ ((hs q hmass).sub (hs q₀ hmass₀)).norm
        (hd.mul_left C)
      intro p
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hw p.2) (abs_nonneg _)
    _ = _ := by rw [tsum_mul_left, hd.tsum_prod]

/-- The actual signed lace kernel is spatially `ℓ¹` continuous from below.
No susceptibility assumption is added to the coefficient continuity criterion. -/
theorem tendsto_tsum_abs_laceSum_sub_Iic_of_diagram_bounds [Countable V]
    (q₀ : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤)
    (hfin : ∀ a : V, ∀ᵐ ω ∂law q₀, (cluster ω a).Finite) :
    Tendsto (fun q : Sym2 V → unitInterval =>
      ∑' y : V, |laceSum q x y - laceSum q₀ x y|) (𝓝[Iic q₀] q₀) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => tsum_nonneg fun _ => abs_nonneg _) ?_
    (tendsto_tsum_abs_laceCoefficient_sub_Iic_of_diagram_bounds
      q₀ x ρ κ hρone hκfinite hρ hκ hinitial hfin)
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact tsum_abs_laceSum_sub_le q q₀ x
    (tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds
      hq x ρ κ hρone hκfinite hρ hκ hinitial)
    (tsum_laceCoefficient_all_mass_ne_top_of_diagram
      q₀ x ρ κ hρone hκfinite hρ hκ hinitial)

/-- The signed total lace correction is continuous from smaller profiles. -/
theorem continuousWithinAt_tsum_laceSum_Iic_of_diagram_bounds [Countable V]
    (q₀ : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤)
    (hfin : ∀ a : V, ∀ᵐ ω ∂law q₀, (cluster ω a).Finite) :
    ContinuousWithinAt (fun q : Sym2 V → unitInterval => ∑' y, laceSum q x y)
      (Iic q₀) q₀ := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_tsum_abs_laceSum_sub_Iic_of_diagram_bounds
      q₀ x ρ κ hρone hκfinite hρ hκ hinitial hfin)
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hs := summable_laceSum q x
    (tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds
      hq x ρ κ hρone hκfinite hρ hκ hinitial)
  have hs₀ := summable_laceSum_of_diagram_bounds
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial
  rw [← hs.tsum_sub hs₀]
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hs.sub hs₀).norm

/-- The norm of every character-transform difference is bounded by the actual
spatial `ℓ¹` distance, with a bound independent of the character. -/
theorem norm_laceSum_character_sub_le [AddCommGroup V]
    (q q' : Sym2 V → unitInterval) (x : V)
    (hq : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤)
    (hq' : (∑' n : ℕ, ∑' y, laceCoefficient q' n x y) ≠ ⊤)
    (ψ : AddChar V Circle) :
    ‖(∑' y, (laceSum q x y : ℂ) * (ψ y : ℂ)) -
      ∑' y, (laceSum q' x y : ℂ) * (ψ y : ℂ)‖ ≤
        ∑' y, |laceSum q x y - laceSum q' x y| := by
  have hs := summable_ofReal_mul_addChar (summable_laceSum q x hq) ψ
  have hs' := summable_ofReal_mul_addChar (summable_laceSum q' x hq') ψ
  rw [← hs.tsum_sub hs']
  simpa only [← sub_mul, ← Complex.ofReal_sub, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hs.sub hs').norm

/-- The actual Fourier correction converges uniformly over all unitary
characters under the same upper-profile diagram and cluster hypotheses. -/
theorem tendstoUniformly_laceSum_character_Iic_of_diagram_bounds
    [Countable V] [AddCommGroup V]
    (q₀ : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤)
    (hfin : ∀ a : V, ∀ᵐ ω ∂law q₀, (cluster ω a).Finite) :
    TendstoUniformly (fun (q : Sym2 V → unitInterval) (ψ : AddChar V Circle) =>
      ∑' y, (laceSum q x y : ℂ) * (ψ y : ℂ))
      (fun ψ => ∑' y, (laceSum q₀ x y : ℂ) * (ψ y : ℂ)) (𝓝[Iic q₀] q₀) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim := tendsto_tsum_abs_laceSum_sub_Iic_of_diagram_bounds
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial hfin
  have hsmall := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hεq
  intro ψ
  rw [dist_comm, dist_eq_norm]
  exact (norm_laceSum_character_sub_le q q₀ x
    (tsum_laceCoefficient_all_mass_ne_top_of_le_diagram_bounds
      hq x ρ κ hρone hκfinite hρ hκ hinitial)
    (tsum_laceCoefficient_all_mass_ne_top_of_diagram
      q₀ x ρ κ hρone hκfinite hρ hκ hinitial) ψ).trans_lt hεq

end PercLib.Percolation.Bond.Lace
