/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original continuity consequences of the canonical independent-layer events
and their proved common diagram envelopes; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Events.LayerContinuity
public import PercLib.Percolation.Bond.Lace.Diagrams.Tuple.Bounds
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Joint continuity of the positive lace coefficient masses

## Main results

Under almost sure finiteness of the upper-profile root clusters and actual
contracting diagram bounds, the positive canonical coefficients are jointly
continuous in order and endpoint in the real `ℓ¹` distance, from smaller profiles.

The proof first applies dominated convergence to the actual weighted tuple
probabilities on the dependent joint index. Both nonnegative tuple terms are
bounded by the same upper-profile envelope, so their absolute difference is
bounded by that envelope itself. Summing over tuples then bounds the coefficient
distance. No coefficient continuity or limit-sum interchange is assumed.
Order zero is not part of the statement.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

/-- The real weighted summand of a fixed ordered coefficient tuple is
continuous from below when its incoming upper-profile root clusters are
almost surely finite. -/
theorem continuousWithinAt_weighted_coefficientEvent_Iic
    (q₀ : Sym2 V → unitInterval) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V)
    (hfin : ∀ i : Fin (n + 2), ∀ᵐ ω ∂law q₀,
      (cluster ω (Fin.cases x (fun j => (b j).2) i)).Finite) :
    ContinuousWithinAt (fun q : Sym2 V → unitInterval =>
      ((∏ i, offDiagonal (fun u v : V =>
        (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (b i).1 (b i).2) *
        (Measure.pi (fun _ : Fin (n + 2) => law q))
          (coefficientEvent x y b)).toReal) (Iic q₀) q₀ := by
  classical
  have hW : Continuous (fun q : Sym2 V → unitInterval =>
      ∏ i, (offDiagonal (fun u v : V =>
        (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (b i).1 (b i).2).toReal) := by
    apply continuous_finsetProd
    intro i _
    by_cases hi : (b i).2 = (b i).1
    · simp only [offDiagonal, ite_eq_left hi, ENNReal.toReal_zero]
      exact continuous_const
    · simp only [offDiagonal, ite_eq_right hi, ENNReal.coe_toReal,
        unitInterval.coe_toNNReal]
      fun_prop
  have hP := continuousWithinAt_pi_law_coefficientEvent_Iic q₀ x y b hfin
  have hPr : ContinuousWithinAt (fun q : Sym2 V → unitInterval =>
      ((Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b)).toReal)
      (Iic q₀) q₀ :=
    (ENNReal.continuousAt_toReal (measure_ne_top _ _)).comp_continuousWithinAt
      (f := fun q : Sym2 V → unitInterval =>
        (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b)) hP
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_prod, Pi.mul_def] using
    hW.continuousWithinAt.mul hPr

/-- Almost surely finite upper-profile clusters and contracting actual diagram
norms give joint `ℓ¹` continuity of all positive orders and endpoints. -/
theorem tendsto_tsum_abs_laceCoefficient_succ_sub_Iic_of_diagram_bounds
    (q₀ : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q₀ p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q₀ p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q₀ x p) ≠ ⊤)
    (hfin : ∀ a : V, ∀ᵐ ω ∂law q₀, (cluster ω a).Finite) :
    Tendsto (fun q : Sym2 V → unitInterval => ∑' n : ℕ, ∑' y : V,
      |(laceCoefficient q (n + 1) x y).toReal -
        (laceCoefficient q₀ (n + 1) x y).toReal|)
      (𝓝[Iic q₀] q₀) (𝓝 0) := by
  classical
  let T := Σ n : ℕ, (Fin (n + 1) → V × V) × V
  let a (q : Sym2 V → unitInterval) (p : T) : ℝ :=
    ((∏ i, offDiagonal (fun u v : V =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (p.2.1 i).1 (p.2.1 i).2) *
      (Measure.pi (fun _ : Fin (p.1 + 2) => law q))
        (coefficientEvent x p.2.2 p.2.1)).toReal
  let F (p : T) : ℝ := (coefficientTupleDiagram q₀ x p.2.2 p.2.1).toReal
  have hFsum : Summable F :=
    summable_coefficientTupleDiagram_toReal q₀ x ρ κ hρone hκfinite hρ hκ hinitial
  have hFmass := tsum_coefficientTupleDiagram_mass_ne_top
    q₀ x ρ κ hρone hκfinite hρ hκ hinitial
  have hFfinite (p : T) : coefficientTupleDiagram q₀ x p.2.2 p.2.1 ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top
      (ENNReal.ne_top_of_tsum_ne_top (ENNReal.ne_top_of_tsum_ne_top hFmass p.1) p.2.1) p.2.2
  have ha_nonneg (q : Sym2 V → unitInterval) (p : T) : 0 ≤ a q p :=
    ENNReal.toReal_nonneg
  have ha_le (q : Sym2 V → unitInterval) (hq : q ≤ q₀) (p : T) : a q p ≤ F p :=
    ENNReal.toReal_mono (hFfinite p)
      (weighted_coefficientEvent_probability_le_upper_coefficientTupleDiagram hq x p.2.2 p.2.1)
  have ha_sum (q : Sym2 V → unitInterval) (hq : q ≤ q₀) : Summable (a q) :=
    hFsum.of_nonneg_of_le (ha_nonneg q) (ha_le q hq)
  have hd_le (q : Sym2 V → unitInterval) (hq : q ≤ q₀) (p : T) :
      |a q p - a q₀ p| ≤ F p := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [ha_nonneg q p, ha_nonneg q₀ p, ha_le q hq p, ha_le q₀ le_rfl p]
  have hd_sum (q : Sym2 V → unitInterval) (hq : q ≤ q₀) :
      Summable (fun p : T => |a q p - a q₀ p|) :=
    hFsum.of_nonneg_of_le (fun _ => abs_nonneg _) (hd_le q hq)
  have hpoint (p : T) : Tendsto (fun q : Sym2 V → unitInterval => |a q p - a q₀ p|)
      (𝓝[Iic q₀] q₀) (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun q : Sym2 V → unitInterval => a q p)
        (𝓝[Iic q₀] q₀) (𝓝 (a q₀ p)) :=
      continuousWithinAt_weighted_coefficientEvent_Iic q₀ x p.2.2 p.2.1
        (fun i => hfin (Fin.cases x (fun j => (p.2.1 j).2) i))
    simpa only [sub_self, abs_zero] using (ht.sub_const (a q₀ p)).abs
  have htuple : Tendsto (fun q : Sym2 V → unitInterval => ∑' p : T, |a q p - a q₀ p|)
      (𝓝[Iic q₀] q₀) (𝓝 (0 : ℝ)) := by
    have hbound : ∀ᶠ q in 𝓝[Iic q₀] q₀, ∀ p : T, ‖|a q p - a q₀ p|‖ ≤ F p := by
      filter_upwards [self_mem_nhdsWithin] with q hq p
      simpa only [Real.norm_eq_abs, abs_abs] using hd_le q hq p
    simpa only [tsum_zero] using
      (tendsto_tsum_of_dominated_convergence (g := fun _ : T => (0 : ℝ))
        hFsum hpoint hbound)
  have hcoef (q : Sym2 V → unitInterval) (hq : q ≤ q₀) (n : ℕ) (y : V) :
      (laceCoefficient q (n + 1) x y).toReal =
        ∑' b : Fin (n + 1) → V × V, a q ⟨n, (b, y)⟩ := by
    apply ENNReal.tsum_toReal_eq
    intro b
    exact ne_top_of_le_ne_top (hFfinite ⟨n, (b, y)⟩)
      (weighted_coefficientEvent_probability_le_upper_coefficientTupleDiagram hq x y b)
  have hcompare (q : Sym2 V → unitInterval) (hq : q ≤ q₀) :
      (∑' n : ℕ, ∑' y : V, |(laceCoefficient q (n + 1) x y).toReal -
        (laceCoefficient q₀ (n + 1) x y).toReal|) ≤ ∑' p : T, |a q p - a q₀ p| := by
    let d (p : T) : ℝ := |a q p - a q₀ p|
    have hd : Summable d := hd_sum q hq
    have hrow (n : ℕ) (y : V) :
        |(laceCoefficient q (n + 1) x y).toReal -
          (laceCoefficient q₀ (n + 1) x y).toReal| ≤
          ∑' b : Fin (n + 1) → V × V, d ⟨n, (b, y)⟩ := by
      have haq : Summable (fun b : Fin (n + 1) → V × V => a q ⟨n, (b, y)⟩) := by
        simpa only [Prod.swap_prod_mk] using
          ((ha_sum q hq).sigma_factor n).prod_symm.prod_factor y
      have haq₀ : Summable (fun b : Fin (n + 1) → V × V => a q₀ ⟨n, (b, y)⟩) := by
        simpa only [Prod.swap_prod_mk] using
          ((ha_sum q₀ le_rfl).sigma_factor n).prod_symm.prod_factor y
      have hnorm : Summable (fun b : Fin (n + 1) → V × V =>
          ‖a q ⟨n, (b, y)⟩ - a q₀ ⟨n, (b, y)⟩‖) := by
        simpa only [Real.norm_eq_abs, Prod.swap_prod_mk, d] using
          (hd.sigma_factor n).prod_symm.prod_factor y
      rw [hcoef q hq n y, hcoef q₀ le_rfl n y, ← haq.tsum_sub haq₀]
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    have hinner (n : ℕ) :
        (∑' y : V, ∑' b : Fin (n + 1) → V × V, d ⟨n, (b, y)⟩) =
          ∑' p : (Fin (n + 1) → V × V) × V, d ⟨n, p⟩ :=
      (hd.sigma_factor n).tsum_comm.trans (hd.sigma_factor n).tsum_prod.symm
    have hright : Summable (fun n : ℕ =>
        ∑' y : V, ∑' b : Fin (n + 1) → V × V, d ⟨n, (b, y)⟩) :=
      hd.sigma.congr (fun n => (hinner n).symm)
    have hn (n : ℕ) :
        (∑' y : V, |(laceCoefficient q (n + 1) x y).toReal -
          (laceCoefficient q₀ (n + 1) x y).toReal|) ≤
          ∑' y : V, ∑' b : Fin (n + 1) → V × V, d ⟨n, (b, y)⟩ := by
      have hr := (hd.sigma_factor n).prod_symm.prod
      have hl := hr.of_nonneg_of_le (fun y => abs_nonneg _) (hrow n)
      exact hl.tsum_le_tsum (hrow n) hr
    have hleft := hright.of_nonneg_of_le
      (fun n => tsum_nonneg (fun y => abs_nonneg _)) hn
    calc
      _ ≤ ∑' n : ℕ, ∑' y : V, ∑' b : Fin (n + 1) → V × V, d ⟨n, (b, y)⟩ :=
        hleft.tsum_le_tsum hn hright
      _ = ∑' p : T, d p := by
        simp_rw [hinner]
        exact hd.tsum_sigma.symm
  apply squeeze_zero' (Eventually.of_forall (fun _ => tsum_nonneg (fun _ =>
    tsum_nonneg (fun _ => abs_nonneg _)))) ?_ htuple
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact hcompare q hq

end PercLib.Percolation.Bond.Lace
