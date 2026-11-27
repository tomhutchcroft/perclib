/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.BoundaryRusso.ClusterDistribution
public import PercLib.Percolation.Bond.Lace.Bootstrap.ClusterMoments
public import PercLib.Percolation.Bond.TriangleClusterMoments
public import Mathlib.Analysis.MeanInequalities

/-!
# A triangle lower bound for expected boundary susceptibility

## Main results

The actual finite-cluster distribution has expected boundary susceptibility at least
`(chi - Delta)₊² / (3 * beta² * Delta²)` for a translation-invariant lattice intensity
with normalized rate rows and finite susceptibility. The pair and third moments are
proved from the percolation law, and Cauchy–Schwarz retains their coefficient three.
Almost sure cluster finiteness and all integrability follow from finite susceptibility.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

private theorem cluster_pair_sum_eq {V : Type*} (ω : Config V) (o : V)
    (C : Finset V) (hC : cluster ω o = (C : Set V)) (f : V → V → ℝ≥0∞) :
    (∑' a, ∑' b, (conn o a ∩ conn o b).indicator (fun _ => f a b) ω) =
      ∑ a ∈ C, ∑ b ∈ C, f a b := by
  classical
  have hc (a : V) : ω ∈ conn o a ↔ a ∈ C := by
    rw [← mem_cluster_iff, hC, Finset.mem_coe]
  rw [tsum_eq_sum (s := C) (fun a ha => by simp [Set.indicator, hc, ha])]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [tsum_eq_sum (s := C) (fun b hb => by simp [Set.indicator, hc, hb])]
  exact Finset.sum_congr rfl fun b hb => by simp [Set.indicator, hc, ha, hb]

private theorem cluster_triple_sum_eq {V : Type*} (ω : Config V) (o : V)
    (C : Finset V) (hC : cluster ω o = (C : Set V)) (f : V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, (conn o a ∩ (conn o b ∩ conn o c)).indicator
      (fun _ => f a b c) ω) = ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, f a b c := by
  classical
  have hc (a : V) : ω ∈ conn o a ↔ a ∈ C := by
    rw [← mem_cluster_iff, hC, Finset.mem_coe]
  rw [tsum_eq_sum (s := C) (fun a ha => by simp [Set.indicator, hc, ha])]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [tsum_eq_sum (s := C) (fun b hb => by simp [Set.indicator, hc, hb])]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [tsum_eq_sum (s := C) (fun c hc' => by simp [Set.indicator, hc, hc'])]
  exact Finset.sum_congr rfl fun c hc' => by simp [Set.indicator, hc, ha, hb, hc']

private theorem ofReal_cluster_pair_sum {V : Type*} (q : Sym2 V → unitInterval)
    (C : Finset V) :
    ENNReal.ofReal (∑ a ∈ C, ∑ b ∈ C, (tau q a b).toReal) =
      ∑ a ∈ C, ∑ b ∈ C, tau q a b := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  exact Finset.sum_congr rfl fun b _ => ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q a b))

private theorem ofReal_cluster_triple_sum {V : Type*} (q : Sym2 V → unitInterval)
    (C : Finset V) :
    ENNReal.ofReal (∑ a ∈ C, (∑ b ∈ C, (tau q a b).toReal) ^ 2) =
      ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, tau q a b * tau q a c := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_pow (Finset.sum_nonneg fun _ _ => by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  simp_rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q a _))]
  rw [pow_two, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]

private theorem cluster_distribution_pair_bound {d : ℕ}
    (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ x y g : Fin d → ℤ, q s(x + g, y + g) = q s(x, y))
    (hchi : chi q 0 ≠ ⊤) :
    (∑' C : Finset (Fin d → ℤ), law q {ω | cluster ω 0 = (C : Set (Fin d → ℤ))} *
      ENNReal.ofReal (∑ a ∈ C, ∑ b ∈ C, (tau q a b).toReal)) ≤
        chi q 0 * ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0 := by
  classical
  rw [← lintegral_finite_cluster_functional_eq_tsum]
  calc
    _ = ∫⁻ ω, ∑' a, ∑' b,
        (conn 0 a ∩ conn 0 b).indicator (fun _ => tau q a b) ω ∂law q := by
      apply lintegral_congr_ae
      filter_upwards [ae_cluster_finite_of_chi_lt_top hchi.lt_top] with ω hω
      rw [dite_eq_left hω, ofReal_cluster_pair_sum,
        cluster_pair_sum_eq ω 0 hω.toFinset hω.coe_toFinset.symm]
    _ ≤ _ := lintegral_cluster_pair_tau_le_chi_mul q 0 _ fun z =>
      (diagonal_triangle_eq_rooted q hq z).le

private theorem cluster_distribution_triple_bound {d : ℕ}
    (q : Sym2 (Fin d → ℤ) → unitInterval)
    (hq : ∀ x y g : Fin d → ℤ, q s(x + g, y + g) = q s(x, y))
    (hchi : chi q 0 ≠ ⊤) :
    (∑' C : Finset (Fin d → ℤ), law q {ω | cluster ω 0 = (C : Set (Fin d → ℤ))} *
      ENNReal.ofReal (∑ a ∈ C, (∑ b ∈ C, (tau q a b).toReal) ^ 2)) ≤
        3 * chi q 0 * (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ^ 2 := by
  classical
  rw [← lintegral_finite_cluster_functional_eq_tsum]
  calc
    _ = ∫⁻ ω, ∑' a, ∑' b, ∑' c,
        (conn 0 a ∩ (conn 0 b ∩ conn 0 c)).indicator
          (fun _ => tau q a b * tau q a c) ω ∂law q := by
      apply lintegral_congr_ae
      filter_upwards [ae_cluster_finite_of_chi_lt_top hchi.lt_top] with ω hω
      rw [dite_eq_left hω, ofReal_cluster_triple_sum,
        cluster_triple_sum_eq ω 0 hω.toFinset hω.coe_toFinset.symm]
    _ ≤ _ := lintegral_cluster_triple_tau_le_three_chi_triangle_sq q hq hchi

private theorem boundary_card_le_pair_add_sqrt {V : Type*} [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (o : V) (hconst : ∀ u, chi (intensityProfile J β) u = chi (intensityProfile J β) o)
    (hchi : chi (intensityProfile J β) o ≠ ⊤) (C : Finset V) :
    (chi (intensityProfile J β) o).toReal * C.card ≤
      (∑ a ∈ C, ∑ b ∈ C, (tau (intensityProfile J β) a b).toReal) +
      (β : ℝ) * Real.sqrt (chi (intensityProfile J β) o).toReal *
        Real.sqrt (∑ a ∈ C, (∑ b ∈ C, (tau (intensityProfile J β) a b).toReal) ^ 2) *
        Real.sqrt (boundarySusceptibility J β C) := by
  classical
  let : Nonempty V := ⟨o⟩
  let q := intensityProfile J β
  let χ := (chi q o).toReal
  let U := ∑ a ∈ C, ∑ b ∈ C, (tau q a b).toReal
  let Q := ∑ a ∈ C, (∑ b ∈ C, (tau q a b).toReal) ^ 2
  have hc (u : V) : chi q u = chi q o := hconst u
  have hiSup : (⨆ u, chi q u) = chi q o := by simp only [hc, iSup_const]
  have hiInf : (⨅ u, chi q u) = chi q o := by simp only [hc, iInf_const]
  have hχ : 0 < χ := lt_of_lt_of_le zero_lt_one (by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hchi (one_le_chi q o))
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hPhi := boundarySusceptibility_nonneg J β C
  have hdet := boundary_susceptibility_bound J β C hrow (by rwa [hiSup])
  have hmain := hdet.2.trans hdet.1
  rw [hiSup, hiInf] at hmain
  change (max (χ * C.card - U) 0) ^ 2 / ((β : ℝ) ^ 2 * χ * Q) ≤
    boundarySusceptibility J β C at hmain
  by_cases hC : C.Nonempty
  · obtain ⟨a, ha⟩ := hC
    have hrowone : (1 : ℝ) ≤ ∑ b ∈ C, (tau q a b).toReal := by
      simpa only [tau_self, ENNReal.toReal_one] using
        Finset.single_le_sum (f := fun b => (tau q a b).toReal)
          (fun b _ => ENNReal.toReal_nonneg) ha
    have hQ : 0 < Q := lt_of_lt_of_le (by nlinarith : (0 : ℝ) <
      (∑ b ∈ C, (tau q a b).toReal) ^ 2)
      (Finset.single_le_sum (f := fun b => (∑ c ∈ C, (tau q b c).toReal) ^ 2)
        (fun b _ => sq_nonneg _) ha)
    have hs := (div_le_iff₀ (by positivity : 0 < (β : ℝ) ^ 2 * χ * Q)).mp hmain
    have hsqχ := Real.sq_sqrt hχ.le
    have hsqQ := Real.sq_sqrt hQ.le
    have hsqPhi := Real.sq_sqrt hPhi
    have hm : max (χ * C.card - U) 0 ≤
        (β : ℝ) * Real.sqrt χ * Real.sqrt Q * Real.sqrt (boundarySusceptibility J β C) := by
      apply (sq_le_sq₀ (le_max_right _ _) (by positivity)).mp
      calc
        _ ≤ boundarySusceptibility J β C * ((β : ℝ) ^ 2 * χ * Q) := hs
        _ = _ := by
          simp only [mul_pow, hsqχ, hsqQ, hsqPhi]
          ring
    change χ * C.card ≤ U + _
    calc
      χ * C.card ≤ U + max (χ * C.card - U) 0 := by
        linarith [le_max_left (χ * C.card - U) 0]
      _ ≤ _ := add_le_add le_rfl hm
  · have hCempty := Finset.not_nonempty_iff_eq_empty.mp hC
    simp [hCempty]

/-- The actual finite-cluster expectation of boundary susceptibility has the triangle
lower bound, including intensity zero. The rate-row normalization is the only size
assumption on the intensity kernel. -/
theorem tsum_law_cluster_eq_mul_boundarySusceptibility_ge_triangle {d : ℕ}
    (J : Sym2 (Fin d → ℤ) → ℝ≥0) (β : ℝ≥0)
    (hJ : ∀ x y g : Fin d → ℤ, J s(x + g, y + g) = J s(x, y))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    let q := intensityProfile J β
    let χ := (chi q 0).toReal
    let Δ := (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0).toReal
    (max (χ - Δ) 0) ^ 2 / (3 * (β : ℝ) ^ 2 * Δ ^ 2) ≤
      ∑' C : Finset (Fin d → ℤ), (law q).real {ω | cluster ω 0 = (C : Set (Fin d → ℤ))} *
        boundarySusceptibility J β C := by
  classical
  let q := intensityProfile J β
  let X := chi q 0
  let D := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
  let χ := X.toReal
  let Δ := D.toReal
  let P := fun C : Finset (Fin d → ℤ) => law q {ω | cluster ω 0 = (C : Set (Fin d → ℤ))}
  let U := fun C : Finset (Fin d → ℤ) => ∑ a ∈ C, ∑ b ∈ C, (tau q a b).toReal
  let Q := fun C : Finset (Fin d → ℤ) => ∑ a ∈ C, (∑ b ∈ C, (tau q a b).toReal) ^ 2
  let F := fun C : Finset (Fin d → ℤ) => boundarySusceptibility J β C
  change (max (χ - Δ) 0) ^ 2 / (3 * (β : ℝ) ^ 2 * Δ ^ 2) ≤
    ∑' C, (P C).toReal * F C
  have hP (C) : 0 ≤ (P C).toReal := ENNReal.toReal_nonneg
  have hU (C) : 0 ≤ U C := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hQ (C) : 0 ≤ Q C := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF (C) : 0 ≤ F C := boundarySusceptibility_nonneg J β C
  by_cases hβ : (β : ℝ) = 0
  · simp only [hβ, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, div_zero]
    exact tsum_nonneg fun C => mul_nonneg (hP C) (hF C)
  have hβpos : 0 < (β : ℝ) := lt_of_le_of_ne β.coe_nonneg (Ne.symm hβ)
  have hq (x y g : Fin d → ℤ) : q s(x + g, y + g) = q s(x, y) := by
    apply Subtype.ext
    simp only [q, intensityProfile, hJ]
  have hconst (u : Fin d → ℤ) : chi q u = X := by
    change chi q u = chi q 0
    rw [chi_eq_tsum_tau, chi_eq_tsum_tau]
    rw [← (Equiv.addRight u).tsum_eq]
    apply tsum_congr
    intro v
    change tau q u (v + u) = tau q 0 v
    rw [tau_eq_rooted_of_add_right q hq u (v + u), add_sub_cancel_right]
  have hsup : (⨆ u, chi q u) = X := by simp only [hconst, iSup_const]
  have hDle : D ≤ X * X := by
    calc
      _ ≤ ∑' u, ∑' v, tau q 0 u * tau q u v := by
        exact ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v =>
          mul_le_of_le_one_right' (tau_le_one q v 0)
      _ = X * X := by
        simp_rw [ENNReal.tsum_mul_left, ← chi_eq_tsum_tau, hconst]
        rw [ENNReal.tsum_mul_right, ← chi_eq_tsum_tau]
  have hD : D ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hchi hchi) hDle
  have hD1 : (1 : ℝ≥0∞) ≤ D := by
    calc
      1 = tau q 0 0 * tau q 0 0 * tau q 0 0 := by rw [tau_self]; norm_num
      _ ≤ ∑' v, tau q 0 0 * tau q 0 v * tau q v 0 :=
        ENNReal.le_tsum (f := fun v => tau q 0 0 * tau q 0 v * tau q v 0) 0
      _ ≤ D := ENNReal.le_tsum (f := fun u =>
        ∑' v, tau q 0 u * tau q u v * tau q v 0) 0
  have hΔ : 0 < Δ := lt_of_lt_of_le zero_lt_one (by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hD hD1)
  have hχ : 0 < χ := lt_of_lt_of_le zero_lt_one (by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hchi (one_le_chi q 0))
  have hpair : (∑' C, P C * ENNReal.ofReal (U C)) ≤ X * D :=
    cluster_distribution_pair_bound q hq hchi
  have htriple : (∑' C, P C * ENNReal.ofReal (Q C)) ≤ 3 * X * D ^ 2 :=
    cluster_distribution_triple_bound q hq hchi
  have hboundary : (∑' C, P C * ENNReal.ofReal (F C)) ≤ X * X := by
    have h := tsum_law_cluster_eq_mul_ofReal_boundarySusceptibility_le
      J β 0 1 hrow (by change (⨆ u, chi q u) ≠ ⊤; rwa [hsup])
    change (∑' C, P C * ENNReal.ofReal (F C)) ≤ 1 * (⨆ u, chi q u) * X at h
    simpa only [hsup, one_mul] using h
  have hNsum : (∑' C, P C * C.card) = X := tsum_law_cluster_eq_mul_card_eq_chi q 0 hchi
  have hPUfin := ne_top_of_le_ne_top (ENNReal.mul_ne_top hchi hD) hpair
  have hPQfin := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hchi) (ENNReal.pow_ne_top hD)) htriple
  have hPFfin := ne_top_of_le_ne_top (ENNReal.mul_ne_top hchi hchi) hboundary
  have hPNfin : (∑' C, P C * C.card) ≠ ⊤ := by rwa [hNsum]
  have hPU : Summable fun C => (P C).toReal * U C := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hU] using
      ENNReal.summable_toReal hPUfin
  have hPQ : Summable fun C => (P C).toReal * Q C := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hQ] using
      ENNReal.summable_toReal hPQfin
  have hPF : Summable fun C => (P C).toReal * F C := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hF] using
      ENNReal.summable_toReal hPFfin
  have hPN : Summable fun C => (P C).toReal * (C.card : ℝ) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using
      ENNReal.summable_toReal hPNfin
  have hN : (∑' C, (P C).toReal * (C.card : ℝ)) = χ := by
    have h := congrArg ENNReal.toReal hNsum
    simpa only [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hPNfin),
      ENNReal.toReal_mul, ENNReal.toReal_natCast] using h
  have hEU : (∑' C, (P C).toReal * U C) ≤ χ * Δ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hchi hD) hpair
    simpa only [ENNReal.toReal_mul,
      ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hPUfin),
      ENNReal.toReal_ofReal (hU _)] using h
  have hEQ : (∑' C, (P C).toReal * Q C) ≤ 3 * χ * Δ ^ 2 := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hchi) (ENNReal.pow_ne_top hD)) htriple
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow,
      ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hPQfin),
      ENNReal.toReal_ofReal (hQ _)] at h
    exact h
  let f := fun C => Real.sqrt ((P C).toReal * Q C)
  let g := fun C => Real.sqrt ((P C).toReal * F C)
  have hf2 (C) : f C ^ (2 : ℝ) = (P C).toReal * Q C := by
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hP C) (hQ C))]
  have hg2 (C) : g C ^ (2 : ℝ) = (P C).toReal * F C := by
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hP C) (hF C))]
  have hcs := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (f := f) (g := g)
    (fun C => Real.sqrt_nonneg _) (fun C => Real.sqrt_nonneg _)
    (by simpa only [hf2] using hPQ) (by simpa only [hg2] using hPF)
  have hfg (C) : f C * g C =
      (P C).toReal * (Real.sqrt (Q C) * Real.sqrt (F C)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hP C), Real.sqrt_mul (hP C)]
    calc
      _ = (Real.sqrt (P C).toReal) ^ 2 *
          (Real.sqrt (Q C) * Real.sqrt (F C)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hP C)]
  have hCS : (∑' C, f C * g C) ≤
      Real.sqrt (∑' C, (P C).toReal * Q C) *
        Real.sqrt (∑' C, (P C).toReal * F C) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [hf2, hg2] using hcs.2
  have hpoint (C) : χ * ((P C).toReal * (C.card : ℝ)) ≤
      (P C).toReal * U C + (β : ℝ) * Real.sqrt χ * (f C * g C) := by
    have h := mul_le_mul_of_nonneg_left
      (boundary_card_le_pair_add_sqrt J β hβpos hrow 0 hconst hchi C) (hP C)
    rw [hfg]
    convert h using 1 <;> ring
  have hsum : χ * χ ≤ (∑' C, (P C).toReal * U C) +
      (β : ℝ) * Real.sqrt χ * (∑' C, f C * g C) := by
    have h := Summable.tsum_le_tsum hpoint (hPN.mul_left χ)
      (hPU.add (hcs.1.mul_left ((β : ℝ) * Real.sqrt χ)))
    simpa only [hPU.tsum_add (hcs.1.mul_left ((β : ℝ) * Real.sqrt χ)),
      tsum_mul_left, hN] using h
  have hfinal : χ * χ ≤ χ * Δ + (β : ℝ) * Real.sqrt χ *
      (Real.sqrt (3 * χ * Δ ^ 2) * Real.sqrt (∑' C, (P C).toReal * F C)) := by
    refine hsum.trans (add_le_add hEU (mul_le_mul_of_nonneg_left
      (hCS.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hEQ)
        (Real.sqrt_nonneg _))) (by positivity)))
  have hmass : 0 ≤ ∑' C, (P C).toReal * F C :=
    tsum_nonneg fun C => mul_nonneg (hP C) (hF C)
  apply (div_le_iff₀ (by positivity : 0 < 3 * (β : ℝ) ^ 2 * Δ ^ 2)).mpr
  by_cases hdiff : χ ≤ Δ
  · rw [max_eq_right (sub_nonpos.mpr hdiff), zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hdiff' : 0 ≤ χ - Δ := sub_nonneg.mpr (le_of_not_ge hdiff)
  rw [max_eq_left hdiff']
  have hs : χ * (χ - Δ) ≤ (β : ℝ) * Real.sqrt χ *
      (Real.sqrt (3 * χ * Δ ^ 2) * Real.sqrt (∑' C, (P C).toReal * F C)) := by
    nlinarith [hfinal]
  have hs2 := pow_le_pow_left₀ (mul_nonneg hχ.le hdiff') hs 2
  have hrootX := Real.sq_sqrt hχ.le
  have hrootD := Real.sq_sqrt (show 0 ≤ 3 * χ * Δ ^ 2 by positivity)
  have hrootF := Real.sq_sqrt hmass
  have heq : ((β : ℝ) * Real.sqrt χ *
      (Real.sqrt (3 * χ * Δ ^ 2) * Real.sqrt (∑' C, (P C).toReal * F C))) ^ 2 =
      χ ^ 2 * ((∑' C, (P C).toReal * F C) * (3 * (β : ℝ) ^ 2 * Δ ^ 2)) := by
    simp only [mul_pow, hrootX, hrootD, hrootF]
    ring
  rw [heq, mul_pow] at hs2
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hχ)).mp hs2

open Classical in
/-- The same lower bound for the actual random-cluster boundary functional, assigning
zero on infinite clusters. Finite susceptibility already makes that exceptional event null. -/
theorem integral_boundarySusceptibility_ge_triangle {d : ℕ}
    (J : Sym2 (Fin d → ℤ) → ℝ≥0) (β : ℝ≥0)
    (hJ : ∀ x y g : Fin d → ℤ, J s(x + g, y + g) = J s(x, y))
    (hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    let q := intensityProfile J β
    let χ := (chi q 0).toReal
    let Δ := (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0).toReal
    (max (χ - Δ) 0) ^ 2 / (3 * (β : ℝ) ^ 2 * Δ ^ 2) ≤
      ∫ ω, (if h : (cluster ω 0).Finite then boundarySusceptibility J β h.toFinset else 0)
        ∂law q := by
  dsimp only
  rw [integral_finite_cluster_functional_eq_tsum _ _ _
    (fun C => boundarySusceptibility_nonneg J β C)]
  exact tsum_law_cluster_eq_mul_boundarySusceptibility_ge_triangle J β hJ hrow hchi

end PercLib.Percolation.Bond.Lace
