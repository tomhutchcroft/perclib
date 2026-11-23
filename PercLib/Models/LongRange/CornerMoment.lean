/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Adapted from the uncommitted, project-generated PercLib candidates `M1/Defs.lean` and
`M1/Main.lean`, under the same Apache 2.0 licence. The duplicate moment abbreviations from
that candidate have been removed in favour of `PercLib.Percolation.Bond.rootMoment` and the
existing root-zero `momToReal`.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 and the proof of Lemma I.4.1. The result here is one-sided at an integer
corner and belongs to the explicit high-temperature regime; it is not a two-sided derivative
at such a corner or a statement for every intensity below the critical one.
-/
module

public import PercLib.Models.LongRange.CornerMoment.Defs
public import PercLib.Models.LongRange.CornerContinuity
public import PercLib.Models.LongRange.CornerDerivative

/-!
# Right-continuity and the right derivative at an integer cutoff corner

The actual uncapped `p`-th root moment is right-continuous at every positive integer cutoff
radius, in the explicit high-temperature power-law regime `β M < 1`. The general theorem uses
`PercLib.Percolation.Bond.rootMoment` at the cutoff bond law, not duplicate moment definitions.

## Main results

* `rootMomentReal_le_soften`: the softened-union estimate in the real form used below, with
  `chiFactor` separated from the reopening probability.
* `tendsto_softenProb`: the reopening probability tends to zero from the right.
* `continuousWithinAt_rootMomentReal`: abstract right-continuity for an antitone profile under
  a finite higher-moment bound on the stated corner window.
* `continuousWithinAt_rootMomentReal_powerLaw_nat`: the concrete power-law form at an arbitrary
  root vertex, with all finiteness inputs discharged.
* `continuousWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat`: the expanded raw
  integral form of that continuity statement.
* `hasDerivWithinAt_rootMomentReal_powerLaw_nat`: for `p ≥ 1` and `n ≥ 1`, the uncorrected
  `momToReal` has right derivative `fluxClosedAt d α β p (n : ℝ)` within `Ici (n : ℝ)`.
* `hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat`: the same derivative for
  the expanded raw cutoff integral, with no convenience moment definition.

No left derivative or two-sided derivative is claimed at an integer corner.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open PercLib.Models.LongRange
open scoped ENNReal NNReal unitInterval Topology

namespace PercLib.Models.LongRange.CornerMoment

variable {d : ℕ}

/-! ### The softened-union estimate in real form -/

/-- For `n ≤ r < n+1`, the real cutoff `p`-th moment at scale `r` is at most its value at `n`,
plus `B^p` times the change term and `B⁻¹` times the `(p+1)`-st moment at scale `r`. -/
theorem rootMomentReal_le_soften {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {n : ℕ}
    {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {ρ : unitInterval}
    (hρ : (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
    (o : Fin d → ℤ) (p : ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hχ : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o ≠ ⊤)
    (hn_fin : PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β)) o p ≠ ⊤)
    (hr_fin : PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o (p + 1) ≠ ⊤) :
    (PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o p).toReal ≤
      (PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K
          (n : ℝ)) β)) o p).toReal +
        (B : ℝ) ^ p * ((ρ : ℝ) * chiFactor (d := d) β K n o) +
        (B : ℝ)⁻¹ *
          (PercLib.Percolation.Bond.rootMoment
            (law (intensityProfile
              (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o (p + 1)).toReal := by
  have H := moment_le_soften (K := K) (β := β) (n := n) (r := r) hK hnr hrn hρ o p
    hB hχ hn_fin hr_fin
  have hmid : ((↑(unitInterval.toNNReal ρ) : ℝ≥0∞) *
      (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) *
        chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o).toReal =
      (ρ : ℝ) * chiFactor (d := d) β K n o := by
    have hρcoe : ((↑(unitInterval.toNNReal ρ) : ℝ≥0∞)).toReal = (ρ : ℝ) := rfl
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hρcoe,
      chiFactor_def]
    ring
  simp only [PercLib.Percolation.Bond.rootMoment]
  simpa only [hmid] using H

/-! ### One-sided continuity of the reopening probability -/

/-- The reopening probability tends to zero from the right at a point of one-sided continuity
of the profile. -/
theorem tendsto_softenProb {K : ℝ → ℝ} {β : ℝ≥0} {n : ℕ}
    (hKc : ContinuousWithinAt K (Ici (n : ℝ)) (n : ℝ)) :
    Tendsto (fun r : ℝ => 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
      (𝓝[Ici (n : ℝ)] (n : ℝ)) (𝓝 0) := by
  have h1 : Tendsto K (𝓝[Ici (n : ℝ)] (n : ℝ)) (𝓝 (K (n : ℝ))) := hKc
  have h2 : Tendsto (fun r : ℝ => K (n : ℝ) - K r) (𝓝[Ici (n : ℝ)] (n : ℝ))
      (𝓝 (K (n : ℝ) - K (n : ℝ))) := tendsto_const_nhds.sub h1
  have h3 : Tendsto (fun r : ℝ => -(β : ℝ) * (K (n : ℝ) - K r)) (𝓝[Ici (n : ℝ)] (n : ℝ))
      (𝓝 (-(β : ℝ) * (K (n : ℝ) - K (n : ℝ)))) := tendsto_const_nhds.mul h2
  have h4 : Tendsto (fun r : ℝ => Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
      (𝓝[Ici (n : ℝ)] (n : ℝ))
      (𝓝 (Real.exp (-(β : ℝ) * (K (n : ℝ) - K (n : ℝ))))) :=
    (Real.continuous_exp.tendsto _).comp h3
  simpa using (tendsto_const_nhds.sub h4 : Tendsto
    (fun r : ℝ => 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
      (𝓝[Ici (n : ℝ)] (n : ℝ))
      (𝓝 (1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K (n : ℝ))))))

/-- The reopening probability is a genuine `unitInterval`-valued probability when `r ≥ n` and
`K` is antitone on `(0,∞)`. -/
theorem exists_softenProb_unitInterval {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0}
    {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hrn : (n : ℝ) ≤ r) :
    ∃ ρ : unitInterval, (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)) := by
  have hn0r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hKr : K r ≤ K (n : ℝ) :=
    hK (by rw [mem_Ioi]; exact hn0r) (by rw [mem_Ioi]; linarith) hrn
  have harg : -(β : ℝ) * (K (n : ℝ) - K r) ≤ 0 := by
    have hb0 : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
    nlinarith
  have hexp : Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)) ≤ 1 := Real.exp_le_one_iff.2 harg
  have hpos : 0 < Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)) := Real.exp_pos _
  exact ⟨⟨1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)), ⟨by linarith, by linarith⟩⟩, rfl⟩

/-! ### Abstract right-continuity at a positive integer -/

/-- The real uncapped canonical root moment is right-continuous at a positive integer when the
profile is antitone and one-sided continuous there and one constant dominates the `(p+1)`-st root
moment on `(n - 1/2, n+1) ∪ {n}`. The truncation `B` is chosen per error tolerance. -/
theorem continuousWithinAt_rootMomentReal {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0}
    {n : ℕ} (hn : 1 ≤ n) (hKc : ContinuousWithinAt K (Ici (n : ℝ)) (n : ℝ))
    (o : Fin d → ℤ) (p : ℕ)
    {M : ℝ≥0∞} (hMtop : M ≠ ⊤)
    (hM : ∀ r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ),
      PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o (p + 1) ≤ M) :
    ContinuousWithinAt (fun r : ℝ => (PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o p).toReal)
      (Ici (n : ℝ)) (n : ℝ) := by
  classical
  have hwin : ∀ r : ℝ, (n : ℝ) ≤ r → r < (n : ℝ) + 1 →
      r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ) := by
    intro r h1 h2
    exact Or.inl ⟨by linarith, by linarith⟩
  have hnwin : (n : ℝ) ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ) :=
    hwin _ le_rfl (by linarith)
  have htop_succ : ∀ r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ),
      PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o (p + 1) ≠ ⊤ :=
    fun r hr => ne_top_of_le_ne_top hMtop (hM r hr)
  have htop_p : ∀ r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ),
      PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o p ≠ ⊤ :=
    fun r hr => ne_top_of_le_ne_top (htop_succ r hr)
      (rootMoment_mono_pow o (Nat.le_succ p) r)
  have hchi : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o
      ≠ ⊤ := by
    have hEq : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o =
        PercLib.Percolation.Bond.rootMoment
          (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β)) o 1 := by
      simp only [chi, PercLib.Percolation.Bond.rootMoment, pow_one]
    rw [hEq]
    exact ne_top_of_le_ne_top (htop_succ _ hnwin)
      (rootMoment_mono_pow o (by omega) (n : ℝ))
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨B, hB1, hBeps⟩ : ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ)⁻¹ * M.toReal < ε / 2 := by
    obtain ⟨B, hB⟩ := exists_nat_gt (M.toReal / (ε / 2))
    have hM0 : (0 : ℝ) ≤ M.toReal := ENNReal.toReal_nonneg
    have hBpos : (0 : ℝ) < (B : ℝ) := lt_of_le_of_lt (div_nonneg hM0 hε2.le) hB
    have hB1 : 1 ≤ B := by exact_mod_cast hBpos
    refine ⟨B, hB1, ?_⟩
    have hlt : M.toReal < (B : ℝ) * (ε / 2) := by
      have h := mul_lt_mul_of_pos_right hB hε2
      rwa [div_mul_cancel₀ _ hε2.ne'] at h
    calc (B : ℝ)⁻¹ * M.toReal < (B : ℝ)⁻¹ * ((B : ℝ) * (ε / 2)) :=
          mul_lt_mul_of_pos_left hlt (by positivity)
      _ = ε / 2 := by field_simp
  have hprob := tendsto_softenProb (β := β) (n := n) hKc
  have hsmall : ∀ᶠ r in 𝓝[Ici (n : ℝ)] (n : ℝ), (B : ℝ) ^ p *
      ((1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r))) *
        chiFactor (d := d) β K n o) < ε / 2 := by
    have h0 : Tendsto (fun r : ℝ => (B : ℝ) ^ p *
        ((1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r))) * chiFactor (d := d) β K n o))
        (𝓝[Ici (n : ℝ)] (n : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ =>
          (1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r))) * chiFactor (d := d) β K n o)
          (𝓝[Ici (n : ℝ)] (n : ℝ)) (𝓝 0) := by
        simpa using hprob.mul_const (chiFactor (d := d) β K n o)
      simpa using h1.const_mul ((B : ℝ) ^ p)
    exact h0.eventually_lt_const hε2
  filter_upwards [hsmall, self_mem_nhdsWithin,
    (eventually_lt_nhds (show (n : ℝ) < (n : ℝ) + 1 by linarith)).filter_mono
      nhdsWithin_le_nhds] with r hsmall_r hrn hrn1
  obtain ⟨ρ, hρ⟩ := exists_softenProb_unitInterval hK hn hrn
  have hbound := rootMomentReal_le_soften (d := d) hK hrn hrn1 hρ o p hB1 hchi
    (htop_p _ hnwin) (htop_succ r (hwin r hrn hrn1))
  rw [hρ] at hbound
  have hMs : (PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o (p + 1)).toReal ≤
      M.toReal := ENNReal.toReal_mono hMtop (hM r (hwin r hrn hrn1))
  have hinv_nonneg : (0 : ℝ) ≤ (B : ℝ)⁻¹ := by positivity
  have hlow : (PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β)) o p).toReal ≤
      (PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o p).toReal :=
    ENNReal.toReal_mono (htop_p r (hwin r hrn hrn1)) (rootMoment_mono_radius hK hrn o p)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hbound, hsmall_r, hBeps, mul_le_mul_of_nonneg_left hMs hinv_nonneg]

/-! ### The concrete power law -/

/-- The real uncapped power-law cutoff root moment is right-continuous at every positive integer
radius in the high-temperature regime, at any root vertex. -/
theorem continuousWithinAt_rootMomentReal_powerLaw_nat {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    (o : Fin d → ℤ) (p : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ContinuousWithinAt (fun r : ℝ => (PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)) o p).toReal)
      (Ici (n : ℝ)) (n : ℝ) := by
  have hK : AntitoneOn (powerLawProfile 1 ((d : ℝ) + α)) (Ioi 0) :=
    antitoneOn_powerLawProfile zero_le_one (by positivity)
  have hKc : ContinuousAt (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    change ContinuousAt (fun s : ℝ => (1 : ℝ) * s ^ (-((d : ℝ) + α))) (n : ℝ)
    simpa using (Real.continuousAt_rpow_const (n : ℝ) (-((d : ℝ) + α)) (Or.inl hn0)).const_mul
      (1 : ℝ)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨M, hMtop, hM⟩ := exists_uniform_rootMoment_bound (d := d) hd hα hβ o p
    (u := (n : ℝ) - 1 / 2) (v := (n : ℝ) + 1) (R := (n : ℝ)) (by linarith) (by linarith)
  exact continuousWithinAt_rootMomentReal (d := d) hK hn hKc.continuousWithinAt o p hMtop hM

/-- The expanded raw integral version of right-continuity at a positive integer radius. -/
theorem continuousWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    (o : Fin d → ℤ) (p : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ContinuousWithinAt (fun r : ℝ =>
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) (Ici (n : ℝ)) (n : ℝ) := by
  exact continuousWithinAt_rootMomentReal_powerLaw_nat (d := d) hd hα hβ o p hn

/-- The uncorrected cutoff root moment has a right derivative at every positive integer radius.
The value is the closed-ball weighted pivotal flux. No two-sided derivative is claimed. -/
theorem hasDerivWithinAt_rootMomentReal_powerLaw_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivWithinAt (momToReal d α β p) (fluxClosedAt d α β p (n : ℝ))
      (Ici (n : ℝ)) (n : ℝ) := by
  exact hasDerivWithinAt_momToReal_of_continuousWithinAt hd hα hβ hp hn
    (continuousWithinAt_rootMomentReal_powerLaw_nat (d := d) hd hα hβ (0 : Fin d → ℤ) p hn)

/-- The uncorrected right derivative, with the moment written out as the raw cutoff integral
on the full infinite lattice. No duplicate moment definition or corrected value is used. -/
theorem hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat {d : ℕ}
    (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivWithinAt (fun r : ℝ =>
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal)
      (fluxClosedAt d α β p (n : ℝ)) (Ici (n : ℝ)) (n : ℝ) :=
  hasDerivWithinAt_rootMomentReal_powerLaw_nat hd hα hβ hp hn

end PercLib.Models.LongRange.CornerMoment
