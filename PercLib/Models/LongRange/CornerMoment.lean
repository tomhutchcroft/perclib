/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/

module

public import PercLib.Models.LongRange.CornerMoment.Defs
public import PercLib.Models.LongRange.CornerDerivative

/-!
# Right-continuity of the actual infinite-lattice cutoff root moment at an integer radius

The main results of this file:

* `rootMomentReal_le_soften` : the published softened-union estimate `moment_le_soften`, in the
  real form used below (change probability `ρ` and the susceptibility factor `chiFactor` separated
  out).
* `tendsto_softenProb` : the reopening probability `1 - exp (-(β (K n - K r)))` tends to `0` as
  `r ↓ n`, from one-sided continuity of the profile at the integer `n`.
* `continuousWithinAt_rootMomentReal` : **abstract right-continuity**. Given a profile `K`
  antitone on `(0,∞)`, continuous at the positive integer `n`, and a single finite constant `M`
  dominating the cutoff `(p+1)`-st moment on the whole window `(n - 1/2, n+1) ∪ {n}`, the real
  uncapped cutoff `p`-th root moment is right-continuous at `n` within `Ici n`. No
  differentiability and no two-sided statement.
* `continuousWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat` : the concrete power law
  `K s = s^{-(d+α)}` at `β M < 1`, with the finite constant `M` discharged by
  `exists_powerLaw_root_succ_moment_bound`.
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

/-- **The published softening estimate, packaged for the right limit.** For `n ≤ r < n+1` the
real cutoff `p`-th moment at scale `r` is at most the value at scale `n`, plus `B^p` times the
change term (reopening probability times the ball count `(2n+1)^d` times the scale-`n`
susceptibility) and `B⁻¹` times the `(p+1)`-st moment at scale `r`. -/
theorem rootMomentReal_le_soften {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {n : ℕ}
    {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {ρ : unitInterval}
    (hρ : (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
    (o : Fin d → ℤ) (p : ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hχ : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o ≠ ⊤)
    (hn_fin : rootMoment (d := d) β K o p (n : ℝ) ≠ ⊤)
    (hr_fin : rootMoment (d := d) β K o (p + 1) r ≠ ⊤) :
    rootMomentReal (d := d) β K o p r ≤
      rootMomentReal (d := d) β K o p (n : ℝ) +
        (B : ℝ) ^ p * ((ρ : ℝ) * chiFactor (d := d) β K n o) +
        (B : ℝ)⁻¹ * rootMomentReal (d := d) β K o (p + 1) r := by
  have H := moment_le_soften (K := K) (β := β) (n := n) (r := r) hK hnr hrn hρ o p hB hχ
    hn_fin hr_fin
  have hmid : ((↑(unitInterval.toNNReal ρ) : ℝ≥0∞) *
      (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) *
        chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o).toReal =
      (ρ : ℝ) * chiFactor (d := d) β K n o := by
    have hρcoe : ((↑(unitInterval.toNNReal ρ) : ℝ≥0∞)).toReal = (ρ : ℝ) := rfl
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hρcoe,
      chiFactor_def]
    ring
  simp only [rootMomentReal, rootMoment]
  simpa only [hmid] using H

/-! ### One-sided continuity of the reopening probability -/

/-- **The reopening probability tends to zero from the right.** Only one-sided continuity of `K`
at `n` is needed: then `r ↦ 1 - exp (-(β (K n - K r)))` tends to `0` as `r ↓ n`. -/
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

/-- The reopening probability is a legitimate `unitInterval`-valued probability when `r ≥ n` and
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

/-- **Right-continuity of the real uncapped cutoff root moment at a positive integer.**

The only inputs are: the profile is antitone on `(0,∞)`, it is continuous from the right at `n`,
and one finite
constant `M` dominates the cutoff `(p+1)`-st moment on the window `(n - 1/2, n+1) ∪ {n}`. The
truncation level `B` in the softening estimate is chosen per `ε`; it is *not* a hypothesis. -/
theorem continuousWithinAt_rootMomentReal {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0}
    {n : ℕ} (hn : 1 ≤ n) (hKc : ContinuousWithinAt K (Ici (n : ℝ)) (n : ℝ))
    (o : Fin d → ℤ) (p : ℕ)
    {M : ℝ≥0∞} (hMtop : M ≠ ⊤)
    (hM : ∀ r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ),
      rootMoment (d := d) β K o (p + 1) r ≤ M) :
    ContinuousWithinAt (rootMomentReal (d := d) β K o p) (Ici (n : ℝ)) (n : ℝ) := by
  classical
  -- the window of the uniform bound, as a predicate
  have hwin : ∀ r : ℝ, (n : ℝ) ≤ r → r < (n : ℝ) + 1 →
      r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ) := by
    intro r h1 h2
    exact Or.inl ⟨by linarith, by linarith⟩
  have hnwin : (n : ℝ) ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ) :=
    hwin _ le_rfl (by linarith)
  -- finiteness of the moments in the window
  have htop_succ : ∀ r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ),
      rootMoment (d := d) β K o (p + 1) r ≠ ⊤ :=
    fun r hr => ne_top_of_le_ne_top hMtop (hM r hr)
  have htop_p : ∀ r ∈ (Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1) ∪ {(n : ℝ)} : Set ℝ),
      rootMoment (d := d) β K o p r ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top (htop_succ r hr) (rootMoment_mono_pow o (Nat.le_succ p) r)
  -- the susceptibility at scale `n` is finite
  have hchi : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o
      ≠ ⊤ := by
    have hEq : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o =
        rootMoment (d := d) β K o 1 (n : ℝ) := by
      simp only [chi, rootMoment, pow_one]
    rw [hEq]
    exact ne_top_of_le_ne_top (htop_succ _ hnwin)
      (rootMoment_mono_pow o (by omega) (n : ℝ))
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- choose the truncation level `B` so that the `(p+1)`-st moment remainder is below `ε/2`
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
  -- the change term tends to zero
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
  -- the `(p+1)`-st moment is bounded by `M`
  have hMs : rootMomentReal (d := d) β K o (p + 1) r ≤ M.toReal :=
    ENNReal.toReal_mono hMtop (hM r (hwin r hrn hrn1))
  have hinv_nonneg : (0 : ℝ) ≤ (B : ℝ)⁻¹ := by positivity
  -- lower bound: monotonicity in the radius
  have hlow : rootMomentReal (d := d) β K o p (n : ℝ) ≤ rootMomentReal (d := d) β K o p r :=
    ENNReal.toReal_mono (htop_p r (hwin r hrn hrn1)) (rootMoment_mono_radius hK hrn o p)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hbound, hsmall_r, hBeps, mul_le_mul_of_nonneg_left hMs hinv_nonneg]

/-! ### The concrete power law -/

/-- **Right-continuity of the real uncapped cutoff root moment at a positive integer radius**,
for the power-law profile `K s = s^{-(d+α)}` in the high-temperature region `β M < 1`. -/
theorem continuousWithinAt_rootMomentReal_powerLaw_nat {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    (o : Fin d → ℤ) (p : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ContinuousWithinAt
      (rootMomentReal (d := d) β (powerLawProfile 1 ((d : ℝ) + α)) o p) (Ici (n : ℝ)) (n : ℝ) := by
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

/-- **Right-continuity at a positive integer radius of the actual infinite-lattice real uncapped
cutoff root moment.** The function
`r ↦ (∫⁻ ω, |K_o(ω)|^p ∂ law (cutoffKernel … r)).toReal` is continuous from the right at `n`
within `Ici n`; the statement writes the moment out. -/
theorem continuousWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    (o : Fin d → ℤ) (p : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ContinuousWithinAt (fun r : ℝ =>
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) (Ici (n : ℝ)) (n : ℝ) := by
  change ContinuousWithinAt
    (rootMomentReal (d := d) β (powerLawProfile 1 ((d : ℝ) + α)) o p) (Ici (n : ℝ)) (n : ℝ)
  exact continuousWithinAt_rootMomentReal_powerLaw_nat (d := d) hd hα hβ o p hn

/-- **The uncorrected cutoff root moment has a right derivative at every positive integer
radius.** This combines the right continuity proved above with the landed local-window mean-value
bridge. Its value is the closed-ball weighted pivotal flux. No two-sided derivative is claimed. -/
theorem hasDerivWithinAt_rootMomentReal_powerLaw_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivWithinAt
      (rootMomentReal (d := d) β (powerLawProfile 1 ((d : ℝ) + α)) (0 : Fin d → ℤ) p)
      (fluxClosedAt d α β p (n : ℝ)) (Ici (n : ℝ)) (n : ℝ) := by
  apply hasDerivWithinAt_momToReal_of_continuousWithinAt hd hα hβ hp hn
  have heq : momToReal d α β p =
      rootMomentReal (d := d) β (powerLawProfile 1 ((d : ℝ) + α)) (0 : Fin d → ℤ) p :=
    rfl
  rw [heq]
  exact continuousWithinAt_rootMomentReal_powerLaw_nat (d := d) hd hα hβ (0 : Fin d → ℤ) p hn

end PercLib.Models.LongRange.CornerMoment
