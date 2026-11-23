/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Models.LongRange.CornerDerivative.Defs
public import PercLib.Models.LongRange.RestorationDerivativeGeneral
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The derivative's right-limit and right-continuity at a cutoff corner

The right-hand derivative of the uncapped toReal root moment has a right-hand closed-ball pivotal
flux limit at every positive integer radius. A local-window mean-value argument converts that
limit into a right derivative when the moment itself is right-continuous; the continuity input is
made explicit, not smuggled into a universal differentiability hypothesis at other integer radii.

A corrected-value derivative via `Function.update` is distinguished from differentiability of the
uncorrected root moment. The correction is vacuous exactly where right-continuity holds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-!
## Proofs

The derivative of the real uncapped moment on the corner-free window `(n, n+1)` is the strict
pivotal flux; its right limit at the natural scale `n` is the closed-ball pivotal flux; and
Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv` turns that pair into a right derivative as soon
as the moment itself is right-continuous at `n`.
-/


/-! ### Bridge lemmas: the named definitions are the landed raw expressions -/

theorem fluxOpen_eq_raw {d : ℕ} (α : ℝ) {β : ℝ≥0} (p : ℕ) (r : ℝ) :
    fluxOpen d α β p r = ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)) := rfl

theorem fluxClosedAt_eq_raw {d : ℕ} (α : ℝ) {β : ℝ≥0} (p : ℕ) (n : ℝ) :
    fluxClosedAt d α β p n = ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s ≤ n then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * n ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) n e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) n) β)) := rfl

/-! ### The derivative on a corner-free window is the strict pivotal flux -/

/-- **The derivative of the real uncapped moment is the strict-ball pivotal flux** on the
corner-free window `(n, n+1)` above a positive integer scale. This is the landed corner-free
derivative rewritten through the named definitions, and it is the exact function whose right limit
at `n` is taken below. Only the window is needed: the derivative formula is not available at the
next corner `n + 1`. -/
theorem deriv_momToReal_eventuallyEq_fluxOpen {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    deriv (momToReal d α β p) =ᶠ[𝓝[>] (n : ℝ)] (fun r => fluxOpen d α β p r) := by
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcorner : ∀ k : ℕ, (k : ℝ) ∉ Ioo (n : ℝ) ((n : ℝ) + 1) := by
    intro k hk
    have h1 : (n : ℝ) < (k : ℝ) := hk.1
    have h2 : (k : ℝ) < (n : ℝ) + 1 := hk.2
    have hk1 : n < k := by exact_mod_cast h1
    have hk2 : k < n + 1 := by exact_mod_cast h2
    omega
  have hwin : Ioo (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) := by
    have h1 : Ioi (n : ℝ) ∈ 𝓝[>] (n : ℝ) := self_mem_nhdsWithin
    have h2 : Iio ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (n : ℝ) < (n : ℝ) + 1 by linarith))
    exact inter_mem h1 h2
  filter_upwards [hwin] with r hr
  have h := hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval (d := d) hd hα hβ p hp
    (u := (n : ℝ)) (v := (n : ℝ) + 1) (r₀ := r) hnn (by linarith) hcorner hr
  refine (h.deriv).trans ?_
  simp only [fluxOpen_eq_raw]

/-! ### The unconditional right limit of the derivative at a natural scale -/

/-- **The derivative of the real uncapped moment has a right limit at every positive integer
scale, and that limit is the closed-ball pivotal flux.**

No continuity of the moment at `n` is assumed: this says that the corner defect sits in the
*value* of the moment and not in the slope. It is the landed closed-ball right flux limit composed
with the corner-free derivative identity on the window `(n, n+1)`. -/
theorem tendsto_deriv_momToReal_nhdsGT_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (deriv (momToReal d α β p)) (𝓝[>] (n : ℝ))
      (𝓝 (fluxClosedAt d α β p (n : ℝ))) := by
  have hflux := tendsto_tsum_cutoffKernel_powerLaw_pivotal_flux_nhdsGT_nat (d := d) hd hα hβ hp hn
  have hmain : Tendsto (fun r => fluxOpen d α β p r) (𝓝[>] (n : ℝ))
      (𝓝 (fluxClosedAt d α β p (n : ℝ))) := by
    rw [fluxClosedAt_eq_raw]
    simpa only [fluxOpen_eq_raw] using hflux
  exact hmain.congr' (deriv_momToReal_eventuallyEq_fluxOpen hd hα hβ hp hn).symm

/-! ### Right derivative at `n` from right continuity of the value -/

/-- **The right derivative of the real uncapped moment at a positive integer scale**, from
right-continuity of the moment at that scale.

Everything else is discharged from landed results: differentiability on the window `(n, n+1)` is
the corner-free binomial derivative `hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval`,
and the right limit of the derivative is `tendsto_deriv_momToReal_nhdsGT_nat`, whose value is the
closed-ball pivotal flux. The mean-value step is Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv`
applied with `s = Ioo (n) (n+1)`.

Right-continuity of the moment is the single remaining input. It is not proved here, and no
statement is made about the left derivative, the two-sided derivative, or parameters outside
`β M < 1`. -/
theorem hasDerivWithinAt_momToReal_of_continuousWithinAt {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n)
    (hcont : ContinuousWithinAt (momToReal d α β p) (Ici (n : ℝ)) (n : ℝ)) :
    HasDerivWithinAt (momToReal d α β p) (fluxClosedAt d α β p (n : ℝ))
      (Ici (n : ℝ)) (n : ℝ) := by
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcorner : ∀ k : ℕ, (k : ℝ) ∉ Ioo (n : ℝ) ((n : ℝ) + 1) := by
    intro k hk
    have h1 : (n : ℝ) < (k : ℝ) := hk.1
    have h2 : (k : ℝ) < (n : ℝ) + 1 := hk.2
    have hk1 : n < k := by exact_mod_cast h1
    have hk2 : k < n + 1 := by exact_mod_cast h2
    omega
  have hwin : Ioo (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) := by
    have h1 : Ioi (n : ℝ) ∈ 𝓝[>] (n : ℝ) := self_mem_nhdsWithin
    have h2 : Iio ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (n : ℝ) < (n : ℝ) + 1 by linarith))
    exact inter_mem h1 h2
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo (n : ℝ) ((n : ℝ) + 1)) ?_ ?_ hwin
    (tendsto_deriv_momToReal_nhdsGT_nat hd hα hβ hp hn)
  · intro r hr
    exact (hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval (d := d) hd hα hβ p hp
      (u := (n : ℝ)) (v := (n : ℝ) + 1) (r₀ := r) hnn (by linarith) hcorner hr)
      |>.differentiableAt.differentiableWithinAt
  · exact hcont.mono (fun y hy => le_of_lt hy.1)

/-- **Right differentiability of the moment at a natural scale is exactly its right continuity.**

Forward: differentiability within a set implies continuity within it. Backward: the assembly
`hasDerivWithinAt_momToReal_of_continuousWithinAt`. So any failure of the right derivative at a
natural scale is a jump of the moment's *value* at that scale and nothing else, and the value the
right derivative takes when it exists is the closed-ball pivotal flux. -/
theorem hasDerivWithinAt_momToReal_iff_continuousWithinAt {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivWithinAt (momToReal d α β p) (fluxClosedAt d α β p (n : ℝ))
        (Ici (n : ℝ)) (n : ℝ) ↔
      ContinuousWithinAt (momToReal d α β p) (Ici (n : ℝ)) (n : ℝ) :=
  ⟨fun h => h.continuousWithinAt,
    fun h => hasDerivWithinAt_momToReal_of_continuousWithinAt hd hα hβ hp hn h⟩

/-! ### Finiteness, monotonicity, and the exact size of the corner defect -/

/-- The named real moment is the `toReal` of the landed `rootMoment`. -/
theorem momToReal_eq_rootMoment_toReal {d : ℕ} (α : ℝ) {β : ℝ≥0} (p : ℕ) (r : ℝ) :
    momToReal d α β p r =
      (PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) (0 : Fin d → ℤ) p).toReal := rfl

/-- **The real moment is finite on any bounded window inside the high-temperature regime**, from
the landed uniform `(p+1)`-st root moment bound and the domination of the `p`-th root moment by the
`(p+1)`-st. This is the `ENNReal`-to-`ℝ` finiteness bridge: it is what lets `toReal` be taken
without discarding an infinite value. -/
theorem lintegral_moment_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} {u R : ℝ} (hu : 0 < u) (hR : 0 < R) {r : ℝ} (hr : r ∈ Ioo u R) :
    (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β))) ≠ ⊤ := by
  obtain ⟨M, hM, hroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := u) (v := R) (R := R) hu hR
  refine ne_top_of_le_ne_top hM
    (le_trans (rootMoment_le_of_le _ (0 : Fin d → ℤ) (Nat.le_succ p)) ?_)
  simpa only [PercLib.Percolation.Bond.rootMoment, ModelNorm.toSeminorm_ofNorm] using
    hroot r (Or.inl hr)

/-- **The extended moment is monotone in the cut-off scale**, in the exact `∫⁻` form of the
named real moment (the landed `rootMoment` form does not unfold definitionally here). -/
theorem lintegral_moment_mono {d : ℕ} {α : ℝ} {β : ℝ≥0} {r ρ : ℝ} (hrρ : r ≤ ρ) (p : ℕ)
    (hK : AntitoneOn (powerLawProfile 1 ((d : ℝ) + α)) (Ioi 0)) :
    (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) ≤
      ∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) := by
  set N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ) with hN
  have h := lintegral_cutoffKernel_mono (d := d) (K := powerLawProfile 1 ((d : ℝ) + α))
    (N := N) (β := β) hK hrρ
    (φ := fun ω => ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)
    ((measurable_encard_cluster_toENNReal (0 : Fin d → ℤ)).pow_const p) ?_
  · simpa only [hN, ModelNorm.toSeminorm_ofNorm] using h
  · intro ω ω' hω
    exact pow_le_pow_left' (by simpa using encard_le_encard (cluster_mono hω (0 : Fin d → ℤ))) p

/-- **The real uncapped moment is monotone in the cut-off scale** on any bounded window inside the
high-temperature regime: increasing the scale adds edges, hence increases the cluster. -/
theorem momToReal_monotoneOn {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    MonotoneOn (momToReal d α β p) (Ioo u R) := by
  set N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ) with hN
  have hK : AntitoneOn (powerLawProfile 1 ((d : ℝ) + α)) (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) zero_le_one (by positivity)
  have hstep : ∀ x ∈ Ioo u R, ∀ y ∈ Ioo u R, x ≤ y →
      momToReal d α β p x ≤ momToReal d α β p y := by
    intro x hx y hy hxy
    refine ENNReal.toReal_mono (lintegral_moment_ne_top hd hα hβ hu hR hy) ?_
    exact lintegral_moment_mono hxy p hK
  intro x hx y hy hxy
  exact hstep x hx y hy hxy

/-- **The right limit of the real moment exists** and is the infimum of its values to the right of
`n`: the moment is monotone in the scale and bounded below by `0`. -/
theorem momToReal_tendsto_nhdsGT_sInf {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (momToReal d α β p) (𝓝[>] (n : ℝ))
      (𝓝 (sInf (momToReal d α β p '' Ioo (n : ℝ) ((n : ℝ) + 1)))) := by
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmono : MonotoneOn (momToReal d α β p) (Ioo (n : ℝ) ((n : ℝ) + 1)) :=
    (momToReal_monotoneOn hd hα hβ (p := p) (u := (n : ℝ) / 2) (R := 2 * (n : ℝ) + 1)
      (by linarith) (by linarith)).mono
      (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  refine MonotoneOn.tendsto_nhdsWithin_Ioo_right
    ⟨(n : ℝ) + 1 / 2, by constructor <;> linarith⟩ hmono ?_
  exact ⟨0, by rintro _ ⟨r, -, rfl⟩; exact ENNReal.toReal_nonneg⟩

/-- **The corner defect is exactly the gap between the value at `n` and the right limit.** The
moment is right-continuous at the natural scale `n` if and only if its value there is the infimum
of its values immediately to the right. Combined with
`hasDerivWithinAt_momToReal_iff_continuousWithinAt` this says the failure of the right derivative at
`n` is a jump of height `sInf … - ψ n ≥ 0` and nothing else. -/
theorem momToReal_continuousWithinAt_iff {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} {n : ℕ} (hn : 1 ≤ n) :
    ContinuousWithinAt (momToReal d α β p) (Ici (n : ℝ)) (n : ℝ) ↔
      momToReal d α β p (n : ℝ) =
        sInf (momToReal d α β p '' Ioo (n : ℝ) ((n : ℝ) + 1)) := by
  have hlim := momToReal_tendsto_nhdsGT_sInf (p := p) hd hα hβ hn
  constructor
  · intro hcont
    have h1 : Tendsto (momToReal d α β p) (𝓝[>] (n : ℝ)) (𝓝 (momToReal d α β p (n : ℝ))) := by
      have := hcont.mono Ioi_subset_Ici_self
      simpa only [ContinuousWithinAt] using this
    exact tendsto_nhds_unique h1 hlim
  · intro hval
    have h1 : Tendsto (momToReal d α β p) (𝓝[>] (n : ℝ)) (𝓝 (momToReal d α β p (n : ℝ))) := by
      rw [hval]; exact hlim
    have h2 : ContinuousWithinAt (momToReal d α β p) (Ioi (n : ℝ)) (n : ℝ) := by
      simpa only [ContinuousWithinAt] using h1
    have hunion : (Ici (n : ℝ)) = insert (n : ℝ) (Ioi (n : ℝ)) := by
      ext x
      simp only [mem_Ici, mem_insert_iff, mem_Ioi]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        exacts [Or.inr h', Or.inl h'.symm]
      · rintro (h' | h')
        exacts [le_of_eq h'.symm, le_of_lt h']
    rw [hunion]
    simpa only [Set.insert_eq] using continuousWithinAt_singleton.union h2

/-! ### The unconditional right derivative after correcting the value at `n` -/

/-- **The right derivative of any function that agrees with the moment on the window and has its
value corrected to the right limit.** This is the assembly of
`hasDerivWithinAt_Ici_of_tendsto_deriv` with the unconditional right limit of the derivative,
packaged so that the value at `n` is free. -/
theorem hasDerivWithinAt_of_deriv_eventuallyEq_fluxOpen {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℝ}
    (hg_cont : ContinuousWithinAt g (Ioo (n : ℝ) ((n : ℝ) + 1)) (n : ℝ))
    (hg_diff : DifferentiableOn ℝ g (Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hg_deriv : deriv g =ᶠ[𝓝[>] (n : ℝ)] (fun r => fluxOpen d α β p r)) :
    HasDerivWithinAt g (fluxClosedAt d α β p (n : ℝ)) (Ici (n : ℝ)) (n : ℝ) := by
  have hwin : Ioo (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) := by
    have h1 : Ioi (n : ℝ) ∈ 𝓝[>] (n : ℝ) := self_mem_nhdsWithin
    have h2 : Iio ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (n : ℝ) < (n : ℝ) + 1 by linarith))
    exact inter_mem h1 h2
  have hlim : Tendsto (deriv g) (𝓝[>] (n : ℝ)) (𝓝 (fluxClosedAt d α β p (n : ℝ))) :=
    (tendsto_deriv_momToReal_nhdsGT_nat hd hα hβ hp hn).congr'
      ((deriv_momToReal_eventuallyEq_fluxOpen hd hα hβ hp hn).trans hg_deriv.symm)
  exact hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo (n : ℝ) ((n : ℝ) + 1))
    hg_diff hg_cont hwin hlim

/-- **The right derivative of the moment at a natural scale, with the value at `n` corrected to
the right limit.** Unconditional: the correction is the infimum of the values immediately to the
right, which exists because the moment is monotone in the scale and bounded below. By
`momToReal_continuousWithinAt_iff` the correction is vacuous exactly when the moment is
right-continuous at `n`, and then this is the right derivative of the moment itself. -/
theorem hasDerivWithinAt_update_momToReal {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivWithinAt (Function.update (momToReal d α β p) (n : ℝ)
      (sInf (momToReal d α β p '' Ioo (n : ℝ) ((n : ℝ) + 1))))
      (fluxClosedAt d α β p (n : ℝ)) (Ici (n : ℝ)) (n : ℝ) := by
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcorner : ∀ k : ℕ, (k : ℝ) ∉ Ioo (n : ℝ) ((n : ℝ) + 1) := by
    intro k hk
    have h1 : (n : ℝ) < (k : ℝ) := hk.1
    have h2 : (k : ℝ) < (n : ℝ) + 1 := hk.2
    have hk1 : n < k := by exact_mod_cast h1
    have hk2 : k < n + 1 := by exact_mod_cast h2
    omega
  set ψ : ℝ → ℝ := momToReal d α β p with hψ
  set c : ℝ := sInf (ψ '' Ioo (n : ℝ) ((n : ℝ) + 1)) with hc
  set g : ℝ → ℝ := Function.update ψ (n : ℝ) c with hg
  have hev_of_ne : ∀ y : ℝ, y ≠ (n : ℝ) → g y = ψ y := by
    intro y hy
    simp only [hg, Function.update_apply, hy, ite_false]
  have hge : g =ᶠ[𝓝[>] (n : ℝ)] ψ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hev_of_ne y (ne_of_gt hy)
  have hgn : g (n : ℝ) = c := by
    simp only [hg, Function.update_apply, ↓reduceIte]
  have hlimψ : Tendsto ψ (𝓝[>] (n : ℝ)) (𝓝 c) := by
    have h := momToReal_tendsto_nhdsGT_sInf (p := p) hd hα hβ hn
    rw [hc, hψ]
    exact h
  have hg_cont : ContinuousWithinAt g (Ioi (n : ℝ)) (n : ℝ) := by
    have h1 : Tendsto g (𝓝[>] (n : ℝ)) (𝓝 c) := hlimψ.congr' hge.symm
    simpa only [ContinuousWithinAt, hgn] using h1
  have hg_cont' : ContinuousWithinAt g (Ioo (n : ℝ) ((n : ℝ) + 1)) (n : ℝ) :=
    hg_cont.mono (fun y hy => hy.1)
  have hnear : ∀ r : ℝ, r ≠ (n : ℝ) → g =ᶠ[𝓝 r] ψ := by
    intro r hr
    filter_upwards [isOpen_ne.mem_nhds hr] with y hy
    exact hev_of_ne y hy
  have hg_has : ∀ r ∈ Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt g (fluxOpen d α β p r) r := by
    intro r hr
    exact (hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval (d := d) hd hα hβ p hp
      (u := (n : ℝ)) (v := (n : ℝ) + 1) (r₀ := r) hnn (by linarith) hcorner hr)
      |>.congr_of_eventuallyEq (by rw [hg, hψ]; exact hnear r (ne_of_gt hr.1))
  have hg_diff : DifferentiableOn ℝ g (Ioo (n : ℝ) ((n : ℝ) + 1)) :=
    fun r hr => (hg_has r hr).differentiableAt.differentiableWithinAt
  have hg_deriv : deriv g =ᶠ[𝓝[>] (n : ℝ)] (fun r => fluxOpen d α β p r) := by
    have hwin : Ioo (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) := by
      have h1 : Ioi (n : ℝ) ∈ 𝓝[>] (n : ℝ) := self_mem_nhdsWithin
      have h2 : Iio ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (show (n : ℝ) < (n : ℝ) + 1 by linarith))
      exact inter_mem h1 h2
    filter_upwards [hwin] with r hr
    exact (hg_has r hr).deriv
  exact hasDerivWithinAt_of_deriv_eventuallyEq_fluxOpen hd hα hβ hp hn hg_cont' hg_diff hg_deriv

end PercLib.Models.LongRange
