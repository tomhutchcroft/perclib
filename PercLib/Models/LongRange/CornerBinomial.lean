/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Adapted from the uncommitted, project-generated candidates `I41AtCorner.lean` and
`I41FluxBinomial.lean`, under the same Apache 2.0 licence. Accepted source revision:
`I41FluxBinomial.lean`, at the uncommitted, project-generated revision validated in the project
journal. Its source digest is retained in the verification log and the integration commit message.
The final assembly with the already landed right derivative is new in this module.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1. The corner statement is the one-sided version in the explicit high-temperature
regime, not ordinary two-sided differentiation there or the full range of intensities.
-/
module

public import PercLib.Models.LongRange.CornerMoment
public import PercLib.Models.LongRange.CornerDerivative
public import PercLib.Models.LongRange.MassTransportI41
public import PercLib.Models.LongRange.TruncatedMoments
public import PercLib.Models.LongRange.HighTemperatureDerivative

/-!
# Lemma I.4.1 at the integer corner `n`: the pivot-flux value *is* the binomial value

The landed right derivative `hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat`
identifies the right derivative of the cutoff root moment at a positive integer radius `n` with
the closed-ball pivotal flux `fluxClosedAt d α β p (n : ℝ)`.  This file identifies that same
number with the paper's binomial right-hand side of Lemma I.4.1, under nothing but `d ≥ 1`,
`α > 0`, the explicit high-temperature condition `β M < 1`, `p ≥ 1` and `n ≥ 1`.  No derivative is
taken here and no two-sided claim is made: this is an identity of two values at the same scale and
the same law.

The chain is:

* `fluxClosedAt_eq_raw` (production) followed by
  `tsum_pivotal_eq_rate_mul_toReal_lintegral` (production), which moves the real series of
  per-pair pivotal expectations to `powerLawRate · (∫⁻ ω, ∑'_e …, ∂μ_n).toReal` by `lintegral_tsum`
  at `ℝ≥0∞` level — no summability of a real series is assumed anywhere;
* `i41_binomial_at_nat` (migrated below from the validated candidate `I41AtCorner.lean`), the
  `ℝ≥0∞` closed-ball identity at the corner itself;
* `i41_real_flux_closed_at_nat`, the `toReal` passage, in which a.e. finiteness of the ball
  clusters comes from the high-temperature root `(p+1)`-moment bound and the finiteness of every
  diagram term comes from the same bound.  Without it `ENNReal.toReal` would silently replace an
  infinite cluster by `0`.

The migrated block below (closed-ball selector, crossing identity, `i41_binomial_at_nat` and the
per-pair closed-coordinate transfer) is the validated `.ultramath/smwt35c3b/m1/I41AtCorner.lean`,
re-elaborated here so that this file is self-contained.

The last theorem,
`hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_paper_binomial_at_nat`, composes the two
components: the raw uncorrected root moment has the paper's binomial expression as its right
derivative at a positive integer radius. This remains a one-sided result.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### The closed-ball selector at a corner -/

/-- **The closed-ball selector needs no corner hypothesis.**  Off the diagonal the radial kernel of
the selector `1(s ≤ n)` is exactly the paper's closed-ball indicator `1(‖y - x‖ ≤ n)`.  This is the
point where the strict selector of the derivative needs `n ∉ (u, v)`; for the right-continuous
closed selector the reconciliation is unconditional. -/
theorem radialKernel_closedSel_eq_ball_of_ne_enn {N : Seminorm ℝ (Fin d → ℝ)} {n : ℝ}
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    ((radialKernel N (fun s => if s ≤ n then 1 else 0) s(x, y) : ℝ≥0) : ℝ≥0∞) =
      if N (Int.cast ∘ (y - x)) ≤ n then (1 : ℝ≥0∞) else 0 := by
  have hsub : N (Int.cast ∘ (x - y)) = N (Int.cast ∘ (y - x)) := by
    simp only [intCast_comp_sub, map_sub_rev N]
  rw [radialKernel_of_ne hxy, hsub]
  by_cases h : N (Int.cast ∘ (y - x)) ≤ n
  · simp [h]
  · simp [h]

/-- The closed-ball radial selector takes only the values `0` and `1`. -/
theorem radialKernel_closedSel_zero_or_one (N : Seminorm ℝ (Fin d → ℝ)) (n : ℝ)
    (e : Sym2 (Fin d → ℤ)) :
    (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) = 0 ∨
      (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) = 1 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      exact Or.inl (by simp)
    · rw [radialKernel_of_ne hxy]
      by_cases h : N (Int.cast ∘ (x - y)) ≤ n
      · right; simp [h]
      · left; simp [h]

open Classical in
/-- **The pivotal sum with the closed-ball selector is the ordered crossing sum.**

This is `tsum_radialKernel_pivotal_eq_tsum_ball` with the strict selector replaced by the
closed-ball selector and, consequently, with *no* corner-free hypothesis: the identity holds at
the integer radius `n` itself.  The diagonal needs no argument, because the factor `1(y ∉ K_o)`
already vanishes at `y = x ∈ K_o`. -/
theorem tsum_closedSel_pivotal_eq_tsum_ball {N : Seminorm ℝ (Fin d → ℝ)} {n : ℝ}
    (ω : Config (Fin d → ℤ)) (o : Fin d → ℤ) (p : ℕ) :
    (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
              ((cluster ω o).encard : ℝ≥0∞) ^ p))) =
      ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
        (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if N (Int.cast ∘ (y - x)) ≤ n then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p) := by
  classical
  rw [PercLib.Percolation.Bond.tsum_pivotal_eq_tsum_crossing (ω := ω) (o := o) (p := p)
    (radial := fun e => ((radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ≥0) : ℝ≥0∞))]
  refine tsum_congr fun x => tsum_congr fun y => ?_
  by_cases hxy : x = y
  · subst hxy
    rw [radialKernel_diag]
    simp only [ENNReal.coe_zero]
    by_cases hx : x ∈ cluster ω o
    · simp [hx]
    · simp [hx]
  · rw [radialKernel_closedSel_eq_ball_of_ne_enn hxy]

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open Classical in
/-- **Lemma I.4.1 at the integer corner.**  At the corner radius `n ∈ ℕ`, `n ≥ 1`, in the
high-temperature regime `β M < 1`, the pivotal sum with the **closed-ball** selector — the
right-continuous reading of the rate weight, carrying the whole sphere `‖e‖ = n` — equals the
paper's binomial right-hand side (I.4.1) with the closed ball `B_n` and with the *same* law
`μ_n`, i.e. with no differentiability in `r` anywhere.

Only the root `p`-th moment enters the binomial step, and it is discharged from the landed
uniform `(p+1)`-st root moment bound of `exists_powerLaw_root_succ_moment_bound`, not assumed.
The identity is in `ℝ≥0∞`: no summability and no finiteness of the far clusters is needed, and
the truncated subtraction agrees with the honest real difference on finite clusters. -/
theorem i41_binomial_at_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    ∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y,
            (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ≥0∞) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) := by
  set N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ) with hN
  set K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α) with hK
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmom : ∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (d := d) N K (n : ℝ)) β)) ≠ ⊤ :=
    lintegral_moment_ne_top (d := d) hd hα hβ (p := p)
      (u := (n : ℝ) / 2) (R := 2 * (n : ℝ) + 1) (by linarith) (by linarith)
      ⟨by linarith, by linarith⟩
  have hstep : ∀ ω : Config (Fin d → ℤ),
      (∑' e : Sym2 (Fin d → ℤ),
          ((radialKernel (N : Seminorm ℝ (Fin d → ℝ))
              (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
            (if e ∈ ω then (0 : ℝ≥0∞) else
              (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
                ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))) =
        ∑' x : Fin d → ℤ, ∑' y : Fin d → ℤ,
          (conn (0 : Fin d → ℤ) x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (if N (Int.cast ∘ (y - x)) ≤ (n : ℝ) then (1 : ℝ≥0∞) else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
                ((cluster ω y).encard : ℝ≥0∞)) ^ p -
              ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) := by
    intro ω
    refine (tsum_closedSel_pivotal_eq_tsum_ball (N := (N : Seminorm ℝ (Fin d → ℝ)))
      (n := (n : ℝ)) ω 0 p).trans ?_
    refine tsum_congr fun x => tsum_congr fun y => ?_
    simp only [Set.indicator_apply, mem_cluster_iff, Set.mem_compl_iff,
      ModelNorm.coe_toSeminorm]
    by_cases h : ω ∈ conn (0 : Fin d → ℤ) y <;> simp [h]
  have hmain := (lintegral_congr hstep).trans
    ((i41_cutoff_massTransport (N := N) K (n : ℝ) β p).trans
      (i41_cutoff_binomial_of_root_moment (N := N) K (n : ℝ) β hp hmom))
  have hns : ∀ z : Fin d → ℝ, (normSeminorm ℝ (Fin d → ℝ)) z = ‖z‖ := fun _ => rfl
  simpa only [hN, hK, ModelNorm.toSeminorm_ofNorm, ModelNorm.coe_ofNorm, Function.comp_def,
    hns] using hmain

end PercLib.Models.LongRange

/-! ### The per-pair and summed closed-coordinate bridges, closed-ball selector -/

namespace PercLib.Models.LongRange

open Classical in
theorem cutoff_pivotal_eq_closed_closedSel {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    {F : ℕ∞ → ℝ} {m : ℝ} (hFm : ∀ n, |F n| ≤ m)
    (β : ℝ≥0) (t : ℝ) (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ)
    (hactive : (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) ≠ 0) :
    ((radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' t * Real.exp (-(β : ℝ) * (cutoffKernel N K t e : ℝ)))) *
        ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
          ∂(law (intensityProfile (cutoffKernel N K t) β)) =
      (β : ℝ) * -K' t *
        ∫ ω, (if e ∈ ω then 0 else F (cluster (insert e ω) o).encard -
          F (cluster ω o).encard) ∂(law (intensityProfile (cutoffKernel N K t) β)) := by
  let q := intensityProfile (cutoffKernel N K t) β
  let G : Config (Fin d → ℤ) → ℝ := fun ω => F (cluster ω o).encard
  have hG : Measurable G :=
    (measurable_of_countable F).comp (measurable_encard_cluster o)
  have hGbd : ∀ ω, |G ω| ≤ m := by intro ω; exact hFm _
  have hclosed : (1 - (q e : ℝ)) * ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q =
      ∫ ω, (if e ∈ ω then 0 else G (insert e ω) - G ω) ∂law q :=
    one_sub_mul_integral_insert_sub_basic q e G hG hGbd
  have hprob : (1 - (q e : ℝ)) =
      Real.exp (-(β : ℝ) * (cutoffKernel N K t e : ℝ)) := by
    simp [q, intensityProfile]
  have hleft : (β : ℝ) * -K' t * (1 - (q e : ℝ)) *
      ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q =
      (β : ℝ) * -K' t * ∫ ω, (if e ∈ ω then 0 else G (insert e ω) - G ω) ∂law q := by
    calc (β : ℝ) * -K' t * (1 - (q e : ℝ)) *
        ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q =
        (β : ℝ) * -K' t * ((1 - (q e : ℝ)) *
          ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q) := by ring
      _ = _ := by rw [hclosed]
  change ((radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) *
    ((β : ℝ) * -K' t * Real.exp (-(β : ℝ) * (cutoffKernel N K t e : ℝ)))) *
      ∫ ω, (G (insert e ω) - G (ω \ {e})) ∂law q = _
  have hrad : (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) = 1 :=
    (radialKernel_closedSel_zero_or_one N t e).resolve_left hactive
  rw [← hprob, hrad, one_mul]
  simpa only [G, q] using hleft

open Classical in
theorem cutoff_pivotal_eq_closed_pow_closedSel {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (pow : ℕ) (β : ℝ≥0) (t : ℝ) (e : Sym2 (Fin d → ℤ)) (o : Fin d → ℤ)
    (hactive : (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) ≠ 0)
    (hfin : ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K t) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (intensityProfile (cutoffKernel N K t) β))) :
    ((radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' t * Real.exp (-(β : ℝ) * (cutoffKernel N K t e : ℝ)))) *
      ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K t) β)) =
    (β : ℝ) * -K' t *
      ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K t) β)) := by
  classical
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K t) β)
  let cw : ℝ := (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ)
  let c₀ : ℝ := (β : ℝ) * -K' t * Real.exp (-(β : ℝ) * (cutoffKernel N K t e : ℝ))
  let c₁ : ℝ := (β : ℝ) * -K' t
  have hkey : ∀ n : ℕ, cw * c₀ * (∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ) =
      c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else (min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ := by
    intro n
    have h := cutoff_pivotal_eq_closed_closedSel (K := K) (K' := K')
      (F := fun k : ℕ∞ => (min (n : ℝ≥0∞) ((k : ℝ≥0∞) ^ pow)).toReal) (m := (n : ℝ))
      (fun k => abs_capped_pow_encard_le n pow k) β t e o hactive
    simpa only [μ, cw, c₀, c₁] using h
  have hlhs : Tendsto (fun n : ℕ => ∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) := by
    have h := (tendsto_integral_capped_pivotal μ e o pow hfin hint).comp
      tendsto_natCast_atTop_atTop
    refine h.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, ENNReal.ofReal_natCast]
  have hrhs : Tendsto (fun n : ℕ => ∫ ω, (if e ∈ ω then (0 : ℝ) else (min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    tendsto_integral_closed_pivotal_truncation μ e o pow hfin hint
  have h1 : Tendsto (fun n : ℕ => cw * c₀ * ∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (cw * c₀ * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    hlhs.const_mul (cw * c₀)
  have h2 : Tendsto (fun n : ℕ => c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else (min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    hrhs.const_mul c₁
  have h2' : Tendsto (fun n : ℕ => cw * c₀ * ∫ ω, ((min (n : ℝ≥0∞)
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (c₁ * ∫ ω, (if e ∈ ω then (0 : ℝ) else
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) :=
    h2.congr' (Eventually.of_forall fun n => (hkey n).symm)
  simpa only [μ, cw, c₀, c₁] using tendsto_nhds_unique h1 h2'

open Classical in
theorem tsum_cutoff_pivotal_eq_closed_pow_closedSel {d : ℕ} {N : Seminorm ℝ (Fin d → ℝ)}
    {K K' : ℝ → ℝ}
    (pow : ℕ) (β : ℝ≥0) (t : ℝ) (o : Fin d → ℤ)
    (cw : Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ e, cw e = (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' t * Real.exp (-(β : ℝ) * (cutoffKernel N K t e : ℝ))))
    (hfin : ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K t) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (intensityProfile (cutoffKernel N K t) β))) :
    (∑' e, cw e * ∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
        ∂(law (intensityProfile (cutoffKernel N K t) β))) =
      ((β : ℝ) * -K' t) *
        ∑' e, (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) *
          ∫ ω, (if e ∈ ω then (0 : ℝ) else
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
              (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow)
            ∂(law (intensityProfile (cutoffKernel N K t) β)) := by
  classical
  let μ : Measure (Config (Fin d → ℤ)) := law (intensityProfile (cutoffKernel N K t) β)
  let rk : Sym2 (Fin d → ℤ) → ℝ :=
    fun e => (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ)
  let Piv : Sym2 (Fin d → ℤ) → ℝ := fun e => ∫ ω,
    ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
      (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ
  let Clo : Sym2 (Fin d → ℤ) → ℝ := fun e => ∫ ω, (if e ∈ ω then (0 : ℝ) else
    (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
      (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ
  have hstep : ∀ e, cw e * Piv e = ((β : ℝ) * -K' t) * (rk e * Clo e) := by
    intro e
    rcases radialKernel_closedSel_zero_or_one N t e with h | h
    · simp only [rk, hcw e, h, zero_mul, mul_zero]
    · have hact : (radialKernel N (fun s => if s ≤ t then 1 else 0) e : ℝ) ≠ 0 := by
        rw [h]
        exact one_ne_zero
      have hz := cutoff_pivotal_eq_closed_pow_closedSel (K := K) (K' := K') pow β t e o hact
        (hfin e) (hint e)
      rw [hcw e]
      simpa only [μ, rk, Piv, Clo, h, one_mul] using hz
  calc ∑' e, cw e * Piv e = ∑' e, ((β : ℝ) * -K' t) * (rk e * Clo e) := tsum_congr hstep
    _ = ((β : ℝ) * -K' t) * ∑' e, rk e * Clo e := tsum_mul_left

/-! ### The binomial diagram is finite at the corner, from the high-temperature moments -/

open Classical in
/-- **The diagram bound at the corner radius.**  The uniform `(p+1)`-st root moment bound of
`exists_powerLaw_root_succ_moment_bound` bounds every `ℓ`-th diagram term of Lemma I.4.1 at the
radius `n` itself by a finite constant, uniformly in `ℓ < p`.  This is the only finiteness input
needed for the `ℝ≥0∞` pivotal flux at the corner. -/
theorem exists_binomial_diagram_bound_closed_at_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} {n : ℕ} (hn : 1 ≤ n) :
    ∃ D : ℕ → ℝ≥0∞, (∑ ℓ ∈ Finset.range p, D ℓ) ≠ ⊤ ∧
      ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (ℓ + 1) *
          (∑' y : Fin d → ℤ,
            (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ≥0∞) else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
              ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) ≤ D ℓ := by
  set N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ) with hN
  set K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α) with hK
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hu : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hR : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  obtain ⟨M, hM, hMroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := (n : ℝ) - 1 / 2) (v := (n : ℝ) + 1 / 2) (R := 2 * (n : ℝ) + 1)
    hu hR
  have hroot : ∀ r ∈ Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
    intro r hr
    simpa only [hN, hK, ModelNorm.toSeminorm_ofNorm] using hMroot r (Or.inl hr)
  obtain ⟨D, hDtop, hDb⟩ := exists_uniform_i41_diagram_bound_of_root_succ_moment (N := N) (K := K)
    β p M hM (u := (n : ℝ) - 1 / 2) (v := (n : ℝ) + 1 / 2) hroot
  refine ⟨D, hDtop, fun ℓ hℓ => ?_⟩
  have hnmem : (n : ℝ) ∈ Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) :=
    ⟨by linarith, by linarith⟩
  have hns : ∀ z : Fin d → ℝ, (normSeminorm ℝ (Fin d → ℝ)) z = ‖z‖ := fun _ => rfl
  simpa only [hN, hK, ModelNorm.coe_ofNorm, ModelNorm.toSeminorm_ofNorm, Function.comp_def, hns]
    using hDb (n : ℝ) hnmem ℓ hℓ

open Classical in
/-- **The closed-ball pivotal flux at the corner is finite.**  Composition of the `ℝ≥0∞`
closed-ball identity `i41_binomial_at_nat` with the finite diagram bound. -/
theorem lintegral_closed_pivotal_ne_top_at_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ := by
  obtain ⟨D, hDtop, hD⟩ := exists_binomial_diagram_bound_closed_at_nat hd hα hβ hn
  refine ne_top_of_le_ne_top hDtop ?_
  rw [i41_binomial_at_nat (d := d) hd hα hβ hp hn]
  exact Finset.sum_le_sum hD

open Classical in
/-- **Per-vertex moment data at the corner radius, from high temperature.**  Every vertex has the
same cutoff `p`-th moment (`lintegral_pow_encard_cluster_eq_root`), and the uniform `(p+1)`-st
root moment bound of `exists_powerLaw_root_succ_moment_bound` bounds it.  This supplies the
per-pair a.e. finiteness, the per-pair integrability and the a.e. finiteness of the ball clusters
used below, with no extra hypothesis. -/
theorem vertex_moments_closed_at_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    (∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤) ∧
      (∀ y : Fin d → ℤ,
        ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)),
          ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤) ∧
      (∀ y : Fin d → ℤ, Integrable (fun ω => ((cluster ω y).encard : ℝ≥0∞).toReal ^ p)
        (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hu : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hR : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  have hnmem : (n : ℝ) ∈ Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) :=
    ⟨by linarith, by linarith⟩
  have hsucc : ∀ y : Fin d → ℤ,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ := by
    intro y
    obtain ⟨M, hM, hMr⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ
      y p (u := (n : ℝ) - 1 / 2) (v := (n : ℝ) + 1 / 2) (R := 2 * (n : ℝ) + 1) hu hR
    exact ne_top_of_le_ne_top hM (hMr (n : ℝ) (Or.inl hnmem))
  have hstep : ∀ y : Fin d → ℤ,
      (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ := by
    intro y
    refine ne_top_of_le_ne_top (hsucc y) ?_
    refine lintegral_mono fun ω => ?_
    have h1 : (1 : ℝ≥0∞) ≤ ((cluster ω y).encard : ℝ≥0∞) := by
      exact_mod_cast one_le_encard_cluster ω y
    exact pow_le_pow_right₀ h1 (Nat.le_succ p)
  exact ⟨hstep,
    fun y => ae_ne_top_of_lintegral_pow_ne_top (measurable_encard_cluster_coe y) p hp (hstep y),
    fun y => integrable_toReal_pow_encard_cluster_of_lintegral_ne_top _ y p (hstep y)⟩

open Classical in
/-- **The real form of the closed-ball binomial identity at the corner.**  This is the `toReal`
passage of Lemma I.4.1 at the integer radius `n` itself: the real integral of the extended-
nonnegative pivotal series with the closed-ball selector is the paper's real binomial sum, with
the closed ball `B_n` and the *same* law.  The a.e. finiteness of the ball clusters, which
`ENNReal.toReal` silently discards otherwise, is the input `hvert`; here it is discharged from the
high-temperature root moment.

The proof transplants the real-binomial passage of `i41_real_of_root_finite` to the corner: the
only extra inputs are the `ℝ≥0∞` identity `i41_binomial_at_nat` (which needs no corner-free
hypothesis) and the per-vertex a.e. finiteness. -/
theorem i41_real_flux_closed_at_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n)
    (hflux : (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤)
    (hvert : ∀ y : Fin d → ℤ,
        ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)),
          ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤) :
    (∫ ω, ((∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)))).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω, (((cluster ω (
        0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ) else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) := by
  classical
  set w : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e =>
    ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) with hwdef
  set P : Config (Fin d → ℤ) → ℝ≥0∞ := fun ω => ∑' e : Sym2 (Fin d → ℤ),
      w e * (if e ∈ ω then (0 : ℝ≥0∞) else
        (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
          ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)) with hPdef
  set A : ℕ → Config (Fin d → ℤ) → ℝ≥0∞ := fun ℓ ω => ((cluster ω (
    0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ≥0∞) else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ)) with hAdef
  set R : ℕ → Config (Fin d → ℤ) → ℝ := fun ℓ ω => (((cluster ω (
    0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ) else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ)) with hRdef
  have hflux' : (∫⁻ ω, P ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ := hflux
  have hPmeas : Measurable P := measurable_tsum_closed_pivotal (V := Fin d → ℤ) 0 p w
  have hENN : ∫⁻ ω, P ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, A ℓ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) :=
    i41_binomial_at_nat (d := d) hd hα hβ hp hn
  have hsumne : (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
      ∫⁻ ω, A ℓ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ := by
    rw [← hENN]; exact hflux'
  have hterm : ∀ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
      ∫⁻ ω, A ℓ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mp hsumne
  have hAint : ∀ ℓ ∈ Finset.range p, (∫⁻ ω, A ℓ ω ∂(law (intensityProfile (cutoffKernel (
    normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ := by
    intro ℓ hℓ
    by_contra h
    have hlt : ℓ < p := Finset.mem_range.mp hℓ
    have hc : (p.choose ℓ : ℝ≥0∞) ≠ 0 := by
      have hpos : 0 < p.choose ℓ := Nat.choose_pos (by omega)
      exact_mod_cast hpos.ne'
    exact hterm ℓ hℓ (by rw [h, ENNReal.mul_top hc])
  have htsum : ∀ ℓ : ℕ, Measurable fun ω : Config (Fin d → ℤ) =>
      ∑' y : Fin d → ℤ,
        (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ≥0∞) else 0) *
          (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((cluster ω y).encard : ℝ≥0∞) ^ (p - ℓ) := by
    intro ℓ
    refine Measurable.tsum fun y => ?_
    exact (measurable_const.mul
      (measurable_const.indicator (measurableSet_conn 0 y).compl)).mul
      ((measurable_encard_cluster_coe y).pow_const (p - ℓ))
  have hAmeas : ∀ ℓ : ℕ, Measurable (A ℓ) := fun ℓ =>
    ((measurable_encard_cluster_coe 0).pow_const (ℓ + 1)).mul (htsum ℓ)
  have hAae : ∀ ℓ ∈ Finset.range p, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (
    normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)), A ℓ ω ≠ ⊤ := by
    intro ℓ hℓ
    filter_upwards [ae_lt_top (hAmeas ℓ) (hAint ℓ hℓ)] with ω hω
    exact hω.ne
  have hPae : ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)), P ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hPmeas hflux'] with ω hω
    exact hω.ne
  have hball_ae : ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)), ∀ y : Fin d → ℤ,
      normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) → ω ∉ conn (0 : Fin d → ℤ) y →
      ((cluster ω y).encard : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [MeasureTheory.ae_all_iff.2 hvert] with ω hω
    intro y _ _
    exact hω y
  calc ∫ ω, (P ω).toReal ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))
      = (∫⁻ ω, P ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))).toReal :=
        integral_toReal_eq_toReal_lintegral hPmeas.aemeasurable hPae
    _ = (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ∫⁻ ω, A ℓ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))).toReal := by rw [hENN]
    _ = ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℝ≥0∞) *
          ∫⁻ ω, A ℓ ω ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))).toReal := ENNReal.toReal_sum hterm
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * (∫⁻ ω, A ℓ ω ∂(law (intensityProfile (
      cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))).toReal := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω, (A ℓ ω).toReal ∂(law (
      intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [integral_toReal_eq_toReal_lintegral (hAmeas ℓ).aemeasurable (hAae ℓ hℓ)]
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω, R ℓ ω ∂(law (intensityProfile (
      cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [integral_congr_ae]
        filter_upwards [hball_ae] with ω hb
        exact toReal_ordered_rhs_of_ball_finite (N := normSeminorm ℝ (Fin d → ℝ))
          (r := (n : ℝ)) (p := p) (ℓ := ℓ) hb




/-! ### The real pivotal series is the rate times the extended-nonnegative flux -/

open Classical in
/-- **`fluxClosedAt` is the rate times the `toReal` cast of the closed-ball `ℝ≥0∞` flux.**

This is `fluxClosedAt_eq_raw` followed by the production transfer
`tsum_pivotal_eq_rate_mul_toReal_lintegral`, which replaces the real series of per-pair pivotal
expectations by the `toReal` of the extended-nonnegative flux using only `lintregral_tsum` at
`ℝ≥0∞` level (no summability of any real series is assumed, so the `tsum = 0` junk value of a
non-summable family never enters).  The per-pair inputs `hfin`, `hint` and `hflux` are discharged
from per-vertex moments at the actual law. -/
theorem fluxClosedAt_eq_rate_mul_lintegral_closed {d : ℕ} {α : ℝ} {β : ℝ≥0} {p : ℕ} {n : ℝ}
    (hfin : ∀ e : Sym2 (Fin d → ℤ), ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (
      normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)),
      ((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω =>
      (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ p) (law (
        intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)))
    (hflux : ∀ e, (∫⁻ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(law (intensityProfile (
        cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤) :
    fluxClosedAt d α β p n = powerLawRate d α β n *
      (∫⁻ ω, (∑' e : Sym2 (Fin d → ℤ),
        ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ≥0) : ℝ≥0∞) *
          (if e ∈ ω then (0 : ℝ≥0∞) else
            (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))) ∂(law (intensityProfile (
                cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))).toReal := by
  classical
  set K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α) with hK
  set K' : ℝ → ℝ := fun t => -(((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)) with hK'
  set w : Sym2 (Fin d → ℤ) → ℝ≥0∞ := fun e =>
    ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (fun s => if s ≤ n then 1 else 0) e : ℝ≥0) : ℝ≥0∞) with hwdef
  set rk : Sym2 (Fin d → ℤ) → ℝ := fun e =>
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s ≤ n then 1 else 0) e : ℝ)
    with hrkdef
  set cw : Sym2 (Fin d → ℤ) → ℝ := fun e => rk e * ((β : ℝ) * -K' n *
    Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) K n e : ℝ))) with hcwdef
  have hwto : ∀ e, (w e).toReal = rk e := fun e => by simp [w, rk]
  have hpair : ∀ e, cw e * ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal ∂(law (
          intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) =
      ((β : ℝ) * -K' n) * ((w e).toReal *
        (∫⁻ ω, (if e ∈ ω then (0 : ℝ≥0∞) else
          (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p)) ∂(law (intensityProfile (
              cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))).toReal) := by
    intro e
    have hcl := integral_toReal_closed_pivotal (law (intensityProfile
      (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) e (0 : Fin d → ℤ) p (hfin e)
    have hsub := integral_pivotal_pow_eq_real_sub (law (intensityProfile
      (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) e (0 : Fin d → ℤ) p (hfin e)
    rw [hwto e, hsub, hcl]
    rcases radialKernel_closedSel_zero_or_one (normSeminorm ℝ (Fin d → ℝ)) n e with h0 | h1
    · simp [cw, rk, h0]
    · have hz := cutoff_pivotal_eq_closed_pow_closedSel (K := K) (K' := K') p β n e
        (0 : Fin d → ℤ) (by rw [h1]; norm_num) (hfin e) (hint e)
      rw [h1, one_mul] at hz
      simpa only [cw, rk, h1, hK', neg_neg, one_mul] using hz
  have hmain := tsum_pivotal_eq_rate_mul_toReal_lintegral (law (intensityProfile (
    cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) (0 : Fin d → ℤ) p w cw
    ((β : ℝ) * -K' n) (fun e => ENNReal.coe_ne_top) hflux hpair
  rw [fluxClosedAt_eq_raw]
  simpa only [hK, hK', hwdef, hrkdef, hcwdef, powerLawRate, neg_neg] using hmain

/-! ### Lemma I.4.1 at the corner: the exact equality of the two values -/

open Classical in
/-- **Lemma I.4.1 at a positive integer radius: `fluxClosedAt` is the paper's binomial flux.**

Under `d ≥ 1`, `α > 0`, the explicit high temperature condition
`β · ∑'_z ‖z‖^{-(d+α)} < 1`, `p ≥ 1` and `n ≥ 1`, the closed-ball pivotal flux at the corner
`n` — the right limit of the derivative of the cutoff root moment, i.e. the value produced by
`hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat` — equals the prefactor
`powerLawRate d α β n` times the paper's binomial expression of Lemma I.4.1 with the closed ball
`B_n` and the *same* law `μ_n`:

`∑_{ℓ<p} C(p,ℓ) ∫ |K_0|^{ℓ+1} ∑_{y: ‖y‖≤n} 1(y ∉ K_0) |K_y|^{p−ℓ} ∂μ_n`,

where `|K|` is the `ncard` of the cluster.  No derivative is taken and no two-sided claim is
made; this is an identity of values at the same scale and law. -/
theorem fluxClosedAt_eq_paper_binomial {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    fluxClosedAt d α β p (n : ℝ) = powerLawRate d α β (n : ℝ) *
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω, (((cluster ω (
        0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
        (∑' y : Fin d → ℤ,
          (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ) else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) := by
  classical
  obtain ⟨hmom, hae, hintU⟩ := vertex_moments_closed_at_nat hd hα hβ hp hn
  have hfluxP := lintegral_closed_pivotal_ne_top_at_nat hd hα hβ hp hn
  have hins : ∀ e : Sym2 (Fin d → ℤ), (∫⁻ ω,
      ((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ :=
    fun e => PercLib.Percolation.Bond.lintegral_pow_encard_cluster_insert_ne_top_forall
      (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) (0 : Fin d → ℤ) p hmom e
  have hfin : ∀ e : Sym2 (Fin d → ℤ), ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel (
    normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)),
      ((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ≠ ⊤ :=
    fun e => ae_ne_top_encard_cluster_insert (law (intensityProfile (cutoffKernel (
      normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) e (0 : Fin d → ℤ) hae
  have hint : ∀ e, Integrable (fun ω =>
      (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ p)
      (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) :=
    fun e => integrable_toReal_pow_encard_cluster_insert e (0 : Fin d → ℤ) p (hins e)
  have hflux : ∀ e, (∫⁻ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p) ∂(law (intensityProfile (
        cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β))) ≠ ⊤ :=
    fun e => lintegral_pivotal_increment_ne_top_of_lintegral_insert_pow_ne_top e
      (0 : Fin d → ℤ) p (hins e)
  refine (fluxClosedAt_eq_rate_mul_lintegral_closed hfin hint hflux).trans ?_
  congr 1
  rw [← integral_toReal_eq_toReal_lintegral]
  · exact i41_real_flux_closed_at_nat hd hα hβ hp hn hfluxP hae
  · exact (measurable_tsum_closed_pivotal (V := Fin d → ℤ) 0 p _).aemeasurable
  · exact ae_ne_top_tsum_closed_pivotal_of_lintegral_ne_top
      (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)) (0 : Fin d → ℤ) p _ hfluxP

open Classical in
/-- **The one-sided form of Lemma I.4.1 at a positive integer radius.** In the explicit
high-temperature regime, the uncorrected, uncapped cutoff root moment has the paper's binomial
expression as its right derivative at `n` within `Ici n`. No two-sided derivative is claimed. -/
theorem hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_paper_binomial_at_nat {d : ℕ}
    (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivWithinAt (fun r : ℝ =>
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal)
      (powerLawRate d α β (n : ℝ) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) * ∫ ω,
          (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (n : ℝ) then (1 : ℝ) else 0) *
                (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
                (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)))
      (Ici (n : ℝ)) (n : ℝ) := by
  have h :=
    CornerMoment.hasDerivWithinAt_lintegral_encard_cluster_pow_toReal_powerLaw_nat
    (d := d) hd hα hβ hp hn
  rw [fluxClosedAt_eq_paper_binomial hd hα hβ hp hn] at h
  exact h

end PercLib.Models.LongRange
