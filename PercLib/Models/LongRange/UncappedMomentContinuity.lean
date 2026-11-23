/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Continuity of the uncapped cut-off power-law cluster moments in the cut-off scale, obtained as a
uniform limit of the bounded capped moments. No derivative-level cap removal is claimed.
-/
module

public import PercLib.Models.LongRange.CappedDerivative
public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Models.LongRange.PowerLawCapMoment
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuity of the uncapped cut-off cluster moments in the cut-off scale

The `p`-th cut-off cluster moment at scale `ρ` is

`m p ρ = (∫⁻ ω, |K_o(ω)| ^ p ∂law (cutoffProfile ρ)).toReal`.

This file proves that `m p` is continuous on every **corner-free** set of positive scales — a set
containing no value of the sup norm on `ℤ^d`, i.e. no natural number. The route is value level and
uses no derivative of the uncapped moment:

* `exists_integral_capCluster_uniform_error_powerLaw_all_scales`: a single finite higher-moment
  constant `M` gives the cap error `m p ρ - m p ρ (capped at B) ≤ B⁻¹ M.toReal` at **every**
  positive scale, not only in a window. This is `PercLib.Probability.capMoment_error_le` with the
  `(p+1)`-st moment dominated by the *uncut* power-law moment, which exists in the high-temperature
  region `β M < 1`.
* `differentiableAt_integral_capCLuster_powerLaw`: the bounded capped moment, as a function of the
  scale, is differentiable at every corner-free positive scale, with the pivotal-flux derivative of
  `PercLib.Models.LongRange.hasDerivAt_integral_cutoff`. This is the production derivative
  interface re-instantiated at a general corner-free scale (production records `r₀ = 1/2`), not a
  new proof of that interface.
* `continuousOn_integral_capCluster_powerLaw`: consequently every bounded capped moment is
  continuous on a corner-free set of positive scales.
* `continuousOn_lintegral_encard_cluster_pow_toReal_powerLaw`: **the uncapped real moment is
  continuous on every corner-free set of positive scales** in the high-temperature region, as a
  locally uniform limit of the continuous capped moments.

What is *not* claimed: no derivative of the uncapped moment, no interchange of the cap limit with
differentiation, no `htail`, and no assertion of differentiability at a lattice-norm corner.
The cut-off probabilities are continuous at corners, but the bounded derivative interfaces exclude
them; this is not a corner counterexample. The cap error bound is uniform on the whole scale window
because the higher-moment constant is scale-uniform, and the limit has uniform error locally in the
scale, not jointly in the cap and every scale parameter.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### The scale-uniform cap error bound -/

/-- **The cap error is `O(1/B)` uniformly over all positive scales.** There is a single finite
`(p+1)`-st root-moment bound `M`, namely the *uncut* power-law moment, such that at every positive
cut-off scale `ρ` and every cap `B ≥ 1` the cap error of the `p`-th moment is at most
`B⁻¹ M.toReal`. Compared with `exists_integral_capCluster_uniform_error_powerLaw`, the window
`Ioo u v ∪ {R}` is replaced by the whole half-line `(0, ∞)`: monotonicity of the cut-off in the
scale bounds the higher moment at every scale by the same uncut moment. -/
theorem exists_integral_capCluster_uniform_error_powerLaw_all_scales {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ r : ℝ, 0 < r → ∀ B : ℕ, 1 ≤ B →
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal -
        ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)
        ≤ ((B : ℝ)⁻¹) * M.toReal := by
  classical
  refine ⟨(∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
      ∂law (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))) β)),
    BFS.power_lintegral_encard_cluster_pow_ne_top hd hα hβ o (p + 1), ?_⟩
  intro r hr B hB
  have hbound : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
        ∂law (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α))) β) :=
    lintegral_cutoffKernel_encard_cluster_pow_le (N := ModelNorm.ofNorm (Fin d → ℝ))
      (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hr β o (p + 1)
  have hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ :=
    ne_top_of_le_ne_top (BFS.power_lintegral_encard_cluster_pow_ne_top hd hα hβ o (p + 1)) hbound
  refine (PercLib.Probability.capMoment_error_le _ (measurable_encard_cluster o) p hB hfin).trans ?_
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono (BFS.power_lintegral_encard_cluster_pow_ne_top hd hα hβ o (p + 1))
      hbound) (by positivity)

/-! ### The bounded capped moment is below the uncapped one -/

/-- **The capped `p`-th moment is at most the uncapped extended `p`-th moment.** The cap envelope
is pointwise below the identity and the `p`-th power is monotone, so the ordinary integral of the
capped weight is at most the `toReal` of the extended moment. -/
theorem integral_capCluster_le_lintegral_toReal_powerLaw {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p B : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β) ≤
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal := by
  rw [PercLib.Probability.integral_capToNat_pow_eq_toReal _ (measurable_encard_cluster o) p B]
  refine ENNReal.toReal_mono (lintegral_cutoffKernel_powerLaw_pow_ne_top hd hα hβ hr o p)
    (lintegral_mono fun ω => ?_)
  refine pow_le_pow_left₀ zero_le ?_ p
  rw [PercLib.Probability.capToNat_eq_inf]
  exact inf_le_left

/-! ### The bounded capped moment is differentiable in the scale -/

/-- **The capped `p`-th moment is differentiable in the cut-off scale at every corner-free positive
scale.** This is the production derivative interface
`PercLib.Models.LongRange.hasDerivAt_integral_cutoff` instantiated at the power law
`powerLawProfile 1 (d + α)` in the sup norm, the bounded, eventually-constant cap envelope
`F_B n = min(n, B) ^ p`, and an arbitrary corner-free `r > 0` (the derivative value — the pivotal
flux at scale `r` — is supplied by that interface and is not restated here). Production records only
`r₀ = 1/2` (`hasDerivAt_integral_cutoff_powerLaw_sup_capped`); the statement at this generality is
what makes continuity on the windows `(2, 3)` and `(5/4, 8/5)` available. -/
theorem differentiableAt_integral_capCluster_powerLaw {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p B : ℕ) {r : ℝ} (hr : 0 < r)
    (hcorner : ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r) :
    DifferentiableAt ℝ (fun s : ℝ => ∫ (ω : Config (Fin d → ℤ)),
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) s) β)) r := by
  classical
  have hda : (0 : ℝ) ≤ (d : ℝ) + α := by positivity
  refine ⟨_, hasDerivAt_integral_cutoff (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) zero_le_one hda)
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add 1 α) β
    (F := fun n : ℕ∞ => (((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ)) ^ p) (m := (B : ℝ) ^ p) ?_ ?_ o
    (R := r + 1) (chi_cutoffKernel_powerLaw_ne_top hd hα hβ (by linarith) o) hr (by linarith) ?_⟩
  · intro n
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (cap_toNat_abs_le B n) p
  · exact ⟨B, fun n hn => by rw [cap_toNat_eq_top B hn]⟩
  · intro z
    simp only [ModelNorm.coe_ofNorm]
    rw [norm_intCast_comp]
    exact hcorner z

/-- **Every bounded capped moment is continuous on a corner-free set of positive scales.** For a set
`I` of positive scales containing no value `‖z‖` of the sup norm on `ℤ^d`, the capped `p`-th moment
is continuous on `I`. Cut-off probabilities are continuous at corners, but the bounded derivative
statement uses the corner-free interface; this value-level statement makes no corner claim. -/
theorem continuousOn_integral_capCluster_powerLaw {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p B : ℕ) {I : Set ℝ} (hI : ∀ r ∈ I, 0 < r)
    (hcorner : ∀ r ∈ I, ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r) :
    ContinuousOn (fun s : ℝ => ∫ (ω : Config (Fin d → ℤ)),
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) s) β)) I :=
  continuousOn_of_forall_continuousAt fun r hr =>
    (differentiableAt_integral_capCluster_powerLaw hd hα hβ o p B (hI r hr)
      (hcorner r hr)).continuousAt

/-! ### Continuity of the uncapped real moment -/

/-- **The uncapped real cut-off cluster moment is continuous on corner-free sets of positive
scales.** In the high-temperature region `β M < 1`, for every root `o` and every `p : ℕ`, the real
moment `ρ ↦ (∫⁻ ω, |K_o(ω)| ^ p ∂law (cutoffProfile ρ)).toReal` is continuous on any set `I` of
positive scales that contains no value of the sup norm on `ℤ^d`.

Proof: each bounded capped moment is continuous on `I`
(`continuousOn_integral_capCluster_powerLaw`) and the scale-uniform cap error bound
(`exists_integral_capCluster_uniform_error_powerLaw_all_scales`) makes the convergence
`B ↦ capped moment B` locally uniform on `I`, so the locally uniform limit theorem applies. The
limit is the honest real moment because the `p`-th moment is finite in the high-temperature region.

Not claimed: differentiability of the limit, equality of its derivative with the binomial flux, or
continuity at a corner scale. -/
theorem continuousOn_lintegral_encard_cluster_pow_toReal_powerLaw {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) {I : Set ℝ} (hI : ∀ r ∈ I, 0 < r)
    (hcorner : ∀ r ∈ I, ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r) :
    ContinuousOn (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) I := by
  classical
  obtain ⟨M, hM, herr⟩ :=
    exists_integral_capCluster_uniform_error_powerLaw_all_scales hd hα hβ o p
  set mB : ℕ → ℝ → ℝ := fun B r => ∫ (ω : Config (Fin d → ℤ)),
      (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) with hmB
  set m : ℝ → ℝ := fun r => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal with hm
  -- the capped moment is bounded above by the uncapped one
  have hmono : ∀ (r : ℝ) (hr : r ∈ I) (B : ℕ), mB B r ≤ m r := by
    intro r hr B
    simp only [hmB, hm]
    exact integral_capCluster_le_lintegral_toReal_powerLaw hd hα hβ o p B (hI r hr)
  -- the scale-uniform cap error bound, two-sided
  have hbound : ∀ (r : ℝ) (hr : r ∈ I) (B : ℕ), 1 ≤ B →
      |m r - mB B r| ≤ ((B : ℝ)⁻¹) * M.toReal := by
    intro r hr B hB
    rw [abs_of_nonneg (by linarith [hmono r hr B])]
    exact herr r (hI r hr) B hB
  -- local uniform convergence of the capped moments
  have hloc : TendstoLocallyUniformlyOn mB m atTop I := by
    intro u hu x hx
    rw [Metric.mem_uniformity_dist] at hu
    obtain ⟨ε, hε, hεu⟩ := hu
    refine ⟨I, self_mem_nhdsWithin, ?_⟩
    have hsmall : ∀ᶠ B : ℕ in atTop, ((B : ℝ)⁻¹) * M.toReal < ε := by
      have h0 : Tendsto (fun B : ℕ => ((B : ℝ)⁻¹) * M.toReal) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const M.toReal
      exact (tendsto_order.1 h0).2 ε hε
    filter_upwards [hsmall, eventually_ge_atTop 1] with B hBsmall hB1 y hy
    refine hεu ?_
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hbound y hy B hB1) hBsmall
  have hcont : ∀ᶠ B : ℕ in atTop, ContinuousOn (mB B) I :=
    Eventually.of_forall fun B =>
      continuousOn_integral_capCluster_powerLaw hd hα hβ o p B hI hcorner
  have hfin := hloc.continuousOn hcont.frequently
  simpa [hm] using hfin

/-! ### Corner-free windows -/

/-- A set containing no natural number is corner-free for the sup norm: sup-norm values on `ℤ^d`
are natural numbers. -/
theorem cornerFree_of_no_nat {I : Set ℝ} (h : ∀ n : ℕ, (n : ℝ) ∉ I) :
    ∀ r ∈ I, ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r := by
  intro _r hr z hz
  obtain ⟨n, hn⟩ := exists_nat_eq_norm z
  exact h n (by rw [← hn, hz]; exact hr)

/-- The window `(2, 3)` used for the nondegenerate scale `5/2` is corner-free. -/
theorem cornerFree_Ioo_two_three :
    ∀ r ∈ Ioo (2 : ℝ) 3, ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r := by
  refine cornerFree_of_no_nat fun n hn => ?_
  have hlt : 2 < n := by exact_mod_cast hn.1
  have hge : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
  linarith [hn.2]

/-- The window `(5/4, 8/5)` used for the nondegenerate scale `3/2` is corner-free. -/
theorem cornerFree_Ioo_five_quarters_eight_fifths :
    ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r := by
  refine cornerFree_of_no_nat fun n hn => ?_
  have h1 : (1 : ℝ) < (n : ℝ) := by linarith [hn.1]
  have hlt : 1 < n := by exact_mod_cast h1
  have hge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 ≤ n by omega)
  linarith [hn.2]

/-! ### Pointwise continuity at a single corner-free scale -/

/-- **The uncapped real cut-off moment is continuous at every corner-free positive scale.** This is
the pointwise form: a corner-free neighbourhood of `r` exists
(`exists_corner_free_interval`), and on it the moment is continuous by
`continuousOn_lintegral_encard_cluster_pow_toReal_powerLaw`. -/
theorem continuousAt_lintegral_encard_cluster_pow_toReal_powerLaw {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) {r : ℝ} (hr : 0 < r)
    (hcorner : ∀ z : Fin d → ℤ, (‖z‖ : ℝ) ≠ r) :
    ContinuousAt (fun s : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) s) β)).toReal) r := by
  obtain ⟨δ, hδ, -, hδI⟩ :=
    exists_corner_free_interval (ModelNorm.ofNorm (Fin d → ℝ)) (r₀ := r) (R := r + 1) hr
      (by linarith) fun z => by
        simpa [ModelNorm.coe_ofNorm, norm_intCast_comp] using hcorner z
  have h0 : 0 ≤ r - δ := by
    by_contra h
    exact hδI 0 ⟨by linarith, by linarith⟩ 0 (by simp)
  have hcont := continuousOn_lintegral_encard_cluster_pow_toReal_powerLaw hd hα hβ o p
    (I := Ioo (r - δ) (r + δ)) (fun s hs => by linarith [hs.1]) fun s hs z => by
      simpa [ModelNorm.coe_ofNorm, norm_intCast_comp] using hδI s hs z
  exact hcont.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-- **Continuity on the `5/2` window.** On `(2, 3)`, which contains the nondegenerate scale `5/2`,
the uncapped real `p`-th cut-off cluster moment is continuous. -/
theorem continuousOn_lintegral_capCluster_pow_toReal_five_halves {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ContinuousOn (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) (Ioo (2 : ℝ) 3) :=
  continuousOn_lintegral_encard_cluster_pow_toReal_powerLaw hd hα hβ o p
    (fun _ hr => lt_trans two_pos hr.1) cornerFree_Ioo_two_three

/-- **Continuity at `5/2`.** -/
theorem continuousAt_lintegral_capCluster_pow_toReal_five_halves {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ContinuousAt (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) (5 / 2) :=
  (continuousOn_lintegral_capCluster_pow_toReal_five_halves hd hα hβ o p).continuousAt
    (Ioo_mem_nhds (by norm_num) (by norm_num))

/-- **Continuity on the `3/2` window.** On `(5/4, 8/5)`, the exact corner-free window of the
`hroot` premise of `hasDerivAt_powerLaw_three_halves_of_root_moment_of_small_tail`, which contains
the nondegenerate scale `3/2`, the uncapped real `p`-th cut-off cluster moment is continuous. -/
theorem continuousOn_lintegral_capCluster_pow_toReal_three_halves {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ContinuousOn (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) (Ioo (5 / 4 : ℝ) (8 / 5)) :=
  continuousOn_lintegral_encard_cluster_pow_toReal_powerLaw hd hα hβ o p
    (fun r hr => by linarith [hr.1]) cornerFree_Ioo_five_quarters_eight_fifths

/-- **Continuity at `3/2`.** -/
theorem continuousAt_lintegral_capCluster_pow_toReal_three_halves {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ContinuousAt (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) (3 / 2) :=
  (continuousOn_lintegral_capCluster_pow_toReal_three_halves hd hα hβ o p).continuousAt
    (Ioo_mem_nhds (by norm_num) (by norm_num))

/-! ### The uniform `ε`-form of the cap approximation -/

/-- **Uniform-in-scale `ε` form of the cap error bound.** For every `ε > 0` there is a cap `B₀` such
that for every cap `B ≥ B₀` and *every* positive scale `ρ` the `p`-th moment differs from its capped
version by less than `ε`. This is the qualitative uniform form of
`exists_integral_capCluster_uniform_error_powerLaw_all_scales`, i.e. the statement that the capped
moments converge to the uncapped moment uniformly on the whole half-line of positive scales. -/
theorem forall_pos_exists_integral_capCluster_uniform_error_powerLaw {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B → ∀ ρ : ℝ, 0 < ρ →
      |(∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)).toReal -
        ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)| < ε := by
  classical
  obtain ⟨M, hM, herr⟩ :=
    exists_integral_capCluster_uniform_error_powerLaw_all_scales hd hα hβ o p
  have hsmall : ∀ᶠ B : ℕ in atTop, ((B : ℝ)⁻¹) * M.toReal < ε := by
    have h0 : Tendsto (fun B : ℕ => ((B : ℝ)⁻¹) * M.toReal) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const M.toReal
    exact (tendsto_order.1 h0).2 ε hε
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 hsmall
  refine ⟨max B₀ 1, fun B hB => ?_⟩
  intro ρ hρ
  have hB1 : 1 ≤ B := le_trans (le_max_right _ _) hB
  have hle := integral_capCluster_le_lintegral_toReal_powerLaw hd hα hβ o p B hρ
  have herr' := herr ρ hρ B hB1
  rw [abs_of_nonneg (by linarith)]
  exact lt_of_le_of_lt herr' (hB₀ B (le_trans (le_max_left _ _) hB))


/-! ### The fully explicit dimension-two witness -/

/-- **Continuity at `5/2` at fully explicit parameters.** At `d = 2`, `α = 1` (`K s = s⁻³`) and
`β = 1/100`, every hypothesis of `continuousAt_lintegral_capCluster_pow_toReal_five_halves` is
discharged, so the uncapped real `p`-th cut-off cluster moment is continuous at `5/2` with no
remaining hypotheses. -/
theorem continuousAt_lintegral_capCluster_d2_beta_one_hundredth_five_halves
    (o : Fin 2 → ℤ) (p : ℕ) :
    ContinuousAt (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
        (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) r) (1 / 100))).toReal) (5 / 2) :=
  continuousAt_lintegral_capCluster_pow_toReal_five_halves (d := 2) (by norm_num) (α := 1)
    one_pos d2_beta_rowSum_lt_one o p

/-- **Continuity on the `5/2` window at fully explicit parameters.** At `d = 2`, `α = 1` and
`β = 1/100`, the uncapped real `p`-th cut-off cluster moment is continuous on all of `(2, 3)`. -/
theorem continuousOn_lintegral_capCluster_d2_beta_one_hundredth_five_halves
    (o : Fin 2 → ℤ) (p : ℕ) :
    ContinuousOn (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
        (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) r) (1 / 100))).toReal) (Ioo (2 : ℝ) 3) :=
  continuousOn_lintegral_capCluster_pow_toReal_five_halves (d := 2) (by norm_num) (α := 1)
    one_pos d2_beta_rowSum_lt_one o p
end PercLib.Models.LongRange
