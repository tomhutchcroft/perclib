/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
# Two-point convergence along the cut-off scale

For a radial profile `K` on `ℤ^d` (Definition I.1.3/5 of T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1) with cut-off kernels
`J_r = radialKernel (cutoffProfile K r)` of `PercLib/Models/LongRange/Defs.lean`, this file
proves that the two-point model at radius `r` converges to the uncut model as `r → ∞`, under the
profile hypotheses

* `∀ t, 0 < t → 0 ≤ K t` (`hKnn`),
* `AntitoneOn K (Ioi 0)` (`hKanti`),
* `Tendsto K atTop (𝓝 0)` (`hK`).

The chain is

1. `tendsto_cutoffProfile_atTop`, `tendsto_cutoffKernel_atTop`, `tendsto_cutoffKernel_pi`: the
   cut-off profile and kernel converge pointwise, hence as functions in the product topology.
   Only `hK` is used here: `Real.toNNReal` is continuous, so neither nonnegativity nor
   antitonicity is needed for the limit itself.
2. `tendsto_intensityProfile_cutoffKernel[_pi]`: the open-pair probabilities
   `q_r = intensityProfile J_r β` converge in the product topology on
   `Sym2 (ℤ^d) → unitInterval`, because `x ↦ 1 - exp (-(β : ℝ) x)` is continuous.
3. `tendsto_tau_of_tendsto_profile`: a general monotone-convergence lemma for bond percolation on
   any countable vertex type: if `q_r` increases in `r`, stays below `q` and converges
   coordinatewise, then `P_{q_r}(x ↔ y)` tends to `P_q(x ↔ y)`. The proof is the only place where
   the infinite product measure is used: `P_q(x ↔ y) = ⨆_n P_q(x ↔ y inside S_n)` for a finite
   exhaustion `S` (`tau_eq_iSup_localConn`, continuity from below) and each finite-domain
   probability is continuous in the profile (`continuous_law_localConn`).
4. `tendsto_law_cylinder_cutoffKernel`, `tendsto_law_localConn_cutoffKernel`,
   `tendsto_tau_cutoffKernel`: the cut-off instantiation of 3, with monotonicity from
   `Models.LongRange.monotone_cutoffKernel` and the comparison
   `Models.LongRange.cutoffKernel_le_radialKernel`. Everything is `ℝ≥0∞`-valued, so an infinite
   two-point function is allowed at both ends; no moment, derivative, temperature or
   summability hypothesis appears.

`cutoffKernel_eq_radialKernel_of_eq_zero_of_le`, `law_cutoffKernel_eq_of_eq_zero_of_le` and
`tau_cutoffKernel_eq_of_eq_zero_of_le` record the finite-range degeneracy: if `K` vanishes on
`[R₀, ∞)`, then at every radius `r ≥ R₀` the cut-off kernel, the law of the configuration and the
two-point function *are* the uncut ones, so the limits of 4 are attained and the model is
radius-independent from `R₀` on.

Cut-off convention: `cutoffProfile K r s = 1{s ≤ r} (K s - K r)`, so distance `s = r` is
included, contributes `K s - K r = 0` there, and distances `s > r` contribute `0`. The diagonal
`x = x` is `0` at every radius, and both sides agree there.

Provenance: all declarations below are new. The production statements used are cited by name in
the proofs and are applied, not restated; nothing is copied from the fork `yujinhkim/lrp`.
-/
module

public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.SusceptibilityContinuity
public import PercLib.Probability.FiniteContinuity

/-!
# Cut-off two-point convergence

Convergence of pointwise cut-off profiles, finite-cylinder and local connection probabilities,
and the full two-point function at a monotone increasing family of bond profiles.
No weak convergence of arbitrary laws, moment convergence or criticality assertion is made.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}

/-- **The cut-off profile converges to the profile at a fixed distance.** At every distance `s`
the value `1{s ≤ r} (K s - K r)` of the cut-off profile tends to `K s` as `r → ∞`, provided the
profile tends to `0` at infinity. Antitonicity and nonnegativity of `K` are not needed: the
truncation `Real.toNNReal` is continuous on `ℝ`. -/
theorem tendsto_cutoffProfile_atTop {s : ℝ} (hK : Tendsto K atTop (𝓝 0)) :
    Tendsto (fun r => cutoffProfile K r s) atTop (𝓝 (K s)) := by
  have h1 : Tendsto (fun r : ℝ => K s - K r) atTop (𝓝 (K s - 0)) :=
    tendsto_const_nhds.sub hK
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop s] with r hr
  exact (cutoffProfile_of_le hr).symm

/-- **Pointwise convergence of the cut-off kernel to the radial kernel.** For every pair
`e : Sym2 (ℤ^d)` the cut-off kernel `J_r e` tends to the uncut kernel `J e` as `r → ∞`, whenever
the profile tends to `0` at infinity. Only that limit is used: the truncation is continuous. -/
theorem tendsto_cutoffKernel_atTop (hK : Tendsto K atTop (𝓝 0)) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r => cutoffKernel N K r e) atTop (𝓝 (radialKernel N K e)) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · simp [h]
    · have hstep : Tendsto
          (fun r => Real.toNNReal (cutoffProfile K r (N (Int.cast ∘ (x - y)))))
          atTop (𝓝 (Real.toNNReal (K (N (Int.cast ∘ (x - y)))))) :=
        continuous_real_toNNReal.continuousAt.tendsto.comp (tendsto_cutoffProfile_atTop hK)
      have htarget : radialKernel N K s(x, y) =
          Real.toNNReal (K (N (Int.cast ∘ (x - y)))) := by
        simp only [radialKernel_of_ne h, ModelNorm.coe_toSeminorm]
      rw [htarget]
      exact hstep.congr' (Filter.Eventually.of_forall fun r => by
        simp only [cutoffKernel_def, radialKernel_of_ne h, ModelNorm.coe_toSeminorm])

/-- **The cut-off kernels converge as functions**, in the product topology on
`Sym2 (ℤ^d) → ℝ≥0`. -/
theorem tendsto_cutoffKernel_pi (hK : Tendsto K atTop (𝓝 0)) :
    Tendsto (fun r => cutoffKernel N.toSeminorm K r) atTop
      (𝓝 (radialKernel N.toSeminorm K)) :=
  tendsto_pi_nhds.mpr fun e => tendsto_cutoffKernel_atTop hK e

/-- **A profile of finite range is untouched by the cut-off beyond its range.** If `K` vanishes
on `[R₀, ∞)`, then at every radius `r ≥ R₀` the cut-off kernel `J_r` coincides with the radial
kernel `J`: inside the range the cut-off contributes `K s - K r = K s - 0`, outside it both
kernels vanish. No monotonicity or nonnegativity is needed. -/
theorem cutoffKernel_eq_radialKernel_of_eq_zero_of_le {R₀ r : ℝ} (hR : R₀ ≤ r)
    (hK₀ : ∀ t, R₀ ≤ t → K t = 0) (e : Sym2 (Fin d → ℤ)) :
    cutoffKernel N K r e = radialKernel N K e := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · simp [h]
    · simp only [cutoffKernel_def, radialKernel_of_ne h, ModelNorm.coe_toSeminorm]
      congr 1
      by_cases hs : N (Int.cast ∘ (x - y)) ≤ r
      · rw [cutoffProfile_of_le hs, hK₀ r hR, sub_zero]
      · rw [cutoffProfile_of_lt (not_le.1 hs)]
        exact (hK₀ _ (hR.trans (le_of_lt (not_le.1 hs)))).symm

/-- The power-law profile tends to zero at infinity when its exponent is positive. -/
theorem tendsto_powerLawProfile_atTop {c a : ℝ} (ha : 0 < a) :
    Tendsto (powerLawProfile c a) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => c * x ^ (-a)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).const_mul c
  exact h.congr' (Filter.Eventually.of_forall fun x => rfl)

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

open PercLib.Analysis PercLib.Models.LongRange

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}

/-- **Monotone convergence of the two-point function along a coordinatewise-convergent
increasing family of profiles.** On any countable bond graph, if the open probabilities `q r`
increase in `r`, stay below the limit profile `q` and converge at every pair, then the
probability that `x` and `y` are connected converges to its value at `q`.

The proof is monotone convergence of the finite-domain connection events: `tau q x y` is the
supremum of the probabilities of `x ↔ y inside S n` over a finite exhaustion `S`
(`tau_eq_iSup_localConn`), each of these is continuous in the profile
(`continuous_law_localConn`), and each is at most `tau (q r) x y`. Hence
`tau q x y ≤ ⨆ r, tau (q r) x y`, while `tau (q r) x y ≤ tau q x y` by monotonicity; the
supremum of the increasing family is therefore its limit.

The argument uses that a connection event is the *countable union* of the cylinder events
`localConn (S n) x y`, not merely that it is increasing and measurable: continuity from below at
a fixed profile is what lets the profile-dependence factor through finitely many pairs. An
arbitrary increasing measurable event (for instance "infinitely many pairs are open") does not
allow this reduction, and no such statement is claimed here. -/
theorem tendsto_tau_of_tendsto_profile {V : Type*} [Countable V]
    {q : ℝ → Sym2 V → unitInterval} {qinf : Sym2 V → unitInterval}
    (hmono : Monotone q) (hle : ∀ r, q r ≤ qinf)
    (hconv : ∀ e, Tendsto (fun r => q r e) atTop (𝓝 (qinf e))) (x y : V) :
    Tendsto (fun r => tau (q r) x y) atTop (𝓝 (tau qinf x y)) := by
  classical
  have htau_mono : Monotone fun r => tau (q r) x y := fun r ρ hrρ => tau_mono (hmono hrρ) x y
  have hbdd : ∀ r, tau (q r) x y ≤ tau qinf x y := fun r => tau_mono (hle r) x y
  obtain ⟨S, hS, hcover⟩ := exists_finset_exhaustion (V := V)
  have hS' : Monotone fun n => (S n : Set V) := fun m n hmn => Finset.coe_subset.2 (hS hmn)
  have hcyl : ∀ n, Tendsto (fun r => law (q r) (localConn (S n : Set V) x y))
      atTop (𝓝 (law qinf (localConn (S n : Set V) x y))) := fun n =>
    ((continuous_law_localConn (S n) x y).tendsto qinf).comp (tendsto_pi_nhds.mpr hconv)
  have hsup : (⨆ r, tau (q r) x y) = tau qinf x y := by
    refine le_antisymm (ciSup_le hbdd) ?_
    rw [tau_eq_iSup_localConn qinf (S := fun n => (S n : Set V)) hS' hcover x y]
    refine iSup_le fun n => ?_
    refine le_of_tendsto' (hcyl n) fun r => ?_
    exact (law_localConn_le_tau _ _ _ _).trans (le_iSup (fun r => tau (q r) x y) r)
  have h := tendsto_atTop_iSup htau_mono
  rwa [hsup] at h

/-- **Open-pair probabilities of the cut-off family converge to the uncut ones.** At a fixed
pair, `q_r(e) = 1 - exp (-(β) J_r(e))` tends to `1 - exp (-(β) J(e))` as `r → ∞`, in the subtype
`unitInterval`, whenever `K → 0` at infinity. The degenerate cases `β = 0` and `J e = 0` are
included. -/
theorem tendsto_intensityProfile_cutoffKernel (hK : Tendsto K atTop (𝓝 0)) (β : ℝ≥0)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r => intensityProfile (cutoffKernel N.toSeminorm K r) β e) atTop
      (𝓝 (intensityProfile (radialKernel N.toSeminorm K) β e)) := by
  refine tendsto_subtype_rng.mpr ?_
  have hJ := PercLib.Models.LongRange.tendsto_cutoffKernel_atTop (N := N) hK e
  have hc : Continuous fun x : ℝ≥0 => 1 - Real.exp (-(β : ℝ) * (x : ℝ)) := by fun_prop
  have h := hc.continuousAt.tendsto.comp hJ
  simpa only [Function.comp_def, intensityProfile] using h

/-- The cut-off profiles converge to the uncut profile in the product topology on the space of
open-pair probabilities. -/
theorem tendsto_intensityProfile_cutoffKernel_pi (hK : Tendsto K atTop (𝓝 0)) (β : ℝ≥0) :
    Tendsto (fun r => intensityProfile (cutoffKernel N.toSeminorm K r) β) atTop
      (𝓝 (intensityProfile (radialKernel N.toSeminorm K) β)) :=
  tendsto_pi_nhds.mpr fun e => tendsto_intensityProfile_cutoffKernel hK β e

/-- **Cylinder probabilities converge.** For every finite set `F` of pairs and every set `A` of
sub-configurations of `F`, the probability that the restriction to `F` lies in `A` converges
along the cut-off scale. This is continuity of finite-cylinder probabilities in the profile
(`PercLib.Probability.tendsto_prodBernoulli_cylinder`) applied to the pointwise convergence of
the open-pair probabilities. -/
theorem tendsto_law_cylinder_cutoffKernel (hK : Tendsto K atTop (𝓝 0)) (β : ℝ≥0)
    (F : Finset (Sym2 (Fin d → ℤ))) (A : Set (Set F)) :
    Tendsto (fun r => law (intensityProfile (cutoffKernel N.toSeminorm K r) β)
        {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A}) atTop
      (𝓝 (law (intensityProfile (radialKernel N.toSeminorm K) β)
        {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A})) :=
  PercLib.Probability.tendsto_prodBernoulli_cylinder _
    (intensityProfile (radialKernel N.toSeminorm K) β)
    (fun e => tendsto_intensityProfile_cutoffKernel hK β e) F A

/-- **Finite-domain connection probabilities converge.** For a finite set `S` of vertices, the
probability that `x` and `y` are joined by an open path inside `S` converges along the cut-off
scale, by continuity of `law · (localConn S x y)` in the profile. -/
theorem tendsto_law_localConn_cutoffKernel (hK : Tendsto K atTop (𝓝 0)) (β : ℝ≥0)
    (S : Finset (Fin d → ℤ)) (x y : Fin d → ℤ) :
    Tendsto (fun r => law (intensityProfile (cutoffKernel N.toSeminorm K r) β)
        (localConn (S : Set (Fin d → ℤ)) x y)) atTop
      (𝓝 (law (intensityProfile (radialKernel N.toSeminorm K) β)
        (localConn (S : Set (Fin d → ℤ)) x y))) :=
  ((continuous_law_localConn S x y).tendsto _).comp
    (tendsto_intensityProfile_cutoffKernel_pi hK β)

/-- **Two-point convergence along the cut-off scale.** Under a nonnegative, decreasing profile
tending to `0` at infinity, the probability that `x` and `y` are connected at radius `r` tends to
the uncut probability as `r → ∞`. Both values are `ℝ≥0∞`-valued, so an infinite two-point
function is allowed. This is `tendsto_tau_of_tendsto_profile` at the cut-off family: monotonicity
in the radius is `monotone_cutoffKernel`, the comparison with the uncut profile is
`cutoffKernel_le_radialKernel` (which needs `0 < r`, whence the split at `r = 1`), and the
coordinatewise convergence is `tendsto_intensityProfile_cutoffKernel`.

Precisely, `hKnn` is used *only* for the comparison `q_r ≤ q`, i.e. for the second hypothesis of
`tendsto_tau_of_tendsto_profile`; the convergence itself needs only `hKanti` and `hK`, because a
monotone family with a coordinatewise limit is automatically below that limit. The comparison is
kept as a hypothesis of the general lemma on purpose: it is the form in which
`cutoffKernel_le_radialKernel` is available for the truncated kernel, and it makes the bound
independent of the limiting profile's existence. -/
theorem tendsto_tau_cutoffKernel (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi 0)) (hK : Tendsto K atTop (𝓝 0)) (β : ℝ≥0)
    (x y : Fin d → ℤ) :
    Tendsto (fun r => tau (intensityProfile (cutoffKernel N.toSeminorm K r) β) x y) atTop
      (𝓝 (tau (intensityProfile (radialKernel N.toSeminorm K) β) x y)) := by
  have hmono : Monotone fun r => intensityProfile (cutoffKernel N.toSeminorm K r) β :=
    fun r ρ hrρ => intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKanti e hrρ) β
  have hle : ∀ r, intensityProfile (cutoffKernel N.toSeminorm K r) β ≤
      intensityProfile (radialKernel N.toSeminorm K) β := by
    intro r
    rcases le_or_gt r 1 with hr | hr
    · exact (intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKanti e hr) β).trans
        (intensityProfile_le_of_le
          (fun e => cutoffKernel_le_radialKernel hKnn one_pos e) β)
    · exact intensityProfile_le_of_le
        (fun e => cutoffKernel_le_radialKernel hKnn (one_pos.trans hr) e) β
  exact tendsto_tau_of_tendsto_profile hmono hle
    (fun e => tendsto_intensityProfile_cutoffKernel hK β e) x y

/-- **Finite range: the laws coincide from the range on.** If `K` vanishes on `[R₀, ∞)` then at
every radius `r ≥ R₀` the law of the radius-`r` configuration is the uncut law, so every event
has the same probability: the model does not depend on the radius once the radius is at least the
range. -/
theorem law_cutoffKernel_eq_of_eq_zero_of_le {R₀ r : ℝ} (hR : R₀ ≤ r)
    (hK₀ : ∀ t, R₀ ≤ t → K t = 0) (β : ℝ≥0) :
    law (intensityProfile (cutoffKernel N.toSeminorm K r) β) =
      law (intensityProfile (radialKernel N.toSeminorm K) β) := by
  have hker : cutoffKernel N.toSeminorm K r = radialKernel N.toSeminorm K :=
    funext fun e =>
      PercLib.Models.LongRange.cutoffKernel_eq_radialKernel_of_eq_zero_of_le (N := N) hR hK₀ e
  rw [hker]

/-- **Finite range: the two-point function is exactly the uncut one** at every radius at least
the range. -/
theorem tau_cutoffKernel_eq_of_eq_zero_of_le {R₀ r : ℝ} (hR : R₀ ≤ r)
    (hK₀ : ∀ t, R₀ ≤ t → K t = 0) (β : ℝ≥0) (x y : Fin d → ℤ) :
    tau (intensityProfile (cutoffKernel N.toSeminorm K r) β) x y =
      tau (intensityProfile (radialKernel N.toSeminorm K) β) x y := by
  rw [tau, tau, law_cutoffKernel_eq_of_eq_zero_of_le hR hK₀ β]

/-- Non-vacuity of the finite-range identity: the profile that is `1` on `(0, 1]` and `0`
elsewhere is untouched by the cut-off at radius `2`, at the pair `{0, 1}` of `ℤ` with the sup
norm. -/
example :
    cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun t => if 0 < t ∧ t ≤ 1 then 1 else 0) 2
        s(0, fun _ => 1) =
      radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun t => if 0 < t ∧ t ≤ 1 then 1 else 0)
        s(0, fun _ => 1) :=
  PercLib.Models.LongRange.cutoffKernel_eq_radialKernel_of_eq_zero_of_le
    (N := ModelNorm.ofNorm (Fin 1 → ℝ)) (R₀ := 2) (r := 2) le_rfl
    (fun t ht => by
      have h1 : ¬ t ≤ 1 := by linarith
      simp [h1])
    _

/-- **Non-vacuity of the two-point limit.** For the power law `s ↦ c s^(-(d+α))` of
Definition I.1.3 with `c ≥ 0` and `α > 0` (so the profile is nonnegative, decreasing and
vanishes at infinity), the uncut sup-norm kernel is the limit of its cut-offs at every pair. No
summability or temperature hypothesis is used, and `d` is arbitrary. -/
theorem tendsto_tau_cutoffKernel_powerLaw {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (β : ℝ≥0) (x y : Fin d → ℤ) :
    Tendsto (fun r => tau (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile c ((d : ℝ) + α)) r) β) x y) atTop
      (𝓝 (tau (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile c ((d : ℝ) + α))) β) x y)) :=
  tendsto_tau_cutoffKernel (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun t ht => mul_nonneg hc (Real.rpow_nonneg ht.le _))
    (PercLib.Models.LongRange.antitoneOn_powerLawProfile hc (by positivity))
    (PercLib.Models.LongRange.tendsto_powerLawProfile_atTop (by positivity)) β x y

end PercLib.Percolation.Bond
