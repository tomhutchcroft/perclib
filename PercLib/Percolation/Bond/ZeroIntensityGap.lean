/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs written for the gap-factorisation input of T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, Lemma I.4.1. No upstream proof is copied and no definition is
added.
-/
module

public import PercLib.Models.LongRange.TruncatedMoments
public import PercLib.Models.LongRange.CutoffMonotone

/-!
# The gap factorisation `hfac` is false at zero intensity

The conditional small-tail estimate of `PercLib.Percolation.Bond.SmallTailMass` consumes one
mathematical input, the *gap factorisation* `hfac`: for every scale `r` of an interval and every
pair `(x, y)` of vertices,

`∫ 1(N(y - x) < r) · 1(x ∈ K_o) · 1(y ∉ K_o) · ((|K_o| + |K_y|)^p - |K_o|^p) ≤ C · min (τ x) (τ y)`

where `K_o = cluster ω o`, `K_y = cluster ω y` and `τ v = P(v ∈ K_o)`. This file shows that this
statement is **false at intensity `β = 0`**, for every constant `C` and every scale `r > 0` at
which some lattice pair sits strictly inside the radius: it is not a consequence of the model at
zero intensity, and the bridge of `SmallTailMass` is usable only where the two-point function does
not degenerate.

The evaluation is elementary. At `β = 0` the law is the Dirac mass at the empty configuration, so
a.s. every cluster is a singleton. For the pair `(o, y)` with `y ≠ o` and `N (y - o) < r` the
integrand is `1 · 1 · 1 · ((1 + 1)^p - 1^p) = 2^p - 1 > 0`, while `τ y = 0` because `y` is not in
the (singleton) cluster of `o`; hence the right-hand side is `0`. For `x ≠ o` the left-hand side
vanishes, so the obstruction is exactly the row of the root.

The second half of the file records the positive fact that makes the failure non-vacuous for the
conditional interface: at `β = 0` the consumed conclusion `htail` holds *unconditionally*, because
the derivative weight `cw` carries a factor `β` and therefore vanishes identically. So `hfac` is
not necessary for `htail`; the conditional bridge simply does not cover `β = 0`.

## Main results

* `PercLib.Percolation.Bond.law_zero`: at zero intensity the configuration law is `Measure.dirac ∅`.
* `PercLib.Percolation.Bond.lintegral_cluster_indicator_law_zero`: the clusters are singletons and
  `τ v = 1{v = o}` at zero intensity.
* `PercLib.Percolation.Bond.lintegral_hfac_integrand_zero_intensity`: the `hfac` left-hand side at
  `(o, y)` equals `2^p - 1`.
* `PercLib.Percolation.Bond.not_hfac_zero_intensity`: the exact `hfac` statement of
  `SmallTailMass` fails at `β = 0` for every `C`.
* `PercLib.Percolation.Bond.not_hfac_zero_intensity_one_dim`: its non-vacuity witness in `d = 1`.
* `PercLib.Percolation.Bond.exists_nhds_htail_of_intensity_eq_zero`: the exact `htail` conclusion
  holds at `β = 0` with no gap factorisation, no susceptibility and no moment hypothesis.
* `PercLib.Percolation.Bond.chi_zero_intensity` and
  `PercLib.Percolation.Bond.exists_finset_norm_lt`: the remaining hypotheses `hχ` and `hS` of the
  conditional bridge also hold at `β = 0`, so the gap factorisation is the single failing input.
* `PercLib.Percolation.Bond.rootMoment_zero_intensity` and
  `PercLib.Percolation.Bond.hasDerivAt_zero_intensity`: at `β = 0` the truncated root moment is the
  constant `1` in the scale, so the derivative statement of Lemma I.4.1 holds there for the trivial
  reason that both sides vanish.

## What this does and does not show

* It does **not** give a counterexample at any `β ≠ 0`. At `β > 0` the pair `(o, y)` has `τ y > 0`
  and the computation above says nothing; the only degeneracy verified here is `β = 0`.
* It does **not** use, or need, finiteness of any moment: at `β = 0` every cluster is a singleton
  and both sides of the failed inequality are finite. The failure is a degeneracy of the
  two-point function, not a moment or infinite-cluster phenomenon.
* The only derivative result here is the trivial zero-intensity boundary; no `htail` or derivative
  is proved at `β ≠ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

open PercLib.Probability PercLib.Analysis

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)}

/-- **The law at zero intensity is the Dirac mass at the empty configuration.** -/
theorem law_zero (J : Sym2 (Fin d → ℤ) → ℝ≥0) :
    law (intensityProfile J (0 : ℝ≥0)) = Measure.dirac (∅ : Config (Fin d → ℤ)) := by
  have hz : intensityProfile J (0 : ℝ≥0) = (fun _ => (0 : unitInterval)) := by
    funext e
    exact intensityProfile_zero J e
  rw [hz, law, ← PercLib.Probability.prodBernoulli_deterministic (∅ : Set (Sym2 (Fin d → ℤ)))]
  simp

open Classical in
/-- **The two-point function at zero intensity**: `τ v = 1{v = o}`. -/
theorem lintegral_cluster_indicator_law_zero (o x : Fin d → ℤ) (J : Sym2 (Fin d → ℤ) → ℝ≥0) :
    ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
      ∂(law (intensityProfile J (0 : ℝ≥0))) = if x = o then 1 else 0 := by
  rw [law_zero]
  rw [MeasureTheory.lintegral_dirac (∅ : Config (Fin d → ℤ))]
  by_cases h : x = o
  · subst h; simp [cluster_empty]
  · simp [h, cluster_empty]

/-- The radial weight of a non-diagonal pair inside the cut-off radius is `1`. -/
theorem radialKernel_indicator_coe_eq_one {r : ℝ} {x y : Fin d → ℤ} (hxy : x ≠ y)
    (hlt : N (Int.cast ∘ (x - y)) < r) :
    (PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞)
      = 1 := by
  rw [PercLib.Models.LongRange.radialKernel_of_ne (N := N)
    (K := fun s => if s < r then 1 else 0) hxy]
  simp [hlt]

/-- A pair at distance `< r` in the direction `y - o` is inside the ball written with `o - y`. -/
theorem norm_neg_sub_lt {r : ℝ} {o y : Fin d → ℤ} (h : N (Int.cast ∘ (y - o)) < r) :
    N (Int.cast ∘ (o - y)) < r := by
  have hsub : (Int.cast ∘ (o - y) : Fin d → ℝ) = -(Int.cast ∘ (y - o)) := by
    rw [PercLib.Models.LongRange.intCast_comp_sub, PercLib.Models.LongRange.intCast_comp_sub]
    ext i; simp [sub_eq_neg_add]
  rw [hsub, map_neg_eq_map]
  exact h

/-- `2^p - 1` is positive for `p ≥ 1` in the extended nonnegative reals. -/
theorem two_pow_sub_one_pos (p : ℕ) (hp : 1 ≤ p) : (0 : ℝ≥0∞) < (2 : ℝ≥0∞) ^ p - 1 := by
  have h : (1 : ℝ≥0∞) < 2 ^ p := one_lt_pow₀ (by norm_num) (by omega)
  exact tsub_pos_of_lt h

open Classical in
/-- **The `hfac` integrand at `β = 0`, on the row of the root.** For `y ≠ o` inside the cut-off
radius the integral of the gap-factorisation integrand is `2^p - 1`, independently of the profile
`K` and of the scale (only `N (y - o) < r` is used). -/
theorem lintegral_hfac_integrand_zero_intensity {K : ℝ → ℝ} {r : ℝ} {o y : Fin d → ℤ}
    (hy : y ≠ o) (hNy : N (Int.cast ∘ (y - o)) < r) (p : ℕ) :
    ∫⁻ ω, (PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0)
        (s(o, y)) : ℝ≥0∞) *
      ((if o ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p))
      ∂(law (intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) (0 : ℝ≥0)))
      = (2 : ℝ≥0∞) ^ p - 1 := by
  have hxy : o ≠ y := fun h => hy h.symm
  rw [law_zero]
  rw [MeasureTheory.lintegral_dirac (∅ : Config (Fin d → ℤ))]
  have hk : (PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0)
      (s(o, y)) : ℝ≥0∞) = 1 := radialKernel_indicator_coe_eq_one hxy (norm_neg_sub_lt hNy)
  have hbase : (1 : ℝ≥0∞) + 1 = 2 := by norm_num
  rw [cluster_empty o, cluster_empty y, Set.encard_singleton, Set.encard_singleton, hk]
  simp [hy, hbase]

open Classical in
/-- **Off the row of the root the `hfac` integrand vanishes at `β = 0`.** -/
theorem lintegral_hfac_integrand_zero_intensity_of_ne {K : ℝ → ℝ} {r : ℝ} {o x y : Fin d → ℤ}
    (hx : x ≠ o) (p : ℕ) :
    ∫⁻ ω, (PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0)
        (s(x, y)) : ℝ≥0∞) *
      ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω o then 0 else 1) *
        ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω o).encard : ℝ≥0∞) ^ p))
      ∂(law (intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) (0 : ℝ≥0)))
      = 0 := by
  rw [law_zero]
  rw [MeasureTheory.lintegral_dirac (∅ : Config (Fin d → ℤ))]
  rw [cluster_empty o]
  simp [hx]

open Classical in
/-- **The exact gap factorisation `hfac` of `SmallTailMass` is false at zero intensity.** For
every constant `C`, every pair of scales `u < r < v`, and every root `o` with a lattice neighbour
`y ≠ o` strictly inside the radius, the uniformly quantified statement consumed by
`SmallTailMass.exists_nhds_htail_of_factorization` — with the same quantifier order and the law at
`β = 0` — fails. -/
theorem not_hfac_zero_intensity {K : ℝ → ℝ} (o : Fin d → ℤ) {u v r : ℝ} (hur : u < r)
    (hrv : r < v) {p : ℕ} (hp : 1 ≤ p) {y : Fin d → ℤ} (hy : y ≠ o)
    (hNy : N (Int.cast ∘ (y - o)) < r) (C : ℝ≥0∞) :
    ¬ (∀ r ∈ Ioo u v, ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (PercLib.Models.LongRange.radialKernel N (fun s => if s < r then 1 else 0)
          (s(x, y)) : ℝ≥0∞) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) (0 : ℝ≥0))) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) N K r)
            (0 : ℝ≥0))))
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (PercLib.Models.LongRange.cutoffKernel (d := d) N K r)
            (0 : ℝ≥0))))) := by
  intro hfac
  have h := hfac r ⟨hur, hrv⟩ o y
  rw [lintegral_hfac_integrand_zero_intensity hy hNy p,
    lintegral_cluster_indicator_law_zero o o _,
    lintegral_cluster_indicator_law_zero o y _] at h
  have ho1 : (if o = o then (1 : ℝ≥0∞) else 0) = 1 := by simp
  have hmin : min (1 : ℝ≥0∞) (if y = o then (1 : ℝ≥0∞) else 0) = 0 := by simp [hy]
  rw [ho1, hmin, mul_zero] at h
  exact absurd h (not_le.2 (two_pow_sub_one_pos p hp))

/-- **Non-vacuity of the pair hypothesis at an `r > 1` scale.** In `d = 1` with the standard model
norm, the lattice point `y = (1)` is at distance `1 < 3/2` from the origin, so
`not_hfac_zero_intensity` applies at the window `Ioo 1 2` and the scale `r = 3/2`. -/
theorem exists_lattice_pair_lt_three_halves :
    ∃ y : Fin 1 → ℤ, y ≠ 0 ∧
      (ModelNorm.ofNorm (Fin 1 → ℝ)) (Int.cast ∘ (y - 0)) < (3/2 : ℝ) := by
  refine ⟨Pi.single 0 1, by simp, ?_⟩
  have h : (Int.cast ∘ (Pi.single (0 : Fin 1) 1 - 0) : Fin 1 → ℝ) = (fun _ => 1) := by
    funext i
    fin_cases i
    simp
  rw [h]
  norm_num

open Classical in
/-- **The consumed `htail` conclusion holds at zero intensity, with no gap factorisation.**

This is the exact conclusion of `SmallTailMass.exists_nhds_htail_of_factorization` (the `∀ r₀, ∀ ε`
statement with the `ℝ`-valued flux series over the complement of a finite pair set) at `β = 0`. The
derivative weight carries a factor `β`, so it vanishes identically and every summand is `0`: no
`hfac`, no susceptibility `hχ`, no moment hypothesis and no corner condition is needed. Together
with `not_hfac_zero_intensity` this shows that the gap factorisation is *sufficient but not
necessary* for `htail`, and that the conditional bridge has a genuine gap at `β = 0` which this
theorem closes by a separate argument. -/
theorem exists_nhds_htail_of_intensity_eq_zero {K K' : ℝ → ℝ} {β : ℝ≥0} (hβ : β = 0)
    (o : Fin d → ℤ) (p : ℕ) (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (PercLib.Models.LongRange.radialKernel N
        (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) *
        (PercLib.Models.LongRange.cutoffKernel (d := d) N K r e : ℝ))))
    {u v : ℝ} :
    ∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile
            (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) β))‖ ≤ ε := by
  subst hβ
  intro r₀ _ ε hε
  exact ⟨univ, univ_mem, ∅, fun r _ => by simpa [hcw] using le_of_lt hε⟩

open Classical in
/-- **Concrete refutation at `d = 1`, `p = 1`, `C = 0` and the `r > 1` scale `r = 3/2`**, in the
root-fixed (`o = 0`) form of the gap factorisation, which is the form consumed by
`SmallTailMass.exists_window_uniform_window_tail_le_of_factorization`. -/
theorem not_hfac_zero_intensity_one_dim (K : ℝ → ℝ) :
    ¬ (∀ r ∈ Ioo (1 : ℝ) 2, ∀ x y : Fin 1 → ℤ,
      ∫⁻ ω, (PercLib.Models.LongRange.radialKernel (ModelNorm.ofNorm (Fin 1 → ℝ))
          (fun s => if s < r then 1 else 0) (s(x, y)) : ℝ≥0∞) *
        ((if x ∈ cluster ω 0 then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω 0 then 0 else 1) *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ 1 -
            ((cluster ω 0).encard : ℝ≥0∞) ^ 1))
        ∂(law (intensityProfile
          (PercLib.Models.LongRange.cutoffKernel (d := 1)
            (ModelNorm.ofNorm (Fin 1 → ℝ)) K r) (0 : ℝ≥0))) ≤
      (0 : ℝ≥0∞) * min (∫⁻ ω, (if x ∈ cluster ω 0 then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile
            (PercLib.Models.LongRange.cutoffKernel (d := 1)
              (ModelNorm.ofNorm (Fin 1 → ℝ)) K r) (0 : ℝ≥0))))
        (∫⁻ ω, (if y ∈ cluster ω 0 then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile
            (PercLib.Models.LongRange.cutoffKernel (d := 1)
              (ModelNorm.ofNorm (Fin 1 → ℝ)) K r) (0 : ℝ≥0))))) :=
  fun h => not_hfac_zero_intensity (N := ModelNorm.ofNorm (Fin 1 → ℝ)) (K := K) (o := 0)
    (u := 1) (v := 2) (r := 3/2) (p := 1) (y := Pi.single 0 1) (C := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp)
    (by
      have h : (Int.cast ∘ (Pi.single (0 : Fin 1) 1 - 0) : Fin 1 → ℝ) = (fun _ => 1) := by
        funext i
        fin_cases i
        simp
      rw [h]
      norm_num) h


open Classical in
/-- **At zero intensity the truncated `p`-th root moment is the constant `1`.** Every cluster is a
singleton whatever the cut-off scale, so the truncated moment does not depend on `r` at all. -/
theorem rootMoment_zero_intensity (o : Fin d → ℤ) (p : ℕ) (K : ℝ → ℝ) (r : ℝ) :
    ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile
        (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) (0 : ℝ≥0))) = 1 := by
  rw [law_zero, MeasureTheory.integral_dirac
    (fun ω => (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal) (∅ : Config (Fin d → ℤ))]
  rw [cluster_empty o, Set.encard_singleton]
  simp

open Classical in
/-- **Lemma I.4.1 at zero intensity holds, for the trivial reason.** The truncated moment is the
constant `1` in the scale, so its derivative is `0`; the derivative formula on the right carries
the factor `β = 0` and is `0` as well. This is the positive counterpart of
`not_hfac_zero_intensity`: the paper's statement at `β = 0` is true, while the *intermediate*
gap factorisation used by the conditional bridge is false there. -/
theorem hasDerivAt_zero_intensity {K : ℝ → ℝ} (o : Fin d → ℤ) (p : ℕ) (r₀ : ℝ) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile
          (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) (0 : ℝ≥0)))) (0 : ℝ) r₀ := by
  have hfun : (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile
        (PercLib.Models.LongRange.cutoffKernel (d := d) N K r) (0 : ℝ≥0))))
      = fun _ => (1 : ℝ) := by
    funext r
    exact rootMoment_zero_intensity o p K r
  rw [hfun]
  exact hasDerivAt_const (c := (1 : ℝ)) (x := r₀)

open Classical in
/-- **The susceptibility at zero intensity is `1`**: the `hχ` hypothesis of the conditional bridge
is satisfied at `β = 0`, for every scale. -/
theorem chi_zero_intensity (o : Fin d → ℤ) (J : Sym2 (Fin d → ℤ) → ℝ≥0) :
    chi (intensityProfile J (0 : ℝ≥0)) o = 1 := by
  rw [chi, law_zero, MeasureTheory.lintegral_dirac (∅ : Config (Fin d → ℤ)),
    cluster_empty o, Set.encard_singleton]
  simp

/-- **The finite window `S` of the conditional bridge exists at every scale.** This is the `hS`
hypothesis: the lattice points of `N`-norm below `v` are finite, and `0` covers the root. -/
theorem exists_finset_norm_lt (v : ℝ) :
    ∃ S : Finset (Fin d → ℤ), ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S := by
  refine ⟨insert 0 (PercLib.Models.LongRange.finite_norm_lt N v).toFinset, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  · exact Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 ⟨hz0, hz⟩)

end PercLib.Percolation.Bond
