/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The corner of the cut-off kernel at `r = ‖x − y‖`: one-sided derivatives of the cut-off
profile of Definition I.1.5 and of the edge probability of the cut-off bond law, adapted from the
repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files `PercLib/CriticalLRP/CutoffCorner.lean`
(theorems `hasDerivWithinAt_cutoffProfile_Iic/Ioi`, `not_hasDerivAt_cutoffProfile`,
`hasDerivWithinAt_cutoffEdgeProbability_Iic/Ioi`, `not_hasDerivAt_cutoffEdgeProbability`) and
`PercLib/CriticalLRP/KernelGeometry.lean` (`hasDerivAt_cutoffProfile`,
`hasDerivAt_cutoffProfile_of_lt`) and `PercLib/CriticalLRP/CutoffRusso.lean`; licence Apache-2.0
as declared in those file headers; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source's `longRangeEdgeProbability β J = 1 - exp (-(β * J))` on unbundled real
parameters is kept as the function `r ↦ 1 - exp (-(β * cutoffProfile K r s))` of the profile
value (`hasDerivWithinAt_one_sub_exp_cutoffProfile_Iic/Ioi`,
`not_hasDerivAt_one_sub_exp_cutoffProfile`), and the bundled bond-law edge probability
`(intensityProfile (cutoffKernel N K r) β e : ℝ)` of
`PercLib/Percolation/Bond/Intensity/Defs.lean` is deduced from it at a non-diagonal pair
`e = s(x, y)` and `r = N (x - y)`, where the truncation `Real.toNNReal` of `radialKernel` needs
`AntitoneOn K (Ioi 0)`. The cutoff Russo statements use finite windows of the bond model
and the existing `FiniteProfile` and infinite-volume Russo APIs, replacing the source's pivotal
mass by the closed-edge exponential factor and a two-sided forced-edge difference. The proofs
of the corner statements are from the explicit piecewise formula of `cutoffProfile`.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Models.LongRange.InfiniteVolumeRusso
public import PercLib.Percolation.Bond.Intensity.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The corner of the cut-off profile at `r = s`

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Definition I.1.5. The
cut-off profile `J_r(s) = ∫_s^r |J'| = K s - K r` for `s ≤ r` and `0` for `s > r` is not
differentiable at `r = s`: its left derivative is `0` while its right derivative is
`-K'(s) = |J'(s)|` for a decreasing profile `K`. Consequently the two-sided derivative in
Lemma I.4.1 does not exist at a scale `r` equal to an edge length of the lattice, and the phrase
"for every `r > 0`" in the paper has to be read as "for every `r` outside the locally finite set
of edge lengths" (equivalently, almost everywhere), which is what its use as a differential
equation requires.

## Main results

### The profile

* `hasDerivWithinAt_cutoffProfile_Iic`: the profile vanishes on `(-∞, s]`, so its left derivative
  at `s` is `0`.
* `hasDerivWithinAt_cutoffProfile_Ioi` and `not_hasDerivAt_cutoffProfile`: for `K` differentiable
  at `s` with derivative `-K'`, the right derivative on `(s, ∞)` is `K'`, and no two-sided
  derivative exists when `K' ≠ 0`.
* `hasDerivAt_cutoffProfile`, `hasDerivAt_cutoffProfile_of_lt`: away from the corner the profile
  is differentiable in the scale, so the corner is the only obstruction.

### The edge probability

* `hasDerivWithinAt_one_sub_exp_cutoffProfile_Iic/Ioi` and
  `not_hasDerivAt_one_sub_exp_cutoffProfile`: the same three statements for
  `r ↦ 1 - exp (-(β J_r(s)))` with `J_r(s) = K s - K r` for `s ≤ r` and `0` for `s > r`, the open
  probability of an edge of length `s` under the cut-off kernel `J_r`, with no hypothesis beyond
  differentiability of `K`.
* `hasDerivWithinAt_cutoffEdgeProbability_Iic/Ioi` and `not_hasDerivAt_cutoffEdgeProbability`:
  the same three statements for the open probability
  `r ↦ (intensityProfile (cutoffKernel N K r) β s(x, y) : ℝ)` of the pair `{x, y}` under the
  cut-off bond law, whose corner is at the edge length `r = N (x - y)`. Its left derivative there
  is `0`, its right derivative is `β K'`, and it is not differentiable when `β K' ≠ 0`.
* `hasDerivAt_cutoffEdgeProbability_if`: the source's exact derivative formula away from
  the corner, for `1 - exp (-β cutoffProfile K r s)`;
* `hasDerivAt_expectation_cutoff`: the finite-window cutoff Russo formula on the bond law,
  with the closed-edge factor made explicit;
* `hasDerivAt_expectation_cutoff_cluster`, `hasDerivAt_expectation_cutoff_finite`: the
  cluster-window and literal finite-edge formulations of the same identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology unitInterval

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}

/-! ## The profile -/

/-- The cut-off profile is identically zero to the *left* of `r = s`, so its left derivative at
`s` vanishes. -/
theorem hasDerivWithinAt_cutoffProfile_Iic {K : ℝ → ℝ} {s : ℝ} :
    HasDerivWithinAt (fun r' => cutoffProfile K r' s) 0 (Iic s) s := by
  refine (hasDerivWithinAt_const (x := s) (s := Iic s) (c := (0 : ℝ))).congr ?_ ?_
  · intro r' hr'
    rcases lt_or_eq_of_le (show r' ≤ s from hr') with h | h
    · rw [cutoffProfile_of_lt h]
    · subst h
      rw [cutoffProfile_of_le le_rfl, sub_self]
  · rw [cutoffProfile_of_le le_rfl, sub_self]

/-- For `r > s` the cut-off profile is `K s − K r`, so its right derivative at `s` is `−K'(s)`,
which is `|J'(s)|` when `K' = −|J'|`. -/
theorem hasDerivWithinAt_cutoffProfile_Ioi {K : ℝ → ℝ} {K' s : ℝ}
    (hK : HasDerivAt K (-K') s) :
    HasDerivWithinAt (fun r' => cutoffProfile K r' s) K' (Ioi s) s := by
  have hder : HasDerivAt (fun r' => K s - K r') K' s := by
    simpa using hK.const_sub (K s)
  refine hder.hasDerivWithinAt.congr ?_ ?_
  · intro r' hr'
    rw [cutoffProfile_of_le (le_of_lt hr')]
  · rw [cutoffProfile_of_le le_rfl]

/-- **The cut-off profile has a genuine corner at `r = s`**: the two-sided derivative does not
exist when `K'(s) ≠ 0`. -/
theorem not_hasDerivAt_cutoffProfile {K : ℝ → ℝ} {K' s L : ℝ}
    (hK : HasDerivAt K (-K') s) (hK' : K' ≠ 0) :
    ¬ HasDerivAt (fun r' => cutoffProfile K r' s) L s := by
  intro h
  have hleft : HasDerivWithinAt (fun r' => cutoffProfile K r' s) L (Iic s) s :=
    h.hasDerivWithinAt
  have hleft0 : HasDerivWithinAt (fun r' => cutoffProfile K r' s) 0 (Iic s) s :=
    hasDerivWithinAt_cutoffProfile_Iic
  have e1 : derivWithin (fun r' => cutoffProfile K r' s) (Iic s) s = L :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic s)
  have e0 : derivWithin (fun r' => cutoffProfile K r' s) (Iic s) s = 0 :=
    hleft0.derivWithin (uniqueDiffWithinAt_Iic s)
  have hL : L = 0 := by rw [← e1, e0]
  subst hL
  have hright : HasDerivWithinAt (fun r' => cutoffProfile K r' s) K' (Ioi s) s :=
    hasDerivWithinAt_cutoffProfile_Ioi hK
  have hright0 : HasDerivWithinAt (fun r' => cutoffProfile K r' s) 0 (Ioi s) s :=
    h.hasDerivWithinAt
  have e2 : derivWithin (fun r' => cutoffProfile K r' s) (Ioi s) s = K' :=
    hright.derivWithin (uniqueDiffWithinAt_Ioi s)
  have e3 : derivWithin (fun r' => cutoffProfile K r' s) (Ioi s) s = 0 :=
    hright0.derivWithin (uniqueDiffWithinAt_Ioi s)
  exact hK' (by rw [← e2, e3])

/-- Away from the corner, above it: for `s < r` the cut-off profile is `K s − K r` near `r`, so
its derivative in the scale at `r` is `K'` when `−K'` is the derivative of `K`. -/
theorem hasDerivAt_cutoffProfile {K : ℝ → ℝ} {K' r s : ℝ} (hsr : s < r)
    (hK : HasDerivAt K (-K') r) :
    HasDerivAt (fun r' => cutoffProfile K r' s) K' r := by
  have hder : HasDerivAt (fun r' => K s - K r') K' r := by
    simpa only [neg_neg] using hK.const_sub (K s)
  refine hder.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hsr] with r' hr'
  rw [cutoffProfile_of_le hr'.le]

/-- Away from the corner, below it: for `r < s` the cut-off profile vanishes near `r`, so its
derivative in the scale at `r` vanishes. -/
theorem hasDerivAt_cutoffProfile_of_lt {K : ℝ → ℝ} {r s : ℝ} (hrs : r < s) :
    HasDerivAt (fun r' => cutoffProfile K r' s) 0 r := by
  refine (hasDerivAt_const (x := r) (c := (0 : ℝ))).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hrs] with r' hr'
  rw [cutoffProfile_of_lt hr']

/-- Non-vacuity: the cut-off profile of the power law `s ↦ s⁻²` has a genuine corner at the
scale `s = 1`, since `s ↦ s⁻²` is differentiable at `1` with derivative `-2`. -/
example (L : ℝ) : ¬ HasDerivAt (fun r' => cutoffProfile (powerLawProfile 1 2) r' 1) L 1 := by
  have hK : HasDerivAt (powerLawProfile 1 2) (-2) 1 := by
    have h : HasDerivAt (fun t : ℝ => t ^ (-2 : ℝ)) ((-2 : ℝ) * (1 : ℝ) ^ ((-2 : ℝ) - 1)) 1 :=
      Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
    have h' : HasDerivAt (fun t : ℝ => powerLawProfile 1 2 t) (-2) 1 := by
      simpa only [powerLawProfile, one_mul, mul_one, Real.one_rpow] using h
    exact h'
  exact not_hasDerivAt_cutoffProfile (K' := 2) hK (by norm_num)

/-! ## The edge probability as a function of the profile value

The source's edge probability of an edge of length `s` under the cut-off kernel is
`longRangeEdgeProbability β (cutoffProfile K r s) = 1 - exp (-(β (K s - K r)))` for `s ≤ r` and
`1 - exp 0 = 0` for `s > r`. It therefore has the same corner at `r = s` as the profile, with
the derivative scaled by `β` and by the factor `exp 0 = 1` at the corner. -/

/-- The cut-off edge probability of an edge of length `s` vanishes on `(-∞, s]`, so its left
derivative at the corner `r = s` vanishes. -/
theorem hasDerivWithinAt_one_sub_exp_cutoffProfile_Iic {K : ℝ → ℝ} {s β : ℝ} :
    HasDerivWithinAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) 0 (Iic s) s := by
  refine (hasDerivWithinAt_const (x := s) (s := Iic s) (c := (0 : ℝ))).congr ?_ ?_
  · intro r' hr'
    rcases lt_or_eq_of_le (show r' ≤ s from hr') with h | h
    · rw [cutoffProfile_of_lt h]
      simp
    · subst h
      rw [cutoffProfile_of_le le_rfl, sub_self]
      simp
  · rw [cutoffProfile_of_le le_rfl, sub_self]
    simp

/-- For `r > s` the cut-off edge probability of an edge of length `s` is
`1 - exp (-(β (K s - K r)))`, so its right derivative at the corner `r = s` is `β (-K'(s))`,
i.e. `β |J'(s)|` for a profile with `K' = −|J'|`. -/
theorem hasDerivWithinAt_one_sub_exp_cutoffProfile_Ioi {K : ℝ → ℝ} {K' s β : ℝ}
    (hK : HasDerivAt K (-K') s) :
    HasDerivWithinAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) (β * K')
      (Ioi s) s := by
  have hder : HasDerivAt (fun r' => 1 - Real.exp (-(β) * (K s - K r'))) (β * K') s := by
    have h1 : HasDerivAt (fun r' : ℝ => K s - K r') K' s := by
      simpa using hK.const_sub (K s)
    have h2 : HasDerivAt (fun r' : ℝ => -(β) * (K s - K r')) ((-(β)) * K') s :=
      h1.const_mul (-(β))
    have h3 : HasDerivAt (fun r' : ℝ => Real.exp (-(β) * (K s - K r')))
        (Real.exp 0 * ((-(β)) * K')) s := by
      simpa using h2.exp
    have h4 : HasDerivAt (fun r' : ℝ => 1 - Real.exp (-(β) * (K s - K r')))
        (0 - Real.exp 0 * ((-(β)) * K')) s :=
      (hasDerivAt_const (x := s) (c := (1 : ℝ))).sub h3
    have hval : (0 : ℝ) - Real.exp 0 * ((-(β)) * K') = β * K' := by
      rw [Real.exp_zero]
      ring
    rw [hval] at h4
    exact h4
  refine hder.hasDerivWithinAt.congr ?_ ?_
  · intro r' hr'
    rw [cutoffProfile_of_le hr'.le]
  · rw [cutoffProfile_of_le le_rfl, sub_self]

/-- **The cut-off edge probability has a genuine corner at the edge length**: it is not
differentiable in the scale at `r = s` when `β K'(s) ≠ 0`. -/
theorem not_hasDerivAt_one_sub_exp_cutoffProfile {K : ℝ → ℝ} {K' s β L : ℝ}
    (hK : HasDerivAt K (-K') s) (hβK' : β * K' ≠ 0) :
    ¬ HasDerivAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) L s := by
  intro h
  have hleft : HasDerivWithinAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) L
      (Iic s) s := h.hasDerivWithinAt
  have hleft0 : HasDerivWithinAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) 0
      (Iic s) s := hasDerivWithinAt_one_sub_exp_cutoffProfile_Iic
  have e1 : derivWithin (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) (Iic s) s = L :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic s)
  have e0 : derivWithin (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) (Iic s) s = 0 :=
    hleft0.derivWithin (uniqueDiffWithinAt_Iic s)
  have hL : L = 0 := by rw [← e1, e0]
  subst hL
  have hright : HasDerivWithinAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s))
      (β * K') (Ioi s) s := hasDerivWithinAt_one_sub_exp_cutoffProfile_Ioi hK
  have hright0 : HasDerivWithinAt (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) 0
      (Ioi s) s := h.hasDerivWithinAt
  have e2 : derivWithin (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) (Ioi s) s
      = β * K' := hright.derivWithin (uniqueDiffWithinAt_Ioi s)
  have e3 : derivWithin (fun r' => 1 - Real.exp (-(β) * cutoffProfile K r' s)) (Ioi s) s = 0 :=
    hright0.derivWithin (uniqueDiffWithinAt_Ioi s)
  exact hβK' (by rw [← e2, e3])

/-! ## The edge probability of the cut-off bond law -/

/-- The edge probability of the bond law `intensityProfile J β` at a pair `e`, as a real
number: `1 - exp (-(β * J e))`. -/
theorem coe_intensityProfile_eq {V : Type*} (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V) :
    (intensityProfile J β e : ℝ) = 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) := rfl

/-- Off the diagonal, at a scale above the corner, the cut-off kernel of a nonnegative
decreasing profile is the difference `K (N(x - y)) - K r`. -/
theorem coe_cutoffKernel_eq_sub {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) {x y : Fin d → ℤ} (hxy : x ≠ y) {r : ℝ}
    (hr : N (Int.cast ∘ (x - y)) ≤ r) :
    (cutoffKernel N K r s(x, y) : ℝ) = K (N (Int.cast ∘ (x - y))) - K r := by
  have hs : 0 < N (Int.cast ∘ (x - y)) := N.intCast_comp_sub_pos hxy
  have hK : 0 ≤ K (N (Int.cast ∘ (x - y))) - K r :=
    sub_nonneg.2 (hKa hs (hs.trans_le hr) hr)
  rw [cutoffKernel_def, radialKernel_of_ne hxy]
  simp only [ModelNorm.coe_toSeminorm]
  rw [cutoffProfile_of_le hr, Real.coe_toNNReal _ hK]

/-- The open probability of a non-diagonal pair under the cut-off kernel is the cut-off edge
probability `1 - exp (-(β (K s - K r)₊))` of its length `s = N(x - y)`, at every scale. The
truncation `Real.toNNReal` in `radialKernel` is inert for a decreasing profile. -/
theorem cutoffEdgeProbability_eq_one_sub_exp {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {x y : Fin d → ℤ} (hxy : x ≠ y) :
    (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ)) =
      fun r' => 1 - Real.exp (-(β : ℝ) * cutoffProfile K r' (N (Int.cast ∘ (x - y)))) := by
  funext r'
  rw [coe_intensityProfile_eq]
  by_cases hr' : N (Int.cast ∘ (x - y)) ≤ r'
  · rw [coe_cutoffKernel_eq_sub hKa hxy hr', cutoffProfile_of_le hr']
  · have hzero : ((cutoffKernel N K r' s(x, y) : ℝ≥0) : ℝ) = 0 := by
      rw [cutoffKernel_def, radialKernel_of_ne hxy, ModelNorm.coe_toSeminorm,
        cutoffProfile_of_lt (not_le.1 hr'), Real.toNNReal_zero]
      simp
    rw [hzero, cutoffProfile_of_lt (not_le.1 hr')]

/-- The open probability of a non-diagonal pair under the cut-off kernel is constant (`0`) on
`(-∞, N(x - y)]`, so its left derivative at the corner `r = N(x - y)` vanishes. -/
theorem hasDerivWithinAt_cutoffEdgeProbability_Iic {N : Seminorm ℝ (Fin d → ℝ)} {K : ℝ → ℝ}
    {β : ℝ≥0} {x y : Fin d → ℤ} (hxy : x ≠ y) :
    HasDerivWithinAt (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ)) 0
      (Iic (N (Int.cast ∘ (x - y)))) (N (Int.cast ∘ (x - y))) := by
  have hzero : ∀ r' ≤ N (Int.cast ∘ (x - y)),
      ((cutoffKernel N K r' s(x, y) : ℝ≥0) : ℝ) = 0 := by
    intro r' hr'
    rcases lt_or_eq_of_le hr' with h | h
    · rw [cutoffKernel_def, radialKernel_of_ne hxy, cutoffProfile_of_lt h, Real.toNNReal_zero]
      simp
    · subst h
      rw [cutoffKernel_def, radialKernel_of_ne hxy, cutoffProfile_of_le le_rfl, sub_self,
        Real.toNNReal_zero]
      simp
  refine (hasDerivWithinAt_const (x := N (Int.cast ∘ (x - y)))
    (s := Iic (N (Int.cast ∘ (x - y)))) (c := (0 : ℝ))).congr ?_ ?_
  · intro r' hr'
    rw [coe_intensityProfile_eq, hzero r' hr']
    simp
  · rw [coe_intensityProfile_eq, hzero _ le_rfl]
    simp

/-- For `r > N(x - y)` the pair `{x, y}` is open with probability
`1 - exp (-(β (K (N(x - y)) - K r)))`, so its right derivative at the corner is `β (-K')`. -/
theorem hasDerivWithinAt_cutoffEdgeProbability_Ioi {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) {K' : ℝ} {β : ℝ≥0} {x y : Fin d → ℤ} (hxy : x ≠ y)
    (hK : HasDerivAt K (-K') (N (Int.cast ∘ (x - y)))) :
    HasDerivWithinAt (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ))
      ((β : ℝ) * K') (Ioi (N (Int.cast ∘ (x - y)))) (N (Int.cast ∘ (x - y))) := by
  have hbase := hasDerivWithinAt_one_sub_exp_cutoffProfile_Ioi
    (s := N (Int.cast ∘ (x - y))) (β := (β : ℝ)) hK
  refine hbase.congr ?_ ?_
  · intro r' hr'
    exact congrFun (cutoffEdgeProbability_eq_one_sub_exp hKa hxy) r'
  · exact congrFun (cutoffEdgeProbability_eq_one_sub_exp hKa hxy) _

/-- **The cut-off edge probability has a genuine corner at an edge length**: it is not
differentiable in the scale at `r = N(x - y)` when `β K' ≠ 0`. -/
theorem not_hasDerivAt_cutoffEdgeProbability {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) {K' L : ℝ} {β : ℝ≥0} {x y : Fin d → ℤ} (hxy : x ≠ y)
    (hK : HasDerivAt K (-K') (N (Int.cast ∘ (x - y)))) (hβK' : (β : ℝ) * K' ≠ 0) :
    ¬ HasDerivAt (fun r' => (intensityProfile (cutoffKernel N K r') β s(x, y) : ℝ)) L
      (N (Int.cast ∘ (x - y))) := by
  rw [cutoffEdgeProbability_eq_one_sub_exp hKa hxy]
  exact not_hasDerivAt_one_sub_exp_cutoffProfile hK hβK'


/-! ### The cut-off expectation derivative -/

/-- **The `r`-derivative of a cut-off edge probability**, away from the corner `r = s`.

For a pair at distance `s`, the open probability under the cut-off kernel is
`1 - exp (-(β cutoffProfile K r s))`. Where `K` has derivative `-K'` at `r`, this is
differentiable at `r` with derivative `β K' exp (-(β cutoffProfile K r s))` when `s ≤ r`,
and `0` when `r < s`. -/
theorem hasDerivAt_cutoffEdgeProbability_if {K : ℝ → ℝ} {K' r s : ℝ} (hne : s ≠ r)
    (hK : HasDerivAt K (-K') r) (β : ℝ) :
    HasDerivAt (fun r' => 1 - Real.exp (-(β * cutoffProfile K r' s)))
      (if s ≤ r then β * K' * Real.exp (-(β * cutoffProfile K r s)) else 0) r := by
  rcases lt_or_gt_of_ne hne with hsr | hrs
  · rw [ite_eq_left hsr.le]
    have hder : HasDerivAt (fun r' => cutoffProfile K r' s) K' r :=
      hasDerivAt_cutoffProfile hsr hK
    have h1 : HasDerivAt (fun r' => β * cutoffProfile K r' s) (β * K') r := hder.const_mul β
    have h2 : HasDerivAt (fun r' => -(β * cutoffProfile K r' s)) (-(β * K')) r := h1.neg
    have h3 : HasDerivAt (fun r' => Real.exp (-(β * cutoffProfile K r' s)))
        (Real.exp (-(β * cutoffProfile K r s)) * (-(β * K'))) r := h2.exp
    have h4 : HasDerivAt (fun r' => 1 - Real.exp (-(β * cutoffProfile K r' s)))
        (0 - Real.exp (-(β * cutoffProfile K r s)) * (-(β * K'))) r :=
      (hasDerivAt_const (x := r) (c := (1 : ℝ))).sub h3
    convert h4 using 1
    ring
  · rw [ite_eq_right (not_le.mpr hrs)]
    have hev : ∀ᶠ r' in 𝓝 r, r' < s := Iio_mem_nhds hrs
    have hzero : (fun r' => 1 - Real.exp (-(β * cutoffProfile K r' s))) =ᶠ[𝓝 r]
        fun _ => (0 : ℝ) := by
      filter_upwards [hev] with r' hr'
      rw [cutoffProfile_of_lt hr']
      simp
    exact (hasDerivAt_const (x := r) (c := (0 : ℝ))).congr_of_eventuallyEq hzero

/-! ### The finite-window Russo formula for the cut-off family -/

/-- The indicator `1{N (e) < r}` of the cut-off kernel takes only the values `0` and `1`. -/
theorem radialKernel_indicator_eq_zero_or_one (N : Seminorm ℝ (Fin d → ℝ)) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) :
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) = 0 ∨
      (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) = 1 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy; exact Or.inl (by simp)
    · rw [radialKernel_of_ne hxy]
      by_cases h : N (Int.cast ∘ (x - y)) < r
      · right; simp [h]
      · left; simp [h]

/-- Sums against a `{0,1}`-valued weight collapse to the support of the weight. -/
theorem sum_indicator_mul_eq_sum_filter {ι : Type*} (S : Finset ι) (ind : ι → ℝ)
    (X : ι → ℝ) (h : ∀ e, ind e = 0 ∨ ind e = 1) :
    ∑ e ∈ S, ind e * X e = ∑ e ∈ S.filter (fun e => ind e ≠ 0), X e := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := S) (p := fun e => ind e ≠ 0)]
  have hzero : ∑ e ∈ S.filter (fun e => ¬ ind e ≠ 0), ind e * X e = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    simp only [Finset.mem_filter, not_not] at he
    rw [he.2, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_filter] at he
  rcases h e with h0 | h1
  · exact absurd h0 he.2
  · rw [h1, one_mul]

/-- **Russo's formula for the cut-off family, finite window, with the paper's constant
`β|J'(r)|`.**

Let `S` be a finite set of pairs that contains no pair at distance exactly `r₀`, and let `h`
be any functional of the configuration restricted to `S`. Then the function
`r ↦ ∫ h (ω ∩ S) d(law (intensityProfile (cutoffKernel N K r) β))` is differentiable at `r₀`
with derivative

  `β (-K' r₀) ∑_{e ∈ S, N(e) < r₀} exp (-β J_{r₀}(e)) ∫ (h(ω ∪ {e}) - h(ω \ {e})) d(law …)`,

i.e. the paper's `β|J'(r)|` times the pivotal flux, with the open-edge probability of the
cut-off kernel written as `1 - exp (-β J_r(e))` and the closed-edge factor
`exp (-β J_r(e)) = 1 - q_e` kept explicitly. No boundedness of `h` is assumed.

The filtered sum runs over the pairs the cut-off indicator `1{N(e) < r}` selects. That
indicator is the radial kernel of `s ↦ 1{s < r}`, which is zero on the diagonal as well, so
diagonal pairs of `S` (which are not edges of the bond model, and for which the edge
probability is identically zero) contribute nothing. At a parameter `r` that is not an edge
length, the filter is `1{N(e) < r}` on the off-diagonal pairs, i.e. the paper's `y ∈ B_r(x)`. -/
theorem hasDerivAt_expectation_cutoff (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t) (β : ℝ≥0)
    (h : Set (Sym2 (Fin d → ℤ)) → ℝ) (S : Finset (Sym2 (Fin d → ℤ))) {r : ℝ} (hr : 0 < r)
    (hre : ∀ e ∈ S, ∀ x y, e = s(x, y) → r ≠ N (Int.cast ∘ (x - y))) :
    HasDerivAt (fun r' => ∫ ω, h (ω ∩ S) ∂(law (intensityProfile (cutoffKernel N K r') β)))
      ((β : ℝ) * -K' r * ∑ e ∈ S.filter (fun e =>
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0),
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
          ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S))
            ∂(law (intensityProfile (cutoffKernel N K r) β))) r := by
  classical
  set p : ℝ → Sym2 (Fin d → ℤ) → unitInterval :=
    fun r' => intensityProfile (cutoffKernel N K r') β with hp
  set c : Sym2 (Fin d → ℤ) → ℝ := fun e =>
    (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))) with hc
  have hder : ∀ e ∈ S, HasDerivAt (fun r' => (p r' e : ℝ)) (c e) r := fun e he =>
    hasDerivAt_cutoff_prob hKa hK' β hr e (hre e he)
  set f : Set S → ℝ := fun η => h (Subtype.val '' η) with hf
  have hmain := PercLib.Probability.FiniteProfile.integral_hasDerivWithinAt (E := S)
    (fun e r' => (p r' e : ℝ)) (fun e => c e) r (fun e => hder e e.2)
    (fun r' (e : S) => p r' e) univ (fun _ => rfl) (fun _ _ _ => rfl) f
  rw [hasDerivWithinAt_univ] at hmain
  have hfun : (fun r' => ∫ ω, h (ω ∩ S) ∂(law (p r'))) =
      fun r' => ∫ η, f η ∂(PercLib.Probability.prodBernoulli fun e : S => p r' e) := by
    funext r'
    rw [← integral_window_eq_restrict]
    simp only [f, image_val_preimage_val]
  have hd : (∑ e : S, c e * ∫ η, (f (insert e η) - f (η \ {e}))
        ∂(PercLib.Probability.prodBernoulli fun e : S => p r e)) =
      ∑ e ∈ S, c e * ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S))
        ∂(law (p r)) := by
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← integral_window_eq_restrict S (fun η : Set S => f (insert e η) - f (η \ {e}))]
    simp only [f, image_val_insert_preimage_val, image_val_diff_preimage_val]
  rw [← hfun, hd] at hmain
  have hsplit : ∑ e ∈ S, c e * ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S))
        ∂(law (p r)) =
      (β : ℝ) * -K' r * ∑ e ∈ S.filter (fun e =>
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0),
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
          ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S)) ∂(law (p r)) := by
    have hterm : ∀ e ∈ S, c e * ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S))
          ∂(law (p r)) =
        (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          (((β : ℝ) * -K' r) * (Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
            ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S)) ∂(law (p r)))) := by
      intro e _
      simp only [c]
      ring
    rw [Finset.sum_congr rfl hterm, sum_indicator_mul_eq_sum_filter S _
      (fun e => ((β : ℝ) * -K' r) * (Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
        ∫ ω, (h ((insert e ω) ∩ S) - h ((ω \ {e}) ∩ S)) ∂(law (p r))))
      (radialKernel_indicator_eq_zero_or_one N r), Finset.mul_sum]
  rw [← hsplit]
  exact hmain

/-- **Russo's formula for the cut-off family, cluster-volume form.** The observable
`F (cluster ω o).encard` of Lemma I.4.1, in the same finite window. -/
theorem hasDerivAt_expectation_cutoff_cluster (hKa : AntitoneOn K (Ioi 0))
    (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t) (β : ℝ≥0) (F : ℕ∞ → ℝ)
    (o : Fin d → ℤ) (S : Finset (Sym2 (Fin d → ℤ))) {r : ℝ} (hr : 0 < r)
    (hre : ∀ e ∈ S, ∀ x y, e = s(x, y) → r ≠ N (Int.cast ∘ (x - y))) :
    HasDerivAt (fun r' => ∫ ω, F (cluster (ω ∩ S) o).encard
        ∂(law (intensityProfile (cutoffKernel N K r') β)))
      ((β : ℝ) * -K' r * ∑ e ∈ S.filter (fun e =>
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) ≠ 0),
        Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)) *
          ∫ ω, (F (cluster (insert e ω ∩ S) o).encard -
            F (cluster ((ω \ {e}) ∩ S) o).encard)
            ∂(law (intensityProfile (cutoffKernel N K r) β))) r :=
  hasDerivAt_expectation_cutoff hKa hK' β (fun ω => F (cluster ω o).encard) S hr hre

/-- **The cut-off Russo formula on a finite edge set**, the literal form of the source's
`hasDerivAt_expectation_cutoff`: for independent edge probabilities
`q_e(r) = 1 - exp (-(β cutoffProfile K r (len e)))`, the expectation of an arbitrary
observable `X` of the finite configuration is differentiable with derivative the paper's
`β|J'(r)|` times the pivotal expectation, with the closed-edge factor displayed. -/
theorem hasDerivAt_expectation_cutoff_finite {E : Type*} [Fintype E]
    (len : E → ℝ) (K : ℝ → ℝ) {K' r β : ℝ} (hne : ∀ e, len e ≠ r)
    (hK : HasDerivAt K (-K') r) (X : (E → Bool) → ℝ) :
    HasDerivAt (fun r' => PercLib.Probability.FiniteProfile.expectation
        (fun e => 1 - Real.exp (-(β * cutoffProfile K r' (len e)))) X)
      (β * K' * ∑ e ∈ (Finset.univ : Finset E).filter (fun e => len e ≤ r),
        Real.exp (-(β * cutoffProfile K r (len e))) *
          PercLib.Probability.FiniteProfile.expectation
            (fun e => 1 - Real.exp (-(β * cutoffProfile K r (len e))))
            (PercLib.Probability.FiniteProfile.difference e X)) r := by
  have hq : ∀ e, HasDerivAt (fun r' => 1 - Real.exp (-(β * cutoffProfile K r' (len e))))
      (if len e ≤ r then β * K' * Real.exp (-(β * cutoffProfile K r (len e))) else 0) r :=
    fun e => hasDerivAt_cutoffEdgeProbability_if (hne e) hK β
  have hmain := PercLib.Probability.FiniteProfile.expectation_hasDerivAt
    (fun e r' => 1 - Real.exp (-(β * cutoffProfile K r' (len e))))
    (fun e => if len e ≤ r then β * K' * Real.exp (-(β * cutoffProfile K r (len e)))
      else 0) r hq X
  convert hmain using 1
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : len e ≤ r
  · simp only [h, ite_true]; ring
  · simp only [h, ite_false, zero_mul]

end PercLib.Models.LongRange
