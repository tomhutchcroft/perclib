/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5, Lemma I.4.1 and its proof.
-/
module

public import PercLib.Models.LongRange.DegreeCorner.Defs

/-!
# The radius corner of the expected degree at a positive integer scale

Definition I.1.5 cuts the power law off at scale `r` by `J_r (s) = K s - K r` for `s ≤ r` and
`J_r (s) = 0` for `r < s`.  If `s = ‖z‖` is the length of an edge and `r` crosses `s`, that edge
alone has a corner (`CutoffCorner.not_hasDerivAt_cutoffEdgeProbability`): its left derivative in
`r` vanishes and its right derivative is `β |K' (s)| > 0`.  For a functional of the whole lattice
this is not the end of the story: an infinite sum of positive jumps could in principle cancel.
This file proves that it does not, and computes the jump.

The functional used is the **expected degree of a vertex**,
`expDegree r = ∑'_z 𝐏(the pair {0, z} is open in the cut-off bond model at scale r)`,
a genuine infinite-volume quantity of the model whose `z`-term is the open probability
`1 - exp (-(β J_r (‖z‖)))` of `CutoffCorner.coe_intensityProfile_eq`.  Since `J_r (‖z‖) = 0` once
`r < ‖z‖`, the sum is a finite sum over the closed box `{‖z‖ ≤ r}`.

The definitions (`boxFinset`, `ballPt`, `edgeProb`, `expDegree`, `localDegree`) are in the
companion module `DegreeCorner/Defs`, where their exact mathematical meaning is reviewed; the
present module contains only theorems about them.

Main results, for the sup norm on `ℤ^d` with `d ≥ 1`, `α > 0`, `β ≥ 0`:

* `expDegree_eq_sum_ballPt`: on `[n, n + 1)` the expected degree is the finite sum over the
  punctured closed box `{0 < ‖z‖ ≤ n}` of `1 - exp (-(β (K ‖z‖ - K r)))`;
* `hasDerivWithinAt_expDegree_right` / `hasDerivWithinAt_expDegree_left`: at the integer scale
  `n ≥ 1` the right derivative on `{n} ∪ (n, n + 1)` and the left derivative on
  `((n - 1), n] ∪ {n}` both exist, with the values
  `β (d + α) n ^ (-(d + α) - 1) ∑_{0 < ‖z‖ ≤ n} exp (-(β (K ‖z‖ - K n)))` and the same sum over
  `0 < ‖z‖ ≤ n - 1`;
* `derivWithin_right_sub_left`: **the jump is exactly the sphere contribution**,
  `β (d + α) n ^ (-(d + α) - 1) · #{z : ‖z‖ = n}`.  Every term of the sphere is counted once,
  with exponential factor `exp 0 = 1`, and nothing cancels because every summand is positive;
* `jump_pos`: the jump is **strictly positive** for `d ≥ 1`, `α > 0`, `β > 0`, `n ≥ 1`, so no
  cancellation between the summands can occur;
* `not_differentiableAt_expDegree_nat`: consequently the expected degree is **not**
  differentiable at any positive integer scale when `β ≠ 0`, so a two-sided reading of the
  differential identity can only hold off the lattice sphere set.  This is the quantitative form of
  the closed-ball convention `B_r = {x : ‖x‖ ≤ r}` in the right-hand side of Lemma I.4.1: that
  right-hand side is right-continuous in `r`, and its value at `n` is the right derivative;
* `hasDerivWithinAt_expDegree_one_one_one_right` / `..._left` and
  `not_differentiableAt_expDegree_concrete`: at `d = 1`, `α = 1`, `β = 1`, `n = 1` the one-sided
  derivatives are exactly `4` and `0`, so the corner is non-vacuous.

The counts `#{‖z‖ ≤ n} = (2 n + 1) ^ d` and `#{‖z‖ = n} = (2 n + 1) ^ d - (2 n - 1) ^ d` are the
published `PowerLaw.card_norm_le` and `PowerLaw.card_norm_eq`.

## What this file does not claim

It does not identify `expDegree` with the cluster moment `E_{β,r} |K|^p` of Lemma I.4.1, and it
makes no claim about the critical or subcritical regime: `β` is an arbitrary nonnegative intensity.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

variable {d : ℕ}

/-! ## The sup-norm box, the punctured box and their cardinalities -/

theorem mem_boxFinset {d n : ℕ} {z : Fin d → ℤ} :
    z ∈ boxFinset d n ↔ ‖z‖ ≤ (n : ℝ) :=
  mem_Icc_iff_norm_le z n


theorem mem_ballPt {d n : ℕ} {z : Fin d → ℤ} :
    z ∈ ballPt d n ↔ z ≠ 0 ∧ ‖z‖ ≤ (n : ℝ) := by
  rw [ballPt, Finset.mem_erase, mem_boxFinset, and_comm]

theorem card_boxFinset (d n : ℕ) : (boxFinset d n).card = (2 * n + 1) ^ d :=
  card_Icc_ball (d := d) n

theorem ballPt_mono (d : ℕ) : Monotone (ballPt d) := by
  intro m n hmn z hz
  rw [mem_ballPt] at hz ⊢
  exact ⟨hz.1, hz.2.trans (by exact_mod_cast hmn)⟩

/-- The punctured box of radius zero is empty. -/
theorem ballPt_zero (d : ℕ) : ballPt d 0 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun z hz => ?_
  rw [mem_ballPt] at hz
  have hz0 : z = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ ‖z‖ := one_le_norm_of_ne_zero hne
    have h2 : ‖z‖ ≤ (0 : ℝ) := by simpa using hz.2
    linarith
  exact hz.1 hz0

/-- The set difference of consecutive punctured boxes is the sphere `{‖z‖ = n}`. -/
theorem sdiff_ballPt {d n : ℕ} (hn : 1 ≤ n) :
    ballPt d n \ ballPt d (n - 1) = (boxFinset d n).filter (fun z => ‖z‖ = (n : ℝ)) := by
  ext z
  simp only [Finset.mem_sdiff, mem_ballPt, Finset.mem_filter, mem_boxFinset]
  constructor
  · rintro ⟨⟨hz0, hzn⟩, hnot⟩
    have hne : ¬ ‖z‖ ≤ ((n - 1 : ℕ) : ℝ) := fun h => hnot ⟨hz0, h⟩
    have hcast : ¬ (⌊‖z‖⌋₊ ≤ n - 1) := by
      intro h'
      exact hne (by rw [← natCast_floor_norm z]; exact_mod_cast h')
    have hge : n ≤ ⌊‖z‖⌋₊ := by omega
    have h2 : (n : ℝ) ≤ ‖z‖ := by
      rw [← natCast_floor_norm z]
      exact_mod_cast hge
    exact ⟨hzn, le_antisymm hzn h2⟩
  · rintro ⟨hzn, hnorm⟩
    refine ⟨⟨?_, by rw [hnorm]⟩, ?_⟩
    · rintro rfl
      have h0 : ((0 : ℕ) : ℝ) = (n : ℝ) := by simpa using hnorm
      have h1 : (0 : ℕ) = n := by exact_mod_cast h0
      omega
    · rintro ⟨hz0, hle⟩
      have h1 : ((n : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by rw [← hnorm]; exact hle
      have h2 : n ≤ n - 1 := by exact_mod_cast h1
      omega

/-- The cardinality of the `n`-th sphere equals the cardinality of the difference of consecutive
punctured boxes. -/
theorem card_sdiff_ballPt {d n : ℕ} (hn : 1 ≤ n) :
    (ballPt d n \ ballPt d (n - 1)).card = Nat.card {z : Fin d → ℤ // ‖z‖ = (n : ℝ)} := by
  rw [sdiff_ballPt hn, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
  simp only [Finset.mem_filter, mem_boxFinset]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [h], h⟩

/-- The explicit sphere count: `#{‖z‖ = n} = (2 n + 1) ^ d - (2 n - 1) ^ d` for `n ≥ 1`. -/
theorem card_sdiff_ballPt_eq {d n : ℕ} (hn : 1 ≤ n) :
    (ballPt d n \ ballPt d (n - 1)).card = (2 * n + 1) ^ d - (2 * n - 1) ^ d := by
  rw [card_sdiff_ballPt hn]
  exact card_norm_eq d hn

/-! ## The expected degree of the cut-off bond model -/



/-- The sup norm of `0 - z` as a `ModelNorm` value is `‖z‖`. -/
theorem ofNorm_intCast_comp_zero_sub {d : ℕ} (z : Fin d → ℤ) :
    ModelNorm.ofNorm (Fin d → ℝ) (Int.cast ∘ ((0 : Fin d → ℤ) - z)) = ‖z‖ := by
  have h : normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ ((0 : Fin d → ℤ) - z)) = ‖z‖ := by
    rw [normSeminorm_intCast]
    simp
  exact h

/-- The diagonal term of the expected degree vanishes. -/
theorem edgeProb_zero {d : ℕ} {α : ℝ} {β : ℝ≥0} {r : ℝ} : edgeProb d α β r 0 = 0 := by
  simp [edgeProb, coe_intensityProfile_eq, cutoffKernel_def]

/-- Off the diagonal the open probability of `{0, z}` is `1 - exp (-(β (J_r (‖z‖))))`. -/
theorem edgeProb_eq {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {r : ℝ} {z : Fin d → ℤ}
    (hz : z ≠ 0) :
    edgeProb d α β r z =
      1 - Real.exp (-((β : ℝ) * cutoffProfile (powerLawProfile 1 ((d : ℝ) + α)) r ‖z‖)) := by
  have hKa : AntitoneOn (powerLawProfile 1 ((d : ℝ) + α)) (Ioi 0) :=
    antitoneOn_powerLawProfile_add (d := d) (c := 1) zero_le_one (by positivity)
  have h := congrFun (cutoffEdgeProbability_eq_one_sub_exp (d := d)
    (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := powerLawProfile 1 ((d : ℝ) + α)) hKa
    (β := β) (x := 0) (y := z) (Ne.symm hz)) r
  rw [edgeProb, h, ofNorm_intCast_comp_zero_sub, neg_mul]

/-- The open probability of a pair beyond the cut-off vanishes. -/
theorem edgeProb_eq_zero_of_lt {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {r : ℝ}
    {z : Fin d → ℤ} (hz : r < ‖z‖) : edgeProb d α β r z = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact edgeProb_zero
  · rw [edgeProb_eq hα hz0, cutoffProfile_of_lt hz]
    simp

/-- **The expected degree on `[n, n + 1)` is a finite sum over the punctured closed box.** -/
theorem expDegree_eq_sum_ballPt {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {r : ℝ} {n : ℕ}
    (hrn : (n : ℝ) ≤ r) (hr : r < (n : ℝ) + 1) :
    expDegree d α β r =
      ∑ z ∈ ballPt d n,
        (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) r)))) := by
  rw [expDegree, tsum_eq_sum (s := ballPt d n) ?_]
  · refine Finset.sum_congr rfl fun z hz => ?_
    rw [edgeProb_eq hα (mem_ballPt.1 hz).1, cutoffProfile_of_le (le_trans (mem_ballPt.1 hz).2 hrn)]
  · intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact edgeProb_zero
    · refine edgeProb_eq_zero_of_lt hα ?_
      have hgt : ¬ ‖z‖ ≤ (n : ℝ) := fun hle => hz (mem_ballPt.2 ⟨hz0, hle⟩)
      have hcast : ¬ (⌊‖z‖⌋₊ ≤ n) := by
        intro h'
        exact hgt (by rw [← natCast_floor_norm z]; exact_mod_cast h')
      have hge : n + 1 ≤ ⌊‖z‖⌋₊ := by omega
      have h2 : ((n : ℕ) : ℝ) + 1 ≤ ‖z‖ := by
        rw [← natCast_floor_norm z]
        exact_mod_cast hge
      linarith

/-! ## The local model and its derivative in the scale -/


/-- The local model at radius zero vanishes identically. -/
theorem localDegree_zero (d : ℕ) (α : ℝ) (β : ℝ≥0) :
    localDegree d α β 0 = fun _ => (0 : ℝ) := by
  funext r
  simp [localDegree, ballPt_zero]

/-- **The derivative of the local model at a positive scale `ρ`**, for a nonempty punctured box.
Each summand is a smooth function of `r` (the corner has been resolved into the difference
`K ‖z‖ - K r`), so the finite sum is differentiable, with the derivative of
`1 - exp (-(β (K ‖z‖ - K r)))` at `ρ` equal to
`β (d + α) ρ ^ (-(d + α) - 1) exp (-(β (K ‖z‖ - K ρ)))`. -/
theorem hasDerivAt_localDegree {d : ℕ} {α : ℝ} {β : ℝ≥0} {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (localDegree d α β n)
      ((β : ℝ) * ((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d n,
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) ρ)))) ρ := by
  have hK : HasDerivAt (powerLawProfile 1 ((d : ℝ) + α))
      (-((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1)) ρ := by
    simpa using hasDerivAt_powerLawProfile_add (d := d) (c := 1) α hρ
  change HasDerivAt (fun r : ℝ => ∑ z ∈ ballPt d n,
      (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) r)))))
    ((β : ℝ) * ((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1) *
      ∑ z ∈ ballPt d n,
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) ρ)))) ρ
  rw [Finset.mul_sum]
  refine HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ) ?_
  intro z hz
  have h1 : HasDerivAt (fun r : ℝ => powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
      powerLawProfile 1 ((d : ℝ) + α) r)
      (-(-((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1))) ρ :=
    hK.const_sub (powerLawProfile 1 ((d : ℝ) + α) ‖z‖)
  have h2 : HasDerivAt (fun r : ℝ => (β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
      powerLawProfile 1 ((d : ℝ) + α) r))
      ((β : ℝ) * (-(-((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1)))) ρ :=
    h1.const_mul (β : ℝ)
  have h3 : HasDerivAt (fun r : ℝ => -((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
      powerLawProfile 1 ((d : ℝ) + α) r)))
      (-((β : ℝ) * (-(-((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1))))) ρ :=
    h2.neg
  have h4 := h3.exp
  have h5 : HasDerivAt (fun r : ℝ => 1 - Real.exp (-((β : ℝ) *
      (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ - powerLawProfile 1 ((d : ℝ) + α) r))))
      (-(Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) ρ))) *
        (-((β : ℝ) * (-(-((d : ℝ) + α) * ρ ^ (-((d : ℝ) + α) - 1))))))) ρ :=
    h4.const_sub (1 : ℝ)
  convert h5 using 1
  ring


/-! ## The one-sided derivatives at a positive integer scale -/

/-- **The right derivative of the expected degree at a positive integer scale.**  On `[n, n + 1)`
the expected degree agrees with the local model on the closed punctured box, which is smooth. -/
theorem hasDerivWithinAt_expDegree_right {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {n : ℕ}
    (hn : 1 ≤ n) :
    HasDerivWithinAt (expDegree d α β)
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d n,
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) (Ici (n : ℝ)) (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hloc : HasDerivWithinAt (localDegree d α β n)
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d n,
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) (Ici (n : ℝ)) (n : ℝ) :=
    (hasDerivAt_localDegree (d := d) (n := n) hnpos).hasDerivWithinAt
  refine hloc.congr_of_eventuallyEq ?_ ?_
  · have hmem : Ico (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝[Ici (n : ℝ)] (n : ℝ) :=
      inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds (by linarith)))
    filter_upwards [hmem] with r hr
    exact expDegree_eq_sum_ballPt hα hr.1 hr.2
  · exact expDegree_eq_sum_ballPt hα le_rfl (by linarith)

-- **At the left endpoint of `(n - 1, n]` the expected degree already equals the local model on
-- the box of radius `n - 1`**: the sphere `{‖z‖ = n}` contributes the factor `1 - exp 0 = 0`. -/
theorem expDegree_eq_localDegree_pred {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {n : ℕ}
    (hn : 1 ≤ n) :
    expDegree d α β (n : ℝ) = localDegree d α β (n - 1) (n : ℝ) := by
  rw [expDegree_eq_sum_ballPt (n := n) hα le_rfl (by linarith)]
  have hsub : ballPt d (n - 1) ⊆ ballPt d n := ballPt_mono d (by omega)
  have hdisj : Disjoint (ballPt d n \ ballPt d (n - 1)) (ballPt d (n - 1)) :=
    (Finset.disjoint_sdiff (s := ballPt d (n - 1)) (t := ballPt d n)).symm
  have hunion : ballPt d n \ ballPt d (n - 1) ∪ ballPt d (n - 1) = ballPt d n :=
    Finset.sdiff_union_of_subset hsub
  have hzero : ∑ z ∈ ballPt d n \ ballPt d (n - 1),
      (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hnorm : ‖z‖ = (n : ℝ) := by
      rw [sdiff_ballPt (d := d) hn] at hz
      exact (Finset.mem_filter.1 hz).2
    rw [hnorm, sub_self, mul_zero, neg_zero, Real.exp_zero]
    ring
  have hsplit : ∑ z ∈ ballPt d n,
      (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) =
      ∑ z ∈ ballPt d n \ ballPt d (n - 1),
        (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) +
      ∑ z ∈ ballPt d (n - 1),
        (1 - Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) := by
    conv_lhs => rw [← hunion]
    rw [Finset.sum_union hdisj]
  rw [hsplit, hzero, zero_add]
  rfl

/-- **The left derivative of the expected degree at a positive integer scale.**  On `(n - 1, n]`
the expected degree agrees with the local model on the closed punctured box of radius `n - 1`. -/
theorem hasDerivWithinAt_expDegree_left {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} {n : ℕ}
    (hn : 1 ≤ n) :
    HasDerivWithinAt (expDegree d α β)
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) (Iic (n : ℝ)) (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hloc : HasDerivWithinAt (localDegree d α β (n - 1))
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) (Iic (n : ℝ)) (n : ℝ) :=
    (hasDerivAt_localDegree (d := d) (n := n - 1) hnpos).hasDerivWithinAt
  refine hloc.congr_of_eventuallyEq ?_ ?_
  · have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    have hmem : Ioc ((n : ℝ) - 1) (n : ℝ) ∈ 𝓝[Iic (n : ℝ)] (n : ℝ) :=
      inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))) self_mem_nhdsWithin
    filter_upwards [hmem] with r hr
    rcases eq_or_lt_of_le hr.2 with h | h
    · rw [h]
      exact expDegree_eq_localDegree_pred hα hn
    · exact expDegree_eq_sum_ballPt (n := n - 1) hα (by rw [hcast]; linarith [hr.1])
        (by rw [hcast]; linarith)
  · exact expDegree_eq_localDegree_pred hα hn

/-! ## The jump at a positive integer scale -/

/-- **The jump of the one-sided derivatives is exactly the sphere contribution.**  The difference
of the right and left derivative values at the integer scale `n` is
`β (d + α) n ^ (-(d + α) - 1)` times the cardinality of the sphere `{‖z‖ = n}`. -/
theorem derivWithin_right_sub_left {d : ℕ} {α : ℝ} {β : ℝ≥0} {n : ℕ} (hn : 1 ≤ n) :
    ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d n,
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) -
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) =
      (β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ((ballPt d n \ ballPt d (n - 1)).card : ℝ) := by
  have hsub : ballPt d (n - 1) ⊆ ballPt d n := ballPt_mono d (by omega)
  have hdisj : Disjoint (ballPt d n \ ballPt d (n - 1)) (ballPt d (n - 1)) :=
    (Finset.disjoint_sdiff (s := ballPt d (n - 1)) (t := ballPt d n)).symm
  have hunion : ballPt d n \ ballPt d (n - 1) ∪ ballPt d (n - 1) = ballPt d n :=
    Finset.sdiff_union_of_subset hsub
  have hstep : (∑ z ∈ ballPt d n,
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) -
      ∑ z ∈ ballPt d (n - 1),
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) =
      ((ballPt d n \ ballPt d (n - 1)).card : ℝ) := by
    have hone : ∀ z ∈ ballPt d n \ ballPt d (n - 1),
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) = 1 := by
      intro z hz
      have hnorm : ‖z‖ = (n : ℝ) := by
        rw [sdiff_ballPt (d := d) hn] at hz
        exact (Finset.mem_filter.1 hz).2
      rw [hnorm, sub_self, mul_zero, neg_zero, Real.exp_zero]
    have hcard : ∑ z ∈ ballPt d n \ ballPt d (n - 1),
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) =
        ((ballPt d n \ ballPt d (n - 1)).card : ℝ) := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsplit : ∑ z ∈ ballPt d n,
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) =
        ∑ z ∈ ballPt d n \ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) +
        ∑ z ∈ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) := by
      conv_lhs => rw [← hunion]
      rw [Finset.sum_union hdisj]
    linarith [hsplit, hcard]
  rw [← mul_sub, hstep]

/-- **The jump in closed form**: `β (d + α) n ^ (-(d + α) - 1)` times
`(2 n + 1) ^ d - (2 n - 1) ^ d`, the size of the `n`-th sup-norm sphere. -/
theorem jump_eq_sphereCount {d : ℕ} {α : ℝ} {β : ℝ≥0} {n : ℕ} (hn : 1 ≤ n) :
    ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d n,
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) -
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) =
      (β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        (((2 * n + 1) ^ d - (2 * n - 1) ^ d : ℕ) : ℝ) := by
  rw [derivWithin_right_sub_left hn, card_sdiff_ballPt_eq hn]

/-! ## The least positive integer scale, in closed form -/

/-- **The right derivative at the least positive integer scale `n = 1`.**  The punctured box
`{0 < ‖z‖ ≤ 1}` is exactly the sphere `{‖z‖ = 1}`, of cardinality `3 ^ d - 1`, and every summand
of the coefficient is `exp 0 = 1`, so the right derivative is `β (d + α) (3 ^ d - 1)`. -/
theorem hasDerivWithinAt_expDegree_one_right {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} :
    HasDerivWithinAt (expDegree d α β)
      ((β : ℝ) * ((d : ℝ) + α) * ((3 ^ d - 1 : ℕ) : ℝ)) (Ici (1 : ℝ)) (1 : ℝ) := by
  have h := hasDerivWithinAt_expDegree_right (d := d) (β := β) hα (n := 1) le_rfl
  push_cast at h
  have hcard : (∑ z ∈ ballPt d 1,
      Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) (1 : ℝ))))) = ((3 ^ d - 1 : ℕ) : ℝ) := by
    have hone : ∀ z ∈ ballPt d 1,
        Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
          powerLawProfile 1 ((d : ℝ) + α) (1 : ℝ)))) = 1 := by
      intro z hz
      obtain ⟨hz0, hz1⟩ := mem_ballPt.1 hz
      have hz1' : ‖z‖ ≤ (1 : ℝ) := by simpa using hz1
      have hnorm : ‖z‖ = (1 : ℝ) := le_antisymm hz1' (one_le_norm_of_ne_zero hz0)
      rw [hnorm, sub_self, mul_zero, neg_zero, Real.exp_zero]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hdiff : ballPt d 1 = ballPt d 1 \ ballPt d 0 := by
      rw [ballPt_zero, Finset.sdiff_empty]
    have hcount : (ballPt d 1 \ ballPt d 0).card = (3 ^ d - 1 : ℕ) := by
      simpa using card_sdiff_ballPt_eq (d := d) (n := 1) le_rfl
    rw [hdiff]
    exact_mod_cast hcount
  have hone : (1 : ℝ) ^ (-((d : ℝ) + α) - 1) = 1 := Real.one_rpow _
  rw [hcard, hone, mul_one] at h
  exact h

/-- **The left derivative at the least positive integer scale `n = 1`** vanishes: there is no
edge of length below one. -/
theorem hasDerivWithinAt_expDegree_one_left {d : ℕ} {α : ℝ} (hα : 0 < α) {β : ℝ≥0} :
    HasDerivWithinAt (expDegree d α β) 0 (Iic (1 : ℝ)) (1 : ℝ) := by
  have h := hasDerivWithinAt_expDegree_left (d := d) (β := β) hα (n := 1) le_rfl
  rw [ballPt_zero] at h
  simpa using h

/-- **The exact right derivative at `d = 1`, `α = 1`, `β = 1`, `n = 1` is `4`**: the general
formula reads `β (d + α) (3 ^ d - 1) = 1 · 2 · 2`. -/
theorem hasDerivWithinAt_expDegree_one_one_one_right :
    HasDerivWithinAt (expDegree 1 1 1) 4 (Ici (1 : ℝ)) (1 : ℝ) := by
  have h := hasDerivWithinAt_expDegree_one_right (d := 1) (α := 1) (β := 1) one_pos
  norm_num at h
  exact h

/-- **The exact left derivative at `d = 1`, `α = 1`, `β = 1`, `n = 1` is `0`**. -/
theorem hasDerivWithinAt_expDegree_one_one_one_left :
    HasDerivWithinAt (expDegree 1 1 1) 0 (Iic (1 : ℝ)) (1 : ℝ) :=
  hasDerivWithinAt_expDegree_one_left (d := 1) (α := 1) (β := 1) one_pos

/-- **The sphere contribution to the jump is strictly positive.**  The difference of the right and
left derivative values at the integer scale `n` is `β (d + α) n ^ (-(d + α) - 1)` times the
exponential factors summed over the sphere `{‖z‖ = n}`, and this is positive for `d ≥ 1`, `n ≥ 1`,
`α > 0`, `β > 0` because every factor is positive and the sphere is nonempty. -/
theorem jump_pos {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0} (hβ : 0 < β)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d n,
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) -
      ((β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
        ∑ z ∈ ballPt d (n - 1),
          Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
            powerLawProfile 1 ((d : ℝ) + α) (n : ℝ))))) := by
  rw [jump_eq_sphereCount hn]
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hdα : (0 : ℝ) < (d : ℝ) + α := by
    have h0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hrate : (0 : ℝ) < (n : ℝ) ^ (-((d : ℝ) + α) - 1) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hcard : (0 : ℝ) < (((2 * n + 1) ^ d - (2 * n - 1) ^ d : ℕ) : ℝ) := by
    have hpos : 0 < (2 * n + 1) ^ d - (2 * n - 1) ^ d := by
      have hlt : (2 * n - 1) ^ d < (2 * n + 1) ^ d :=
        Nat.pow_lt_pow_left (by omega) (by omega)
      omega
    exact_mod_cast hpos
  exact mul_pos (mul_pos (mul_pos hβ' hdα) hrate) hcard

/-- **The expected degree is not differentiable at a positive integer scale.**  Both one-sided
derivatives exist at `n` and their difference is the strictly positive sphere contribution, so no
two-sided derivative exists. -/
theorem not_differentiableAt_expDegree_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0} (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    ¬ DifferentiableAt ℝ (expDegree d α β) (n : ℝ) := by
  intro hdiff
  set vR : ℝ := (β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
    ∑ z ∈ ballPt d n,
      Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) with hvR
  set vL : ℝ := (β : ℝ) * ((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1) *
    ∑ z ∈ ballPt d (n - 1),
      Real.exp (-((β : ℝ) * (powerLawProfile 1 ((d : ℝ) + α) ‖z‖ -
        powerLawProfile 1 ((d : ℝ) + α) (n : ℝ)))) with hvL
  have hR : HasDerivWithinAt (expDegree d α β) vR (Ici (n : ℝ)) (n : ℝ) :=
    hasDerivWithinAt_expDegree_right hα hn
  have hL : HasDerivWithinAt (expDegree d α β) vL (Iic (n : ℝ)) (n : ℝ) :=
    hasDerivWithinAt_expDegree_left hα hn
  have e1 : derivWithin (expDegree d α β) (Ici (n : ℝ)) (n : ℝ) = vR :=
    hR.derivWithin (uniqueDiffWithinAt_Ici _)
  have e2 : derivWithin (expDegree d α β) (Ici (n : ℝ)) (n : ℝ) =
      deriv (expDegree d α β) (n : ℝ) :=
    (hdiff.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ici _)
  have e3 : derivWithin (expDegree d α β) (Iic (n : ℝ)) (n : ℝ) = vL :=
    hL.derivWithin (uniqueDiffWithinAt_Iic _)
  have e4 : derivWithin (expDegree d α β) (Iic (n : ℝ)) (n : ℝ) =
      deriv (expDegree d α β) (n : ℝ) :=
    (hdiff.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Iic _)
  have heq : vR = vL := by
    calc vR = derivWithin (expDegree d α β) (Ici (n : ℝ)) (n : ℝ) := e1.symm
      _ = deriv (expDegree d α β) (n : ℝ) := e2
      _ = derivWithin (expDegree d α β) (Iic (n : ℝ)) (n : ℝ) := e4.symm
      _ = vL := e3
  have hpos : 0 < vR - vL := jump_pos hd hα hβ hn
  rw [heq, sub_self] at hpos
  exact lt_irrefl (0 : ℝ) hpos

/-- The `β ≠ 0` form of `not_differentiableAt_expDegree_nat` (equivalent for `β : ℝ≥0`). -/
theorem not_differentiableAt_expDegree_nat' {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0} (hβ : (β : ℝ) ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ¬ DifferentiableAt ℝ (expDegree d α β) (n : ℝ) := by
  have hβℝ : (0 : ℝ) < (β : ℝ) := lt_of_le_of_ne β.coe_nonneg (Ne.symm hβ)
  exact not_differentiableAt_expDegree_nat hd hα (by exact_mod_cast hβℝ) hn

/-- **The corner at the least positive integer scale**, non-vacuously: at `d = 1`, `α = 1`,
`β = 1` the expected degree of the sup-norm power-law cut-off model is not differentiable at
`1`; its right derivative there is `4` and its left derivative is `0`. -/
theorem not_differentiableAt_expDegree_concrete :
    ¬ DifferentiableAt ℝ (expDegree 1 1 1) (1 : ℝ) := by
  simpa using not_differentiableAt_expDegree_nat (d := 1) (α := 1) (β := 1) le_rfl one_pos
    one_pos (n := 1) le_rfl

end PercLib.Models.LongRange
