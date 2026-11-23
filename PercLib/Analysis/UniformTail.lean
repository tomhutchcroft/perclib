/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
-/
module

public import PercLib.Models.LongRange.RestorationDerivativeGeneral

/-!
# Series convergence from uniformly small tails and pointwise convergence

A finite uniformly small-tail condition, together with summability of that tail at each nearby
parameter value, replaces a uniform summable dominator. Finite-prefix Fatou bounds establish
summability of the limiting series explicitly; no non-summable `tsum = 0` convention is used.
-/

@[expose] public section
open Filter
open scoped Topology

namespace PercLib.Analysis

/-- **Tannery's theorem with uniform small tails.**  Let `f r : ι → ℝ` be a family of series
whose tails outside a single finite set are uniformly small along a filter `𝓕`, and suppose every
summand converges along `𝓕`.  Then the sums converge to the sum of the limits, and that limit
series is summable.

Neither a summable majorant of the summands nor pointwise summability *of the limit series* is
assumed: the latter is derived, by the Fatou argument below. -/
theorem tendsto_tsum_of_tendsto_of_uniform_tail {ι : Type*} {𝓕 : Filter ℝ}
    {f : ℝ → ι → ℝ} {g : ι → ℝ}
    (hconv : ∀ e, Tendsto (fun r => f r e) 𝓕 (𝓝 (g e)))
    (htail : ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ r in 𝓕,
      Summable (fun e : ↥(F : Set ι)ᶜ => ‖f r e.1‖) ∧
        ∑' e : ↥(F : Set ι)ᶜ, ‖f r e.1‖ ≤ ε) :
    Tendsto (fun r => ∑' e, f r e) 𝓕 (𝓝 (∑' e, g e)) := by
  rcases 𝓕.eq_or_neBot with rfl | hne
  · simp only [tendsto_bot]
  have hsumm : ∀ᶠ r in 𝓕, Summable (f r) := by
    obtain ⟨F, hF⟩ := htail 1 one_pos
    filter_upwards [hF] with r hr
    exact (summable_subtype_and_compl (s := (F : Set ι)) (f := f r)).1
      ⟨(Summable.of_finite : Summable (fun e : ↥(F : Set ι) => f r e.1)), hr.1.of_norm⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ := htail (ε / 4) (by positivity)
  have hb : ∀ S : Finset ↥(F : Set ι)ᶜ, ∑ e ∈ S, ‖g e.1‖ ≤ ε / 4 := by
    intro S
    have htend : Tendsto (fun r => ∑ e ∈ S, ‖f r e.1‖) 𝓕 (𝓝 (∑ e ∈ S, ‖g e.1‖)) := by
      refine tendsto_finsetSum _ (fun e _ => ?_)
      exact (hconv e.1).norm
    refine le_of_tendsto htend ?_
    filter_upwards [hF] with r hr
    exact (hr.1.sum_le_tsum S (fun i _ => norm_nonneg _)).trans hr.2
  have hgnorm : Summable (fun e : ↥(F : Set ι)ᶜ => ‖g e.1‖) :=
    summable_of_sum_le (f := fun e : ↥(F : Set ι)ᶜ => ‖g e.1‖) (fun e => norm_nonneg _) hb
  have hgtail : ∑' e : ↥(F : Set ι)ᶜ, ‖g e.1‖ ≤ ε / 4 :=
    Real.tsum_le_of_sum_le (f := fun e : ↥(F : Set ι)ᶜ => ‖g e.1‖) (fun e => norm_nonneg _) hb
  have hgsumm' : Summable g :=
    (summable_subtype_and_compl (s := (F : Set ι)) (f := g)).1
      ⟨(Summable.of_finite : Summable (fun e : ↥(F : Set ι) => g e.1)), hgnorm.of_norm⟩
  have hfin : ∀ᶠ r in 𝓕, ‖∑ e ∈ F, (f r e - g e)‖ ≤ ε / 4 := by
    have htend : Tendsto (fun r => ∑ e ∈ F, (f r e - g e)) 𝓕 (𝓝 0) := by
      have h0 : Tendsto (fun r => ∑ e ∈ F, (f r e - g e)) 𝓕
          (𝓝 (∑ e ∈ F, (g e - g e))) :=
        tendsto_finsetSum _ (fun e _ => (hconv e).sub tendsto_const_nhds)
      simpa using h0
    have h2 : Tendsto (fun r => ‖∑ e ∈ F, (f r e - g e)‖) 𝓕 (𝓝 0) := by
      simpa using htend.norm
    exact ((tendsto_order.1 h2).2 (ε / 4) (by positivity)).mono (fun r hr => hr.le)
  filter_upwards [hF, hsumm, hfin] with r hr hs hfr
  rw [dist_eq_norm, ← hs.tsum_sub hgsumm',
    ← (hs.sub hgsumm').sum_add_tsum_compl (s := F)]
  have htaildiff : ‖∑' x : ↥(F : Set ι)ᶜ, (f r x.1 - g x.1)‖ ≤ ε / 4 + ε / 4 := by
    rw [show (∑' x : ↥(F : Set ι)ᶜ, (f r x.1 - g x.1)) =
        (∑' x : ↥(F : Set ι)ᶜ, f r x.1) - ∑' x : ↥(F : Set ι)ᶜ, g x.1 from
      Summable.tsum_sub (f := fun x : ↥(F : Set ι)ᶜ => f r x.1)
        (g := fun x : ↥(F : Set ι)ᶜ => g x.1) hr.1.of_norm hgnorm.of_norm]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_tsum_le_tsum_norm hr.1).trans hr.2
    · exact (norm_tsum_le_tsum_norm hgnorm).trans hgtail
  refine (norm_add_le _ _).trans_lt ?_
  linarith [norm_nonneg (∑' x : ↥(F : Set ι)ᶜ, (f r x.1 - g x.1))]

end PercLib.Analysis
