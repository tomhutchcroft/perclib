/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied. This is a general real-analysis
interchange lemma extracted for the cut-off derivative programme. Mathematical reference:
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1, for the
shape of the (bounded) cut-off derivative formula that is to be passed to the cap limit.
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.Dini

/-!
# Monotone cap removal at the level of derivatives

The cut-off moments of the long-range model are realised as a monotone family `f n` of bounded
("capped") moment functions, each differentiable in the cut-off scale with derivative `f' n`, and
increasing pointwise in the cap `n`. The uncapped moment is the pointwise limit `g` of `f n`, and
the derivative-level cap removal problem asks whether `g` is differentiable with derivative the
pointwise limit `g'` of the capped derivatives `f' n`.

This file isolates the general real-analysis statement behind that step. Its content is that
*no uniform-in-cap estimate on the fluxes is needed*: continuity of every capped flux together
with continuity of the limit flux and pointwise monotone convergence upgrade, via Dini's theorem,
to local uniform convergence of the derivatives, after which mathlib's
`hasDerivAt_of_tendstoLocallyUniformlyOn` gives the derivative.

## Main results

* `PercLib.Analysis.hasDerivAt_of_monotone_tendsto_deriv`: if `s` is open, every `f' n` is
  continuous on `s`, the family `f' n` is pointwise monotone in `n` with pointwise limit `g'`
  continuous on `s`, every `f n` has derivative `f' n` on `s`, and `f n → g` pointwise on `s`,
  then `g` has derivative `g'` at every point of `s`.

Nothing here is specific to percolation; the percolation instance is the family of capped cluster
moments and their pivotal fluxes.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace PercLib.Analysis

/-- **Cap removal for derivatives from monotone capped fluxes.** Let `s` be an open set of scales.
Suppose that for every cap `n` the capped moment `f n` is differentiable on `s` with derivative
`f' n`; that each `f' n` is continuous on `s`; that at each scale the capped derivatives increase
with the cap; that the capped derivatives converge pointwise on `s` to a function `g'` that is
continuous on `s`; and that the capped moments converge pointwise on `s` to `g`. Then `g` is
differentiable on `s` with derivative `g'`.

The only analytic input is Dini's theorem: monotone pointwise convergence of continuous functions
to a continuous limit is locally uniform, so the derivative limit is locally uniform and
`hasDerivAt_of_tendstoLocallyUniformlyOn` applies. No summable majorant of the capped fluxes and no
uniform-in-cap bound on their tails is required. -/
theorem hasDerivAt_of_monotone_tendsto_deriv {s : Set ℝ} (hs : IsOpen s)
    {f f' : ℕ → ℝ → ℝ} {g g' : ℝ → ℝ}
    (hf'c : ∀ n, ContinuousOn (f' n) s)
    (hf'mono : ∀ x ∈ s, Monotone fun n => f' n x)
    (hg' : ContinuousOn g' s)
    (hf'lim : ∀ x ∈ s, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)))
    (hfd : ∀ n, ∀ x ∈ s, HasDerivAt (f n) (f' n x) x)
    (hflim : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {x₀ : ℝ} (hx : x₀ ∈ s) : HasDerivAt g (g' x₀) x₀ :=
  hasDerivAt_of_tendstoLocallyUniformlyOn hs
    (Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto hf'c hf'mono hg' hf'lim)
    (Eventually.of_forall hfd) hflim hx

/-! ### Two pointwise ingredients of the monotonicity in the cap

The two lemmas below are the arithmetic and series halves of the statement that the capped
fluxes increase with the cap. They are stated in the generality in which they are used: the first
is the elementary `min`-arithmetic fact for one increment, the second says that a pointwise
monotone family of summable real series has monotone sums. -/

/-- **The capped increment grows with the cap.** For real volumes `x ≤ y` and caps `B ≤ B'`,
`min y B - min x B ≤ min y B' - min x B'`; equivalently, the loss `t - min t B` has increments
that shrink as the cap grows. This is the one-increment arithmetic behind the pointwise
monotonicity in the cap of the capped pivotal flux. -/
theorem min_sub_min_le_of_le {x y B B' : ℝ} (hxy : x ≤ y) (hBB : B ≤ B') :
    min y B - min x B ≤ min y B' - min x B' := by
  have key : ∀ t : ℝ, min t B = min t B' - max 0 (min t B' - B) := by
    intro t
    rcases le_total t B with h | h
    · rw [min_eq_left h, min_eq_left (le_trans h hBB),
        max_eq_left (by linarith : t - B ≤ 0), sub_zero]
    · rcases le_total t B' with h' | h'
      · rw [min_eq_right h, min_eq_left h',
          max_eq_right (by linarith : (0:ℝ) ≤ t - B)]
        ring
      · rw [min_eq_right h, min_eq_right h',
          max_eq_right (by linarith : (0:ℝ) ≤ B' - B)]
        ring
  have hmono : max 0 (min x B' - B) ≤ max 0 (min y B' - B) :=
    max_le_max le_rfl (sub_le_sub_right (min_le_min hxy le_rfl) B)
  have hx := key x
  have hy := key y
  linarith

/-- **Monotonicity of an edge series in a monotone cap.** If every edge term `a B e` is monotone in
the cap `B` and every cap level is summable over the edge set, then the edge sums are monotone in
the cap. -/
theorem monotone_tsum_of_monotone {ι : Type*} {a : ℕ → ι → ℝ}
    (hmono : ∀ e, Monotone fun B => a B e) (hsum : ∀ B, Summable (a B)) :
    Monotone fun B => ∑' e, a B e := by
  intro B B' hBB
  exact Summable.tsum_le_tsum (fun e => hmono e hBB) (hsum B) (hsum B')

end PercLib.Analysis
