/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The integration and exhaustion steps of the supercritical density bound (L0TE, second
half), with the finite-volume differential inequality as an ordinary hypothesis. New proofs
from the escape-probability theorems of this library and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679's monotonicity from derivatives. No upstream code
is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.IntensityMonotone
public import PercLib.Percolation.Bond.ProfileRegularity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # The supercritical density bound from the differential inequality

* `sub_le_mul_of_hasDerivAt` (item 1): `f' ≥ (1 − f)/s` on `(a,b)`, `f a ≥ 0` give
  `b f(b) ≥ b − a`; `one_sub_le_mul_of_hasDerivAt` is the `p`-form.
* `one_sub_div_le_of_hasDerivAt`: on `(t, ∞)` the inequality gives `f β ≥ 1 − t/β`.
* `law_cluster_infinite_ge_of_escape` (item 2): exhaustion.
* `law_cluster_infinite_ge_of_escape_deriv`, `rootCriticalIntensity_le_of_escape_deriv`
  (item 3): conditional supercritical bound and `β_c ≤ t`; `min_div_le_one_sub_div` is the
  closing real inequality.

The escape probability from a finite `Λ` is `law q_β (⋃ w ∉ Λ, conn o w)`; along the real
parameter it is written
`(law (intensityProfile J s.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-! ### Item 1: integration -/

/-- **Integration lemma.** Let `0 < a ≤ b`, `f` continuous on `[a,b]` with `f a ≥ 0`, and
`f' s ≥ (1 − f s)/s` for a derivative `f'` on `(a,b)`. Then `b f(b) ≥ b − a`. -/
theorem sub_le_mul_of_hasDerivAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b)) (hfa : 0 ≤ f a)
    (hd : ∀ s ∈ Ioo a b, HasDerivAt f (f' s) s ∧ (1 - f s) / s ≤ f' s) :
    b - a ≤ b * f b := by
  have hmono : MonotoneOn (fun s => s * f s - s) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      ((continuousOn_id.mul hc).sub continuousOn_id) (f' := fun s => f s + s * f' s - 1)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      have h := (((hasDerivAt_id s).mul (hd s hs).1).sub (hasDerivAt_id s)).hasDerivWithinAt
        (s := interior (Icc a b))
      refine h.congr_deriv ?_
      simp
    · rw [interior_Icc] at hs
      have hs0 : 0 < s := ha.trans hs.1
      have h := (hd s hs).2
      rw [div_le_iff₀ hs0] at h
      linarith
  have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at this
  nlinarith [mul_nonneg ha.le hfa]

/-- **Integration lemma, `p`-form.** If `0 < t ≤ p < 1`, `g` is continuous on `[t,p]` and
`g' s ≥ (1 − g s)/(s(1 − s))` on `(t,p)`, then
`1 − g p ≤ (1 − g t) · t(1 − p)/(p(1 − t))`. -/
theorem one_sub_le_mul_of_hasDerivAt {t p : ℝ} (ht : 0 < t) (htp : t ≤ p) (hp : p < 1)
    {g g' : ℝ → ℝ} (hc : ContinuousOn g (Icc t p))
    (hd : ∀ s ∈ Ioo t p, HasDerivAt g (g' s) s ∧ (1 - g s) / (s * (1 - s)) ≤ g' s) :
    1 - g p ≤ (1 - g t) * (t * (1 - p) / (p * (1 - t))) := by
  -- `h s = (1 − g s) · s / (1 − s)` is antitone on `[t,p]`.
  have h1 : ∀ s ∈ Icc t p, 0 < 1 - s := fun s hs => by linarith [hs.2]
  have hanti : AntitoneOn (fun s => (1 - g s) * (s / (1 - s))) (Icc t p) := by
    have hm : MonotoneOn (fun s => -((1 - g s) * (s / (1 - s)))) (Icc t p) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t p) ?_
        (f' := fun s => -(-g' s * (s / (1 - s)) + (1 - g s) * (1 / (1 - s) ^ 2)))
        (fun s hs => ?_) (fun s hs => ?_)
      · refine ((continuousOn_const.sub hc).mul (continuousOn_id.div
          (continuousOn_const.sub continuousOn_id) fun s hs => (h1 s hs).ne')).neg
      · rw [interior_Icc] at hs
        have hs1 : (1 - s) ≠ 0 := (h1 s (Ioo_subset_Icc_self hs)).ne'
        have hq : HasDerivAt (fun s => s / (1 - s)) (1 / (1 - s) ^ 2) s := by
          have := (hasDerivAt_id s).div ((hasDerivAt_id s).const_sub 1) hs1
          refine this.congr_deriv ?_
          simp only [id]
          ring
        have h := ((((hd s hs).1.const_sub 1).mul hq).neg).hasDerivWithinAt
          (s := interior (Icc t p))
        convert h using 1
      · rw [interior_Icc] at hs
        have hs0 : 0 < s := ht.trans hs.1
        have hs1 : 0 < 1 - s := h1 s (Ioo_subset_Icc_self hs)
        have h := (hd s hs).2
        rw [div_le_iff₀ (mul_pos hs0 hs1)] at h
        have e : -(-g' s * (s / (1 - s)) + (1 - g s) * (1 / (1 - s) ^ 2)) =
            (g' s * (s * (1 - s)) - (1 - g s)) / (1 - s) ^ 2 := by
          field_simp
          ring
        rw [e]
        exact div_nonneg (by linarith) (by positivity)
    exact fun x hx y hy hxy => neg_le_neg_iff.1 (hm hx hy hxy)
  have hle := hanti ⟨le_rfl, htp⟩ ⟨htp, le_rfl⟩ htp
  simp only at hle
  have hp0 : 0 < p := ht.trans_le htp
  have hp1 : 0 < 1 - p := by linarith
  have ht1 : 0 < 1 - t := by linarith
  have e : (1 - g t) * (t * (1 - p) / (p * (1 - t))) =
      (1 - g t) * (t / (1 - t)) * ((1 - p) / p) := by
    field_simp
  rw [e]
  have e2 : 1 - g p = (1 - g p) * (p / (1 - p)) * ((1 - p) / p) := by
    field_simp
  rw [e2]
  exact mul_le_mul_of_nonneg_right hle (div_nonneg hp1.le hp0.le)

/-- On `(t, ∞)` with `t ≥ 0`: if `f ≥ 0` and `f' s ≥ (1 − f s)/s` for a derivative `f'`,
then `f β ≥ 1 − t/β` for every `β > t`. -/
theorem one_sub_div_le_of_hasDerivAt {t : ℝ} (ht : 0 ≤ t) {f f' : ℝ → ℝ}
    (hd : ∀ s, t < s → HasDerivAt f (f' s) s ∧ (1 - f s) / s ≤ f' s)
    (h0 : ∀ s, t < s → 0 ≤ f s) {β : ℝ} (hβ : t < β) :
    1 - t / β ≤ f β := by
  have hβ0 : 0 < β := ht.trans_lt hβ
  -- For every `a ∈ (t, β)`, `f β ≥ 1 − a/β`.
  have key : ∀ a, t < a → a < β → 1 - a / β ≤ f β := fun a hta haβ => by
    have hc : ContinuousOn f (Icc a β) := fun s hs =>
      (hd s (hta.trans_le hs.1)).1.continuousAt.continuousWithinAt
    have h := sub_le_mul_of_hasDerivAt (ht.trans_lt hta) haβ.le hc (h0 a hta)
      fun s hs => hd s (hta.trans hs.1)
    rw [sub_div' hβ0.ne', div_le_iff₀ hβ0]
    linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set δ := min (ε * β / 2) ((β - t) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
  have hδ1 : δ ≤ ε * β / 2 := min_le_left _ _
  have hδ2 : δ ≤ (β - t) / 2 := min_le_right _ _
  have h := key (t + δ) (by linarith) (by linarith)
  have e : 1 - (t + δ) / β = 1 - t / β - δ / β := by ring
  have hδβ : δ / β ≤ ε / 2 := by rw [div_le_iff₀ hβ0]; linarith
  linarith

/-! ### Item 2: exhaustion -/

/-- **Exhaustion.** If the escape probability from every set of an increasing exhaustion
by finite sets is at least `c`, so is the probability that the cluster is infinite. -/
theorem law_cluster_infinite_ge_of_escape {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) {Λ : ℕ → Finset V} (hΛ : Monotone Λ)
    (hcov : ∀ v, ∃ n, v ∈ Λ n) (o : V) {c : ℝ≥0∞}
    (h : ∀ n, c ≤ law q (⋃ y ∈ (Λ n : Set V)ᶜ, conn o y)) :
    c ≤ law q {ω | (cluster ω o).Infinite} := by
  rw [law_cluster_infinite_eq_iInf_escape q (F := fun n => (Λ n : Set V))
    (fun m n hmn => Finset.coe_subset.2 (hΛ hmn)) (fun n => (Λ n).finite_toSet) hcov o]
  exact le_iInf h

/-! ### Item 3: the conditional supercritical bound -/

/-- **Conditional supercritical bound.** Let `t ≥ 0`. Suppose that for every finite
`Λ ∋ o` the escape probability `f_Λ(s)` has a derivative `f'_Λ(s) ≥ (1 − f_Λ(s))/s` at
every `s > t` (in particular it is continuous on `(t, ∞)`). Then
`law q_β {(cluster ω o).Infinite} ≥ 1 − t/β` for every `β > t`. -/
theorem law_cluster_infinite_ge_of_escape_deriv {V : Type*} [Countable V]
    (J : Sym2 V → ℝ≥0) (o : V) {t : ℝ} (ht : 0 ≤ t) (F' : Finset V → ℝ → ℝ)
    (hF : ∀ Λ : Finset V, o ∈ Λ → ∀ s, t < s →
      HasDerivAt (fun r : ℝ =>
        (law (intensityProfile J r.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal)
        (F' Λ s) s ∧
      (1 - (law (intensityProfile J s.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal) / s ≤
        F' Λ s)
    (β : ℝ≥0) (hβ : t < β) :
    ENNReal.ofReal (1 - t / β) ≤ law (intensityProfile J β) {ω | (cluster ω o).Infinite} := by
  classical
  obtain ⟨S, hS, hcov⟩ := exists_finset_exhaustion (V := V)
  have hΛ : Monotone fun n => insert o (S n) := fun m n h => Finset.insert_subset_insert o (hS h)
  refine law_cluster_infinite_ge_of_escape _ hΛ
    (fun v => (hcov v).imp fun n hn => Finset.mem_insert_of_mem hn) o fun n => ?_
  have h := one_sub_div_le_of_hasDerivAt ht (hF (insert o (S n)) (Finset.mem_insert_self o _))
    (fun s _ => ENNReal.toReal_nonneg) hβ
  simp only [Real.toNNReal_coe] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- **Conditional supercritical bound, threshold form.** Under the same hypotheses,
`rootCriticalIntensity J o ≤ t`. -/
theorem rootCriticalIntensity_le_of_escape_deriv {V : Type*} [Countable V]
    (J : Sym2 V → ℝ≥0) (o : V) {t : ℝ} (ht : 0 ≤ t) (F' : Finset V → ℝ → ℝ)
    (hF : ∀ Λ : Finset V, o ∈ Λ → ∀ s, t < s →
      HasDerivAt (fun r : ℝ =>
        (law (intensityProfile J r.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal)
        (F' Λ s) s ∧
      (1 - (law (intensityProfile J s.toNNReal) (⋃ y ∈ (Λ : Set V)ᶜ, conn o y)).toReal) / s ≤
        F' Λ s) :
    rootCriticalIntensity J o ≤ ENNReal.ofReal t := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨β, htβ, hβc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have htβ' : t < β := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht] at htβ
  have hpos : 0 < law (intensityProfile J β) {ω | (cluster ω o).Infinite} := by
    refine lt_of_lt_of_le ?_ (law_cluster_infinite_ge_of_escape_deriv J o ht F' hF β htβ')
    rw [ENNReal.ofReal_pos, sub_pos, div_lt_one (ht.trans_lt htβ')]
    exact htβ'
  have hle : rootCriticalIntensity J o ≤ β := sInf_le ⟨β, rfl, hpos⟩
  exact absurd hβc (not_lt.2 hle)

/-- The closing inequality: for `0 ≤ β_c < β`,
`min (β − β_c) 1 / (β_c + 1) ≤ 1 − β_c / β`. -/
theorem min_div_le_one_sub_div {βc β : ℝ} (hc : 0 ≤ βc) (hβ : βc < β) :
    min (β - βc) 1 / (βc + 1) ≤ 1 - βc / β := by
  have hβ0 : 0 < β := hc.trans_lt hβ
  have e : 1 - βc / β = (β - βc) / β := by field_simp
  rw [e]
  rcases le_total β (βc + 1) with h | h
  · rw [min_eq_left (by linarith)]
    exact div_le_div_of_nonneg_left (by linarith) hβ0 h
  · rw [min_eq_right (by linarith), div_le_div_iff₀ (by linarith) hβ0]
    nlinarith

/-! ### Non-vacuity witnesses -/

/-- The derivative of `s ↦ 1 − 1/s`. -/
theorem hasDerivAt_one_sub_one_div {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun r : ℝ => 1 - 1 / r) (1 / s ^ 2) s := by
  have := (hasDerivAt_inv hs).const_sub 1
  simp only [one_div]
  convert this using 1
  simp

/-- The equality case of item 1: `f s = 1 − a/s` on `[1, 2]` with `a = 1`. -/
example : (2 : ℝ) - 1 ≤ 2 * (fun s : ℝ => 1 - 1 / s) 2 :=
  sub_le_mul_of_hasDerivAt (f := fun s : ℝ => 1 - 1 / s) (f' := fun s => 1 / s ^ 2)
    one_pos one_le_two
    (fun s hs => (hasDerivAt_one_sub_one_div
      (by linarith [hs.1] : s ≠ 0)).continuousAt.continuousWithinAt) (by norm_num)
    fun s hs => by
      have hs0 : s ≠ 0 := by linarith [hs.1]
      refine ⟨hasDerivAt_one_sub_one_div hs0, le_of_eq ?_⟩
      field_simp
      ring

/-- The `p`-form with `g ≡ 1`: the hypotheses hold and both sides vanish. -/
example : 1 - (fun _ : ℝ => (1 : ℝ)) (1 / 2) ≤
    (1 - (fun _ : ℝ => (1 : ℝ)) (1 / 4)) * (1 / 4 * (1 - 1 / 2) / (1 / 2 * (1 - 1 / 4))) :=
  one_sub_le_mul_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num) (g' := fun _ => 0)
    continuousOn_const fun s _ => ⟨hasDerivAt_const s 1, by simp⟩

/-- Item 3's real hypothesis is satisfiable: `f s = 1 − t/s` on `(t, ∞)` with `t = 1`
meets it with equality, and the conclusion is the equality `f 2 = 1 − 1/2`. -/
example : 1 - 1 / (2 : ℝ) ≤ (fun s : ℝ => 1 - 1 / s) 2 :=
  one_sub_div_le_of_hasDerivAt (f := fun s : ℝ => 1 - 1 / s) (f' := fun s => 1 / s ^ 2)
    zero_le_one
    (fun s hs => by
      have hs0 : s ≠ 0 := by linarith
      refine ⟨hasDerivAt_one_sub_one_div hs0, le_of_eq ?_⟩
      field_simp
      ring)
    (fun s hs => by
      have : 1 / s ≤ 1 := by rw [div_le_one (by linarith)]; exact hs.le
      linarith) one_lt_two

end PercLib.Percolation.Bond
