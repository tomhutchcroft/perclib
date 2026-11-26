/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Left-continuity of the susceptibility in the intensity, and finite susceptibility forces a
contracting finite set. New proofs from the regularity, local-connectivity and intensity
theorems of this library and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679's
lower semicontinuity of sums and Tannery's theorem. No upstream code is copied and no
definition is added.
-/
module

public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Order.Filter.AtTopBot.Finset
public import PercLib.Models.Line

/-! # Left-continuity of `χ` and contracting finite sets

For a finite `T ∋ o`, `τ_T(o,u)` is the probability that `o` and `u` are joined inside `T`
and `Φ_q(o,T) = ∑_{u ∈ T} ∑'_{v ∉ T} τ_T(o,u) q s(u,v)`; both are written out.

* `tendsto_chi_intensity_nhdsLT`: `β ↦ chi q_β x` is left-continuous in `ℝ≥0∞`, infinite
  values allowed.
* `tendsto_boundaryFlux_exhaustion` (RDF0, `⇒`): bounded off-diagonal rows and
  `chi q o < ⊤` give `Φ_q(o, T_n) → 0` along any increasing exhaustion by finite sets
  containing `o`.
* `exists_boundaryFlux_lt_one_of_chi_lt_top`: for intensity kernels with uniformly bounded
  rows, `chi q_β o < ⊤` gives a finite `T ∋ o` with `Φ_{q_β}(o,T) < 1`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### Left-continuity (item 1) -/

/-- The susceptibility is lower semicontinuous in the intensity. -/
theorem lowerSemicontinuous_chi_intensity (J : Sym2 V → ℝ≥0) (x : V) :
    LowerSemicontinuous fun β : ℝ≥0 => chi (intensityProfile J β) x := by
  simp_rw [chi_eq_tsum_tau]
  exact lowerSemicontinuous_tsum fun y => (lowerSemicontinuous_tau x y).comp
    (continuous_pi fun e => (continuous_intensityProfile J e).subtype_mk _)

/-- **Left-continuity of `χ`.** For every `x` and `b`,
`chi q_β x → chi q_b x` as `β ↑ b`, in `ℝ≥0∞` (infinite values allowed). -/
theorem tendsto_chi_intensity_nhdsLT (J : Sym2 V → ℝ≥0) (x : V) (b : ℝ≥0) :
    Tendsto (fun β : ℝ≥0 => chi (intensityProfile J β) x) (𝓝[<] b)
      (𝓝 (chi (intensityProfile J b) x)) :=
  (continuousWithinAt_Iic_of_lowerSemicontinuous_of_monotone
    (lowerSemicontinuous_chi_intensity J x)
    (fun _ _ h => chi_mono (fun e => intensityProfile_mono J h e) x) b).tendsto.mono_left
    (nhdsWithin_mono _ Iio_subset_Iic_self)

/-! ### Finite susceptibility gives contraction (item 2) -/

omit [Countable V] in
/-- An internal connection probability is at most the two-point function. -/
theorem law_localConn_le_tau (q : Sym2 V → unitInterval) (T : Set V) (o u : V) :
    law q (localConn T o u) ≤ tau q o u :=
  measure_mono fun _ ⟨ho, hu, h⟩ => conn_of_localConn _ T ⟨o, ho⟩ ⟨u, hu⟩ h

omit [Countable V] in
open Classical in
/-- The exterior tails of a finite off-diagonal row tend to zero along an exhaustion. -/
theorem tendsto_exteriorRow_zero (q : Sym2 V → unitInterval) (u : V)
    (hrow : rowSum (fun e => unitInterval.toENNReal (q e)) u ≠ ∞)
    {T : ℕ → Finset V} (hT : Monotone T) (hcov : ∀ v, ∃ n, v ∈ T n) :
    Tendsto (fun n => ∑' v, if v ∈ T n then 0 else
      (if v = u then 0 else (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_tsum_compl_atTop_zero hrow).comp
    (tendsto_atTop_finset_of_monotone hT hcov)
  refine h.congr fun n => ?_
  simp only [Function.comp]
  refine (tsum_subtype {x : V | x ∉ T n} (fun v => if v = u then 0 else
    (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))).trans (tsum_congr fun v => ?_)
  by_cases hv : v ∈ T n <;> simp [Set.indicator, hv]

open Classical in
/-- **`⇒` direction.** If the off-diagonal rows of `q` are bounded by `Q < ⊤` and
`chi q o < ⊤`, then along any increasing sequence of finite sets `T_n` exhausting `V`,
`Φ_q(o, T_n) → 0`. (The hypothesis `o ∈ T_n` is not needed: the internal
connection probability vanishes when `o ∉ T_n`.) -/
theorem tendsto_boundaryFlux_exhaustion (q : Sym2 V → unitInterval) {Q : ℝ≥0∞} (hQ : Q < ⊤)
    (hrow : ∀ u, rowSum (fun e => unitInterval.toENNReal (q e)) u ≤ Q)
    {o : V} (hchi : chi q o < ⊤) {T : ℕ → Finset V} (hT : Monotone T)
    (hcov : ∀ v, ∃ n, v ∈ T n) :
    Tendsto (fun n => boundaryFlux q (T n) o) atTop (𝓝 0) := by
  -- The exterior row of `u` beyond `T n`, with the diagonal removed.
  set R : ℕ → V → ℝ≥0∞ := fun n u => ∑' v, if v ∈ T n then 0 else
      (if v = u then 0 else (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) with hR
  have hRle : ∀ n u, R n u ≤ Q := fun n u =>
    (ENNReal.tsum_le_tsum fun v => by split_ifs <;> simp).trans
      ((rowSum_toENNReal q u).ge.trans (hrow u))
  have hRlim : ∀ u, Tendsto (fun n => R n u) atTop (𝓝 0) := fun u =>
    tendsto_exteriorRow_zero q u ((hrow u).trans_lt hQ).ne hT hcov
  -- The dominating summable sequence `Q · tau q o u`.
  have hsum_tau : (∑' u, tau q o u) ≠ ∞ := by rw [← chi_eq_tsum_tau]; exact hchi.ne
  have htau_ne : ∀ u, tau q o u ≠ ∞ := fun u => (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  -- Upper bound `Φ_n ≤ ∑' u, tau q o u * R n u`.
  have hle : ∀ n, (boundaryFlux q (T n) o) ≤ ∑' u, tau q o u * R n u := by
    intro n
    refine le_trans (Finset.sum_le_sum fun u hu => ?_) (ENNReal.sum_le_tsum _)
    simp only [hR]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv : v ∈ T n
    · simp [hv]
    · have hvu : v ≠ u := fun h => hv (h ▸ hu)
      simp only [hv, hvu, ite_false]
      exact mul_le_mul' (law_localConn_le_tau q _ o u) le_rfl
  -- Tannery's theorem in `ℝ` for `tau q o u * R n u`.
  have hfin : ∀ n u, tau q o u * R n u ≠ ∞ := fun n u =>
    ENNReal.mul_ne_top (htau_ne u) ((hRle n u).trans_lt hQ).ne
  have hreal : Tendsto (fun n => ∑' u, (tau q o u * R n u).toReal) atTop (𝓝 (∑' _u : V, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence (bound := fun u => (Q * tau q o u).toReal)
      (ENNReal.summable_toReal (by
        rw [ENNReal.tsum_mul_left]; exact ENNReal.mul_ne_top hQ.ne hsum_tau))
      (fun u => by
        have h1 := ENNReal.Tendsto.const_mul (hRlim u) (Or.inr (htau_ne u))
        rw [mul_zero] at h1
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
        rw [ENNReal.toReal_zero] at this
        exact this)
      (Eventually.of_forall fun n u => by
        rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top hQ.ne (htau_ne u))
          ((mul_le_mul' le_rfl (hRle n u)).trans_eq (mul_comm _ _)))
  rw [tsum_zero] at hreal
  have hen : ∀ n, ∑' u, tau q o u * R n u = ENNReal.ofReal (∑' u, (tau q o u * R n u).toReal) := by
    intro n
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg)]
    · exact tsum_congr fun u => (ENNReal.ofReal_toReal (hfin n u)).symm
    · exact ENNReal.summable_toReal (ne_top_of_le_ne_top
        (by rw [ENNReal.tsum_mul_left]; exact ENNReal.mul_ne_top hQ.ne hsum_tau)
        (ENNReal.tsum_le_tsum fun u => (mul_le_mul' le_rfl (hRle n u)).trans_eq (mul_comm _ _)))
  have hlim : Tendsto (fun n => ∑' u, tau q o u * R n u) atTop (𝓝 0) := by
    simp_rw [hen]
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rw [ENNReal.ofReal_zero] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) hle

open Classical in
/-- **`⇒` direction, existence form.** Under the same hypotheses, some finite `T ∋ o`
has `Φ_q(o,T) < 1`. -/
theorem exists_boundaryFlux_lt_one (q : Sym2 V → unitInterval) {Q : ℝ≥0∞} (hQ : Q < ⊤)
    (hrow : ∀ u, rowSum (fun e => unitInterval.toENNReal (q e)) u ≤ Q)
    {o : V} (hchi : chi q o < ⊤) :
    ∃ T : Finset V, o ∈ T ∧ boundaryFlux q T o < 1 := by
  obtain ⟨S, hS, hcov⟩ := exists_finset_exhaustion (V := V)
  have hT : Monotone fun n => insert o (S n) := fun m n h => Finset.insert_subset_insert o (hS h)
  have h := tendsto_boundaryFlux_exhaustion q hQ hrow hchi hT
    (fun v => (hcov v).imp fun n hn => Finset.mem_insert_of_mem hn)
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
  exact ⟨_, Finset.mem_insert_self o _, hn⟩

open Classical in
/-- **Corollary for intensity kernels.** If every off-diagonal row of `J` is at most `M` and
`chi q_β o < ⊤`, then some finite `T ∋ o` has `Φ_{q_β}(o,T) < 1`. -/
theorem exists_boundaryFlux_lt_one_of_chi_lt_top (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0) {o : V}
    (hchi : chi (intensityProfile J β) o < ⊤) :
    ∃ T : Finset V, o ∈ T ∧ boundaryFlux (intensityProfile J β) T o < 1 :=
  exists_boundaryFlux_lt_one _ (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)
    (fun u => by convert intensity_rowSum_le J M hJ β u) hchi

/-! ### Non-vacuity witnesses -/

/-- The nearest-neighbour intensity on `ℤ`. -/
theorem exists_nearestNeighbour_kernel :
    ∃ J : Sym2 ℤ → ℝ≥0, ∀ a b, J s(a, b) = if |b - a| = 1 then 1 else 0 :=
  ⟨Sym2.lift ⟨fun a b => if |b - a| = 1 then 1 else 0, fun a b => by
      simp only [abs_sub_comm]⟩, fun _ _ => rfl⟩

/-- Item 1 on the nearest-neighbour line at `b = 1`: `χ` is explicit there
(`PercLib.Models.Line.chi_eq`) and is the left limit of `χ`. -/
example : ∃ J : Sym2 ℤ → ℝ≥0,
    Tendsto (fun β : ℝ≥0 => chi (intensityProfile J β) 0) (𝓝[<] 1)
      (𝓝 ((1 + (unitInterval.toNNReal (intensityProfile J 1 s(0, 1)) : ℝ≥0∞)) /
        (1 - (unitInterval.toNNReal (intensityProfile J 1 s(0, 1)) : ℝ≥0∞)))) := by
  obtain ⟨J, hJ⟩ := exists_nearestNeighbour_kernel
  refine ⟨J, ?_⟩
  rw [← PercLib.Models.Line.chi_eq (intensityProfile J 1 s(0, 1)) _ (fun a b hab => ?_) 0]
  · exact tendsto_chi_intensity_nhdsLT J 0 1
  · split_ifs with h
    · exact Subtype.ext (by simp only [intensityProfile, hJ, h]; norm_num)
    · exact intensityProfile_eq_zero_of_eq_zero J (by rw [hJ, ite_eq_right h]) 1

open Classical in
/-- Item 2 with `q = 0` on `ℤ`: `χ = 1 < ⊤` and the rows vanish, so some finite `T ∋ 0` has
`Φ < 1` (here `Φ = 0`). -/
example : ∃ T : Finset ℤ, 0 ∈ T ∧ ∑ u ∈ T, ∑' v, (if v ∈ T then 0 else
    law (fun _ : Sym2 ℤ => (0 : unitInterval))
      (localConn (T : Set ℤ) 0 u) *
    (unitInterval.toNNReal (0 : unitInterval) : ℝ≥0∞)) < 1 := by
  have := exists_boundaryFlux_lt_one (V := ℤ) (fun _ => 0) (Q := 0) ENNReal.zero_lt_top
    (fun u => by simp) (o := 0)
    (by rw [chi_eq_one_of_offDiagonal_zero _ (fun _ _ _ => rfl)]; exact ENNReal.one_lt_top)
  obtain ⟨T, hT, h⟩ := this
  rw [boundaryFlux_def] at h
  exact ⟨T, hT, by convert h⟩

end PercLib.Percolation.Bond
