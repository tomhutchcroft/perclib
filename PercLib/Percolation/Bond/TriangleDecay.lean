/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface, from the positive semidefiniteness of the connection
kernel (`ConnectionKernel.lean`). The statements follow the wiki tag 96A2 (connection kernels). No
source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.ConnectionKernel
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.Transport.Reindexing
public import PercLib.Models.Line
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Decay of the open triangle under a uniform triangle bound

Let `μ` be a probability measure on bond configurations (no independence is assumed) and
write `T = connProb μ` (under the independent law `T = tau q`),
`T²(u,x) = ∑' v, T(u,v) T(v,x)`, `T³(u,x) = ∑' v w, T(u,v) T(v,w) T(w,x)`
and `Δₓ = T³(x,x)`.

* `tsum_bilin_sq_le`: for finite-valued `a, b ≥ 0`,
  `(∑ a(u) T(u,v) b(v))² ≤ (∑ a T a)(∑ b T b)` (Cauchy–Schwarz for the positive semidefinite
  kernel `T`, over all of `V`);
* `tendsto_connProb_cofinite`, `tendsto_connProb_sq_cofinite`: if `Δ_v < ⊤` then `T(x,v) → 0`,
  and if moreover `Δ_u < ⊤` then `T²(u,x) → 0`, as `x` leaves finite sets;
* `tendsto_triangle_cofinite` and `exists_finset_triangle_lt` (96A2, item 1): if
  `D = ⨆ x, Δₓ < ⊤`, then `T³(o,x) → 0` along the cofinite filter: for every `ε > 0` there is
  a finite `E` with `T³(o,x) < ε` for `x ∉ E`;
* `tendsto_iSup_triangle` (96A2, item 2): if bijections of `V` preserving `T` and a real
  function `d` act transitively and `Δ_o < ⊤`, then `⨆_{d(u,v) ≥ r} T³(u,v) → 0` as `r → ∞`.

The function `d` need not be a metric: only its invariance is used.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Cauchy–Schwarz for the connection kernel -/

/-- `z² ≤ c² → z ≤ c` in `ℝ≥0∞`. -/
theorem ennreal_le_of_sq_le_sq {z c : ℝ≥0∞} (h : z ^ 2 ≤ c ^ 2) : z ≤ c := by
  have hroot : ∀ w : ℝ≥0∞, (w ^ 2) ^ (1 / 2 : ℝ) = w := fun w => by
    have := ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) w
    simpa [one_div] using this
  have := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [hroot, hroot] at this

/-- A finite bilinear sum against `T`, as a real sum. -/
private theorem sum_bilin_eq_ofReal (μ : Measure (Config V)) [IsFiniteMeasure μ] (F : Finset V)
    (a b : V → ℝ≥0∞) (ha : ∀ u, a u ≠ ⊤) (hb : ∀ v, b v ≠ ⊤) :
    ∑ u ∈ F, ∑ v ∈ F, a u * connProb μ u v * b v =
      ENNReal.ofReal (∑ u ∈ F, ∑ v ∈ F, (a u).toReal * (b v).toReal * (connProb μ u v).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun u _ => Finset.sum_nonneg fun v _ => by positivity]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal (ha u), ENNReal.ofReal_toReal (hb v),
    ENNReal.ofReal_toReal (connProb_ne_top μ u v)]
  ring

private theorem sum_bilin_le_tsum (μ : Measure (Config V)) (F : Finset V)
    (a b : V → ℝ≥0∞) :
    ∑ u ∈ F, ∑ v ∈ F, a u * connProb μ u v * b v ≤ ∑' u, ∑' v, a u * connProb μ u v * b v :=
  (Finset.sum_le_sum fun _ _ => ENNReal.sum_le_tsum F).trans (ENNReal.sum_le_tsum F)

open Classical in
/-- **Cauchy–Schwarz for `T`.** For finite-valued `a, b`,
`(∑' u v, a(u) T(u,v) b(v))² ≤ (∑' u v, a(u) T(u,v) a(v)) (∑' u v, b(u) T(u,v) b(v))`. -/
theorem tsum_bilin_sq_le [Countable V] (μ : Measure (Config V)) [IsFiniteMeasure μ] (a b : V → ℝ≥0∞)
    (ha : ∀ u, a u ≠ ⊤) (hb : ∀ v, b v ≠ ⊤) :
    (∑' u, ∑' v, a u * connProb μ u v * b v) ^ 2 ≤
      (∑' u, ∑' v, a u * connProb μ u v * a v) * ∑' u, ∑' v, b u * connProb μ u v * b v := by
  set P := (∑' u, ∑' v, a u * connProb μ u v * a v) * ∑' u, ∑' v, b u * connProb μ u v * b v
  have hroot : ∀ z : ℝ≥0∞, z ^ 2 ≤ P → z ≤ P ^ (1 / 2 : ℝ) := by
    intro z hz
    have h := ENNReal.rpow_le_rpow hz (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have he : (z ^ 2) ^ (1 / 2 : ℝ) = z := by
      have := ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) z
      simpa [one_div] using this
    rwa [he] at h
  have hfin : ∀ F : Finset V, (∑ u ∈ F, ∑ v ∈ F, a u * connProb μ u v * b v) ^ 2 ≤ P := by
    intro F
    have hcs := sum_connProb_cauchySchwarz μ F (fun u => (a u).toReal) (fun v => (b v).toReal)
    have hsym : ∀ u v, (connProb μ u v).toReal = (connProb μ v u).toReal := fun u v => by
      rw [connProb_comm]
    rw [sum_bilin_eq_ofReal μ F a b ha hb, ← ENNReal.ofReal_pow (Finset.sum_nonneg fun u _ =>
      Finset.sum_nonneg fun v _ => by positivity)]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal _ := ENNReal.ofReal_le_ofReal hcs
      _ = (∑ u ∈ F, ∑ v ∈ F, a u * connProb μ u v * a v) *
            ∑ u ∈ F, ∑ v ∈ F, b u * connProb μ u v * b v := by
          rw [sum_bilin_eq_ofReal μ F a a ha ha, sum_bilin_eq_ofReal μ F b b hb hb,
            ← ENNReal.ofReal_mul (Finset.sum_nonneg fun u _ =>
              Finset.sum_nonneg fun v _ => by positivity)]
      _ ≤ P := mul_le_mul' (sum_bilin_le_tsum μ F a a) (sum_bilin_le_tsum μ F b b)
  have hle : ∑' u, ∑' v, a u * connProb μ u v * b v ≤ P ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.tsum_prod]
    refine ENNReal.summable.tsum_le_of_sum_le fun s => hroot _ ?_
    set F : Finset V := s.image Prod.fst ∪ s.image Prod.snd
    have hsub : s ⊆ F ×ˢ F := fun p hp => Finset.mem_product.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
    have hle : ∑ p ∈ s, a p.1 * connProb μ p.1 p.2 * b p.2 ≤
        ∑ u ∈ F, ∑ v ∈ F, a u * connProb μ u v * b v :=
      (Finset.sum_le_sum_of_subset hsub).trans_eq (Finset.sum_product F F
        (fun p : V × V => a p.1 * connProb μ p.1 p.2 * b p.2))
    exact (pow_le_pow_left₀ bot_le hle 2).trans (hfin F)
  refine (pow_le_pow_left₀ bot_le hle 2).trans_eq ?_
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-! ### Pointwise decay -/

/-- If `Δ_v < ⊤` then `T(x,v) → 0` as `x` leaves finite sets. -/
theorem tendsto_connProb_cofinite (μ : Measure (Config V)) [IsProbabilityMeasure μ] (v : V)
    (hv : ∑' u, ∑' w, connProb μ v u * connProb μ u w * connProb μ w v < ⊤) :
    Tendsto (fun x => connProb μ x v) cofinite (𝓝 0) := by
  have hsq : Tendsto (fun x => connProb μ v x ^ 2) cofinite (𝓝 0) :=
    ENNReal.tendsto_cofinite_zero_of_tsum_ne_top
      ((tsum_connProb_sq_le_triangle μ v).trans_lt hv).ne
  have hcont := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp hsq
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hcont
  refine hcont.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [connProb_comm μ x v]
  have := ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (connProb μ v x)
  simpa [one_div] using this

open Classical in
/-- The tail `∑_{v ∉ H, w ∉ H} T(u,v) T(v,w) T(w,u)` is at most the tail
`∑_{v ∉ H} T(u,v) T²(v,u)` of `Δ_u`. -/
private theorem tail_le (μ : Measure (Config V)) (u : V) (H : Finset V) :
    ∑' v, ∑' w, (if v ∈ H then 0 else connProb μ u v) * connProb μ v w *
        (if w ∈ H then 0 else connProb μ u w) ≤
      ∑' v, (if v ∈ H then 0 else connProb μ u v * ∑' w, connProb μ v w * connProb μ w u) := by
  refine ENNReal.tsum_le_tsum fun v => ?_
  by_cases hv : v ∈ H
  · simp [hv]
  · simp only [hv, ite_false]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    by_cases hw : w ∈ H
    · simp [hw]
    · simp only [hw, ite_false]
      rw [connProb_comm μ u w, mul_assoc]

open Classical in
/-- Tails of a finite triangle are eventually small. -/
private theorem exists_tail_lt (μ : Measure (Config V)) (u : V)
    (hu : ∑' v, ∑' w, connProb μ u v * connProb μ v w * connProb μ w u < ⊤) {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ H : Finset V,
      ∑' v, (if v ∈ H then 0 else connProb μ u v * ∑' w, connProb μ v w * connProb μ w u) < δ := by
  have hsum : ∑' v, connProb μ u v * ∑' w, connProb μ v w * connProb μ w u ≠ ⊤ := by
    refine ne_top_of_le_ne_top hu.ne (le_of_eq ?_)
    exact tsum_congr fun v => by rw [← ENNReal.tsum_mul_left]; simp_rw [mul_assoc]
  have h := ENNReal.tendsto_tsum_compl_atTop_zero hsum
  obtain ⟨H, hH⟩ := (h.eventually (gt_mem_nhds hδ)).exists
  refine ⟨H, lt_of_eq_of_lt ?_ hH⟩
  rw [show (∑' b : {x // x ∉ H}, connProb μ u b * ∑' w, connProb μ b w * connProb μ w u) =
      ∑' v, ({v | v ∉ H} : Set V).indicator
        (fun v => connProb μ u v * ∑' w, connProb μ v w * connProb μ w u) v from
    tsum_subtype {v | v ∉ H} (fun v => connProb μ u v * ∑' w, connProb μ v w * connProb μ w u)]
  exact tsum_congr fun v => by by_cases hv : v ∈ H <;> simp [hv]

open Classical in
/-- `∑' w, [w = x] f w = f x`. -/
private theorem tsum_ite_eq_mul (x : V) (f : V → ℝ≥0∞) :
    ∑' w, (if w = x then (1 : ℝ≥0∞) else 0) * f w = f x := by
  rw [tsum_eq_single x (fun w hw => by simp [hw])]
  simp

open Classical in
/-- If `D = ⨆ x, Δₓ < ⊤`, then `T²(u,x) → 0` as `x` leaves finite sets. -/
theorem tendsto_connProb_sq_cofinite [Countable V] (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (hD : (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) < ⊤) (u : V) :
    Tendsto (fun x => ∑' v, connProb μ u v * connProb μ v x) cofinite (𝓝 0) := by
  have hΔ : ∀ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x < ⊤ := fun x =>
    (le_iSup (fun x => ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) x).trans_lt hD
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  set η := ε / 2 with heta
  have hη : 0 < η := ENNReal.half_pos hε.ne'
  obtain ⟨H, hH⟩ := exists_tail_lt μ u (hΔ u) (δ := η ^ 2) (ENNReal.pow_pos hη 2)
  have htail : ∀ x, ∑' v, (if v ∈ H then 0 else connProb μ u v) * connProb μ v x ≤ η := by
    intro x
    set c : V → ℝ≥0∞ := fun v => if v ∈ H then 0 else connProb μ u v with hcdef
    set e : V → ℝ≥0∞ := fun w => if w = x then 1 else 0 with hedef
    have hc : ∀ v, c v ≠ ⊤ := fun v => by
      by_cases hv : v ∈ H
      · simp [c, hv]
      · simpa [c, hv] using connProb_ne_top μ u v
    have he : ∀ w, e w ≠ ⊤ := fun w => by by_cases hw : w = x <;> simp [e, hw]
    have hcs := tsum_bilin_sq_le μ e c he hc
    have h1 : ∑' w, ∑' v, e w * connProb μ w v * c v = ∑' v, c v * connProb μ v x := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
      rw [tsum_ite_eq_mul x (fun w => ∑' v, connProb μ w v * c v)]
      exact tsum_congr fun v => by rw [connProb_comm, mul_comm]
    have h2 : ∑' w, ∑' v, e w * connProb μ w v * e v = 1 := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
      rw [tsum_ite_eq_mul x (fun w => ∑' v, connProb μ w v * e v)]
      simp_rw [mul_comm (connProb μ x _)]
      rw [tsum_ite_eq_mul x (fun v => connProb μ x v), connProb_self]
    rw [h1, h2, one_mul] at hcs
    exact ennreal_le_of_sq_le_sq (hcs.trans ((tail_le μ u H).trans hH.le))
  have hhead : Tendsto (fun x => ∑ v ∈ H, connProb μ x v) cofinite (𝓝 0) := by
    have := tendsto_finsetSum H (fun v _ => tendsto_connProb_cofinite μ v (hΔ v))
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hhead) η hη] with x hx
  calc ∑' v, connProb μ u v * connProb μ v x
      = ∑' v, (if v ∈ H then connProb μ u v else 0) * connProb μ v x +
          ∑' v, (if v ∈ H then 0 else connProb μ u v) * connProb μ v x := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr fun v => by by_cases hv : v ∈ H <;> simp [hv]
    _ ≤ ∑ v ∈ H, connProb μ x v + η := by
        gcongr
        · rw [tsum_eq_sum (s := H) (fun v hv => by simp [hv])]
          refine Finset.sum_le_sum fun v hv => ?_
          simp only [hv, ite_true]
          rw [connProb_comm μ v x]
          exact mul_le_of_le_one_left' (connProb_le_one μ u v)
        · exact htail x
    _ ≤ η + η := by gcongr
    _ = ε := ENNReal.add_halves ε

/-! ### Item 1: decay of the open triangle -/

open Classical in
/-- **Item 1.** If `D = ⨆ x, Δₓ < ⊤`, then for every `o`, `T³(o,x) → 0` as `x` leaves
finite sets. -/
theorem tendsto_triangle_cofinite [Countable V] (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (hD : (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) < ⊤) (o : V) :
    Tendsto (fun x => ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v x) cofinite
      (𝓝 0) := by
  set D := ⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x with hDdef
  have hΔle : ∀ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x ≤ D := fun x =>
    le_iSup (fun x => ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) x
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  set η := ε / 2 with heta
  have hη : 0 < η := ENNReal.half_pos hε.ne'
  set M := D + 1 with hMdef
  have hM0 : M ≠ 0 := by simp [M]
  have hMt : M ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hD.ne, ENNReal.one_ne_top⟩
  have hδ : 0 < η ^ 2 / M := ENNReal.div_pos (ENNReal.pow_pos hη 2).ne' hMt
  obtain ⟨F, hF⟩ := exists_tail_lt μ o ((hΔle o).trans_lt hD) hδ
  have htail : ∀ x,
      ∑' u, ∑' v, (if u ∈ F then 0 else connProb μ o u) * connProb μ u v * connProb μ v x ≤ η := by
    intro x
    set a : V → ℝ≥0∞ := fun u => if u ∈ F then 0 else connProb μ o u with hadef
    have ha : ∀ u, a u ≠ ⊤ := fun u => by
      by_cases hu : u ∈ F
      · simp [a, hu]
      · simpa [a, hu] using connProb_ne_top μ o u
    have hcs := tsum_bilin_sq_le μ a (fun v => connProb μ v x) ha (fun v => connProb_ne_top μ v x)
    have hb : ∑' u, ∑' v, connProb μ u x * connProb μ u v * connProb μ v x ≤ D := by
      refine le_of_eq_of_le (tsum_congr fun u => tsum_congr fun v => ?_) (hΔle x)
      rw [connProb_comm μ u x]
    refine ennreal_le_of_sq_le_sq (hcs.trans ?_)
    calc (∑' u, ∑' v, a u * connProb μ u v * a v) *
          ∑' u, ∑' v, connProb μ u x * connProb μ u v * connProb μ v x
        ≤ (η ^ 2 / M) * M := by
          gcongr
          · exact (tail_le μ o F).trans hF.le
          · exact hb.trans (le_self_add)
      _ = η ^ 2 := ENNReal.div_mul_cancel hM0 hMt
  have hhead :
      Tendsto (fun x => ∑ u ∈ F, ∑' v, connProb μ u v * connProb μ v x) cofinite (𝓝 0) := by
    have := tendsto_finsetSum F (fun u _ => tendsto_connProb_sq_cofinite μ hD u)
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hhead) η hη] with x hx
  calc ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v x
      = ∑' u, ∑' v, (if u ∈ F then connProb μ o u else 0) * connProb μ u v * connProb μ v x +
          ∑' u, ∑' v, (if u ∈ F then 0 else connProb μ o u) * connProb μ u v * connProb μ v x := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun u => ?_
        rw [← ENNReal.tsum_add]
        exact tsum_congr fun v => by by_cases hu : u ∈ F <;> simp [hu]
    _ ≤ ∑ u ∈ F, ∑' v, connProb μ u v * connProb μ v x + η := by
        gcongr
        · rw [tsum_eq_sum (s := F) (fun u hu => by simp [hu])]
          refine Finset.sum_le_sum fun u hu => ?_
          simp only [hu, ite_true]
          refine ENNReal.tsum_le_tsum fun v => ?_
          rw [mul_assoc]
          exact mul_le_of_le_one_left' (connProb_le_one μ o u)
        · exact htail x
    _ ≤ η + η := by gcongr
    _ = ε := ENNReal.add_halves ε

/-- **Item 1, finite-set form.** If `D = ⨆ x, Δₓ < ⊤`, then for every `o` and `ε > 0`
there is a finite `E` with `T³(o,x) < ε` for every `x ∉ E`. -/
theorem exists_finset_triangle_lt [Countable V] (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (hD : (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) < ⊤) (o : V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ E : Finset V, ∀ x ∉ E, ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v x < ε := by
  have h := (tendsto_triangle_cofinite μ hD o).eventually (gt_mem_nhds hε)
  rw [Filter.eventually_cofinite] at h
  exact ⟨h.toFinset, fun x hx => by simpa using hx⟩

/-! ### Item 2: transitive models -/

/-- A bijection preserving the connection kernel preserves `T³`. -/
theorem triangle_map_eq (μ : Measure (Config V)) (σ : V ≃ V)
    (hσ : ∀ a b, connProb μ (σ a) (σ b) = connProb μ a b) (x y : V) :
    ∑' u, ∑' v, connProb μ (σ x) u * connProb μ u v * connProb μ v (σ y) =
      ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v y := by
  rw [← σ.tsum_eq]
  refine tsum_congr fun u => ?_
  rw [← σ.tsum_eq]
  exact tsum_congr fun v => by rw [hσ, hσ, hσ]

/-- **Item 2.** Suppose bijections of `V` preserving the connection kernel and a function
`d : V → V → ℝ` act transitively, and `Δ_o < ⊤`. Then `⨆_{d(u,v) ≥ r} T³(u,v) → 0` as
`r → ∞` (the empty supremum is `0`). -/
theorem tendsto_iSup_triangle [Countable V] (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ)
    (htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧
      (∀ a b, connProb μ (σ a) (σ b) = connProb μ a b) ∧ ∀ a b, d (σ a) (σ b) = d a b)
    (o : V) (ho : ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o < ⊤) :
    Tendsto (fun r : ℝ => ⨆ u, ⨆ v, ⨆ (_ : r ≤ d u v),
      ∑' w, ∑' z, connProb μ u w * connProb μ w z * connProb μ z v) atTop (𝓝 0) := by
  have hΔ : ∀ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x =
      ∑' u, ∑' v, connProb μ o u * connProb μ u v * connProb μ v o := by
    intro x
    obtain ⟨σ, hσx, hσq, -⟩ := htrans o x
    rw [← hσx, triangle_map_eq μ σ hσq]
  have hD : (⨆ x, ∑' u, ∑' v, connProb μ x u * connProb μ u v * connProb μ v x) < ⊤ := by
    exact (iSup_le fun x => (hΔ x).le).trans_lt ho
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨E, hE⟩ := exists_finset_triangle_lt μ hD o hε
  rw [Filter.eventually_atTop]
  refine ⟨∑ x ∈ E, |d o x| + 1, fun r hr => ?_⟩
  refine iSup_le fun u => iSup_le fun v => iSup_le fun huv => ?_
  obtain ⟨σ, hσu, hσq, hσd⟩ := htrans u o
  rw [← triangle_map_eq μ σ hσq, hσu]
  refine (hE (σ v) fun hv => ?_).le
  have h1 : |d o (σ v)| ≤ ∑ x ∈ E, |d o x| :=
    Finset.single_le_sum (f := fun x => |d o x|) (fun x _ => abs_nonneg _) hv
  have h2 : d o (σ v) = d u v := by rw [← hσu, hσd]
  have h3 := le_abs_self (d o (σ v))
  linarith

/-! ### Non-vacuity -/

/-- Non-vacuity, item 1 on a finite vertex type: `D < ⊤` holds since every `Δₓ ≤ |V|²`. -/
example (q : Sym2 Bool → unitInterval) (o : Bool) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ E : Finset Bool, ∀ x ∉ E, ∑' u, ∑' v, tau q o u * tau q u v * tau q v x < ε := by
  simp only [← connProb_law]
  refine exists_finset_triangle_lt (law q) (lt_of_le_of_lt (iSup_le fun x => ?_)
    (show (4 : ℝ≥0∞) < ⊤ by simp)) o hε
  calc ∑' u, ∑' v, connProb (law q) x u * connProb (law q) u v * connProb (law q) v x
        ≤ ∑' _u : Bool, ∑' _v : Bool, (1 : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => by
          calc connProb (law q) x u * connProb (law q) u v * connProb (law q) v x ≤ 1 * 1 * 1 := by
                gcongr <;> exact connProb_le_one _ _ _
            _ = 1 := by ring
    _ = 4 := by simp [tsum_fintype]; norm_num

/-- Non-vacuity, item 2 on `ℤ` with `q = p < 1` on nearest-neighbour pairs (and `0` elsewhere),
`d(a,b) = |b - a|`, transitive by translations; `Δ₀ ≤ χ² < ⊤`. -/
example (p : unitInterval) (hp : p < 1) :
    ∃ q : Sym2 ℤ → unitInterval, (∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) ∧
      Tendsto (fun r : ℝ => ⨆ u, ⨆ v, ⨆ (_ : r ≤ |((v - u : ℤ) : ℝ)|),
        ∑' w, ∑' z, tau q u w * tau q w z * tau q z v) atTop (𝓝 0) := by
  let q : Sym2 ℤ → unitInterval :=
    Sym2.lift ⟨fun a b => if |b - a| = 1 then p else 0, fun a b => by simp only [abs_sub_comm]⟩
  have hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0 := fun _ _ _ => rfl
  refine ⟨q, hq, ?_⟩
  simp only [← connProb_law]
  refine tendsto_iSup_triangle (law q) (fun u v => |((v - u : ℤ) : ℝ)|) ?_ 0 ?_
  · intro x y
    refine ⟨Equiv.addRight (y - x), by simp, fun a b => ?_, fun a b => ?_⟩
    · simp only [connProb_law]
      refine tau_apply_eq_of_map_law_eq _
        (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q _ fun e => ?_) a b
      induction e using Sym2.ind with
      | _ a b =>
        simp only [Sym2.map_mk, Equiv.coe_addRight, q, Sym2.lift_mk]
        congr 3
        ring
    · simp only [Equiv.coe_addRight]
      congr 2
      ring
  · simp only [connProb_law]
    set C := chi q 0 with hCdef
    have hC : ∀ a, chi q a = C := fun a => by
      rw [PercLib.Models.Line.chi_eq p q hq, hCdef, PercLib.Models.Line.chi_eq p q hq]
    calc ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
        ≤ ∑' u, ∑' v, tau q 0 u * tau q u v * 1 :=
          ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => by
            gcongr; exact tau_le_one q v 0
      _ = ∑' u, tau q 0 u * C := by
          refine tsum_congr fun u => ?_
          simp_rw [mul_one]
          rw [ENNReal.tsum_mul_left, ← chi_eq_tsum_tau, hC]
      _ = C * C := by rw [ENNReal.tsum_mul_right, ← chi_eq_tsum_tau]
      _ < ⊤ := ENNReal.mul_lt_top (PercLib.Models.Line.chi_lt_top p hp q hq 0)
          (PercLib.Models.Line.chi_lt_top p hp q hq 0)

end PercLib.Percolation.Bond
