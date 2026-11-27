/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. Mathematical reference:
H. Kesten, "Scaling relations for 2D-percolation", Comm. Math. Phys. 109 (1987).
-/
module

public import PercLib.Percolation.Bond.ArmContraction
public import PercLib.Percolation.Bond.ClusterMoments
public import PercLib.Percolation.Bond.Tightness.Hyperscaling
public import PercLib.Probability.TailComparison

/-!
# A conditional planar volume-tail bound

Let `μ` be the law of a random subgraph of `ℤ^d` whose open pairs are almost surely
nearest-neighbour bonds. A nearest-neighbour path changes the sup-norm by at most one per
step, so a cluster that leaves the box `Λ_r = {‖x‖_∞ ≤ r}` meets the vertex boundary
`∂Λ_r = {‖x‖_∞ = r}`. On `ℤ²`, the two-point bound `P(0 ↔ x) ≤ C₂ (1+‖x‖_∞)^{-η}` with
`0 < η < 2` gives `E|K_0 ∩ Λ_r| ≤ C r^{2-η}`. Together with an arm bound
`P(0 ↔ ∂Λ_r) ≤ C₁ r^{-η/2}`, the escape and window-mean comparison of
`PercLib/Probability/TailComparison.lean` gives `P(|K_0| ≥ n) ≤ C n^{-η/(4-η)}`, and a
volume-tail exponent `δ`, when it exists, satisfies `δ ≤ (4-η)/η`.

## Main results

* `exists_mem_cluster_norm_eq`: a cluster reaching sup-norm `≥ r` meets `{‖x‖ = r}`.
* `sum_Icc_one_add_abs_rpow_neg_le`, `sum_piFinset_Icc_one_add_norm_rpow_neg_le`:
  power sums over boxes of `ℤ` and `ℤ²`.
* `lintegral_encard_cluster_inter_eq_sum`: `E|K_v ∩ F| = ∑_{x ∈ F} P(v ↔ x)` for any measure.
* `measure_encard_cluster_ge_le_of_arm_of_two_point`,
  `le_of_log_tail_exponent_of_arm_of_two_point`: the planar statements.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter PercLib.Models.Site PercLib.Probability
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-- The sup-norm of a vertex of `ℤ^d` is a natural number. -/
theorem exists_norm_eq_natCast (x : Fin d → ℤ) : ∃ m : ℕ, ‖x‖ = m := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · exact ⟨0, by simp [Subsingleton.elim x 0]⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    Finset.univ_nonempty fun j => ‖x j‖₊
  refine ⟨(x i).natAbs, ?_⟩
  rw [Pi.norm_def, hi, coe_nnnorm, Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

/-- Box membership is a sup-norm bound. -/
theorem mem_piFinset_Icc_iff_norm_le (r : ℕ) (x : Fin d → ℤ) :
    x ∈ Fintype.piFinset (fun _ => Finset.Icc (-(r : ℤ)) r) ↔ ‖x‖ ≤ r := by
  rw [Fintype.mem_piFinset, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg r)]
  refine forall_congr' fun i => ?_
  rw [Finset.mem_Icc, Int.norm_eq_abs, ← abs_le]
  exact_mod_cast Iff.rfl

/-- **Discrete intermediate values.** Along a walk of open pairs that are nearest-neighbour
bonds, from sup-norm at most `r` to sup-norm at least `r`, some vertex has sup-norm `r`. -/
theorem exists_mem_support_norm_eq {ω : Config (Fin d → ℤ)} (hω : ω ⊆ (zdGraph d).edgeSet)
    (r : ℕ) {a b : Fin d → ℤ} (w : (openGraph ω).Walk a b) (ha : ‖a‖ ≤ r) (hb : (r : ℝ) ≤ ‖b‖) :
    ∃ v ∈ w.support, ‖v‖ = r := by
  induction w with
  | nil => exact ⟨_, SimpleGraph.Walk.start_mem_support _, le_antisymm ha hb⟩
  | @cons a c b hac p ih =>
    by_cases har : ‖a‖ = r
    · exact ⟨a, SimpleGraph.Walk.start_mem_support _, har⟩
    have hlt : ‖a‖ < r := lt_of_le_of_ne ha har
    obtain ⟨m, hm⟩ := exists_norm_eq_natCast a
    have hm' : m + 1 ≤ r := by
      rw [hm] at hlt
      exact_mod_cast hlt
    have hadj : (zdGraph d).Adj a c :=
      (SimpleGraph.mem_edgeSet _).1 (hω ((openGraph_adj_iff ω a c).1 hac).1)
    have hca := norm_sub_le_one_of_zdGraph_adj hadj
    have hc : ‖c‖ ≤ r := by
      have := norm_add_le (c - a) a
      rw [sub_add_cancel] at this
      have hr : ((m : ℝ) + 1) ≤ r := by exact_mod_cast hm'
      linarith
    obtain ⟨v, hv, hvr⟩ := ih hc hb
    exact ⟨v, SimpleGraph.Walk.support_cons _ _ ▸ List.mem_cons_of_mem _ hv, hvr⟩

/-- **A cluster reaching sup-norm `≥ r` meets `∂Λ_r`.** If every open pair is a
nearest-neighbour bond and `K_0` contains `x` with `‖x‖ ≥ r`, then `K_0` contains a
vertex of sup-norm exactly `r`. -/
theorem exists_mem_cluster_norm_eq {ω : Config (Fin d → ℤ)} (hω : ω ⊆ (zdGraph d).edgeSet)
    (r : ℕ) {x : Fin d → ℤ} (hx : x ∈ cluster ω 0) (hr : (r : ℝ) ≤ ‖x‖) :
    ∃ y ∈ cluster ω 0, ‖y‖ = r := by
  classical
  obtain ⟨w⟩ := (mem_cluster_iff ω 0 x).1 hx
  obtain ⟨v, hv, hvr⟩ := exists_mem_support_norm_eq hω r w (by simp) hr
  exact ⟨v, (mem_cluster_iff ω 0 v).2 ⟨w.takeUntil v hv⟩, hvr⟩

/-- **Power sums over an interval of `ℤ`.** For `0 ≤ s < 1`,
`∑_{|a| ≤ r} (1+|a|)^{-s} ≤ 2 (r+1)^{1-s}/(1-s)`. -/
theorem sum_Icc_one_add_abs_rpow_neg_le (r : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∑ a ∈ Finset.Icc (-(r : ℤ)) r, (1 + |(a : ℝ)|) ^ (-s) ≤
      2 * (((r + 1 : ℕ) : ℝ) ^ (1 - s) / (1 - s)) := by
  have hpt : ∀ a : ℤ, (1 + |(a : ℝ)|) ^ (-s) = (((a.natAbs : ℕ) : ℝ) + 1) ^ (-s) := by
    intro a
    rw [Nat.cast_natAbs, Int.cast_abs, add_comm]
  simp_rw [hpt]
  have hmaps : ∀ a ∈ Finset.Icc (-(r : ℤ)) r, a.natAbs ∈ Finset.range (r + 1) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ n ∈ Finset.range (r + 1), ∑ a ∈ Finset.Icc (-(r : ℤ)) r with a.natAbs = n,
        (((a.natAbs : ℕ) : ℝ) + 1) ^ (-s)
      ≤ ∑ n ∈ Finset.range (r + 1), 2 * (((n : ℝ) + 1) ^ (-s)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hcongr : ∑ a ∈ Finset.Icc (-(r : ℤ)) r with a.natAbs = n,
            (((a.natAbs : ℕ) : ℝ) + 1) ^ (-s) =
            ∑ a ∈ Finset.Icc (-(r : ℤ)) r with a.natAbs = n, ((n : ℝ) + 1) ^ (-s) :=
          Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]
        rw [hcongr, Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
        have hsub : (Finset.Icc (-(r : ℤ)) r).filter (fun a => a.natAbs = n) ⊆
            {(n : ℤ), -(n : ℤ)} := by
          intro a ha
          have := (Finset.mem_filter.1 ha).2
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        have h2 : ((Finset.Icc (-(r : ℤ)) r).filter (fun a => a.natAbs = n)).card ≤ 2 :=
          (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        exact_mod_cast h2
    _ = 2 * ∑ n ∈ Finset.range (r + 1), ((n : ℝ) + 1) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ 2 * (((r + 1 : ℕ) : ℝ) ^ (1 - s) / (1 - s)) := by
        gcongr
        exact sum_rpow_neg_le (r + 1) hs0 hs1

/-- **Power sums over a box of `ℤ²`.** For `0 ≤ η < 2`,
`∑_{‖x‖ ≤ r} (1+‖x‖)^{-η} ≤ (2 (r+1)^{1-η/2}/(1-η/2))²`. -/
theorem sum_piFinset_Icc_one_add_norm_rpow_neg_le (r : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη2 : η < 2) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r), (1 + ‖x‖) ^ (-η) ≤
      (2 * (((r + 1 : ℕ) : ℝ) ^ (1 - η / 2) / (1 - η / 2))) ^ 2 := by
  have hpt : ∀ x : Fin 2 → ℤ, (1 + ‖x‖) ^ (-η) ≤
      ∏ i, (1 + |((x i : ℤ) : ℝ)|) ^ (-(η / 2)) := by
    intro x
    rw [Fin.prod_univ_two]
    have hsplit : (1 + ‖x‖) ^ (-η) = (1 + ‖x‖) ^ (-(η / 2)) * (1 + ‖x‖) ^ (-(η / 2)) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    rw [hsplit]
    have hle : ∀ i, (1 + ‖x‖) ^ (-(η / 2)) ≤ (1 + |((x i : ℤ) : ℝ)|) ^ (-(η / 2)) := by
      intro i
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      have := norm_le_pi_norm x i
      rw [Int.norm_eq_abs] at this
      linarith
    exact mul_le_mul (hle 0) (hle 1) (by positivity) (by positivity)
  calc _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r),
        ∏ i, (1 + |((x i : ℤ) : ℝ)|) ^ (-(η / 2)) := Finset.sum_le_sum fun x _ => hpt x
    _ = (∑ a ∈ Finset.Icc (-(r : ℤ)) r, (1 + |(a : ℝ)|) ^ (-(η / 2))) ^ 2 :=
        (Finset.sum_prod_piFinset (Finset.Icc (-(r : ℤ)) r)
          (fun _ a => (1 + |(a : ℝ)|) ^ (-(η / 2)))).trans (by rw [Fin.prod_univ_two, sq])
    _ ≤ _ := by
        gcongr
        exact sum_Icc_one_add_abs_rpow_neg_le r (by linarith) (by linarith)

/-- **Window mean for any measure.** `E|K_v ∩ F| = ∑_{x ∈ F} P(v ↔ x)`. -/
theorem lintegral_encard_cluster_inter_eq_sum {V : Type*} [Countable V]
    (μ : Measure (Config V)) (v : V) (F : Finset V) :
    ∫⁻ ω, ((cluster ω v ∩ (F : Set V)).encard : ℝ≥0∞) ∂μ = ∑ x ∈ F, μ (conn v x) := by
  simp_rw [encard_cluster_inter_finset_eq_sum]
  rw [lintegral_finsetSum _ fun x _ => measurable_const.indicator (measurableSet_conn v x)]
  exact Finset.sum_congr rfl fun x _ => lintegral_indicator_one (measurableSet_conn v x)

section Planar

variable (μ : Measure (Config (Fin 2 → ℤ)))

/-- The escape and window-mean hypotheses of the tail comparison, from the arm and
two-point bounds on `ℤ²`. -/
theorem escape_and_window_bounds_of_arm_of_two_point
    (hnn : ∀ᵐ ω ∂μ, ω ⊆ (zdGraph 2).edgeSet) {η C₁ C₂ : ℝ} (hη0 : 0 < η) (hη2 : η < 2)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ∃ x : Fin 2 → ℤ, ‖x‖ = r ∧ ω ∈ conn 0 x} ≤
      ENNReal.ofReal (C₁ * (r : ℝ) ^ (-η / 2)))
    (h2 : ∀ x : Fin 2 → ℤ, μ (conn 0 x) ≤ ENNReal.ofReal (C₂ * (1 + ‖x‖) ^ (-η))) :
    (∀ r : ℕ, 1 ≤ r → μ {ω | ¬ cluster ω 0 ⊆
        (Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r) : Set (Fin 2 → ℤ))} ≤
      ENNReal.ofReal (max C₁ 0 * (r : ℝ) ^ (-(η / 2)))) ∧
    (∀ r : ℕ, 1 ≤ r → ∫⁻ ω, ((cluster ω 0 ∩
        (Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r) : Set (Fin 2 → ℤ))).encard :
          ℝ≥0∞) ∂μ ≤
      ENNReal.ofReal (max C₂ 0 * (4 * 2 ^ (2 - η) / (1 - η / 2) ^ 2) * (r : ℝ) ^ (2 - η))) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · refine (measure_mono_ae ?_).trans ((h1 r hr).trans (ENNReal.ofReal_le_ofReal ?_))
    · filter_upwards [hnn] with ω hω hs
      simp only [Set.not_subset, Finset.mem_coe,
        mem_piFinset_Icc_iff_norm_le, not_le] at hs
      obtain ⟨x, hx, hxr⟩ := hs
      obtain ⟨y, hy, hyr⟩ := exists_mem_cluster_norm_eq hω r hx hxr.le
      exact ⟨y, hyr, (mem_cluster_iff ω 0 y).1 hy⟩
    · rw [neg_div]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg r) _)
  · set B := Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r)
    rw [lintegral_encard_cluster_inter_eq_sum]
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hs : 0 < 1 - η / 2 := by linarith
    calc ∑ x ∈ B, μ (conn 0 x) ≤ ∑ x ∈ B, ENNReal.ofReal (max C₂ 0 * (1 + ‖x‖) ^ (-η)) :=
          Finset.sum_le_sum fun x _ => (h2 x).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      _ = ENNReal.ofReal (∑ x ∈ B, max C₂ 0 * (1 + ‖x‖) ^ (-η)) :=
          (ENNReal.ofReal_sum_of_nonneg fun x _ => by positivity).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Finset.mul_sum, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          refine (sum_piFinset_Icc_one_add_norm_rpow_neg_le r hη0.le hη2).trans ?_
          have hr2 : (((r + 1 : ℕ) : ℝ)) ≤ 2 * r := by push_cast; linarith
          have hpow : (((r + 1 : ℕ) : ℝ) ^ (1 - η / 2)) ^ 2 = ((r + 1 : ℕ) : ℝ) ^ (2 - η) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            ring_nf
          have hmono : ((r + 1 : ℕ) : ℝ) ^ (2 - η) ≤ (2 * r) ^ (2 - η) :=
            Real.rpow_le_rpow (by positivity) hr2 (by linarith)
          rw [Real.mul_rpow (by norm_num) (by positivity)] at hmono
          calc (2 * (((r + 1 : ℕ) : ℝ) ^ (1 - η / 2) / (1 - η / 2))) ^ 2
              = 4 * (((r + 1 : ℕ) : ℝ) ^ (1 - η / 2)) ^ 2 / (1 - η / 2) ^ 2 := by
                rw [mul_pow, div_pow]
                ring
            _ = 4 * ((r + 1 : ℕ) : ℝ) ^ (2 - η) / (1 - η / 2) ^ 2 := by rw [hpow]
            _ ≤ 4 * ((2 : ℝ) ^ (2 - η) * (r : ℝ) ^ (2 - η)) / (1 - η / 2) ^ 2 := by gcongr
            _ = 4 * 2 ^ (2 - η) / (1 - η / 2) ^ 2 * (r : ℝ) ^ (2 - η) := by ring

/-- **Planar volume tail.** Under the arm bound `P(0 ↔ ∂Λ_r) ≤ C₁ r^{-η/2}` and the two-point
bound `P(0 ↔ x) ≤ C₂ (1+‖x‖)^{-η}` with `0 < η < 2`, for a random nearest-neighbour bond
subgraph of `ℤ²`: `P(|K_0| ≥ n) ≤ C n^{-η/(4-η)}` for `n ≥ 1`, for an explicit finite `C`. -/
theorem measure_encard_cluster_ge_le_of_arm_of_two_point
    (hnn : ∀ᵐ ω ∂μ, ω ⊆ (zdGraph 2).edgeSet) {η C₁ C₂ : ℝ} (hη0 : 0 < η) (hη2 : η < 2)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ∃ x : Fin 2 → ℤ, ‖x‖ = r ∧ ω ∈ conn 0 x} ≤
      ENNReal.ofReal (C₁ * (r : ℝ) ^ (-η / 2)))
    (h2 : ∀ x : Fin 2 → ℤ, μ (conn 0 x) ≤ ENNReal.ofReal (C₂ * (1 + ‖x‖) ^ (-η))) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → μ {ω | (n : ℕ∞) ≤ (cluster ω 0).encard} ≤
      ENNReal.ofReal (C * (n : ℝ) ^ (-η / (4 - η))) := by
  obtain ⟨he, hw⟩ := escape_and_window_bounds_of_arm_of_two_point μ hnn hη0 hη2 h1 h2
  refine ⟨2 ^ (η / 2) * max C₁ 0 + max C₂ 0 * (4 * 2 ^ (2 - η) / (1 - η / 2) ^ 2),
    fun n hn => ?_⟩
  have h := measure_le_encard_le (μ := μ) (K := fun ω => cluster ω 0)
    (fun x => measurableSet_conn 0 x)
    (fun r => Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r)
    (a := η / 2) (b := 2 - η) (by linarith) (by linarith)
    (le_max_right C₁ 0) (mul_nonneg (le_max_right C₂ 0) (by positivity)) he hw hn
  have hexp : -(η / 2) / (η / 2 + (2 - η)) = -η / (4 - η) := by
    have : (4 - η) ≠ 0 := by linarith
    field_simp
    ring
  rwa [hexp] at h

/-- **Planar volume-tail exponent.** Under the hypotheses of
`measure_encard_cluster_ge_le_of_arm_of_two_point`, if `log P(|K_0| ≥ n)/log n → -1/δ`
with `δ > 0`, then `δ ≤ (4-η)/η`. -/
theorem le_of_log_tail_exponent_of_arm_of_two_point [IsProbabilityMeasure μ]
    (hnn : ∀ᵐ ω ∂μ, ω ⊆ (zdGraph 2).edgeSet) {η C₁ C₂ : ℝ} (hη0 : 0 < η) (hη2 : η < 2)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ∃ x : Fin 2 → ℤ, ‖x‖ = r ∧ ω ∈ conn 0 x} ≤
      ENNReal.ofReal (C₁ * (r : ℝ) ^ (-η / 2)))
    (h2 : ∀ x : Fin 2 → ℤ, μ (conn 0 x) ≤ ENNReal.ofReal (C₂ * (1 + ‖x‖) ^ (-η)))
    {δ : ℝ} (hδ : 0 < δ)
    (hlim : Tendsto (fun n : ℕ => Real.log (μ {ω | (n : ℕ∞) ≤ (cluster ω 0).encard}).toReal /
      Real.log n) atTop (𝓝 (-1 / δ))) :
    δ ≤ (4 - η) / η := by
  obtain ⟨he, hw⟩ := escape_and_window_bounds_of_arm_of_two_point μ hnn hη0 hη2 h1 h2
  have h := le_of_log_tail_exponent (μ := μ) (K := fun ω => cluster ω 0)
    (fun x => measurableSet_conn 0 x)
    (fun r => Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-(r : ℤ)) r)
    (a := η / 2) (b := 2 - η) (by linarith) (by linarith)
    (le_max_right C₁ 0) (mul_nonneg (le_max_right C₂ 0) (by positivity)) he hw hδ hlim
  have hexp : (η / 2 + (2 - η)) / (η / 2) = (4 - η) / η := by
    have : η ≠ 0 := hη0.ne'
    field_simp
    ring
  rwa [hexp] at h

end Planar

end PercLib.Percolation.Bond
