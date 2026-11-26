/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
Mathematical reference: the ordered cluster-discovery argument for the fourth central moment of
cluster power sums in finite independent bond percolation (Hutchcroft, hierarchical volumes,
section 6.3, with the corrected coefficient three).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.Integration
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Percolation.Bond.ClusterPartition

/-!
# Fourth central moment of cluster power sums

For independent bond percolation on a finite vertex set and a real exponent `p ≥ 1`, let
`S_p = ∑_C |C|^p` be the sum over the open clusters. Then
`E (S_p - E S_p)^4 ≤ E S_{4p} + 3 (E S_{2p})^2`.

The proof orders the vertices, writes `S_p` as the sum of the increments `Z_i` of the mass of
the clusters meeting the first `i` vertices, and shows that `Z_i` and the earlier mass
`U_i = ∑_{j<i} Z_j` satisfy a fibrewise stochastic domination: conditionally on the cluster of
the `i`-th vertex being a set `B` avoiding the earlier vertices, `U_i` is computed with every
pair meeting `B` closed, is independent of that event, and is dominated by its unconditional
value. A convex comparison then bounds the fourth central moment by that of an independent sum.

## Main results

* `PercLib.Probability.integral_comp_add_le_integral_integral_of_fiber`: the two-variable
  comparison with an independent copy, under fibrewise domination.
* `PercLib.Probability.integral_sum_sub_pow_four_le`: the fourth central moment of a sum of
  nonnegative variables, each compared with an independent copy of the earlier partial sum.
* `PercLib.Percolation.Bond.cluster_inter_avoid_eq`: clusters off a cluster `B` are unchanged
  by closing every pair meeting `B`.
* `PercLib.Percolation.Bond.integral_indicator_cluster_eq_le`: the conditional domination of
  the earlier cluster mass.
* `PercLib.Percolation.Bond.integral_sub_pow_four_le`: the fourth central moment bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Comparison with an independent copy under fibrewise domination.** Let `Z ≥ 0` be
constant on the fibres of `κ`, and suppose that on every fibre where `Z ≠ 0` the law of `U` is
dominated, for monotone test functions, by its unconditional law. Then for every `h` whose
increments `u ↦ h (z + u) - h u` are monotone for `z ≥ 0` (for instance a convex `h`),
`E h(Z + U)` is at most the same expectation with `U` replaced by an independent copy. -/
theorem integral_comp_add_le_integral_integral_of_fiber {β : Type*} (κ : Ω → β) (Z U : Ω → ℝ)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZκ : ∀ ω ω', κ ω = κ ω' → Z ω = Z ω')
    (hdom : ∀ ω, Z ω ≠ 0 → ∀ m : ℝ → ℝ, Monotone m →
      ∫ ω', {ω' | κ ω' = κ ω}.indicator (fun ω' => m (U ω')) ω' ∂μ ≤
        μ.real {ω' | κ ω' = κ ω} * ∫ ω', m (U ω') ∂μ)
    {h : ℝ → ℝ} (hh : ∀ z, 0 ≤ z → Monotone fun u => h (z + u) - h u) :
    ∫ ω, h (Z ω + U ω) ∂μ ≤ ∫ ω, ∫ ω', h (Z ω + U ω') ∂μ ∂μ := by
  classical
  have := Fintype.ofFinite Ω
  have hI : ∀ f : Ω → ℝ, Integrable f μ := fun f => Integrable.of_finite
  have hM : ∀ s : Set Ω, MeasurableSet s := fun s => (Set.toFinite s).measurableSet
  set D : Ω → ℝ := fun ω => h (Z ω + U ω) - h (U ω) with hD
  set E : Ω → ℝ := fun ω => ∫ ω', (h (Z ω + U ω') - h (U ω')) ∂μ with hE
  have hL : ∫ ω, h (Z ω + U ω) ∂μ = ∫ ω, h (U ω) ∂μ + ∫ ω, D ω ∂μ := by
    rw [← integral_add (hI _) (hI _)]
    congr 1
    ext ω
    simp [D]
  have hR : ∫ ω, ∫ ω', h (Z ω + U ω') ∂μ ∂μ = ∫ ω, h (U ω) ∂μ + ∫ ω, E ω ∂μ := by
    have : ∀ ω, ∫ ω', h (Z ω + U ω') ∂μ = ∫ ω', h (U ω') ∂μ + E ω := by
      intro ω
      simp only [E]
      rw [integral_sub (hI _) (hI _)]
      ring
    simp_rw [this]
    rw [integral_add (hI _) (hI _), integral_const]
    simp
  rw [hL, hR]
  rw [add_le_add_iff_left]
  have hfib : ∀ F : Ω → ℝ, ∫ ω, F ω ∂μ =
      ∑ b ∈ Finset.univ.image κ, ∫ ω, {ω | κ ω = b}.indicator F ω ∂μ := by
    intro F
    rw [← integral_finsetSum _ (fun _ _ => hI _)]
    congr 1
    ext ω
    simp [Set.indicator_apply]
  rw [hfib D, hfib E]
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨ω0, -, rfl⟩ := Finset.mem_image.1 hb
  by_cases hz : Z ω0 = 0
  · have e1 : {ω | κ ω = κ ω0}.indicator D = 0 := by
      ext ω
      by_cases hω : κ ω = κ ω0
      · simp [hω, D, hZκ ω ω0 hω, hz]
      · simp [hω]
    have e2 : {ω | κ ω = κ ω0}.indicator E = 0 := by
      ext ω
      by_cases hω : κ ω = κ ω0
      · simp [hω, E, hZκ ω ω0 hω, hz]
      · simp [hω]
    simp [e1, e2]
  · set m : ℝ → ℝ := fun u => h (Z ω0 + u) - h u with hm_def
    have hm : Monotone m := hh _ (hZ0 ω0)
    have e1 : {ω | κ ω = κ ω0}.indicator D = {ω | κ ω = κ ω0}.indicator fun ω => m (U ω) := by
      ext ω
      by_cases hω : κ ω = κ ω0
      · simp [hω, D, m, hZκ ω ω0 hω]
      · simp [hω]
    have e2 : {ω | κ ω = κ ω0}.indicator E =
        {ω | κ ω = κ ω0}.indicator fun _ => ∫ ω', m (U ω') ∂μ := by
      ext ω
      by_cases hω : κ ω = κ ω0
      · simp [hω, E, m, hZκ ω ω0 hω]
      · simp [hω]
    rw [e1, e2, integral_indicator_const _ (hM _), smul_eq_mul]
    exact hdom ω0 hz m hm

/-- Increments of a translated fourth power are monotone. -/
theorem monotone_add_pow_four_sub (α z : ℝ) (hz : 0 ≤ z) :
    Monotone fun u => (α + (z + u)) ^ 4 - (α + u) ^ 4 := by
  intro u v huv
  simp only
  set s := α + u
  set s' := α + v
  have hss : 0 ≤ s' - s := by simp [s, s', huv]
  have hQ : 0 ≤ 4 * (s' ^ 2 + s' * s + s ^ 2) + 6 * z * (s' + s) + 4 * z ^ 2 := by
    nlinarith [sq_nonneg (s' + s + z), sq_nonneg z, sq_nonneg (s' - s)]
  have hid : ((α + (z + v)) ^ 4 - (α + v) ^ 4) - ((α + (z + u)) ^ 4 - (α + u) ^ 4) =
      z * (s' - s) * (4 * (s' ^ 2 + s' * s + s ^ 2) + 6 * z * (s' + s) + 4 * z ^ 2) := by
    simp only [s, s']
    ring
  nlinarith [mul_nonneg (mul_nonneg hz hss) hQ]

/-- **Fourth central moment under successive comparison.** If every nonnegative `Z i`
(`i < n`) satisfies the comparison of `integral_comp_add_le_integral_integral_of_fiber` with the
earlier partial sum, then the fourth central moment of the total is at most
`∑ E Z_i^4 + 3 (∑ E Z_i^2)^2`. -/
theorem integral_sum_sub_pow_four_le (Z : ℕ → Ω → ℝ) (n : ℕ)
    (hZ0 : ∀ i < n, ∀ ω, 0 ≤ Z i ω)
    (hcomp : ∀ i < n, ∀ h : ℝ → ℝ, (∀ z, 0 ≤ z → Monotone fun u => h (z + u) - h u) →
      ∫ ω, h (Z i ω + ∑ j ∈ Finset.range i, Z j ω) ∂μ ≤
        ∫ ω, ∫ ω', h (Z i ω + ∑ j ∈ Finset.range i, Z j ω') ∂μ ∂μ) :
    ∫ ω, (∑ i ∈ Finset.range n, Z i ω - ∫ ω', ∑ i ∈ Finset.range n, Z i ω' ∂μ) ^ 4 ∂μ ≤
      ∑ i ∈ Finset.range n, ∫ ω, Z i ω ^ 4 ∂μ +
        3 * (∑ i ∈ Finset.range n, ∫ ω, Z i ω ^ 2 ∂μ) ^ 2 := by
  have hI : ∀ f : Ω → ℝ, Integrable f μ := fun f => Integrable.of_finite
  set c : ℕ → ℝ := fun i => ∫ ω, Z i ω ∂μ with hc
  have key : ∀ k ≤ n, ∀ x : ℝ,
      ∫ ω, (x + ∑ i ∈ Finset.range k, (Z i ω - c i)) ^ 4 ∂μ ≤
        x ^ 4 + 6 * x ^ 2 * (∑ i ∈ Finset.range k, ∫ ω, Z i ω ^ 2 ∂μ) +
          4 * x * (∑ i ∈ Finset.range k, ∫ ω, (Z i ω - c i) ^ 3 ∂μ) +
          (∑ i ∈ Finset.range k, ∫ ω, Z i ω ^ 4 ∂μ +
            3 * (∑ i ∈ Finset.range k, ∫ ω, Z i ω ^ 2 ∂μ) ^ 2) := by
    intro k
    induction k with
    | zero => intro _ x; simp
    | succ k ih =>
      intro hk x
      have hkn : k < n := by omega
      have ih' := ih hkn.le
      set a := ∑ i ∈ Finset.range k, ∫ ω, Z i ω ^ 2 ∂μ with ha_def
      set κ3 := ∑ i ∈ Finset.range k, ∫ ω, (Z i ω - c i) ^ 3 ∂μ with hκ3
      set b4 := ∑ i ∈ Finset.range k, ∫ ω, Z i ω ^ 4 ∂μ with hb4
      set d := ∑ i ∈ Finset.range k, c i with hd
      have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
      have hck : 0 ≤ c k := integral_nonneg fun ω => hZ0 k hkn ω
      have hsum : ∀ ω, ∑ i ∈ Finset.range k, (Z i ω - c i) =
          ∑ j ∈ Finset.range k, Z j ω - d := by
        intro ω
        rw [Finset.sum_sub_distrib]
      have hstep1 : ∫ ω, (x + ∑ i ∈ Finset.range (k + 1), (Z i ω - c i)) ^ 4 ∂μ ≤
          ∫ ω, ∫ ω', ((x + (Z k ω - c k)) + ∑ i ∈ Finset.range k, (Z i ω' - c i)) ^ 4 ∂μ ∂μ := by
        have := hcomp k hkn (fun t => (x - c k - d + t) ^ 4)
          (fun z hz => monotone_add_pow_four_sub _ z hz)
        calc ∫ ω, (x + ∑ i ∈ Finset.range (k + 1), (Z i ω - c i)) ^ 4 ∂μ
            = ∫ ω, (x - c k - d + (Z k ω + ∑ j ∈ Finset.range k, Z j ω)) ^ 4 ∂μ := by
              congr 1
              ext ω
              rw [Finset.sum_range_succ, hsum]
              ring
          _ ≤ _ := this
          _ = _ := by
              congr 1
              ext ω
              congr 1
              ext ω'
              rw [hsum]
              ring
      have hstep2 : ∫ ω, ∫ ω', ((x + (Z k ω - c k)) +
            ∑ i ∈ Finset.range k, (Z i ω' - c i)) ^ 4 ∂μ ∂μ ≤
          ∫ ω, ((x + (Z k ω - c k)) ^ 4 + 6 * (x + (Z k ω - c k)) ^ 2 * a +
            4 * (x + (Z k ω - c k)) * κ3 + (b4 + 3 * a ^ 2)) ∂μ :=
        integral_mono (hI _) (hI _) fun ω => ih' _
      set L := 4 * x ^ 3 - 12 * x ^ 2 * c k - c k ^ 3 + 12 * a * x - 12 * a * c k + 4 * κ3
      have hstep3 : ∫ ω, ((x + (Z k ω - c k)) ^ 4 + 6 * (x + (Z k ω - c k)) ^ 2 * a +
            4 * (x + (Z k ω - c k)) * κ3 + (b4 + 3 * a ^ 2)) ∂μ ≤
          ∫ ω, ((x ^ 4 + 6 * a * x ^ 2 + 4 * κ3 * x + (b4 + 3 * a ^ 2)) +
            L * (Z k ω - c k) + 6 * x ^ 2 * Z k ω ^ 2 + 4 * x * (Z k ω - c k) ^ 3 +
            Z k ω ^ 4 + 6 * a * Z k ω ^ 2) ∂μ := by
        refine integral_mono (hI _) (hI _) fun ω => ?_
        have hz := hZ0 k hkn ω
        set z := Z k ω
        have h2 : (z - c k) ^ 2 ≤ z ^ 2 - 2 * c k * (z - c k) := by nlinarith [sq_nonneg (c k)]
        have hq : 0 ≤ 4 * z ^ 2 - 6 * c k * z + 3 * c k ^ 2 := by
          nlinarith [sq_nonneg (2 * z - 3 / 2 * c k), sq_nonneg (c k)]
        have h4 : (z - c k) ^ 4 ≤ z ^ 4 - c k ^ 3 * (z - c k) := by
          nlinarith [mul_nonneg (mul_nonneg hck hz) hq]
        simp only [L]
        nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 h2), sub_nonneg.2 h4,
          mul_nonneg ha (sub_nonneg.2 h2)]
      have hY0 : ∫ ω, (Z k ω - c k) ∂μ = 0 := by
        rw [integral_sub (hI _) (hI _)]
        simp [c]
      have hstep4 : ∫ ω, ((x ^ 4 + 6 * a * x ^ 2 + 4 * κ3 * x + (b4 + 3 * a ^ 2)) +
            L * (Z k ω - c k) + 6 * x ^ 2 * Z k ω ^ 2 + 4 * x * (Z k ω - c k) ^ 3 +
            Z k ω ^ 4 + 6 * a * Z k ω ^ 2) ∂μ =
          (x ^ 4 + 6 * a * x ^ 2 + 4 * κ3 * x + (b4 + 3 * a ^ 2)) +
            L * ∫ ω, (Z k ω - c k) ∂μ + 6 * x ^ 2 * ∫ ω, Z k ω ^ 2 ∂μ +
            4 * x * ∫ ω, (Z k ω - c k) ^ 3 ∂μ + ∫ ω, Z k ω ^ 4 ∂μ +
            6 * a * ∫ ω, Z k ω ^ 2 ∂μ := by
        rw [integral_add (hI _) (hI _), integral_add (hI _) (hI _), integral_add (hI _) (hI _),
          integral_add (hI _) (hI _), integral_add (hI _) (hI _), integral_const,
          integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
        simp
      rw [hY0] at hstep4
      have he2 : 0 ≤ ∫ ω, Z k ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
      rw [Finset.sum_range_succ (fun i => ∫ ω, Z i ω ^ 2 ∂μ) k,
        Finset.sum_range_succ (fun i => ∫ ω, (Z i ω - c i) ^ 3 ∂μ) k,
        Finset.sum_range_succ (fun i => ∫ ω, Z i ω ^ 4 ∂μ) k, ← ha_def, ← hκ3, ← hb4]
      calc _ ≤ _ := hstep1
        _ ≤ _ := hstep2
        _ ≤ _ := hstep3
        _ = _ := hstep4
        _ ≤ _ := by nlinarith [sq_nonneg (∫ ω, Z k ω ^ 2 ∂μ)]
  have hfin := key n le_rfl 0
  have hc' : ∀ ω, ∑ i ∈ Finset.range n, Z i ω - ∫ ω', ∑ i ∈ Finset.range n, Z i ω' ∂μ =
      0 + ∑ i ∈ Finset.range n, (Z i ω - c i) := by
    intro ω
    rw [integral_finsetSum _ (fun _ _ => hI _), Finset.sum_sub_distrib, zero_add]
  simp_rw [hc']
  simpa using hfin

end PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

open scoped Classical in
/-- The mass `∑_{x ↔ s} |K(x)|^{r-1}` of the clusters meeting `s` is monotone in the
configuration when `r ≥ 1`. -/
theorem sum_rpow_cluster_meeting_mono [Fintype V] (s : Finset V) {r : ℝ} (hr : 1 ≤ r)
    {ω ω' : Config V} (h : ω ⊆ ω') :
    (∑ x, if ∃ w ∈ s, w ∈ cluster ω x then ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0) ≤
      ∑ x, if ∃ w ∈ s, w ∈ cluster ω' x then ((cluster ω' x).ncard : ℝ) ^ (r - 1) else 0 := by
  classical
  refine Finset.sum_le_sum fun x _ => ?_
  have hsub : cluster ω x ⊆ cluster ω' x := fun y hy => conn_mono h hy
  have hn : ((cluster ω x).ncard : ℝ) ≤ (cluster ω' x).ncard := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  split_ifs with h1 h2 h2
  · exact Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by linarith)
  · obtain ⟨w, hw, hwc⟩ := h1
    exact absurd ⟨w, hw, hsub hwc⟩ h2
  · positivity
  · exact le_rfl

/-- Closing every pair that meets the cluster of `a` does not change the cluster of a vertex
outside it. -/
theorem cluster_inter_avoid_eq {ω : Config V} {a x : V} (hx : x ∉ cluster ω a) :
    cluster (ω ∩ {e | ∀ v ∈ e, v ∉ cluster ω a}) x = cluster ω x := by
  refine Set.Subset.antisymm (fun y hy => conn_mono Set.inter_subset_left hy) ?_
  have H : ∀ u y (q : (openGraph ω).Walk u y), u ∉ cluster ω a →
      (openGraph (ω ∩ {e | ∀ v ∈ e, v ∉ cluster ω a})).Reachable u y := by
    intro u y q
    induction q with
    | nil => exact fun _ => SimpleGraph.Reachable.refl _
    | @cons u v w hadj q ih =>
      intro hu
      have hv : v ∉ cluster ω a := fun hv =>
        hu ((show (openGraph ω).Reachable a v from hv).trans hadj.symm.reachable)
      have hadj' : (openGraph (ω ∩ {e | ∀ v ∈ e, v ∉ cluster ω a})).Adj u v := by
        rw [openGraph_adj_iff] at hadj ⊢
        refine ⟨⟨hadj.1, fun z hz => ?_⟩, hadj.2⟩
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hu
        · exact hv
      exact hadj'.reachable.trans (ih hv)
  intro y hy
  obtain ⟨p⟩ := (hy : (openGraph ω).Reachable x y)
  exact H x y p hx


open scoped Classical in
/-- If the cluster of `a` avoids `s`, the mass of the clusters meeting `s` is unchanged by
closing every pair that meets the cluster of `a`. -/
theorem sum_rpow_cluster_meeting_inter_avoid [Fintype V] (s : Finset V) (r : ℝ)
    {ω : Config V} {a : V} (hs : ∀ w ∈ s, w ∉ cluster ω a) :
    (∑ x, if ∃ w ∈ s, w ∈ cluster (ω ∩ {e | ∀ v ∈ e, v ∉ cluster ω a}) x then
        ((cluster (ω ∩ {e | ∀ v ∈ e, v ∉ cluster ω a}) x).ncard : ℝ) ^ (r - 1) else 0) =
      ∑ x, if ∃ w ∈ s, w ∈ cluster ω x then ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0 := by
  classical
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ cluster ω a
  · have hxa : cluster ω x = cluster ω a :=
      (cluster_eq_iff_conn ω x a).2 (show (openGraph ω).Reachable x a from
        (show (openGraph ω).Reachable a x from hx).symm)
    have h1 : ¬ ∃ w ∈ s, w ∈ cluster ω x := by
      rintro ⟨w, hw, hwc⟩
      exact hs w hw (hxa ▸ hwc)
    have h2 : ¬ ∃ w ∈ s, w ∈ cluster (ω ∩ {e | ∀ v ∈ e, v ∉ cluster ω a}) x := by
      rintro ⟨w, hw, hwc⟩
      exact h1 ⟨w, hw, conn_mono Set.inter_subset_left hwc⟩
    rw [ite_eq_right h1, ite_eq_right h2]
  · rw [cluster_inter_avoid_eq hx]

open scoped Classical in
/-- **Increment of the cluster mass.** Adding `a` to `s` increases the mass of the clusters
meeting `s` by `|K(a)|^r` if the cluster of `a` avoids `s`, and by zero otherwise. -/
theorem sum_rpow_cluster_meeting_insert_sub [Fintype V] (s : Finset V) (a : V) (r : ℝ)
    (ω : Config V) :
    (∑ x, if ∃ w ∈ insert a s, w ∈ cluster ω x then ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0) -
      (∑ x, if ∃ w ∈ s, w ∈ cluster ω x then ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0) =
    if ∀ w ∈ s, w ∉ cluster ω a then ((cluster ω a).ncard : ℝ) ^ r else 0 := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ x, ((if ∃ w ∈ insert a s, w ∈ cluster ω x then
        ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0) -
      (if ∃ w ∈ s, w ∈ cluster ω x then ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0)) =
      if x ∈ cluster ω a then
        (if ∀ w ∈ s, w ∉ cluster ω a then ((cluster ω a).ncard : ℝ) ^ (r - 1) else 0) else 0 := by
    intro x
    by_cases hx : x ∈ cluster ω a
    · have hxa : cluster ω x = cluster ω a :=
        (cluster_eq_iff_conn ω x a).2 (show (openGraph ω).Reachable x a from
          (show (openGraph ω).Reachable a x from hx).symm)
      rw [hxa, ite_eq_left hx]
      by_cases hs : ∀ w ∈ s, w ∉ cluster ω a
      · have h1 : ∃ w ∈ insert a s, w ∈ cluster ω a :=
          ⟨a, Finset.mem_insert_self a s, mem_cluster_self ω a⟩
        have h2 : ¬ ∃ w ∈ s, w ∈ cluster ω a := fun ⟨w, hw, hwc⟩ => hs w hw hwc
        rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left hs, sub_zero]
      · obtain ⟨w, hw, hwc⟩ : ∃ w ∈ s, w ∈ cluster ω a := by
          by_contra hcon
          exact hs fun w hw hwc => hcon ⟨w, hw, hwc⟩
        have hs' : ¬ ∀ w ∈ s, w ∉ cluster ω a := fun h => h w hw hwc
        rw [ite_eq_left ⟨w, Finset.mem_insert_of_mem hw, hwc⟩, ite_eq_left ⟨w, hw, hwc⟩,
          ite_eq_right hs', sub_self]
    · have ha : a ∉ cluster ω x := fun h => hx ((mem_cluster_comm ω x a).1 h)
      have hiff : (∃ w ∈ insert a s, w ∈ cluster ω x) ↔ ∃ w ∈ s, w ∈ cluster ω x := by
        constructor
        · rintro ⟨w, hw, hwc⟩
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact absurd hwc ha
          · exact ⟨w, hw, hwc⟩
        · rintro ⟨w, hw, hwc⟩
          exact ⟨w, Finset.mem_insert_of_mem hw, hwc⟩
      rw [ite_eq_right hx]
      by_cases h : ∃ w ∈ s, w ∈ cluster ω x
      · rw [ite_eq_left (hiff.2 h), ite_eq_left h, sub_self]
      · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, sub_self]
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter fun x => x ∈ cluster ω a).card : ℝ) =
      (cluster ω a).ncard := by
    rw [← Set.ncard_coe_finset]
    congr 2
    ext y
    simp
  rw [hcard]
  have hpos : (cluster ω a).ncard ≠ 0 :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨a, mem_cluster_self ω a⟩ |>.ne'
  split_ifs
  · rw [Real.rpow_sub_one (by exact_mod_cast hpos)]
    field_simp
  · simp

open scoped Classical in
/-- **Conditional domination of the earlier cluster mass.** If `B` avoids `t`, then for every
monotone `m`, conditionally on `K(a) = B` the mass of the clusters meeting `t` is dominated by
its unconditional law. -/
theorem integral_indicator_cluster_eq_le [Fintype V] (q : Sym2 V → unitInterval) (t : Finset V)
    {r : ℝ} (hr : 1 ≤ r) (a : V) (B : Set V) (hB : ∀ w ∈ t, w ∉ B) {m : ℝ → ℝ}
    (hm : Monotone m) :
    ∫ ω, {ω | cluster ω a = B}.indicator (fun ω => m (∑ x, if ∃ w ∈ t, w ∈ cluster ω x then
        ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0)) ω ∂law q ≤
      (law q).real {ω | cluster ω a = B} * ∫ ω, m (∑ x, if ∃ w ∈ t, w ∈ cluster ω x then
        ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0) ∂law q := by
  classical
  obtain ⟨Mf, hMf⟩ : ∃ Mf : Config V → ℝ, ∀ ω, Mf ω = ∑ x, if ∃ w ∈ t, w ∈ cluster ω x then
      ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0 := ⟨_, fun _ => rfl⟩
  simp_rw [← hMf]
  have hMS : ∀ A : Set (Config V), MeasurableSet A := fun A => (Set.toFinite A).measurableSet
  have hI : ∀ f : Config V → ℝ, Integrable f (law q) := fun f => Integrable.of_finite
  obtain ⟨C, rfl⟩ : ∃ C : Finset V, (C : Set V) = B := ⟨(Set.toFinite B).toFinset, by simp⟩
  by_cases ha : a ∈ C
  swap
  · have hE : {ω : Config V | cluster ω a = C} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact ha (by simpa [h] using mem_cluster_self ω a)
    simp [hE]
  set E := {ω : Config V | cluster ω a = C} with hE_def
  set Q : Set (Sym2 V) := {e | ∀ v ∈ e, v ∉ (C : Set V)} with hQ_def
  set S : Set (Sym2 V) := {e | ∃ v ∈ e, v ∈ C} with hS_def
  set g : Config V → ℝ := fun ω => m (Mf (ω ∩ Q)) with hg_def
  have step1 : E.indicator (fun ω => m (Mf ω)) = fun ω => E.indicator 1 ω * g ω := by
    ext ω
    by_cases hω : ω ∈ E
    · have hωa : cluster ω a = C := hω
      have hav := sum_rpow_cluster_meeting_inter_avoid t r (ω := ω) (a := a)
        (by rw [hωa]; exact hB)
      rw [hωa] at hav
      simp only [Set.indicator_of_mem hω, Pi.one_apply, one_mul, g, hMf]
      rw [hav]
    · simp [Set.indicator_of_notMem hω]
  have hindep : IndepFun (E.indicator (1 : Config V → ℝ)) g (law q) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro u v _ _
    refine PercLib.Probability.prodBernoulli_inter_of_determined_inter q S Q ?_
      (hMS _) (hMS _) ?_ ?_
    · exact Set.disjoint_left.2 fun e ⟨v, hv, hvC⟩ he => he v hv hvC
    · intro ω
      have hd := cluster_eq_finset_determined a C ha ω
      by_cases hω : ω ∈ E
      · have hω' : ω ∩ S ∈ E := hd.1 hω
        simp [Set.indicator_of_mem hω, Set.indicator_of_mem hω']
      · have hω' : ω ∩ S ∉ E := fun h => hω (hd.2 h)
        simp [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω']
    · intro ω
      simp [g, Set.inter_assoc]
  rw [step1]
  have hmul := hindep.integral_mul_eq_mul_integral
    (Measurable.of_discrete).aestronglyMeasurable (Measurable.of_discrete).aestronglyMeasurable
  simp only [Pi.mul_apply] at hmul
  rw [hmul, integral_indicator_one (hMS _)]
  refine mul_le_mul_of_nonneg_left (integral_mono (hI _) (hI _) fun ω => ?_) measureReal_nonneg
  simp only [g, hMf]
  exact hm (sum_rpow_cluster_meeting_mono t hr Set.inter_subset_left)

/-- **Fourth central moment of cluster power sums.** For independent bond percolation on a
finite vertex set with arbitrary edge probabilities and `p ≥ 1`, with
`S_p = ∑_C |C|^p` over the open clusters,
`E (S_p - E S_p)^4 ≤ E S_{4p} + 3 (E S_{2p})^2`. -/
theorem integral_sub_pow_four_le [Finite V] (q : Sym2 V → unitInterval) {p : ℝ} (hp : 1 ≤ p) :
    ∫ ω, (∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ p -
        ∫ ω', ∑' C : (openGraph ω').ConnectedComponent, (C.supp.ncard : ℝ) ^ p ∂law q) ^ 4
        ∂law q ≤
      ∫ ω, ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ (4 * p) ∂law q +
        3 * (∫ ω, ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ (2 * p)
          ∂law q) ^ 2 := by
  classical
  have := Fintype.ofFinite V
  have hI : ∀ f : Config V → ℝ, Integrable f (law q) := fun f => Integrable.of_finite
  obtain ⟨M, hM⟩ : ∃ M : ℝ → Finset V → Config V → ℝ, ∀ r t ω, M r t ω =
      ∑ x, if ∃ w ∈ t, w ∈ cluster ω x then ((cluster ω x).ncard : ℝ) ^ (r - 1) else 0 :=
    ⟨_, fun _ _ _ => rfl⟩
  set N := Fintype.card V with hN
  set e := Fintype.equivFin V with he
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Finset V, ∀ i, s i = Finset.univ.filter fun x => (e x : ℕ) < i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ → ℕ → Config V → ℝ, ∀ r i ω,
      Z r i ω = M r (s (i + 1)) ω - M r (s i) ω := ⟨_, fun _ _ _ => rfl⟩
  have hs0 : s 0 = ∅ := by simp [hs]
  have hsN : s N = Finset.univ := by
    ext x
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (e x).isLt
  have hsucc : ∀ i (hi : i < N), s (i + 1) = insert (e.symm ⟨i, hi⟩) (s i) := by
    intro i hi
    ext x
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Equiv.eq_symm_apply, Fin.ext_iff]
    change (e x : ℕ) < i + 1 ↔ (e x : ℕ) = i ∨ (e x : ℕ) < i
    omega
  have hM0 : ∀ r ω, M r ∅ ω = 0 := by simp [hM]
  have hMuniv : ∀ r, r ≠ 0 → ∀ ω,
      M r Finset.univ ω = ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ r := by
    intro r hr ω
    have h := tsum_cluster_real_function ω (fun n => (n : ℝ) ^ (r - 1))
    rw [tsum_fintype] at h
    rw [hM, Finset.sum_congr rfl fun x _ =>
      ite_eq_left ⟨x, Finset.mem_univ x, mem_cluster_self ω x⟩,
      h]
    congr 1
    ext C
    rcases eq_or_ne C.supp.ncard 0 with h0 | h0
    · simp [h0, Real.zero_rpow hr]
    · rw [Real.rpow_sub_one (by exact_mod_cast h0)]
      field_simp
  have hpref : ∀ r i ω, ∑ j ∈ Finset.range i, Z r j ω = M r (s i) ω := by
    intro r i ω
    simp only [hZ]
    rw [Finset.sum_range_sub (fun j => M r (s j) ω), hs0, hM0, sub_zero]
  have hsumZ : ∀ r, r ≠ 0 → ∀ ω, ∑ i ∈ Finset.range N, Z r i ω =
      ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ r := by
    intro r hr ω
    rw [hpref, hsN, hMuniv r hr]
  have hZform : ∀ r i (hi : i < N) ω, Z r i ω =
      if ∀ w ∈ s i, w ∉ cluster ω (e.symm ⟨i, hi⟩) then
        ((cluster ω (e.symm ⟨i, hi⟩)).ncard : ℝ) ^ r else 0 := by
    intro r i hi ω
    rw [hZ, hsucc i hi, hM, hM]
    exact sum_rpow_cluster_meeting_insert_sub _ _ _ _
  have hZpow : ∀ (k : ℕ), k ≠ 0 → ∀ i (hi : i < N) ω, Z p i ω ^ k = Z (k * p) i ω := by
    intro k hk i hi ω
    rw [hZform p i hi, hZform _ i hi]
    split_ifs
    · rw [mul_comm, Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    · simp [hk]
  have hp0 : p ≠ 0 := by positivity
  have main := PercLib.Probability.integral_sum_sub_pow_four_le (μ := law q) (Z p) N
    (fun i hi ω => by rw [hZform p i hi]; split_ifs <;> positivity)
    (fun i hi h hh => by
      simp_rw [hpref p i]
      refine PercLib.Probability.integral_comp_add_le_integral_integral_of_fiber
        (fun ω => cluster ω (e.symm ⟨i, hi⟩)) (Z p i) (M p (s i))
        (fun ω => by rw [hZform p i hi]; split_ifs <;> positivity)
        (fun ω ω' hωω' => by rw [hZform p i hi, hZform p i hi, hωω'])
        (fun ω hz m hm => ?_) hh
      have hav : ∀ w ∈ s i, w ∉ cluster ω (e.symm ⟨i, hi⟩) := by
        by_contra hcon
        exact hz (by rw [hZform p i hi, ite_eq_right hcon])
      simp only [hM]
      exact integral_indicator_cluster_eq_le q (s i) hp _ _ hav hm)
  have hS : ∀ ω, ∑ i ∈ Finset.range N, Z p i ω =
      ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ p := hsumZ p hp0
  have hpow : ∀ k : ℕ, k ≠ 0 → ∑ i ∈ Finset.range N, ∫ ω, Z p i ω ^ k ∂law q =
      ∫ ω, ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ (k * p) ∂law q := by
    intro k hk
    rw [← integral_finsetSum _ (fun _ _ => hI _)]
    congr 1
    ext ω
    rw [← hsumZ (k * p) (by positivity) ω]
    exact Finset.sum_congr rfl fun i hi => hZpow k hk i (Finset.mem_range.1 hi) ω
  have h4 := hpow 4 (by norm_num)
  have h2 := hpow 2 (by norm_num)
  push_cast at h4 h2
  simp_rw [hS] at main
  rw [h4, h2] at main
  exact main

end PercLib.Percolation.Bond
