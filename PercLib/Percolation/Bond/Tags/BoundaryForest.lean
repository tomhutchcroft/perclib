/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for boundary, forest and walk-kernel assertions. All mathematical inputs are
proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.FirstExit
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.SelfAvoidingChi
public import PercLib.Percolation.Bond.Wiring.BoundaryLaw
public import PercLib.Percolation.Bond.Wiring.Collapse
public import PercLib.Probability.Transport.Pullback

/-!
# Boundaries, forests and walk kernels: correspondence

Wiki correspondence for boundary laws, the first-exit inequality, forest hosts, walk kernels,
bounded-degree path counts and intensity bounds.

## Main results

* `boundary_mark_exponential`
* `boundary_escape_and_percolation`
* `forest_path_and_susceptibility`
* `walk_kernel_row_bounds`
* `bounded_degree_susceptibility_and_finiteness`
* `intensity_susceptibility_and_thresholds`
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Summable exterior intensities determine the closed boundary mark, including
zero intensity. No condition on interior or diagonal probabilities is needed. -/
@[tag "ZANA"]
theorem boundary_mark_exponential [Countable V] (q : Sym2 V → unitInterval)
    (S : Set V) (x : S) (J : Sym2 V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ y : (Sᶜ : Set V), 0 ≤ J s((x : V), (y : V)))
    (hs : Summable (fun y : (Sᶜ : Set V) => J s((x : V), (y : V))))
    (hq : ∀ y : (Sᶜ : Set V), (q s((x : V), (y : V)) : ℝ) =
      1 - Real.exp (-β * J s((x : V), (y : V)))) :
    law q {ω | ∀ y : (Sᶜ : Set V), s((x : V), (y : V)) ∉ ω} =
      ENNReal.ofReal (Real.exp (-β * ∑' y : (Sᶜ : Set V), J s((x : V), (y : V)))) := by
  have he (y : (Sᶜ : Set V)) : max (J s((x : V), (y : V))) 0 =
      J s((x : V), (y : V)) := max_eq_left (hJ y)
  have hs' := hs.congr (fun y => (he y).symm)
  simpa only [he] using law_boundary_closed_exponential q S x (fun e => max (J e) 0)
    β hβ (fun e => le_max_right _ _) hs' (fun y => by simpa only [he] using hq y)

open Classical in
/-- The first-exit chain, its singleton form, and the zero-boundary case. -/
@[tag "ROY9"]
theorem boundary_escape_and_percolation [Countable V] (q : Sym2 V → unitInterval)
    (S : Finset V) {x : V} (hx : x ∈ S) :
    (law q {ω | (cluster ω x).Infinite} ≤ law q {ω | ¬ cluster ω x ⊆ S}) ∧
    (law q {ω | ¬ cluster ω x ⊆ S} ≤
      ∑ y ∈ S, ∑' z, if z ∈ S then 0 else
        law q {ω | ∃ hy : y ∈ S,
          ((openGraph ω).induce (S : Set V)).Reachable ⟨x,hx⟩ ⟨y,hy⟩} *
            (unitInterval.toNNReal (q s(y,z)) : ℝ≥0∞)) ∧
    (law q {ω | cluster ω x ≠ {x}} ≤
      rowSum (fun e => unitInterval.toENNReal (q e)) x) ∧
    ((∀ y ∈ S, ∀ z ∉ S, q s(y,z) = 0) →
      law q {ω | ¬ cluster ω x ⊆ S} = 0) := by
  have heq (T : Set V) : {ω : Config V | ¬ cluster ω x ⊆ T} =
      ⋃ w ∈ Tᶜ, conn x w := by
    ext ω
    simp only [mem_ofPred_eq, subset_def, not_forall, mem_iUnion,
      mem_compl_iff, cluster]
    tauto
  have hsingle : {ω : Config V | cluster ω x ≠ {x}} =
      {ω | ¬ cluster ω x ⊆ ({x} : Set V)} := by
    ext ω
    exact not_congr ⟨fun h => h.subset, fun h =>
      Set.Subset.antisymm h (singleton_subset_iff.mpr (mem_cluster_self ω x))⟩
  refine ⟨measure_mono (fun ω hi hs => hi (S.finite_toSet.subset hs)), ?_, ?_, ?_⟩
  · rw [heq]
    exact law_escape_le_phi q S hx
  · rw [hsingle, heq]
    exact law_escape_singleton_le_rowSum q x
  · intro hz
    rw [heq]
    exact law_escape_eq_zero_of_boundary_zero q S hx hz

/-- Both sides of the first-exit estimate are exact on every initial ray segment. -/
@[tag "6J9C"]
theorem ray_escape_and_boundary_sum (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n, n + 1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m, n) = 0)
    (n : ℕ) :
    law q (⋃ w ∈ (Finset.range (n+1) : Set ℕ)ᶜ, conn 0 w) =
      (unitInterval.toNNReal t : ℝ≥0∞) ^ (n+1) ∧
    (∑ y ∈ Finset.range (n+1), ∑' z, if z ∈ Finset.range (n+1) then 0 else
      law q {ω | ∃ hy : y ∈ Finset.range (n+1),
        ((openGraph ω).induce (Finset.range (n+1) : Set ℕ)).Reachable
          ⟨0,by simp⟩ ⟨y,hy⟩} *
        (unitInterval.toNNReal (q s(y,z)) : ℝ≥0∞)) =
      (unitInterval.toNNReal t : ℝ≥0∞) ^ (n+1) :=
  ⟨law_escape_nat_range q t hedge hz n, phi_nat_range q t hedge hz n⟩

/-- Positive-probability support contains the entire configuration almost surely;
the associated simple graph automatically discards diagonal pairs. -/
@[tag "XHFN"]
theorem positive_support_contains_configuration [Countable V] (q : Sym2 V → unitInterval) :
    (∀ᵐ ω ∂law q, ω ⊆ {e | 0 < q e}) ∧
    (∀ᵐ ω ∂law q, openGraph ω ≤ SimpleGraph.fromEdgeSet {e | 0 < q e}) :=
  ⟨ae_config_subset_positive q, ae_openGraph_le_support q⟩

open Classical in
/-- A forest host gives the unique-path product, zero between different components,
and the exact susceptibility sum, with the root contributing its empty path. -/
@[tag "8KVE"]
theorem forest_path_and_susceptibility [Countable V] (q : Sym2 V → unitInterval)
    (G : SimpleGraph V) (hG : G.IsAcyclic)
    (hhost : ∀ᵐ ω ∂law q, openGraph ω ≤ G) :
    (∀ x y (p : G.Path x y), tau q x y =
      ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ∧
    (∀ x y, ¬ G.Reachable x y → tau q x y = 0) ∧
    (∀ x, chi q x = ∑' y, ∑' p : G.Path x y,
      ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ∧
    (∀ x, tau q x x = 1) := by
  refine ⟨fun _ _ p => tau_eq_prod_of_ae_le_acyclic q hG hhost p,
    fun _ _ h => tau_eq_zero_of_ae_le q hhost h, ?_, tau_self q⟩
  intro x
  rw [chi_eq_tsum_tau]
  apply tsum_congr
  intro y
  let : Subsingleton (G.Path x y) := hG.subsingleton_path x y
  by_cases h : G.Reachable x y
  · obtain ⟨p, hp⟩ := h.exists_isPath
    let r : G.Path x y := ⟨p, hp⟩
    rw [tsum_eq_single r]
    · exact tau_eq_prod_of_ae_le_acyclic q hG hhost r
    · intro b hb
      exact (hb (Subsingleton.elim _ _)).elim
  · let : IsEmpty (G.Path x y) := ⟨fun p => h ⟨p.1⟩⟩
    rw [tsum_empty]
    exact tau_eq_zero_of_ae_le q hhost h

/-- Ray two-point probabilities and the complete endpoint susceptibility formula,
including the critical endpoint and the equivalence characterising finiteness. -/
@[tag "TGL4"]
theorem ray_two_point_and_susceptibility (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n, n + 1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m, n) = 0) :
    (∀ m n, tau q m n = (unitInterval.toNNReal t : ℝ≥0∞) ^ Nat.dist m n) ∧
    chi q 0 = ∑' n : ℕ, (unitInterval.toNNReal t : ℝ≥0∞) ^ n ∧
    chi q 0 = (1 - (unitInterval.toNNReal t : ℝ≥0∞))⁻¹ ∧
    (t = 1 → chi q 0 = ⊤) ∧ (chi q 0 < ⊤ ↔ t < 1) := by
  have he := chi_nat_zero_eq_geometric q t hedge hz
  refine ⟨tau_nat_eq_pow_dist q t hedge hz, ?_, he, ?_, ?_⟩
  · rw [ENNReal.tsum_geometric]
    exact he
  · intro ht
    simpa [ht] using he
  · rw [he, ENNReal.inv_lt_top, tsub_pos_iff_lt, ENNReal.coe_lt_one_iff]
    rfl

/-- Sequence-product representation, recurrence and all row bounds, including the
masked kernel with an unconstrained original diagonal and extended row constants. -/
@[tag "HDHT"]
theorem walk_kernel_row_bounds (a : V → V → ℝ≥0∞) :
    (∀ n v, walkSum a n v = ∑' p : Fin n → V, walkWeight a v p) ∧
    (∀ n v, walkSum a (n+1) v = ∑' w, a v w * walkSum a n w) ∧
    (∀ m : ℝ≥0∞, (∀ v, (∑' w, a v w) ≤ m) →
      (∀ n v, walkSum a n v ≤ m^n) ∧
      (m < 1 → (∀ v, (∑' n, walkSum a n v) ≤ (1-m)⁻¹) ∧ (1-m)⁻¹ < ⊤)) ∧
    (∀ m : ℝ≥0∞, (∀ v, (∑' w, offDiagonal a v w) ≤ m) →
      (∀ n v, walkSum (offDiagonal a) n v ≤ m^n) ∧
      (m < 1 → (∀ v, (∑' n, walkSum (offDiagonal a) n v) ≤ (1-m)⁻¹) ∧
        (1-m)⁻¹ < ⊤)) := by
  refine ⟨walkSum_eq_tsum_walkWeight a, walkSum_succ a, ?_, ?_⟩
  · intro m hrow
    exact ⟨walkSum_le_pow a m hrow, fun hm =>
      ⟨walkSum_total_le a m hrow hm, ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hm)⟩⟩
  · intro m hrow
    exact ⟨walkSum_masked_le_pow a m hrow, fun hm =>
      ⟨walkSum_masked_total_le a m hrow hm, ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hm)⟩⟩

open Classical in
/-- The finite count and probability bound for positive-length simple host paths.
The vertex type is arbitrary and no off-host probability assumption is made. -/
@[tag "8WML"]
theorem bounded_degree_path_count_and_probability (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p) (x : V) (n : ℕ) :
    Finite {r : Σ y, G.Path x y // r.2.1.length = n+1} ∧
    Nat.card {r : Σ y, G.Path x y // r.2.1.length = n+1} ≤ Δ * (Δ-1)^n ∧
    law q {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
      (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} ≤
      (Δ * (Δ-1)^n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) ∧
    (Δ * (Δ-1)^n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) =
      Δ * (unitInterval.toNNReal p : ℝ≥0∞) *
        ((Δ-1 : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞))^n := by
  obtain ⟨hfin, hcard⟩ := finite_card_paths_length G hΔ x n
  refine ⟨hfin, hcard, law_exists_path_length_le G hΔ q p hle x n, ?_⟩
  push_cast
  rw [pow_succ, mul_pow]
  ac_rfl

private theorem degree_susceptibility_geometric [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p) (x : V) :
    chi q x ≤ 1 + (Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) /
      (1 - ((Δ-1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)) := by
  by_cases hzero : Δ = 0
  · subst Δ
    simpa using chi_le_one_add_tsum_selfAvoiding G hΔ q p hoff hle x
  · have hc : ((Δ-1 : ℕ) : ℝ≥0∞) = (Δ : ℝ≥0∞) - 1 := by
      simp only [ENNReal.natCast_sub, Nat.cast_one]
    refine (chi_le_one_add_tsum_selfAvoiding G hΔ q p hoff hle x).trans_eq ?_
    congr 1
    have he (n : ℕ) : (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞)-1)^n *
        (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) =
        ((Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)) *
          (((Δ : ℝ≥0∞)-1) * (unitInterval.toNNReal p : ℝ≥0∞))^n := by
      rw [pow_succ, mul_pow]
      ac_rfl
    simp_rw [he]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv, hc]

/-- The sharp degree criterion bounds susceptibility and gives simultaneous
finiteness. Its degree-zero and degree-one specialisations include all probabilities. -/
@[tag "YP44"]
theorem bounded_degree_susceptibility_and_finiteness [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (hp : ((Δ - 1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) < 1) :
    (∀ x, chi q x ≤ 1 + (Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) /
      (1 - ((Δ-1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞))) ∧
    (∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite) ∧
    (Δ = 0 → ∀ x, chi q x = 1) ∧
    (Δ = 1 → ∀ x, chi q x ≤ 1 + (unitInterval.toNNReal p : ℝ≥0∞)) := by
  have hb := degree_susceptibility_geometric G hΔ q p hoff hle
  have hfinite (x : V) : chi q x < ⊤ := by
    apply (hb x).trans_lt
    apply ENNReal.add_lt_top.mpr
    refine ⟨by simp, ENNReal.div_lt_top (by finiteness) (ne_of_gt (tsub_pos_of_lt hp))⟩
  have hae (x : V) : ∀ᵐ ω ∂law q, (cluster ω x).Finite := by
    have hm : Measurable (fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞)) :=
      (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster x)
    filter_upwards [ae_lt_top hm (hfinite x).ne] with ω hω
    exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp hω)
  refine ⟨hb, ae_all_iff.mpr hae, ?_, ?_⟩
  · intro hzero x
    apply le_antisymm _ (one_le_chi q x)
    simpa [hzero] using hb x
  · intro hone x
    simpa [hone] using hb x

/-- Intensity rows control both susceptibility and percolation thresholds. The
zero-parameter assertion is independent of a row bound; zero rows give infinite
thresholds at every root and susceptibility one at every finite parameter. -/
@[tag "BPR6"]
theorem intensity_susceptibility_and_thresholds [Countable V] (J : Sym2 V → ℝ≥0) :
    (∀ x, chi (intensityProfile J 0) x = 1) ∧
    (∀ M : ℝ≥0, (∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) →
      (∀ β : ℝ≥0, (β : ℝ≥0∞)*M < 1 →
        (∀ x, 1 ≤ chi (intensityProfile J β) x ∧
          chi (intensityProfile J β) x ≤ (1-(β : ℝ≥0∞)*M)⁻¹) ∧
        (1-(β : ℝ≥0∞)*M)⁻¹ < ⊤ ∧
        (∀ᵐ ω ∂law (intensityProfile J β), ∀ x, (cluster ω x).Finite)) ∧
      ((M : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J) ∧
      (∀ x, (M : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x) ∧
      (M = 0 → (∀ β x, chi (intensityProfile J β) x = 1) ∧
        globalCriticalIntensity J = ⊤ ∧ (∀ x, rootCriticalIntensity J x = ⊤))) := by
  refine ⟨chi_intensity_zero J, ?_⟩
  intro M hJ
  refine ⟨?_, inv_le_globalCriticalIntensity J M hJ,
    inv_le_rootCriticalIntensity J M hJ, ?_⟩
  · intro β hβ
    exact ⟨fun x => ⟨one_le_chi _ x, chi_intensity_le J M hJ β hβ x⟩,
      ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hβ),
      ae_all_clusters_finite_of_rowSum _ _ (intensity_rowSum_le J M hJ β) hβ⟩
  · intro hzero
    subst M
    have hz : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 0 := by
      simpa using hJ
    exact ⟨chi_intensity_eq_one_of_rowSum_zero J hz,
      globalCriticalIntensity_eq_top_of_rowSum_zero J hz,
      rootCriticalIntensity_eq_top_of_rowSum_zero J hz⟩

/-- Joint independence, boundary marginals and convergence along every finite
increasing exterior exhaustion, with both degenerate boundary cases explicit. -/
@[tag "AGF6"]
theorem boundary_independence_and_marginals [Countable V]
    (q : Sym2 V → unitInterval) (S : Set V) :
    iIndepFun (Sum.elim
      (fun (x : S) (ω : Config V) => ∃ y : (Sᶜ : Set V), s((x : V), (y : V)) ∈ ω)
      (fun (z : Sym2 S) (ω : Config V) => Sym2.map Subtype.val z ∈ ω)) (law q) ∧
    (∀ x : S, law q {ω | ∀ y : (Sᶜ : Set V), s((x : V), (y : V)) ∉ ω} =
      ∏' y : (Sᶜ : Set V),
        (unitInterval.toNNReal (unitInterval.symm (q s((x : V), (y : V)))) : ℝ≥0∞)) ∧
    (∀ (x : S) (F : ℕ → Finset (Sᶜ : Set V)), Monotone F →
      (∀ y, ∃ n, y ∈ F n) → Filter.Tendsto
        (fun n => ∏ y ∈ F n,
          (unitInterval.toNNReal (unitInterval.symm (q s((x : V), (y : V)))) : ℝ≥0∞))
        Filter.atTop (nhds (law q {ω | ∀ y : (Sᶜ : Set V), s((x : V), (y : V)) ∉ ω}))) ∧
    (S = univ → ∀ x : S,
      law q {ω | ∀ y : (Sᶜ : Set V), s((x : V), (y : V)) ∉ ω} = 1) ∧
    (∀ x : S, (∃ y : (Sᶜ : Set V), q s((x : V), (y : V)) = 1) →
      law q {ω | ∀ y : (Sᶜ : Set V), s((x : V), (y : V)) ∉ ω} = 0) := by
  refine ⟨law_iIndepFun_boundary_internal q S,
    fun x => law_boundary_closed q S x, ?_, ?_, ?_⟩
  · intro x F hF hcover
    rw [law_boundary_closed]
    have hm := ENNReal.multipliable_of_le_one (fun y : (Sᶜ : Set V) =>
      show (unitInterval.toNNReal (unitInterval.symm (q s((x : V), (y : V)))) : ℝ≥0∞) ≤ 1 by
        exact_mod_cast (unitInterval.symm (q s((x : V), (y : V)))).property.2)
    exact hm.hasProd.comp (hF.tendsto_atTop_finset hcover)
  · rintro rfl x
    simp
  · intro x ⟨y, hy⟩
    rw [law_boundary_closed]
    exact tprod_of_exists_eq_zero ⟨y, by simp [hy]⟩

-- The general-kernel statement permits an infinite original diagonal, even on
-- an uncountable vertex type. Its masked row and total are zero and one.
example : (∀ v : ℝ, walkSum (offDiagonal (fun v w : ℝ => if w = v then ⊤ else 0)) 0 v = 1) := by
  simp

example : ∀ v : ℝ, (∑' n, walkSum
    (offDiagonal (fun v w : ℝ => if w = v then ⊤ else 0)) n v) ≤ 1 := by
  simpa using ((walk_kernel_row_bounds
    (fun v w : ℝ => if w = v then ⊤ else 0)).2.2.2 0 (by
      intro v
      simp [offDiagonal])).2 (by simp) |>.1

-- Zero degree and probability one satisfy the sharp criterion simultaneously.
example : (∀ x : Unit, chi (fun _ => (1 : unitInterval)) x = 1) := by
  have h := bounded_degree_susceptibility_and_finiteness (⊥ : SimpleGraph Unit)
    (Δ := 0) (by simp) (fun _ => 1) 1
    (by intro e he; exact (he (Sym2.isDiag_of_subsingleton e)).elim)
    (by simp) (by simp)
  exact h.2.2.1 rfl

-- The boundary exponential includes beta = 0 with a nonempty exterior.
example : law (fun _ : Sym2 ℕ => 0)
    {ω | ∀ y : (({0} : Set ℕ)ᶜ : Set ℕ), s(0, (y : ℕ)) ∉ ω} = 1 := by
  simpa using boundary_mark_exponential (fun _ => 0) {0} ⟨0, by simp⟩
    (fun _ => 0) 0 (by simp) (by simp) (by simp) (by simp)

-- Every ray parameter is realised, including t = 0 and t = 1, while its
-- diagonal profile is arbitrary. These are actual witnesses to both ray tags.
example (t : unitInterval) (d : ℕ → unitInterval) :
    ∃ q : Sym2 ℕ → unitInterval,
      (∀ n, q s(n,n) = d n) ∧
      (∀ m n, tau q m n = (unitInterval.toNNReal t : ℝ≥0∞) ^ Nat.dist m n) ∧
      (chi q 0 < ⊤ ↔ t < 1) ∧
      (∀ n, law q (⋃ w ∈ (Finset.range (n+1) : Set ℕ)ᶜ, conn 0 w) =
        (unitInterval.toNNReal t : ℝ≥0∞) ^ (n+1)) := by
  let q : Sym2 ℕ → unitInterval := Sym2.lift ⟨fun m n =>
    if m = n then d m else if m + 1 = n ∨ n + 1 = m then t else 0, by
      intro m n
      dsimp
      by_cases h : m = n
      · subst n; rfl
      · simp [h, Ne.symm h, or_comm]⟩
  have he (n) : q s(n,n+1) = t := by simp [q]
  have hz (m n) (hne : m ≠ n) (h : ¬ (m + 1 = n ∨ n + 1 = m)) : q s(m,n) = 0 := by
    simp [q, hne, h]
  have hr := ray_two_point_and_susceptibility q t he hz
  exact ⟨q, (by intro n; simp [q]), hr.1, hr.2.2.2.2,
    fun n => (ray_escape_and_boundary_sum q t he hz n).1⟩

-- Positive intensity and a nonzero subcritical parameter satisfy the row hypothesis.
example : chi (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ≥0)) (1/2)) false ≤
    (1 - ((1/2 : ℝ≥0) : ℝ≥0∞))⁻¹ := by
  have h := (intensity_susceptibility_and_thresholds (fun _ : Sym2 Bool => (1 : ℝ≥0))).2 1
    (fun v => by cases v <;> simp [rowSum_def, tsum_fintype])
  have hb := (h.1 (1/2) (by norm_num) ).1 false
  simpa using hb.2

-- Zero off-diagonal intensity on an infinite type leaves nonzero diagonal rates free.
example : globalCriticalIntensity
    (fun e : Sym2 ℕ => if e.IsDiag then (1 : ℝ≥0) else 0) = ⊤ := by
  have h := (intensity_susceptibility_and_thresholds
    (fun e : Sym2 ℕ => if e.IsDiag then (1 : ℝ≥0) else 0)).2 0 (by
      intro v
      apply le_of_eq
      apply ENNReal.tsum_eq_zero.mpr
      intro w
      by_cases hw : w = v
      · simp [hw]
      · simp [hw, Sym2.mk_isDiag_iff, Ne.symm hw])
  exact (h.2.2.2 rfl).2.1

-- Degree one allows probability one on the edge and on both diagonal coordinates.
example : ∀ x : Bool, chi (fun _ : Sym2 Bool => (1 : unitInterval)) x ≤ 2 := by
  have h := bounded_degree_susceptibility_and_finiteness (⊤ : SimpleGraph Bool)
    (Δ := 1) (by intro v; simp) (fun _ => 1) 1
    (by intro e he hn; exact (hn (by simpa using he)).elim)
    (by intro e he; exact le_rfl) (by simp)
  simpa only [unitInterval.toNNReal_one, ENNReal.coe_one, one_add_one_eq_two] using h.2.2.2 rfl

open Classical in
/-- The defining sequence product, its full sum, empty sequences and diagonal
removal. All objects are the existing definitions; no paths or countability
restrictions are imposed on the sequence index. -/
@[tag "O357"]
theorem sequence_weights_sums_and_diagonal (a : V → V → ℝ≥0∞) :
    (∀ (n : ℕ) (v : V) (p : Fin n → V), walkWeight a v p =
      ∏ i : Fin n, a ((Fin.cons v p : Fin (n+1) → V) i.castSucc) (p i)) ∧
    (∀ n v, walkSum a n v = ∑' p : Fin n → V, walkWeight a v p) ∧
    (∀ v (p : Fin 0 → V), walkWeight a v p = 1) ∧
    (∀ v, walkSum a 0 v = 1) ∧
    (∀ v w, offDiagonal a v w = if w = v then 0 else a v w) :=
  ⟨fun _ _ _ => rfl, walkSum_eq_tsum_walkWeight a, walkWeight_zero a,
    walkSum_zero a, offDiagonal_apply a⟩

open Classical in
/-- A boundary mark is precisely the edge to the collapsed exterior. Internal
connections use the induced graph, equivalently the restricted pair configuration;
their probability is its canonical two-point function. -/
@[tag "XN06"]
theorem boundary_marks_and_internal_connections [Countable V]
    (q : Sym2 V → unitInterval) (S : Set V) (π : V → Option S)
    (hπ : ∀ v, π v = if h : v ∈ S then some ⟨v, h⟩ else none) :
    (∀ (ω : Config V) (x : S),
      (openGraph {z : Sym2 (Option S) | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}).Adj
        (some x) none ↔ ∃ y : (Sᶜ : Set V), s((x : V), (y : V)) ∈ ω) ∧
    (∀ (ω : Config V) (x y : S),
      ((openGraph ω).induce S).Reachable x y ↔
        Sym2.map (Subtype.val : S → V) ⁻¹' ω ∈ conn x y) ∧
    (∀ x y : S, tau (q ∘ Sym2.map (Subtype.val : S → V)) x y =
      law q {ω | ((openGraph ω).induce S).Reachable x y}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω x
    rw [openGraph_adj_iff]
    constructor
    · rintro ⟨⟨e, he, hm, hnd⟩, _⟩
      obtain ⟨y, hy, rfl⟩ := (ghost_fibre_boundary π hπ x e).mp ⟨hm, hnd⟩
      exact ⟨⟨y,hy⟩,he⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨s((x : V), (y : V)), hy,
        (ghost_fibre_boundary π hπ x _).mpr ⟨y, y.property, rfl⟩⟩, by simp⟩
  · intro ω x y
    rw [openGraph_induce]
    rfl
  · intro x y
    simp only [openGraph_induce]
    exact (prodBernoulli_preimage_preimage q
      (Sym2.map.injective Subtype.val_injective) (measurableSet_conn x y)).symm

-- Two disjoint edges can become connected through the ghost. The boundary
-- marks therefore encode boundary bonds, and do not claim an original connection.
open Classical in
example : ∃ (S : Set (Bool × Bool)) (ω : Config (Bool × Bool)) (a b : S)
    (π : (Bool × Bool) → Option S),
    (∀ v, π v = if h : v ∈ S then some ⟨v,h⟩ else none) ∧
    ω ∉ conn (a : Bool × Bool) b ∧
    {z : Sym2 (Option S) | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag} ∈
      conn (some a) (some b) ∧ (cluster ω a).Finite := by
  classical
  let S : Set (Bool × Bool) := {v | v.2 = false}
  let : DecidablePred (· ∈ S) := fun v => Classical.propDecidable (v ∈ S)
  let ω : Config (Bool × Bool) := {s((false,false), (false,true)),
    s((true,false), (true,true))}
  let a : S := ⟨(false,false), rfl⟩
  let b : S := ⟨(true,false), rfl⟩
  let π : (Bool × Bool) → Option S := fun v => if h : v ∈ S then some ⟨v,h⟩ else none
  have hπ (v) : π v = if h : v ∈ S then some ⟨v,h⟩ else none := rfl
  have ha := (boundary_marks_and_internal_connections (fun _ => 0) S π hπ).1 ω a
  have hb := (boundary_marks_and_internal_connections (fun _ => 0) S π hπ).1 ω b
  have ha' := ha.mpr ⟨⟨(false,true), by simp [S]⟩, by simp [ω, a]⟩
  have hb' := hb.mpr ⟨⟨(true,true), by simp [S]⟩, by simp [ω, b]⟩
  refine ⟨S, ω, a, b, π, hπ, ?_, ha'.reachable.trans hb'.symm.reachable,
    Set.toFinite _⟩
  have hadj : ∀ x y, (openGraph ω).Adj x y → x.1 = y.1 := by
    intro x y h
    obtain ⟨he, _⟩ := (openGraph_adj_iff ω x y).mp h
    simp only [ω, mem_insert_iff, mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> rfl
  have hconn : ∀ x y, (openGraph ω).Reachable x y → x.1 = y.1 := by
    intro x y h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | @tail y z _ hyz ih => exact ih.trans (hadj y z hyz)
  intro h
  have hh := hconn a b h
  change false = true at hh
  cases hh

end PercLib.Percolation.Bond
