/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.CriticalDiagrams
public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.Criticality
public import PercLib.Percolation.Bond.Lace.Bootstrap.DiagramNorms
public import PercLib.Percolation.Bond.Lace.Diagrams.Convergence

/-!
# The actual nearest-neighbour lace expansion at criticality

## Main results

The critical diagrams give separate forward and reverse contraction constants,
a smaller terminal factor, and an initial mass retaining its exact diagonal.
Their dimension-dependent bounds imply transfer at most `1/855` and terminal
mass at most `1/1712` in dimension at least `50000`. All actual coefficient
masses are summable and the infinite spatial lace expansion holds at criticality.
Finite deleted clusters follow from actual almost-sure cluster finiteness;
finite critical susceptibility is not a premise.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter DiscreteConvolution
open scoped ENNReal NNReal Topology DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

private theorem critical_profile_add (x y g : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    q s(x + g, y + g) = q s(x, y) := by
  dsimp only
  rw [intensityProfile_nearestNeighborIntensity]
  exact homogeneous_zdGraph_add _ x y g

private theorem initial_mass_eq_rooted {G : Type*} [AddCommGroup G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x : G) :
    (∑' p, diagramInitial q x p) = ∑' p, diagramInitial q 0 p := by
  classical
  have ht (a b g : G) : tau q (a + g) (b + g) = tau q a b := by
    rw [tau_eq_rooted_of_add_right q hq (a + g) (b + g),
      tau_eq_rooted_of_add_right q hq a b, add_sub_add_right_eq_sub]
  have he (s h : G) : diagramInitial q x (s + x, h + x) = diagramInitial q 0 (s, h) := by
    have hs : s + x = x ↔ s = 0 := by
      constructor
      · intro h
        exact add_right_cancel (show s + x = 0 + x by simpa only [zero_add] using h)
      · intro h
        simp only [h, zero_add]
    have hh : h + x = x ↔ h = 0 := by
      constructor
      · intro h'
        exact add_right_cancel (show h + x = 0 + x by simpa only [zero_add] using h')
      · intro h'
        simp only [h', zero_add]
    have hxs : tau q x (s + x) = tau q 0 s := by
      simpa only [zero_add] using ht 0 s x
    have hxh : tau q x (h + x) = tau q 0 h := by
      simpa only [zero_add] using ht 0 h x
    simp only [diagramInitial, hs, hh, hxs, hxh, ht]
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod', ← (Equiv.addRight x).tsum_eq]
  apply tsum_congr
  intro s
  rw [← (Equiv.addRight x).tsum_eq]
  exact tsum_congr fun h => he s h

/-- The actual critical forward transfer keeps its dimension-dependent constant. -/
theorem nn_critical_diagramTransfer_mass_le (hd : 50000 ≤ d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' r, diagramTransfer q p r) ≤
      ENNReal.ofReal (2 * (1 + 4441 / (105 * (d : ℝ))) * (9197 / (315 * (d : ℝ)))) := by
  refine (diagramTransfer_mass_le_two_mul_triangle_continuation _ critical_profile_add _ _
    (nn_critical_triangle_le hd) (nn_critical_step_tau_three_le hd) p).trans_eq ?_
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]

/-- The reverse interior-connector product has its own critical bound; no
reversibility of the deleted connector is assumed. -/
theorem nn_critical_diagramInterior_connector_mass_le (hd : 50000 ≤ d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤
      ENNReal.ofReal (2 * (1 + 4441 / (105 * (d : ℝ))) * (9197 / (315 * (d : ℝ)))) := by
  refine (diagramInterior_connector_mass_le_two_mul_triangle_continuation _
    critical_profile_add _ _ (nn_critical_triangle_le hd)
    (nn_critical_step_tau_three_le hd) p).trans_eq ?_
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]

/-- The critical terminal norm keeps the smaller continuation value at zero. -/
theorem nn_critical_diagramTerminal_mass_le (hd : 50000 ≤ d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' y, diagramTerminal q p y) ≤
      ENNReal.ofReal ((9197 / (315 * (d : ℝ))) * (1 + 4441 / (315 * (d : ℝ)))) := by
  refine (diagramTerminal_mass_le_continuation_bound _ critical_profile_add _
    (nn_critical_step_tau_three_le hd) p).trans ?_
  refine (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl
    (nn_critical_step_tau_three_zero_le hd)))).trans_eq ?_
  have hc : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- At every root, the critical initial mass retains the exact diagonal one. -/
theorem nn_critical_diagramInitial_mass_le (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' p, diagramInitial q x p) ≤ ENNReal.ofReal (1 + 8882 / (315 * (d : ℝ))) := by
  dsimp only
  rw [initial_mass_eq_rooted _ critical_profile_add x]
  refine (diagramInitial_mass_le_min_triangle_step _ critical_profile_add).trans ?_
  refine (min_le_right _ _).trans ?_
  refine (add_le_add le_rfl (nn_critical_step_tau_three_zero_le hd)).trans_eq ?_
  rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]

private theorem critical_constants_le (hd : 50000 ≤ d) :
    2 * (1 + 4441 / (105 * (d : ℝ))) * (9197 / (315 * (d : ℝ))) ≤ 1 / 855 ∧
      (9197 / (315 * (d : ℝ))) * (1 + 4441 / (315 * (d : ℝ))) ≤ 1 / 1712 := by
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hM : 9197 / (315 * (d : ℝ)) ≤ 9197 / (315 * 50000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hD : 4441 / (105 * (d : ℝ)) ≤ 4441 / (105 * 50000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hZ : 4441 / (315 * (d : ℝ)) ≤ 4441 / (315 * 50000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  constructor
  · calc
      _ ≤ 2 * (1 + 4441 / (105 * 50000 : ℝ)) * (9197 / (315 * 50000 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add le_rfl hD) (by norm_num))
          hM (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  · calc
      _ ≤ (9197 / (315 * 50000 : ℝ)) * (1 + 4441 / (315 * 50000 : ℝ)) :=
        mul_le_mul hM (add_le_add le_rfl hZ) (by positivity) (by norm_num)
      _ ≤ _ := by norm_num

/-- A convenient strict forward contraction at the actual critical profile. -/
theorem nn_critical_diagramTransfer_mass_le_one_div (hd : 50000 ≤ d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' r, diagramTransfer q p r) ≤ ENNReal.ofReal (1 / 855 : ℝ) :=
  (nn_critical_diagramTransfer_mass_le hd p).trans
    (ENNReal.ofReal_le_ofReal (critical_constants_le hd).1)

/-- The independently bounded reverse product has the same convenient contraction. -/
theorem nn_critical_diagramInterior_connector_mass_le_one_div (hd : 50000 ≤ d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤
      ENNReal.ofReal (1 / 855 : ℝ) :=
  (nn_critical_diagramInterior_connector_mass_le hd p).trans
    (ENNReal.ofReal_le_ofReal (critical_constants_le hd).1)

/-- The terminal factor is strictly smaller than a full critical transfer. -/
theorem nn_critical_diagramTerminal_mass_le_one_div (hd : 50000 ≤ d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' y, diagramTerminal q p y) ≤ ENNReal.ofReal (1 / 1712 : ℝ) :=
  (nn_critical_diagramTerminal_mass_le hd p).trans
    (ENNReal.ofReal_le_ofReal (critical_constants_le hd).2)

/-- The continuation needed for the remainder is bounded by the same actual
shifted continuation diagram, retaining a constant of order `1/d`. -/
theorem nn_critical_continuation_le (hd : 50000 ≤ d) (u z : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' v, offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v z) ≤
        ENNReal.ofReal (9197 / (315 * (d : ℝ))) := by
  let q := intensityProfile (nearestNeighborIntensity d)
    (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  refine le_trans ?_ (nn_critical_step_tau_three_le hd (z - u))
  rw [← shifted_continuation_triangle_eq_step_tau_three q critical_profile_add z u]
  calc
    _ = tau q z z * (∑' v, offDiagonal (fun a b : Fin d → ℤ =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v z) * tau q z z := by
      rw [tau_self, one_mul, mul_one]
    _ ≤ ∑' t, tau q z z * (∑' v, offDiagonal (fun a b : Fin d → ℤ =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v t) * tau q z t :=
      ENNReal.le_tsum (f := fun t => tau q z z *
        (∑' v, offDiagonal (fun a b : Fin d → ℤ =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v t) * tau q z t) z
    _ ≤ _ := ENNReal.le_tsum (f := fun s => ∑' t, tau q z s *
      (∑' v, offDiagonal (fun a b : Fin d → ℤ =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v t) * tau q s t) z

/-- Every deleted-bond cluster is actually finite almost surely at criticality. -/
theorem ae_deleted_cluster_finite_nearestNeighbor_critical (hd : 50000 ≤ d)
    (a u v : Fin d → ℤ) :
    ∀ᵐ ω ∂law (intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal),
      (cluster (ω \ {s(u, v)}) a).Finite := by
  filter_upwards [ae_finite_cluster_nearestNeighbor_critical hd a] with ω hω
  exact hω.subset (cluster_mono sdiff_subset a)

/-- Actual critical coefficients obey a geometric positive-order mass estimate. -/
theorem laceCoefficient_mass_nearestNeighbor_critical_le (hd : 50000 ≤ d)
    (x : Fin d → ℤ) (n : ℕ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' y, laceCoefficient q (n + 1) x y) ≤
      ENNReal.ofReal (1 + 8882 / (315 * (d : ℝ))) *
        ENNReal.ofReal (1 / 855 : ℝ) ^ n * ENNReal.ofReal (1 / 1712 : ℝ) := by
  refine (laceCoefficient_mass_le_diagram_geometric _ x _ _
    (nn_critical_diagramTransfer_mass_le_one_div hd)
    (nn_critical_diagramTerminal_mass_le_one_div hd) n).trans ?_
  exact mul_le_mul' (mul_le_mul' (nn_critical_diagramInitial_mass_le hd x) le_rfl) le_rfl

/-- All actual coefficient masses are finite at criticality, including order zero. -/
theorem tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top
    (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤ := by
  apply tsum_laceCoefficient_all_mass_ne_top_of_diagram _ x
    (ENNReal.ofReal (1 / 855 : ℝ)) (ENNReal.ofReal (1 / 1712 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top
    (nn_critical_diagramTransfer_mass_le_one_div hd)
    (nn_critical_diagramTerminal_mass_le_one_div hd)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (nn_critical_diagramInitial_mass_le hd x)

/-- The canonical signed lace kernel is absolutely summable at the actual critical point. -/
theorem summable_laceSum_nearestNeighbor_critical (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    Summable (laceSum q x) :=
  summable_laceSum _ x (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd x)

/-- The canonical finite signed kernels converge to their critical infinite sum. -/
theorem tendsto_partialLaceSum_nearestNeighbor_critical (hd : 50000 ≤ d)
    (x y : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    Tendsto (fun n => partialLaceSum q n x y) atTop (𝓝 (laceSum q x y)) :=
  tendsto_partialLaceSum _ x y
    (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd x)

/-- The actual signed remainder tends to zero at criticality. -/
theorem tendsto_signedLaceRemainder_nearestNeighbor_critical_zero (hd : 50000 ≤ d)
    (x y : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    Tendsto (fun n => signedLaceRemainder q n x y) atTop (𝓝 0) :=
  tendsto_signedLaceRemainder_zero _ x y _ ENNReal.ofReal_ne_top
    (nn_critical_continuation_le hd)
    (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd x)

open scoped Classical in
/-- The actual infinite spatial lace expansion at the nearest-neighbour critical point.
Every hypothesis needed by the abstract finite-layer limit has been proved for the model. -/
@[tag "XBMM"]
theorem infinite_lace_expansion_nearestNeighbor_critical (hd : 50000 ≤ d)
    (x y : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (tau q x y).toReal = (if x = y then 1 else 0) + laceSum q x y +
      (∑' v, (offDiagonal (fun a b : Fin d → ℤ =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
      (∑' u, ∑' v, laceSum q x u * (offDiagonal (fun a b : Fin d → ℤ =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal) := by
  dsimp only
  have h := infinite_lace_expansion _ x y
    (ae_deleted_cluster_finite_nearestNeighbor_critical hd)
    _ ENNReal.ofReal_ne_top (nn_critical_continuation_le hd)
    (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd x)
  by_cases hxy : x = y <;> simpa only [hxy, ↓reduceIte] using h

end PercLib.Percolation.Bond.Lace
