/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original bounds for the actual second joining core. Mathematical reference:
Heydenreich and van der Hofstad (2017), Section 8.3, retaining both step masses.
No upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.WeightedPair
public import PercLib.Percolation.Bond.Lace.Diagrams.ZeroWeighted
public import PercLib.Analysis.LatticeFourier.JoiningContraction
public import PercLib.Analysis.LatticeFourier.JoiningIntegral
public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborIntegrals
public import PercLib.Percolation.Bond.SpatialMoments.FiniteRange

/-!
# The actual second joining core

## Main results

Dropping the connector deletions and the excluded joining diagonal gives the
seven-edge spatial diagram used in its Fourier estimate. The two actual step
kernels remain present, so their two masses are retained in subsequent bounds.
The proved three-frequency contraction and joining-integral estimate give the
actual nearest-neighbour bound `300 j² K⁸ S₃² B₃ (1 - D(k))`, assuming finite
susceptibility and the actual Fourier ratio and second-difference bounds by `K`.
No spatial joining estimate or integrability condition is an extra premise.
-/

@[expose] public section
noncomputable section

open DiscreteConvolution
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The actual continuation between two vertices is the rooted step/two-point
convolution evaluated at their displacement. -/
theorem continuation_eq_rooted_convolution
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) :
    (∑' v, offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) a v * tau q v b) =
      ((offDiagonal (fun x y : G =>
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0) (b - a) := by
  have h := tsum_offDiagonal_mul_tau_add_right q hq a b (-a)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at h
  rw [← h, addRingConvolution_eq_tsum_sub]
  apply tsum_congr
  intro v
  rw [tau_eq_rooted_of_add_right q hq v (b - a)]

private theorem continuation_convolution_even
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    Function.Even ((offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0) := by
  intro z
  have h := tsum_offDiagonal_mul_tau_comm q hq 0 z
  rw [continuation_eq_rooted_convolution q hq,
    continuation_eq_rooted_convolution q hq] at h
  simpa only [sub_zero, zero_sub] using h.symm

/-- Summing the common translation of the final deleted connector costs the
actual step/two-point/two-point convolution, with its relative endpoint retained. -/
theorem tsum_diagramConnector_translate_le_convolution
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a b : G) (r : G × G) :
    (∑' y, diagramConnector q (a, b) (r.1 + y, r.2 + y)) ≤
      (tau q 0 ⋆ᵣ₊ ((offDiagonal (fun x y : G =>
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0))
          (b - a - (r.2 - r.1)) := by
  let U := (offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0) ⋆ᵣ₊ tau q 0
  calc
    _ ≤ ∑' y, tau q a (r.1 + y) * U (r.2 + y - b) := by
      apply ENNReal.tsum_le_tsum
      intro y
      simpa only [continuation_eq_rooted_convolution q hq, U] using
        diagramConnector_le q (a, b) (r.1 + y, r.2 + y)
    _ = _ := by
      rw [← (Equiv.addRight (a - r.1)).tsum_eq, addRingConvolution_eq_tsum_sub]
      apply tsum_congr
      intro z
      change tau q a (r.1 + (z + (a - r.1))) * U (r.2 + (z + (a - r.1)) - b) =
        tau q 0 z * U (b - a - (r.2 - r.1) - z)
      have hfirst : r.1 + (z + (a - r.1)) - a = z := by abel
      have hsecond : r.2 + (z + (a - r.1)) - b =
          -(b - a - (r.2 - r.1) - z) := by abel
      have hU : Function.Even U := continuation_convolution_even q hq
      rw [tau_eq_rooted_of_add_right q hq, hfirst, hsecond, hU]

/-- The actual second joining core is bounded by its seven-edge convolution
diagram. The weight is arbitrary and the two actual step kernels are preserved. -/
theorem diagramMarkedJoiningSecondCore_le_spatial_sum
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (p r : G × G) :
    let J := offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
    let T := tau q 0
    let U := J ⋆ᵣ₊ T
    let L := T ⋆ᵣ₊ U
    diagramMarkedJoiningSecondCore q w p r ≤
      ∑' u, ∑' s, ∑' t, ∑' z,
        T u * U (s - (p.2 - p.1)) * T (z - s) * T (u - z) * T (t - z) *
          (w (t - u) * T (t - u)) * L (t - s - (r.2 - r.1)) := by
  classical
  dsimp only
  let J := offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  let U := J ⋆ᵣ₊ tau q 0
  let L := tau q 0 ⋆ᵣ₊ U
  have hgroup (u v t : G) :
      (∑' y, diagramConnector q p (u, v) * tau q u t *
        (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) *
          diagramConnector q (v, t) (r.1 + y, r.2 + y) * w (t - u)) =
      (diagramConnector q p (u, v) * tau q u t *
        (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) * w (t - u)) *
          ∑' y, diagramConnector q (v, t) (r.1 + y, r.2 + y) := by
    conv_rhs => rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro y
    ring
  have hinner (u v t : G) :
      (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) ≤
        ∑' z, tau q v z * tau q z u * tau q z t := by
    apply ENNReal.tsum_le_tsum
    intro z
    split_ifs <;> first | exact zero_le | exact le_rfl
  have hfirst (u v : G) : diagramConnector q p (u, v) ≤
      tau q p.1 u * U (v - p.2) := by
    simpa only [continuation_eq_rooted_convolution q hq, U, J] using
      diagramConnector_le q p (u, v)
  calc
    _ = ∑' u, ∑' v, ∑' t,
        (diagramConnector q p (u, v) * tau q u t *
          (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) * w (t - u)) *
            ∑' y, diagramConnector q (v, t) (r.1 + y, r.2 + y) := by
      unfold diagramMarkedJoiningSecondCore
      simp_rw [hgroup]
    _ ≤ ∑' u, ∑' v, ∑' t,
        ((tau q p.1 u * U (v - p.2)) * tau q u t *
          (∑' z, tau q v z * tau q z u * tau q z t) * w (t - u)) *
            L (t - v - (r.2 - r.1)) := by
      apply ENNReal.tsum_le_tsum
      intro u
      apply ENNReal.tsum_le_tsum
      intro v
      apply ENNReal.tsum_le_tsum
      intro t
      exact mul_le_mul'
        (mul_le_mul' (mul_le_mul' (mul_le_mul' (hfirst u v) le_rfl) (hinner u v t)) le_rfl)
        (tsum_diagramConnector_translate_le_convolution q hq v t r)
    _ = ∑' u, ∑' v, ∑' t, ∑' z,
        tau q p.1 u * U (v - p.2) * tau q v z * tau q z u * tau q z t *
          (w (t - u) * tau q u t) * L (t - v - (r.2 - r.1)) := by
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      apply tsum_congr
      intro t
      simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro z
      ring
    _ = _ := by
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro u
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro s
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro t
      rw [← (Equiv.addRight p.1).tsum_eq]
      apply tsum_congr
      intro z
      change tau q p.1 (u + p.1) * U (s + p.1 - p.2) *
        tau q (s + p.1) (z + p.1) * tau q (z + p.1) (u + p.1) *
          tau q (z + p.1) (t + p.1) *
            (w (t + p.1 - (u + p.1)) * tau q (u + p.1) (t + p.1)) *
              L (t + p.1 - (s + p.1) - (r.2 - r.1)) = _
      have hs : s + p.1 - p.2 = s - (p.2 - p.1) := by abel
      rw [tau_eq_rooted_of_add_right q hq p.1 (u + p.1),
        tau_eq_rooted_of_add_right q hq (s + p.1) (z + p.1),
        tau_eq_rooted_of_add_right q hq (z + p.1) (u + p.1),
        tau_eq_rooted_of_add_right q hq (z + p.1) (t + p.1),
        tau_eq_rooted_of_add_right q hq (u + p.1) (t + p.1)]
      simp only [add_sub_add_right_eq_sub, add_sub_cancel_right, hs, L, U, J]

end PercLib.Percolation.Bond.Lace

namespace PercLib.Percolation.Bond.Lace

open MeasureTheory UnitAddTorus Real PercLib.Analysis PercLib.Models.Site

/-- Finite susceptibility gives the actual seven-edge Fourier majorant for the
nearest-neighbour joining core. Both step kernels and both endpoint phases are
retained. No assumed Fourier contraction is used. -/
theorem diagramMarkedJoiningSecondCore_le_fourier_integral {d : ℕ}
    (p : unitInterval) (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (k : Fin d → ℝ) (s t : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := homogeneousProfile (zdGraph d) p
    let T := fun z : Fin d → ℤ => (tau q 0 z).toReal
    let J := fun z : Fin d → ℤ => (q s(0, z) : ℝ)
    let U := J ⋆ᵣ₊ T
    let L := T ⋆ᵣ₊ U
    let M := fun z : Fin d → ℤ => T z * (1 - cos (∑ i, k i * (z i : ℝ)))
    let FT := fun (f : (Fin d → ℤ) → ℝ) (l : UnitAddTorus (Fin d)) =>
      ∑' z, (f z : ℂ) * mFourier z l
    diagramMarkedJoiningSecondCore q (fun z => ENNReal.ofReal
      (1 - cos (∑ i, k i * (z i : ℝ)))) s t ≤
      ENNReal.ofReal ‖∫ l₁ : UnitAddTorus (Fin d), ∫ l₂ : UnitAddTorus (Fin d),
        ∫ l₃ : UnitAddTorus (Fin d),
          mFourier (s.2 - s.1) l₁ * mFourier (t.2 - t.1) l₂ *
            FT U l₁ * FT T l₁ * FT L l₂ * FT M l₃ *
            FT T (l₁ - l₂) * FT T (l₂ - l₃) * FT T (l₁ - l₃)
          ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
          ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
          ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ := by
  let q := homogeneousProfile (zdGraph d) p
  let TE := tau q 0
  let JE := offDiagonal (fun x y : Fin d → ℤ =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  let UE := JE ⋆ᵣ₊ TE
  let LE := TE ⋆ᵣ₊ UE
  let w := fun z : Fin d → ℤ => 1 - cos (∑ i, k i * (z i : ℝ))
  let T := fun z : Fin d → ℤ => (TE z).toReal
  let J := fun z : Fin d → ℤ => (q s(0, z) : ℝ)
  let U := J ⋆ᵣ₊ T
  let L := T ⋆ᵣ₊ U
  let M := fun z : Fin d → ℤ => T z * w z
  let SE := fun z : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    TE z.1 * UE (z.2.1 - (s.2 - s.1)) * TE (z.2.2.2 - z.2.1) * TE (z.1 - z.2.2.2) *
      TE (z.2.2.1 - z.2.2.2) * (ENNReal.ofReal (w (z.2.2.1 - z.1)) * TE (z.2.2.1 - z.1)) *
      LE (z.2.2.1 - z.2.1 - (t.2 - t.1))
  let SR := fun z : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    T z.1 * U (z.2.1 - (s.2 - s.1)) * T (z.2.2.2 - z.2.1) * T (z.1 - z.2.2.2) *
      T (z.2.2.1 - z.2.2.2) * M (z.2.2.1 - z.1) * L (z.2.2.1 - z.2.1 - (t.2 - t.1))
  have hw0 (z : Fin d → ℤ) : 0 ≤ w z := sub_nonneg.mpr (cos_le_one _)
  have hTE : (∑' z, TE z) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have hJE : (∑' z, JE z) ≠ ⊤ := nn_step_mass_ne_top p
  have hUE : (∑' z, UE z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hJE hTE
  have hTEz (z) : TE z ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q 0 z)
  have hJEz (z) : JE z ≠ ⊤ := by
    dsimp only [JE, q]
    rw [nn_offDiagonal_eq]
    exact ENNReal.ofReal_ne_top
  have hUEz (z) : UE z ≠ ⊤ := addRingConvolution_ennreal_ne_top hJE hTE z
  have hLEz (z) : LE z ≠ ⊤ := addRingConvolution_ennreal_ne_top hTE hUE z
  have hJreal (z) : (JE z).toReal = J z := nn_offDiagonal_toReal p z
  have hUreal (z) : (UE z).toReal = U z := by
    rw [toReal_addRingConvolution_ennreal hJEz hTEz]
    simp only [hJreal]
    rfl
  have hLreal (z) : (LE z).toReal = L z := by
    rw [toReal_addRingConvolution_ennreal hTEz hUEz]
    simp only [hUreal]
    rfl
  have hSEfinite (z) : SE z ≠ ⊤ := by
    dsimp only [SE]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hTEz _) (hUEz _))
        (hTEz _)) (hTEz _)) (hTEz _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTEz _))) (hLEz _)
  have hSEreal (z) : (SE z).toReal = SR z := by
    simp only [SE, SR, M, ENNReal.toReal_mul, hUreal, hLreal,
      ENNReal.toReal_ofReal (hw0 _)]
    dsimp only [T]
    ring
  have hSR0 (z) : 0 ≤ SR z := by
    rw [← hSEreal]
    exact ENNReal.toReal_nonneg
  have hSEofReal (z) : ENNReal.ofReal (SR z) = SE z := by
    rw [← hSEreal, ENNReal.ofReal_toReal (hSEfinite z)]
  have hT : Summable T := ENNReal.summable_toReal hTE
  have hJ : Summable J := summable_homogeneous_zdGraph p
  have hU : Summable U := summable_addRingConvolution_real hJ hT
  have hL : Summable L := summable_addRingConvolution_real hT hU
  have hM : Summable M := summable_tau_mul_cosine_weight q hchi k
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  have heM : Function.Even M := by
    intro z
    simp only [M, w, heT z, Pi.neg_apply, Int.cast_neg, mul_neg,
      Finset.sum_neg_distrib, cos_neg]
  have hbase := joining_series_summable_and_integral_eq
    (fun z => (T z : ℂ)) (fun z => (U z : ℂ)) (fun z => (L z : ℂ)) (fun z => (M z : ℂ))
    (by simpa only [Complex.norm_real] using hT.norm)
    (by simpa only [Complex.norm_real] using hU.norm)
    (by simpa only [Complex.norm_real] using hL.norm)
    (by simpa only [Complex.norm_real] using hM.norm)
    (fun z => by simp only [heT z]) (fun z => by simp only [heM z])
    (s.2 - s.1) (t.2 - t.1)
  dsimp only at hbase
  have hSR : Summable SR := by
    apply hbase.1.of_norm_bounded
    intro z
    simp only [← Complex.ofReal_mul, Complex.norm_real, SR]
    exact le_rfl
  have hid := congrArg Complex.re hbase.2
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, Complex.ofReal_re] at hid
  calc
    _ ≤ ∑' z, SE z := by
      have h := diagramMarkedJoiningSecondCore_le_spatial_sum q
        (homogeneous_zdGraph_add p) (fun z => ENNReal.ofReal (w z)) s t
      simpa only [SE, LE, UE, TE, JE, q, w, ENNReal.tsum_prod'] using h
    _ = ENNReal.ofReal (∑' z, SR z) := by
      simp_rw [← hSEofReal]
      exact (ENNReal.ofReal_tsum_of_nonneg hSR0 hSR).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← hid]
      exact Complex.re_le_norm _


/-- The actual weak Fourier bootstrap bounds all seven joining factors. Both
step masses are retained, and the marked transform contributes the exact factor 100. -/
theorem abs_joining_fourier_product_le {d : ℕ} (hd : 0 < d)
    (p : unitInterval) (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK₂ : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (hK₃ : fourierDifferenceSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (k l₁ l₂ l₃ : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    let T := fun z : Fin d → ℤ => (tau q 0 z).toReal
    let J := fun z : Fin d → ℤ => (q s(0, z) : ℝ)
    let M := fun z : Fin d → ℤ => T z * (1 - cos (∑ i, k i * (z i : ℝ)))
    let C := nearestNeighborResolvent (susceptibilityWalkParameter q)
    let Q := fun a b : Fin d → ℝ =>
      |nearestNeighborSymbol l₁| * C l₁ ^ 2 * |nearestNeighborSymbol l₂| * C l₂ ^ 2 *
        C (l₃ + a) * C (l₃ + b) * C (l₁ - l₂) * C (l₂ - l₃) * C (l₁ - l₃)
    |latticeCosineTransform (J ⋆ᵣ₊ T) l₁| * |latticeCosineTransform T l₁| *
      |latticeCosineTransform (T ⋆ᵣ₊ (J ⋆ᵣ₊ T)) l₂| * |latticeCosineTransform M l₃| *
      |latticeCosineTransform T (l₁ - l₂)| * |latticeCosineTransform T (l₂ - l₃)| *
      |latticeCosineTransform T (l₁ - l₃)| ≤
      100 * (2 * d * (p : ℝ)) ^ 2 * K ^ 8 * (1 - nearestNeighborSymbol k) *
        (Q (-k) 0 + Q 0 k + Q (-k) k) := by
  let q := homogeneousProfile (zdGraph d) p
  let T := fun z : Fin d → ℤ => (tau q 0 z).toReal
  let J := fun z : Fin d → ℤ => (q s(0, z) : ℝ)
  let M := fun z : Fin d → ℤ => T z * (1 - cos (∑ i, k i * (z i : ℝ)))
  let j : ℝ := 2 * d * (p : ℝ)
  let r := susceptibilityWalkParameter q
  let C := nearestNeighborResolvent (d := d) r
  let g := 1 - nearestNeighborSymbol k
  have hj0 : 0 ≤ j := mul_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) p.2.1
  have hg0 : 0 ≤ g := sub_nonneg.mpr (le_abs_self _ |>.trans
    (nearestNeighborSymbol_abs_le_one hd k))
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hC0 (l : Fin d → ℝ) : 0 ≤ C l := (nearestNeighborResolvent_pos hd hr l).le
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have hJ : Summable J := summable_homogeneous_zdGraph p
  have heJ : Function.Even J := even_homogeneous_zdGraph p
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  have hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤ :=
    (spatialMoment_sq_lt_top_of_finiteRange_of_transitive q 0 (by norm_num : (0 : ℝ) ≤ 1)
      (homogeneous_zdGraph_eq_zero_of_one_lt_norm p) (homogeneous_zdGraph_transitive p) hchi).ne
  have hUhat (l : Fin d → ℝ) : latticeCosineTransform (J ⋆ᵣ₊ T) l =
      j * nearestNeighborSymbol l * tauFourier q l := by
    rw [latticeCosineTransform_addRingConvolution hJ hT heJ,
      latticeCosineTransform_homogeneous_zdGraph hd p]
    rfl
  have hLhat (l : Fin d → ℝ) : latticeCosineTransform (T ⋆ᵣ₊ (J ⋆ᵣ₊ T)) l =
      tauFourier q l * (j * nearestNeighborSymbol l * tauFourier q l) := by
    rw [latticeCosineTransform_addRingConvolution hT
      (summable_addRingConvolution_real hJ hT) heT, hUhat]
    rfl
  have hτ (l : Fin d → ℝ) : |tauFourier q l| ≤ K * C l :=
    abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd q hchi hK₂ l
  have hMhat : |latticeCosineTransform M l₃| ≤
      100 * K * g * bootstrapTripleProduct r k l₃ :=
    abs_tau_weightFourier_le_of_fourierDifferenceSup_le hd q hchi hsecond hK₃ k l₃
  have hC12 := hC0 (l₁ - l₂)
  have hC23 := hC0 (l₂ - l₃)
  have hC13 := hC0 (l₁ - l₃)
  have hV0 : 0 ≤ bootstrapTripleProduct r k l₃ :=
    add_nonneg (add_nonneg (mul_nonneg (hC0 _) (hC0 _))
      (mul_nonneg (hC0 _) (hC0 _))) (mul_nonneg (hC0 _) (hC0 _))
  change |latticeCosineTransform (J ⋆ᵣ₊ T) l₁| * |tauFourier q l₁| *
    |latticeCosineTransform (T ⋆ᵣ₊ (J ⋆ᵣ₊ T)) l₂| * |latticeCosineTransform M l₃| *
    |tauFourier q (l₁ - l₂)| * |tauFourier q (l₂ - l₃)| *
    |tauFourier q (l₁ - l₃)| ≤ _
  calc
    _ = j ^ 2 * |nearestNeighborSymbol l₁| * |nearestNeighborSymbol l₂| *
        |tauFourier q l₁| ^ 2 * |tauFourier q l₂| ^ 2 * |latticeCosineTransform M l₃| *
        |tauFourier q (l₁ - l₂)| * |tauFourier q (l₂ - l₃)| *
        |tauFourier q (l₁ - l₃)| := by
      simp only [hUhat, hLhat, abs_mul, abs_of_nonneg hj0]
      ring
    _ ≤ j ^ 2 * |nearestNeighborSymbol l₁| * |nearestNeighborSymbol l₂| *
        (K * C l₁) ^ 2 * (K * C l₂) ^ 2 *
        (100 * K * g * bootstrapTripleProduct r k l₃) *
        (K * C (l₁ - l₂)) * (K * C (l₂ - l₃)) * (K * C (l₁ - l₃)) := by
      gcongr <;> exact hτ _
    _ = _ := by
      dsimp only [bootstrapTripleProduct, C, r, j, g]
      simp only [add_zero, ← sub_eq_add_neg]
      ring


open Metric in
/-- The actual nearest-neighbour joining core obeys the walk-integral estimate
under the actual weak Fourier bootstrap. The exact two step masses are retained. -/
theorem diagramMarkedJoiningSecondCore_le_nn_walk_integrals {d : ℕ} (hd : 0 < d)
    (p : unitInterval) (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK₂ : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (hK₃ : fourierDifferenceSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) (s t : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := homogeneousProfile (zdGraph d) p
    let r := susceptibilityWalkParameter q
    let S₃ := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborResolvent r l ^ 3
    let B₃ := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3
    diagramMarkedJoiningSecondCore q (fun z => ENNReal.ofReal
      (1 - cos (∑ i, k i * (z i : ℝ)))) s t ≤
      ENNReal.ofReal (300 * (2 * d * (p : ℝ)) ^ 2 * K ^ 8 * S₃ ^ 2 * B₃ *
        (1 - nearestNeighborSymbol k)) := by
  let q := homogeneousProfile (zdGraph d) p
  let T := fun z : Fin d → ℤ => (tau q 0 z).toReal
  let J := fun z : Fin d → ℤ => (q s(0, z) : ℝ)
  let U := J ⋆ᵣ₊ T
  let L := T ⋆ᵣ₊ U
  let M := fun z : Fin d → ℤ => T z * (1 - cos (∑ i, k i * (z i : ℝ)))
  let r := susceptibilityWalkParameter q
  let A := 100 * (2 * d * (p : ℝ)) ^ 2 * K ^ 8 * (1 - nearestNeighborSymbol k)
  let Φ := fun l : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
    |latticeCosineTransform U l.1| * |latticeCosineTransform T l.1| *
      |latticeCosineTransform L l.2.1| * |latticeCosineTransform M l.2.2| *
      |latticeCosineTransform T (l.1 - l.2.1)| *
      |latticeCosineTransform T (l.2.1 - l.2.2)| *
      |latticeCosineTransform T (l.1 - l.2.2)|
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have hJ : Summable J := summable_homogeneous_zdGraph p
  have hU : Summable U := summable_addRingConvolution_real hJ hT
  have hL : Summable L := summable_addRingConvolution_real hT hU
  have hM : Summable M := summable_tau_mul_cosine_weight q hchi k
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  have heJ : Function.Even J := even_homogeneous_zdGraph p
  have heU : Function.Even U := even_addRingConvolution heJ heT
  have heL : Function.Even L := even_addRingConvolution heT heU
  have heM : Function.Even M := by
    intro z
    simp only [M, heT z, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, cos_neg]
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (pow_nonneg hK0 8)) (sub_nonneg.mpr (le_abs_self _ |>.trans
      (nearestNeighborSymbol_abs_le_one hd k)))
  have hcT := continuous_latticeCosineTransform hT
  have hcU := continuous_latticeCosineTransform hU
  have hcL := continuous_latticeCosineTransform hL
  have hcM := continuous_latticeCosineTransform hM
  have hΦ : Continuous Φ := by dsimp only [Φ]; fun_prop
  have hΦ0 (l) : 0 ≤ Φ l := by dsimp only [Φ]; positivity
  have hi := integral_le_of_nearestNeighbor_joining_majorant hd
    (susceptibilityWalkParameter_mem_Ico q hchi) hA k Φ hΦ hΦ0
    (fun l₁ l₂ l₃ => abs_joining_fourier_product_le hd p hchi hK0 hK₂ hK₃ k l₁ l₂ l₃)
  have hn := norm_joining_integral_le_normalized_abs_cosine_transforms T U L M
    hT hU hL hM heT heU heL heM (s.2 - s.1) (t.2 - t.1)
  have hcore := diagramMarkedJoiningSecondCore_le_fourier_integral p hchi k s t
  convert hcore.trans (ENNReal.ofReal_le_ofReal (hn.trans hi)) using 1
  congr 1
  dsimp only [A]
  ring

end PercLib.Percolation.Bond.Lace
