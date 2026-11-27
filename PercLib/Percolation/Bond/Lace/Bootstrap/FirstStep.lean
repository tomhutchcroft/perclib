/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the first-step decomposition in the Fourier bootstrap
for nearest-neighbour percolation, Heydenreich and van der Hofstad (2017).
-/
module

public import PercLib.Analysis.DiscreteConvolution
public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedConnectorBounds

/-!
# The actual first-step convolution expansion

The connection bound obtained from the last exit from a singleton gives
`J * tau³ ≤ J + J² * tau + J² * tau² + J² * tau³`. The inequality is proved
in physical space, where every factor is nonnegative. It therefore makes no
comparison involving a signed Fourier transform of the step kernel.

## Main results

* `tau_le_single_add_addRingConvolution`: the actual rooted first-step bound.
* `step_tau_three_le_firstStep_expansion`: the extended-nonnegative expansion.
* `step_tau_three_toReal_le_firstStep_expansion`: its real Fourier-compatible form.
-/

@[expose] public section
noncomputable section

open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

/-- The existing nonnegative convolution associativity in additive-fiber notation. -/
theorem addRingConvolution_ennreal_assoc (f g h : G → ℝ≥0∞) :
    (f ⋆ᵣ₊ g) ⋆ᵣ₊ h = f ⋆ᵣ₊ (g ⋆ᵣ₊ h) := by
  funext x
  simp only [addRingConvolution_eq_tsum_sub]
  have ha := PercLib.Analysis.conv_assoc (fun y : Multiplicative G => f y.toAdd)
    (fun y : Multiplicative G => g y.toAdd) (fun y : Multiplicative G => h y.toAdd)
    (Multiplicative.ofAdd x)
  simp only [← Multiplicative.ofAdd.tsum_eq] at ha
  simpa only [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg, add_comm] using ha

/-- Nonnegative convolution preserves pointwise inequalities in both factors. -/
theorem addRingConvolution_ennreal_mono {f f' g g' : G → ℝ≥0∞}
    (hf : f ≤ f') (hg : g ≤ g') : f ⋆ᵣ₊ g ≤ f' ⋆ᵣ₊ g' := by
  intro x
  exact ENNReal.tsum_le_tsum fun p => mul_le_mul' (hf p.val.1) (hg p.val.2)

/-- Total mass of the existing additive convolution of nonnegative kernels. -/
theorem tsum_addRingConvolution_ennreal (f g : G → ℝ≥0∞) :
    (∑' x, (f ⋆ᵣ₊ g) x) = (∑' x, f x) * ∑' x, g x := by
  simp only [addRingConvolution_eq_tsum_sub]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro y
  rw [ENNReal.tsum_mul_left]
  congr 1
  simpa only [sub_eq_add_neg, Equiv.coe_addRight] using (Equiv.addRight (-y)).tsum_eq g

/-- Finite masses give finite convolution entries. -/
theorem addRingConvolution_ennreal_ne_top {f g : G → ℝ≥0∞}
    (hf : (∑' x, f x) ≠ ⊤) (hg : (∑' x, g x) ≠ ⊤) (x : G) :
    (f ⋆ᵣ₊ g) x ≠ ⊤ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hf hg)
  rw [← tsum_addRingConvolution_ennreal]
  exact ENNReal.le_tsum x

/-- Real projection commutes with convolution of kernels with finite entries. -/
theorem toReal_addRingConvolution_ennreal {f g : G → ℝ≥0∞}
    (hf : ∀ x, f x ≠ ⊤) (hg : ∀ x, g x ≠ ⊤) (x : G) :
    ((f ⋆ᵣ₊ g) x).toReal =
      ((fun y => (f y).toReal) ⋆ᵣ₊ (fun y => (g y).toReal)) x := by
  simp only [DiscreteConvolution.addRingConvolution_apply]
  rw [ENNReal.tsum_toReal_eq
    (fun p : DiscreteConvolution.addFiber x => ENNReal.mul_ne_top (hf p.val.1) (hg p.val.2))]
  simp only [ENNReal.toReal_mul]

open Classical in
/-- Iterating a first-step inequality three times leaves two step factors in
every convolution term except the direct step. -/
theorem addRingConvolution_three_le_of_firstStep (J T : G → ℝ≥0∞)
    (hT : T ≤ Pi.single 0 1 + J ⋆ᵣ₊ T) :
    J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) ≤
      J + J ⋆ᵣ₊ (J ⋆ᵣ₊ T) + J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T)) +
        J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) := by
  classical
  have h1 : J ⋆ᵣ₊ T ≤ J + J ⋆ᵣ₊ (J ⋆ᵣ₊ T) := by
    have h := addRingConvolution_ennreal_mono (le_refl J) hT
    simpa only [DiscreteConvolution.addRingConvolution_add _ _ _
      (fun _ => ENNReal.summable) (fun _ => ENNReal.summable),
      DiscreteConvolution.addRingConvolution_single] using h
  have hstep (F : G → ℝ≥0∞) :
      J ⋆ᵣ₊ (T ⋆ᵣ₊ F) ≤ J ⋆ᵣ₊ F + J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ F)) := by
    have h := addRingConvolution_ennreal_mono (le_refl J)
      (addRingConvolution_ennreal_mono hT (le_refl F))
    simpa only [DiscreteConvolution.add_addRingConvolution _ _ _
      (fun _ => ENNReal.summable) (fun _ => ENNReal.summable),
      DiscreteConvolution.single_addRingConvolution,
      DiscreteConvolution.addRingConvolution_add _ _ _
        (fun _ => ENNReal.summable) (fun _ => ENNReal.summable),
      addRingConvolution_ennreal_assoc] using h
  intro x
  exact (hstep (T ⋆ᵣ₊ T) x).trans
    (add_le_add ((hstep T x).trans (add_le_add (h1 x) le_rfl)) le_rfl)

open Classical in
/-- The actual two-point function satisfies the rooted first-step inequality. -/
theorem tau_le_single_add_addRingConvolution [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    tau q 0 ≤ Pi.single 0 1 +
      (offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
        ⋆ᵣ₊ tau q 0) := by
  classical
  intro x
  by_cases hx : x = 0
  · subst x
    simp only [Pi.add_apply, Pi.single_eq_same, tau_self]
    exact le_add_right le_rfl
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hx, zero_add,
      addRingConvolution_eq_tsum_sub]
    refine (tau_le_tsum_offDiagonal_mul_tau q (Ne.symm hx)).trans_eq ?_
    apply tsum_congr
    intro v
    rw [tau_eq_rooted_of_add_right q hq v x]

/-- The first-step expansion for the actual two-point function, without any
summability assumption. -/
theorem step_tau_three_le_firstStep_expansion [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) :
    let J := offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    let T := tau q 0
    J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) ≤
      J + J ⋆ᵣ₊ (J ⋆ᵣ₊ T) + J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T)) +
        J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) :=
  addRingConvolution_three_le_of_firstStep _ _ (tau_le_single_add_addRingConvolution q hq)

/-- Finite step mass and finite susceptibility give the real convolution form
of the actual first-step expansion, ready for Fourier coefficient bounds. -/
theorem step_tau_three_toReal_le_firstStep_expansion [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (hJ : (∑' z, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 z) ≠ ⊤)
    (hchi : chi q 0 ≠ ⊤) :
    let J : G → ℝ := fun z => (offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 z).toReal
    let T : G → ℝ := fun z => (tau q 0 z).toReal
    J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) ≤
      J + J ⋆ᵣ₊ (J ⋆ᵣ₊ T) + J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T)) +
        J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) := by
  let J := offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
  let T := tau q 0
  have hT : (∑' z, T z) ≠ ⊤ := by rwa [chi_eq_tsum_tau] at hchi
  have hm (f g : G → ℝ≥0∞) (hf : (∑' z, f z) ≠ ⊤) (hg : (∑' z, g z) ≠ ⊤) :
      (∑' z, (f ⋆ᵣ₊ g) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hf hg
  have hT2 := hm T T hT hT
  have hT3 := hm T (T ⋆ᵣ₊ T) hT hT2
  have hJT := hm J T hJ hT
  have hJTT := hm J (T ⋆ᵣ₊ T) hJ hT2
  have hJTTT := hm J (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) hJ hT3
  have hJJT := hm J (J ⋆ᵣ₊ T) hJ hJT
  have hJJTT := hm J (J ⋆ᵣ₊ (T ⋆ᵣ₊ T)) hJ hJTT
  have hJJTTT := hm J (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) hJ hJTTT
  have hp (f : G → ℝ≥0∞) (hf : (∑' z, f z) ≠ ⊤) (z : G) : f z ≠ ⊤ :=
    ne_top_of_le_ne_top hf (ENNReal.le_tsum z)
  dsimp only
  intro x
  have h := step_tau_three_le_firstStep_expansion q hq x
  change (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x ≤
    J x + (J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) x + (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x +
      (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)))) x at h
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hp J hJ x, hp _ hJJT x⟩, hp _ hJJTT x⟩,
      hp _ hJJTTT x⟩) h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hp J hJ x, hp _ hJJT x⟩, hp _ hJJTT x⟩) (hp _ hJJTTT x),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hp J hJ x, hp _ hJJT x⟩) (hp _ hJJTT x),
    ENNReal.toReal_add (hp J hJ x) (hp _ hJJT x)] at hreal
  simp only [toReal_addRingConvolution_ennreal (hp J hJ) (hp _ hJTTT),
    toReal_addRingConvolution_ennreal (hp J hJ) (hp _ hJTT),
    toReal_addRingConvolution_ennreal (hp J hJ) (hp _ hJT),
    toReal_addRingConvolution_ennreal (hp J hJ) (hp _ hT3),
    toReal_addRingConvolution_ennreal (hp J hJ) (hp _ hT2),
    toReal_addRingConvolution_ennreal (hp J hJ) (hp T hT),
    toReal_addRingConvolution_ennreal (hp T hT) (hp _ hT2),
    toReal_addRingConvolution_ennreal (hp T hT) (hp T hT)] at hreal
  exact hreal

end PercLib.Percolation.Bond.Lace
