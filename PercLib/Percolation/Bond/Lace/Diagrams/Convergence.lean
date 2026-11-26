/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Coefficients
public import PercLib.Percolation.Bond.Lace.Diagrams.Bounds
public import PercLib.Percolation.Bond.Lace.Expansion.Infinite

/-!
# Coefficient summability from the proved diagram comparison

The actual positive coefficients inherit the pair-state geometric estimate.
The zeroth coefficient is controlled by a slice of the initial diagram, so
finite initial diagram mass also supplies its summability. The total bound
retains the actual zeroth mass instead of replacing it by a larger diagram.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Classical Topology

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

/-- A slice of the initial pair-state diagram dominates the zeroth coefficient. -/
theorem piZero_le_diagramInitial (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y ≤ diagramInitial q x (x, y) := by
  by_cases hy : y = x
  · subst y
    simp [diagramInitial]
  · simpa [diagramInitial, hy, pow_two, tau_self] using piZero_le_tau_sq q x y

/-- Finite initial diagram mass also controls the zeroth coefficient row. -/
theorem tsum_piZero_le_diagramInitial (q : Sym2 V → unitInterval) (x : V) :
    (∑' y, piZero q x y) ≤ ∑' p, diagramInitial q x p := by
  refine (ENNReal.tsum_le_tsum (piZero_le_diagramInitial q x)).trans ?_
  have hi : Function.Injective (fun y : V => (x, y)) :=
    fun _ _ h => congrArg Prod.snd h
  exact ENNReal.tsum_comp_le_tsum_of_injective hi (diagramInitial q x)

/-- The actual coefficient of order `n+1` has the exact geometric row bound,
including the separate terminal constant. -/
theorem laceCoefficient_mass_le_diagram_geometric (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) (n : ℕ) :
    (∑' y, laceCoefficient q (n + 1) x y) ≤
      (∑' p, diagramInitial q x p) * ρ ^ n * κ :=
  (ENNReal.tsum_le_tsum (laceCoefficient_succ_le_laceDiagram q n x)).trans
    (laceDiagram_mass_le_geometric q x ρ κ hρ hκ n)

/-- The total positive coefficient mass inherits the geometric denominator
from the actual pair-state diagram estimate. -/
theorem tsum_laceCoefficient_mass_le_diagram (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) :
    (∑' n : ℕ, ∑' y, laceCoefficient q (n + 1) x y) ≤
      (∑' p, diagramInitial q x p) * (1 - ρ)⁻¹ * κ :=
  (ENNReal.tsum_le_tsum fun n =>
    ENNReal.tsum_le_tsum (laceCoefficient_succ_le_laceDiagram q n x)).trans
      (tsum_laceDiagram_mass_le q x ρ κ hρ hκ)

/-- The total mass over all orders retains the actual zeroth coefficient row. -/
theorem tsum_laceCoefficient_all_mass_le_diagram (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) :
    (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≤
      (∑' y, piZero q x y) + (∑' p, diagramInitial q x p) * (1 - ρ)⁻¹ * κ := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  exact add_le_add le_rfl (tsum_laceCoefficient_mass_le_diagram q x ρ κ hρ hκ)

/-- Subunit transfer and finite initial and terminal bounds imply summability
of all actual coefficient masses, including order zero. -/
theorem tsum_laceCoefficient_all_mass_ne_top_of_diagram
    (q : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤ := by
  have hzero : (∑' y, piZero q x y) ≠ ⊤ :=
    ne_top_of_le_ne_top hinitial (tsum_piZero_le_diagramInitial q x)
  have hpositive : (∑' n : ℕ, ∑' y, laceCoefficient q (n + 1) x y) ≠ ⊤ :=
    ne_top_of_le_ne_top (tsum_laceDiagram_mass_ne_top q x ρ κ hρone hκfinite hρ hκ hinitial)
      (ENNReal.tsum_le_tsum fun n =>
        ENNReal.tsum_le_tsum (laceCoefficient_succ_le_laceDiagram q n x))
  rw [tsum_eq_zero_add' ENNReal.summable]
  exact ENNReal.add_ne_top.mpr ⟨hzero, hpositive⟩

/-- The canonical infinite signed kernel is summable under the proved diagram
criterion. No separate zeroth-coefficient assumption is needed. -/
theorem summable_laceSum_of_diagram_bounds (q : Sym2 V → unitInterval)
    (x : V) (ρ κ : ℝ≥0∞) (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    Summable (laceSum q x) :=
  summable_laceSum q x
    (tsum_laceCoefficient_all_mass_ne_top_of_diagram q x ρ κ hρone hκfinite hρ hκ hinitial)

/-- The finite signed kernels converge under the diagram criterion. -/
theorem tendsto_partialLaceSum_of_diagram_bounds (q : Sym2 V → unitInterval)
    (x y : V) (ρ κ : ℝ≥0∞) (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' z, diagramTerminal q p z) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    Tendsto (fun N => partialLaceSum q N x y) atTop (𝓝 (laceSum q x y)) :=
  tendsto_partialLaceSum q x y
    (tsum_laceCoefficient_all_mass_ne_top_of_diagram q x ρ κ hρone hκfinite hρ hκ hinitial)

/-- Diagram contraction supplies the analytic summability needed for the
actual signed remainder to vanish. -/
theorem tendsto_signedLaceRemainder_zero_of_diagram_bounds
    (q : Sym2 V → unitInterval) (x y : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' z, diagramTerminal q p z) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u z, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v z) ≤ C) :
    Tendsto (fun N => signedLaceRemainder q N x y) atTop (𝓝 0) :=
  tendsto_signedLaceRemainder_zero q x y C hCfinite hC
    (tsum_laceCoefficient_all_mass_ne_top_of_diagram q x ρ κ hρone hκfinite hρ hκ hinitial)

/-- The infinite signed lace expansion follows from the actual diagram
contraction criterion, together with finite deleted clusters and a finite
uniform continuation bound. -/
theorem infinite_lace_expansion_of_diagram_bounds
    (q : Sym2 V → unitInterval) (x y : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' z, diagramTerminal q p z) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤)
    (hfin : ∀ a u v : V, ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u z, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v z) ≤ C) :
    (tau q x y).toReal = (if x = y then 1 else 0) + laceSum q x y +
      (∑' v, (offDiagonal (fun a b : V =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) x v).toReal * (tau q v y).toReal) +
      (∑' u, ∑' v, laceSum q x u *
        (offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v).toReal * (tau q v y).toReal) :=
  infinite_lace_expansion q x y hfin C hCfinite hC
    (tsum_laceCoefficient_all_mass_ne_top_of_diagram q x ρ κ hρone hκfinite hρ hκ hinitial)

end PercLib.Percolation.Bond.Lace
