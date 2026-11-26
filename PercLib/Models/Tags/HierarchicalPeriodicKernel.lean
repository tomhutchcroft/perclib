/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's periodic-kernel theorems. No upstream code is copied and no
definition is added. Mathematical reference: T. Hutchcroft, *Critical cluster volumes in
hierarchical percolation*, arXiv:2211.05686 (periodic boundary conditions on a block).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalPeriodicKernel

/-!
# The periodic block kernel (tagged statement)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `hasSum_projFibre_and_periodicKernel_eq_and_law`: periodizing the exact hierarchical kernel
  over the fibres of the projection onto a block adds the constant `q/(1-q) L^{-sn}`, and periodic
  percolation on the block is the block process with its last coalescent stage run to time
  `β L^{-sn}/(1 - q)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models.HierarchicalLayers

variable {d L : ℕ}

/-- **Periodizing the hierarchical kernel adds an explicit final coalescent time.** On the
hierarchical lattice `V = ℕ →₀ (Fin d → ZMod L)`, `L ≥ 2`, let `α > 0`, `s = d + α`,
`q = L^{-α}`, and let `π_n` keep the coordinates below `n`, so that `block n 0 = B_n` and
`projFibre n y = {z | π_n z = y}`.
* For distinct `x, y ∈ B_n` the fibre sum `J_n^per(x,y) = ∑_{π_n z = y} J_∞(x,z)` converges to
  `J_n^free(x,y) + q/(1-q) L^{-sn}`, where `J_n^free(x,y) = ∑_{j=h(x,y)}^n L^{-sj}` is the
  truncated kernel `truncatedKernel L s n 0`.
* As kernels on all pairs, `periodicKernel = J_n^free + q/(1-q) L^{-sn}` on the pairs of `B_n`.
* At every intensity `β`, periodic percolation on `B_n` is the union of independent copies of the
  truncated block law and of a complete-graph layer on `B_n` of intensity `β q/(1-q) L^{-sn}`.
* Equivalently, it is the union of the layers below level `n` (left unchanged) and an
  independent complete-graph layer on `B_n` of intensity `β L^{-sn}/(1 - q)`: the last coalescent
  stage runs to time `β L^{-sn}/(1 - q)` instead of `β L^{-sn}`. -/
@[tag "YY9S"]
theorem hasSum_projFibre_and_periodicKernel_eq_and_law (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α)
    (n : ℕ) :
    let s : ℝ := d + α
    let q : ℝ := (L : ℝ) ^ (-α)
    (∀ x y : ℕ →₀ (Fin d → ZMod L), x ∈ block n 0 → y ∈ block n 0 → x ≠ y →
      HasSum (fun z : projFibre n y => (exactKernel (L : ℝ) s s(x, z) : ℝ))
        ((truncatedKernel (L : ℝ) s n 0 s(x, y) : ℝ) + q / (1 - q) * (L : ℝ) ^ (-(s * n)))) ∧
    periodicKernel (L : ℝ) s n (A := Fin d → ZMod L) =
      truncatedKernel (L : ℝ) s n 0 +
        completeKernel n 0 (q / (1 - q) * (L : ℝ) ^ (-(s * n))).toNNReal ∧
    (∀ β : ℝ≥0,
      law (intensityProfile (periodicKernel (L : ℝ) s n (A := Fin d → ZMod L)) β) =
        ((law (intensityProfile (truncatedKernel (L : ℝ) s n 0) β)).prod
          (law (intensityProfile
            (completeKernel n 0 (q / (1 - q) * (L : ℝ) ^ (-(s * n))).toNNReal) β))).map
          (fun ω => ω.1 ∪ ω.2)) ∧
    (∀ β : ℝ≥0,
      law (intensityProfile (periodicKernel (L : ℝ) s n (A := Fin d → ZMod L)) β) =
        ((law (intensityProfile (truncatedKernel (L : ℝ) s n 0 -
            completeKernel n 0 ((L : ℝ) ^ (-(s * n))).toNNReal) β)).prod
          (law (intensityProfile
            (completeKernel n 0 ((L : ℝ) ^ (-(s * n)) / (1 - q)).toNNReal) β))).map
          (fun ω => ω.1 ∪ ω.2)) := by
  intro s q
  exact ⟨fun x y hx hy hxy => hasSum_projFibre_exactKernel hL hα hx hy hxy,
    periodicKernel_eq_add_completeKernel hL hα n,
    fun β => law_periodicKernel_eq_map_union hL hα n β,
    fun β => law_periodicKernel_eq_map_union_lastLayer hL hα n β⟩

end PercLib.Models.HierarchicalLayers
