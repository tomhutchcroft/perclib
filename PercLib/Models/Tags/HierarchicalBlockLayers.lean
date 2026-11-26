/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's block-layer theorems. No upstream code is copied and no
definition is added. Mathematical reference: T. Hutchcroft, *Critical cluster volumes in
hierarchical percolation*, arXiv:2211.05686 (the exact radial model and its block layers).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalBlockLayers

/-!
# Independent complete-block layers (tagged statement)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `law_fullConfig_and_blockConfig_and_iUnion_cluster`: exponential-clock block layers on the
  hierarchical lattice give the exact radial law, the truncated block laws, the induced graph on
  a block as the block layers plus an independent ancestor layer, and increasing block clusters.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models.HierarchicalLayers

variable {d L : ℕ}

/-- **Independent complete-block layers and the hierarchical cluster law.** On the hierarchical
lattice `V = ℕ →₀ (Fin d → ZMod L)`, `L ≥ 2`, let `α > 0`, `s = d + α` and `β ≥ 0`. Index the
copies of the pairs by `(m, e)`, a copy of `e` in its common block of level `m ≥ h(e)`
(`IsCopy`), give them independent rate-one exponential clocks `T`, and open a copy when
`T(m, e) ≤ t_m = β L^{-sm}` (`openCopies`). Then:
1. the open copies are independent with probabilities `1 - exp(-t_m)` (`layerProfile`);
2. the union of all layers `ω` (`fullConfig`) is bond percolation with kernel `J_∞`
   (`exactKernel`, `L^s/(L^s - 1) ‖x - y‖^{-s}` with `‖x - y‖ = L^{h(x,y)}`), and
   `J_∞(x,y) = ∑_{m ≥ h(x,y)} L^{-sm}`;
3. for the block `B = block n z` of level `n`, the union `η_B` of the layers of the blocks
   inside `B` (`blockConfig`) is bond percolation with kernel `J_n(x,y) = ∑_{m=h(x,y)}^n L^{-sm}`
   on the pairs of `B` (`truncatedKernel`), and `J_n = J_∞ - L^{-sn}/(L^s - 1)` there;
4. the graph induced by `ω` on `B` is `η_B` together with the layers of the strict ancestors
   of `B` (`ancestorConfig`), and the two are independent, the second being complete-graph
   percolation on `B` with probability `1 - exp(-β L^{-sn}/(L^s - 1))` (`ancestorKernel`);
5. for every realisation of the layers, the clusters of `0` in `η_{B_n}`, `B_n = block n 0`,
   increase with `n` to the cluster of `0` in `ω`. -/
@[tag "VI3Y"]
theorem law_fullConfig_and_blockConfig_and_iUnion_cluster (hL : 2 ≤ L) {α : ℝ} (hα : 0 < α)
    (β : ℝ≥0) :
    let s : ℝ := d + α
    let μ := Measure.infinitePi fun _ : ℕ × Sym2 (ℕ →₀ (Fin d → ZMod L)) => expMeasure 1
    μ.map (openCopies (L : ℝ) s β) = PercLib.Probability.prodBernoulli (layerProfile L s β) ∧
    μ.map (fun T => fullConfig (openCopies (L : ℝ) s β T)) =
      law (intensityProfile (exactKernel L s) β) ∧
    (∀ e : Sym2 (ℕ →₀ (Fin d → ZMod L)), ¬ e.IsDiag →
      (exactKernel L s e : ℝ) = ∑' m : ℕ, if pairLevel e ≤ m then (L : ℝ) ^ (-(s * m)) else 0) ∧
    (∀ (n : ℕ) (z : ℕ →₀ (Fin d → ZMod L)),
      μ.map (fun T => blockConfig n z (openCopies (L : ℝ) s β T)) =
        law (intensityProfile (truncatedKernel L s n z) β)) ∧
    (∀ (n : ℕ) (z x y : ℕ →₀ (Fin d → ZMod L)), x ∈ block n z → y ∈ block n z → x ≠ y →
      (truncatedKernel L s n z s(x, y) : ℝ) =
        exactKernel L s s(x, y) - (L : ℝ) ^ (-(s * n)) / ((L : ℝ) ^ s - 1)) ∧
    (∀ (n : ℕ) (z : ℕ →₀ (Fin d → ZMod L)) (ξ : Set (ℕ × Sym2 (ℕ →₀ (Fin d → ZMod L)))),
      fullConfig ξ ∩ {e | ∀ v ∈ e, v ∈ block n z} = blockConfig n z ξ ∪ ancestorConfig n z ξ) ∧
    (∀ (n : ℕ) (z : ℕ →₀ (Fin d → ZMod L)),
      μ.map (fun T => (blockConfig n z (openCopies (L : ℝ) s β T),
          ancestorConfig n z (openCopies (L : ℝ) s β T))) =
        (law (intensityProfile (truncatedKernel L s n z) β)).prod
          (law (intensityProfile (ancestorKernel L s n z) β))) ∧
    (∀ ξ : Set (ℕ × Sym2 (ℕ →₀ (Fin d → ZMod L))),
      Monotone (fun n => cluster (blockConfig n 0 ξ) 0) ∧
        ⋃ n, cluster (blockConfig n 0 ξ) 0 = cluster (fullConfig ξ) 0) := by
  intro s μ
  have : NeZero L := ⟨by omega⟩
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hs : 0 < s := by positivity
  exact ⟨infinitePi_map_openCopies (by positivity) β,
    infinitePi_map_fullConfig_openCopies hL1 hs β,
    fun e he => coe_exactKernel_eq_tsum hL1 hs he,
    fun n z => infinitePi_map_blockConfig_openCopies hL1 β n z,
    fun n z x y hx hy hxy => coe_truncatedKernel_eq_sub hL1 hs hx hy hxy,
    fun n z ξ => fullConfig_inter_eq_blockConfig_union_ancestorConfig n z ξ,
    fun n z => infinitePi_map_blockConfig_ancestorConfig_openCopies hL1 hs β n z,
    fun ξ => ⟨monotone_cluster_blockConfig 0 ξ, iUnion_cluster_blockConfig 0 ξ⟩⟩

end PercLib.Models.HierarchicalLayers
