/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's theorems on translated hierarchical edge layers. No
upstream code is copied and no definition is added. Mathematical reference: T. Hutchcroft,
*Sharp hierarchical upper bounds on the critical two-point function for long-range
percolation on ℤ^d*, arXiv:2202.07634v2, Section 2, with the digit weight `L^{m-1}`.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalComparison

/-!
# Translated hierarchical edge layers and good blocks (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `DigitHierarchy.nested_and_law_eq_map_union_layerKernel`: the digit hierarchies on `ℤ^d`,
  their blocks and hierarchical layers, and the decomposition of the bond law.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal
open MeasureTheory PercLib.Percolation.Bond

namespace PercLib.Models.DigitHierarchy

variable {d L : ℕ} [NeZero L]

open Classical in
/-- **Translated hierarchical edge layers and good blocks.** Let `J` be a kernel on `ℤ^d` with
`J(x, y) ≥ c ‖x - y‖_∞^{-s}` for `x ≠ y`, where `s = d + α`, `α > 0`, and let `σ` be a digit
hierarchy with base `L` (offsets `t_n = ∑_{m < n} L^m σ_m`, level-`n` blocks
`t_n + L^n k + {0, …, L^n-1}^d`, `blockIndex n x = k`). Then:
the partitions are nested; the level-`n` block `σ.block n z` is the set of points with the
block index of `z`, and every level-`(n+1)` block has `Q = L^d` children; every translate of
the hierarchy is again a digit hierarchy; a level-`n` block has `ℓ^∞` diameter less than
`L^n`, so that `H_σ(x, y) = c L^{-s h_σ(x, y)}` (`σ.layerKernel c s`, with
`h_σ = σ.commonLevel`, `L^{-∞} = 0`) satisfies `H_σ ≤ J`; the layer `ω_B` of a level-`(m+1)`
block `B` (`σ.blockLayerKernel`) opens exactly the pairs of `B` in different children, at
intensity `c L^{-s(m+1)}`; the bond law of `J` is the union of independent configurations with
kernels `H_σ` and `R_σ = J - H_σ`; the restricted configuration `η_B`
(`σ.restrictedKernel J c s n z`, `J` minus the strict-ancestor layers) satisfies
`η_P = η_B ∪ ω_P` in law for the parent `P`, with `ω_P` independent; and siblings have the
same restricted configuration. The block quantities `E Z_B`, `M_B`, `S_B` at intensity `β` are
`σ.expectedBlockMax`, `σ.blockScale`, `σ.blockPairSum`, and good and ancestrally good blocks
are `σ.IsGoodBlock` and `σ.IsAncestrallyGood`. -/
@[tag "EKDO"]
theorem nested_and_law_eq_map_union_layerKernel {α : ℝ} (hα : 0 < α) (c : ℝ≥0)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y : Fin d → ℤ, x ≠ y → (c : ℝ) * ‖x - y‖ ^ (-((d : ℝ) + α)) ≤ J s(x, y))
    (σ : DigitHierarchy d L) :
    (∀ n (x y : Fin d → ℤ), σ.blockIndex n x = σ.blockIndex n y →
        σ.blockIndex (n + 1) x = σ.blockIndex (n + 1) y) ∧
      (∀ n (z x : Fin d → ℤ), x ∈ σ.block n z ↔ σ.blockIndex n x = σ.blockIndex n z) ∧
      (∀ n (z : Fin d → ℤ), ((σ.block (n + 1) z).image (σ.blockIndex n)).card = L ^ d) ∧
      (∀ x : Fin d → ℤ, ∃ τ : DigitHierarchy d L, ∀ n (u v : Fin d → ℤ),
        τ.blockIndex n (u + x) = τ.blockIndex n (v + x) ↔
          σ.blockIndex n u = σ.blockIndex n v) ∧
      (∀ n (x y : Fin d → ℤ), σ.blockIndex n x = σ.blockIndex n y → ‖x - y‖ < (L : ℝ) ^ n) ∧
      σ.layerKernel c ((d : ℝ) + α) ≤ J ∧
      (∀ x y : Fin d → ℤ, σ.layerKernel c ((d : ℝ) + α) s(x, y) =
        if x = y then 0 else layerWeight L c ((d : ℝ) + α) (σ.commonLevel x y)) ∧
      (∀ n (z x y : Fin d → ℤ), σ.restrictedKernel J c ((d : ℝ) + α) n z s(x, y) =
        J s(x, y) - if σ.InStrictAncestor n z x y then σ.layerKernel c ((d : ℝ) + α) s(x, y)
          else 0) ∧
      (∀ m (z x y : Fin d → ℤ), σ.blockLayerKernel c ((d : ℝ) + α) (m + 1) z s(x, y) =
        if x ∈ σ.block (m + 1) z ∧ y ∈ σ.block (m + 1) z ∧
            σ.blockIndex m x ≠ σ.blockIndex m y
        then c * (L : ℝ≥0) ^ (-(((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) else 0) ∧
      (∀ β : ℝ≥0, law (intensityProfile J β) =
        ((law (intensityProfile (σ.layerKernel c ((d : ℝ) + α)) β)).prod
          (law (intensityProfile (J - σ.layerKernel c ((d : ℝ) + α)) β))).map
            (fun ω => ω.1 ∪ ω.2)) ∧
      (∀ (β : ℝ≥0) n (z : Fin d → ℤ),
        law (intensityProfile (σ.restrictedKernel J c ((d : ℝ) + α) (n + 1) z) β) =
          ((law (intensityProfile (σ.restrictedKernel J c ((d : ℝ) + α) n z) β)).prod
            (law (intensityProfile (σ.blockLayerKernel c ((d : ℝ) + α) (n + 1) z) β))).map
              (fun ω => ω.1 ∪ ω.2)) ∧
      (∀ n (z z' : Fin d → ℤ), σ.blockIndex (n + 1) z = σ.blockIndex (n + 1) z' →
        σ.restrictedKernel J c ((d : ℝ) + α) n z =
          σ.restrictedKernel J c ((d : ℝ) + α) n z') := by
  have hHJ : σ.layerKernel c ((d : ℝ) + α) ≤ J :=
    σ.layerKernel_le (by positivity) hJ
  exact ⟨fun _ _ _ h => σ.blockIndex_succ_eq_of_eq h, fun _ _ _ => σ.mem_block,
    σ.card_image_blockIndex_block_succ, σ.exists_blockIndex_add_iff,
    fun _ _ _ h => σ.norm_sub_lt_of_blockIndex_eq h, hHJ, σ.layerKernel_apply c _,
    fun n z x y => by rw [σ.restrictedKernel_apply, σ.ancestorKernel_apply],
    σ.blockLayerKernel_succ_apply c _, σ.law_intensityProfile_eq_map_union_layerKernel hHJ,
    σ.law_restrictedKernel_succ hHJ,
    fun _ _ _ h => σ.restrictedKernel_eq_of_blockIndex_succ_eq J c _ h⟩

end PercLib.Models.DigitHierarchy
