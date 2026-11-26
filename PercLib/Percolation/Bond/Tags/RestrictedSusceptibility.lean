/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for restricted and intersection susceptibilities.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.RestrictedSusceptibility

/-!
# Restricted and intersection susceptibilities: correspondence

## Main results

* `restrictedChi_interChi_def_and_lt_example`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

open Classical in
/-- For a region `Λ` and a vertex `v`, `χ^Λ_q(v) = E_q |K^Λ_v|` and
`χ̃^Λ_q(v) = E_q |K_v ∩ Λ|`; always `χ^Λ_q(v) ≤ χ̃^Λ_q(v)`, and they differ on the
three-vertex path `0 – 1 – 2` (both bonds open almost surely) with `Λ = {0, 2}`, whose middle
vertex lies outside the region. -/
@[tag "BX1L"]
theorem restrictedChi_interChi_def_and_lt_example {V : Type*} :
    (∀ (q : Sym2 V → unitInterval) (Λ : Set V) (v : V),
      restrictedChi q Λ v = ∫⁻ ω, ((localCluster ω Λ v).encard : ℝ≥0∞) ∂law q) ∧
    (∀ (q : Sym2 V → unitInterval) (Λ : Set V) (v : V),
      interChi q Λ v = ∫⁻ ω, ((cluster ω v ∩ Λ).encard : ℝ≥0∞) ∂law q) ∧
    (∀ (q : Sym2 V → unitInterval) (Λ : Set V) (v : V),
      restrictedChi q Λ v ≤ interChi q Λ v) ∧
    restrictedChi (fun e => if e ∈ (openGraph ({s(0, 1), s(1, 2)} : Config (Fin 3))).edgeSet
        then (1 : unitInterval) else 0) {0, 2} 0 <
      interChi (fun e => if e ∈ (openGraph ({s(0, 1), s(1, 2)} : Config (Fin 3))).edgeSet
        then (1 : unitInterval) else 0) {0, 2} 0 :=
  ⟨restrictedChi_def, interChi_def, restrictedChi_le_interChi,
    restrictedChi_lt_interChi_fin_three⟩

end PercLib.Percolation.Bond
