/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.BoundarySusceptibility
public import PercLib.Percolation.Bond.SusceptibilityDerivative
public import PercLib.Percolation.Bond.SusceptibilityEndpoint

/-! Correspondence wrappers for deleted-set connection loss, the boundary susceptibility
bound, and the susceptibility derivative in a transitive intensity model.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Deleting a deterministic vertex set `S` can only lose connections, and the loss is at
most `∑_{c ∈ S} τ(y,c) τ(c,w)`. -/
@[tag "7902"]
theorem tau_deleted_loss [Countable V] (q : Sym2 V → unitInterval) (S : Set V) (y w : V) :
    law q (localConn Sᶜ y w) ≤ tau q y w ∧
    tau q y w ≤ law q (localConn Sᶜ y w) +
      ∑' c : S, tau q y c * tau q c w :=
  ⟨law_deleted_le_tau q S y w, tau_le_deleted_add q S y w⟩

open Classical in
/-- The boundary susceptibility lower bound with positive part, and, when the
susceptibility does not depend on the root, the identification of the expression inside the
positive part with `L(S)`. -/
@[tag "67GX"]
theorem boundary_susceptibility_bound_positive_part [Countable V] (J : Sym2 V → ℝ≥0)
    (β : ℝ≥0) (S : Finset V)
    (hJ : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (hχ : (⨆ u, chi (intensityProfile J β) u) ≠ ⊤) :
    (∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau (intensityProfile J β) u w).toReal) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) ≤
      boundarySusceptibility J β S ∧
    (max ((⨅ u, chi (intensityProfile J β) u).toReal * S.card -
          ∑ u ∈ S, ∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) 0) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) ≤
      (∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau (intensityProfile J β) u w).toReal) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) ∧
    ((∀ u v, chi (intensityProfile J β) u = chi (intensityProfile J β) v) →
      (⨅ u, chi (intensityProfile J β) u).toReal * S.card -
          ∑ u ∈ S, ∑ v ∈ S, (tau (intensityProfile J β) u v).toReal =
        ∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau (intensityProfile J β) u w).toReal) := by
  obtain ⟨h1, h2⟩ := boundary_susceptibility_bound J β S hJ hχ
  refine ⟨h1, h2, fun hconst => ?_⟩
  set q := intensityProfile J β with hq
  have hfin : ∀ u, chi q u ≠ ⊤ := fun u => ne_top_of_le_ne_top hχ (le_iSup (chi q) u)
  have hinf : ∀ u, (⨅ v, chi q v) = chi q u := by
    intro u
    have : Nonempty V := ⟨u⟩
    rw [show (fun v => chi q v) = fun _ => chi q u from funext fun v => hconst v u]
    exact iInf_const
  have hsum : ∑ u ∈ S, (chi q u).toReal = (⨅ v, chi q v).toReal * S.card := by
    rw [Finset.sum_congr rfl (fun u _ => congrArg ENNReal.toReal (hinf u).symm),
      Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [← hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [toReal_chi_eq_add S q u (hfin u)]
  ring

/-- In a transitive intensity model with finite off-diagonal row sum `R` and susceptibility
finite on `(a,b)`, `0 ≤ a`: the susceptibility is locally Lipschitz on `(a,b)`, almost
every `β ∈ (a,b)` has a derivative in `[0, R χ(β)²]`, and if `R > 0` and `χ(b) = ∞` then
`χ(β) ≥ 1/(R(b-β))` on `(a,b)`. -/
@[tag "MXGM"]
theorem susceptibility_derivative_blowup [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) (o : V)
    (hR : rowSum (fun e => (J e : ℝ≥0∞)) o ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a)
    (hfin : ∀ β ∈ Ioo a b, chi (intensityProfile J β.toNNReal) o ≠ ⊤) :
    LocallyLipschitzOn (Ioo a b) (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) ∧
    (∀ᵐ β, β ∈ Ioo a b → ∃ D,
      HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) D β ∧ 0 ≤ D ∧
      D ≤ (rowSum (fun e => (J e : ℝ≥0∞)) o).toReal *
        (chi (intensityProfile J β.toNNReal) o).toReal ^ 2) ∧
    (0 < rowSum (fun e => (J e : ℝ≥0∞)) o →
      chi (intensityProfile J b.toNNReal) o = ⊤ → ∀ β ∈ Ioo a b,
        1 / ((rowSum (fun e => (J e : ℝ≥0∞)) o).toReal * (b - β)) ≤
          (chi (intensityProfile J β.toNNReal) o).toReal) := by
  refine ⟨PercLib.Models.NormalizedSmallIntensity.locallyLipschitzOn_chi J hJ o hR ha hfin, ?_,
    fun hR0 hb β hβ => one_div_le_chi_of_chi_eq_top J hJ o hR hR0 ha hfin hb hβ⟩
  · filter_upwards [ae_differentiableAt_chi J hJ o hR ha hfin] with β hβ hmem
    have hd := (hβ hmem).hasDerivAt
    exact ⟨_, hd, hasDerivAt_chi_mem_Icc J hJ o hR ha hfin hmem hd⟩

end PercLib.Percolation.Bond
