/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.SelfAvoiding
public import PercLib.Percolation.Bond.ThetaSemicontinuity
public import PercLib.Models.Tree

/-!
# Restricted and intersection susceptibilities

For a vertex set `Λ`, the restricted susceptibility `χ^Λ_q(v) = E_q |K^Λ_v|` is the expected
size of the cluster of `v` inside `Λ` (open paths with every vertex in `Λ`), and the
intersection susceptibility `χ̃^Λ_q(v) = E_q |K_v ∩ Λ|` counts the vertices of `Λ` in the full
cluster. Always `χ^Λ ≤ χ̃^Λ ≤ χ`, both equal `χ` for `Λ = univ`, and on the path `0 – 1 – 2`
with both bonds open almost surely and `Λ = {0, 2}` the first inequality is strict.

## Main definitions

* `PercLib.Percolation.Bond.restrictedChi`: `χ^Λ_q(v)`.
* `PercLib.Percolation.Bond.interChi`: `χ̃^Λ_q(v)`.

## Main results

* `restrictedChi_le_interChi`, `interChi_le_chi`, `restrictedChi_univ`, `interChi_univ`
* `ae_openGraph_eq_of_indicator`: with probability one on the edges of `G` and zero
  elsewhere, the open graph is `G` almost surely.
* `restrictedChi_lt_interChi_fin_three`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The restricted susceptibility `χ^Λ_q(v) = E_q |K^Λ_v|`: the expected number of vertices
joined to `v` by open paths with every vertex in `Λ`. -/
def restrictedChi (q : Sym2 V → unitInterval) (Λ : Set V) (v : V) : ℝ≥0∞ :=
  ∫⁻ ω, ((localCluster ω Λ v).encard : ℝ≥0∞) ∂law q

/-- The intersection susceptibility `χ̃^Λ_q(v) = E_q |K_v ∩ Λ|`. -/
def interChi (q : Sym2 V → unitInterval) (Λ : Set V) (v : V) : ℝ≥0∞ :=
  ∫⁻ ω, ((cluster ω v ∩ Λ).encard : ℝ≥0∞) ∂law q

theorem restrictedChi_def (q : Sym2 V → unitInterval) (Λ : Set V) (v : V) :
    restrictedChi q Λ v = ∫⁻ ω, ((localCluster ω Λ v).encard : ℝ≥0∞) ∂law q :=
  rfl

theorem interChi_def (q : Sym2 V → unitInterval) (Λ : Set V) (v : V) :
    interChi q Λ v = ∫⁻ ω, ((cluster ω v ∩ Λ).encard : ℝ≥0∞) ∂law q :=
  rfl

/-- `χ^Λ ≤ χ̃^Λ`, since `K^Λ_v ⊆ K_v ∩ Λ`. -/
theorem restrictedChi_le_interChi (q : Sym2 V → unitInterval) (Λ : Set V) (v : V) :
    restrictedChi q Λ v ≤ interChi q Λ v :=
  lintegral_mono fun ω => ENat.toENNReal_le.2 (Set.encard_le_encard (localCluster_subset ω Λ v))

/-- `χ̃^Λ ≤ χ`. -/
theorem interChi_le_chi (q : Sym2 V → unitInterval) (Λ : Set V) (v : V) :
    interChi q Λ v ≤ chi q v :=
  lintegral_mono fun _ => ENat.toENNReal_le.2 (Set.encard_le_encard Set.inter_subset_left)

@[simp]
theorem interChi_univ (q : Sym2 V → unitInterval) (v : V) : interChi q univ v = chi q v := by
  simp [interChi, chi]

@[simp]
theorem restrictedChi_univ (q : Sym2 V → unitInterval) (v : V) :
    restrictedChi q univ v = chi q v := by
  simp [restrictedChi, chi, localCluster_univ]

/-- The restricted cluster depends on the configuration only through its open graph. -/
theorem localCluster_eq_of_openGraph_eq {ω ω' : Config V} (h : openGraph ω = openGraph ω')
    (S : Set V) (x : V) : localCluster ω S x = localCluster ω' S x := by
  ext y
  simp only [mem_localCluster, localConn, mem_ofPred_eq, h]

/-- The cluster depends on the configuration only through its open graph. -/
theorem cluster_eq_of_openGraph_eq {ω ω' : Config V} (h : openGraph ω = openGraph ω')
    (x : V) : cluster ω x = cluster ω' x := by
  simp only [cluster, h]

open Classical in
/-- With open probability one on the edges of `G` and zero on every other pair, the open
graph is `G` almost surely. -/
theorem ae_openGraph_eq_of_indicator [Countable V] (G : SimpleGraph V) :
    ∀ᵐ ω ∂law (fun e => if e ∈ G.edgeSet then (1 : unitInterval) else 0), openGraph ω = G := by
  filter_upwards [PercLib.Models.ae_edgeSet_subset_of_forall_eq_one G _
      fun e he => ite_eq_left he,
    ae_open_offDiag_mem_edgeSet G (q := fun e => if e ∈ G.edgeSet then (1 : unitInterval) else 0)
      fun e he _ => ite_eq_right he] with ω h1 h2
  ext x y
  rw [openGraph_adj_iff]
  constructor
  · rintro ⟨hω, hxy⟩
    exact h2 _ hω (Sym2.mk_isDiag_iff.not.2 hxy)
  · intro hG
    exact ⟨h1 hG, hG.ne⟩

open Classical in
/-- **The two finite-region susceptibilities differ.** On `Fin 3`, with the bonds `{0, 1}` and
`{1, 2}` open almost surely and every other pair closed, and `Λ = {0, 2}`, the middle vertex
lies outside `Λ`, so `χ^Λ(0) < χ̃^Λ(0)`. -/
theorem restrictedChi_lt_interChi_fin_three :
    restrictedChi (fun e => if e ∈ (openGraph ({s(0, 1), s(1, 2)} : Config (Fin 3))).edgeSet
        then (1 : unitInterval) else 0) {0, 2} 0 <
      interChi (fun e => if e ∈ (openGraph ({s(0, 1), s(1, 2)} : Config (Fin 3))).edgeSet
        then (1 : unitInterval) else 0) {0, 2} 0 := by
  set ω₀ : Config (Fin 3) := {s(0, 1), s(1, 2)}
  have hae := ae_openGraph_eq_of_indicator (openGraph ω₀)
  have hr : restrictedChi (fun e => if e ∈ (openGraph ω₀).edgeSet then (1 : unitInterval) else 0)
      {0, 2} 0 = ((localCluster ω₀ {0, 2} 0).encard : ℝ≥0∞) := by
    rw [restrictedChi, lintegral_congr_ae (g := fun _ => ((localCluster ω₀ {0, 2} 0).encard :
      ℝ≥0∞)) (hae.mono fun ω h => by rw [localCluster_eq_of_openGraph_eq h]),
      lintegral_const, measure_univ, mul_one]
  have hi : interChi (fun e => if e ∈ (openGraph ω₀).edgeSet then (1 : unitInterval) else 0)
      {0, 2} 0 = ((cluster ω₀ 0 ∩ {0, 2}).encard : ℝ≥0∞) := by
    rw [interChi, lintegral_congr_ae (g := fun _ => ((cluster ω₀ 0 ∩ {0, 2}).encard :
      ℝ≥0∞)) (hae.mono fun ω h => by rw [cluster_eq_of_openGraph_eq h]),
      lintegral_const, measure_univ, mul_one]
  rw [hr, hi]
  exact ENat.toENNReal_lt.2
    ((Set.toFinite _).encard_lt_encard localCluster_ssubset_cluster_inter_fin_three)

end PercLib.Percolation.Bond
