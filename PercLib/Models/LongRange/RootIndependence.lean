/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Discharge of the premise `hG` that the formalisation of contributor yujinhkim cited below adds to
Proposition I.3.1 of T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1. The
premise is read from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/VolumeTailAllN.lean`,
`PercLib/CriticalLRP/Analysis/VolumeTailUpper.lean` and
`PercLib/CriticalLRP/CountableProduct/GhostField.lean` (`ghostHits`, hypothesis `hG`); licence
Apache-2.0 as declared in those file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not
independently verified). Contributor: yujinhkim. No code is copied: the proofs are new, from the
transport lemmas of this library.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.IndependentLayer.Ghost

/-! # Root independence of cluster-volume functionals

The fork's premise `hG` asks that the probability that the cluster of `y` meets an
independent ghost field be at most that for the root `o`. On `main` this probability is
`∫⁻ (1 - e^{-h |K_y|}) d(law q)` (`lintegral_cluster_one_sub_exp_eq_prod`). Here:

* `lintegral_encard_cluster_eq_of_map_law_eq`: a law-preserving vertex bijection leaves
  every functional `∫⁻ F (|K_x|)` unchanged, for any `F : ℕ∞ → ℝ≥0∞` (no measurability);
* the transitive form (`…_of_transitive`, `…_intensity_of_transitive`) and the
  translation-invariant form on an additive group (`…_of_translationInvariant`);
* the radial and cut-off kernels on `ℤ^d` are translation invariant at every norm, profile,
  scale and intensity, so `hG` holds for both, with equality, at every scale
  (`ghost_hits_le_root_radialKernel`, `ghost_hits_le_root_cutoffKernel`).

No hypothesis beyond the paper's is needed: `hG` holds for the whole cut-off family.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal unitInterval
open PercLib.Percolation.Bond PercLib.Probability

namespace PercLib.Models.LongRange

/-! ### Transport of cluster-volume functionals -/

section General

variable {V : Type*}

/-- A law-preserving vertex bijection leaves every cluster-volume functional unchanged. -/
theorem lintegral_encard_cluster_eq_of_map_law_eq {q : Sym2 V → unitInterval} (φ : V ≃ V)
    (h : (law q).map (fun ω => Sym2.map φ '' ω) = law q) (F : ℕ∞ → ℝ≥0∞) (x : V) :
    ∫⁻ ω, F (cluster ω (φ x)).encard ∂(law q) = ∫⁻ ω, F (cluster ω x).encard ∂(law q) := by
  conv_lhs => rw [← h]
  rw [lintegral_map_image_sym2Map]
  simp_rw [encard_cluster_image]

/-- **Root independence under transitivity of the profile.** -/
theorem lintegral_encard_cluster_eq_of_transitive (q : Sym2 V → unitInterval)
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, q (Sym2.map φ e) = q e)
    (F : ℕ∞ → ℝ≥0∞) (x y : V) :
    ∫⁻ ω, F (cluster ω x).encard ∂(law q) = ∫⁻ ω, F (cluster ω y).encard ∂(law q) := by
  obtain ⟨φ, hφx, hφ⟩ := hT x y
  rw [← hφx]
  exact (lintegral_encard_cluster_eq_of_map_law_eq φ
    (prodBernoulli_map_image_sym2_invariant q φ hφ) F x).symm

/-- **Root independence under transitivity of the kernel**, at every intensity (item 4, in the
transitivity spelling of `chi_eq_of_transitive`). -/
theorem lintegral_encard_cluster_intensity_eq_of_transitive (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) (β : ℝ≥0)
    (F : ℕ∞ → ℝ≥0∞) (x y : V) :
    ∫⁻ ω, F (cluster ω x).encard ∂(law (intensityProfile J β)) =
      ∫⁻ ω, F (cluster ω y).encard ∂(law (intensityProfile J β)) := by
  obtain ⟨φ, hφx, hφ⟩ := hT x y
  rw [← hφx]
  exact (lintegral_encard_cluster_eq_of_map_law_eq φ
    (law_intensityProfile_map_eq J φ hφ β) F x).symm

end General

/-! ### Translation invariance on an additive group -/

section Group

variable {G : Type*} [AddGroup G]

/-- A translation-invariant profile is transitive: the translation by `y - x` carries `x`
to `y`. -/
theorem transitive_of_map_add_invariant {β : Type*} (q : Sym2 G → β)
    (hq : ∀ (a : G) e, q (Sym2.map (· + a) e) = q e) :
    ∀ x y : G, ∃ φ : G ≃ G, φ x = y ∧ ∀ e, q (Sym2.map φ e) = q e :=
  fun x y => ⟨Equiv.addRight (-x + y), by simp, fun e => hq _ e⟩

/-- **Item 1.** For a translation-invariant profile on an additive group,
`∫⁻ F (|K_x|) d(law q)` does not depend on `x`, for every `F : ℕ∞ → ℝ≥0∞`. -/
theorem lintegral_encard_cluster_eq_of_translationInvariant (q : Sym2 G → unitInterval)
    (hq : ∀ (a : G) e, q (Sym2.map (· + a) e) = q e) (F : ℕ∞ → ℝ≥0∞) (x y : G) :
    ∫⁻ ω, F (cluster ω x).encard ∂(law q) = ∫⁻ ω, F (cluster ω y).encard ∂(law q) :=
  lintegral_encard_cluster_eq_of_transitive q (transitive_of_map_add_invariant q hq) F x y

/-- **Item 2, Laplace form.** The ghost transform `∫⁻ (1 - e^{-h |K_y|})`
of a translation-invariant profile does not depend on the root. -/
theorem lintegral_one_sub_exp_cluster_eq_of_translationInvariant (q : Sym2 G → unitInterval)
    (hq : ∀ (a : G) e, q (Sym2.map (· + a) e) = q e) (h : ℝ) (x y : G) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω x).encard : ℝ≥0∞) : EReal))))
        ∂(law q) =
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω y).encard : ℝ≥0∞) : EReal))))
        ∂(law q) :=
  lintegral_encard_cluster_eq_of_translationInvariant q hq
    (fun n => 1 - EReal.exp (-((h : EReal) * ((n : ℝ≥0∞) : EReal)))) x y

/-- **Item 2, marked-vertex form, with equality.** For a translation-invariant
profile, the probability that the cluster of `y` contains a mark of an independent field of
intensity `1 - e^{-h}` is the same at every `y`. -/
theorem ghost_hits_eq_of_translationInvariant [Countable G] (q : Sym2 G → unitInterval)
    (hq : ∀ (a : G) e, q (Sym2.map (· + a) e) = q e) {h : ℝ} {p : I} (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) (x y : G) :
    ((law q).prod (prodBernoulli fun _ : G => p)) {z | (cluster z.1 x ∩ z.2).Nonempty} =
      ((law q).prod (prodBernoulli fun _ : G => p)) {z | (cluster z.1 y ∩ z.2).Nonempty} := by
  rw [← lintegral_cluster_one_sub_exp_eq_prod q x hh hp,
    ← lintegral_cluster_one_sub_exp_eq_prod q y hh hp]
  exact lintegral_one_sub_exp_cluster_eq_of_translationInvariant q hq h x y

/-- **Item 2, in the fork's form `hG`:** every root's ghost-hit probability is
at most the one at `o`. -/
theorem ghost_hits_le_root_of_translationInvariant [Countable G] (q : Sym2 G → unitInterval)
    (hq : ∀ (a : G) e, q (Sym2.map (· + a) e) = q e) {h : ℝ} {p : I} (hh : 0 < h)
    (hp : ((σ p : I) : ℝ) = Real.exp (-h)) (o y : G) :
    ((law q).prod (prodBernoulli fun _ : G => p)) {z | (cluster z.1 y ∩ z.2).Nonempty} ≤
      ((law q).prod (prodBernoulli fun _ : G => p)) {z | (cluster z.1 o ∩ z.2).Nonempty} :=
  (ghost_hits_eq_of_translationInvariant q hq hh hp y o).le

/-- An intensity profile of a translation-invariant kernel is translation invariant. -/
theorem intensityProfile_map_add {J : Sym2 G → ℝ≥0}
    (hJ : ∀ (a : G) e, J (Sym2.map (· + a) e) = J e) (β : ℝ≥0) (a : G) (e : Sym2 G) :
    intensityProfile J β (Sym2.map (· + a) e) = intensityProfile J β e :=
  Subtype.ext (by simp only [intensityProfile, hJ])

end Group

/-! ### The radial and cut-off kernels on `ℤ^d` (item 3) -/

section Lattice

variable {d : ℕ}

/-- The radial kernel is translation invariant, for every norm and profile. -/
theorem radialKernel_map_add (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (a : Fin d → ℤ)
    (e : Sym2 (Fin d → ℤ)) : radialKernel N K (Sym2.map (· + a) e) = radialKernel N K e := by
  induction e using Sym2.ind with
  | _ x y => simp only [Sym2.map_mk, radialKernel_mk, add_left_inj, add_sub_add_right_eq_sub]

/-- The cut-off kernel is translation invariant, at every scale. -/
theorem cutoffKernel_map_add (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (r : ℝ)
    (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    cutoffKernel N K r (Sym2.map (· + a) e) = cutoffKernel N K r e :=
  radialKernel_map_add N (cutoffProfile K r) a e

/-- **`hG` for the full law**, at every norm, profile and intensity. -/
theorem ghost_hits_le_root_radialKernel (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ)
    (β : ℝ≥0) {h : ℝ} {p : I} (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h))
    (o y : Fin d → ℤ) :
    ((law (intensityProfile (radialKernel N K) β)).prod
        (prodBernoulli fun _ : Fin d → ℤ => p)) {z | (cluster z.1 y ∩ z.2).Nonempty} ≤
      ((law (intensityProfile (radialKernel N K) β)).prod
        (prodBernoulli fun _ : Fin d → ℤ => p)) {z | (cluster z.1 o ∩ z.2).Nonempty} :=
  ghost_hits_le_root_of_translationInvariant _
    (intensityProfile_map_add (radialKernel_map_add N K) β) hh hp o y

/-- **`hG` for the cut-off law**, at every norm, profile, scale and intensity. -/
theorem ghost_hits_le_root_cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (r : ℝ)
    (β : ℝ≥0) {h : ℝ} {p : I} (hh : 0 < h) (hp : ((σ p : I) : ℝ) = Real.exp (-h))
    (o y : Fin d → ℤ) :
    ((law (intensityProfile (cutoffKernel N K r) β)).prod
        (prodBernoulli fun _ : Fin d → ℤ => p)) {z | (cluster z.1 y ∩ z.2).Nonempty} ≤
      ((law (intensityProfile (cutoffKernel N K r) β)).prod
        (prodBernoulli fun _ : Fin d → ℤ => p)) {z | (cluster z.1 o ∩ z.2).Nonempty} :=
  ghost_hits_le_root_of_translationInvariant _
    (intensityProfile_map_add (cutoffKernel_map_add N K r) β) hh hp o y

/-- Root independence of every cluster-volume functional for the cut-off law. -/
theorem lintegral_encard_cluster_cutoffKernel_eq (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ)
    (r : ℝ) (β : ℝ≥0) (F : ℕ∞ → ℝ≥0∞) (x y : Fin d → ℤ) :
    ∫⁻ ω, F (cluster ω x).encard ∂(law (intensityProfile (cutoffKernel N K r) β)) =
      ∫⁻ ω, F (cluster ω y).encard ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  lintegral_encard_cluster_eq_of_translationInvariant _
    (intensityProfile_map_add (cutoffKernel_map_add N K r) β) F x y

/-- Root independence of every cluster-volume functional for the full law. -/
theorem lintegral_encard_cluster_radialKernel_eq (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ)
    (β : ℝ≥0) (F : ℕ∞ → ℝ≥0∞) (x y : Fin d → ℤ) :
    ∫⁻ ω, F (cluster ω x).encard ∂(law (intensityProfile (radialKernel N K) β)) =
      ∫⁻ ω, F (cluster ω y).encard ∂(law (intensityProfile (radialKernel N K) β)) :=
  lintegral_encard_cluster_eq_of_translationInvariant _
    (intensityProfile_map_add (radialKernel_map_add N K) β) F x y

end Lattice

/-! ### Witnesses -/

/-- Item 3 at `d = 1`, `α = 1` (power law `s ↦ s^(-2)`), sup norm, `β = 1`, `r = 2`:
the cut-off law is translation invariant. -/
example (a : Fin 1 → ℤ) (e : Sym2 (Fin 1 → ℤ)) :
    intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2) 2) 1
        (Sym2.map (· + a) e) =
      intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2) 2) 1
        e :=
  intensityProfile_map_add (cutoffKernel_map_add _ _ _) 1 a e

/-- Item 2 at `h = 1`, for the same cut-off law: `hG` holds at the explicit mark
probability `p = 1 - e^{-1}`, for the roots `0` and `y`. -/
example (y : Fin 1 → ℤ) :
    ((law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (powerLawProfile 1 2) 2) 1)).prod
        (prodBernoulli fun _ : Fin 1 → ℤ =>
          σ ⟨Real.exp (-1), (Real.exp_pos _).le, Real.exp_le_one_iff.2 (by norm_num)⟩))
        {z | (cluster z.1 y ∩ z.2).Nonempty} ≤
      ((law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (powerLawProfile 1 2) 2) 1)).prod
        (prodBernoulli fun _ : Fin 1 → ℤ =>
          σ ⟨Real.exp (-1), (Real.exp_pos _).le, Real.exp_le_one_iff.2 (by norm_num)⟩))
        {z | (cluster z.1 0 ∩ z.2).Nonempty} :=
  ghost_hits_le_root_cutoffKernel _ _ _ _ one_pos (by rw [unitInterval.symm_symm]) 0 y

/-- Item 2 at `h = 1`, Laplace form, for the full power-law kernel. -/
example (y : Fin 1 → ℤ) :
    ∫⁻ ω, (1 - EReal.exp (-(((1 : ℝ) : EReal) * (((cluster ω y).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile (radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (powerLawProfile 1 2)) 1)) =
      ∫⁻ ω, (1 - EReal.exp (-(((1 : ℝ) : EReal) * (((cluster ω 0).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile (radialKernel (normSeminorm ℝ (Fin 1 → ℝ))
          (powerLawProfile 1 2)) 1)) :=
  lintegral_one_sub_exp_cluster_eq_of_translationInvariant _
    (intensityProfile_map_add (radialKernel_map_add _ _) 1) 1 y 0

end PercLib.Models.LongRange
