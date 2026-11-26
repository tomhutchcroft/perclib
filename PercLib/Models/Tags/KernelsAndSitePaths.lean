/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the displacement-kernels and site-percolation articles.
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.NonSummable
public import PercLib.Models.Site.SelfAvoiding

/-!
# Displacement kernels on groups and site path bounds: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `exists_sym2_kernel_mul_iff_and_translation_invariance`: on a group, `J s(x, y) = k (y * x⁻¹)`
  is well defined on unordered pairs iff `k` is inversion-even; it is then right-invariant,
  and left-invariant iff `k` is conjugation invariant.
* `cluster_infinite_and_criticalIntensity_eq_zero_of_mulTranslationInvariant`: a non-summable
  displacement kernel gives infinite degree and an infinite cluster at every vertex almost
  surely at each positive intensity, zero rooted and global thresholds, and singleton
  clusters at intensity zero.
* `siteBernoulli_exists_path_length_le_chain`: the site path chain
  `P_w(E_n(x)) ≤ ∑_γ ∏_{v ∈ γ} w_v ≤ w_x Δ b^(n-1) p^n ≤ Δ b^(n-1) p^(n+1)` and the
  length-`(n+1)` form.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-- On a countable group `G`, written multiplicatively, let `k : G → [0, ∞)` be a finite
nonnegative kernel. The prescription `J(x, y) = k (y x⁻¹)` defines a function on unordered
pairs, repeated pairs included, if and only if `k (z⁻¹) = k z` for every `z`. When it does,
`J` is invariant under simultaneous right translation, and it is invariant under all
simultaneous left translations if and only if `k (g z g⁻¹) = k z` for all `g, z`. -/
@[tag "U8CI"]
theorem exists_sym2_kernel_mul_iff_and_translation_invariance {G : Type*} [Group G]
    [Countable G] (k : G → ℝ≥0) :
    ((∃ J : Sym2 G → ℝ≥0, ∀ x y, J s(x, y) = k (y * x⁻¹)) ↔ ∀ z, k z⁻¹ = k z) ∧
      ∀ J : Sym2 G → ℝ≥0, (∀ x y, J s(x, y) = k (y * x⁻¹)) →
        (∀ g x y, J s(x * g, y * g) = J s(x, y)) ∧
        ((∀ g x y, J s(g * x, g * y) = J s(x, y)) ↔ ∀ g z, k (g * z * g⁻¹) = k z) :=
  ⟨exists_sym2_kernel_mul_iff k, fun _ hJ =>
    ⟨apply_mk_mul_right_of_mulTranslationInvariant hJ,
      forall_apply_mk_mul_left_iff_of_mulTranslationInvariant hJ⟩⟩

open Classical in
/-- On a countable group `G`, written multiplicatively, let `k : G → [0, ∞)` be a finite
nonnegative kernel with `∑_{z ≠ e} k z = ∞`, and let `J s(x, y) = k (y x⁻¹)` be its pair
intensity (so `k` is inversion-even, `inv_eq_of_mulTranslationInvariant`). For each `β > 0`,
under independent bonds whose non-diagonal probabilities are `1 - e^{-β k (y x⁻¹)}` and whose
diagonal probabilities are arbitrary, almost surely every vertex has infinitely many open
neighbours, and hence an infinite cluster. All rooted critical intensities and the global
critical intensity are zero. At `β = 0`, whatever the diagonal probabilities, almost surely
the open graph has no edges and every cluster is a singleton. -/
@[tag "K38T"]
theorem cluster_infinite_and_criticalIntensity_eq_zero_of_mulTranslationInvariant
    {G : Type*} [Group G] [Countable G] (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y * x⁻¹))
    (hk : (∑' z, if z = 1 then 0 else (k z : ℝ≥0∞)) = ∞) :
    (∀ β : ℝ≥0, 0 < β → ∀ q : Sym2 G → unitInterval,
        (∀ x y, x ≠ y → q s(x, y) = intensityProfile J β s(x, y)) →
        ∀ᵐ ω ∂law q, ∀ v, ((openGraph ω).neighborSet v).Infinite) ∧
      (∀ β : ℝ≥0, 0 < β → ∀ q : Sym2 G → unitInterval,
        (∀ x y, x ≠ y → q s(x, y) = intensityProfile J β s(x, y)) →
        ∀ᵐ ω ∂law q, ∀ v, (cluster ω v).Infinite) ∧
      (∀ v, rootCriticalIntensity J v = 0) ∧
      globalCriticalIntensity J = 0 ∧
      (∀ q : Sym2 G → unitInterval,
        (∀ x y, x ≠ y → q s(x, y) = intensityProfile J 0 s(x, y)) →
        ∀ᵐ ω ∂law q, openGraph ω = ⊥) ∧
      (∀ q : Sym2 G → unitInterval,
        (∀ x y, x ≠ y → q s(x, y) = intensityProfile J 0 s(x, y)) →
        ∀ᵐ ω ∂law q, ∀ v, cluster ω v = {v}) :=
  ⟨fun _ hβ q hq => ae_forall_neighborSet_infinite_of_mulTranslationInvariant J k hJ hk hβ q hq,
    fun _ hβ q hq => ae_forall_cluster_infinite_of_mulTranslationInvariant J k hJ hk hβ q hq,
    rootCriticalIntensity_eq_zero_of_mulTranslationInvariant J k hJ hk,
    globalCriticalIntensity_eq_zero_of_mulTranslationInvariant J k hJ hk,
    ae_openGraph_eq_bot_of_intensity_zero J,
    ae_cluster_eq_singleton_of_intensity_zero J⟩

end PercLib.Models

namespace PercLib.Models.Site

variable {V : Type*}

open Classical in
/-- Let `G` be a simple graph, on an arbitrary vertex type, of maximum degree at most
`Δ ∈ ℕ`, and write `b = Δ - 1` (truncated at zero). Let vertices be open independently with
probabilities `0 ≤ w_v ≤ p ≤ 1`, and let `E_n(x)` be the event that some simple path of `n`
edges from `x` has all its vertices open. For every `n ≥ 1`,
`P_w(E_n(x)) ≤ ∑_{γ ∈ 𝒫_n(x)} ∏_{v ∈ γ} w_v ≤ w_x Δ b^(n-1) p^n ≤ Δ b^(n-1) p^(n+1)`;
in particular, for every `n ≥ 0`, `P_w(E_{n+1}(x)) ≤ Δ b^n p^(n+2)`. -/
@[tag "5U4L"]
theorem siteBernoulli_exists_path_length_le_chain (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (w : V → unitInterval) (p : unitInterval)
    (hw : ∀ v, w v ≤ p) (x : V) :
    (∀ n : ℕ, 1 ≤ n →
      siteBernoulli w {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n ∧
          ∀ z ∈ r.1.support, z ∈ ω} ≤
        ∑' r : {r : Σ y, G.Path x y // r.2.1.length = n},
          ∏ z ∈ r.1.2.1.support.toFinset, (unitInterval.toNNReal (w z) : ℝ≥0∞) ∧
      ∑' r : {r : Σ y, G.Path x y // r.2.1.length = n},
          ∏ z ∈ r.1.2.1.support.toFinset, (unitInterval.toNNReal (w z) : ℝ≥0∞) ≤
        (unitInterval.toNNReal (w x) : ℝ≥0∞) * (Δ * (Δ - 1) ^ (n - 1) : ℕ) *
          (unitInterval.toNNReal p : ℝ≥0∞) ^ n ∧
      (unitInterval.toNNReal (w x) : ℝ≥0∞) * (Δ * (Δ - 1) ^ (n - 1) : ℕ) *
          (unitInterval.toNNReal p : ℝ≥0∞) ^ n ≤
        (Δ * (Δ - 1) ^ (n - 1) : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1)) ∧
    ∀ n : ℕ,
      siteBernoulli w {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n + 1 ∧
          ∀ z ∈ r.1.support, z ∈ ω} ≤
        (Δ * (Δ - 1) ^ n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 2) :=
  ⟨fun _ hn => ⟨siteBernoulli_exists_path_length_le_tsum_prod G hΔ w x hn,
      tsum_prod_support_le G hΔ w p hw x hn, coe_toNNReal_mul_mul_pow_le w p hw x _ _⟩,
    siteBernoulli_exists_path_length_le G hΔ w p hw x⟩

end PercLib.Models.Site
