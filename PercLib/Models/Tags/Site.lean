/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the site-percolation article.
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.Site.Harris
public import PercLib.Models.Site.SelfAvoiding

/-!
# Site percolation: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `siteBernoulli_siteConn_basic`
* `siteEvents_measurable_upper`
* `siteBernoulli_harris_four`
* `site_monotonicity`
* `siteInfinite_eq_zero_of_degree_le_all`
* `thetaSite_eq_zero_and_inv_le_criticalProbSite`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Models.Site

variable {V : Type*}

/-- Site connection probabilities: `τ_s(x,x) = w_x`; `τ_s(x,y) ≤ w_x w_y` for `x ≠ y`; and
equality for adjacent `x, y`. -/
@[tag "9R9K"]
theorem siteBernoulli_siteConn_basic (G : SimpleGraph V) (w : V → unitInterval) :
    (∀ x, siteBernoulli w (siteConn G x x) = (unitInterval.toNNReal (w x) : ℝ≥0∞)) ∧
    (∀ x y, x ≠ y → siteBernoulli w (siteConn G x y) ≤
      (unitInterval.toNNReal (w x) : ℝ≥0∞) * (unitInterval.toNNReal (w y) : ℝ≥0∞)) ∧
    (∀ x y, G.Adj x y → siteBernoulli w (siteConn G x y) =
      (unitInterval.toNNReal (w x) : ℝ≥0∞) * (unitInterval.toNNReal (w y) : ℝ≥0∞)) :=
  ⟨siteBernoulli_siteConn_self G w, fun _ _ hxy => siteBernoulli_siteConn_le_mul_of_ne G w hxy,
    fun _ _ h => siteBernoulli_siteConn_of_adj G w h⟩

/-- On a countable vertex set, connection and infinite-cluster events are measurable and
increasing, and for any increasing finite exhaustion `F n ↑ V` the infinite-cluster event is
`⋂ n, ⋃ y ∉ F n, {x ↔ₛ y}`. -/
@[tag "3YMY"]
theorem siteEvents_measurable_upper [Countable V] (G : SimpleGraph V) :
    (∀ x y, MeasurableSet (siteConn G x y) ∧ IsUpperSet (siteConn G x y)) ∧
    (∀ x, MeasurableSet {ω : SiteConfig V | (siteCluster G ω x).Infinite} ∧
      IsUpperSet {ω : SiteConfig V | (siteCluster G ω x).Infinite}) ∧
    (∀ (x : V) (F : ℕ → Finset V), Monotone F → (∀ v, ∃ n, v ∈ F n) →
      {ω : SiteConfig V | (siteCluster G ω x).Infinite} =
        ⋂ n, ⋃ y ∈ ((F n : Set V))ᶜ, siteConn G x y) :=
  ⟨fun x y => ⟨measurableSet_siteConn G x y, isUpperSet_siteConn G x y⟩,
    fun x => ⟨measurableSet_siteInfinite G x, isUpperSet_siteInfinite G x⟩,
    siteInfinite_eq_iInter_of_monotone G⟩

/-- Harris inequality for site percolation on a countable vertex set: for connection events
and infinite-cluster events, and the two consequences `τ_s(x,y) τ_s(y,z) ≤ τ_s(x,z)` and
`τ_s(x,y) θ_s(x) ≤ θ_s(y)`. -/
@[tag "AR5B"]
theorem siteBernoulli_harris_four [Countable V] (G : SimpleGraph V) (w : V → unitInterval) :
    (∀ x y u v, siteBernoulli w (siteConn G x y) * siteBernoulli w (siteConn G u v) ≤
      siteBernoulli w (siteConn G x y ∩ siteConn G u v)) ∧
    (∀ x y, siteBernoulli w {ω | (siteCluster G ω x).Infinite} *
      siteBernoulli w {ω | (siteCluster G ω y).Infinite} ≤
      siteBernoulli w {ω | (siteCluster G ω x).Infinite ∧ (siteCluster G ω y).Infinite}) ∧
    (∀ x y z, siteBernoulli w (siteConn G x y) * siteBernoulli w (siteConn G y z) ≤
      siteBernoulli w (siteConn G x z)) ∧
    (∀ x y, siteBernoulli w (siteConn G x y) *
      siteBernoulli w {ω | (siteCluster G ω x).Infinite} ≤
      siteBernoulli w {ω | (siteCluster G ω y).Infinite}) :=
  ⟨siteBernoulli_harris_siteConn G w, siteBernoulli_harris_siteInfinite G w,
    siteBernoulli_siteConn_mul_le G w, siteBernoulli_siteConn_mul_infinite_le G w⟩

/-- Monotonicity in site percolation on a countable vertex set: increasing measurable events
are monotone in the profile, the homogeneous `θ` at any root is nondecreasing, and on `ℤ^d`
`θ_s(p) = 0` below `p_c^s` and `θ_s(p) > 0` above it. -/
@[tag "M28D"]
theorem site_monotonicity (V : Type*) [Countable V] :
    (∀ (w w' : V → unitInterval), w ≤ w' → ∀ A : Set (SiteConfig V), MeasurableSet A →
      IsUpperSet A → siteBernoulli w A ≤ siteBernoulli w' A) ∧
    (∀ (G : SimpleGraph V) (x : V), Monotone (thetaSiteOn G x)) ∧
    (∀ (d : ℕ) (p : unitInterval), (p : ℝ) < criticalProbSite d → thetaSite d p = 0) ∧
    (∀ (d : ℕ) (p : unitInterval), criticalProbSite d < (p : ℝ) → 0 < thetaSite d p) :=
  ⟨fun w w' h _ hA hup => siteBernoulli_mono_event w w' h hA hup, monotone_thetaSiteOn,
    thetaSite_eq_zero_of_lt_critical, thetaSite_pos_of_critical_lt⟩

/-- Degree criterion: on a graph of maximum degree at most `Δ`, with `w_v ≤ p`, if
`max(Δ-1,0) p < 1` then every fixed site cluster is a.s. finite (in the `ℕ`-subtraction and
real forms), and on a countable vertex set all site clusters are a.s. finite. -/
@[tag "3HEP"]
theorem siteInfinite_eq_zero_of_degree_le_all (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (w : V → unitInterval) (p : unitInterval)
    (hw : ∀ v, w v ≤ p) :
    ((((Δ - 1 : ℕ) : ℝ≥0∞) * unitInterval.toNNReal p < 1) →
      ∀ x, siteBernoulli w {ω | (siteCluster G ω x).Infinite} = 0) ∧
    ((((Δ : ℝ) - 1) * (p : ℝ) < 1) →
      ∀ x, siteBernoulli w {ω | (siteCluster G ω x).Infinite} = 0) ∧
    (∀ [Countable V], (((Δ : ℝ) - 1) * (p : ℝ) < 1) →
      ∀ᵐ ω ∂siteBernoulli w, ∀ x, (siteCluster G ω x).Finite) :=
  ⟨fun hp x => siteBernoulli_siteInfinite_eq_zero_of_degree_le_ennreal G hΔ w p hw hp x,
    fun hp x => siteBernoulli_siteInfinite_eq_zero_of_degree_le G hΔ w p hw hp x,
    fun hp => ae_all_siteClusters_finite_of_degree_le G hΔ w p hw hp⟩

/-- On `ℤ^d` with `d ≥ 1`, `θ_s(p) = 0` for `p < 1/(2d-1)`, and `p_c^s ≥ 1/(2d-1)`. -/
@[tag "MIUX"]
theorem thetaSite_eq_zero_and_inv_le_criticalProbSite :
    ∀ d : ℕ, 1 ≤ d →
      (∀ p : unitInterval, (p : ℝ) < 1 / (2 * (d : ℝ) - 1) → thetaSite d p = 0) ∧
      1 / (2 * (d : ℝ) - 1) ≤ criticalProbSite d :=
  fun _ hd => ⟨fun p hp => thetaSite_eq_zero_of_lt_inv hd p hp, inv_le_criticalProbSite hd⟩

end PercLib.Models.Site
