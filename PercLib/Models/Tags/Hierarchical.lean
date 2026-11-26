/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the hierarchical-lattice and hierarchical-runaway articles.
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalGeometry
public import PercLib.Models.HierarchicalCutoff
public import PercLib.Models.HierarchicalTwoPoint
public import PercLib.Models.HierarchicalAmplificationStep

/-!
# The hierarchical lattice: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `hierarchical_level_properties`
* `hierarchical_ball_counts`
* `hierarchical_radial_sums`
* `hierarchical_geometricRadial_criterion`
* `hierarchical_cutoff`
* `hierarchical_subcritical`
* `hierarchical_two_point`
* `tightnessScale_hierarchical_amplification_offDiag`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-! ### Geometry -/

/-- For an abelian coefficient group `A`: the level is zero only at zero;
`ℓ(u+v) ≤ max`; displacement levels are symmetric, translation invariant and satisfy the strong
triangle inequality; each ball `B_n` is a subgroup, isomorphic to `A^n` by restriction; the
level-`n` balls are exactly the translates of `B_n`, and two of them coincide or are disjoint;
`B_{n+1}` is the disjoint union of the translates `e_n(a) + B_n`; balls are finite when `A` is
finite; and `B_1` is infinite when `A` is infinite. -/
@[tag "BW7V"]
theorem hierarchical_level_properties (A : Type*) [AddCommGroup A] :
    (∀ z : ℕ →₀ A, z.support.sup Nat.succ = 0 ↔ z = 0) ∧
    (∀ x y : ℕ →₀ A,
      (x + y).support.sup Nat.succ ≤ max (x.support.sup Nat.succ) (y.support.sup Nat.succ)) ∧
    (∀ x y : ℕ →₀ A, (y - x).support.sup Nat.succ = (x - y).support.sup Nat.succ) ∧
    (∀ x y g : ℕ →₀ A,
      ((y + g) - (x + g)).support.sup Nat.succ = (y - x).support.sup Nat.succ) ∧
    (∀ x y z : ℕ →₀ A, (z - x).support.sup Nat.succ ≤
      max ((y - x).support.sup Nat.succ) ((z - y).support.sup Nat.succ)) ∧
    (∀ n : ℕ, ∃ B : AddSubgroup (ℕ →₀ A), ∀ z, z ∈ B ↔ z.support.sup Nat.succ ≤ n) ∧
    (∀ n : ℕ, Function.Bijective (fun z : {z : ℕ →₀ A // z.support.sup Nat.succ ≤ n} =>
      fun i : Fin n => z.1 i)) ∧
    (∀ (x : ℕ →₀ A) (n : ℕ), {y | (y - x).support.sup Nat.succ ≤ n} =
      (fun z => x + z) '' {z | z.support.sup Nat.succ ≤ n}) ∧
    (∀ (x y : ℕ →₀ A) (n : ℕ),
      {z | (z - x).support.sup Nat.succ ≤ n} = {z | (z - y).support.sup Nat.succ ≤ n} ∨
      Disjoint {z | (z - x).support.sup Nat.succ ≤ n} {z | (z - y).support.sup Nat.succ ≤ n}) ∧
    (∀ n : ℕ, {z : ℕ →₀ A | z.support.sup Nat.succ ≤ n + 1} =
      ⋃ a : A, {z | (z - Finsupp.single n a).support.sup Nat.succ ≤ n}) ∧
    (∀ n : ℕ, Pairwise (fun a b : A => Disjoint
      {z : ℕ →₀ A | (z - Finsupp.single n a).support.sup Nat.succ ≤ n}
      {z : ℕ →₀ A | (z - Finsupp.single n b).support.sup Nat.succ ≤ n})) ∧
    (∀ [Finite A] (n : ℕ), {z : ℕ →₀ A | z.support.sup Nat.succ ≤ n}.Finite) ∧
    (∀ [Infinite A], {z : ℕ →₀ A | z.support.sup Nat.succ ≤ 1}.Infinite) :=
  ⟨level_eq_zero_iff, level_add_le_max, level_sub_comm, level_sub_add_right,
    level_sub_le_max, exists_addSubgroup_level_ball, level_ball_restrict_bijective,
    level_ball_eq_translate, level_balls_eq_or_disjoint, level_ball_succ_eq_iUnion,
    pairwise_disjoint_level_ball_succ, fun n => finite_level_ball n, infinite_level_ball_one⟩

variable {d L : ℕ}

/-- On `ℕ →₀ (Fin d → ZMod L)` (`L ≥ 1`), `|B_n| = N^n` and
`|{ℓ = n+1}| = N^{n+1} - N^n` with `N = L^d`; and any two blocks of levels `m ≤ n` are nested
or disjoint. -/
@[tag "9408"]
theorem hierarchical_ball_counts [NeZero L] :
    (∀ n : ℕ, Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ ≤ n} =
      (L ^ d) ^ n) ∧
    (∀ n : ℕ, Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n + 1} =
      (L ^ d) ^ (n + 1) - (L ^ d) ^ n) ∧
    (∀ (x y : ℕ →₀ (Fin d → ZMod L)) (m n : ℕ), m ≤ n →
      {z | (z - x).support.sup Nat.succ ≤ m} ⊆ {z | (z - y).support.sup Nat.succ ≤ n} ∨
      {z | (z - y).support.sup Nat.succ ≤ n} ⊆ {z | (z - x).support.sup Nat.succ ≤ m} ∨
      Disjoint {z | (z - x).support.sup Nat.succ ≤ m} {z | (z - y).support.sup Nat.succ ≤ n}) :=
  ⟨card_ball, card_shell_succ, fun x y _ _ hmn => level_balls_subset_or_disjoint_of_le x y hmn⟩

/-- Radial sums: `∑_x f(ℓ(x)) = f(0) + ∑_{n ≥ 1} (N^n - N^{n-1}) f(n) ≤ ∑_n N^n f(n)`;
for `k = C r^ℓ` with `N r < 1`, `∑_{x ≠ 0} k = C(N-1)r/(1-Nr)` and `∑_x k ≤ C/(1-Nr)`; and if
`2 N r ≤ 1` the total is at most `2C`. -/
@[tag "6KJQ"]
theorem hierarchical_radial_sums [NeZero L] :
    (∀ f : ℕ → ℝ≥0∞, (∑' z : ℕ →₀ (Fin d → ZMod L), f (z.support.sup Nat.succ)) =
      f 0 + ∑' n : ℕ, (((L ^ d) ^ (n + 1) - (L ^ d) ^ n : ℕ) : ℝ≥0∞) * f (n + 1)) ∧
    (∀ f : ℕ → ℝ≥0∞, ∑' z : ℕ →₀ (Fin d → ZMod L), f (z.support.sup Nat.succ) ≤
      ∑' n, (((L ^ d) ^ n : ℕ) : ℝ≥0∞) * f n) ∧
    (∀ C r : ℝ≥0, (L : ℝ≥0) ^ d * r < 1 →
      (∑' z : ℕ →₀ (Fin d → ZMod L),
          if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)) =
        (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) ∧
      ∑' z : ℕ →₀ (Fin d → ZMod L), ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞) ≤
        (C : ℝ≥0∞) / (1 - (L : ℝ≥0∞) ^ d * r)) ∧
    (∀ C r : ℝ≥0, (L : ℝ≥0) ^ d * r * 2 ≤ 1 →
      ∑' z : ℕ →₀ (Fin d → ZMod L), ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞) ≤
        ((2 * C : ℝ≥0) : ℝ≥0∞)) :=
  ⟨tsum_radial_eq, tsum_radial_le,
    fun C r _ => ⟨tsum_geometricRadial_mul_eq C r, tsum_radial_mul_le C r⟩,
    fun C r hr => tsum_geometricRadial_le C r hr⟩

/-- For `r ∈ [0, ∞]`, `S(r) = ∑_{z ≠ 0} r^{ℓ(z)} = (N-1) r ∑_n (Nr)^n`, with the
degenerate cases: `S = 0` if `N = 1` or `r = 0`; for `N > 1` and `0 < r < ∞`,
`S = (N-1)r/(1-Nr)` if `Nr < 1` and `S = ∞` if `Nr ≥ 1`; `S(∞) = ∞` for `N > 1`. And for
`L ≥ 2`, `d ≥ 1` and real `α`, `∑_{z ≠ 0} L^{-(d+α)ℓ(z)} < ∞ ↔ α > 0`. -/
@[tag "YW7B"]
theorem hierarchical_geometricRadial_criterion [NeZero L] :
    (∀ r : ℝ≥0∞,
      (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else r ^ (z.support.sup Nat.succ)) =
        ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r * ∑' n : ℕ, ((L : ℝ≥0∞) ^ d * r) ^ n) ∧
    (∀ r : ℝ≥0∞, (L ^ d = 1 ∨ r = 0) →
      (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else r ^ (z.support.sup Nat.succ)) = 0) ∧
    (∀ r : ℝ≥0∞, 1 < L ^ d → 0 < r → r < ⊤ →
      ((L : ℝ≥0∞) ^ d * r < 1 →
        (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else r ^ (z.support.sup Nat.succ)) =
          ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r)) ∧
      (1 ≤ (L : ℝ≥0∞) ^ d * r →
        (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else r ^ (z.support.sup Nat.succ)) =
          ⊤)) ∧
    (1 < L ^ d →
      (∑' z : ℕ →₀ (Fin d → ZMod L),
        if z = 0 then 0 else (⊤ : ℝ≥0∞) ^ (z.support.sup Nat.succ)) = ⊤) ∧
    (2 ≤ L → 1 ≤ d → ∀ α : ℝ,
      (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else
        ENNReal.ofReal ((L : ℝ) ^ (-((d : ℝ) + α) * ((z.support.sup Nat.succ : ℕ) : ℝ)))) < ⊤ ↔
        0 < α) :=
  ⟨tsum_geometricRadial_eq_mul_tsum, fun _ h => tsum_geometricRadial_eq_zero h,
    fun r hN hr0 _ => ⟨fun _ => tsum_geometricRadial_eq_div r,
      fun h => tsum_geometricRadial_eq_top hN hr0 h⟩,
    tsum_geometricRadial_top, fun hL hd α => tsum_powerLaw_lt_top_iff hL hd α⟩

/-! ### Cutoff, subcriticality and two-point bounds -/

/-- For `J(x,y) = C r^{ℓ(y-x)}` off the diagonal (diagonal arbitrary) with `N r < 1`:
if only bonds of level at most `n` are open, every cluster at `x` lies in `x + B_n` and has
volume at most `N^n`, in every configuration (and almost surely for a profile vanishing above
level `n`); the omitted row above level `n` is `M (Nr)^n`, `M = C(N-1)r/(1-Nr)`; and the
omitted probability row is at most `β M (Nr)^n`. -/
@[tag "KL29"]
theorem hierarchical_cutoff [NeZero L] (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (_hr : (L : ℝ≥0) ^ d * r < 1) :
    (∀ (n : ℕ) (ω : Config (ℕ →₀ (Fin d → ZMod L))),
      (∀ a b, a ≠ b → s(a, b) ∈ ω → (b - a).support.sup Nat.succ ≤ n) →
      ∀ x, cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} ∧
        (cluster ω x).encard ≤ (((L ^ d) ^ n : ℕ) : ℕ∞)) ∧
    (∀ (n : ℕ) (x : (ℕ →₀ (Fin d → ZMod L))),
      (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
        (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
          ((L : ℝ≥0∞) ^ d * r) ^ n) ∧
    (∀ (β : ℝ≥0) (n : ℕ) (x : (ℕ →₀ (Fin d → ZMod L))),
      (∑' y, if n < (y - x).support.sup Nat.succ then
          (unitInterval.toNNReal (intensityProfile J β s(x, y)) : ℝ≥0∞) else 0) ≤
        (β : ℝ≥0∞) * ((C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r /
          (1 - (L : ℝ≥0∞) ^ d * r) * ((L : ℝ≥0∞) ^ d * r) ^ n)) ∧
    (∀ (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval) (n : ℕ),
      (∀ x y, n < (y - x).support.sup Nat.succ → q s(x, y) = 0) →
      ∀ᵐ ω ∂law q, ∀ x, cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} ∧
        (cluster ω x).encard ≤ (((L ^ d) ^ n : ℕ) : ℕ∞)) :=
  ⟨cluster_subset_level_ball_of_forall, tsum_level_gt_eq_of_ne J C r hJ,
    tsum_level_gt_intensity_le_of_ne J C r hJ, fun q n hq => ae_cluster_subset_ball q n hq⟩

/-- For `J(x,y) = C r^{ℓ(y-x)}` off the diagonal (diagonal arbitrary) with `N r < 1`
and `M = C(N-1)r/(1-Nr)`: if `β M < 1` then `χ ≤ (1 - βM)⁻¹` and a.s. all clusters are finite;
both thresholds are at least `M⁻¹`; if `M = 0`, all off-diagonal intensities vanish, clusters
are a.s. singletons, `χ = 1` and both thresholds are `∞`; and with `2Nr ≤ 1` the same bounds
hold with `2C` in place of `M`. -/
@[tag "B6KD"]
theorem hierarchical_subcritical [NeZero L] (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) :
    (∀ β : ℝ≥0, (β : ℝ≥0∞) *
        ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1 →
      (∀ x, chi (intensityProfile J β) x ≤
        (1 - (β : ℝ≥0∞) *
          ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞))⁻¹) ∧
      law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0) ∧
    (((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
        globalCriticalIntensity J ∧
      ∀ x, ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
        rootCriticalIntensity J x) ∧
    (C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) = 0 →
      (∀ x y, x ≠ y → J s(x, y) = 0) ∧
      (∀ β : ℝ≥0, (∀ᵐ ω ∂law (intensityProfile J β), ∀ x, cluster ω x = {x}) ∧
        ∀ x, chi (intensityProfile J β) x = 1) ∧
      globalCriticalIntensity J = ⊤ ∧ ∀ x, rootCriticalIntensity J x = ⊤) ∧
    ((L : ℝ≥0) ^ d * r * 2 ≤ 1 →
      (∀ β : ℝ≥0, (β : ℝ≥0∞) * ((2 * C : ℝ≥0) : ℝ≥0∞) < 1 → ∀ x,
        chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) * ((2 * C : ℝ≥0) : ℝ≥0∞))⁻¹) ∧
      ((2 * C : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
      ∀ x, ((2 * C : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x) :=
  ⟨fun β hβ => ⟨fun x => chi_intensity_le_hierarchical_sharp_of_ne J C r hJ hr β hβ x,
      law_exists_infinite_hierarchical_eq_zero_of_ne J C r hJ hr β hβ⟩,
    ⟨inv_le_globalCriticalIntensity_hierarchical_sharp_of_ne J C r hJ hr,
      fun x => inv_le_rootCriticalIntensity_hierarchical_sharp_of_ne J C r hJ hr x⟩,
    fun hM => ⟨fun _ _ hxy => eq_zero_of_hierarchical_M_eq_zero J C r hJ hr hM hxy,
      fun β => ⟨(hierarchical_of_M_eq_zero_of_ne J C r hJ hr hM β).1,
        (hierarchical_of_M_eq_zero_of_ne J C r hJ hr hM β).2.1⟩,
      (hierarchical_of_M_eq_zero_of_ne J C r hJ hr hM 0).2.2.1,
      (hierarchical_of_M_eq_zero_of_ne J C r hJ hr hM 0).2.2.2⟩,
    fun h2 => ⟨fun β hβ x => chi_intensity_le_hierarchical_of_ne J C r hJ h2 β hβ x,
      inv_le_globalCriticalIntensity_hierarchical_of_ne J C r hJ h2,
      fun x => inv_le_rootCriticalIntensity_hierarchical_of_ne J C r hJ h2 x⟩⟩

/-- For `C ≥ 0`, `0 ≤ r ≤ 1`, `β ≥ 0` and `J(x,y) = C r^{ℓ(y-x)}` off the diagonal
(diagonal arbitrary), with `M = ∑_{z ≠ 0} C r^{ℓ(z)}` and `H(t) = ∑_n t^n`: for `x ≠ y`,
`τ_β(x,y) ≤ β J(x,y) H(2βM) H(βM)`, and when `M < ∞` and `2βM < 1`,
`τ_β(x,y) ≤ βJ(x,y)/((1-2βM)(1-βM))`. -/
@[tag "0K45"]
theorem hierarchical_two_point [NeZero L] (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ)) (hr : r ≤ 1)
    (β : ℝ≥0) {x y : (ℕ →₀ (Fin d → ZMod L))} (hxy : x ≠ y) :
    tau (intensityProfile J β) x y ≤
      (β : ℝ≥0∞) * J s(x, y) * (∑' n : ℕ, (2 * (β : ℝ≥0∞) * (∑' z : ℕ →₀ (Fin d → ZMod L),
          (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)))) ^ n) *
        (∑' n : ℕ, ((β : ℝ≥0∞) * (∑' z : ℕ →₀ (Fin d → ZMod L),
          (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)))) ^ n) ∧
    ((∑' z : ℕ →₀ (Fin d → ZMod L),
          (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞))) < ⊤ →
      2 * (β : ℝ≥0∞) * (∑' z : ℕ →₀ (Fin d → ZMod L),
          (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞))) < 1 →
      (tau (intensityProfile J β) x y).toReal ≤
        (β : ℝ) * (J s(x, y) : ℝ) /
          ((1 - 2 * (β : ℝ) * (∑' z : ℕ →₀ (Fin d → ZMod L),
            (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞))).toReal) *
            (1 - (β : ℝ) * (∑' z : ℕ →₀ (Fin d → ZMod L),
            (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞))).toReal))) :=
  ⟨tau_intensity_le_hierarchical_of_ne J C r hJ hr β hxy,
    tau_intensity_toReal_le_hierarchical_of_ne J C r hJ hr β hxy⟩

open Classical in
/-- On `ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `c, α > 0`, a kernel `J` invariant under
translations of distinct pairs with `J(u,v) ≥ c L^{-(d+α)j}` at first common level `j`: with
`R_n(β)` the quantile `tightnessScale` of the origin's level-`n` block under the profile
restricted to that block, `N = L^{dℓ}`, `e^{-N/(8e)} ≤ 1/4`, `L^{(d-α)ℓ} ≥ 16e²` and
`A = (4/c) L^{(d+α)ℓ} log(2N²)`, for every `β > 0` and `n`,
`R_n² ≥ (A/β) L^{(d+α)n}` implies `R_{n+ℓ}² ≥ (A/β) L^{(d+α)(n+ℓ)}`. -/
@[tag "7AER"]
theorem tightnessScale_hierarchical_amplification_offDiag [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, u ≠ v → J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {β : ℝ≥0} (hβ : 0 < β) (n : ℕ)
    (hn : (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) /
        β * (L : ℝ) ^ (((d : ℝ) + α) * n) ≤
      (tightnessScale (fun e => if e ∈ {z : (ℕ →₀ (Fin d → ZMod L)) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2) :
    (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
        (L : ℝ) ^ (((d : ℝ) + α) * ((n : ℝ) + ℓ)) ≤
      (tightnessScale (fun e => if e ∈ {z : (ℕ →₀ (Fin d → ZMod L)) |
        z.support.sup Nat.succ ≤ n + ℓ}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball (n + ℓ)).toFinset : ℝ) ^ 2 :=
  tightnessScale_hierarchical_amplification_of_ne hL hc hα J hJt hJ hexp hℓ hβ n hn

end PercLib.Models
