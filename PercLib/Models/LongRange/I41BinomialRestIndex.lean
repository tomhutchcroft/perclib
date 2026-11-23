/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
# Lemma I.4.1: the restricted vertex sum, and why `1(y ∉ K)` is there

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1, p. 34.

The single-site binomial identities of that lemma already exist in the recovered worktree and are
**cited, never restated** here:

* `PercLib.Probability.sum_choose_mul_pow_eq_pow_sub`,
  `PercLib.Probability.mul_pow_sub_pow_eq_sum_choose` (real forms);
* `PercLib.Models.LongRange.ofReal_mul_pow_sub_pow`,
  `PercLib.Models.LongRange.mul_pow_sub_pow_eq_sum_choose_ennreal` (MassTransportI41.lean);
* `PercLib.Models.LongRange.mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite` and
  `PercLib.Percolation.Bond.pow_add_sub_pow_eq_sum_choose_ennreal` (TruncatedMoments.lean);
* the concrete bookkeeping of
  `PercLib.Models.LongRange.russoRHS_eq_binomial_of_finite` (MassTransportI41.lean) and
  `PercLib.Models.LongRange.russoRHS_eq_binomial_of_root_finite` (TruncatedMoments.lean).

What is new here is the layer that is still missing from those files:

* `mul_sum_choose_mul_pow_eq_sum_choose_mul_pow_succ`: the index shift `a^ℓ ↦ a^(ℓ+1)` that
  turns the plain real identity into the multiply-by-`a` form, so the extra power of `a` is
  accounted for exactly once;
* `sum_mul_pow_sub_pow_eq_sum_choose` and `tsum_mul_pow_sub_pow_eq_sum_choose`: the sum-over-`y`
  form of the binomial step for an **arbitrary weight** `w` and with **only the root volume
  finite** (`B y` may be `⊤`). The two recovered files prove only the concrete instances, with
  `w y = 1{B_r}(y) · 1(y ∉ K)`, inside the calc block of `russoRHS_eq_binomial_of_finite` /
  `russoRHS_eq_binomial_of_root_finite`; there is no statement of the weighted form, and no
  Finset version at all;
* `tsum_indicator_one_mul_eq_tsum_subtype`: the rest-indexing that makes `1(y ∉ K)` mean "sum
  over `y ∉ K`". Without it the indicator is only a formal weight;
* `PercLib.Percolation.Bond.tsum_compl_cluster_indicator_mul_pow_sub_pow` and its subtype form:
  the binomial step with `1(y ∉ K)`, `K` the cluster of an arbitrary root `x`, in the bond
  algebra;
* `mul_pow_sub_pow_self_pos` and `compl_cluster_indicator_omission_counterexample`: the
  restriction is not redundant. At `y ∈ K` the two cluster volumes coincide, `b = a`, and the
  summand `a((2a)^p − a^p)` is strictly positive for `a > 0`, `p ≥ 1`; on two vertices with every
  pair open, `K = univ` and every volume is `2`, so the restricted sum is `0` while the
  unrestricted one is `8`. (The sharpness statement `top_mul_pow_sub_pow_ne_sum_choose` of the
  recovered files is about `A = ⊤`, a different failure mode: there the root volume is infinite.)

No definitions. Every `ℝ≥0∞` statement either carries an explicit `≠ ⊤` hypothesis or handles
`⊤` exactly; no infinite cluster is read as a finite volume.
-/
module

public import PercLib.Models.LongRange.MassTransportI41
public import PercLib.Models.LongRange.TruncatedMoments

/-!
# Rest-indexing and restricted sums for the binomial moment expansion

Weighted algebraic consequences of Lemma I.4.1's binomial expansion, with the paper's `1(y∉K)`
restriction retained. The root-finite weighted sums, complement-subtype reformulation, exact
omitted mass, and an explicit two-vertex omission counterexample avoid any finite interpretation
of an infinite cluster. No derivative or criticality claim is asserted.
-/

@[expose] public section

noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.Probability

/-- **The index shift of the binomial step.** Multiplying the `ℓ`-th summand of the plain
binomial expansion by one further factor of `a` raises the exponent of `a` from `ℓ` to `ℓ + 1`.
Composing this with `sum_choose_mul_pow_eq_pow_sub` gives the multiply-by-`a` form
`mul_pow_sub_pow_eq_sum_choose`. -/
theorem mul_sum_choose_mul_pow_eq_sum_choose_mul_pow_succ (a b : ℝ) (p : ℕ) :
    a * (∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ ℓ * b ^ (p - ℓ))
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ (ℓ + 1) * b ^ (p - ℓ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [pow_succ]
  ring

/-- At a vertex of the root cluster the two volumes coincide, `b = a`, and the corresponding
summand of the binomial step is strictly positive: `0 < a ((a + a)^p − a^p)` for `a > 0`,
`p ≥ 1`. This is why the restriction `1(y ∉ K)` of Lemma I.4.1 cannot be dropped. -/
theorem mul_pow_sub_pow_self_pos {a : ℝ} (ha : 0 < a) {p : ℕ} (hp : 1 ≤ p) :
    0 < a * ((a + a) ^ p - a ^ p) := by
  have hlt : a ^ p < (a + a) ^ p := pow_lt_pow_left₀ (by linarith) ha.le (by omega)
  nlinarith

end PercLib.Probability

namespace PercLib.Models.LongRange

variable {ι : Type*}

/-- **The sum-over-`y` form of the binomial step**, for a finite set of vertices and an arbitrary
nonnegative weight `w`: the weight and the coefficient `C(p,ℓ)` pass through the sum, and only
the factors depending on `y` stay inside. Only the root volume `A` has to be finite; the target
volumes `B y` may be infinite
(`mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite`). -/
theorem sum_mul_pow_sub_pow_eq_sum_choose (s : Finset ι) (w B : ι → ℝ≥0∞) (A : ℝ≥0∞)
    (hA : A ≠ ⊤) (p : ℕ) :
    ∑ y ∈ s, w y * (A * ((A + B y) ^ p - A ^ p))
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) *
          ∑ y ∈ s, w y * B y ^ (p - ℓ) := by
  have hterm : ∀ y ∈ s, w y * (A * ((A + B y) ^ p - A ^ p))
      = ∑ ℓ ∈ range p, w y * ((p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) * B y ^ (p - ℓ)) := by
    intro y _
    rw [mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite hA p, Finset.mul_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ac_rfl

/-- **The sum-over-`y` form of the binomial step, unrestricted.** The same statement with a
`tsum` over all vertices. Every `ℝ≥0∞` series converges, and only the root volume needs to be
finite. -/
theorem tsum_mul_pow_sub_pow_eq_sum_choose (w B : ι → ℝ≥0∞) (A : ℝ≥0∞)
    (hA : A ≠ ⊤) (p : ℕ) :
    ∑' y, w y * (A * ((A + B y) ^ p - A ^ p))
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) *
          ∑' y, w y * B y ^ (p - ℓ) := by
  have hterm : ∀ y, w y * (A * ((A + B y) ^ p - A ^ p))
      = ∑ ℓ ∈ range p, w y * ((p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) * B y ^ (p - ℓ)) := by
    intro y
    rw [mul_pow_sub_pow_eq_sum_choose_ennreal_of_finite hA p, Finset.mul_sum]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (s := range p) (fun ℓ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun y => by ac_rfl

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The paper's weight `1(y ∈ s)` restricts a vertex sum to `s`:
`∑_y 1(y ∈ s) f y = ∑_{y ∈ s} f y`. This is what makes `1(y ∉ K)` mean "sum over `y ∉ K`". -/
theorem tsum_indicator_one_mul_eq_tsum_subtype (s : Set V) (f : V → ℝ≥0∞) :
    ∑' y, s.indicator (fun _ => (1 : ℝ≥0∞)) y * f y = ∑' y : ↥s, f y := by
  rw [_root_.tsum_subtype]
  refine tsum_congr fun y => ?_
  by_cases h : y ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- **The binomial step of Lemma I.4.1 with the paper's restriction `1(y ∉ K)`**, `K` the cluster
of a root `x` in canonical bond algebra: for a finite root volume `A`,
`∑_y 1(y ∉ K) A ((A + B_y)^p − A^p) = ∑_{ℓ<p} C(p,ℓ) A^{ℓ+1} ∑_y 1(y ∉ K) B_y^{p−ℓ}`.
The cluster volumes `B y` may be infinite: only `A` has to be finite. An extra far-vertex weight
is recovered from the abstract form by taking `w := fun y => 1(y ∉ K) * w' y`. -/
theorem tsum_compl_cluster_indicator_mul_pow_sub_pow (ω : Config V) (x : V) (A : ℝ≥0∞)
    (B : V → ℝ≥0∞) (hA : A ≠ ⊤) (p : ℕ) :
    ∑' y, (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        (A * ((A + B y) ^ p - A ^ p))
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) *
          ∑' y, (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * B y ^ (p - ℓ) :=
  PercLib.Models.LongRange.tsum_mul_pow_sub_pow_eq_sum_choose
    (fun y => (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y) B A hA p

/-- **The binomial step of Lemma I.4.1 summed over `y ∉ K`**, in the form the paper writes it:
the indicator is replaced by summation over the complement of the root cluster. -/
theorem tsum_compl_cluster_mul_pow_sub_pow (ω : Config V) (x : V) (A : ℝ≥0∞) (B : V → ℝ≥0∞)
    (hA : A ≠ ⊤) (p : ℕ) :
    ∑' y : ↥((cluster ω x)ᶜ), A * ((A + B y) ^ p - A ^ p)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ≥0∞) * A ^ (ℓ + 1) *
          ∑' y : ↥((cluster ω x)ᶜ), B y ^ (p - ℓ) := by
  rw [← tsum_indicator_one_mul_eq_tsum_subtype ((cluster ω x)ᶜ)
    (fun y => A * ((A + B y) ^ p - A ^ p))]
  rw [tsum_compl_cluster_indicator_mul_pow_sub_pow ω x A B hA p]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [tsum_indicator_one_mul_eq_tsum_subtype]

/-- **The exact mass that `1(y ∉ K)` removes.** Every `y` in the root cluster has the root's
cluster (`cluster_eq_of_mem_conn`), hence the root's volume, so the sum of the binomial summand
over the cluster itself is the volume `|K|` times the single-vertex increment
`A ((2A)^p − A^p)`, `A = |K|`. This is precisely the gap between the unrestricted vertex sum and
the one restricted by `1(y ∉ K)`. -/
theorem tsum_cluster_omitted_mass (ω : Config V) (x : V) (p : ℕ) :
    ∑' y : ↥(cluster ω x), ((cluster ω x).encard : ℝ≥0∞) *
        ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω x).encard : ℝ≥0∞) ^ p)
      = ((cluster ω x).encard : ℝ≥0∞) *
          (((cluster ω x).encard : ℝ≥0∞) *
            ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω x).encard : ℝ≥0∞)) ^ p -
              ((cluster ω x).encard : ℝ≥0∞) ^ p)) := by
  have hconst : ∀ y : ↥(cluster ω x), (cluster ω y).encard = (cluster ω x).encard := by
    intro y
    exact congrArg Set.encard (cluster_eq_of_mem_conn ((mem_cluster_iff ω x y).1 y.2)).symm
  calc ∑' y : ↥(cluster ω x), ((cluster ω x).encard : ℝ≥0∞) *
        ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
          ((cluster ω x).encard : ℝ≥0∞) ^ p)
      = ∑' _y : ↥(cluster ω x), ((cluster ω x).encard : ℝ≥0∞) *
          ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω x).encard : ℝ≥0∞)) ^ p -
            ((cluster ω x).encard : ℝ≥0∞) ^ p) :=
        tsum_congr fun y => by
          show ((cluster ω x).encard : ℝ≥0∞) * _ = ((cluster ω x).encard : ℝ≥0∞) * _
          rw [hconst y]
    _ = ((cluster ω x).encard : ℝ≥0∞) *
          (((cluster ω x).encard : ℝ≥0∞) *
            ((((cluster ω x).encard : ℝ≥0∞) + ((cluster ω x).encard : ℝ≥0∞)) ^ p -
              ((cluster ω x).encard : ℝ≥0∞) ^ p)) :=
        ENNReal.tsum_set_const (s := cluster ω x) _

/-- **The factor `1(y ∉ K)` is not redundant.** On the two-vertex set `Fin 2` with every pair
open, the cluster of `0` is all of `Fin 2` (`hK` below), so the root volume and every cluster
volume equal `2`; with `p = 1` each summand of the binomial step is `2 * ((2 + 2) - 2) = 4`. The
sum restricted to `y ∉ K` is `0`, while the unrestricted sum is `8 = 2 * 4`, in agreement with
`tsum_cluster_omitted_mass` (`|K| · A · (2A − A) = 2 · 2 · 2`): replacing
`1(y ∉ K)` by `1` in the sum-over-`y` form changes its value, so the restriction is part of the
statement and not a convenience. -/
theorem compl_cluster_indicator_omission_counterexample :
    (∑ y : Fin 2,
        (cluster (Set.univ : Config (Fin 2)) 0)ᶜ.indicator (fun _ => (1 : ℝ)) y *
          (2 * ((2 + 2) ^ 1 - 2 ^ 1)) = 0) ∧
      (∑ _y : Fin 2, (2 : ℝ) * ((2 + 2) ^ 1 - 2 ^ 1) = 8) ∧
      ((∑ y : Fin 2,
          (cluster (Set.univ : Config (Fin 2)) 0)ᶜ.indicator (fun _ => (1 : ℝ)) y *
            (2 * ((2 + 2) ^ 1 - 2 ^ 1)))
        ≠ ∑ _y : Fin 2, (2 : ℝ) * ((2 + 2) ^ 1 - 2 ^ 1)) := by
  have hK : cluster (Set.univ : Config (Fin 2)) 0 = Set.univ := by
    have h0 : (0 : Fin 2) ∈ cluster (Set.univ : Config (Fin 2)) 0 := mem_cluster_self _ 0
    have h1 : (1 : Fin 2) ∈ cluster (Set.univ : Config (Fin 2)) 0 := by
      rw [mem_cluster_iff]
      exact mem_conn_of_mem (by decide) (by simp)
    refine Set.eq_univ_of_forall fun y => ?_
    fin_cases y
    · exact h0
    · exact h1
  have hzero : (∑ y : Fin 2,
      (cluster (Set.univ : Config (Fin 2)) 0)ᶜ.indicator (fun _ => (1 : ℝ)) y *
        (2 * ((2 + 2) ^ 1 - 2 ^ 1))) = 0 := by
    simp [hK]
  have hfull : (∑ _y : Fin 2, (2 : ℝ) * ((2 + 2) ^ 1 - 2 ^ 1)) = 8 := by
    rw [Fin.sum_univ_two]
    norm_num
  exact ⟨hzero, hfull, by rw [hzero, hfull]; norm_num⟩

end PercLib.Percolation.Bond
