/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Energy and exit-time bounds for the return kernel of lazy simple random walk on a fixed
infinite connected locally finite graph. Mathematical reference: M. T. Barlow, A. A. Járai,
A. Kumagai and G. Slade, "Random walk on the incipient infinite cluster for oriented
percolation in high dimensions", Comm. Math. Phys. 278 (2008), Section 2.1.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Field
public import PercLib.Probability.KilledGreen

/-!
# The lazy return kernel: energy and exit-time bounds

Let `G` be a connected locally finite graph with all degrees positive, `π(x) = deg x`, and let
`p n x y` be the `n`-step transition probabilities of the lazy simple random walk, given by the
first-step recursion `p (n+1) x y = p n x y / 2 + (∑_{z ∼ x} p n z y) / (2 deg x)`. The lazy
operator `Q f x = f x / 2 + (∑_{z ∼ x} f z) / (2 deg x)` is self-adjoint and nonnegative on
finitely supported functions in `ℓ²(π)`; the column `x ↦ p n x o` equals `Qⁿ 𝟙_o`.

## Main results

* `SimpleGraph.Connected.finite_setOf_dist_le`: balls of a connected locally finite graph are
  finite.
* `PercLib.Probability.degree_mul_lazy_kernel_comm`: reversibility,
  `deg x · p n x y = deg y · p n y x`.
* `PercLib.Probability.lazy_return_le`: the energy bound
  `p n o o / deg o ≤ 2 / V(r) + 2r / (n + 1)`, where `V(r) = ∑_{d(o,x) ≤ r} deg x`.
* `PercLib.Probability.lazy_return_ge`: the exit-time bound
  `(u - n)₊² / (M² V(ρ)) ≤ p (2n) o o / deg o`, where, for the killed survival function
  `s n x = P_x(Y_0, …, Y_n ∈ B(ρ))`, `u = ∑ₙ s n o` and `M = sup_{x ∈ B(ρ)} ∑ₙ s n x`.
-/

@[expose] public section
noncomputable section

open Finset
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- Every vertex adjacent to `x` is at most one step farther from `o` than `x`. -/
theorem SimpleGraph.Connected.dist_le_dist_add_one_of_adj (hG : G.Connected) {o x z : V}
    (h : G.Adj x z) : G.dist o z ≤ G.dist o x + 1 := by
  have := hG.dist_triangle (u := o) (v := x) (w := z)
  rwa [SimpleGraph.dist_eq_one_iff_adj.2 h] at this

/-- Balls of a connected locally finite graph are finite. -/
theorem SimpleGraph.Connected.finite_setOf_dist_le (hG : G.Connected) (o : V) (r : ℕ) :
    {x | G.dist o x ≤ r}.Finite := by
  induction r with
  | zero =>
    refine (Set.finite_singleton o).subset fun x hx => ?_
    have : G.dist o x = 0 := Nat.le_zero.1 hx
    exact ((hG.preconnected o x).dist_eq_zero_iff.1 this).symm
  | succ r ih =>
    refine (ih.biUnion fun x _ => ((G.neighborSet x).toFinite.insert x)).subset ?_
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_ofPred_eq, exists_prop]
    rcases Nat.lt_or_ge (G.dist o y) (r + 1) with h | h
    · exact ⟨y, by omega, Or.inl rfl⟩
    · have hd : G.dist o y = r + 1 := le_antisymm hy h
      obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist o y
      have hne : y ≠ o := by
        rintro rfl; simp at hd
      obtain ⟨z, h, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne w.reverse
      have hlen : q.length = r := by
        have := congrArg SimpleGraph.Walk.length hq
        simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons] at this
        omega
      refine ⟨z, ?_, Or.inr h.symm⟩
      rw [SimpleGraph.dist_comm]
      exact hlen ▸ SimpleGraph.dist_le q

namespace PercLib.Probability

/-- Swapping the endpoints in a sum over ordered adjacent pairs, for a summand that vanishes
when its first vertex lies outside `F₀`, where `F` contains `F₀` and its neighbours. -/
theorem sum_neighborFinset_comm_of_vanish {F₀ F : Finset V} (hsub : F₀ ⊆ F)
    (hF : ∀ x ∈ F₀, ∀ z, G.Adj x z → z ∈ F) (φ : V → V → ℝ)
    (hφ : ∀ x z, x ∉ F₀ → φ x z = 0) :
    ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, φ x z = ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, φ z x := by
  classical
  have h1 : ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, φ x z =
      ∑ x ∈ F₀, ∑ z ∈ G.neighborFinset x, φ x z :=
    (Finset.sum_subset hsub fun x _ hx => Finset.sum_eq_zero fun z _ => hφ x z hx).symm
  have h2 : ∀ x ∈ F, ∑ z ∈ G.neighborFinset x, φ z x =
      ∑ z ∈ (G.neighborFinset x).filter (· ∈ F₀), φ z x := by
    intro x _
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun z _ => by
      split_ifs with h
      · rfl
      · exact hφ z x h
  rw [h1, Finset.sum_congr rfl h2]
  refine Finset.sum_comm' fun x z => ?_
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hx, hxz⟩
    exact ⟨⟨hxz.symm, hx⟩, hF x hx z hxz⟩
  · rintro ⟨⟨hzx, hx⟩, _⟩
    exact ⟨hx, hzx.symm⟩

section Lazy

variable (Q : (V → ℝ) → V → ℝ)

theorem degree_mul_lazy_mul_eq (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (f g : V → ℝ) (x : V) :
    (G.degree x : ℝ) * Q f x * g x =
      G.degree x * f x * g x / 2 + (∑ z ∈ G.neighborFinset x, g x * f z) / 2 := by
  have hd : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast (hdeg x).ne'
  rw [hQ, ← Finset.mul_sum]
  field_simp

/-- The lazy operator is self-adjoint in `ℓ²(deg)` against a function supported in `F₀`. -/
theorem sum_degree_mul_lazy_comm (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    {F₀ F : Finset V} (hsub : F₀ ⊆ F) (hF : ∀ x ∈ F₀, ∀ z, G.Adj x z → z ∈ F)
    (a b : V → ℝ) (hb : ∀ x ∉ F₀, b x = 0) :
    ∑ x ∈ F, (G.degree x : ℝ) * Q a x * b x = ∑ x ∈ F, (G.degree x : ℝ) * a x * Q b x := by
  have h1 : ∀ x, (G.degree x : ℝ) * a x * Q b x = G.degree x * Q b x * a x := fun x => by ring
  simp only [h1, degree_mul_lazy_mul_eq Q hdeg hQ, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [sum_neighborFinset_comm_of_vanish hsub hF (fun x z => b x * a z)
    (fun x z hx => by simp [hb x hx])]
  have e1 : ∑ x ∈ F, (G.degree x : ℝ) * a x * b x = ∑ x ∈ F, (G.degree x : ℝ) * b x * a x :=
    Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, b z * a x =
      ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, a x * b z :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by ring
  rw [e1, e2]

/-- Quadratic-form identities for the lazy operator: `∑_{x, z ∼ x} (w x + w z)² = 4⟨w, Qw⟩`
and `∑_{x, z ∼ x} (w x - w z)² = 4(⟨w, w⟩ - ⟨w, Qw⟩)` in `ℓ²(deg)`. -/
theorem lazy_quadratic_identities (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    {F₀ F : Finset V} (hsub : F₀ ⊆ F) (hF : ∀ x ∈ F₀, ∀ z, G.Adj x z → z ∈ F)
    (w : V → ℝ) (hw : ∀ x ∉ F₀, w x = 0) :
    ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, (w x + w z) ^ 2 =
        4 * ∑ x ∈ F, (G.degree x : ℝ) * w x * Q w x ∧
      ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, (w x - w z) ^ 2 =
        4 * (∑ x ∈ F, (G.degree x : ℝ) * w x * w x -
          ∑ x ∈ F, (G.degree x : ℝ) * w x * Q w x) := by
  have hA : ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x ^ 2 =
      ∑ x ∈ F, (G.degree x : ℝ) * w x * w x := Finset.sum_congr rfl fun x _ => by
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]; ring
  have hA' : ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w z ^ 2 =
      ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x ^ 2 :=
    (sum_neighborFinset_comm_of_vanish hsub hF (fun x _ => w x ^ 2)
      (fun x z hx => by simp [hw x hx])).symm
  have hQ' : ∑ x ∈ F, (G.degree x : ℝ) * w x * Q w x =
      (∑ x ∈ F, (G.degree x : ℝ) * w x * w x) / 2 +
        (∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x * w z) / 2 := by
    have h1 : ∀ x, (G.degree x : ℝ) * w x * Q w x = G.degree x * Q w x * w x :=
      fun x => by ring
    simp only [h1, degree_mul_lazy_mul_eq Q hdeg hQ, Finset.sum_add_distrib, ← Finset.sum_div]
  have e1 : ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, (w x + w z) ^ 2 =
      ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x ^ 2 +
        ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w z ^ 2 +
        2 * ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x * w z := by
    have : ∀ x z, (w x + w z) ^ 2 = w x ^ 2 + w z ^ 2 + 2 * (w x * w z) := fun _ _ => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e2 : ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, (w x - w z) ^ 2 =
      ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x ^ 2 +
        ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w z ^ 2 -
        2 * ∑ x ∈ F, ∑ z ∈ G.neighborFinset x, w x * w z := by
    have : ∀ x z, (w x - w z) ^ 2 = w x ^ 2 + w z ^ 2 - 2 * (w x * w z) := fun _ _ => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  constructor
  · rw [e1, hA', hA, hQ']; ring
  · rw [e2, hA', hA, hQ']; ring

theorem lazy_sub
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (f h : V → ℝ) : Q (fun x => f x - h x) = fun x => Q f x - Q h x := by
  funext x
  rw [hQ, hQ, hQ, Finset.sum_sub_distrib]
  ring

theorem lazy_const_one (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x)) :
    Q (fun _ => 1) = fun _ => 1 := by
  funext x
  have hd : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast (hdeg x).ne'
  rw [hQ, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
  field_simp
  ring

variable (hG : G.Connected) (o : V)
include hG

theorem lazy_eq_zero_of_dist
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    {b : V → ℝ} {m : ℕ} (hb : ∀ x, m < G.dist o x → b x = 0) :
    ∀ x, m + 1 < G.dist o x → Q b x = 0 := by
  intro x hx
  have hs : ∑ z ∈ G.neighborFinset x, b z = 0 := Finset.sum_eq_zero fun z hz => hb z (by
    have := hG.dist_le_dist_add_one_of_adj (o := o) ((G.mem_neighborFinset x z).1 hz).symm
    omega)
  rw [hQ, hb x (by omega), hs]
  simp

theorem iterate_lazy_eq_zero_of_dist
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    {b : V → ℝ} {m : ℕ} (hb : ∀ x, m < G.dist o x → b x = 0) (k : ℕ) :
    ∀ x, m + k < G.dist o x → Q^[k] b x = 0 := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    exact lazy_eq_zero_of_dist Q hG o hQ ih x (by omega)

/-- Self-adjointness of the lazy operator on the ball `B(R)`, against a function supported in
`B(m)` with `m < R`. -/
theorem sum_ball_lazy_comm (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    {R m : ℕ} (hmR : m + 1 ≤ R) (a b : V → ℝ) (hb : ∀ x, m < G.dist o x → b x = 0) :
    ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset, (G.degree x : ℝ) * Q a x * b x =
      ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset, (G.degree x : ℝ) * a x * Q b x := by
  refine sum_degree_mul_lazy_comm Q hdeg hQ (F₀ := (hG.finite_setOf_dist_le o m).toFinset)
    ?_ ?_ a b ?_
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
    omega
  · intro x hx z hxz
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
    have := hG.dist_le_dist_add_one_of_adj (o := o) hxz
    omega
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hx
    exact hb x hx

theorem sum_ball_iterate_lazy_comm (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    {R m : ℕ} (k : ℕ) (hmR : m + k ≤ R) (a b : V → ℝ) (hb : ∀ x, m < G.dist o x → b x = 0) :
    ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset, (G.degree x : ℝ) * Q^[k] a x * b x =
      ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset, (G.degree x : ℝ) * a x * Q^[k] b x := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (by omega) (Q a),
      sum_ball_lazy_comm Q hG o hdeg hQ (m := m + k) (by omega) a (Q^[k] b)
        (iterate_lazy_eq_zero_of_dist Q hG o hQ hb k),
      ← Function.iterate_succ_apply' Q k b]

end Lazy

section Kernel

variable [DecidableEq V] (Q : (V → ℝ) → V → ℝ) (p : ℕ → V → V → ℝ)

theorem lazy_kernel_nonneg (hdeg : ∀ x, 0 < G.degree x)
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (n : ℕ) (x y : V) : 0 ≤ p n x y := by
  induction n generalizing x with
  | zero => rw [hp0]; split_ifs <;> norm_num
  | succ n ih =>
    rw [hps]
    have hd : (0 : ℝ) < 2 * G.degree x := by have := hdeg x; positivity
    exact add_nonneg (by linarith [ih x])
      (div_nonneg (Finset.sum_nonneg fun z _ => ih z) hd.le)

theorem lazy_kernel_column_eq_iterate
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (y : V) (n : ℕ) : (fun x => p n x y) = Q^[n] (fun x => if x = y then 1 else 0) := by
  induction n with
  | zero => funext x; exact hp0 x y
  | succ n ih =>
    funext x
    rw [Function.iterate_succ_apply', ← ih, hQ, hps]

omit [DecidableEq V] in
theorem iterate_lazy_kernel_column
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (y : V) (j k : ℕ) : Q^[j] (fun x => p k x y) = fun x => p (j + k) x y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    rw [show j + 1 + k = (j + k) + 1 by omega, hps, hQ]

variable (hG : G.Connected) (o : V)
include hG

theorem lazy_kernel_eq_zero_of_lt_dist
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    {y : V} {k : ℕ} {x : V} (hx : G.dist o y + k < G.dist o x) : p k x y = 0 := by
  refine (congrFun (lazy_kernel_column_eq_iterate Q p hQ hp0 hps y k) x).trans ?_
  refine iterate_lazy_eq_zero_of_dist Q hG o hQ (m := G.dist o y) ?_ k x hx
  intro z hz
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  rintro rfl
  omega

/-- Reversibility of lazy simple random walk: `deg x · p n x y = deg y · p n y x`. -/
theorem degree_mul_lazy_kernel_comm (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (n : ℕ) (x y : V) : (G.degree x : ℝ) * p n x y = G.degree y * p n y x := by
  have h := sum_ball_iterate_lazy_comm Q hG x hdeg hQ
    (R := G.dist x y + n) (m := G.dist x y) n (by omega)
    (fun z => if z = x then 1 else 0) (fun z => if z = y then 1 else 0)
    (by intro z hz; simp only [ite_eq_right_iff, one_ne_zero, imp_false]; rintro rfl; omega)
  rw [← lazy_kernel_column_eq_iterate Q p hQ hp0 hps x,
    ← lazy_kernel_column_eq_iterate Q p hQ hp0 hps y] at h
  rw [Finset.sum_eq_single y (fun z _ hz => by simp [hz]) (fun h => absurd (by simp) h),
    Finset.sum_eq_single x (fun z _ hz => by simp [hz]) (fun h => absurd (by simp) h)]
    at h
  simp only [↓reduceIte, mul_one] at h
  linarith

/-- The `ℓ²(deg)` inner product of two columns at `o`:
`∑_x deg x · p j x o · p k x o = deg o · p (j + k) o o` on any ball containing the supports. -/
theorem sum_ball_degree_mul_column_mul_column (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    {R : ℕ} (j k : ℕ) (h : j + k ≤ R) :
    ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset, (G.degree x : ℝ) * p j x o * p k x o =
      G.degree o * p (j + k) o o := by
  have hc := sum_ball_iterate_lazy_comm Q hG o hdeg hQ (R := R) (m := k) j (by omega)
    (fun z => if z = o then 1 else 0) (fun x => p k x o)
    (fun x hx => lazy_kernel_eq_zero_of_lt_dist Q p hG o hQ hp0 hps (by simpa using hx))
  rw [iterate_lazy_kernel_column Q p hQ hps, ← lazy_kernel_column_eq_iterate Q p hQ hp0 hps o]
    at hc
  rw [hc, Finset.sum_eq_single o (fun z _ hz => by simp [hz])
    (fun h => absurd (by simp) h)]
  simp

/-- The degree-weighted mass of a column is at most `deg o`. -/
theorem sum_ball_degree_mul_column_le (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (n r : ℕ) :
    ∑ x ∈ (hG.finite_setOf_dist_le o r).toFinset, (G.degree x : ℝ) * p n x o ≤ G.degree o := by
  have hc := sum_ball_iterate_lazy_comm Q hG o hdeg hQ (R := n + r) (m := 0) n (by omega)
    (fun _ => 1) (fun z => if z = o then 1 else 0)
    (by intro z hz; simp only [ite_eq_right_iff, one_ne_zero, imp_false]; rintro rfl; simp at hz)
  have h1 : ∀ k, Q^[k] (fun _ : V => (1 : ℝ)) = fun _ => 1 := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, lazy_const_one Q hdeg hQ]
  rw [h1, ← lazy_kernel_column_eq_iterate Q p hQ hp0 hps o,
    Finset.sum_eq_single o (fun z _ hz => by simp [hz]) (fun h => absurd (by simp) h)] at hc
  simp only [↓reduceIte, mul_one] at hc
  rw [hc]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (lazy_kernel_nonneg p hdeg hp0 hps n x o)
  intro x hx
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
  omega

end Kernel

section Path

variable [DecidableEq V] (hG : G.Connected)
include hG

/-- Cauchy–Schwarz along a shortest path: `(f o - f y)² ≤ d(o, y) · 𝓔(f)`, where
`𝓔(f) = ½ ∑_{x ∈ F} ∑_{z ∼ x} (f x - f z)²` and `F` contains the ball of radius `d(o, y)`.
Assembled from the walk lemmas of `PercLib.Probability.KilledGreen`. -/
theorem sq_sub_le_dist_mul_energy (o y : V) (f : V → ℝ) {F : Finset V}
    (hF : ∀ x, G.dist o x ≤ G.dist o y → x ∈ F) :
    (f o - f y) ^ 2 ≤
      G.dist o y * ((∑ x ∈ F, ∑ z ∈ G.neighborFinset x, (f x - f z) ^ 2) / 2) := by
  obtain ⟨w, hw, hlen⟩ := (hG.preconnected o y).exists_path_of_dist
  have hsupp : ∀ v ∈ w.support, v ∈ F := by
    intro v hv
    apply hF
    calc G.dist o v ≤ (w.takeUntil v hv).length := SimpleGraph.dist_le _
      _ ≤ w.length := SimpleGraph.Walk.length_takeUntil_le_length _ _
      _ = G.dist o y := hlen
  have h1 := SimpleGraph.Walk.sq_sub_le_length_mul_sum f w
  have h2 := hw.two_mul_sum_sq_sub_le f (A := F) fun i _ => hsupp _ (w.getVert_mem_support i)
  rw [hlen] at h1 h2
  refine h1.trans ?_
  gcongr
  linarith

end Path

section Upper

theorem le_two_div_add_two_mul_of_sq_sub_le {a b W t : ℝ} (hb0 : 0 ≤ b)
    (hb : b ≤ 1 / W) (ht : 0 ≤ t) (h : (a - b) ^ 2 ≤ 2 * t * a) : a ≤ 2 / W + 2 * t := by
  by_contra hlt
  push Not at hlt
  have h1 : 2 * b ≤ 2 / W := by rw [div_eq_mul_one_div 2 W]; linarith
  have ha : a - b > a / 2 + t := by linarith
  have hpos : 0 < a / 2 + t := by linarith [h1, hb0]
  nlinarith [sq_nonneg (a / 2 - t), mul_lt_mul'' ha ha hpos.le hpos.le]

variable [DecidableEq V] (Q : (V → ℝ) → V → ℝ) (p : ℕ → V → V → ℝ) (hG : G.Connected) (o : V)
include hG

/-- **Energy bound for the lazy return kernel.** For all `n` and `r`,
`p n o o / deg o ≤ 2 / V(r) + 2r / (n + 1)` with `V(r) = ∑_{d(o,x) ≤ r} deg x`. -/
theorem lazy_return_le (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (n r : ℕ) :
    p n o o / G.degree o ≤
      2 / ∑ x ∈ (hG.finite_setOf_dist_le o r).toFinset, (G.degree x : ℝ) + 2 * r / (n + 1) := by
  set R := 2 * n + r + 4 with hR
  set c : ℕ → ℝ := fun m => p m o o with hc
  have hdo : (0 : ℝ) < G.degree o := by exact_mod_cast hdeg o
  have hpos := lazy_kernel_nonneg p hdeg hp0 hps
  have hin : ∀ j k, j + k ≤ R → ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset,
      (G.degree x : ℝ) * p j x o * p k x o = G.degree o * c (j + k) :=
    fun j k h => sum_ball_degree_mul_column_mul_column Q p hG o hdeg hQ hp0 hps j k h
  have hsub : (hG.finite_setOf_dist_le o (R - 1)).toFinset ⊆
      (hG.finite_setOf_dist_le o R).toFinset := by
    intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
    omega
  have hF : ∀ x ∈ (hG.finite_setOf_dist_le o (R - 1)).toFinset, ∀ z, G.Adj x z →
      z ∈ (hG.finite_setOf_dist_le o R).toFinset := by
    intro x hx z hxz
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
    have := hG.dist_le_dist_add_one_of_adj (o := o) hxz
    omega
  have hcol : ∀ k, k + 2 ≤ R → ∀ x ∉ (hG.finite_setOf_dist_le o (R - 1)).toFinset,
      p k x o = 0 := by
    intro k hk x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hx
    exact lazy_kernel_eq_zero_of_lt_dist Q p hG o hQ hp0 hps (by simp; omega)
  have hQcol : ∀ k, Q (fun x => p k x o) = fun x => p (k + 1) x o := by
    intro k
    have := iterate_lazy_kernel_column Q p hQ hps o 1 k
    rw [Function.iterate_one, add_comm 1 k] at this
    exact this
  -- second differences of `c` are nonnegative
  have hconv : ∀ m, m + 4 ≤ R → 0 ≤ c m - 2 * c (m + 1) + c (m + 2) := by
    intro m hm
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · have e : ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset,
          (G.degree x : ℝ) * (p k x o - p (k + 1) x o) ^ 2 =
          G.degree o * (c (2 * k) - 2 * c (2 * k + 1) + c (2 * k + 2)) := by
        have h1 := hin k k (by omega)
        have h2 := hin k (k + 1) (by omega)
        have h3 := hin (k + 1) (k + 1) (by omega)
        rw [show k + k = 2 * k by omega] at h1
        rw [show k + (k + 1) = 2 * k + 1 by omega] at h2
        rw [show k + 1 + (k + 1) = 2 * k + 2 by omega] at h3
        have : ∀ x, (G.degree x : ℝ) * (p k x o - p (k + 1) x o) ^ 2 =
            G.degree x * p k x o * p k x o - 2 * (G.degree x * p k x o * p (k + 1) x o) +
              G.degree x * p (k + 1) x o * p (k + 1) x o := fun x => by ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          h1, h2, h3]
        ring
      have : 0 ≤ (G.degree o : ℝ) * (c (2 * k) - 2 * c (2 * k + 1) + c (2 * k + 2)) :=
        e ▸ Finset.sum_nonneg fun x _ => by positivity
      exact (mul_nonneg_iff_of_pos_left hdo).1 this
    · set w : V → ℝ := fun x => p k x o - p (k + 1) x o with hw
      have hQw : Q w = fun x => p (k + 1) x o - p (k + 2) x o := by
        rw [hw, lazy_sub Q hQ, hQcol, hQcol]
      have hws : ∀ x ∉ (hG.finite_setOf_dist_le o (R - 1)).toFinset, w x = 0 := by
        intro x hx
        simp only [hw, hcol k (by omega) x hx, hcol (k + 1) (by omega) x hx, sub_zero]
      have hid := (lazy_quadratic_identities Q hdeg hQ hsub hF w hws).1
      have e : ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset, (G.degree x : ℝ) * w x * Q w x =
          G.degree o * (c (2 * k + 1) - 2 * c (2 * k + 1 + 1) + c (2 * k + 1 + 2)) := by
        have h1 := hin k (k + 1) (by omega)
        have h2 := hin k (k + 2) (by omega)
        have h3 := hin (k + 1) (k + 1) (by omega)
        have h4 := hin (k + 1) (k + 2) (by omega)
        rw [show k + (k + 1) = 2 * k + 1 by omega] at h1
        rw [show k + (k + 2) = 2 * k + 1 + 1 by omega] at h2
        rw [show k + 1 + (k + 1) = 2 * k + 1 + 1 by omega] at h3
        rw [show k + 1 + (k + 2) = 2 * k + 1 + 2 by omega] at h4
        rw [hQw]
        have : ∀ x, (G.degree x : ℝ) * w x * (p (k + 1) x o - p (k + 2) x o) =
            G.degree x * p k x o * p (k + 1) x o - G.degree x * p k x o * p (k + 2) x o -
              G.degree x * p (k + 1) x o * p (k + 1) x o +
              G.degree x * p (k + 1) x o * p (k + 2) x o := fun x => by rw [hw]; ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
        ring
      have : 0 ≤ (G.degree o : ℝ) *
          (c (2 * k + 1) - 2 * c (2 * k + 1 + 1) + c (2 * k + 1 + 2)) := by
        rw [← e]
        have : 0 ≤ ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset,
            ∑ z ∈ G.neighborFinset x, (w x + w z) ^ 2 :=
          Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ => sq_nonneg _
        linarith
      exact (mul_nonneg_iff_of_pos_left hdo).1 this
  have hd : ∀ m j, m + j + 4 ≤ R → c (m + j) - c (m + j + 1) ≤ c m - c (m + 1) := by
    intro m j
    induction j with
    | zero => intro; simp
    | succ j ih =>
      intro h
      have := hconv (m + j) (by omega)
      have := ih (by omega)
      rw [show m + (j + 1) = m + j + 1 by omega]
      linarith
  have htel : (n + 1 : ℝ) * (c (2 * n) - c (2 * n + 1)) ≤ c n - c (2 * n + 1) := by
    have hs : ∑ k ∈ Finset.range (n + 1), (c (n + k) - c (n + (k + 1))) =
        c (n + 0) - c (n + (n + 1)) :=
      Finset.sum_range_sub' (fun k => c (n + k)) (n + 1)
    rw [show n + 0 = n by omega, show n + (n + 1) = 2 * n + 1 by omega] at hs
    rw [← hs]
    calc (n + 1 : ℝ) * (c (2 * n) - c (2 * n + 1))
        = ∑ _k ∈ Finset.range (n + 1), (c (2 * n) - c (2 * n + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_range] at hk
        have := hd (n + k) (n - k) (by omega)
        rw [show n + k + (n - k) = 2 * n by omega] at this
        rw [show n + (k + 1) = n + k + 1 by omega]
        exact this
  have hE : ∑ x ∈ (hG.finite_setOf_dist_le o R).toFinset,
      ∑ z ∈ G.neighborFinset x, (p n x o - p n z o) ^ 2 =
      4 * G.degree o * (c (2 * n) - c (2 * n + 1)) := by
    have hid := (lazy_quadratic_identities Q hdeg hQ hsub hF (fun x => p n x o)
      (hcol n (by omega))).2
    rw [hQcol] at hid
    have h1 := hin n n (by omega)
    have h2 := hin n (n + 1) (by omega)
    rw [show n + n = 2 * n by omega] at h1
    rw [show n + (n + 1) = 2 * n + 1 by omega] at h2
    rw [hid, h1, h2]
    ring
  -- a point of the ball where the normalized column is at most `1 / V(r)`
  set W := ∑ x ∈ (hG.finite_setOf_dist_le o r).toFinset, (G.degree x : ℝ)
  have hoR : o ∈ (hG.finite_setOf_dist_le o r).toFinset := by simp
  have hWpos : 0 < W := Finset.sum_pos (fun x _ => by exact_mod_cast hdeg x) ⟨o, hoR⟩
  have hmass := sum_ball_degree_mul_column_le Q p hG o hdeg hQ hp0 hps n r
  obtain ⟨y, hy, hyle⟩ : ∃ y ∈ (hG.finite_setOf_dist_le o r).toFinset,
      p n y o * W ≤ G.degree o := by
    by_contra hcon
    push Not at hcon
    have : ∑ y ∈ (hG.finite_setOf_dist_le o r).toFinset, (G.degree y : ℝ) * G.degree o <
        ∑ y ∈ (hG.finite_setOf_dist_le o r).toFinset, (G.degree y : ℝ) * (p n y o * W) :=
      Finset.sum_lt_sum_of_nonempty ⟨o, hoR⟩ fun y hy =>
        mul_lt_mul_of_pos_left (hcon y hy) (by exact_mod_cast hdeg y)
    rw [← Finset.sum_mul] at this
    simp only [← mul_assoc] at this
    rw [← Finset.sum_mul] at this
    nlinarith
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hy
  have hpath := sq_sub_le_dist_mul_energy hG o y (fun x => p n x o)
    (F := (hG.finite_setOf_dist_le o R).toFinset)
    (fun x hx => by simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; omega)
  rw [hE] at hpath
  have hc2 : 0 ≤ c (2 * n + 1) := hpos _ _ _
  have hcn : 0 ≤ c n := hpos _ _ _
  have hEle : (c (2 * n) - c (2 * n + 1)) ≤ c n / (n + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hEnn : 0 ≤ c (2 * n) - c (2 * n + 1) := by
    have : 0 ≤ 4 * (G.degree o : ℝ) * (c (2 * n) - c (2 * n + 1)) :=
      hE ▸ Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ => sq_nonneg _
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 this
  have key : (p n o o - p n y o) ^ 2 ≤ 2 * (r / (n + 1)) * (p n o o / G.degree o) *
      (G.degree o) ^ 2 := by
    have e : 2 * ((r : ℝ) / (n + 1)) * (p n o o / G.degree o) * (G.degree o) ^ 2 =
        r * (4 * G.degree o * (c n / (n + 1))) / 2 := by
      simp only [hc]; field_simp; ring
    rw [e]
    calc (p n o o - p n y o) ^ 2 ≤ _ := hpath
      _ ≤ r * (4 * G.degree o * (c (2 * n) - c (2 * n + 1)) / 2) := by
          gcongr
      _ ≤ r * (4 * G.degree o * (c n / (n + 1))) / 2 := by
          have h4 : (0 : ℝ) ≤ r * (4 * G.degree o) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hEle h4]
  have hb : p n y o / G.degree o ≤ 1 / W := by
    rw [div_le_div_iff₀ hdo hWpos]; linarith
  have := le_two_div_add_two_mul_of_sq_sub_le (a := p n o o / G.degree o) (t := r / (n + 1))
    (b := p n y o / G.degree o) (div_nonneg (hpos _ _ _) hdo.le) hb
    (by positivity) (by
      rw [div_sub_div_same, div_pow, div_le_iff₀ (by positivity)]; exact key)
  rw [mul_div_assoc]
  exact this

end Upper

section Lower

variable [DecidableEq V] (Q : (V → ℝ) → V → ℝ) (p : ℕ → V → V → ℝ) (hG : G.Connected) (o : V)
  (ρ : ℕ) (s : ℕ → V → ℝ≥0∞)

omit [DecidableEq V] in
theorem survival_eq_zero (hs0 : ∀ x, s 0 x = if G.dist o x ≤ ρ then 1 else 0)
    (hss : ∀ n x, s (n + 1) x = if G.dist o x ≤ ρ then
      s n x / 2 + (∑ z ∈ G.neighborFinset x, s n z) / (2 * G.degree x) else 0)
    {x : V} (hx : ¬ G.dist o x ≤ ρ) (n : ℕ) : s n x = 0 := by
  cases n with
  | zero => simp [hs0, hx]
  | succ n => simp [hss, hx]

omit [DecidableEq V] in
/-- Markov property at time `n` for the killed lazy walk, in tail-sum form:
`∑_j s (n + j) x ≤ M · s n x` with `M = sup_{y ∈ B(ρ)} ∑_j s j y`. -/
theorem tsum_survival_add_le (hs0 : ∀ x, s 0 x = if G.dist o x ≤ ρ then 1 else 0)
    (hss : ∀ n x, s (n + 1) x = if G.dist o x ≤ ρ then
      s n x / 2 + (∑ z ∈ G.neighborFinset x, s n z) / (2 * G.degree x) else 0)
    (n : ℕ) (x : V) :
    ∑' j, s (n + j) x ≤ (⨆ y, ⨆ (_ : G.dist o y ≤ ρ), ∑' j, s j y) * s n x := by
  set M := ⨆ y, ⨆ (_ : G.dist o y ≤ ρ), ∑' j, s j y with hM
  induction n generalizing x with
  | zero =>
    by_cases hx : G.dist o x ≤ ρ
    · simp only [zero_add, hs0, hx, ↓reduceIte, mul_one]
      exact le_iSup₂ (f := fun y (_ : G.dist o y ≤ ρ) => ∑' j, s j y) x hx
    · simp [survival_eq_zero o ρ s hs0 hss hx]
  | succ n ih =>
    by_cases hx : G.dist o x ≤ ρ
    · have e : ∀ j, s (n + 1 + j) x =
          s (n + j) x * 2⁻¹ +
            (∑ z ∈ G.neighborFinset x, s (n + j) z) * (2 * (G.degree x : ℝ≥0∞))⁻¹ :=
        fun j => by
          rw [show n + 1 + j = (n + j) + 1 by omega, hss]
          simp only [hx, ↓reduceIte, div_eq_mul_inv]
      simp only [e]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
        Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), hss]
      simp only [hx, ↓reduceIte, div_eq_mul_inv]
      calc (∑' j, s (n + j) x) * 2⁻¹ +
            (∑ z ∈ G.neighborFinset x, ∑' j, s (n + j) z) * (2 * (G.degree x : ℝ≥0∞))⁻¹
          ≤ M * s n x * 2⁻¹ +
              (∑ z ∈ G.neighborFinset x, M * s n z) * (2 * (G.degree x : ℝ≥0∞))⁻¹ := by
            gcongr with z hz
            · exact ih x
            · exact ih z
        _ = _ := by rw [← Finset.mul_sum]; ring
    · simp [survival_eq_zero o ρ s hs0 hss hx]

theorem survival_le_ofReal_sum (hdeg : ∀ x, 0 < G.degree x)
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (hs0 : ∀ x, s 0 x = if G.dist o x ≤ ρ then 1 else 0)
    (hss : ∀ n x, s (n + 1) x = if G.dist o x ≤ ρ then
      s n x / 2 + (∑ z ∈ G.neighborFinset x, s n z) / (2 * G.degree x) else 0)
    (n : ℕ) (x : V) :
    s n x ≤ ENNReal.ofReal (∑ y ∈ (hG.finite_setOf_dist_le o ρ).toFinset, p n x y) := by
  induction n generalizing x with
  | zero =>
    by_cases hx : G.dist o x ≤ ρ
    · simp [hs0, hx, hp0, Finset.sum_ite_eq]
    · simp [hs0, hx]
  | succ n ih =>
    by_cases hx : G.dist o x ≤ ρ
    · rw [hss]
      simp only [hx, ↓reduceIte]
      have hA : ∀ z, 0 ≤ ∑ y ∈ (hG.finite_setOf_dist_le o ρ).toFinset, p n z y :=
        fun z => Finset.sum_nonneg fun y _ => lazy_kernel_nonneg p hdeg hp0 hps n z y
      have hd : (0 : ℝ) < 2 * G.degree x := by have := hdeg x; positivity
      have eq : ∑ y ∈ (hG.finite_setOf_dist_le o ρ).toFinset, p (n + 1) x y =
          (∑ y ∈ (hG.finite_setOf_dist_le o ρ).toFinset, p n x y) / 2 +
            (∑ z ∈ G.neighborFinset x,
              ∑ y ∈ (hG.finite_setOf_dist_le o ρ).toFinset, p n z y) / (2 * G.degree x) := by
        simp only [hps, Finset.sum_add_distrib, ← Finset.sum_div]
        rw [Finset.sum_comm]
      rw [eq, ENNReal.ofReal_add (div_nonneg (hA x) two_pos.le)
        (div_nonneg (Finset.sum_nonneg fun z _ => hA z) hd.le), ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_sum_of_nonneg fun z _ => hA z]
      have h2 : ENNReal.ofReal 2 = 2 := by simp
      have hdd : ENNReal.ofReal (2 * G.degree x) = 2 * G.degree x := by
        rw [ENNReal.ofReal_mul two_pos.le, h2]; simp
      rw [h2, hdd]
      gcongr with z hz
      · exact ih x
      · exact ih z
    · simp [hss, hx]

include hG

/-- **Exit-time bound for the lazy return kernel.** With `u = ∑ₙ s n o` (the mean exit time
from `B(ρ)` started at `o`) and `M = sup_{x ∈ B(ρ)} ∑ₙ s n x`,
`(u - n)₊² / (M² V(ρ)) ≤ p (2n) o o / deg o`. -/
theorem lazy_return_ge (hdeg : ∀ x, 0 < G.degree x)
    (hQ : ∀ f x, Q f x = f x / 2 + (∑ z ∈ G.neighborFinset x, f z) / (2 * G.degree x))
    (hp0 : ∀ x y, p 0 x y = if x = y then 1 else 0)
    (hps : ∀ n x y, p (n + 1) x y =
      p n x y / 2 + (∑ z ∈ G.neighborFinset x, p n z y) / (2 * G.degree x))
    (hs0 : ∀ x, s 0 x = if G.dist o x ≤ ρ then 1 else 0)
    (hss : ∀ n x, s (n + 1) x = if G.dist o x ≤ ρ then
      s n x / 2 + (∑ z ∈ G.neighborFinset x, s n z) / (2 * G.degree x) else 0)
    (n : ℕ) :
    (∑' k, s k o - n) ^ 2 / ((⨆ y, ⨆ (_ : G.dist o y ≤ ρ), ∑' j, s j y) ^ 2 *
        ENNReal.ofReal (∑ x ∈ (hG.finite_setOf_dist_le o ρ).toFinset, (G.degree x : ℝ))) ≤
      ENNReal.ofReal (p (2 * n) o o / G.degree o) := by
  set M := ⨆ y, ⨆ (_ : G.dist o y ≤ ρ), ∑' j, s j y with hM
  set D := (hG.finite_setOf_dist_le o ρ).toFinset with hD
  set W := ∑ x ∈ D, (G.degree x : ℝ)
  have hdo : (0 : ℝ) < G.degree o := by exact_mod_cast hdeg o
  have hoD : o ∈ D := by simp [hD]
  have hWpos : 0 < W := Finset.sum_pos (fun x _ => by exact_mod_cast hdeg x) ⟨o, hoD⟩
  have hpos := lazy_kernel_nonneg p hdeg hp0 hps
  have hrow : ∀ k, ∑ y ∈ D, p k o y = ∑ y ∈ D, (G.degree y : ℝ) * p k y o / G.degree o := by
    intro k
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← degree_mul_lazy_kernel_comm Q p hG hdeg hQ hp0 hps k o y]
    field_simp
  have hS : ∀ k, s k o ≤ ENNReal.ofReal (∑ y ∈ D, (G.degree y : ℝ) * p k y o / G.degree o) :=
    fun k => (hrow k) ▸ survival_le_ofReal_sum p hG o ρ s hdeg hp0 hps hs0 hss k o
  have hle1 : ∀ k, s k o ≤ 1 := by
    intro k
    refine (hS k).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.sum_div, div_le_one hdo]
    exact sum_ball_degree_mul_column_le Q p hG o hdeg hQ hp0 hps k ρ
  set σ := ∑ y ∈ D, (G.degree y : ℝ) * p n y o / G.degree o with hσ
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun y _ =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos _ _ _)) hdo.le
  -- Cauchy–Schwarz
  have hCS : σ ^ 2 / W ≤ p (2 * n) o o / G.degree o := by
    calc σ ^ 2 / W ≤ ∑ y ∈ D, ((G.degree y : ℝ) * p n y o / G.degree o) ^ 2 / G.degree y :=
          sq_sum_div_le_sum_sq_div D _ fun y _ => by exact_mod_cast hdeg y
      _ = ∑ y ∈ D, (G.degree y : ℝ) * p n y o * p n y o / (G.degree o) ^ 2 := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have : (G.degree y : ℝ) ≠ 0 := by exact_mod_cast (hdeg y).ne'
          field_simp
      _ ≤ ∑ y ∈ (hG.finite_setOf_dist_le o (2 * n + ρ)).toFinset,
            (G.degree y : ℝ) * p n y o * p n y o / (G.degree o) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => by
            have := hpos n y o; positivity
          intro y hy
          simp only [hD, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hy ⊢
          omega
      _ = p (2 * n) o o / G.degree o := by
          rw [← Finset.sum_div, sum_ball_degree_mul_column_mul_column Q p hG o hdeg hQ hp0 hps
            n n (by omega), show n + n = 2 * n by omega]
          field_simp
  have hu : ∑' k, s k o ≤ n + M * s n o := by
    rw [← (ENNReal.summable (f := fun i => s (i + n) o)).sum_add_tsum_nat_add']
    gcongr
    · calc ∑ k ∈ Finset.range n, s k o ≤ ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun k _ => hle1 k
        _ = n := by simp
    · simpa [add_comm] using tsum_survival_add_le o ρ s hs0 hss n o
  have h1 : ∑' k, s k o - n ≤ M * ENNReal.ofReal σ :=
    tsub_le_iff_left.2 (hu.trans (by gcongr; exact hS n))
  have hWne : ENNReal.ofReal W ≠ 0 := by simpa using hWpos
  rcases eq_or_ne M 0 with hM0 | hM0
  · rw [hM0, zero_mul, nonpos_iff_eq_zero] at h1
    simp [h1]
  rcases eq_or_ne M ⊤ with hMt | hMt
  · rw [hMt]
    simp [ENNReal.top_mul hWne]
  calc (∑' k, s k o - n) ^ 2 / (M ^ 2 * ENNReal.ofReal W)
      ≤ (M * ENNReal.ofReal σ) ^ 2 / (M ^ 2 * ENNReal.ofReal W) := by gcongr
    _ = ENNReal.ofReal σ ^ 2 / ENNReal.ofReal W := by
        rw [mul_pow, ENNReal.mul_div_mul_left _ _ (pow_ne_zero 2 hM0) (ENNReal.pow_ne_top hMt)]
    _ = ENNReal.ofReal (σ ^ 2 / W) := by
        rw [ENNReal.ofReal_div_of_pos hWpos, ENNReal.ofReal_pow hσ0]
    _ ≤ ENNReal.ofReal (p (2 * n) o o / G.degree o) := ENNReal.ofReal_le_ofReal hCS

end Lower

end PercLib.Probability
