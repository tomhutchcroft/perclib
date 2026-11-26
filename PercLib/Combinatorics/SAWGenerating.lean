/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied. Source of the statements:
N. Madras and G. Slade, *The Self-Avoiding Walk* (1993), §1.2 (locators to be checked).
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import PercLib.Models.ConnectiveConstant

/-!
# Uniform fixed-length self-avoiding walks and their generating functions

Self-avoiding walks of length `n` from the origin of `ℤ^d` are the paths
`{p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n}` used in
`PercLib.Models.ConnectiveConstant`; `c_n(x)` is
`Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n}`. Laws on walks are `PMF`s on
`Σ y, (zdGraph d).Walk 0 y`. No new definition is introduced.

## Main results

* `PMF.exists_apply_eq_ite_of_finite`, `PMF.filter_apply_of_apply_eq_ite`,
  `PMF.map_apply_of_apply_eq_ite`: the uniform law on a finite nonempty set, its conditioning
  on a set and its image law.
* `SimpleGraph.card_walks_length_eq_pow`: a `k`-regular locally finite graph has `k ^ n`
  walks of length `n` from each vertex.
* `PercLib.Models.Site.card_paths_to_length_zero`: `c_0(x) = 1_{x = 0}`.
* `PercLib.Models.Site.card_paths_eq_tsum`: `c_n = ∑_x c_n(x)`.
* `PercLib.Models.Site.tsum_tsum_card_paths_to_mul_pow`: `∑_x ∑_n c_n(x) z^n = ∑_n c_n z^n`.
* `PercLib.Models.Site.filter_isPath_apply`: the simple random walk law at horizon `n`,
  conditioned on self-avoidance, is the uniform law on self-avoiding walks of length `n`.
* `PercLib.Models.Site.map_take_apply`: under that uniform law, the law of the first `k`
  steps gives a prefix the number of its self-avoiding continuations divided by `c_n`.
* `PercLib.Models.Site.exists_map_take_ne`: in `ℤ^2`, at horizon `8`, a trapped prefix of
  length `7` has weight zero and a straight one has positive weight.
-/

@[expose] public section

open SimpleGraph
open scoped ENNReal

section General

variable {α β : Type*}

/-- Summing the constant `c` over a finite set gives `|s| c`. -/
theorem ENNReal.tsum_ite_mem_const {s : Set α} [DecidablePred (· ∈ s)] (hs : s.Finite)
    (c : ℝ≥0∞) :
    ∑' a, (if a ∈ s then c else 0) = (Nat.card s : ℝ≥0∞) * c := by
  have : Finite s := hs
  have h1 : ∑' a, (if a ∈ s then c else 0) = ∑' a : s, c := by
    rw [tsum_subtype s (fun _ => c)]
    exact tsum_congr fun a => by by_cases ha : a ∈ s <;> simp [ha]
  rw [h1, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  norm_cast

/-- **The uniform law on a finite nonempty set** exists. -/
theorem PMF.exists_apply_eq_ite_of_finite {s : Set α} [DecidablePred (· ∈ s)] (hs : s.Finite)
    (hne : s.Nonempty) :
    ∃ P : PMF α, ∀ a, P a = if a ∈ s then (Nat.card s : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have : Finite s := hs
  have : Nonempty s := hne.to_subtype
  have hN : (Nat.card s : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)
  refine ⟨⟨fun a => if a ∈ s then (Nat.card s : ℝ≥0∞)⁻¹ else 0, ?_⟩, fun _ => rfl⟩
  rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_ite_mem_const hs]
  exact ENNReal.mul_inv_cancel hN (by simp)

/-- **Conditioning a uniform law** on a set `t` gives the uniform law on `s ∩ t`. -/
theorem PMF.filter_apply_of_apply_eq_ite {Q : PMF α} {s t : Set α} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ s ∩ t)] {c : ℝ≥0∞}
    (hs : s.Finite) (hQ : ∀ a, Q a = if a ∈ s then c else 0)
    (h : ∃ a ∈ t, a ∈ Q.support) (a : α) :
    Q.filter t h a = if a ∈ s ∩ t then (Nat.card ↥(s ∩ t) : ℝ≥0∞)⁻¹ else 0 := by
  classical
  obtain ⟨a₀, ha₀t, ha₀⟩ := h
  rw [PMF.mem_support_iff, hQ] at ha₀
  have ha₀s : a₀ ∈ s := by by_contra hc; simp [hc] at ha₀
  have hc0 : c ≠ 0 := by simpa [ha₀s] using ha₀
  have hctop : c ≠ ⊤ := by
    have := Q.apply_ne_top a₀
    rw [hQ] at this
    simpa [ha₀s] using this
  have hind : ∀ b, t.indicator Q b = if b ∈ s ∩ t then c else 0 := by
    intro b
    by_cases hb : b ∈ t <;> by_cases hb' : b ∈ s <;> simp [hb, hb', hQ]
  have hN : (Nat.card ↥(s ∩ t) : ℝ≥0∞) ≠ 0 := by
    have : Finite ↥(s ∩ t) := hs.subset Set.inter_subset_left
    have : Nonempty ↥(s ∩ t) := ⟨⟨a₀, ha₀s, ha₀t⟩⟩
    exact Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)
  rw [PMF.filter_apply, hind, tsum_congr hind,
    ENNReal.tsum_ite_mem_const (hs.subset Set.inter_subset_left)]
  split_ifs
  · rw [ENNReal.mul_inv (Or.inl hN) (Or.inr hc0), mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel hc0 hctop, mul_one]
  · simp

/-- **Image of a uniform law**: the image of the uniform law with weight `c` on a finite set
`s` gives `b` the weight `c` times the number of points of `s` sent to `b`. -/
theorem PMF.map_apply_of_apply_eq_ite {P : PMF α} {s : Set α} [DecidablePred (· ∈ s)] {c : ℝ≥0∞}
    (hs : s.Finite) (hP : ∀ a, P a = if a ∈ s then c else 0) (f : α → β) (b : β) :
    P.map f b = (Nat.card {a // a ∈ s ∧ f a = b} : ℝ≥0∞) * c := by
  classical
  rw [PMF.map_apply]
  have hu : {a | a ∈ s ∧ f a = b}.Finite := hs.subset fun _ h => h.1
  rw [show (Nat.card {a // a ∈ s ∧ f a = b} : ℝ≥0∞) = Nat.card ↥{a | a ∈ s ∧ f a = b} from rfl,
    ← ENNReal.tsum_ite_mem_const hu]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ s <;> by_cases hb : f a = b <;> simp [ha, hb, hP, eq_comm]

/-- In a `k`-regular locally finite graph there are finitely many walks of length `n` from a
vertex, and `k ^ n` of them. -/
theorem SimpleGraph.finite_and_card_walks_length_eq_pow {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] {k : ℕ} (hk : ∀ v, G.degree v = k) (n : ℕ) (x : V) :
    Finite {w : Σ y, G.Walk x y // w.2.length = n} ∧
      Nat.card {w : Σ y, G.Walk x y // w.2.length = n} = k ^ n := by
  classical
  induction n generalizing x with
  | zero =>
    have hu : ∀ w : {w : Σ y, G.Walk x y // w.2.length = 0}, w = ⟨⟨x, .nil⟩, rfl⟩ := by
      rintro ⟨⟨y, _ | ⟨h, p⟩⟩, hl⟩
      · rfl
      · simp at hl
    have : Unique {w : Σ y, G.Walk x y // w.2.length = 0} := ⟨⟨⟨⟨x, .nil⟩, rfl⟩⟩, hu⟩
    exact ⟨inferInstance, Nat.card_unique.trans (pow_zero k).symm⟩
  | succ n ih =>
    let f : (Σ v : G.neighborSet x, {w : Σ y, G.Walk v.1 y // w.2.length = n}) →
        {w : Σ y, G.Walk x y // w.2.length = n + 1} := fun w =>
      ⟨⟨w.2.1.1, .cons ((mem_neighborSet G x _).1 w.1.2) w.2.1.2⟩, by
        change (Walk.cons _ w.2.1.2).length = n + 1
        rw [Walk.length_cons, w.2.2]⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨⟨v, h⟩, ⟨⟨y, p⟩, hp⟩⟩ ⟨⟨v', h'⟩, ⟨⟨y', p'⟩, hp'⟩⟩ he
        simp only [f, Subtype.mk.injEq, Sigma.mk.injEq] at he
        obtain ⟨rfl, he⟩ := he
        obtain ⟨rfl, hpp⟩ := Walk.cons.inj (eq_of_heq he)
        cases hpp
        rfl
      · rintro ⟨⟨y, _ | ⟨h, p⟩⟩, hl⟩
        · simp at hl
        · exact ⟨⟨⟨_, h⟩, ⟨⟨y, p⟩, by simpa using hl⟩⟩, rfl⟩
    have hfin : ∀ v : G.neighborSet x, Finite {w : Σ y, G.Walk v.1 y // w.2.length = n} :=
      fun v => (ih v.1).1
    refine ⟨Finite.of_surjective f hf.2, ?_⟩
    rw [← Nat.card_eq_of_bijective f hf, Nat.card_sigma]
    simp_rw [fun v : G.neighborSet x => (ih v.1).2]
    rw [Finset.sum_const, Finset.card_univ, card_neighborSet_eq_degree, hk, smul_eq_mul,
      pow_succ, mul_comm]

/-- **Walk count of a regular graph**: `k ^ n` walks of length `n` from each vertex. -/
theorem SimpleGraph.card_walks_length_eq_pow {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] {k : ℕ} (hk : ∀ v, G.degree v = k) (n : ℕ) (x : V) :
    Nat.card {w : Σ y, G.Walk x y // w.2.length = n} = k ^ n :=
  (G.finite_and_card_walks_length_eq_pow hk n x).2

end General

namespace PercLib.Models.Site

variable {d : ℕ}

/-- `c_0(x) = 1_{x = 0}`: the length-zero walk is the only path of length zero. -/
theorem card_paths_to_length_zero (x : Fin d → ℤ) :
    Nat.card {q : (zdGraph d).Path 0 x // q.1.length = 0} = if x = 0 then 1 else 0 := by
  split_ifs with hx
  · subst hx
    have hu : ∀ q : {q : (zdGraph d).Path 0 0 // q.1.length = 0}, q = ⟨Path.nil, rfl⟩ := by
      rintro ⟨⟨_ | ⟨h, p⟩, hp⟩, hl⟩
      · rfl
      · simp at hl
    have : Unique {q : (zdGraph d).Path 0 0 // q.1.length = 0} := ⟨⟨⟨Path.nil, rfl⟩⟩, hu⟩
    exact Nat.card_unique
  · have : IsEmpty {q : (zdGraph d).Path 0 x // q.1.length = 0} :=
      ⟨fun q => hx (Walk.eq_of_length_eq_zero q.2).symm⟩
    exact Nat.card_of_isEmpty

/-- The paths of length `n` from the origin, sorted by endpoint. -/
theorem card_paths_eq_tsum (n : ℕ) :
    (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞) =
      ∑' x, (Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n} : ℝ≥0∞) := by
  have hT := finite_paths_length d n 0
  have hfin : ∀ x, Finite {q : (zdGraph d).Path 0 x // q.1.length = n} := fun x =>
    Finite.of_injective (fun q => (⟨⟨x, q.1⟩, q.2⟩ :
      {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n})) (fun q q' h => by
        have := congrArg (fun p => p.1) h
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
        exact Subtype.ext this)
  have h1 : ∀ x, (Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n} : ℝ≥0∞) =
      ∑' _ : {q : (zdGraph d).Path 0 x // q.1.length = n}, (1 : ℝ≥0∞) := by
    intro x
    rw [ENNReal.tsum_one, ENat.card_eq_coe_natCard]
    simp
  simp_rw [h1]
  rw [← ENNReal.tsum_sigma' (fun _ => (1 : ℝ≥0∞)), ENNReal.tsum_one]
  let e : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} ≃
      Σ x, {q : (zdGraph d).Path 0 x // q.1.length = n} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Nat.card_congr e
  have : Finite (Σ x, {q : (zdGraph d).Path 0 x // q.1.length = n}) := Finite.of_equiv _ e
  rw [hc, ENat.card_eq_coe_natCard]
  simp

/-- **Tonelli for the self-avoiding generating functions**:
`∑_x ∑_n c_n(x) z^n = ∑_n c_n z^n` in `[0, ∞]`. -/
theorem tsum_tsum_card_paths_to_mul_pow (z : ℝ≥0∞) :
    ∑' x, ∑' n, (Nat.card {q : (zdGraph d).Path 0 x // q.1.length = n} : ℝ≥0∞) * z ^ n =
      ∑' n, (Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞) *
        z ^ n := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun n => ?_
  rw [ENNReal.tsum_mul_right, card_paths_eq_tsum]

/-- `ℤ^d` has `(2d)^n` nearest-neighbour walks of length `n` from the origin. -/
theorem card_walks_length (d n : ℕ) :
    Nat.card {w : Σ y, (zdGraph d).Walk 0 y // w.2.length = n} = (2 * d) ^ n := by
  classical
  let : (zdGraph d).LocallyFinite := fun v => (zdGraph_finite_neighborSet v).fintype
  exact (zdGraph d).card_walks_length_eq_pow (fun v => zdGraph_degree d v) n 0

/-- The walks of length `n` from the origin of `ℤ^d` form a finite set. -/
theorem finite_walks_length (d n : ℕ) :
    {w : Σ y, (zdGraph d).Walk 0 y | w.2.length = n}.Finite := by
  classical
  let : (zdGraph d).LocallyFinite := fun v => (zdGraph_finite_neighborSet v).fintype
  exact Set.finite_coe_iff.mp
    ((zdGraph d).finite_and_card_walks_length_eq_pow (fun v => zdGraph_degree d v) n 0).1

/-- The self-avoiding walks of length `n`, viewed among all walks, number `c_n`. -/
theorem card_isPath_walks_length (n : ℕ) :
    Nat.card {w : Σ y, (zdGraph d).Walk 0 y // w.2.IsPath ∧ w.2.length = n} =
      Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} :=
  Nat.card_congr
    { toFun := fun w => ⟨⟨w.1.1, ⟨w.1.2, w.2.1⟩⟩, w.2.2⟩
      invFun := fun p => ⟨⟨p.1.1, p.1.2.1⟩, ⟨p.1.2.2, p.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Simple random walk at horizon `n`**: for `d ≥ 1` there is a law on walks from the
origin giving each nearest-neighbour walk of length `n` the probability `(2d)^{-n}`. -/
theorem exists_pmf_walk_eq_ite (hd : 1 ≤ d) (n : ℕ) :
    ∃ Q : PMF (Σ y, (zdGraph d).Walk 0 y),
      ∀ w, Q w = if w.2.length = n then ((2 * d : ℝ≥0∞) ^ n)⁻¹ else 0 := by
  have hne : {w : Σ y, (zdGraph d).Walk 0 y | w.2.length = n}.Nonempty := by
    have h0 : Nat.card {w : Σ y, (zdGraph d).Walk 0 y // w.2.length = n} ≠ 0 := by
      rw [card_walks_length]
      exact pow_ne_zero _ (by omega)
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 h0).1
    exact ⟨w, hw⟩
  obtain ⟨Q, hQ⟩ := PMF.exists_apply_eq_ite_of_finite (finite_walks_length d n) hne
  refine ⟨Q, fun w => ?_⟩
  rw [hQ]
  have hc : Nat.card ↥{w : Σ y, (zdGraph d).Walk 0 y | w.2.length = n} = (2 * d) ^ n :=
    card_walks_length d n
  rw [hc]
  push_cast
  rfl

/-- The self-avoiding walks of length `n` form a finite set of walks. -/
theorem finite_isPath_walks_length (d n : ℕ) :
    {w : Σ y, (zdGraph d).Walk 0 y | w.2.IsPath ∧ w.2.length = n}.Finite :=
  (finite_walks_length d n).subset fun _ h => h.2

/-- **The uniform law on self-avoiding walks of length `n`** exists for `d ≥ 1`. -/
theorem exists_pmf_path_eq_ite (hd : 1 ≤ d) (n : ℕ) :
    ∃ P : PMF (Σ y, (zdGraph d).Walk 0 y),
      ∀ w, P w = if w.2.IsPath ∧ w.2.length = n then
        ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹ else 0 := by
  have hc := card_isPath_walks_length (d := d) n
  have hpos := one_le_card_paths hd n
  have hne : {w : Σ y, (zdGraph d).Walk 0 y | w.2.IsPath ∧ w.2.length = n}.Nonempty := by
    have h0 : Nat.card {w : Σ y, (zdGraph d).Walk 0 y // w.2.IsPath ∧ w.2.length = n} ≠ 0 := by
      omega
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 h0).1
    exact ⟨w, hw⟩
  obtain ⟨P, hP⟩ := PMF.exists_apply_eq_ite_of_finite (finite_isPath_walks_length d n) hne
  exact ⟨P, fun w => by rw [hP, ← hc]; rfl⟩

/-- **The uniform self-avoiding law is simple random walk conditioned on self-avoidance**:
conditioning the law giving each walk of length `n` the probability `(2d)^{-n}` on the
walk being a path gives each self-avoiding walk of length `n` the probability `1 / c_n`. -/
theorem filter_isPath_apply {Q : PMF (Σ y, (zdGraph d).Walk 0 y)} {n : ℕ}
    (hQ : ∀ w, Q w = if w.2.length = n then ((2 * d : ℝ≥0∞) ^ n)⁻¹ else 0)
    (h : ∃ w ∈ {w : Σ y, (zdGraph d).Walk 0 y | w.2.IsPath}, w ∈ Q.support)
    (w : Σ y, (zdGraph d).Walk 0 y) :
    Q.filter {w | w.2.IsPath} h w = if w.2.IsPath ∧ w.2.length = n then
      ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹ else 0 := by
  have hcard : Nat.card ↥({w : Σ y, (zdGraph d).Walk 0 y | w.2.length = n} ∩
      {w | w.2.IsPath}) = Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)).trans
      (card_isPath_walks_length n)
  have hmem : w ∈ ({w : Σ y, (zdGraph d).Walk 0 y | w.2.length = n} ∩ {w | w.2.IsPath}) ↔
      (w.2.IsPath ∧ w.2.length = n) := and_comm
  rw [PMF.filter_apply_of_apply_eq_ite (finite_walks_length d n) hQ h, hcard]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hmem.1 h1) h2
  · exact absurd (hmem.2 h2) h1
  · rfl

/-- **Marginal of the uniform self-avoiding law on its first `k` steps**: a prefix gets
`c_n⁻¹` times the number of self-avoiding walks of length `n` extending it. -/
theorem map_take_apply {P : PMF (Σ y, (zdGraph d).Walk 0 y)} {n : ℕ}
    (hP : ∀ w, P w = if w.2.IsPath ∧ w.2.length = n then
      ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹ else 0)
    (k : ℕ) (p : Σ y, (zdGraph d).Walk 0 y) :
    P.map (fun w => ⟨w.2.getVert k, w.2.take k⟩) p =
      (Nat.card {w : Σ y, (zdGraph d).Walk 0 y //
        (w.2.IsPath ∧ w.2.length = n) ∧ (⟨w.2.getVert k, w.2.take k⟩ :
          Σ y, (zdGraph d).Walk 0 y) = p} : ℝ≥0∞) *
      ((Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} : ℝ≥0∞))⁻¹ :=
  PMF.map_apply_of_apply_eq_ite (finite_isPath_walks_length d n)
    (fun w => by rw [hP]; rfl) _ p

/-- Finitely many self-avoiding walks of length `n` start with a given prefix. -/
theorem finite_isPath_take (n k : ℕ) (p : Σ y, (zdGraph d).Walk 0 y) :
    Finite {w : Σ y, (zdGraph d).Walk 0 y //
      (w.2.IsPath ∧ w.2.length = n) ∧ (⟨w.2.getVert k, w.2.take k⟩ :
        Σ y, (zdGraph d).Walk 0 y) = p} :=
  have : Finite ↥{w : Σ y, (zdGraph d).Walk 0 y | w.2.IsPath ∧ w.2.length = n} :=
    (finite_isPath_walks_length d n).to_subtype
  Finite.of_injective (fun w => (⟨w.1, w.2.1⟩ :
    ↥{w : Σ y, (zdGraph d).Walk 0 y | w.2.IsPath ∧ w.2.length = n}))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))

/-- **A trapped prefix has no continuation**: if every neighbour of the endpoint of a walk
`p` of length `k` lies on `p`, no self-avoiding walk of length `k + 1` starts with `p`. -/
theorem card_isPath_take_eq_zero_of_trapped {k : ℕ} {p : Σ y, (zdGraph d).Walk 0 y}
    (htrap : ∀ y, (zdGraph d).Adj p.1 y → y ∈ p.2.support) :
    Nat.card {w : Σ y, (zdGraph d).Walk 0 y //
      (w.2.IsPath ∧ w.2.length = k + 1) ∧ (⟨w.2.getVert k, w.2.take k⟩ :
        Σ y, (zdGraph d).Walk 0 y) = p} = 0 := by
  have : IsEmpty {w : Σ y, (zdGraph d).Walk 0 y //
      (w.2.IsPath ∧ w.2.length = k + 1) ∧ (⟨w.2.getVert k, w.2.take k⟩ :
        Σ y, (zdGraph d).Walk 0 y) = p} := by
    refine ⟨fun ⟨w, ⟨hw, hl⟩, ht⟩ => ?_⟩
    have h1 : w.2.getVert k = p.1 := congrArg Sigma.fst ht
    have h2 : (w.2.take k).support = p.2.support :=
      congrArg (fun s : Σ y, (zdGraph d).Walk 0 y => s.2.support) ht
    have hadj := w.2.adj_getVert_succ (i := k) (by omega)
    rw [h1] at hadj
    have hmem := htrap _ hadj
    rw [← h2, Walk.mem_support_iff_exists_getVert] at hmem
    obtain ⟨j, hj, hjl⟩ := hmem
    rw [Walk.take_getVert, Walk.take_length] at *
    have := hw.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hj
    omega
  exact Nat.card_of_isEmpty

/-- **The marginal at a smaller horizon is not uniform**: in `ℤ^2`, under the uniform law on
self-avoiding walks of length `8`, a trapped self-avoiding prefix of length `7` has weight
zero while the straight one has positive weight. -/
theorem exists_map_take_ne :
    ∃ p₁ p₂ : Σ y, (zdGraph 2).Walk 0 y,
      (p₁.2.IsPath ∧ p₁.2.length = 7) ∧ (p₂.2.IsPath ∧ p₂.2.length = 7) ∧
      ∀ P : PMF (Σ y, (zdGraph 2).Walk 0 y),
        (∀ w, P w = if w.2.IsPath ∧ w.2.length = 8 then
          ((Nat.card {p : Σ y, (zdGraph 2).Path 0 y // p.2.1.length = 8} : ℝ≥0∞))⁻¹
          else 0) →
        P.map (fun w => ⟨w.2.getVert 7, w.2.take 7⟩) p₁ = 0 ∧
          P.map (fun w => ⟨w.2.getVert 7, w.2.take 7⟩) p₂ ≠ 0 := by
  refine ⟨⟨![-1, 0], .cons ((zdGraph_adj_iff_l1 0 ![0, 1]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![-1, 1]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![-2, 1]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![-2, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![-2, -1]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![-1, -1]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![-1, 0]).2 (by decide)) .nil⟩,
    ⟨![7, 0], .cons ((zdGraph_adj_iff_l1 0 ![1, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![2, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![3, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![4, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![5, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![6, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![7, 0]).2 (by decide)) .nil⟩,
    ⟨by rw [Walk.isPath_def]; decide, rfl⟩, ⟨by rw [Walk.isPath_def]; decide, rfl⟩,
    fun P hP => ⟨?_, ?_⟩⟩
  · rw [map_take_apply hP, card_isPath_take_eq_zero_of_trapped, Nat.cast_zero, zero_mul]
    intro y hy
    rw [zdGraph_adj_iff_eq_update] at hy
    obtain ⟨⟨i, b⟩, rfl⟩ := hy
    fin_cases i <;> cases b <;> decide
  · rw [map_take_apply hP]
    refine mul_ne_zero ?_ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    refine Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨⟨![8, 0],
      .cons ((zdGraph_adj_iff_l1 0 ![1, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![2, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![3, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![4, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![5, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![6, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![7, 0]).2 (by decide)) <|
      .cons ((zdGraph_adj_iff_l1 _ ![8, 0]).2 (by decide)) .nil⟩,
      ⟨by rw [Walk.isPath_def]; decide, rfl⟩, rfl⟩⟩, finite_isPath_take 8 7 _⟩)

end PercLib.Models.Site
