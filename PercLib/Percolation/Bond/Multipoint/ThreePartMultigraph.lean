/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. Statement from the wiki article `multipoint-trees` (the
regular multigraph expansion); T. Hutchcroft, *Critical long-range percolation II*,
arXiv:2508.18808v1, (II.3.3). No upstream proof is copied and no definition is added.
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Three-part product inequalities yield the regular multigraph bound

Let `A` be a finite set with `n ≥ 2` elements and `t` a nonnegative function on the subsets of
`A` with at least two elements. Suppose every `B ⊆ A` with `|B| ≥ 3` admits a partition
`B = B₁ ⊔ B₂ ⊔ B₃` into nonempty parts with
`t(B)² ≤ K_{|B|} t(B₁ ∪ B₂) t(B₁ ∪ B₃) t(B₂ ∪ B₃)`. Then `t(A) ^ 2 ^ (n - 2)` is at most a
constant, depending only on `n` and `K`, times the sum over all connected loopless multigraphs
on `A` that are `2 ^ (n - 2)`-regular of the pair-weight monomials `∏ t({x, y}) ^ q_{xy}`.

A multigraph is a finitely supported multiplicity function `q : Sym2 α →₀ ℕ`; it is loopless and
lives on `A` when every edge in its support is off the diagonal with both ends in `A`, its degree
at `x ∈ A` is `∑ y ∈ A, q s(x, y)`, and it is connected when any two points of `A` are joined in
the simple graph of the edges of positive multiplicity.

The proof is the induction of the wiki article, run in its "maximal term" form: one shows that a
single regular multigraph `Q` already satisfies `t(A) ^ 2 ^ (n - 2) ≤ C ∏ t(e) ^ Q e`. For a
pairwise union `U` of size `m` the inductive multigraph is taken `2 ^ (n - m - 1)` times; the
three resulting multigraphs add up to one that is regular of degree `2 ^ (n - 2)`, because every
point lies in exactly two pairwise unions.

## Main results

* `finite_setOf_regularMultigraph`: there are finitely many loopless multigraphs on `A` of
  given constant degree;
* `exists_regularMultigraph_pow_le`: the maximal-term form of the bound, uniformly for all
  subsets of size at most `n`;
* `pow_le_mul_finsum_regularMultigraph`: the regular multigraph bound;
* `le_mul_finsum_prod_rpow_regularMultigraph`: its root form
  `t(A) ≤ C ∑_Q ∏ t({x, y}) ^ (q_{xy} / 2 ^ (n - 2))`.
-/

@[expose] public section

noncomputable section

open Finset

universe u

namespace PercLib.Percolation.Bond

variable {α : Type u} [DecidableEq α]

/-- The degree inside `B` of a multigraph whose edges have both ends in `B' ⊆ B` is its degree
inside `B'` at points of `B'`, and zero elsewhere. -/
theorem sum_apply_mk_eq_ite_of_support_subset {q : Sym2 α →₀ ℕ} {B B' : Finset α}
    (hBB : B' ⊆ B) (hq : ∀ e ∈ q.support, ∀ x ∈ e, x ∈ B') (x : α) :
    ∑ y ∈ B, q s(x, y) = if x ∈ B' then ∑ y ∈ B', q s(x, y) else 0 := by
  split_ifs with hx
  · symm
    refine Finset.sum_subset hBB fun y _ hy => ?_
    by_contra h
    exact hy (hq _ (Finsupp.mem_support_iff.2 h) y (Sym2.mem_mk_right x y))
  · refine Finset.sum_eq_zero fun y _ => ?_
    by_contra h
    exact hx (hq _ (Finsupp.mem_support_iff.2 h) x (Sym2.mem_mk_left x y))

/-- The pair-weight monomial of a loopless multigraph on `B ⊆ A` is nonnegative when `t` is
nonnegative on the subsets of `A` with at least two elements. -/
theorem prod_pow_nonneg_of_support {A B : Finset α} {t : Finset α → ℝ}
    (ht : ∀ B' ⊆ A, 2 ≤ B'.card → 0 ≤ t B') (hBA : B ⊆ A) {q : Sym2 α →₀ ℕ}
    (hq : ∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ B) :
    0 ≤ q.prod fun e k => t e.toFinset ^ k := by
  unfold Finsupp.prod
  exact Finset.prod_nonneg fun e he => pow_nonneg (ht _
    (fun x hx => hBA ((hq e he).2 x (Sym2.mem_toFinset.1 hx)))
    (Sym2.card_toFinset_of_not_isDiag e (hq e he).1).ge) _

/-- On a two-point set the single edge is a connected loopless `1`-regular multigraph whose
pair-weight monomial is `t` of the set. -/
theorem exists_regularMultigraph_of_card_eq_two (t : Finset α → ℝ) {B : Finset α}
    (hB : B.card = 2) : ∃ q : Sym2 α →₀ ℕ,
      ((∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ B) ∧
        (∀ x ∈ B, ∑ y ∈ B, q s(x, y) = 1) ∧
        ∀ x ∈ B, ∀ y ∈ B, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y) ∧
      (q.prod fun e k => t e.toFinset ^ k) = t B := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hB
  refine ⟨Finsupp.single s(x, y) 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at he
    subst he
    refine ⟨Sym2.mk_isDiag_iff.not.2 hxy, fun z hz => ?_⟩
    rcases Sym2.mem_iff.1 hz with rfl | rfl <;> simp
  · intro z hz
    rw [Finset.sum_pair hxy]
    rcases Finset.mem_insert.1 hz with rfl | hz
    · simp [hxy]
    · rw [Finset.mem_singleton] at hz
      subst hz
      simp [Ne.symm hxy, Sym2.eq_swap]
  · have hadj : (SimpleGraph.fromRel fun u v =>
        (Finsupp.single s(x, y) 1 : Sym2 α →₀ ℕ) s(u, v) ≠ 0).Adj x y := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hxy, Or.inl (by simp)⟩
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [.refl _, hadj.reachable, hadj.reachable.symm, .refl _]
  · rw [Finsupp.prod_single_index (h := fun (e : Sym2 α) (k : ℕ) => t e.toFinset ^ k)
      (pow_zero _), pow_one,
      Sym2.toFinset_mk_eq]

/-- There are finitely many loopless multigraphs on `A` with constant degree `D`. -/
theorem finite_setOf_regularMultigraph (A : Finset α) (D : ℕ) :
    {q : Sym2 α →₀ ℕ | (∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ A) ∧
      (∀ x ∈ A, ∑ y ∈ A, q s(x, y) = D) ∧
      ∀ x ∈ A, ∀ y ∈ A, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y}.Finite := by
  refine ((Finset.range (A.sym2.card * D + 1)).finite_toSet.biUnion
    fun k _ => (A.sym2.finsuppAntidiag k).finite_toSet).subset ?_
  rintro q ⟨hsupp, hdeg, -⟩
  have hsub : q.support ⊆ A.sym2 := fun e he => Finset.mem_sym2_iff.2 (hsupp e he).2
  have hle : ∀ e ∈ A.sym2, q e ≤ D := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mk_mem_sym2_iff] at he
      rw [← hdeg x he.1]
      exact Finset.single_le_sum (f := fun z => q s(x, z)) (fun _ _ => Nat.zero_le _) he.2
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, Finset.mem_finsuppAntidiag]
  exact ⟨A.sym2.sum q, Nat.lt_succ_of_le ((Finset.sum_le_card_nsmul _ _ _ hle).trans
    (by simp)), rfl, hsub⟩

/-- The maximal-term form of the regular multigraph bound: under the three-part product
inequalities, every `B ⊆ A` with `2 ≤ |B| ≤ n` carries a connected loopless
`2 ^ (|B| - 2)`-regular multigraph `q` with `t(B) ^ 2 ^ (|B| - 2) ≤ C ∏ t(e) ^ q e`, where
`C ≥ 1` depends only on `n` and `K`. No sign condition on `K` is needed. -/
theorem exists_regularMultigraph_pow_le (K : ℕ → ℝ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {α : Type u} [DecidableEq α] (A : Finset α) (t : Finset α → ℝ),
      (∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) →
      (∀ B ⊆ A, 3 ≤ B.card → ∃ B₁ B₂ B₃ : Finset α, B₁.Nonempty ∧ B₂.Nonempty ∧ B₃.Nonempty ∧
        Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧ B₁ ∪ B₂ ∪ B₃ = B ∧
        t B ^ 2 ≤ K B.card * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) →
      ∀ B ⊆ A, 2 ≤ B.card → B.card ≤ n → ∃ q : Sym2 α →₀ ℕ,
        ((∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ B) ∧
          (∀ x ∈ B, ∑ y ∈ B, q s(x, y) = 2 ^ (B.card - 2)) ∧
          ∀ x ∈ B, ∀ y ∈ B, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y) ∧
        t B ^ 2 ^ (B.card - 2) ≤ C * q.prod fun e k => t e.toFinset ^ k := by
  induction n with
  | zero => exact ⟨1, le_rfl, fun A t _ _ B _ h2 hn => absurd (h2.trans hn) (by norm_num)⟩
  | succ n ih =>
    obtain ⟨C, hC, hih⟩ := ih
    refine ⟨max 1 (K (n + 1)) ^ 2 ^ (n - 2) * C ^ (3 * 2 ^ (n - 2)),
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _)) (one_le_pow₀ hC), ?_⟩
    intro α _ A t ht hK B hBA hB2 hBn
    have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
    have hCC : C ≤ max 1 (K (n + 1)) ^ 2 ^ (n - 2) * C ^ (3 * 2 ^ (n - 2)) := by
      calc C = 1 * C ^ 1 := by simp
        _ ≤ _ := mul_le_mul (one_le_pow₀ (le_max_left _ _))
            (pow_le_pow_right₀ hC (Nat.one_le_iff_ne_zero.2 (by positivity)))
            (by positivity) (by positivity)
    -- Subsets of size at most `n` and two-point sets.
    rcases Nat.lt_or_ge B.card (n + 1) with hlt | hge
    · obtain ⟨q, hq, hle⟩ := hih A t ht hK B hBA hB2 (Nat.lt_succ_iff.1 hlt)
      exact ⟨q, hq, hle.trans (mul_le_mul_of_nonneg_right hCC
        (prod_pow_nonneg_of_support ht hBA hq.1))⟩
    have hBc : B.card = n + 1 := le_antisymm hBn hge
    rcases Nat.lt_or_ge B.card 3 with h3 | h3
    · have hB : B.card = 2 := by omega
      obtain ⟨q, hq, heq⟩ := exists_regularMultigraph_of_card_eq_two t hB
      refine ⟨q, by rw [hB]; exact hq, ?_⟩
      rw [hB, heq]
      norm_num
      calc t B = 1 * t B := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (hCC.trans' hC) (ht B hBA hB2)
    -- The inductive step on a set of size `n + 1 ≥ 3`.
    have hn2 : 2 ≤ n := by omega
    set h := 2 ^ (n - 2) with hh
    -- Each pairwise union carries a multigraph of degree `h`.
    have key : ∀ U ⊆ B, 2 ≤ U.card → U.card ≤ n → ∃ p : Sym2 α →₀ ℕ,
        (∀ e ∈ p.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ U) ∧
        (∀ x, ∑ y ∈ B, p s(x, y) = if x ∈ U then h else 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, (SimpleGraph.fromRel fun u v => p s(u, v) ≠ 0).Reachable x y) ∧
        0 ≤ (p.prod fun e k => t e.toFinset ^ k) ∧
        t U ^ h ≤ C ^ h * p.prod fun e k => t e.toFinset ^ k := by
      intro U hUB hU2 hUn
      obtain ⟨q, ⟨hqs, hqd, hqr⟩, hle⟩ := hih A t ht hK U (hUB.trans hBA) hU2 hUn
      have hexp : 2 ^ (U.card - 2) * 2 ^ (n - U.card) = h := by
        rw [hh, ← pow_add]; congr 1; omega
      have hpe : ∀ e, (2 ^ (n - U.card) • q) e ≠ 0 ↔ q e ≠ 0 := fun e => by
        simp
      have hps : ∀ e ∈ (2 ^ (n - U.card) • q).support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ U :=
        fun e he => hqs e (Finsupp.mem_support_iff.2 ((hpe e).1 (Finsupp.mem_support_iff.1 he)))
      have hprod : ∀ j : ℕ, ((j • q).prod fun e k => t e.toFinset ^ k) =
          (q.prod fun e k => t e.toFinset ^ k) ^ j := fun j => by
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [succ_nsmul, Finsupp.prod_add_index' (fun _ => pow_zero _)
            (fun _ _ _ => pow_add _ _ _), ihj, pow_succ]
      have hw0 := prod_pow_nonneg_of_support ht (hUB.trans hBA) hqs
      refine ⟨2 ^ (n - U.card) • q, hps, fun x => ?_, fun x hx y hy => ?_,
        prod_pow_nonneg_of_support ht (hUB.trans hBA) hps, ?_⟩
      · rw [sum_apply_mk_eq_ite_of_support_subset hUB (fun e he => (hps e he).2)]
        split_ifs with hxU
        · simp only [Finsupp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hqd x hxU]
          rw [mul_comm, hexp]
        · rfl
      · refine (hqr x hx y hy).mono fun u v huv => ?_
        rw [SimpleGraph.fromRel_adj] at huv ⊢
        exact ⟨huv.1, huv.2.imp (hpe _).2 (hpe _).2⟩
      · rw [hprod, ← hexp, pow_mul]
        calc (t U ^ 2 ^ (U.card - 2)) ^ 2 ^ (n - U.card)
            ≤ (C * q.prod fun e k => t e.toFinset ^ k) ^ 2 ^ (n - U.card) :=
              pow_le_pow_left₀ (pow_nonneg (ht U (hUB.trans hBA) hU2) _) hle _
          _ = C ^ 2 ^ (n - U.card) * (q.prod fun e k => t e.toFinset ^ k) ^ 2 ^ (n - U.card) :=
              mul_pow _ _ _
          _ ≤ C ^ (2 ^ (U.card - 2) * 2 ^ (n - U.card)) *
                (q.prod fun e k => t e.toFinset ^ k) ^ 2 ^ (n - U.card) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC
                (Nat.le_mul_of_pos_left _ (by positivity))) (pow_nonneg hw0 _)
    -- The three-part inequality for `B` and the three pairwise unions.
    obtain ⟨B₁, B₂, B₃, h₁, h₂, h₃, d₁₂, d₁₃, d₂₃, hU, hle⟩ := hK B hBA (by omega)
    subst hU
    have hcB : (B₁ ∪ B₂ ∪ B₃).card = B₁.card + B₂.card + B₃.card := by
      rw [card_union_of_disjoint (disjoint_union_left.2 ⟨d₁₃, d₂₃⟩), card_union_of_disjoint d₁₂]
    have c₁ := h₁.card_pos
    have c₂ := h₂.card_pos
    have c₃ := h₃.card_pos
    have s₁₂ : B₁ ∪ B₂ ⊆ B₁ ∪ B₂ ∪ B₃ := fun x hx => by simp only [mem_union] at hx ⊢; tauto
    have s₁₃ : B₁ ∪ B₃ ⊆ B₁ ∪ B₂ ∪ B₃ := fun x hx => by simp only [mem_union] at hx ⊢; tauto
    have s₂₃ : B₂ ∪ B₃ ⊆ B₁ ∪ B₂ ∪ B₃ := fun x hx => by simp only [mem_union] at hx ⊢; tauto
    have e₁₂ := card_union_of_disjoint d₁₂
    have e₁₃ := card_union_of_disjoint d₁₃
    have e₂₃ := card_union_of_disjoint d₂₃
    obtain ⟨p₁₂, hs₁₂, hd₁₂, hr₁₂, hw₁₂, hl₁₂⟩ := key _ s₁₂ (by omega) (by omega)
    obtain ⟨p₁₃, hs₁₃, hd₁₃, hr₁₃, hw₁₃, hl₁₃⟩ := key _ s₁₃ (by omega) (by omega)
    obtain ⟨p₂₃, hs₂₃, hd₂₃, hr₂₃, hw₂₃, hl₂₃⟩ := key _ s₂₃ (by omega) (by omega)
    have hD : 2 ^ (n + 1 - 2) = h + h := by
      rw [hh, ← two_mul, ← pow_succ']; congr 1; omega
    rw [hBc]
    refine ⟨p₁₂ + p₁₃ + p₂₃, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro e he
      have he' := Finsupp.mem_support_iff.1 he
      simp only [Finsupp.add_apply] at he'
      rcases (by omega : p₁₂ e ≠ 0 ∨ p₁₃ e ≠ 0 ∨ p₂₃ e ≠ 0) with h' | h' | h'
      · exact (hs₁₂ e (Finsupp.mem_support_iff.2 h')).imp_right fun H x hx => s₁₂ (H x hx)
      · exact (hs₁₃ e (Finsupp.mem_support_iff.2 h')).imp_right fun H x hx => s₁₃ (H x hx)
      · exact (hs₂₃ e (Finsupp.mem_support_iff.2 h')).imp_right fun H x hx => s₂₃ (H x hx)
    · intro x hx
      simp only [Finsupp.add_apply, Finset.sum_add_distrib, hd₁₂, hd₁₃, hd₂₃, hD]
      simp only [mem_union] at hx
      rcases hx with (hx | hx) | hx
      · simp [hx, Finset.disjoint_left.1 d₁₂ hx, Finset.disjoint_left.1 d₁₃ hx]
      · simp [hx, Finset.disjoint_right.1 d₁₂ hx, Finset.disjoint_left.1 d₂₃ hx]
      · simp [hx, Finset.disjoint_right.1 d₁₃ hx, Finset.disjoint_right.1 d₂₃ hx]
    · have hmono : ∀ p : Sym2 α →₀ ℕ, (∀ e, p e ≠ 0 → (p₁₂ + p₁₃ + p₂₃) e ≠ 0) →
          ∀ u v, (SimpleGraph.fromRel fun u v => p s(u, v) ≠ 0).Reachable u v →
          (SimpleGraph.fromRel fun u v => (p₁₂ + p₁₃ + p₂₃) s(u, v) ≠ 0).Reachable u v :=
        fun p hp u v huv => huv.mono fun a b hab => by
          rw [SimpleGraph.fromRel_adj] at hab ⊢
          exact ⟨hab.1, hab.2.imp (hp _) (hp _)⟩
      obtain ⟨b, hb⟩ := h₁
      have hbz : ∀ z ∈ B₁ ∪ B₂ ∪ B₃, (SimpleGraph.fromRel fun u v =>
          (p₁₂ + p₁₃ + p₂₃) s(u, v) ≠ 0).Reachable b z := by
        intro z hz
        simp only [mem_union] at hz
        rcases hz with (hz | hz) | hz
        · exact hmono p₁₂ (fun e he => by simp only [Finsupp.add_apply]; omega) _ _
            (hr₁₂ b (by simp [hb]) z (by simp [hz]))
        · exact hmono p₁₂ (fun e he => by simp only [Finsupp.add_apply]; omega) _ _
            (hr₁₂ b (by simp [hb]) z (by simp [hz]))
        · exact hmono p₁₃ (fun e he => by simp only [Finsupp.add_apply]; omega) _ _
            (hr₁₃ b (by simp [hb]) z (by simp [hz]))
      intro x hx y hy
      exact (hbz x hx).symm.trans (hbz y hy)
    · have hw : ∀ q₁ q₂ : Sym2 α →₀ ℕ, ((q₁ + q₂).prod fun e k => t e.toFinset ^ k) =
          (q₁.prod fun e k => t e.toFinset ^ k) * q₂.prod fun e k => t e.toFinset ^ k :=
        fun q₁ q₂ => Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
      rw [hw, hw, hD, ← two_mul, pow_mul]
      rw [hBc] at hle
      have t₁₂ := ht _ (s₁₂.trans hBA) (by omega)
      have t₁₃ := ht _ (s₁₃.trans hBA) (by omega)
      have t₂₃ := ht _ (s₂₃.trans hBA) (by omega)
      have hCh : (0 : ℝ) ≤ C ^ h := pow_nonneg hC0 _
      calc (t (B₁ ∪ B₂ ∪ B₃) ^ 2) ^ h
          ≤ (max 1 (K (n + 1)) * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) ^ h :=
            pow_le_pow_left₀ (sq_nonneg _) (hle.trans (mul_le_mul_of_nonneg_right
              (le_max_right _ _) (mul_nonneg (mul_nonneg t₁₂ t₁₃) t₂₃))) h
        _ = max 1 (K (n + 1)) ^ h * (t (B₁ ∪ B₂) ^ h * t (B₁ ∪ B₃) ^ h * t (B₂ ∪ B₃) ^ h) := by
            rw [mul_pow, mul_pow, mul_pow]
        _ ≤ max 1 (K (n + 1)) ^ h * ((C ^ h * p₁₂.prod fun e k => t e.toFinset ^ k) *
              (C ^ h * p₁₃.prod fun e k => t e.toFinset ^ k) *
              (C ^ h * p₂₃.prod fun e k => t e.toFinset ^ k)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hl₁₂ hl₁₃ (pow_nonneg t₁₃ _)
              (mul_nonneg hCh hw₁₂)) hl₂₃ (pow_nonneg t₂₃ _)
              (mul_nonneg (mul_nonneg hCh hw₁₂) (mul_nonneg hCh hw₁₃)))
              (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
        _ = _ := by rw [show 3 * h = h + h + h by ring, pow_add, pow_add]; ring

/-- The maximal-term form on the whole set: if `|A| = n ≥ 2`, a single connected loopless
`2 ^ (n - 2)`-regular multigraph `q` on `A` satisfies
`t(A) ^ 2 ^ (n - 2) ≤ C ∏_{x ≠ y} t({x, y}) ^ q_{xy}`, with `C ≥ 1` depending only on `n`
and `K`. -/
theorem exists_mem_setOf_regularMultigraph_pow_le (n : ℕ) (hn : 2 ≤ n) (K : ℕ → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {α : Type u} [DecidableEq α] (A : Finset α) (t : Finset α → ℝ),
      A.card = n → (∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) →
      (∀ B ⊆ A, 3 ≤ B.card → ∃ B₁ B₂ B₃ : Finset α, B₁.Nonempty ∧ B₂.Nonempty ∧ B₃.Nonempty ∧
        Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧ B₁ ∪ B₂ ∪ B₃ = B ∧
        t B ^ 2 ≤ K B.card * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) →
      ∃ q ∈ {q : Sym2 α →₀ ℕ | (∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ A) ∧
          (∀ x ∈ A, ∑ y ∈ A, q s(x, y) = 2 ^ (n - 2)) ∧
          ∀ x ∈ A, ∀ y ∈ A, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y},
        t A ^ 2 ^ (n - 2) ≤ C * ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ q e := by
  obtain ⟨C, hC, hmain⟩ := exists_regularMultigraph_pow_le.{u} K n
  refine ⟨C, hC, fun A t hA ht hK => ?_⟩
  obtain ⟨q, hq, hle⟩ := hmain A t ht hK A subset_rfl (hA ▸ hn) hA.le
  rw [hA] at hq hle
  refine ⟨q, hq, ?_⟩
  rwa [Finsupp.prod_of_support_subset q (s := A.sym2.filter fun e => ¬e.IsDiag)
    (fun e he => Finset.mem_filter.2 ⟨Finset.mem_sym2_iff.2 (hq.1 e he).2, (hq.1 e he).1⟩) _
    (fun _ _ => pow_zero _)] at hle

/-- Under the three-part product inequalities, a factor of a pair-weight monomial over the
off-diagonal pairs of `A` is nonnegative. -/
theorem pow_nonneg_of_mem_filter_sym2 {A : Finset α} {t : Finset α → ℝ}
    (ht : ∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) {e : Sym2 α}
    (he : e ∈ A.sym2.filter fun e => ¬e.IsDiag) : 0 ≤ t e.toFinset := by
  rw [Finset.mem_filter, Finset.mem_sym2_iff] at he
  exact ht _ (fun x hx => he.1 x (Sym2.mem_toFinset.1 hx))
    (Sym2.card_toFinset_of_not_isDiag e he.2).ge

/-- **The regular multigraph bound.** Let `|A| = n ≥ 2` and let `t ≥ 0` on the subsets of `A`
with at least two elements. If every `B ⊆ A` with `|B| ≥ 3` has a partition into three nonempty
parts with `t(B)² ≤ K_{|B|} t(B₁ ∪ B₂) t(B₁ ∪ B₃) t(B₂ ∪ B₃)`, then
`t(A) ^ 2 ^ (n - 2) ≤ C ∑_Q ∏_{x ≠ y} t({x, y}) ^ q_{xy}`, the sum running over the connected
loopless `2 ^ (n - 2)`-regular multigraphs on `A` (a finite set,
`finite_setOf_regularMultigraph`), with `C` depending only on `n` and `K`. -/
theorem pow_le_mul_finsum_regularMultigraph (n : ℕ) (hn : 2 ≤ n) (K : ℕ → ℝ) :
    ∃ C : ℝ, ∀ {α : Type u} [DecidableEq α] (A : Finset α) (t : Finset α → ℝ), A.card = n →
      (∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) →
      (∀ B ⊆ A, 3 ≤ B.card → ∃ B₁ B₂ B₃ : Finset α, B₁.Nonempty ∧ B₂.Nonempty ∧ B₃.Nonempty ∧
        Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧ B₁ ∪ B₂ ∪ B₃ = B ∧
        t B ^ 2 ≤ K B.card * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) →
      t A ^ 2 ^ (n - 2) ≤ C * ∑ᶠ q ∈ {q : Sym2 α →₀ ℕ |
          (∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ A) ∧
          (∀ x ∈ A, ∑ y ∈ A, q s(x, y) = 2 ^ (n - 2)) ∧
          ∀ x ∈ A, ∀ y ∈ A, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y},
        ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ q e := by
  obtain ⟨C, hC, hmain⟩ := exists_mem_setOf_regularMultigraph_pow_le.{u} n hn K
  refine ⟨C, ?_⟩
  intro α _ A t hA ht hK
  obtain ⟨q, hq, hle⟩ := hmain A t hA ht hK
  have hS := finite_setOf_regularMultigraph A (2 ^ (n - 2))
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hC))
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  exact Finset.single_le_sum
    (f := fun q : Sym2 α →₀ ℕ => ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ q e)
    (fun q' _ => Finset.prod_nonneg fun e he => pow_nonneg (pow_nonneg_of_mem_filter_sym2 ht he) _)
    (hS.mem_toFinset.2 hq)

/-- **The root form of the regular multigraph bound.** Under the hypotheses of
`pow_le_mul_finsum_regularMultigraph`,
`t(A) ≤ C ∑_Q ∏_{x ≠ y} t({x, y}) ^ (q_{xy} / 2 ^ (n - 2))`, the sum running over the same
finite set of multigraphs, with `C` depending only on `n` and `K`. -/
theorem le_mul_finsum_prod_rpow_regularMultigraph (n : ℕ) (hn : 2 ≤ n) (K : ℕ → ℝ) :
    ∃ C : ℝ, ∀ {α : Type u} [DecidableEq α] (A : Finset α) (t : Finset α → ℝ), A.card = n →
      (∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) →
      (∀ B ⊆ A, 3 ≤ B.card → ∃ B₁ B₂ B₃ : Finset α, B₁.Nonempty ∧ B₂.Nonempty ∧ B₃.Nonempty ∧
        Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧ B₁ ∪ B₂ ∪ B₃ = B ∧
        t B ^ 2 ≤ K B.card * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) →
      t A ≤ C * ∑ᶠ q ∈ {q : Sym2 α →₀ ℕ |
          (∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ A) ∧
          (∀ x ∈ A, ∑ y ∈ A, q s(x, y) = 2 ^ (n - 2)) ∧
          ∀ x ∈ A, ∀ y ∈ A, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y},
        ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ ((q e : ℝ) / 2 ^ (n - 2)) := by
  obtain ⟨C, hC, hmain⟩ := exists_mem_setOf_regularMultigraph_pow_le.{u} n hn K
  refine ⟨C ^ ((2 ^ (n - 2) : ℕ) : ℝ)⁻¹, ?_⟩
  intro α _ A t hA ht hK
  obtain ⟨q, hq, hle⟩ := hmain A t hA ht hK
  have hS := finite_setOf_regularMultigraph A (2 ^ (n - 2))
  have hD : (2 ^ (n - 2) : ℕ) ≠ 0 := by positivity
  have htA : 0 ≤ t A := ht A subset_rfl (hA ▸ hn)
  have hP : ∀ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), 0 ≤ t e.toFinset :=
    fun e he => pow_nonneg_of_mem_filter_sym2 ht he
  have hP0 : 0 ≤ ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ q e :=
    Finset.prod_nonneg fun e he => pow_nonneg (hP e he) _
  have hroot : t A ≤ C ^ ((2 ^ (n - 2) : ℕ) : ℝ)⁻¹ *
      ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ ((q e : ℝ) / 2 ^ (n - 2)) := by
    calc t A = (t A ^ 2 ^ (n - 2)) ^ ((2 ^ (n - 2) : ℕ) : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast htA hD).symm
      _ ≤ (C * ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ q e) ^
            ((2 ^ (n - 2) : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow (pow_nonneg htA _) hle (by positivity)
      _ = _ := by
          rw [Real.mul_rpow (zero_le_one.trans hC) hP0, ← Real.finsetProd_rpow _ _
            (fun e he => pow_nonneg (hP e he) _)]
          congr 1
          refine Finset.prod_congr rfl fun e he => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hP e he), div_eq_mul_inv]
          push_cast
          rfl
  refine hroot.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  exact Finset.single_le_sum (f := fun q : Sym2 α →₀ ℕ =>
      ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ ((q e : ℝ) / 2 ^ (n - 2)))
    (fun q' _ => Finset.prod_nonneg fun e he => Real.rpow_nonneg (hP e he) _)
    (hS.mem_toFinset.2 hq)

end PercLib.Percolation.Bond
