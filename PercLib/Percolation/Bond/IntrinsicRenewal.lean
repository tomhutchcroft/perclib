/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.BallExploration
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.Transport.Reindexing
public import PercLib.Models.Line

/-!
# Intrinsic spheres and balls at infinite susceptibility (R5XZ, lower bounds)

Let `q` be a transitive profile on a countable `V` with `D = ∑'_{v ≠ o} q(o, v) < ⊤` and
`χ_o = ⊤`. Write `a_r = E|S_ω(o, r)|` and `b_r = E|B_ω(o, r)|` for the intrinsic spheres and
balls. Then for every `r`:

* `one_le_lintegral_encard_sphere`: `1 ≤ a_r`;
* `succ_le_lintegral_encard_ball`: `r + 1 ≤ b_r`.

(The upper bound `b_r ≤ ∑_{j ≤ r} D^j` is `lintegral_encard_ball_le_of_transitive`.)

Route (wiki, R5XZ): under transitivity every radius-`k` ball has mean `b_k`
(`lintegral_encard_ball_eq_of_transitive`), so the renewal inequality of `BallExploration.lean`
reads `b_{m+n} ≤ b_m + a_m b_n`. If `a_m < 1` for some `m ≥ 1`, iteration bounds every `b_r` by
`b_m / (1 - a_m) < ⊤`, and `χ_o = sup_r b_r` would be finite. Hence `a_m ≥ 1`; and
`b_{r+1} = b_r + a_{r+1}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Transport of intrinsic distances -/

/-- Graph isomorphisms preserve extended distances. -/
theorem edist_iso {W W' : Type*} {G : SimpleGraph W} {G' : SimpleGraph W'} (φ : G ≃g G')
    (u v : W) : G'.edist (φ u) (φ v) = G.edist u v := by
  refine le_antisymm ?_ ?_
  · by_cases hr : G.Reachable u v
    · obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
      rw [← hw, ← SimpleGraph.Walk.length_map φ.toHom]
      exact SimpleGraph.edist_le _
    · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]; exact le_top
  · by_cases hr : G'.Reachable (φ u) (φ v)
    · obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
      rw [← hw, ← SimpleGraph.Walk.length_map φ.symm.toHom]
      have := SimpleGraph.edist_le (w.map φ.symm.toHom)
      simpa using this
    · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]; exact le_top

/-- Intrinsic distances are carried along a vertex bijection. -/
theorem edist_image_sym2Map (σ : V ≃ V) (ω : Config V) (x y : V) :
    (openGraph (Sym2.map σ '' ω)).edist (σ x) (σ y) = (openGraph ω).edist x y := by
  obtain ⟨φ, hφ⟩ := nonempty_iso_openGraph_image σ ω
  have := edist_iso φ x y
  rwa [hφ] at this

/-- **Root independence of ball means.** Under a transitive profile, every radius-`k` ball
has the same mean. -/
theorem lintegral_encard_ball_eq_of_transitive [Countable V] (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (x o : V) (k : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist x y ≤ k} : Set V).encard : ℝ≥0∞) ∂law q =
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ k} : Set V).encard : ℝ≥0∞) ∂law q := by
  obtain ⟨σ, rfl, hσ⟩ := hq o x
  have hlaw : (law q).map (fun ω => Sym2.map σ '' ω) = law q :=
    PercLib.Probability.prodBernoulli_map_image_sym2_invariant q σ hσ
  rw [lintegral_encard_ball, lintegral_encard_ball, ← σ.tsum_eq]
  refine tsum_congr fun y => ?_
  conv_lhs => rw [← hlaw]
  rw [map_image_sym2Map_apply]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, edist_image_sym2Map]

/-! ### Spheres and balls -/

/-- `b_{r+1} = b_r + a_{r+1}`. -/
theorem lintegral_encard_ball_succ [Countable V] (μ : Measure (Config V)) (o : V) (r : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} : Set V).encard : ℝ≥0∞) ∂μ =
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂μ +
        ∫⁻ ω, (({y | (openGraph ω).edist o y = ((r + 1 : ℕ) : ℕ∞)} : Set V).encard : ℝ≥0∞)
          ∂μ := by
  rw [lintegral_encard_ball, lintegral_encard_ball, lintegral_encard_sphere, ← ENNReal.tsum_add]
  refine tsum_congr fun y => ?_
  rw [← measure_union _ (measurableSet_edist_eq_succ o y r)]
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, edist_eq_succ_iff]
    constructor
    · intro h
      by_cases h' : (openGraph ω).edist o y ≤ r
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | ⟨h, -⟩)
      · exact h.trans (by exact_mod_cast Nat.le_succ r)
      · exact h
  · rw [Set.disjoint_left]
    intro ω h1 h2
    exact ((edist_eq_succ_iff _ o y r).1 h2).2 h1

/-- `b_0 = 1`. -/
theorem lintegral_encard_ball_zero [Countable V] (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (o : V) : ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ (0 : ℕ)} : Set V).encard : ℝ≥0∞) ∂μ = 1 := by
  have : ∀ ω : Config V, ({y | (openGraph ω).edist o y ≤ (0 : ℕ)} : Set V) = {o} := by
    intro ω
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.cast_zero, nonpos_iff_eq_zero,
      SimpleGraph.edist_eq_zero_iff]
    exact eq_comm
  simp_rw [this]
  simp

/-- The ball means are monotone in the radius. -/
theorem lintegral_encard_ball_mono [Countable V] (μ : Measure (Config V)) (o : V) {r s : ℕ}
    (h : r ≤ s) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ s} : Set V).encard : ℝ≥0∞) ∂μ :=
  lintegral_mono fun ω => ENat.toENNReal_le.2 (Set.encard_le_encard fun y hy =>
    (show (openGraph ω).edist o y ≤ r from hy).trans (by exact_mod_cast h))

/-- The susceptibility is at most any uniform bound on the ball means. -/
theorem chi_le_of_lintegral_encard_ball_le [Countable V] (q : Sym2 V → unitInterval) (o : V)
    {C : ℝ≥0∞}
    (hC : ∀ r : ℕ, ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)
      ∂law q ≤ C) : chi q o ≤ C := by
  rw [chi_eq_tsum_tau]
  -- `τ(o, y) = sup_r P(edist o y ≤ r)`
  have htau : ∀ y, tau q o y = ⨆ r : ℕ, law q {ω | (openGraph ω).edist o y ≤ r} := by
    intro y
    have hmono : Monotone fun r : ℕ => {ω : Config V | (openGraph ω).edist o y ≤ r} :=
      fun r s h ω (hω : (openGraph ω).edist o y ≤ r) =>
        (show (openGraph ω).edist o y ≤ s from hω.trans (by exact_mod_cast h))
    rw [tau, ← hmono.measure_iUnion]
    congr 1
    ext ω
    simp only [mem_conn_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      have hne := SimpleGraph.edist_ne_top_iff_reachable.2 h
      exact ⟨(openGraph ω |>.edist o y).toNat, (ENat.natCast_toNat hne).ge⟩
    · rintro ⟨r, hr⟩
      exact SimpleGraph.edist_ne_top_iff_reachable.1 (ne_top_of_le_ne_top (by simp) hr)
  simp_rw [htau]
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  rw [ENNReal.finsetSum_iSup_of_monotone (f := fun y (r : ℕ) =>
    law q {ω : Config V | (openGraph ω).edist o y ≤ r}) fun y r t h => measure_mono fun ω
    (hω : (openGraph ω).edist o y ≤ r) =>
      (show (openGraph ω).edist o y ≤ t from hω.trans (by exact_mod_cast h))]
  refine iSup_le fun r => ?_
  refine le_trans ?_ (hC r)
  rw [lintegral_encard_ball]
  exact ENNReal.sum_le_tsum s

/-! ### R5XZ, lower bounds -/

/-- `b · (1 - a)⁻¹ = b + a (b (1 - a)⁻¹)` for `a < 1`. -/
theorem mul_inv_one_sub_eq {a b : ℝ≥0∞} (ha : a < 1) :
    b + a * (b * (1 - a)⁻¹) = b * (1 - a)⁻¹ := by
  have h1 : 1 - a ≠ 0 := (tsub_pos_of_lt ha).ne'
  have h2 : 1 - a ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have key : (1 : ℝ≥0∞) + a * (1 - a)⁻¹ = (1 - a)⁻¹ := by
    calc (1 : ℝ≥0∞) + a * (1 - a)⁻¹ = (1 - a) * (1 - a)⁻¹ + a * (1 - a)⁻¹ := by
          rw [ENNReal.mul_inv_cancel h1 h2]
      _ = ((1 - a) + a) * (1 - a)⁻¹ := (add_mul _ _ _).symm
      _ = (1 - a)⁻¹ := by rw [tsub_add_cancel_of_le ha.le, one_mul]
  calc b + a * (b * (1 - a)⁻¹) = b * (1 + a * (1 - a)⁻¹) := by ring
    _ = b * (1 - a)⁻¹ := by rw [key]

/-- **Spheres.** Under transitivity, `D < ⊤` and `χ_o = ⊤`,
`1 ≤ E|S_ω(o, r)|` for every `r`. -/
theorem one_le_lintegral_encard_sphere [Countable V] (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V)
    (hD : rowSum (fun e => unitInterval.toENNReal (q e)) o < ⊤)
    (hchi : chi q o = ⊤) (r : ℕ) :
    1 ≤ ∫⁻ ω, (({y | (openGraph ω).edist o y = r} : Set V).encard : ℝ≥0∞) ∂law q := by
  set D := rowSum (fun e => unitInterval.toENNReal (q e)) o with hDdef
  have hrow : ∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v ≤ D :=
    fun v => (rowSum_eq_of_transitive_profile q hq o v).le
  set b : ℕ → ℝ≥0∞ := fun k =>
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ k} : Set V).encard : ℝ≥0∞) ∂law q with hb
  have hbfin : ∀ k, b k < ⊤ := fun k =>
    (lintegral_encard_ball_le_of_rowSum q D hrow o k).trans_lt
      (ENNReal.sum_lt_top.2 fun j _ => ENNReal.pow_lt_top hD)
  rcases r with _ | m
  · -- `S(o, 0) = {o}`
    have : ∀ ω : Config V, ({y | (openGraph ω).edist o y = ((0 : ℕ) : ℕ∞)} : Set V) = {o} := by
      intro ω; ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.cast_zero,
        SimpleGraph.edist_eq_zero_iff]
      exact eq_comm
    simp_rw [this]
    simp
  by_contra hlt
  rw [not_le] at hlt
  set a := ∫⁻ ω, (({y | (openGraph ω).edist o y = ((m + 1 : ℕ) : ℕ∞)} : Set V).encard : ℝ≥0∞)
    ∂law q with ha
  set C := b (m + 1) * (1 - a)⁻¹ with hC
  have hCfin : C < ⊤ := ENNReal.mul_lt_top (hbfin _)
    (ENNReal.inv_lt_top.2 (tsub_pos_of_lt (by exact_mod_cast hlt)))
  -- the renewal inequality, `b_{(m+1)(j+1)} ≤ b_{m+1} + a b_{(m+1)j}`
  have hren : ∀ k, b (m + 1 + k) ≤ b (m + 1) + a * b k := by
    intro k
    have h := renewal_ball q o m k (ae_finite_ball_of_rowSum q hD hrow o m) (b := b k)
      (fun x => le_of_eq (lintegral_encard_ball_eq_of_transitive q hq x o k))
    exact h
  have hiter : ∀ j : ℕ, b ((m + 1) * (j + 1)) ≤ C := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, mul_one, hC]
      exact le_mul_of_one_le_right bot_le (ENNReal.one_le_inv.2 tsub_le_self)
    | succ j ih =>
      calc b ((m + 1) * (j + 1 + 1)) = b (m + 1 + (m + 1) * (j + 1)) := by ring_nf
        _ ≤ b (m + 1) + a * b ((m + 1) * (j + 1)) := hren _
        _ ≤ b (m + 1) + a * C := add_le_add le_rfl (mul_le_mul' le_rfl ih)
        _ = C := mul_inv_one_sub_eq (by exact_mod_cast hlt)
  have hall : ∀ k : ℕ, b k ≤ C := fun k =>
    (lintegral_encard_ball_mono (law q) o (show k ≤ (m + 1) * (k + 1) by nlinarith)).trans
      (hiter k)
  have := chi_le_of_lintegral_encard_ball_le q o hall
  rw [hchi] at this
  exact absurd (lt_of_le_of_lt this hCfin) (lt_irrefl _)

/-- **Balls.** Under the same hypotheses, `r + 1 ≤ E|B_ω(o, r)|` for every `r`. -/
theorem succ_le_lintegral_encard_ball [Countable V] (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V)
    (hD : rowSum (fun e => unitInterval.toENNReal (q e)) o < ⊤)
    (hchi : chi q o = ⊤) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂law q := by
  induction r with
  | zero => rw [lintegral_encard_ball_zero]; simp
  | succ r ih =>
    rw [lintegral_encard_ball_succ]
    have h1 := one_le_lintegral_encard_sphere q hq o hD hchi (r + 1)
    push_cast at h1 ih ⊢
    exact add_le_add ih h1

/-! ### Non-vacuity witness -/

/-- The all-open nearest-neighbour line: transitive, `D = 2`, `χ = ⊤`; so every sphere has
mean at least `1` and every ball of radius `r` mean at least `r + 1`. -/
example (r : ℕ) :
    let q : Sym2 ℤ → unitInterval :=
      Sym2.lift ⟨fun a b => if |b - a| = 1 then 1 else 0, fun a b => by
        simp only [abs_sub_comm]⟩
    1 ≤ ∫⁻ ω, (({y | (openGraph ω).edist 0 y = r} : Set ℤ).encard : ℝ≥0∞) ∂law q ∧
      ((r + 1 : ℕ) : ℝ≥0∞) ≤
        ∫⁻ ω, (({y | (openGraph ω).edist 0 y ≤ r} : Set ℤ).encard : ℝ≥0∞) ∂law q := by
  intro q
  have hq : ∀ x y : ℤ, ∃ σ : ℤ ≃ ℤ, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e := by
    intro x y
    refine ⟨Equiv.addRight (y - x), by simp, fun e => ?_⟩
    induction e using Sym2.ind with
    | h a b => simp [q, Sym2.map_mk]
  have hD : rowSum (fun e => unitInterval.toENNReal (q e)) 0 < ⊤ := by
    rw [rowSum_toENNReal, tsum_eq_sum (s := {1, -1}) fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      have : ¬ |v - 0| = 1 := by
        rw [sub_zero]; intro h
        rcases abs_eq (zero_le_one) |>.1 h with h | h
        · exact hv.1 h
        · exact hv.2 h
      have this' : ¬ |v| = 1 := by simpa using this
      split_ifs
      · rfl
      · simp only [q, Sym2.lift_mk, sub_zero, this', ↓reduceIte]; rfl]
    exact ENNReal.sum_lt_top.2 fun v _ => by split_ifs <;> simp
  have hchi : chi q 0 = ⊤ := by
    rw [PercLib.Models.Line.chi_eq 1 q (fun a b _ => rfl) 0]
    have h1 : (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞) = 1 := by
      rw [ENNReal.coe_eq_one]; rfl
    rw [h1, tsub_self, ENNReal.div_zero (by norm_num)]
  exact ⟨one_le_lintegral_encard_sphere q hq 0 hD hchi r,
    succ_le_lintegral_encard_ball q hq 0 hD hchi r⟩

end PercLib.Percolation.Bond
