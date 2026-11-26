/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: connection loss on deleting a vertex set (wiki
integrated-susceptibility, tag 7902) and the lower bound for the boundary functional by the boundary
susceptibility (wiki boundary-susceptibility, tag 67GX). No upstream proof is copied, no definition
is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.BoundaryContraction
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.CountableBK
public import PercLib.Probability.OpenEventHarris

/-! # Deleting a vertex set, and the boundary susceptibility

For `S ⊆ V` write `τ^S(y,w)` for the probability that `y` and `w` are joined in the open
graph with the vertices of `S` deleted, spelled
`law q {ω | ∃ hy : y ∈ Sᶜ, ∃ hw : w ∈ Sᶜ, ((openGraph ω).induce Sᶜ).Reachable ⟨y,hy⟩ ⟨w,hw⟩}`.

* `law_deleted_le_tau`, `tau_le_deleted_add` (7902): for `y, w ∉ S`,
  `τ^S(y,w) ≤ τ(y,w) ≤ τ^S(y,w) + ∑_{c ∈ S} τ(y,c) τ(c,w)`.
* `boundary_susceptibility_bound` (67GX): for `q = intensityProfile J β` with off-diagonal
  row sums of `J` at most `1` and `χ_max = ⨆ u, χ(u) < ∞`, and every finite `S`,
  `Φ_β(S) ≥ L(S)² / (β² χ_max Q(S)) ≥ (χ_min |S| - ∑_{u,v ∈ S} τ(u,v))₊² / (β² χ_max Q(S))`,
  where `χ_{Sᶜ}(z) = ∑_{w ∉ S} τ^S(z,w)`, `Φ_β(S) = ∑_{v ∈ S} ∑_{z ∉ S} J(v,z) χ_{Sᶜ}(z)`,
  `Q(S) = ∑_{u ∈ S} (∑_{v ∈ S} τ(u,v))²` and `L(S) = ∑_{u ∈ S} ∑_{w ∉ S} τ(u,w)`.

7902 takes an open simple path from `y` to `w`; if it meets `S` at `c`, the two segments
are disjoint witnesses of `y ↔ c` and `c ↔ w`, and BK applies. For 67GX, the first-exit
inequality of `BoundaryContraction.lean`, applied from `w ∉ S` with domain `Sᶜ`, is a
last-exit bound `τ(u,w) ≤ ∑_{y ∈ S} ∑_x τ(u,y) q(y,x) τ^S(x,w)`. Summing gives
`L(S) ≤ β ∑_{y ∈ S} a_y φ_y` with `a_y = ∑_{u ∈ S} τ(y,u)` and
`φ_y = ∑_{x ∉ S} J(y,x) χ_{Sᶜ}(x) ≤ χ_max`. Cauchy–Schwarz then gives
`L(S)² ≤ β² Q(S) ∑ φ_y² ≤ β² Q(S) χ_max Φ_β(S)`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-! ### Splitting an open path -/

/-- The pairs of a walk in the open graph are open. -/
theorem mem_of_mem_edges_openGraph {ω : Config V} {x y : V} (p : (openGraph ω).Walk x y)
    {e : Sym2 V} (he : e ∈ p.edges) : e ∈ ω := by
  have := p.edges_subset_edgeSet he
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
  exact this.1

/-- A walk in the open graph witnesses a connection in the configuration of its own
pairs. -/
theorem edges_mem_conn {ω : Config V} {x y : V} (p : (openGraph ω).Walk x y) :
    {e | e ∈ p.edges} ∈ conn x y :=
  mem_conn_of_walk_edges p fun _ he => he

open Classical in
/-- If an open path from `x` to `y` passes through `c`, then `x ↔ c` and `c ↔ y` occur
disjointly. -/
theorem mem_disjointOccurrence_of_path {ω : Config V} {x y c : V}
    (p : (openGraph ω).Walk x y) (hp : p.IsPath) (hc : c ∈ p.support) :
    ω ∈ disjointOccurrence (conn x c) (conn c y) := by
  rw [mem_disjointOccurrence_iff_open (isUpperSet_conn x c) (isUpperSet_conn c y)]
  have hspec := p.take_spec hc
  have hnd : (p.takeUntil c hc).edges ++ (p.dropUntil c hc).edges |>.Nodup := by
    rw [← SimpleGraph.Walk.edges_append, hspec]
    exact hp.isTrail.edges_nodup
  refine ⟨{e | e ∈ (p.takeUntil c hc).edges}, {e | e ∈ (p.dropUntil c hc).edges},
    List.finite_toSet _, List.finite_toSet _, ?_, fun e he => mem_of_mem_edges_openGraph _ he,
    fun e he => mem_of_mem_edges_openGraph _ he, edges_mem_conn _, edges_mem_conn _⟩
  rw [Set.disjoint_left]
  intro e h1 h2
  exact List.disjoint_of_nodup_append hnd h1 h2

/-! ### 7902: connection loss on deleting a vertex set -/

/-- Connection with `S` deleted implies connection. -/
theorem law_deleted_le_tau (q : Sym2 V → unitInterval) (S : Set V) (y w : V) :
    law q (localConn Sᶜ y w) ≤ tau q y w := by
  refine measure_mono fun ω ⟨hy, hw, h⟩ => ?_
  exact conn_of_localConn ω Sᶜ ⟨y, hy⟩ ⟨w, hw⟩ h

/-- An open connection from `y` to `w` that is lost when `S` is deleted passes through some
`c ∈ S`, and then `y ↔ c` and `c ↔ w` occur disjointly. -/
theorem conn_subset_deleted_union (S : Set V) (y w : V) :
    conn y w ⊆ localConn Sᶜ y w ∪
      ⋃ c : S, disjointOccurrence (conn y (c : V)) (conn (c : V) w) := by
  intro ω hω
  obtain ⟨p, hp⟩ := (show (openGraph ω).Reachable y w from hω).exists_isPath
  by_cases hS : ∀ x ∈ p.support, x ∈ Sᶜ
  · exact Or.inl ⟨hS _ p.start_mem_support, hS _ p.end_mem_support, ⟨p.induce Sᶜ hS⟩⟩
  · push Not at hS
    obtain ⟨c, hc, hcS⟩ := hS
    refine Or.inr (mem_iUnion.2 ⟨⟨c, not_not.1 hcS⟩, ?_⟩)
    exact mem_disjointOccurrence_of_path p hp hc

/-- **Connection loss on deleting a set.** For `y, w ∉ S`,
`τ(y,w) ≤ τ^S(y,w) + ∑_{c ∈ S} τ(y,c) τ(c,w)`. -/
theorem tau_le_deleted_add [Countable V] (q : Sym2 V → unitInterval) (S : Set V) (y w : V) :
    tau q y w ≤ law q (localConn Sᶜ y w) +
      ∑' c : S, tau q y c * tau q c w := by
  refine (measure_mono (conn_subset_deleted_union S y w)).trans
    ((measure_union_le _ _).trans (add_le_add_right ?_ _))
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun c => ?_)
  exact countable_profile_bk q (isUpperSet_conn _ _) (isUpperSet_conn _ _)

/-! ### Last exit from a finite set -/

/-- Connection inside the whole vertex set to a singleton is connection. -/
theorem setOf_induce_univ_singleton (y u : V) :
    {ω : Config V | ∃ b ∈ ({u} : Set V), ω ∈ localConn univ y b} =
      conn y u := by
  ext ω
  simp only [mem_singleton_iff, exists_eq_left, mem_ofPred_eq, localConn_univ]

open Classical in
/-- **Last exit.** For `u ∈ S` and `w ∉ S`, an open path from `u` to `w` has a last pair
`s(y,x)` with `y ∈ S`, `x ∉ S`, after which it avoids `S`:
`τ(u,w) ≤ ∑_{x} ∑_{y ∈ S} τ^S(w,x) q(x,y) τ(y,u)`. -/
theorem tau_le_lastExit [Countable V] (q : Sym2 V → unitInterval) (S : Set V) {u w : V}
    (hu : u ∈ S) (hw : w ∉ S) :
    tau q u w ≤ ∑' x, ∑' y, if y ∈ S then
      law q (localConn Sᶜ w x) *
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) * tau q y u else 0 := by
  have h := law_reach_le_firstExit q (S := Sᶜ) (A := univ) (B := {u}) (u := w) hw
    (by
      intro b hb
      rw [mem_singleton_iff.1 hb]
      exact ⟨mem_univ u, not_not.2 hu⟩)
  rw [setOf_induce_univ_singleton] at h
  rw [tau_comm]
  refine h.trans_eq (tsum_congr fun x => tsum_congr fun y => ?_)
  by_cases hy : y ∈ S
  · rw [ite_eq_right (show ¬ y ∈ Sᶜ from not_not.2 hy), ite_eq_left hy,
      setOf_induce_univ_singleton]
    rfl
  · rw [ite_eq_left (show y ∈ Sᶜ from hy), ite_eq_right hy]

open Classical in
/-- **The boundary sum by last exit.** For finite `S`,
`L(S) = ∑_{u ∈ S} ∑_{w ∉ S} τ(u,w) ≤ ∑_{y ∈ S} (∑_{u ∈ S} τ(y,u)) ∑_x q(y,x) χ_{Sᶜ}(x)`,
where `χ_{Sᶜ}(x) = ∑_w τ^S(x,w)`. -/
theorem boundarySum_le [Countable V] (q : Sym2 V → unitInterval) (S : Finset V) :
    ∑ u ∈ S, ∑' w, (if w ∈ S then 0 else tau q u w) ≤
      ∑ y ∈ S, (∑ u ∈ S, tau q y u) * ∑' x, (unitInterval.toNNReal (q s(y, x)) : ℝ≥0∞) *
        ∑' w, law q (localConn (S : Set V)ᶜ x w) := by
  set D : V → V → ℝ≥0∞ := fun x w => law q (localConn (S : Set V)ᶜ x w)
  have hD : ∀ x w, D x w = D w x := fun x w => by
    simp only [D]
    rw [localConn_comm]
  set qq : V → V → ℝ≥0∞ := fun x y => (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)
  have hqq : ∀ x y, qq x y = qq y x := fun x y => by simp only [qq, Sym2.eq_swap]
  calc ∑ u ∈ S, ∑' w, (if w ∈ S then 0 else tau q u w)
      ≤ ∑ u ∈ S, ∑' w, ∑' x, ∑ y ∈ S, D w x * qq x y * tau q y u := by
        refine Finset.sum_le_sum fun u hu => ENNReal.tsum_le_tsum fun w => ?_
        split_ifs with hw
        · exact zero_le
        · refine (tau_le_lastExit q S hu hw).trans_eq (tsum_congr fun x => ?_)
          refine (tsum_eq_sum (s := S) fun y hy => ite_eq_right (by simpa using hy)).trans
            (Finset.sum_congr rfl fun y hy => ite_eq_left (by simpa using hy))
    _ = ∑ y ∈ S, ∑ u ∈ S, ∑' x, ∑' w, tau q y u * (qq y x * D x w) := by
        have hs : ∀ u w, ∑' x, ∑ y ∈ S, D w x * qq x y * tau q y u =
            ∑ y ∈ S, ∑' x, D w x * qq x y * tau q y u := fun u w =>
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        simp_rw [hs]
        have hs' : ∀ u, ∑' w, ∑ y ∈ S, ∑' x, D w x * qq x y * tau q y u =
            ∑ y ∈ S, ∑' w, ∑' x, D w x * qq x y * tau q y u := fun u =>
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        simp_rw [hs']
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun x => tsum_congr fun w => ?_
        rw [hD, hqq]
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp_rw [Finset.sum_mul, ← ENNReal.tsum_mul_left]
        rfl

/-- The deleted susceptibility is at most the susceptibility. -/
theorem tsum_law_deleted_le_chi [Countable V] (q : Sym2 V → unitInterval) (S : Set V)
    (x : V) :
    ∑' w, law q (localConn Sᶜ x w) ≤ chi q x := by
  rw [chi_eq_tsum_tau]
  exact ENNReal.tsum_le_tsum fun w => law_deleted_le_tau q S x w

/-- Connection with `S` deleted from a vertex of `S` is impossible. -/
theorem setOf_deleted_of_mem (S : Set V) {x : V} (hx : x ∈ S) (w : V) :
    localConn Sᶜ x w = ∅ := by
  ext ω
  simp only [mem_empty_iff_false, iff_false]
  exact fun ⟨hx', _⟩ => hx' hx

open Classical in
/-- `L(S) ≤ β ∑_{y ∈ S} (∑_{u ∈ S} τ(y,u)) φ_y` with
`φ_y = ∑_{x ∉ S} J(y,x) χ_{Sᶜ}(x)`, in the intensity family. -/
theorem boundarySum_le_intensity [Countable V] (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (S : Finset V) :
    ∑ u ∈ S, ∑' w, (if w ∈ S then 0 else tau (intensityProfile J β) u w) ≤
      ∑ y ∈ S, (∑ u ∈ S, tau (intensityProfile J β) y u) * ((β : ℝ≥0∞) *
        ∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ≥0∞)) *
          ∑' w, law (intensityProfile J β) (localConn (S : Set V)ᶜ x w)) := by
  refine (boundarySum_le _ S).trans (Finset.sum_le_sum fun y _ => ?_)
  refine mul_le_mul_right ?_ _
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ S
  · have h0 : ∀ w, law (intensityProfile J β) (localConn (S : Set V)ᶜ x w) = 0 := fun w => by
      rw [setOf_deleted_of_mem _ (Finset.mem_coe.2 hx), measure_empty]
    simp only [h0, tsum_zero, mul_zero, zero_le]
  · rw [ite_eq_right hx, ← mul_assoc]
    refine mul_le_mul_left ?_ _
    have := intensityProfile_toNNReal_le J β s(y, x)
    exact_mod_cast this

open Classical in
/-- With off-diagonal row sums of `J` at most `1`, `φ_y ≤ χ_max` for `y ∈ S`. -/
theorem boundaryRow_le_iSup_chi [Countable V] (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (hJ : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1) (S : Finset V)
    {y : V} (hy : y ∈ S) :
    ∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ≥0∞)) *
        ∑' w, law (intensityProfile J β) (localConn (S : Set V)ᶜ x w) ≤
      ⨆ u, chi (intensityProfile J β) u := by
  calc _ ≤ ∑' x, (if x = y then 0 else (J s(y, x) : ℝ≥0∞)) *
        ⨆ u, chi (intensityProfile J β) u := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ S
        · simp [hx]
        · have hxy : x ≠ y := fun h => hx (h ▸ hy)
          rw [ite_eq_right hx, ite_eq_right hxy]
          exact mul_le_mul_right ((tsum_law_deleted_le_chi _ _ x).trans (le_iSup _ x)) _
    _ = rowSum (fun e => (J e : ℝ≥0∞)) y *
        ⨆ u, chi (intensityProfile J β) u := by rw [rowSum_def, ENNReal.tsum_mul_right]
    _ ≤ 1 * ⨆ u, chi (intensityProfile J β) u := mul_le_mul_left (hJ y) _
    _ = _ := one_mul _

/-! ### 67GX in real numbers -/

section Real

variable [Countable V] (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (S : Finset V)

omit [Countable V] in
theorem toReal_tsum_law_deleted (q : Sym2 V → unitInterval) (x : V) :
    (∑' w, law q (localConn (S : Set V)ᶜ x w)).toReal =
    ∑' w, (law q).real (localConn (S : Set V)ᶜ x w) :=
  ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _

open Classical in
theorem toReal_boundaryRow (hχ : (⨆ u, chi (intensityProfile J β) u) ≠ ⊤) (y : V) :
    (∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ≥0∞)) *
        ∑' w, law (intensityProfile J β) (localConn (S : Set V)ᶜ x w)).toReal =
      ∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ)) *
        ∑' w, (law (intensityProfile J β)).real (localConn (S : Set V)ᶜ x w) := by
  have hfin : ∀ x, ∑' w, law (intensityProfile J β) (localConn (S : Set V)ᶜ x w) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top hχ ((tsum_law_deleted_le_chi _ _ x).trans (le_iSup _ x))
  rw [ENNReal.tsum_toReal_eq fun x => ENNReal.mul_ne_top (by split_ifs <;> simp) (hfin x)]
  refine tsum_congr fun x => ?_
  rw [ENNReal.toReal_mul, toReal_tsum_law_deleted]
  split_ifs <;> simp

open Classical in
/-- **First inequality.** In the intensity family with off-diagonal row sums of `J` at
most `1` and `χ_max = ⨆ u, χ(u) < ∞`, for every finite `S`,
`L(S)² / (β² χ_max Q(S)) ≤ Φ_β(S)`, where `L(S) = ∑_{u ∈ S} ∑_{w ∉ S} τ(u,w)`,
`Q(S) = ∑_{u ∈ S} (∑_{v ∈ S} τ(u,v))²` and
`Φ_β(S) = ∑_{v ∈ S} ∑_{z ∉ S} J(v,z) χ_{Sᶜ}(z)`. -/
theorem boundarySum_sq_div_le
    (hJ : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (hχ : (⨆ u, chi (intensityProfile J β) u) ≠ ⊤) :
    (∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau (intensityProfile J β) u w).toReal) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) ≤
      boundarySusceptibility J β S := by
  set q := intensityProfile J β
  set M := (⨆ u, chi q u).toReal
  set a : V → ℝ := fun y => ∑ u ∈ S, (tau q y u).toReal
  set φ : V → ℝ := fun y => ∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ)) *
    ∑' w, (law q).real (localConn (S : Set V)ᶜ x w)
  set L := ∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau q u w).toReal
  have htau : ∀ u v, tau q u v ≠ ⊤ := fun u v => ne_top_of_le_ne_top ENNReal.one_ne_top
    (tau_le_one q u v)
  -- The real form of the last-exit bound.
  have hF1 : L ≤ β * ∑ y ∈ S, a y * φ y := by
    have hE := boundarySum_le_intensity J β S
    have hrow : ∀ y ∈ S, (∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ≥0∞)) *
        ∑' w, law q (localConn (S : Set V)ᶜ x w)) ≠ ⊤ :=
      fun y hy => ne_top_of_le_ne_top hχ (boundaryRow_le_iSup_chi J β hJ S hy)
    have hfinR : ∀ y ∈ S, (∑ u ∈ S, tau q y u) * ((β : ℝ≥0∞) *
        ∑' x, (if x ∈ S then 0 else (J s(y, x) : ℝ≥0∞)) *
          ∑' w, law q (localConn (S : Set V)ᶜ x w)) ≠ ⊤ :=
      fun y hy => ENNReal.mul_ne_top (ENNReal.sum_ne_top.2 fun u _ => htau y u)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (hrow y hy))
    have hL : ∀ u ∈ S, ∑' w, (if w ∈ S then 0 else tau q u w) ≠ ⊤ := fun u _ =>
      ne_top_of_le_ne_top hχ ((ENNReal.tsum_le_tsum fun w => by
        split_ifs <;> simp).trans ((chi_eq_tsum_tau q u).symm.le.trans (le_iSup _ u)))
    have := (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.2 hL)
      (ENNReal.sum_ne_top.2 hfinR)).2 hE
    rw [ENNReal.toReal_sum hL, ENNReal.toReal_sum hfinR] at this
    convert this using 1
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [ENNReal.tsum_toReal_eq fun w => by split_ifs <;> simp [htau]]
      exact tsum_congr fun w => by split_ifs <;> simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum fun u _ => htau y u,
        toReal_boundaryRow J β S hχ y]
      simp only [a, φ, ENNReal.coe_toReal]
      ring
  have hφ : ∀ y ∈ S, 0 ≤ φ y ∧ φ y ≤ M := by
    intro y hy
    have h : φ y = _ := (toReal_boundaryRow J β S hχ y).symm
    rw [h]
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact ENNReal.toReal_mono hχ (boundaryRow_le_iSup_chi J β hJ S hy)
  have ha : ∀ y, 0 ≤ a y := fun y => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun u _ => tsum_nonneg fun w => by
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hΦ0 : 0 ≤ ∑ y ∈ S, φ y := Finset.sum_nonneg fun y hy => (hφ y hy).1
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S a φ
  have hφ2 : ∑ y ∈ S, φ y ^ 2 ≤ M * ∑ y ∈ S, φ y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hφ y hy).2 (hφ y hy).1
  have hQ0 : 0 ≤ ∑ y ∈ S, a y ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hsum0 : 0 ≤ ∑ y ∈ S, a y * φ y :=
    Finset.sum_nonneg fun y hy => mul_nonneg (ha y) (hφ y hy).1
  have hkey : L ^ 2 ≤ (β : ℝ) ^ 2 * M * (∑ y ∈ S, a y ^ 2) * ∑ y ∈ S, φ y := by
    have h1 : L ^ 2 ≤ ((β : ℝ) * ∑ y ∈ S, a y * φ y) ^ 2 :=
      pow_le_pow_left₀ hL0 hF1 2
    have h2 : (∑ y ∈ S, a y * φ y) ^ 2 ≤ (∑ y ∈ S, a y ^ 2) * (M * ∑ y ∈ S, φ y) :=
      hCS.trans (mul_le_mul_of_nonneg_left hφ2 hQ0)
    calc L ^ 2 ≤ ((β : ℝ) * ∑ y ∈ S, a y * φ y) ^ 2 := h1
      _ = (β : ℝ) ^ 2 * (∑ y ∈ S, a y * φ y) ^ 2 := by ring
      _ ≤ (β : ℝ) ^ 2 * ((∑ y ∈ S, a y ^ 2) * (M * ∑ y ∈ S, φ y)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  change L ^ 2 / ((β : ℝ) ^ 2 * M * ∑ y ∈ S, a y ^ 2) ≤ ∑ y ∈ S, φ y
  rcases (mul_nonneg (mul_nonneg (sq_nonneg (β : ℝ)) hM0) hQ0).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact hΦ0
  · rw [div_le_iff₀ hpos]
    linarith

omit [Countable V] in
open Classical in
/-- `χ(u) = ∑_{w ∈ S} τ(u,w) + ∑_{w ∉ S} τ(u,w)` in real numbers, when `χ(u) < ∞`. -/
theorem toReal_chi_eq_add [Countable V] (q : Sym2 V → unitInterval) (u : V)
    (hu : chi q u ≠ ⊤) :
    (chi q u).toReal = ∑ w ∈ S, (tau q u w).toReal +
      ∑' w, if w ∈ S then 0 else (tau q u w).toReal := by
  have hsplit : chi q u = ∑ w ∈ S, tau q u w + ∑' w, if w ∈ S then 0 else tau q u w := by
    have h1 : ∑ w ∈ S, tau q u w = ∑' w, if w ∈ S then tau q u w else 0 :=
      ((tsum_eq_sum (s := S) fun w hw => ite_eq_right hw).trans
        (Finset.sum_congr rfl fun w hw => ite_eq_left hw)).symm
    rw [chi_eq_tsum_tau, h1, ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    split_ifs <;> simp
  have htau : ∀ w, tau q u w ≠ ⊤ := fun w => ne_top_of_le_ne_top ENNReal.one_ne_top
    (tau_le_one q u w)
  rw [hsplit] at hu ⊢
  rw [ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun w _ => htau w) (ENNReal.add_ne_top.1 hu).2,
    ENNReal.toReal_sum fun w _ => htau w,
    ENNReal.tsum_toReal_eq fun w => by split_ifs <;> simp [htau]]
  congr 1
  exact tsum_congr fun w => by split_ifs <;> simp

open Classical in
/-- **Second inequality.** `(χ_min |S| - ∑_{u,v ∈ S} τ(u,v))₊ ≤ L(S)`, so the
positive-part square is at most `L(S)²` over any nonnegative denominator. -/
theorem posPart_sq_div_le_boundarySum_sq_div (q : Sym2 V → unitInterval)
    (hχ : (⨆ u, chi q u) ≠ ⊤) {D : ℝ} (hD : 0 ≤ D) :
    (max ((⨅ u, chi q u).toReal * S.card - ∑ u ∈ S, ∑ v ∈ S, (tau q u v).toReal) 0) ^ 2 / D ≤
      (∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau q u w).toReal) ^ 2 / D := by
  have hfin : ∀ u, chi q u ≠ ⊤ := fun u => ne_top_of_le_ne_top hχ (le_iSup _ u)
  have hL0 : 0 ≤ ∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau q u w).toReal :=
    Finset.sum_nonneg fun u _ => tsum_nonneg fun w => by
      split_ifs
      · exact le_rfl
      · exact ENNReal.toReal_nonneg
  have hle : (⨅ u, chi q u).toReal * S.card - ∑ u ∈ S, ∑ v ∈ S, (tau q u v).toReal ≤
      ∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau q u w).toReal := by
    have h1 : (⨅ u, chi q u).toReal * S.card ≤ ∑ u ∈ S, (chi q u).toReal := by
      rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun u _ =>
        ENNReal.toReal_mono (hfin u) (iInf_le _ u)
    have h2 : ∑ u ∈ S, (chi q u).toReal = ∑ u ∈ S, ∑ v ∈ S, (tau q u v).toReal +
        ∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau q u w).toReal := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => toReal_chi_eq_add S q u (hfin u)
    linarith
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (le_max_right _ _) (max_le hle hL0) 2) hD

open Classical in
/-- **Boundary susceptibility bound.** In the intensity family with off-diagonal row sums of `J` at
most `1` and `χ_max < ∞`, for every finite `S`,
`Φ_β(S) ≥ L(S)² / (β² χ_max Q(S)) ≥ (χ_min |S| - ∑_{u,v ∈ S} τ(u,v))₊² / (β² χ_max Q(S))`. -/
theorem boundary_susceptibility_bound
    (hJ : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u ≤ 1)
    (hχ : (⨆ u, chi (intensityProfile J β) u) ≠ ⊤) :
    (∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau (intensityProfile J β) u w).toReal) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) ≤
      boundarySusceptibility J β S ∧
    (max ((⨅ u, chi (intensityProfile J β) u).toReal * S.card -
          ∑ u ∈ S, ∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) 0) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) ≤
      (∑ u ∈ S, ∑' w, if w ∈ S then 0 else (tau (intensityProfile J β) u w).toReal) ^ 2 /
        ((β : ℝ) ^ 2 * (⨆ u, chi (intensityProfile J β) u).toReal *
          ∑ u ∈ S, (∑ v ∈ S, (tau (intensityProfile J β) u v).toReal) ^ 2) :=
  ⟨boundarySum_sq_div_le J β S hJ hχ,
    posPart_sq_div_le_boundarySum_sq_div S _ hχ (by positivity)⟩

end Real

/-! ### Non-vacuity -/

/-- `tau_le_deleted_add` with `S = ∅`: deleting nothing loses nothing, and both bounds are
equalities. -/
example [Countable V] (q : Sym2 V → unitInterval) (y w : V) :
    law q (localConn (∅ : Set V)ᶜ y w) = tau q y w := by
  refine le_antisymm (law_deleted_le_tau q ∅ y w) ?_
  simpa using tau_le_deleted_add q ∅ y w

/-- `tau_le_deleted_add` with `S = {1}` on the path `0 - 1 - 2`. -/
example (q : Sym2 (Fin 3) → unitInterval) :
    tau q 0 2 ≤ law q (localConn ({1} : Set (Fin 3))ᶜ 0 2) +
      ∑' c : ({1} : Set (Fin 3)), tau q 0 c * tau q c 2 :=
  tau_le_deleted_add q {1} 0 2

/-- On two vertices with `J = 1` on the one pair, the hypotheses of `boundary_susceptibility_bound`
hold at every `β`: the row sums are `1` and every susceptibility is at most `2`. -/
example (β : ℝ≥0) :=
  boundary_susceptibility_bound (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0) β
    {false}
    (fun u => by cases u <;> simp [rowSum_def, tsum_fintype, Sym2.eq_swap])
    (by
      refine ne_top_of_le_ne_top (b := 2) ENNReal.ofNat_ne_top (iSup_le fun u => ?_)
      rw [chi_eq_tsum_tau, tsum_fintype, Fintype.sum_bool]
      calc _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add (tau_le_one _ _ _) (tau_le_one _ _ _)
        _ = 2 := one_add_one_eq_two)

end PercLib.Percolation.Bond
