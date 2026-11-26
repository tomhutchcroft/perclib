/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions and proofs, written on 2026-11-21. No upstream code is copied.
Mathematical reference: G. Grimmett, Percolation, 2nd ed., Springer, 1999, Section 11.2
(planar duality, pp. 283-286).
-/
module

public import Mathlib.Data.Pi.Interval
public import PercLib.Models.Lattice
public import PercLib.Percolation.Bond.Basic

/-!
# The square lattice and its dual: definitions

Vocabulary for planar duality of bond percolation on the square lattice `zdGraph 2`, on the
bond interface of the library: a configuration is a `Set (Sym2 (LatticeSite 2))`, and only its
nearest-neighbour pairs are used here.

* **Crossings.** `crossing i lo hi` is the event that the box `Set.Icc lo hi` of `ℤ^d` is
  crossed in direction `i` by a path of open nearest-neighbour edges inside the box.
* **The dual lattice.** The dual lattice `ℤ² + (1/2, 1/2)` is a second copy of `ℤ²`: the dual
  vertex `f` stands for the unit face with lower-left corner `f`, centred at `f + (1/2, 1/2)`.
  The dual edge `dualEdge e` of an edge `e` is the quarter turn of `e` about its midpoint, the
  unique dual edge crossing `e`. It is a bijection of the edge set (`dualEdgeEquiv`), and the
  dual configuration `dualConfig ω` opens a dual edge exactly when the edge it crosses is
  closed in `ω`.
* **The corner lattice.** A point `s` of `ℤ²` also stands for a corner: the vertex
  `cornerVertex s` of the face `cornerFace s`, where `s = cornerVertex s + cornerFace s`. The
  corner lies on one horizontal edge `cornerHEdge s` and one vertical edge `cornerVEdge s` of
  its face. The involution `hPartner ω` pairs the two corners on the same side of
  `cornerHEdge s` when that edge is open, and the two corners on the same side of its dual edge
  when it is closed; `vPartner ω` does the same with `cornerVEdge s`. Together they are the
  loop representation of `ω`: the interface between the open clusters and the dual clusters.

## Main definitions

* `PercLib.Models.Planar.crossing`
* `PercLib.Models.Planar.dualEdge`, `PercLib.Models.Planar.dualEdgeEquiv`,
  `PercLib.Models.Planar.dualConfig`
* `PercLib.Models.Planar.cornerVertex`, `PercLib.Models.Planar.cornerFace`,
  `PercLib.Models.Planar.cornerHEdge`, `PercLib.Models.Planar.cornerVEdge`,
  `PercLib.Models.Planar.hPartner`, `PercLib.Models.Planar.vPartner`

## Main results

* `mem_edgeSet_zdGraph_two_iff`: every edge of `ℤ²` is `{(x, y), (x + 1, y)}` or
  `{(x, y), (x, y + 1)}`.
* `dualEdge_horizontal`, `dualEdge_vertical`: the dual of `{(x, y), (x + 1, y)}` is
  `{(x, y - 1), (x, y)}` and the dual of `{(x, y), (x, y + 1)}` is `{(x - 1, y), (x, y)}`.
* `dualEdge_mem_dualConfig_iff`: a dual edge is open exactly when the edge it crosses is
  closed.
* `measurableSet_crossing`, `isUpperSet_crossing`, `measurable_dualConfig`.
* `hPartner_hPartner`, `vPartner_vPartner`, `hPartner_ne`, `vPartner_ne`: the partner maps
  are involutions without fixed points.
-/

@[expose] public section

noncomputable section

open Set PercLib.Percolation.Bond PercLib.Models.Site

namespace PercLib.Models.Planar

/-! ### Points and edges of `ℤ²` -/

/-- A point of `ℤ²` is the vector of its two coordinates. -/
theorem eq_vec_two (v : LatticeSite 2) : v = ![v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

/-- A point of `ℤ²` is `![a, b]` exactly when its coordinates are `a` and `b`. -/
theorem eq_vec_two_iff {v : LatticeSite 2} {a b : ℤ} : v = ![a, b] ↔ v 0 = a ∧ v 1 = b := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    rw [eq_vec_two v, h0, h1]

/-- Two unordered pairs of points of `ℤ²` given by coordinates agree when the coordinates do. -/
theorem sym2_vec_two_eq {a b c d a' b' c' d' : ℤ} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c')
    (h₄ : d = d') : s(![a, b], ![c, d]) = s(![a', b'], ![c', d']) := by
  subst h₁ h₂ h₃ h₄
  rfl

theorem vec_two_add (a b : ℤ) (c : LatticeSite 2) : ![a, b] + c = ![a + c 0, b + c 1] := by
  funext i
  fin_cases i <;> simp

theorem vec_two_sub (a b : ℤ) (c : LatticeSite 2) : ![a, b] - c = ![a - c 0, b - c 1] := by
  funext i
  fin_cases i <;> simp

/-- Membership in a box of `ℤ²`, coordinate by coordinate. -/
theorem mem_Icc_two_iff {v lo hi : LatticeSite 2} :
    v ∈ Icc lo hi ↔ lo 0 ≤ v 0 ∧ v 0 ≤ hi 0 ∧ lo 1 ≤ v 1 ∧ v 1 ≤ hi 1 := by
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_two]
  tauto

/-- **Adjacency in `ℤ²`.** Two points are adjacent when they differ by one in one coordinate and
agree in the other. -/
theorem zdGraph_two_adj_iff (u v : LatticeSite 2) :
    (zdGraph 2).Adj u v ↔ (u 0 = v 0 ∧ (u 1 + 1 = v 1 ∨ v 1 + 1 = u 1)) ∨
      (u 1 = v 1 ∧ (u 0 + 1 = v 0 ∨ v 0 + 1 = u 0)) := by
  rw [zdGraph_adj_iff_exists, Fin.exists_fin_two]
  simp only [Fin.forall_fin_two, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and,
    Fin.isValue, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    not_false_eq_true, forall_const, and_true]
  tauto

/-- **The edges of `ℤ²`.** Every edge is horizontal, `{(x, y), (x + 1, y)}`, or vertical,
`{(x, y), (x, y + 1)}`. -/
theorem mem_edgeSet_zdGraph_two_iff (e : Sym2 (LatticeSite 2)) :
    e ∈ (zdGraph 2).edgeSet ↔
      ∃ x y : ℤ, e = s(![x, y], ![x + 1, y]) ∨ e = s(![x, y], ![x, y + 1]) := by
  induction e using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
    constructor
    · rintro (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
      · exact ⟨u 0, u 1, Or.inr (Sym2.eq_iff.2 (Or.inl
          ⟨eq_vec_two u, eq_vec_two_iff.2 ⟨h0.symm, h1.symm⟩⟩))⟩
      · exact ⟨v 0, v 1, Or.inr (Sym2.eq_iff.2 (Or.inr
          ⟨eq_vec_two_iff.2 ⟨h0, h1.symm⟩, eq_vec_two v⟩))⟩
      · exact ⟨u 0, u 1, Or.inl (Sym2.eq_iff.2 (Or.inl
          ⟨eq_vec_two u, eq_vec_two_iff.2 ⟨h0.symm, h1.symm⟩⟩))⟩
      · exact ⟨v 0, v 1, Or.inl (Sym2.eq_iff.2 (Or.inr
          ⟨eq_vec_two_iff.2 ⟨h0.symm, h1⟩, eq_vec_two v⟩))⟩
    · rintro ⟨x, y, h | h⟩ <;> rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- The horizontal edge `{(x, y), (x + 1, y)}` is an edge of `ℤ²`. -/
theorem horizontal_mem_edgeSet (x y : ℤ) :
    s(![x, y], ![x + 1, y]) ∈ (zdGraph 2).edgeSet :=
  (mem_edgeSet_zdGraph_two_iff _).2 ⟨x, y, Or.inl rfl⟩

/-- The vertical edge `{(x, y), (x, y + 1)}` is an edge of `ℤ²`. -/
theorem vertical_mem_edgeSet (x y : ℤ) :
    s(![x, y], ![x, y + 1]) ∈ (zdGraph 2).edgeSet :=
  (mem_edgeSet_zdGraph_two_iff _).2 ⟨x, y, Or.inr rfl⟩

/-- Translations preserve the edges of `ℤ²`. -/
theorem map_add_mem_edgeSet {e : Sym2 (LatticeSite 2)} (c : LatticeSite 2)
    (he : e ∈ (zdGraph 2).edgeSet) : Sym2.map (· + c) e ∈ (zdGraph 2).edgeSet := by
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := 2) c
  induction e using Sym2.ind with
  | h u v =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, ← hφ, ← hφ]
    exact φ.map_adj_iff.2 he

/-! ### Crossings of boxes -/

section Crossing

variable {d : ℕ}

/-- The **open crossing** of the box `Set.Icc lo hi` of `ℤ^d` in direction `i`: some vertex of
the box with `i`-th coordinate `lo i` is joined to some vertex of the box with `i`-th coordinate
`hi i` by a path of open nearest-neighbour edges all of whose vertices lie in the box. Open
pairs that are not edges of `zdGraph d` are ignored. In `ℤ²`, `crossing 0` is a left-right
crossing and `crossing 1` a bottom-top crossing. The box is closed. A box of width zero in
direction `i` (`lo ≤ hi`, `lo i = hi i`) is crossed by every configuration
(`crossing_eq_univ_of_eq`), and an empty box (`¬lo ≤ hi`) by none
(`crossing_eq_empty_of_not_le`). -/
def crossing (i : Fin d) (lo hi : LatticeSite d) : Set (Config (LatticeSite d)) :=
  {ω | ∃ a ∈ Icc lo hi, a i = lo i ∧ ∃ b ∈ Icc lo hi, b i = hi i ∧
    ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b}

theorem mem_crossing_iff (i : Fin d) (lo hi : LatticeSite d) (ω : Config (LatticeSite d)) :
    ω ∈ crossing i lo hi ↔ ∃ a ∈ Icc lo hi, a i = lo i ∧ ∃ b ∈ Icc lo hi, b i = hi i ∧
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b :=
  Iff.rfl

/-- A crossing depends only on the nearest-neighbour edges. -/
@[simp]
theorem inter_edgeSet_mem_crossing_iff (i : Fin d) (lo hi : LatticeSite d)
    (ω : Config (LatticeSite d)) :
    ω ∩ (zdGraph d).edgeSet ∈ crossing i lo hi ↔ ω ∈ crossing i lo hi := by
  simp only [mem_crossing_iff, inter_assoc, inter_self]

/-- A crossing is an increasing event. -/
theorem crossing_mono {i : Fin d} {lo hi : LatticeSite d} {ω ω' : Config (LatticeSite d)}
    (h : ω ⊆ ω') (hω : ω ∈ crossing i lo hi) : ω' ∈ crossing i lo hi := by
  obtain ⟨a, ha, hai, b, hb, hbi, hab⟩ := hω
  exact ⟨a, ha, hai, b, hb, hbi, localConn_mono (inter_subset_inter_left _ h) hab⟩

theorem isUpperSet_crossing (i : Fin d) (lo hi : LatticeSite d) :
    IsUpperSet (crossing i lo hi) :=
  fun _ _ h hω => crossing_mono h hω

/-- A crossing is a measurable event. -/
theorem measurableSet_crossing (i : Fin d) (lo hi : LatticeSite d) :
    MeasurableSet (crossing i lo hi) := by
  have h : crossing i lo hi = ⋃ a ∈ {a | a ∈ Icc lo hi ∧ a i = lo i},
      ⋃ b ∈ {b | b ∈ Icc lo hi ∧ b i = hi i},
        (fun ω : Config (LatticeSite d) => ω ∩ (zdGraph d).edgeSet) ⁻¹'
          localConn (Icc lo hi) a b := by
    ext ω
    simp only [mem_crossing_iff, mem_iUnion, mem_preimage, mem_ofPred_eq, exists_prop, and_assoc]
  rw [h]
  exact MeasurableSet.biUnion (to_countable _) fun a _ =>
    MeasurableSet.biUnion (to_countable _) fun b _ =>
      (measurableSet_localConn _ a b).preimage (by fun_prop)

/-- A box of width zero in direction `i` is crossed in every configuration. -/
theorem crossing_eq_univ_of_eq {i : Fin d} {lo hi : LatticeSite d} (hle : lo ≤ hi)
    (h : lo i = hi i) : crossing i lo hi = univ := by
  refine eq_univ_of_forall fun ω => ⟨lo, left_mem_Icc.2 hle, rfl, lo, left_mem_Icc.2 hle, h, ?_⟩
  rw [localConn_self (left_mem_Icc.2 hle)]
  exact mem_univ _

/-- An empty box is never crossed. -/
theorem crossing_eq_empty_of_not_le {i : Fin d} {lo hi : LatticeSite d} (h : ¬lo ≤ hi) :
    crossing i lo hi = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, ha, _⟩ => h (ha.1.trans ha.2)

/-- With no open edge, a box of positive width is not crossed: the event is not everything. -/
theorem empty_notMem_crossing {i : Fin d} {lo hi : LatticeSite d} (h : lo i < hi i) :
    (∅ : Config (LatticeSite d)) ∉ crossing i lo hi := by
  rintro ⟨a, -, hai, b, -, hbi, hab⟩
  rw [empty_inter] at hab
  have hab' := (empty_mem_conn_iff a b).1 (localConn_subset_conn _ a b hab)
  subst hab'
  omega

end Crossing

/-! ### The dual lattice -/

/-- The **dual edge** of a pair `{u, v}` of `ℤ²`: the quarter turn of `{u, v}` counterclockwise
about its midpoint, written in the coordinates of the dual lattice, where the dual vertex `f`
is the face centred at `f + (1/2, 1/2)`. For an edge `e` of `ℤ²` it is the unique dual edge
crossing `e` (`dualEdge_horizontal`, `dualEdge_vertical`). -/
def dualEdge : Sym2 (LatticeSite 2) → Sym2 (LatticeSite 2) :=
  Sym2.lift ⟨fun u v => s(![(u 0 + v 0 - u 1 + v 1 - 1) / 2, (u 0 - v 0 + u 1 + v 1 - 1) / 2],
    ![(v 0 + u 0 - v 1 + u 1 - 1) / 2, (v 0 - u 0 + v 1 + u 1 - 1) / 2]),
    fun _ _ => Sym2.eq_swap⟩

@[simp]
theorem dualEdge_mk (u v : LatticeSite 2) :
    dualEdge s(u, v) =
      s(![(u 0 + v 0 - u 1 + v 1 - 1) / 2, (u 0 - v 0 + u 1 + v 1 - 1) / 2],
        ![(v 0 + u 0 - v 1 + u 1 - 1) / 2, (v 0 - u 0 + v 1 + u 1 - 1) / 2]) :=
  rfl

/-- The dual of the horizontal edge `{(x, y), (x + 1, y)}` is the vertical dual edge
`{(x, y - 1), (x, y)}`: the faces below and above it. -/
theorem dualEdge_horizontal (x y : ℤ) :
    dualEdge s(![x, y], ![x + 1, y]) = s(![x, y - 1], ![x, y]) := by
  simp only [dualEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- The dual of the vertical edge `{(x, y), (x, y + 1)}` is the horizontal dual edge
`{(x - 1, y), (x, y)}`: the faces to its left and right. -/
theorem dualEdge_vertical (x y : ℤ) :
    dualEdge s(![x, y], ![x, y + 1]) = s(![x, y], ![x - 1, y]) := by
  simp only [dualEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- The dual edge commutes with translations. -/
theorem dualEdge_map_add (c : LatticeSite 2) (e : Sym2 (LatticeSite 2)) :
    dualEdge (Sym2.map (· + c) e) = Sym2.map (· + c) (dualEdge e) := by
  induction e using Sym2.ind with
  | h u v =>
    simp only [Sym2.map_mk, dualEdge_mk, Pi.add_apply, vec_two_add]
    exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- The dual of an edge of `ℤ²` is an edge. -/
theorem dualEdge_mem_edgeSet {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    dualEdge e ∈ (zdGraph 2).edgeSet := by
  obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal]
    simpa using vertical_mem_edgeSet x (y - 1)
  · rw [dualEdge_vertical, Sym2.eq_swap]
    simpa using horizontal_mem_edgeSet (x - 1) y

/-- Taking the dual twice translates an edge by `(-1, -1)`. -/
theorem dualEdge_dualEdge {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    dualEdge (dualEdge e) = Sym2.map (· - 1) e := by
  obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal]
    simp only [dualEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Sym2.map_mk, vec_two_sub,
      Pi.one_apply]
    rw [Sym2.eq_swap]
    exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · rw [dualEdge_vertical]
    simp only [dualEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Sym2.map_mk, vec_two_sub,
      Pi.one_apply]
    rw [Sym2.eq_swap]
    exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- Undoing the dual: translating the dual of the dual by `(1, 1)` gives the edge back. -/
theorem map_add_one_dualEdge_dualEdge {e : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) : Sym2.map (· + 1) (dualEdge (dualEdge e)) = e := by
  have h : ((fun v : LatticeSite 2 => v + 1) ∘ fun v => v - 1) = id := by
    funext v
    simp
  rw [dualEdge_dualEdge he, Sym2.map_map, h, Sym2.map_id, id]

/-- The **edge-dual bijection** of `ℤ²`: each edge is matched with the dual edge crossing it.
The dual edge set is identified with the edge set of `ℤ²` through the shift by
`(1/2, 1/2)`. -/
def dualEdgeEquiv : (zdGraph 2).edgeSet ≃ (zdGraph 2).edgeSet where
  toFun e := ⟨dualEdge e, dualEdge_mem_edgeSet e.2⟩
  invFun f := ⟨Sym2.map (· + 1) (dualEdge f), map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet f.2)⟩
  left_inv e := Subtype.ext (map_add_one_dualEdge_dualEdge e.2)
  right_inv f := Subtype.ext (by
    simp only
    rw [dualEdge_map_add, map_add_one_dualEdge_dualEdge f.2])

@[simp]
theorem dualEdgeEquiv_apply (e : (zdGraph 2).edgeSet) : (dualEdgeEquiv e : Sym2 _) = dualEdge e :=
  rfl

@[simp]
theorem dualEdgeEquiv_symm_apply (f : (zdGraph 2).edgeSet) :
    (dualEdgeEquiv.symm f : Sym2 _) = Sym2.map (· + 1) (dualEdge f) :=
  rfl

/-- Distinct edges have distinct duals. -/
theorem dualEdge_injOn : InjOn dualEdge (zdGraph 2).edgeSet := fun e he e' he' h => by
  have := dualEdgeEquiv.injective (a₁ := ⟨e, he⟩) (a₂ := ⟨e', he'⟩) (Subtype.ext h)
  exact congrArg Subtype.val this

/-- The **dual configuration**: the dual edge crossing an edge `e` of `ℤ²` is open when `e` is
closed in `ω`. Only edges of `ℤ²` enter. -/
def dualConfig (ω : Config (LatticeSite 2)) : Config (LatticeSite 2) :=
  dualEdge '' ((zdGraph 2).edgeSet \ ω)

theorem mem_dualConfig_iff' (ω : Config (LatticeSite 2)) (f : Sym2 (LatticeSite 2)) :
    f ∈ dualConfig ω ↔ ∃ e ∈ (zdGraph 2).edgeSet, e ∉ ω ∧ dualEdge e = f := by
  simp [dualConfig, and_assoc]

/-- **A dual edge is open exactly when the edge it crosses is closed.** -/
@[simp]
theorem dualEdge_mem_dualConfig_iff {ω : Config (LatticeSite 2)} {e : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) : dualEdge e ∈ dualConfig ω ↔ e ∉ ω := by
  rw [mem_dualConfig_iff']
  constructor
  · rintro ⟨e', he', hω, h⟩
    rwa [← dualEdge_injOn he' he h]
  · exact fun h => ⟨e, he, h, rfl⟩

/-- Membership in the dual configuration, through the inverse of the dual map. -/
theorem mem_dualConfig_iff (ω : Config (LatticeSite 2)) (f : Sym2 (LatticeSite 2)) :
    f ∈ dualConfig ω ↔ f ∈ (zdGraph 2).edgeSet ∧ Sym2.map (· + 1) (dualEdge f) ∉ ω := by
  constructor
  · rintro ⟨e, ⟨he, hω⟩, rfl⟩
    exact ⟨dualEdge_mem_edgeSet he, by rwa [map_add_one_dualEdge_dualEdge he]⟩
  · rintro ⟨hf, hω⟩
    have he := map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hf)
    have hfe : dualEdge (Sym2.map (· + 1) (dualEdge f)) = f :=
      congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨f, hf⟩)
    rw [← hfe]
    exact (dualEdge_mem_dualConfig_iff he).2 hω

/-- The dual configuration uses only edges of `ℤ²`. -/
theorem dualConfig_subset_edgeSet (ω : Config (LatticeSite 2)) :
    dualConfig ω ⊆ (zdGraph 2).edgeSet := by
  rintro _ ⟨e, ⟨he, -⟩, rfl⟩
  exact dualEdge_mem_edgeSet he

/-- Opening edges closes dual edges. -/
theorem dualConfig_anti : Antitone dualConfig :=
  fun _ _ h => image_mono (sdiff_subset_sdiff_right h)

/-- The dual configuration depends only on the edges of `ℤ²`. -/
@[simp]
theorem dualConfig_inter_edgeSet (ω : Config (LatticeSite 2)) :
    dualConfig (ω ∩ (zdGraph 2).edgeSet) = dualConfig ω := by
  rw [dualConfig, dualConfig, sdiff_inter_self_eq_sdiff]

/-- With every edge closed, every dual edge is open. -/
@[simp]
theorem dualConfig_empty : dualConfig ∅ = (zdGraph 2).edgeSet := by
  refine (dualConfig_subset_edgeSet _).antisymm fun f hf => ?_
  rw [mem_dualConfig_iff]
  exact ⟨hf, notMem_empty _⟩

/-- With every edge open, every dual edge is closed. -/
@[simp]
theorem dualConfig_univ : dualConfig univ = ∅ := by
  rw [dualConfig, sdiff_univ, image_empty]

/-- The dual configuration is a measurable function of the configuration. -/
theorem measurable_dualConfig : Measurable dualConfig := by
  refine Measurable.of_mem fun f => ?_
  simp_rw [mem_dualConfig_iff]
  exact measurable_const.and (measurable_set_mem _).not

/-! ### The corner lattice -/

/-- The vertex of the corner `s`: the point `s` of the corner lattice stands for the vertex
`cornerVertex s` of the face `cornerFace s`, and `s = cornerVertex s + cornerFace s`. -/
def cornerVertex (s : LatticeSite 2) : LatticeSite 2 := fun i => (s i + 1) / 2

/-- The face of the corner `s`, a vertex of the dual lattice. -/
def cornerFace (s : LatticeSite 2) : LatticeSite 2 := fun i => s i / 2

@[simp]
theorem cornerVertex_apply (s : LatticeSite 2) (i : Fin 2) : cornerVertex s i = (s i + 1) / 2 :=
  rfl

@[simp]
theorem cornerFace_apply (s : LatticeSite 2) (i : Fin 2) : cornerFace s i = s i / 2 :=
  rfl

/-- A corner is the sum of its vertex and its face. -/
theorem cornerVertex_add_cornerFace (s : LatticeSite 2) : cornerVertex s + cornerFace s = s := by
  funext i
  simp only [Pi.add_apply, cornerVertex_apply, cornerFace_apply]
  omega

/-- The vertex of a corner is a corner of its face: it is `cornerFace s + δ` with
`δ ∈ {0, 1}²`. -/
theorem cornerFace_le_cornerVertex (s : LatticeSite 2) (i : Fin 2) :
    cornerFace s i ≤ cornerVertex s i ∧ cornerVertex s i ≤ cornerFace s i + 1 := by
  simp only [cornerVertex_apply, cornerFace_apply]
  omega

/-- The horizontal edge of the face of `s` through the vertex of `s`. -/
def cornerHEdge (s : LatticeSite 2) : Sym2 (LatticeSite 2) :=
  s(![cornerFace s 0, cornerVertex s 1], ![cornerFace s 0 + 1, cornerVertex s 1])

/-- The vertical edge of the face of `s` through the vertex of `s`. -/
def cornerVEdge (s : LatticeSite 2) : Sym2 (LatticeSite 2) :=
  s(![cornerVertex s 0, cornerFace s 1], ![cornerVertex s 0, cornerFace s 1 + 1])

theorem cornerHEdge_eq (s : LatticeSite 2) :
    cornerHEdge s = s(![s 0 / 2, (s 1 + 1) / 2], ![s 0 / 2 + 1, (s 1 + 1) / 2]) :=
  rfl

theorem cornerVEdge_eq (s : LatticeSite 2) :
    cornerVEdge s = s(![(s 0 + 1) / 2, s 1 / 2], ![(s 0 + 1) / 2, s 1 / 2 + 1]) :=
  rfl

theorem cornerHEdge_mem_edgeSet (s : LatticeSite 2) : cornerHEdge s ∈ (zdGraph 2).edgeSet :=
  horizontal_mem_edgeSet _ _

theorem cornerVEdge_mem_edgeSet (s : LatticeSite 2) : cornerVEdge s ∈ (zdGraph 2).edgeSet :=
  vertical_mem_edgeSet _ _

/-- The vertex of a corner is an endpoint of its horizontal edge. -/
theorem cornerVertex_mem_cornerHEdge (s : LatticeSite 2) : cornerVertex s ∈ cornerHEdge s := by
  rw [cornerHEdge, Sym2.mem_iff]
  rcases (cornerFace_le_cornerVertex s 0) with ⟨h1, h2⟩
  rcases h1.eq_or_lt with h | h
  · exact Or.inl (eq_vec_two_iff.2 ⟨h.symm, rfl⟩)
  · exact Or.inr (eq_vec_two_iff.2 ⟨by omega, rfl⟩)

/-- The vertex of a corner is an endpoint of its vertical edge. -/
theorem cornerVertex_mem_cornerVEdge (s : LatticeSite 2) : cornerVertex s ∈ cornerVEdge s := by
  rw [cornerVEdge, Sym2.mem_iff]
  rcases (cornerFace_le_cornerVertex s 1) with ⟨h1, h2⟩
  rcases h1.eq_or_lt with h | h
  · exact Or.inl (eq_vec_two_iff.2 ⟨rfl, h.symm⟩)
  · exact Or.inr (eq_vec_two_iff.2 ⟨rfl, by omega⟩)

/-- The face of a corner is an endpoint of the dual of its horizontal edge. -/
theorem cornerFace_mem_dualEdge_cornerHEdge (s : LatticeSite 2) :
    cornerFace s ∈ dualEdge (cornerHEdge s) := by
  rw [cornerHEdge, dualEdge_horizontal, Sym2.mem_iff]
  rcases (cornerFace_le_cornerVertex s 1) with ⟨h1, h2⟩
  rcases h1.eq_or_lt with h | h
  · exact Or.inr (eq_vec_two_iff.2 ⟨rfl, h⟩)
  · exact Or.inl (eq_vec_two_iff.2 ⟨rfl, by omega⟩)

/-- The face of a corner is an endpoint of the dual of its vertical edge. -/
theorem cornerFace_mem_dualEdge_cornerVEdge (s : LatticeSite 2) :
    cornerFace s ∈ dualEdge (cornerVEdge s) := by
  rw [cornerVEdge, dualEdge_vertical, Sym2.mem_iff]
  rcases (cornerFace_le_cornerVertex s 0) with ⟨h1, h2⟩
  rcases h1.eq_or_lt with h | h
  · exact Or.inl (eq_vec_two_iff.2 ⟨h, rfl⟩)
  · exact Or.inr (eq_vec_two_iff.2 ⟨by omega, rfl⟩)

open Classical in
/-- The **horizontal partner** of the corner `s` in the loop representation of `ω`. If the
horizontal edge `cornerHEdge s` is open, it is the corner of the same face at the other end of
that edge; if it is closed, it is the corner at the same vertex of the face across that edge.
In coordinates the first moves `s` horizontally within `{2k, 2k + 1}`, the second vertically
within `{2k - 1, 2k}`. -/
def hPartner (ω : Config (LatticeSite 2)) (s : LatticeSite 2) : LatticeSite 2 :=
  if cornerHEdge s ∈ ω then ![s 0 + 1 - 2 * (s 0 % 2), s 1]
  else ![s 0, s 1 - 1 + 2 * (s 1 % 2)]

open Classical in
/-- The **vertical partner** of the corner `s` in the loop representation of `ω`. If the vertical
edge `cornerVEdge s` is open, it is the corner of the same face at the other end of that edge;
if it is closed, it is the corner at the same vertex of the face across that edge. In
coordinates the first moves `s` vertically within `{2k, 2k + 1}`, the second horizontally
within `{2k - 1, 2k}`. -/
def vPartner (ω : Config (LatticeSite 2)) (s : LatticeSite 2) : LatticeSite 2 :=
  if cornerVEdge s ∈ ω then ![s 0, s 1 + 1 - 2 * (s 1 % 2)]
  else ![s 0 - 1 + 2 * (s 0 % 2), s 1]

theorem hPartner_of_mem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerHEdge s ∈ ω) : hPartner ω s = ![s 0 + 1 - 2 * (s 0 % 2), s 1] := by
  rw [hPartner, ite_eq_left h]

theorem hPartner_of_notMem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerHEdge s ∉ ω) : hPartner ω s = ![s 0, s 1 - 1 + 2 * (s 1 % 2)] := by
  rw [hPartner, ite_eq_right h]

theorem vPartner_of_mem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerVEdge s ∈ ω) : vPartner ω s = ![s 0, s 1 + 1 - 2 * (s 1 % 2)] := by
  rw [vPartner, ite_eq_left h]

theorem vPartner_of_notMem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerVEdge s ∉ ω) : vPartner ω s = ![s 0 - 1 + 2 * (s 0 % 2), s 1] := by
  rw [vPartner, ite_eq_right h]

/-- With every edge closed, the horizontal partner is the corner across the horizontal edge. -/
@[simp]
theorem hPartner_empty (s : LatticeSite 2) : hPartner ∅ s = ![s 0, s 1 - 1 + 2 * (s 1 % 2)] :=
  hPartner_of_notMem (notMem_empty _)

/-- With every edge closed, the vertical partner is the corner across the vertical edge. -/
@[simp]
theorem vPartner_empty (s : LatticeSite 2) : vPartner ∅ s = ![s 0 - 1 + 2 * (s 0 % 2), s 1] :=
  vPartner_of_notMem (notMem_empty _)

/-- A corner and its horizontal partner share their horizontal edge. -/
@[simp]
theorem cornerHEdge_hPartner (ω : Config (LatticeSite 2)) (s : LatticeSite 2) :
    cornerHEdge (hPartner ω s) = cornerHEdge s := by
  by_cases h : cornerHEdge s ∈ ω
  · rw [hPartner_of_mem h, cornerHEdge_eq, cornerHEdge_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases Int.emod_two_eq_zero_or_one (s 0) with h0 | h0 <;>
      exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · rw [hPartner_of_notMem h, cornerHEdge_eq, cornerHEdge_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases Int.emod_two_eq_zero_or_one (s 1) with h1 | h1 <;>
      exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- A corner and its vertical partner share their vertical edge. -/
@[simp]
theorem cornerVEdge_vPartner (ω : Config (LatticeSite 2)) (s : LatticeSite 2) :
    cornerVEdge (vPartner ω s) = cornerVEdge s := by
  by_cases h : cornerVEdge s ∈ ω
  · rw [vPartner_of_mem h, cornerVEdge_eq, cornerVEdge_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases Int.emod_two_eq_zero_or_one (s 1) with h1 | h1 <;>
      exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · rw [vPartner_of_notMem h, cornerVEdge_eq, cornerVEdge_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases Int.emod_two_eq_zero_or_one (s 0) with h0 | h0 <;>
      exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- The horizontal partner map is an involution. -/
@[simp]
theorem hPartner_hPartner (ω : Config (LatticeSite 2)) (s : LatticeSite 2) :
    hPartner ω (hPartner ω s) = s := by
  by_cases h : cornerHEdge s ∈ ω
  · have h' : cornerHEdge (hPartner ω s) ∈ ω := by rwa [cornerHEdge_hPartner]
    rw [hPartner_of_mem h', hPartner_of_mem h, eq_comm, eq_vec_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_true]
    rcases Int.emod_two_eq_zero_or_one (s 0) with h0 | h0 <;> omega
  · have h' : cornerHEdge (hPartner ω s) ∉ ω := by rwa [cornerHEdge_hPartner]
    rw [hPartner_of_notMem h', hPartner_of_notMem h, eq_comm, eq_vec_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
    rcases Int.emod_two_eq_zero_or_one (s 1) with h1 | h1 <;> omega

/-- The vertical partner map is an involution. -/
@[simp]
theorem vPartner_vPartner (ω : Config (LatticeSite 2)) (s : LatticeSite 2) :
    vPartner ω (vPartner ω s) = s := by
  by_cases h : cornerVEdge s ∈ ω
  · have h' : cornerVEdge (vPartner ω s) ∈ ω := by rwa [cornerVEdge_vPartner]
    rw [vPartner_of_mem h', vPartner_of_mem h, eq_comm, eq_vec_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
    rcases Int.emod_two_eq_zero_or_one (s 1) with h1 | h1 <;> omega
  · have h' : cornerVEdge (vPartner ω s) ∉ ω := by rwa [cornerVEdge_vPartner]
    rw [vPartner_of_notMem h', vPartner_of_notMem h, eq_comm, eq_vec_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_true]
    rcases Int.emod_two_eq_zero_or_one (s 0) with h0 | h0 <;> omega

theorem hPartner_involutive (ω : Config (LatticeSite 2)) : Function.Involutive (hPartner ω) :=
  hPartner_hPartner ω

theorem vPartner_involutive (ω : Config (LatticeSite 2)) : Function.Involutive (vPartner ω) :=
  vPartner_vPartner ω

/-- No corner is its own horizontal partner. -/
theorem hPartner_ne (ω : Config (LatticeSite 2)) (s : LatticeSite 2) : hPartner ω s ≠ s := by
  intro h
  by_cases hs : cornerHEdge s ∈ ω
  · rw [hPartner_of_mem hs, eq_comm, eq_vec_two_iff] at h
    rcases Int.emod_two_eq_zero_or_one (s 0) with h0 | h0 <;> omega
  · rw [hPartner_of_notMem hs, eq_comm, eq_vec_two_iff] at h
    rcases Int.emod_two_eq_zero_or_one (s 1) with h1 | h1 <;> omega

/-- No corner is its own vertical partner. -/
theorem vPartner_ne (ω : Config (LatticeSite 2)) (s : LatticeSite 2) : vPartner ω s ≠ s := by
  intro h
  by_cases hs : cornerVEdge s ∈ ω
  · rw [vPartner_of_mem hs, eq_comm, eq_vec_two_iff] at h
    rcases Int.emod_two_eq_zero_or_one (s 1) with h1 | h1 <;> omega
  · rw [vPartner_of_notMem hs, eq_comm, eq_vec_two_iff] at h
    rcases Int.emod_two_eq_zero_or_one (s 0) with h0 | h0 <;> omega

/-! ### Non-vacuity -/

/-- The edge `{(0, 0), (1, 0)}` and the dual edge `{(0, -1), (0, 0)}` crossing it: with no edge
open, the dual edge is open, and with every edge open it is closed. -/
example : s(![(0 : ℤ), -1], ![0, 0]) ∈ dualConfig ∅ ∧
    s(![(0 : ℤ), -1], ![0, 0]) ∉ dualConfig univ := by
  have h := dualEdge_horizontal 0 0
  simp only [zero_add, zero_sub] at h
  rw [← h, dualEdge_mem_dualConfig_iff (by simpa using horizontal_mem_edgeSet 0 0),
    dualEdge_mem_dualConfig_iff (by simpa using horizontal_mem_edgeSet 0 0)]
  exact ⟨notMem_empty _, not_not.2 (mem_univ _)⟩

/-- A box of `ℤ²` of positive width is not crossed when every edge is closed. -/
example : (∅ : Config (LatticeSite 2)) ∉ crossing 0 0 ![1, 0] :=
  empty_notMem_crossing (by simp)

end PercLib.Models.Planar
