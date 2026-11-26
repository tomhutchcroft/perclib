/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions and proofs, written on 2026-11-22, 2026-11-23 and 2026-11-24. No upstream code
is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (separated arms, Theorem 11 and Lemma 15).
-/
module

public import PercLib.Models.Planar.Arms.Defs

/-!
# Arms separated at the boundaries of an annulus

Nolin's separation theorem (Theorem 11) says that, up to a constant factor, the arms of a
multi-arm event can be chosen *separated*: their ends are far apart, far from the corners, and
each carries a small fence of its colour beyond the boundary, along which the arms are later
extended or glued at a bounded cost. This file defines separation at the outer boundary and at
the inner boundary of the annulus between `B_r(z)` and `B_R(z)`, on the arm events of
`PercLib.Models.Planar.Arms.Defs`, at three levels: one arm, a family of arms, and the event.

* **Fences.** `HasOuterFence ω c z R M K γ`: the arm `γ` of colour `c` (open for `c = true`,
  dual for `c = false`) ends at `b`, its last vertex or last face, on one of the four sides of
  `B_R(z)`, and carries a fence there: a path of its colour from one end to the other of the box
  of length `2K` along the side and depth `M` outside `B_R(z)` standing on the side at `b` (on
  the top side, from the column `b₀ - K` to the column `b₀ + K` inside
  `[b₀ - K, b₀ + K] × [b₁, b₁ + M]`), whose first end is joined in the colour of the arm to a
  vertex (face) of the arm inside the box of radius `M` about `b`. For a dual arm the paths are
  walks of faces along dual edges open in `dualConfig ω`, and the sides are read off the last
  face: `b₁ = z₁ + R` (top), `b₀ = z₀ + R` (right), `b₁ = z₁ - R - 1` (bottom),
  `b₀ = z₀ - R - 1` (left); for an open arm the last two are `b₁ = z₁ - R` and `b₀ = z₀ - R`.
* **Separated families.** `ArmsOuterSeparated ω σ z R s M K γ`: the landing positions of the
  arms on the boundary of `B_R(z)` (`landingPos`, on the doubled lattice) are pairwise at least
  `s` apart and at least `s` from the doubled corners `4 m R`, and every arm has a fence.
* **The separated event.** `outerSeparatedArmEvent σ z r R s M K`: the `j`-arm event
  `multiArmEvent σ z r R` witnessed by a separated family: a disjoint family of arms of colours
  `σ` from `B_r(z)` to the boundary of `B_R(z)`, landing in counterclockwise order, separated
  with fences.

* **Inner fences and inner separation.** `HasInnerFence ω c z r M K γ`,
  `ArmsInnerSeparated ω σ z r s M K γ` and `innerSeparatedArmEvent σ z r R s M K`: the mirror
  images at the start `a` of each arm (its first vertex or face, on a side of `B_r(z)`), with the
  fence box of length `2K` and depth `M` standing at `a` *inside* `B_r(z)` (on the top side
  `[a₀ - K, a₀ + K] × [a₁ - M, a₁]`), and the inner positions (`innerPos`, on the boundary of the
  doubled box `2z + [-(2r + 1), 2r + 1]²`, corners at the multiples of `4r + 2`) separated.

In Nolin's outer separation step, with `R = 2N + 1` and separation scale `η`, the parameters are
`s = 4 √η N`, `M = ⌊√η N⌋` and `K = ⌊η N⌋`.

## Main definitions

* `PercLib.Models.Planar.HasOuterFence`
* `PercLib.Models.Planar.ArmsOuterSeparated`
* `PercLib.Models.Planar.outerSeparatedArmEvent`
* `PercLib.Models.Planar.HasInnerFence`
* `PercLib.Models.Planar.ArmsInnerSeparated`
* `PercLib.Models.Planar.innerSeparatedArmEvent`

## Main results

* `mem_outerSeparatedArmEvent_iff`: membership in the event, written out in full.
* `outerSeparatedArmEvent_subset_multiArmEvent`: separated arms are arms.
* `HasOuterFence.mono`, `ArmsOuterSeparated.mono`, `outerSeparatedArmEvent_mono`: the event
  shrinks when the separation `s` grows and grows with the depth `M` of the fences.
* `outerSeparatedArmEvent_fin_zero`: with no arm the event is everything.
* `measurableSet_setOf_hasOuterFence`, `measurableSet_outerSeparatedArmEvent`: measurability.
* `dualConfig_inter_eq_of_inter_eq`, `cond_inter_edgeSet_mem_localConn_iff_of_inter_eq`,
  `hasOuterFence_iff_of_inter_eq`, `mem_outerSeparatedArmEvent_iff_of_inter_eq`: determination;
  for `r < R` the event is determined by the edges with both ends in `B_{R + M + K + 1}(z)`.
* `HasOuterFence.map_add`, `image_add_mem_outerSeparatedArmEvent_iff`: translation.
* `IsArm.end_mem_Icc`: an arm from a box inside the interior of the outer box ends in the outer
  box (open arm) or at a face just outside it (dual arm); `IsArm.start_mem_Icc`: an arm from
  `B_r(z)` starts in `Icc (z - r - 1) (z + r)`.
* The same API for the inner boundary: `mem_innerSeparatedArmEvent_iff`,
  `innerSeparatedArmEvent_subset_multiArmEvent`, `HasInnerFence.mono`, `ArmsInnerSeparated.mono`,
  `innerSeparatedArmEvent_mono`, `innerSeparatedArmEvent_fin_zero`,
  `measurableSet_setOf_hasInnerFence`, `measurableSet_innerSeparatedArmEvent`,
  `hasInnerFence_iff_of_inter_eq`, `mem_innerSeparatedArmEvent_iff_of_inter_eq`,
  `HasInnerFence.map_add`, `image_add_mem_innerSeparatedArmEvent_iff`.

## Implementation notes

* The parameters are the separation `s : ℝ` of landing positions, on the doubled lattice, and the
  sizes `M` and `K` of the fences, rather than Nolin's `η` and `N`: the definition contains no
  square root or integer part, and the same notion serves every scale.
* The event is not monotone in `K`: a fence must run exactly from `b₀ - K` to `b₀ + K` (on the
  top side), and the first end of a fence of a wider box need not be joined to the arm inside the
  box of radius `M` about `b`.
* A fence is a connection inside its box between its two ends; it may meet the two ends' sides
  of the box elsewhere too.
* For `r ≥ R` the arms may be walks of length zero anywhere in `B_r(z)`; the determination lemma
  assumes `r < R`.
* The inner fence box of a dual arm contains the row (column) of its first face, which lies just
  outside `B_r(z)`, and the `M` rows (columns) inside it; a fence one row (column) further in is
  also a fence in this sense, so both forms an inner separation step may produce are covered.
* Arms separated at both boundaries of one annulus are written out where needed:
  `ArmsOuterSeparated ω σ z R s M K γ ∧ ArmsInnerSeparated ω σ z r s' M' K' γ`.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

namespace PercLib.Models.Planar

/-! ### Duals inside a box of faces -/

/-- **Duals inside a box of faces.** Whether the dual edges between faces of the box
`Icc lo hi` are open in `dualConfig ω` depends only on the edges of `ℤ²` with both ends in
`Icc lo (hi + 1)`: such a dual edge crosses an edge whose ends are corners of its two faces. -/
theorem dualConfig_inter_eq_of_inter_eq {lo hi : LatticeSite 2} {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} = ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)}) :
    dualConfig ω ∩ {f | ∀ g ∈ f, g ∈ Icc lo hi} = dualConfig ω' ∩ {f | ∀ g ∈ f, g ∈ Icc lo hi} := by
  have key : ∀ f : Sym2 (LatticeSite 2), f ∈ (zdGraph 2).edgeSet → (∀ g ∈ f, g ∈ Icc lo hi) →
      (Sym2.map (· + 1) (dualEdge f) ∈ ω ↔ Sym2.map (· + 1) (dualEdge f) ∈ ω') := by
    intro f hf hfg
    set e := Sym2.map (· + 1) (dualEdge f) with he
    have heE : e ∈ (zdGraph 2).edgeSet := map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hf)
    have hde : dualEdge e = f := congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨f, hf⟩)
    have heP : ∀ v ∈ e, v ∈ Icc lo (hi + 1) := by
      intro v hv
      obtain ⟨g, hg⟩ : ∃ g, g ∈ f := ⟨(Quot.out f).1, Sym2.out_fst_mem f⟩
      have hvg := mem_Icc_of_mem_dualEdge heE hv (hde ▸ hg)
      have hgB := hfg g hg
      refine ⟨hgB.1.trans hvg.1, fun i => ?_⟩
      have h₁ : v i ≤ (g + 1) i := hvg.2 i
      have h₂ : g i ≤ hi i := hgB.2 i
      simp only [Pi.add_apply, Pi.one_apply] at h₁ ⊢
      omega
    constructor
    · intro hω
      have : e ∈ ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} := ⟨hω, heP⟩
      rw [h] at this
      exact this.1
    · intro hω
      have : e ∈ ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} := ⟨hω, heP⟩
      rw [← h] at this
      exact this.1
  ext f
  simp only [mem_inter_iff, mem_ofPred_eq, mem_dualConfig_iff]
  constructor
  · rintro ⟨⟨hf, hω⟩, hfg⟩
    exact ⟨⟨hf, fun h' => hω ((key f hf hfg).2 h')⟩, hfg⟩
  · rintro ⟨⟨hf, hω⟩, hfg⟩
    exact ⟨⟨hf, fun h' => hω ((key f hf hfg).1 h')⟩, hfg⟩

/-- **Connections of either colour inside a box** are determined by the pairs inside any set
containing the box enlarged by one at its upper corner: for `c = true` the open edges with both
ends in the box, for `c = false` the dual edges between its faces, which cross edges with both
ends in the enlarged box (`dualConfig_inter_eq_of_inter_eq`). -/
theorem cond_inter_edgeSet_mem_localConn_iff_of_inter_eq (c : Bool) {lo hi : LatticeSite 2}
    {T : Set (LatticeSite 2)} (hT : Icc lo (hi + 1) ⊆ T) {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) (x y : LatticeSite 2) :
    cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x y ↔
      cond c ω' (dualConfig ω') ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x y := by
  have h' : ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} = ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} := by
    ext e
    have he := Set.ext_iff.1 h e
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨(he.1 ⟨h₁, fun v hv => hT (h₂ v hv)⟩).1, h₂⟩,
      fun ⟨h₁, h₂⟩ => ⟨(he.2 ⟨h₁, fun v hv => hT (h₂ v hv)⟩).1, h₂⟩⟩
  have hS : Icc lo hi ⊆ Icc lo (hi + 1) := Icc_subset_Icc le_rfl fun i => by
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  cases c
  · exact inter_mem_localConn_iff_of_inter_eq subset_rfl _ (dualConfig_inter_eq_of_inter_eq h') x y
  · exact inter_mem_localConn_iff_of_inter_eq hS _ h' x y

/-! ### Where an arm ends -/

/-- **Where an arm ends.** An arm from a box inside the interior of the outer box `Icc lo hi` ends
in `Icc (lo - 1) hi`: an open arm on the boundary of the outer box, a dual arm at a face just
outside it. -/
theorem IsArm.end_mem_Icc {ω : Config (LatticeSite 2)} {c : Bool} {z : LatticeSite 2} {r : ℕ}
    {lo hi a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) : b ∈ Icc (lo - 1) hi := by
  cases c
  · exact boxBoundary_subset_Icc _ _ (IsDualArm.end_mem_boxBoundary h (IsDualArm.not_nil h hB))
  · refine Icc_subset_Icc_left (fun i => ?_)
      (boxBoundary_subset_Icc _ _ (IsOpenArm.end_mem_boxBoundary h (IsOpenArm.not_nil h hB)))
    simp only [Pi.sub_apply, Pi.one_apply]
    omega

/-! ### Fences at the outer boundary -/

/-- An arm `γ` of colour `c` to the boundary of `B_R(z)` **has an outer fence** of length `2K` and
depth `M`: writing `b` for its end (its last vertex, or its last face if `c = false`) and reading
paths in the colour of the arm (open edges of `ω` for `c = true`, dual edges between faces open in
`dualConfig ω` for `c = false`), there are a vertex (face) `x` of the arm and points `u`, `v` such
that `x` is joined to `u` inside the box `Icc (b - M) (b + M)`, and `u` is joined to `v` across
the box of length `2K` and depth `M` standing at `b` outside `B_R(z)` on the side where `b` lies,
from its end at distance `K` before `b` along the side to its end at distance `K` after `b`. The
four cases are the top side (`b₁ = z₁ + R`, box `[b₀ - K, b₀ + K] × [b₁, b₁ + M]`), the right side
(`b₀ = z₀ + R`, box `[b₀, b₀ + M] × [b₁ - K, b₁ + K]`), the bottom side
(`b₁ = z₁ - R - [c = false]`, box `[b₀ - K, b₀ + K] × [b₁ - M, b₁]`) and the left side
(`b₀ = z₀ - R - [c = false]`, box `[b₀ - M, b₀] × [b₁ - K, b₁ + K]`); the last face of a dual arm
lies outside the faces `Icc (z - R) (z + R - 1)` of `B_R(z)`. -/
def HasOuterFence (ω : Config (LatticeSite 2)) (c : Bool) (z : LatticeSite 2) (R M K : ℕ)
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) : Prop :=
  ∃ x ∈ γ.support, ∃ u v : LatticeSite 2,
    cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (b - (M : LatticeSite 2)) (b + (M : LatticeSite 2))) x u ∧
    ((b 1 = z 1 + R ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b 0 - K, b 1] ![b 0 + K, b 1 + M]) u v) ∨
      (b 0 = z 0 + R ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b 0, b 1 - K] ![b 0 + M, b 1 + K]) u v) ∨
      (b 1 = z 1 - R - cond c 0 1 ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b 0 - K, b 1 - M] ![b 0 + K, b 1]) u v) ∨
      (b 0 = z 0 - R - cond c 0 1 ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b 0 - M, b 1 - K] ![b 0, b 1 + K]) u v))

/-- A family of arms with colours `σ` to the boundary of `B_R(z)` is **separated at the outer
boundary** with separation `s` and fences of length `2K` and depth `M`: the landing positions of
any two arms (`landingPos (z - R) (z + R)`, on the doubled lattice, where the boundary of
`B_R(z)` has perimeter `16 R` and corners at the multiples of `4 R`) are at least `s` apart, every
landing position is at least `s` from every doubled corner `4 m R`, and every arm has an outer
fence (`HasOuterFence`). -/
def ArmsOuterSeparated (ω : Config (LatticeSite 2)) {j : ℕ} (σ : Fin j → Bool)
    (z : LatticeSite 2) (R : ℕ) (s : ℝ) (M K : ℕ) {a b : Fin j → LatticeSite 2}
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)) : Prop :=
  (∀ i k, i ≠ k → s ≤ |((landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k) : ℤ) : ℝ)|) ∧
    (∀ i (m : ℕ), s ≤ |((landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R : ℤ) : ℝ)|) ∧
    ∀ i, HasOuterFence ω (σ i) z R M K (γ i)

/-- The **`j`-arm event with arms separated at the outer boundary**, from `B_r(z)` to the boundary
of `B_R(z)`: there is a disjoint family of `j` arms (`ArmsDisjoint`) of colours `σ`, landing in
counterclockwise order as in `multiArmEvent`, whose landing positions are at least `s` apart and
at least `s` from the doubled corners, each arm carrying an outer fence of length `2K` and depth
`M` (`ArmsOuterSeparated`). -/
def outerSeparatedArmEvent {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) (s : ℝ)
    (M K : ℕ) : Set (Config (LatticeSite 2)) :=
  {ω | ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
    (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
    ArmsOuterSeparated ω σ z R s M K γ}

section OuterSeparated

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}
  {ω ω' : Config (LatticeSite 2)}

/-- **Membership**, with the separation and the fences written out. -/
theorem mem_outerSeparatedArmEvent_iff : ω ∈ outerSeparatedArmEvent σ z r R s M K ↔
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      (∀ i k, i ≠ k → s ≤ |((landingPos (z - R) (z + R) (σ i) (γ i) -
        landingPos (z - R) (z + R) (σ k) (γ k) : ℤ) : ℝ)|) ∧
      (∀ i (m : ℕ), s ≤ |((landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R : ℤ) : ℝ)|) ∧
      ∀ i, ∃ x ∈ (γ i).support, ∃ u v : LatticeSite 2,
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc (b i - (M : LatticeSite 2)) (b i + (M : LatticeSite 2))) x u ∧
        ((b i 1 = z 1 + R ∧ u 0 = b i 0 - K ∧ v 0 = b i 0 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b i 0 - K, b i 1] ![b i 0 + K, b i 1 + M]) u v) ∨
          (b i 0 = z 0 + R ∧ u 1 = b i 1 - K ∧ v 1 = b i 1 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b i 0, b i 1 - K] ![b i 0 + M, b i 1 + K]) u v) ∨
          (b i 1 = z 1 - R - cond (σ i) 0 1 ∧ u 0 = b i 0 - K ∧ v 0 = b i 0 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b i 0 - K, b i 1 - M] ![b i 0 + K, b i 1]) u v) ∨
          (b i 0 = z 0 - R - cond (σ i) 0 1 ∧ u 1 = b i 1 - K ∧ v 1 = b i 1 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b i 0 - M, b i 1 - K] ![b i 0, b i 1 + K]) u v)) :=
  Iff.rfl

/-- **Separated arms are arms.** -/
theorem outerSeparatedArmEvent_subset_multiArmEvent :
    outerSeparatedArmEvent σ z r R s M K ⊆ multiArmEvent σ z r R :=
  fun _ ⟨a, b, γ, hγ, hd, ho, _⟩ => mem_multiArmEvent_iff.2 ⟨a, b, γ, hγ, hd, ho⟩

/-- **The trivial case.** With no arm the event is everything. -/
@[simp]
theorem outerSeparatedArmEvent_fin_zero (σ : Fin 0 → Bool) :
    outerSeparatedArmEvent σ z r R s M K = univ :=
  eq_univ_of_forall fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, fun i => i.elim0⟩

/-! #### Monotonicity -/

/-- **Monotonicity in the depth.** A fence of depth `M` is a fence of every depth `M' ≥ M`: its box
and the box about the end in which it is joined to the arm only grow. -/
theorem HasOuterFence.mono {c : Bool} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    {M' : ℕ} (hM : M ≤ M') (h : HasOuterFence ω c z R M K γ) : HasOuterFence ω c z R M' K γ := by
  have hbox : ∀ p p' q q' : LatticeSite 2, p' ≤ p → q ≤ q' → ∀ x y,
      cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y →
      cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p' q') x y :=
    fun p p' q q' hp hq x y hxy => localConn_mono_set (Icc_subset_Icc hp hq) x y hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := h
  refine ⟨x, hx, u, v, hbox _ _ _ _ (fun i => ?_) (fun i => ?_) _ _ hxu, ?_⟩
  · simp only [Pi.sub_apply, Pi.natCast_apply]
    omega
  · simp only [Pi.add_apply, Pi.natCast_apply]
    omega
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨h₁, h₂, h₃, hbox _ _ _ _ le_rfl (Fin.forall_fin_two.2 ⟨?_, ?_⟩) _ _ h₄⟩
    · exact le_rfl
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · refine Or.inr (Or.inl ⟨h₁, h₂, h₃, hbox _ _ _ _ le_rfl (Fin.forall_fin_two.2 ⟨?_, ?_⟩) _ _ h₄⟩)
    · simp only [Matrix.cons_val_zero]
      omega
    · exact le_rfl
  · refine Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃,
      hbox _ _ _ _ (Fin.forall_fin_two.2 ⟨?_, ?_⟩) le_rfl _ _ h₄⟩))
    · exact le_rfl
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · refine Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃,
      hbox _ _ _ _ (Fin.forall_fin_two.2 ⟨?_, ?_⟩) le_rfl _ _ h₄⟩))
    · simp only [Matrix.cons_val_zero]
      omega
    · exact le_rfl

/-- **Monotonicity.** A family separated by `s` with fences of depth `M` is separated by every
`s' ≤ s` with fences of every depth `M' ≥ M`. -/
theorem ArmsOuterSeparated.mono {s' : ℝ} {M' : ℕ} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hs : s' ≤ s) (hM : M ≤ M')
    (h : ArmsOuterSeparated ω σ z R s M K γ) : ArmsOuterSeparated ω σ z R s' M' K γ :=
  ⟨fun i k hik => hs.trans (h.1 i k hik), fun i m => hs.trans (h.2.1 i m),
    fun i => (h.2.2 i).mono hM⟩

/-- **Monotonicity.** The event shrinks when the separation grows and grows with the depth of the
fences. (It is not monotone in the length `2K` of the fences.) -/
theorem outerSeparatedArmEvent_mono {s' : ℝ} {M' : ℕ} (hs : s' ≤ s) (hM : M ≤ M') :
    outerSeparatedArmEvent σ z r R s M K ⊆ outerSeparatedArmEvent σ z r R s' M' K :=
  fun _ ⟨a, b, γ, hγ, hd, ho, hsep⟩ => ⟨a, b, γ, hγ, hd, ho, hsep.mono hs hM⟩

/-! #### Measurability -/

/-- **Measurability.** The configurations in which an arm has an outer fence form a measurable
set. -/
theorem measurableSet_setOf_hasOuterFence (c : Bool) (z : LatticeSite 2) (R M K : ℕ)
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) :
    MeasurableSet {ω | HasOuterFence ω c z R M K γ} := by
  have hconn : ∀ (S : Set (LatticeSite 2)) (x y : LatticeSite 2), Measurable fun
      ω : Config (LatticeSite 2) => cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈
        localConn S x y := by
    intro S x y
    refine measurableSet_setOfPred.1 ?_
    cases c
    · exact (measurableSet_localConn S x y).preimage ((by fun_prop :
        Measurable fun ω : Config (LatticeSite 2) => ω ∩ (zdGraph 2).edgeSet).comp
          measurable_dualConfig)
    · exact (measurableSet_localConn S x y).preimage (by fun_prop :
        Measurable fun ω : Config (LatticeSite 2) => ω ∩ (zdGraph 2).edgeSet)
  refine measurableSet_setOfPred.2 (Measurable.exists fun x => measurable_const.and
    (Measurable.exists fun u => Measurable.exists fun v => (hconn _ _ _).and ?_))
  exact ((measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))).or
    ((measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))).or
      ((measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))).or
        (measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))))))

/-- **Measurability.** The separated event is a countable union of measurable events. -/
theorem measurableSet_outerSeparatedArmEvent (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ)
    (s : ℝ) (M K : ℕ) : MeasurableSet (outerSeparatedArmEvent σ z r R s M K) := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  exact (Measurable.forall fun i => measurableSet_setOfPred.1
    (measurableSet_setOf_isArm _ z r _ _ (γ i))).and (measurable_const.and (measurable_const.and
      (measurable_const.and (measurable_const.and (Measurable.forall fun i =>
        measurableSet_setOfPred.1 (measurableSet_setOf_hasOuterFence _ z R M K (γ i)))))))

/-! #### Determination -/

/-- **Determination.** Whether an arm ending at `b` has an outer fence of length `2K` and depth `M`
depends only on the pairs with both ends in any set containing
`Icc (b - (M + K)) (b + (M + K + 1))`. -/
theorem hasOuterFence_iff_of_inter_eq {c : Bool} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} {T : Set (LatticeSite 2)}
    (hT : Icc (b - ((M + K : ℕ) : LatticeSite 2)) (b + ((M + K + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    HasOuterFence ω c z R M K γ ↔ HasOuterFence ω' c z R M K γ := by
  suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      ω₁ ∩ {e | ∀ v ∈ e, v ∈ T} = ω₂ ∩ {e | ∀ v ∈ e, v ∈ T} →
      HasOuterFence ω₁ c z R M K γ → HasOuterFence ω₂ c z R M K γ from
    ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω₁ ω₂ h₁₂ hf
  have hconn : ∀ p q : LatticeSite 2, (∀ w ∈ Icc p (q + 1), w ∈
      Icc (b - ((M + K : ℕ) : LatticeSite 2)) (b + ((M + K + 1 : ℕ) : LatticeSite 2))) →
      ∀ x y, cond c ω₁ (dualConfig ω₁) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y →
        cond c ω₂ (dualConfig ω₂) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y :=
    fun p q hpq x y hxy => (cond_inter_edgeSet_mem_localConn_iff_of_inter_eq c
      (fun w hw => hT (hpq w hw)) h₁₂ x y).1 hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  refine ⟨x, hx, u, v, hconn _ _ (fun w hw => ?_) _ _ hxu, ?_⟩
  · rw [mem_Icc_two_iff] at hw ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩)
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩))
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩))
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega

/-- **Determination by a box.** For `r < R`, the separated event is determined by the pairs with
both ends in any set containing the box `B_{R + M + K + 1}(z)`: the arms use edges of `B_R(z)`
and cross edges of `B_R(z)`, and the fences and their connections to the arms lie within
`M + K + 1` of the ends. -/
theorem mem_outerSeparatedArmEvent_iff_of_inter_eq (hrR : r < R) {T : Set (LatticeSite 2)}
    (hT : Icc (z - ((R + M + K + 1 : ℕ) : LatticeSite 2))
      (z + ((R + M + K + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ outerSeparatedArmEvent σ z r R s M K ↔ ω' ∈ outerSeparatedArmEvent σ z r R s M K := by
  suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      ω₁ ∩ {e | ∀ v ∈ e, v ∈ T} = ω₂ ∩ {e | ∀ v ∈ e, v ∈ T} →
      ω₁ ∈ outerSeparatedArmEvent σ z r R s M K → ω₂ ∈ outerSeparatedArmEvent σ z r R s M K from
    ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω₁ ω₂ h₁₂ ⟨a, b, γ, hγ, hd, ho, hsep, hcor, hfen⟩
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) := by
    refine Icc_subset_Icc ?_ ?_ <;> intro i <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] <;> omega
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc (z - R) (z + R)) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω₁ ↔ e ∈ ω₂) := by
    intro e _ he _
    have heT : e ∈ {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ T} := fun v hv => hT (by
      have hv' := he v hv
      rw [mem_Icc_two_iff] at hv' ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv' ⊢
      push_cast
      omega)
    have hmem := Set.ext_iff.1 h₁₂ e
    exact ⟨fun h' => (hmem.1 ⟨h', heT⟩).1, fun h' => (hmem.2 ⟨h', heT⟩).1⟩
  refine ⟨a, b, γ, fun i => (hγ i).of_agree hagree, hd, ho, hsep, hcor, fun i =>
    (hasOuterFence_iff_of_inter_eq (fun w hw => hT ?_) h₁₂).1 (hfen i)⟩
  have hb := (hγ i).end_mem_Icc hB
  rw [mem_Icc_two_iff] at hb hw ⊢
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hb hw ⊢
  push_cast at hw ⊢
  omega

/-! #### Translation -/

/-- **Translation.** Translating the configuration, the centre and the arm by `c` carries outer
fences to outer fences. Here `f` is the translation by `c`, as a homomorphism of `ℤ²`. -/
theorem HasOuterFence.map_add {col : Bool} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    {f : zdGraph 2 →g zdGraph 2} {c : LatticeSite 2} (hf : ∀ x, f x = x + c)
    (h : HasOuterFence ω col z R M K γ) :
    HasOuterFence (Sym2.map (· + c) '' ω) col (z + c) R M K (γ.map f) := by
  have hconn : ∀ (S S' : Set (LatticeSite 2)), (∀ w, w ∈ S' ↔ w - c ∈ S) → ∀ x y,
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn S x y →
      cond col (Sym2.map (· + c) '' ω) (dualConfig (Sym2.map (· + c) '' ω)) ∩
        (zdGraph 2).edgeSet ∈ localConn S' (x + c) (y + c) := by
    intro S S' hS x y hxy
    have hS' : S' = (· + c) '' S := by
      ext w
      rw [hS, image_add_right, mem_preimage, sub_eq_add_neg]
    subst hS'
    cases col
    · rw [dualConfig_image_add]
      exact (image_add_inter_edgeSet_mem_localConn_iff c _ S x y).2 hxy
    · exact (image_add_inter_edgeSet_mem_localConn_iff c ω S x y).2 hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := h
  refine ⟨f x, ?_, u + c, v + c, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map]
    exact List.mem_map_of_mem hx
  · rw [hf x, hf b]
    refine hconn _ _ (fun w => ?_) _ _ hxu
    rw [mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    constructor <;> intro hw <;> omega
  rw [hf b]
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega
  · refine Or.inr (Or.inl ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩)
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩))
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega
  · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩))
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega

/-- **Translation**, one direction. -/
theorem image_add_mem_outerSeparatedArmEvent (c : LatticeSite 2)
    (h : ω ∈ outerSeparatedArmEvent σ z r R s M K) :
    Sym2.map (· + c) '' ω ∈ outerSeparatedArmEvent σ (z + c) r R s M K := by
  obtain ⟨a, b, γ, hγ, hd, ho, hsep, hcor, hfen⟩ := h
  let f : zdGraph 2 →g zdGraph 2 := ⟨(· + c), fun {x y} hxy =>
    (zdGraph_adj_iff_of_sub fun i => by simp only [Pi.add_apply, add_sub_add_right_eq_sub]).2 hxy⟩
  have hf : ∀ x, f x = x + c := fun _ => rfl
  have hlo : z + c - (R : LatticeSite 2) = z - R + c := by abel
  have hhi : z + c + (R : LatticeSite 2) = z + R + c := by abel
  have hL : ∀ i, landingPos (z + c - R) (z + c + R) (σ i) ((γ i).map f) =
      landingPos (z - R) (z + R) (σ i) (γ i) := fun i => by
    rw [hlo, hhi]
    exact landingPos_map_add (γ i) hf _ _ _
  refine ⟨fun i => f (a i), fun i => f (b i), fun i => (γ i).map f, fun i => ?_,
    hd.map (add_left_injective c), fun i k l hik hkl => ?_, fun i k hik => ?_, fun i m => ?_,
    fun i => (hfen i).map_add hf⟩
  · rw [hlo, hhi]
    exact (hγ i).map_add hf
  · simp only [hL]
    exact ho i k l hik hkl
  · simp only [hL]
    exact hsep i k hik
  · simp only [hL]
    exact hcor i m

/-- **Translation.** Translating the configuration by `c` carries the separated event at `z` to the
separated event at `z + c`. -/
theorem image_add_mem_outerSeparatedArmEvent_iff (c : LatticeSite 2) :
    Sym2.map (· + c) '' ω ∈ outerSeparatedArmEvent σ (z + c) r R s M K ↔
      ω ∈ outerSeparatedArmEvent σ z r R s M K := by
  refine ⟨fun h => ?_, image_add_mem_outerSeparatedArmEvent c⟩
  have := image_add_mem_outerSeparatedArmEvent (-c) h
  rwa [image_add_neg_image_add, add_neg_cancel_right] at this

end OuterSeparated

/-! ### Separation at the inner boundary -/

/-- **Where an arm starts.** An arm from `B_r(z)` starts in `Icc (z - r - 1) (z + r)`: an open arm
at a vertex of `B_r(z)`, a dual arm at a face touching it. -/
theorem IsArm.start_mem_Icc {ω : Config (LatticeSite 2)} {c : Bool} {z : LatticeSite 2} {r : ℕ}
    {lo hi a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r lo hi γ) :
    a ∈ Icc (z - (r : LatticeSite 2) - 1) (z + r) := by
  cases c
  · exact h.isCrossing.start_mem
  · refine Icc_subset_Icc_left (fun i => ?_) h.isCrossing.start_mem
    simp only [Pi.sub_apply, Pi.one_apply]
    omega

/-- An arm `γ` of colour `c` from `B_r(z)` **has an inner fence** of length `2K` and depth `M`: the
mirror image of `HasOuterFence` at the start `a` of the arm (its first vertex, or its first face if
`c = false`). There are a vertex (face) `x` of the arm and points `u`, `v` such that `x` is joined
to `u` inside the box `Icc (a - M) (a + M)` and `u` is joined to `v` across the box of length `2K`
and depth `M` standing at `a` *inside* `B_r(z)` on the side where `a` lies, from its end at
distance `K` before `a` along the side to its end at distance `K` after `a`. The four cases are the
top side (`a₁ = z₁ + r`, box `[a₀ - K, a₀ + K] × [a₁ - M, a₁]`), the right side (`a₀ = z₀ + r`, box
`[a₀ - M, a₀] × [a₁ - K, a₁ + K]`), the bottom side (`a₁ = z₁ - r - [c = false]`, box
`[a₀ - K, a₀ + K] × [a₁, a₁ + M]`) and the left side (`a₀ = z₀ - r - [c = false]`, box
`[a₀, a₀ + M] × [a₁ - K, a₁ + K]`); the first face of a dual arm touches `B_r(z)` from outside, and
its box contains that face's row (column). -/
def HasInnerFence (ω : Config (LatticeSite 2)) (c : Bool) (z : LatticeSite 2) (r M K : ℕ)
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) : Prop :=
  ∃ x ∈ γ.support, ∃ u v : LatticeSite 2,
    cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (a - (M : LatticeSite 2)) (a + (M : LatticeSite 2))) x u ∧
    ((a 1 = z 1 + r ∧ u 0 = a 0 - K ∧ v 0 = a 0 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![a 0 - K, a 1 - M] ![a 0 + K, a 1]) u v) ∨
      (a 0 = z 0 + r ∧ u 1 = a 1 - K ∧ v 1 = a 1 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![a 0 - M, a 1 - K] ![a 0, a 1 + K]) u v) ∨
      (a 1 = z 1 - r - cond c 0 1 ∧ u 0 = a 0 - K ∧ v 0 = a 0 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![a 0 - K, a 1] ![a 0 + K, a 1 + M]) u v) ∨
      (a 0 = z 0 - r - cond c 0 1 ∧ u 1 = a 1 - K ∧ v 1 = a 1 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![a 0, a 1 - K] ![a 0 + M, a 1 + K]) u v))

/-- A family of arms with colours `σ` from `B_r(z)` is **separated at the inner boundary** with
separation `s` and fences of length `2K` and depth `M`: the inner positions of any two arms
(`innerPos z r`, on the doubled lattice, where the boundary of the doubled box
`2z + [-(2r + 1), 2r + 1]²` has perimeter `16 r + 8` and corners at the multiples of `4 r + 2`)
are at least `s` apart, every inner position is at least `s` from every doubled corner
`m (4 r + 2)`, and every arm has an inner fence (`HasInnerFence`). -/
def ArmsInnerSeparated (ω : Config (LatticeSite 2)) {j : ℕ} (σ : Fin j → Bool)
    (z : LatticeSite 2) (r : ℕ) (s : ℝ) (M K : ℕ) {a b : Fin j → LatticeSite 2}
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)) : Prop :=
  (∀ i k, i ≠ k → s ≤ |((innerPos z r (σ i) (γ i) - innerPos z r (σ k) (γ k) : ℤ) : ℝ)|) ∧
    (∀ i (m : ℕ), s ≤ |((innerPos z r (σ i) (γ i) - m * (4 * r + 2) : ℤ) : ℝ)|) ∧
    ∀ i, HasInnerFence ω (σ i) z r M K (γ i)

/-- The **`j`-arm event with arms separated at the inner boundary**, from `B_r(z)` to the
boundary of `B_R(z)`: there is a disjoint family of `j` arms (`ArmsDisjoint`) of colours `σ`,
landing in counterclockwise order as in `multiArmEvent`, whose inner positions are at least `s`
apart and at least `s` from the doubled corners of the inner box, each arm carrying an inner fence
of length `2K` and depth `M` (`ArmsInnerSeparated`). -/
def innerSeparatedArmEvent {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) (s : ℝ)
    (M K : ℕ) : Set (Config (LatticeSite 2)) :=
  {ω | ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
    (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
    ArmsInnerSeparated ω σ z r s M K γ}

section InnerSeparated

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}
  {ω ω' : Config (LatticeSite 2)}

/-- **Membership**, with the separation and the fences written out. -/
theorem mem_innerSeparatedArmEvent_iff : ω ∈ innerSeparatedArmEvent σ z r R s M K ↔
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      (∀ i k, i ≠ k → s ≤ |((innerPos z r (σ i) (γ i) - innerPos z r (σ k) (γ k) : ℤ) : ℝ)|) ∧
      (∀ i (m : ℕ), s ≤ |((innerPos z r (σ i) (γ i) - m * (4 * r + 2) : ℤ) : ℝ)|) ∧
      ∀ i, ∃ x ∈ (γ i).support, ∃ u v : LatticeSite 2,
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc (a i - (M : LatticeSite 2)) (a i + (M : LatticeSite 2))) x u ∧
        ((a i 1 = z 1 + r ∧ u 0 = a i 0 - K ∧ v 0 = a i 0 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![a i 0 - K, a i 1 - M] ![a i 0 + K, a i 1]) u v) ∨
          (a i 0 = z 0 + r ∧ u 1 = a i 1 - K ∧ v 1 = a i 1 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![a i 0 - M, a i 1 - K] ![a i 0, a i 1 + K]) u v) ∨
          (a i 1 = z 1 - r - cond (σ i) 0 1 ∧ u 0 = a i 0 - K ∧ v 0 = a i 0 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![a i 0 - K, a i 1] ![a i 0 + K, a i 1 + M]) u v) ∨
          (a i 0 = z 0 - r - cond (σ i) 0 1 ∧ u 1 = a i 1 - K ∧ v 1 = a i 1 + K ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![a i 0, a i 1 - K] ![a i 0 + M, a i 1 + K]) u v)) :=
  Iff.rfl

/-- **Separated arms are arms.** -/
theorem innerSeparatedArmEvent_subset_multiArmEvent :
    innerSeparatedArmEvent σ z r R s M K ⊆ multiArmEvent σ z r R :=
  fun _ ⟨a, b, γ, hγ, hd, ho, _⟩ => mem_multiArmEvent_iff.2 ⟨a, b, γ, hγ, hd, ho⟩

/-- **The trivial case.** With no arm the event is everything. -/
@[simp]
theorem innerSeparatedArmEvent_fin_zero (σ : Fin 0 → Bool) :
    innerSeparatedArmEvent σ z r R s M K = univ :=
  eq_univ_of_forall fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, fun i => i.elim0⟩

/-! #### Monotonicity -/

/-- **Monotonicity in the depth.** An inner fence of depth `M` is an inner fence of every depth
`M' ≥ M`. -/
theorem HasInnerFence.mono {c : Bool} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    {M' : ℕ} (hM : M ≤ M') (h : HasInnerFence ω c z r M K γ) : HasInnerFence ω c z r M' K γ := by
  have hbox : ∀ p p' q q' : LatticeSite 2, p' ≤ p → q ≤ q' → ∀ x y,
      cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y →
      cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p' q') x y :=
    fun p p' q q' hp hq x y hxy => localConn_mono_set (Icc_subset_Icc hp hq) x y hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := h
  refine ⟨x, hx, u, v, hbox _ _ _ _ (fun i => ?_) (fun i => ?_) _ _ hxu, ?_⟩
  · simp only [Pi.sub_apply, Pi.natCast_apply]
    omega
  · simp only [Pi.add_apply, Pi.natCast_apply]
    omega
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨h₁, h₂, h₃, hbox _ _ _ _ (Fin.forall_fin_two.2 ⟨?_, ?_⟩) le_rfl _ _ h₄⟩
    · exact le_rfl
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · refine Or.inr (Or.inl ⟨h₁, h₂, h₃, hbox _ _ _ _ (Fin.forall_fin_two.2 ⟨?_, ?_⟩) le_rfl _ _ h₄⟩)
    · simp only [Matrix.cons_val_zero]
      omega
    · exact le_rfl
  · refine Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃,
      hbox _ _ _ _ le_rfl (Fin.forall_fin_two.2 ⟨?_, ?_⟩) _ _ h₄⟩))
    · exact le_rfl
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · refine Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃,
      hbox _ _ _ _ le_rfl (Fin.forall_fin_two.2 ⟨?_, ?_⟩) _ _ h₄⟩))
    · simp only [Matrix.cons_val_zero]
      omega
    · exact le_rfl

/-- **Monotonicity.** A family separated at the inner boundary by `s` with fences of depth `M` is
separated by every `s' ≤ s` with fences of every depth `M' ≥ M`. -/
theorem ArmsInnerSeparated.mono {s' : ℝ} {M' : ℕ} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hs : s' ≤ s) (hM : M ≤ M')
    (h : ArmsInnerSeparated ω σ z r s M K γ) : ArmsInnerSeparated ω σ z r s' M' K γ :=
  ⟨fun i k hik => hs.trans (h.1 i k hik), fun i m => hs.trans (h.2.1 i m),
    fun i => (h.2.2 i).mono hM⟩

/-- **Monotonicity.** The event shrinks when the separation grows and grows with the depth of the
fences. (It is not monotone in the length `2K` of the fences.) -/
theorem innerSeparatedArmEvent_mono {s' : ℝ} {M' : ℕ} (hs : s' ≤ s) (hM : M ≤ M') :
    innerSeparatedArmEvent σ z r R s M K ⊆ innerSeparatedArmEvent σ z r R s' M' K :=
  fun _ ⟨a, b, γ, hγ, hd, ho, hsep⟩ => ⟨a, b, γ, hγ, hd, ho, hsep.mono hs hM⟩

/-! #### Measurability -/

/-- **Measurability.** The configurations in which an arm has an inner fence form a measurable
set. -/
theorem measurableSet_setOf_hasInnerFence (c : Bool) (z : LatticeSite 2) (r M K : ℕ)
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) :
    MeasurableSet {ω | HasInnerFence ω c z r M K γ} := by
  have hconn : ∀ (S : Set (LatticeSite 2)) (x y : LatticeSite 2), Measurable fun
      ω : Config (LatticeSite 2) => cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈
        localConn S x y := by
    intro S x y
    refine measurableSet_setOfPred.1 ?_
    cases c
    · exact (measurableSet_localConn S x y).preimage ((by fun_prop :
        Measurable fun ω : Config (LatticeSite 2) => ω ∩ (zdGraph 2).edgeSet).comp
          measurable_dualConfig)
    · exact (measurableSet_localConn S x y).preimage (by fun_prop :
        Measurable fun ω : Config (LatticeSite 2) => ω ∩ (zdGraph 2).edgeSet)
  refine measurableSet_setOfPred.2 (Measurable.exists fun x => measurable_const.and
    (Measurable.exists fun u => Measurable.exists fun v => (hconn _ _ _).and ?_))
  exact ((measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))).or
    ((measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))).or
      ((measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))).or
        (measurable_const.and (measurable_const.and (measurable_const.and (hconn _ _ _)))))))

/-- **Measurability.** The event of arms separated at the inner boundary is a countable union of
measurable events. -/
theorem measurableSet_innerSeparatedArmEvent (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ)
    (s : ℝ) (M K : ℕ) : MeasurableSet (innerSeparatedArmEvent σ z r R s M K) := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  exact (Measurable.forall fun i => measurableSet_setOfPred.1
    (measurableSet_setOf_isArm _ z r _ _ (γ i))).and (measurable_const.and (measurable_const.and
      (measurable_const.and (measurable_const.and (Measurable.forall fun i =>
        measurableSet_setOfPred.1 (measurableSet_setOf_hasInnerFence _ z r M K (γ i)))))))

/-! #### Determination -/

/-- **Determination.** Whether an arm starting at `a` has an inner fence of length `2K` and depth
`M` depends only on the pairs with both ends in any set containing
`Icc (a - (M + K)) (a + (M + K + 1))`. -/
theorem hasInnerFence_iff_of_inter_eq {c : Bool} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} {T : Set (LatticeSite 2)}
    (hT : Icc (a - ((M + K : ℕ) : LatticeSite 2)) (a + ((M + K + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    HasInnerFence ω c z r M K γ ↔ HasInnerFence ω' c z r M K γ := by
  suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      ω₁ ∩ {e | ∀ v ∈ e, v ∈ T} = ω₂ ∩ {e | ∀ v ∈ e, v ∈ T} →
      HasInnerFence ω₁ c z r M K γ → HasInnerFence ω₂ c z r M K γ from
    ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω₁ ω₂ h₁₂ hf
  have hconn : ∀ p q : LatticeSite 2, (∀ w ∈ Icc p (q + 1), w ∈
      Icc (a - ((M + K : ℕ) : LatticeSite 2)) (a + ((M + K + 1 : ℕ) : LatticeSite 2))) →
      ∀ x y, cond c ω₁ (dualConfig ω₁) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y →
        cond c ω₂ (dualConfig ω₂) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y :=
    fun p q hpq x y hxy => (cond_inter_edgeSet_mem_localConn_iff_of_inter_eq c
      (fun w hw => hT (hpq w hw)) h₁₂ x y).1 hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  refine ⟨x, hx, u, v, hconn _ _ (fun w hw => ?_) _ _ hxu, ?_⟩
  · rw [mem_Icc_two_iff] at hw ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩)
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩))
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩))
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega

/-- **Determination by a box.** For `r < R`, the event of arms separated at the inner boundary is
determined by the pairs with both ends in any set containing the box `B_{R + M + K + 1}(z)`: the
arms use edges of `B_R(z)` and cross edges of `B_R(z)`, and the inner fences and their connections
to the arms lie within `M + K + 1` of the starts, which lie in `B_{r + 1}(z)`. -/
theorem mem_innerSeparatedArmEvent_iff_of_inter_eq (hrR : r < R) {T : Set (LatticeSite 2)}
    (hT : Icc (z - ((R + M + K + 1 : ℕ) : LatticeSite 2))
      (z + ((R + M + K + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ innerSeparatedArmEvent σ z r R s M K ↔ ω' ∈ innerSeparatedArmEvent σ z r R s M K := by
  suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      ω₁ ∩ {e | ∀ v ∈ e, v ∈ T} = ω₂ ∩ {e | ∀ v ∈ e, v ∈ T} →
      ω₁ ∈ innerSeparatedArmEvent σ z r R s M K → ω₂ ∈ innerSeparatedArmEvent σ z r R s M K from
    ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω₁ ω₂ h₁₂ ⟨a, b, γ, hγ, hd, ho, hsep, hcor, hfen⟩
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc (z - R) (z + R)) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω₁ ↔ e ∈ ω₂) := by
    intro e _ he _
    have heT : e ∈ {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ T} := fun v hv => hT (by
      have hv' := he v hv
      rw [mem_Icc_two_iff] at hv' ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv' ⊢
      push_cast
      omega)
    have hmem := Set.ext_iff.1 h₁₂ e
    exact ⟨fun h' => (hmem.1 ⟨h', heT⟩).1, fun h' => (hmem.2 ⟨h', heT⟩).1⟩
  refine ⟨a, b, γ, fun i => (hγ i).of_agree hagree, hd, ho, hsep, hcor, fun i =>
    (hasInnerFence_iff_of_inter_eq (fun w hw => hT ?_) h₁₂).1 (hfen i)⟩
  have ha := (hγ i).start_mem_Icc
  rw [mem_Icc_two_iff] at ha hw ⊢
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at ha hw ⊢
  push_cast at hw ⊢
  omega

/-! #### Translation -/

/-- **Translation.** Translating the configuration, the centre and the arm by `c` carries inner
fences to inner fences. Here `f` is the translation by `c`, as a homomorphism of `ℤ²`. -/
theorem HasInnerFence.map_add {col : Bool} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    {f : zdGraph 2 →g zdGraph 2} {c : LatticeSite 2} (hf : ∀ x, f x = x + c)
    (h : HasInnerFence ω col z r M K γ) :
    HasInnerFence (Sym2.map (· + c) '' ω) col (z + c) r M K (γ.map f) := by
  have hconn : ∀ (S S' : Set (LatticeSite 2)), (∀ w, w ∈ S' ↔ w - c ∈ S) → ∀ x y,
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn S x y →
      cond col (Sym2.map (· + c) '' ω) (dualConfig (Sym2.map (· + c) '' ω)) ∩
        (zdGraph 2).edgeSet ∈ localConn S' (x + c) (y + c) := by
    intro S S' hS x y hxy
    have hS' : S' = (· + c) '' S := by
      ext w
      rw [hS, image_add_right, mem_preimage, sub_eq_add_neg]
    subst hS'
    cases col
    · rw [dualConfig_image_add]
      exact (image_add_inter_edgeSet_mem_localConn_iff c _ S x y).2 hxy
    · exact (image_add_inter_edgeSet_mem_localConn_iff c ω S x y).2 hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := h
  refine ⟨f x, ?_, u + c, v + c, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map]
    exact List.mem_map_of_mem hx
  · rw [hf x, hf a]
    refine hconn _ _ (fun w => ?_) _ _ hxu
    rw [mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    constructor <;> intro hw <;> omega
  rw [hf a]
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega
  · refine Or.inr (Or.inl ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩)
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩))
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega
  · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, hconn _ _ (fun w => ?_) _ _ h₄⟩))
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
    · rw [mem_Icc_two_iff, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro hw <;> omega

/-- **Translation**, one direction. -/
theorem image_add_mem_innerSeparatedArmEvent (c : LatticeSite 2)
    (h : ω ∈ innerSeparatedArmEvent σ z r R s M K) :
    Sym2.map (· + c) '' ω ∈ innerSeparatedArmEvent σ (z + c) r R s M K := by
  obtain ⟨a, b, γ, hγ, hd, ho, hsep, hcor, hfen⟩ := h
  let f : zdGraph 2 →g zdGraph 2 := ⟨(· + c), fun {x y} hxy =>
    (zdGraph_adj_iff_of_sub fun i => by simp only [Pi.add_apply, add_sub_add_right_eq_sub]).2 hxy⟩
  have hf : ∀ x, f x = x + c := fun _ => rfl
  have hlo : z + c - (R : LatticeSite 2) = z - R + c := by abel
  have hhi : z + c + (R : LatticeSite 2) = z + R + c := by abel
  have hL : ∀ i, landingPos (z + c - R) (z + c + R) (σ i) ((γ i).map f) =
      landingPos (z - R) (z + R) (σ i) (γ i) := fun i => by
    rw [hlo, hhi]
    exact landingPos_map_add (γ i) hf _ _ _
  have hI : ∀ i, innerPos (z + c) r (σ i) ((γ i).map f) = innerPos z r (σ i) (γ i) := fun i =>
    innerPos_map_add (γ i) hf _ _ _
  refine ⟨fun i => f (a i), fun i => f (b i), fun i => (γ i).map f, fun i => ?_,
    hd.map (add_left_injective c), fun i k l hik hkl => ?_, fun i k hik => ?_, fun i m => ?_,
    fun i => (hfen i).map_add hf⟩
  · rw [hlo, hhi]
    exact (hγ i).map_add hf
  · simp only [hL]
    exact ho i k l hik hkl
  · simp only [hI]
    exact hsep i k hik
  · simp only [hI]
    exact hcor i m

/-- **Translation.** Translating the configuration by `c` carries the event of arms separated at
the inner boundary at `z` to the same event at `z + c`. -/
theorem image_add_mem_innerSeparatedArmEvent_iff (c : LatticeSite 2) :
    Sym2.map (· + c) '' ω ∈ innerSeparatedArmEvent σ (z + c) r R s M K ↔
      ω ∈ innerSeparatedArmEvent σ z r R s M K := by
  refine ⟨fun h => ?_, image_add_mem_innerSeparatedArmEvent c⟩
  have := image_add_mem_innerSeparatedArmEvent (-c) h
  rwa [image_add_neg_image_add, add_neg_cancel_right] at this

end InnerSeparated

/-- **One arm separated at the inner boundary.** With every edge open, the open arm from `(1, 0)`
on the right side of `B_1(0)` to `(2, 0)` on the boundary of `B_2(0)` is separated at the inner
boundary with `s = 2` and fences of length `2` and depth `1`: its inner position `9` is at
distance `3` from the doubled corners `6` and `12` of the inner box, and its inner fence runs from
`(1, -1)` to `(1, 1)` inside `[0, 1] × [-1, 1]`. -/
example : (univ : Config (LatticeSite 2)) ∈ innerSeparatedArmEvent ![true] 0 1 2 2 1 1 := by
  have hadj : (zdGraph 2).Adj ![1, 0] ![2, 0] := by
    rw [zdGraph_two_adj_iff]
    simp
  have hsnd : hadj.toWalk.snd = ![2, 0] := rfl
  have hpos : innerPos (0 : LatticeSite 2) 1 true hadj.toWalk = 9 := by
    rw [innerPos_true, hsnd, perimeterPos_of_right (by simp) (by simp)]
    simp
  refine ⟨fun _ => ![1, 0], fun _ => ![2, 0], fun _ => hadj.toWalk, fun i => ?_,
    armsDisjoint_of_subsingleton le_rfl _ _, fun i k l hik => absurd hik (by omega),
    fun i k hik => absurd (Subsingleton.elim i k) hik, fun i m => ?_, fun i => ?_⟩
  · rw [Fin.fin_one_eq_zero i]
    refine (isOpenArm_toWalk_iff hadj).2 ⟨?_, ?_, ?_, ?_, mem_univ _⟩ <;>
      simp [mem_Icc_two_iff, -mem_Icc]
  · rw [Fin.fin_one_eq_zero i]
    change (2 : ℝ) ≤ |((innerPos (0 : LatticeSite 2) 1 true hadj.toWalk -
      m * (4 * ((1 : ℕ) : ℤ) + 2) : ℤ) : ℝ)|
    rw [hpos]
    have h : (2 : ℤ) ≤ |9 - (m : ℤ) * (4 * ((1 : ℕ) : ℤ) + 2)| := le_abs.2 (by omega)
    exact_mod_cast h
  · rw [Fin.fin_one_eq_zero i]
    refine ⟨![1, 0], SimpleGraph.Walk.start_mem_support _, ![1, -1], ![1, 1], ?_,
      Or.inr (Or.inl ⟨by simp, by simp, by simp, ?_⟩)⟩
    · simp only [Matrix.cons_val_zero, Bool.cond_true, univ_inter]
      exact edgeSet_mem_localConn_Icc
        (by simp [mem_Icc_two_iff, Matrix.vecHead, Matrix.vecTail, -mem_Icc])
        (by simp [mem_Icc_two_iff, Matrix.vecHead, Matrix.vecTail, -mem_Icc])
    · simp only [Matrix.cons_val_zero, Bool.cond_true, univ_inter]
      exact edgeSet_mem_localConn_Icc (by simp [mem_Icc_two_iff, -mem_Icc])
        (by simp [mem_Icc_two_iff, -mem_Icc])

/-! ### Non-vacuity -/

/-- **One separated open arm.** With every edge open, the open arm from the origin to `(1, 0)` on
the right side of `B_1(0)` is separated with `s = 2` and fences of length `2` and depth `1`: its
landing position `6` is at distance `2` from the doubled corners `4` and `8`, and its fence runs
from `(1, -1)` to `(1, 1)` inside `[1, 2] × [-1, 1]`. -/
example : (univ : Config (LatticeSite 2)) ∈ outerSeparatedArmEvent ![true] 0 0 1 2 1 1 := by
  have hadj : (zdGraph 2).Adj ![0, 0] ![1, 0] := by
    rw [zdGraph_two_adj_iff]
    simp
  have hpos : landingPos (0 - ((1 : ℕ) : LatticeSite 2)) (0 + ((1 : ℕ) : LatticeSite 2)) true
      hadj.toWalk = 6 := by
    rw [landingPos_true, perimeterPos_of_right (by simp) (by simp)]
    simp
  refine ⟨fun _ => ![0, 0], fun _ => ![1, 0], fun _ => hadj.toWalk, fun i => ?_,
    armsDisjoint_of_subsingleton le_rfl _ _, fun i k l hik => absurd hik (by omega),
    fun i k hik => absurd (Subsingleton.elim i k) hik, fun i m => ?_, fun i => ?_⟩
  · rw [Fin.fin_one_eq_zero i]
    refine (isOpenArm_toWalk_iff hadj).2 ⟨?_, ?_, ?_, ?_, mem_univ _⟩ <;>
      simp [-mem_Icc]
  · rw [Fin.fin_one_eq_zero i]
    change (2 : ℝ) ≤ |((landingPos (0 - ((1 : ℕ) : LatticeSite 2)) (0 + ((1 : ℕ) : LatticeSite 2))
      true hadj.toWalk - 4 * m * ((1 : ℕ) : ℤ) : ℤ) : ℝ)|
    rw [hpos]
    have h : (2 : ℤ) ≤ |6 - 4 * (m : ℤ) * ((1 : ℕ) : ℤ)| := le_abs.2 (by omega)
    exact_mod_cast h
  · rw [Fin.fin_one_eq_zero i]
    refine ⟨![1, 0], SimpleGraph.Walk.end_mem_support _, ![1, -1], ![1, 1], ?_,
      Or.inr (Or.inl ⟨by simp, by simp, by simp, ?_⟩)⟩
    · simp only [Matrix.cons_val_zero, Bool.cond_true, univ_inter]
      exact edgeSet_mem_localConn_Icc
        (by simp [mem_Icc_two_iff, Matrix.vecHead, Matrix.vecTail, -mem_Icc])
        (by simp [mem_Icc_two_iff, Matrix.vecHead, Matrix.vecTail, -mem_Icc])
    · simp only [Matrix.cons_val_zero, Bool.cond_true, univ_inter]
      exact edgeSet_mem_localConn_Icc (by simp [mem_Icc_two_iff, -mem_Icc])
        (by simp [mem_Icc_two_iff, -mem_Icc])

/-- With no open edge there is no separated open arm: the event is not everything. -/
example : (∅ : Config (LatticeSite 2)) ∉ outerSeparatedArmEvent ![true] 0 0 1 2 1 1 := fun h =>
  empty_notMem_multiArmEventTo (by simp) ⟨0, rfl⟩ (outerSeparatedArmEvent_subset_multiArmEvent h)

end PercLib.Models.Planar
