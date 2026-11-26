/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Percolation.Bond.Embedding
public import PercLib.Models.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Lower semicontinuity of the threshold under local convergence (468P)

For a finite `S ∋ o`, the boundary functional
`Φ_q(o,S) = ∑_{u ∈ S} ∑'_{v ∉ S} τ_S(o,u) q s(u,v)` only sees the pairs inside a set `A`
that contains `S` and every partner of `S` with `q ≠ 0`.

* `boundaryFlux_image_eq`: an injective map `f` on such an `A` that carries `q` on `A` to
  `q'`, and whose image contains every partner of `f '' S`, transports `Φ_q(o,S)` to
  `Φ_{q'}(f o, f '' S)` exactly.
* `boundaryFlux_eq_of_ballIso` (item 1): for host graphs, written as the intensity profiles
  of the edge indicators, a rooted isomorphism of the closed balls of radius `R + 1` carries
  every finite `S` in the closed ball of radius `R` to a set with the same `Φ`.
* `rootCriticalIntensity_le_liminf` (468P, item 2): if `(G_n, o_n)` converges locally to a
  connected locally finite `(G, o)` and every `G_n` is vertex-transitive and locally finite,
  then `β_c(G) ≤ liminf_n β_c(G_n)`.

The closed ball of radius `R` is mathlib's `G.ball o (R + 1)` (`edist < R + 1`).
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {U V W : Type*}

/-! ### Internal connections seen through an embedding -/

/-- The open graph of a pulled-back configuration is the induced open graph on the range. -/
theorem localConn_range_iff (g : U ↪ V) (ω : Config V) (a b : U) :
    (ω ∈ localConn (range g) (g a) (g b)) ↔
    (openGraph (Sym2.map g ⁻¹' ω : Config U)).Reachable a b := by
  let ψ : openGraph (Sym2.map g ⁻¹' ω : Config U) ≃g (openGraph ω).induce (range g) :=
    { toEquiv := Equiv.ofInjective g g.injective
      map_rel_iff' := fun {x y} => by
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
          Equiv.ofInjective_apply, openGraph_adj_iff, mem_preimage, Sym2.map_mk,
          ne_eq, g.injective.eq_iff] }
  have hψ : ∀ x, ψ x = ⟨g x, mem_range_self x⟩ := fun _ => rfl
  constructor
  · rintro ⟨ha, hb, h⟩
    rw [← SimpleGraph.Iso.reachable_iff (φ := ψ)]
    exact h
  · intro h
    exact ⟨mem_range_self a, mem_range_self b, (SimpleGraph.Iso.reachable_iff (φ := ψ)).2 h⟩

/-- The probability of an internal connection in the range of an embedding is that of a
connection under the pulled-back profile. -/
theorem law_localConn_range_eq (q : Sym2 V → unitInterval) [Countable U] (g : U ↪ V)
    {T : Set V} (hT : range g = T) (a b : U) :
    law q (localConn T (g a) (g b)) =
    law (fun e => q (Sym2.map g e)) (conn a b) := by
  subst hT
  rw [← law_map_preimage_sym2Map, Measure.map_apply (measurable_preimage_sym2Map _)
    (measurableSet_conn a b)]
  congr 1
  ext ω
  exact localConn_range_iff g ω a b

/-! ### Transport of the boundary functional -/

open Classical in
/-- **Transport of `Φ`.** Let `f` be injective on `A ⊇ S`, carry `q` on pairs of `A` to
`q'`, and suppose every partner of `S` under `q` lies in `A` and every partner of `f '' S`
under `q'` lies in `f '' A`. Then `Φ_{q'}(f o, f '' S) = Φ_q(o, S)`. -/
theorem boundaryFlux_image_eq (q : Sym2 V → unitInterval) (q' : Sym2 W → unitInterval)
    (f : V → W) (A : Set V) (hf : InjOn f A) (S : Finset V) (hSA : (S : Set V) ⊆ A)
    {o : V} (hoS : o ∈ S)
    (hq : ∀ a ∈ A, ∀ b ∈ A, q' s(f a, f b) = q s(a, b))
    (hsupp : ∀ u ∈ S, ∀ v, v ∉ A → q s(u, v) = 0)
    (hsupp' : ∀ u ∈ S, ∀ w, w ∉ f '' A → q' s(f u, w) = 0) :
    boundaryFlux q' (S.image f) (f o) = boundaryFlux q S o := by
  classical
  have hfS : InjOn f (S : Set V) := hf.mono hSA
  rw [boundaryFlux_def, boundaryFlux_def, Finset.sum_image fun x hx y hy h => hfS hx hy h]
  refine Finset.sum_congr rfl fun u hu => ?_
  -- The embeddings of `S` into `V` and into `W`.
  let g : (S : Set V) ↪ V := Function.Embedding.subtype _
  let g' : (S : Set V) ↪ W := ⟨fun x => f x, fun x y h => Subtype.ext (hfS x.2 y.2 h)⟩
  have hg : range g = (S : Set V) := Subtype.range_coe
  have hg' : range g' = ((S.image f : Finset W) : Set W) := by
    ext w
    simp only [mem_range, Finset.coe_image, mem_image, Finset.mem_coe, g']
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  -- The internal connection probabilities agree.
  have hP : law q' (localConn ((S.image f : Finset W) : Set W) (f o) (f u)) =
      law q (localConn (S : Set V) o u) := by
    have h1 := law_localConn_range_eq q' g' hg' ⟨o, hoS⟩ ⟨u, hu⟩
    have h2 := law_localConn_range_eq q g hg ⟨o, hoS⟩ ⟨u, hu⟩
    have hpro : (fun e => q' (Sym2.map g' e)) = fun e => q (Sym2.map g e) := by
      funext e
      induction e using Sym2.ind with
      | h x y => exact hq x (hSA x.2) y (hSA y.2)
    rw [hpro, ← h2] at h1
    exact h1
  -- The exterior rows agree, both being sums over `A`.
  have hiA : Function.Injective fun a : A => f a := fun x y h => Subtype.ext (hf x.2 y.2 h)
  have hsW : ∀ w, (if w ∈ S.image f then 0 else
      law q' (localConn ((S.image f : Finset W) : Set W) (f o) (f u)) *
      (unitInterval.toNNReal (q' s(f u, w)) : ℝ≥0∞)) ≠ 0 → w ∈ range fun a : A => f a := by
    intro w hw
    by_contra hwA
    refine hw ?_
    have : w ∉ f '' A := fun ⟨a, ha, haw⟩ => hwA ⟨⟨a, ha⟩, haw⟩
    rw [hsupp' u hu w this]
    simp
  have hsV : ∀ v, (if v ∈ S then 0 else
      law q (localConn (S : Set V) o u) *
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) ≠ 0 → v ∈ range fun a : A => (a : V) := by
    intro v hv
    by_contra hvA
    refine hv ?_
    have : v ∉ A := fun ha => hvA ⟨⟨v, ha⟩, rfl⟩
    rw [hsupp u hu v this]
    simp
  rw [← hiA.tsum_eq (fun w hw => hsW w hw), ← Subtype.val_injective.tsum_eq
    (fun v hv => hsV v hv)]
  refine tsum_congr fun a => ?_
  have hmem : f a ∈ S.image f ↔ (a : V) ∈ S := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxa⟩
      rwa [← hf (hSA hx) a.2 hxa]
    · intro h; exact ⟨a, h, rfl⟩
  by_cases ha : (a : V) ∈ S
  · simp [ha, hmem.2 ha]
  · rw [ite_eq_right_iff.2 fun h => absurd h (mt hmem.1 ha),
      ite_eq_right_iff.2 fun h => absurd h ha, hP, hq u (hSA hu) a a.2]

/-! ### Rooted isomorphisms of balls -/

section Balls

variable {G : SimpleGraph V} {G' : SimpleGraph W}

/-- Under a rooted isomorphism of the balls `edist < r`, a vertex within distance `k < r` of
the root is sent within distance `k` of the root. -/
theorem edist_ballIso_le {o : V} {o' : W} {r : ℕ∞}
    (φ : G.induce (G.ball o r) ≃g G'.induce (G'.ball o' r))
    (hφ : ∀ h, (φ ⟨o, h⟩ : W) = o') (k : ℕ) (hk : (k : ℕ∞) < r) (u : V)
    (hu : G.edist u o ≤ k) :
    G'.edist (φ ⟨u, lt_of_le_of_lt hu hk⟩ : W) o' ≤ k := by
  induction k generalizing u with
  | zero =>
    have hu0 : u = o := by simpa using hu
    subst hu0
    simp only [Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff]
    exact hφ _
  | succ k ih =>
    have hk' : (k : ℕ∞) < r := lt_of_le_of_lt (by exact_mod_cast Nat.le_succ k) hk
    by_cases h : G.edist u o ≤ k
    · exact (ih hk' u h).trans (by exact_mod_cast Nat.le_succ k)
    · have heq : G.edist u o = ((k + 1 : ℕ) : ℕ∞) := by
        refine le_antisymm hu ?_
        rw [not_le] at h
        push_cast
        exact Order.add_one_le_of_lt h
      obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe heq
      cases p with
      | nil => simp at hp
      | @cons _ v _ hadj q =>
        have hql : q.length = k := by simpa using hp
        have hv : G.edist v o ≤ k := hql ▸ SimpleGraph.Walk.edist_le q
        have hvk := ih hk' v hv
        have hadj' : G'.Adj (φ ⟨u, lt_of_le_of_lt hu hk⟩ : W)
            (φ ⟨v, lt_of_le_of_lt hv hk'⟩ : W) := by
          have := (φ.map_adj_iff (v := ⟨u, lt_of_le_of_lt hu hk⟩)
            (w := ⟨v, lt_of_le_of_lt hv hk'⟩)).2 (by simpa using hadj)
          simpa using this
        calc G'.edist (φ ⟨u, lt_of_le_of_lt hu hk⟩ : W) o'
            ≤ G'.edist (φ ⟨u, lt_of_le_of_lt hu hk⟩ : W) (φ ⟨v, lt_of_le_of_lt hv hk'⟩ : W) +
              G'.edist (φ ⟨v, lt_of_le_of_lt hv hk'⟩ : W) o' := SimpleGraph.edist_triangle
          _ ≤ 1 + k := add_le_add (SimpleGraph.edist_eq_one_iff_adj.2 hadj').le hvk
          _ = ((k + 1 : ℕ) : ℕ∞) := by push_cast; ring

open Classical in
/-- The edge indicator of a graph is invariant under its automorphisms. -/
theorem indicator_edgeSet_map_iso (σ : G ≃g G) (e : Sym2 V) :
    G.edgeSet.indicator (fun _ => (1 : ℝ≥0)) (Sym2.map σ e) =
      G.edgeSet.indicator (fun _ => (1 : ℝ≥0)) e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [Sym2.map_mk, Set.indicator, SimpleGraph.mem_edgeSet, σ.map_adj_iff]

/-- A vertex-transitive graph gives a transitive edge indicator. -/
theorem transitive_indicator_edgeSet (hT : ∀ x y : V, ∃ σ : G ≃g G, σ x = y) (x y : V) :
    ∃ σ : V ≃ V, σ x = y ∧ ∀ e, G.edgeSet.indicator (fun _ => (1 : ℝ≥0)) (Sym2.map σ e) =
      G.edgeSet.indicator (fun _ => (1 : ℝ≥0)) e := by
  obtain ⟨σ, hσ⟩ := hT x y
  exact ⟨σ.toEquiv, hσ, indicator_edgeSet_map_iso σ⟩

/-- A locally finite graph has summable edge-indicator rows. -/
theorem summable_indicator_edgeSet (hG : ∀ v, (G.neighborSet v).Finite) (u : V) :
    Summable fun v => ((G.edgeSet.indicator (fun _ => (1 : ℝ≥0)) s(u, v) : ℝ≥0) : ℝ) := by
  refine summable_of_ne_finset_zero (s := (hG u).toFinset) fun v hv => ?_
  have hadj : ¬ G.Adj u v := by simpa using hv
  simp [Set.indicator, SimpleGraph.mem_edgeSet, hadj]

open Classical in
/-- **Item 1, transport of certificates.** A rooted isomorphism of the balls `edist < r + 1`
carries every finite `S ∋ o` in the ball `edist < r` to a finite `S' ∋ o'` with the same
boundary functional for the edge-indicator intensities at every `β`. -/
theorem boundaryFlux_eq_of_ballIso {o : V} {o' : W} {r : ℕ∞}
    (φ : G.induce (G.ball o (r + 1)) ≃g G'.induce (G'.ball o' (r + 1)))
    (hφ : ∀ h, (φ ⟨o, h⟩ : W) = o') (S : Finset V) (hoS : o ∈ S)
    (hS : (S : Set V) ⊆ G.ball o r) (β : ℝ≥0) :
    ∃ S' : Finset W, o' ∈ S' ∧ S'.card = S.card ∧
    boundaryFlux (intensityProfile (G'.edgeSet.indicator fun _ => (1 : ℝ≥0)) β) S' o' =
    boundaryFlux (intensityProfile (G.edgeSet.indicator fun _ => (1 : ℝ≥0)) β) S o := by
  have hrA : G.ball o r ⊆ G.ball o (r + 1) := SimpleGraph.ball_mono le_self_add
  let f : V → W := fun x => if hx : x ∈ G.ball o (r + 1) then (φ ⟨x, hx⟩ : W) else o'
  have hfA : ∀ x (hx : x ∈ G.ball o (r + 1)), f x = φ ⟨x, hx⟩ := fun x hx =>
    dite_eq_left_of_eq_true (eq_true hx)
  have hf : InjOn f (G.ball o (r + 1)) := fun x hx y hy h => by
    rw [hfA x hx, hfA y hy] at h
    simpa using φ.injective (Subtype.ext h)
  have hadj : ∀ a (ha : a ∈ G.ball o (r + 1)) b (hb : b ∈ G.ball o (r + 1)),
      G'.Adj (f a) (f b) ↔ G.Adj a b := by
    intro a ha b hb
    rw [hfA a ha, hfA b hb]
    have := φ.map_adj_iff (v := ⟨a, ha⟩) (w := ⟨b, hb⟩)
    simpa using this
  have hfo : f o = o' := by
    rw [hfA o (hrA (hS hoS))]
    exact hφ _
  refine ⟨S.image f, ?_, ?_, ?_⟩
  · rw [Finset.mem_image]; exact ⟨o, hoS, hfo⟩
  · exact Finset.card_image_of_injOn (hf.mono fun x hx => hrA (hS hx))
  · rw [← hfo]
    refine boundaryFlux_image_eq _ _ f _ hf S (fun x hx => hrA (hS hx)) hoS ?_ ?_ ?_
    · intro a ha b hb
      refine Subtype.ext ?_
      simp only [intensityProfile, Set.indicator, SimpleGraph.mem_edgeSet, hadj a ha b hb]
    · intro u hu v hv
      refine intensityProfile_eq_zero_of_eq_zero _ ?_ β
      simp only [Set.indicator, SimpleGraph.mem_edgeSet, ite_eq_right_iff, one_ne_zero,
        imp_false]
      intro h
      refine hv ?_
      have hu' : G.edist u o < r := hS hu
      change G.edist v o < r + 1
      calc G.edist v o ≤ G.edist v u + G.edist u o := SimpleGraph.edist_triangle
        _ = G.edist u o + 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.2 h.symm, add_comm]
        _ < r + 1 := (ENat.add_lt_add_iff_right ENat.one_ne_top).2 hu'
    · intro u hu w hw
      refine intensityProfile_eq_zero_of_eq_zero _ ?_ β
      simp only [Set.indicator, SimpleGraph.mem_edgeSet, ite_eq_right_iff, one_ne_zero,
        imp_false]
      intro h
      refine hw ?_
      have hu' : G.edist u o < r := hS hu
      have hne : G.edist u o ≠ ⊤ := ne_top_of_lt hu'
      set k := (G.edist u o).toNat
      have hku : G.edist u o = k := (ENat.natCast_toNat hne).symm
      have hk : (k : ℕ∞) < r := hku ▸ hu'
      have hk1 : (k : ℕ∞) < r + 1 := lt_of_lt_of_le hk le_self_add
      have hfu := edist_ballIso_le φ hφ k hk1 u hku.le
      rw [← hfA u (hrA hu')] at hfu
      have hw' : G'.edist w o' < r + 1 :=
        calc G'.edist w o' ≤ G'.edist w (f u) + G'.edist (f u) o' :=
              SimpleGraph.edist_triangle
          _ ≤ 1 + k := add_le_add (SimpleGraph.edist_eq_one_iff_adj.2 h.symm).le hfu
          _ = k + 1 := add_comm _ _
          _ < r + 1 := (ENat.add_lt_add_iff_right ENat.one_ne_top).2 hk
      refine ⟨(φ.symm ⟨w, hw'⟩ : V), (φ.symm ⟨w, hw'⟩).2, ?_⟩
      rw [hfA _ (φ.symm ⟨w, hw'⟩).2]
      simp

end Balls

/-! ### Lower semicontinuity of the threshold (468P) -/

/-- **Lower semicontinuity of the threshold under local convergence.** Let `G` be connected and
locally finite on a countable type, and let every `G_n` be vertex-transitive and locally finite on a
countable type. If for every `R` the closed balls of radius `R` about `o_n` in `G_n` are eventually
isomorphic, as rooted graphs, to the closed ball of radius `R` about `o` in `G`, then for
homogeneous nearest-neighbour percolation (the intensity profiles of the edge indicators),
`β_c(G) ≤ liminf_n β_c(G_n)`. -/
theorem rootCriticalIntensity_le_liminf [Countable V] {W : ℕ → Type*} [∀ n, Countable (W n)]
    (G : SimpleGraph V) (Gs : ∀ n, SimpleGraph (W n)) (o : V) (os : ∀ n, W n)
    (hG : G.Connected) (hGf : ∀ v, (G.neighborSet v).Finite)
    (hGsf : ∀ n v, ((Gs n).neighborSet v).Finite)
    (hGsT : ∀ n (x y : W n), ∃ σ : Gs n ≃g Gs n, σ x = y)
    (hloc : ∀ R : ℕ, ∀ᶠ n in atTop, ∃ φ : G.induce (G.ball o (R + 1)) ≃g
      (Gs n).induce ((Gs n).ball (os n) (R + 1)), ∀ h, (φ ⟨o, h⟩ : W n) = os n) :
    rootCriticalIntensity (G.edgeSet.indicator fun _ => (1 : ℝ≥0)) o ≤
      liminf (fun n => rootCriticalIntensity ((Gs n).edgeSet.indicator fun _ => (1 : ℝ≥0))
        (os n)) atTop := by
  refine le_of_forall_lt fun c hc => ?_
  have h := hc.trans_le (rootCriticalIntensity_le_sSup_boundaryFlux_lt_one _
    (summable_indicator_edgeSet hGf) o)
  rw [lt_sSup_iff] at h
  obtain ⟨_, ⟨β, ⟨S, hoS, hΦ⟩, rfl⟩, hcβ⟩ := h
  refine hcβ.trans_le (le_liminf_of_le (by isBoundedDefault) ?_)
  -- A radius containing `S`.
  set R : ℕ := S.sup fun u => (G.edist u o).toNat
  have hS : (S : Set V) ⊆ G.ball o ((R + 1 : ℕ) : ℕ∞) := fun u hu => by
    have hne : G.edist u o ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.2 (hG.preconnected u o)
    change G.edist u o < ((R + 1 : ℕ) : ℕ∞)
    rw [← ENat.natCast_toNat hne, Nat.cast_lt]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun u => (G.edist u o).toNat) hu)
  filter_upwards [hloc (R + 1)] with n ⟨φ, hφ⟩
  obtain ⟨S', hoS', -, hΦ'⟩ := boundaryFlux_eq_of_ballIso φ hφ S hoS hS β
  rw [← hΦ'] at hΦ
  exact (lt_rootCriticalIntensity_of_boundaryFlux_lt_one _
    (transitive_indicator_edgeSet (hGsT n))
    (offDiag_rowSum_lt_top_of_summable _ (summable_indicator_edgeSet (hGsf n))) S' hoS' β
    hΦ).le

/-! ### Non-vacuity witnesses -/

section Witness

open PercLib.Models.Site

open Classical in
/-- Item 1 with the identity isomorphism of the balls of `ℤ`. -/
example (S : Finset (Fin 1 → ℤ)) (hoS : 0 ∈ S) (r : ℕ∞)
    (hS : (S : Set (Fin 1 → ℤ)) ⊆ (zdGraph 1).ball 0 r) (β : ℝ≥0) :
    ∃ S' : Finset (Fin 1 → ℤ), 0 ∈ S' ∧ S'.card = S.card ∧
    ∑ u ∈ S', ∑' w, (if w ∈ S' then 0 else
      law (intensityProfile ((zdGraph 1).edgeSet.indicator fun _ => (1 : ℝ≥0)) β)
        (localConn (S' : Set (Fin 1 → ℤ)) 0 u) *
      (unitInterval.toNNReal
        (intensityProfile ((zdGraph 1).edgeSet.indicator fun _ => (1 : ℝ≥0)) β s(u, w)) :
          ℝ≥0∞)) =
    ∑ u ∈ S, ∑' v, (if v ∈ S then 0 else
      law (intensityProfile ((zdGraph 1).edgeSet.indicator fun _ => (1 : ℝ≥0)) β)
        (localConn (S : Set (Fin 1 → ℤ)) 0 u) *
      (unitInterval.toNNReal
        (intensityProfile ((zdGraph 1).edgeSet.indicator fun _ => (1 : ℝ≥0)) β s(u, v)) :
          ℝ≥0∞)) := by
  have h := boundaryFlux_eq_of_ballIso SimpleGraph.Iso.refl (fun _ => rfl) S hoS hS β
  simp only [boundaryFlux_def] at h
  convert h

/-- `rootCriticalIntensity_le_liminf` for the constant sequence `G_n = G = ℤ` (nearest-neighbour
line, `zdGraph 1`): every hypothesis holds. -/
example : rootCriticalIntensity ((zdGraph 1).edgeSet.indicator fun _ => (1 : ℝ≥0)) 0 ≤
    liminf (fun _ : ℕ => rootCriticalIntensity
      ((zdGraph 1).edgeSet.indicator fun _ => (1 : ℝ≥0)) (0 : Fin 1 → ℤ)) atTop :=
  rootCriticalIntensity_le_liminf (zdGraph 1) (fun _ => zdGraph 1) 0 (fun _ => 0)
    (zdGraph_connected 1) zdGraph_finite_neighborSet (fun _ => zdGraph_finite_neighborSet)
    (fun _ x y => by
      obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (y - x)
      exact ⟨φ, by rw [hφ]; abel⟩)
    (fun _ => Eventually.of_forall fun _ => ⟨SimpleGraph.Iso.refl, fun _ => rfl⟩)

end Witness

end PercLib.Percolation.Bond
