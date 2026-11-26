/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the exact derivative of the escape probability from a finite
domain and the finite-size differential inequality (wiki finite-size-sharpness, tag HATE). No
upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.Wiring.Collapse
public import PercLib.Percolation.Bond.WiredDerivative
public import PercLib.Percolation.Bond.FiniteVolumeRusso
public import PercLib.Percolation.Bond.Pivotal
public import PercLib.Probability.RussoIntegral

/-! # The derivative of the escape probability from a finite domain

Fix `Λ` finite, `o ∈ Λ`, and write `f(β) = P_β(K_o ⊄ Λ)` in the intensity family
`q_β = 1 - e^{-β J}`. Let `S(ω) = {u ∈ Λ | K_u ⊆ Λ}`. Then, for `β > 0`,

`f'(β) = ∑_{T ⊆ Λ, o ∈ T} P_β(S = T) ∑_{u ∈ T} τ_{T,β}(o,u) ∑_{v ∉ T} J(u,v)`

(`hasDerivAt_law_escape`); the same formula is the right derivative at `0`
(`hasDerivWithinAt_law_escape`). Since `q_β ≤ β J`,
`f'(β) ≥ (1 - f(β))/β · min_{T} ∑_{u ∈ T} τ_{T,β}(o,u) ∑_{v ∉ T} q_β(u,v)`
(`deriv_law_escape_ge`).

The proof collapses the exterior of `Λ` to a ghost vertex (`Wiring/Collapse.lean`). On the
finite collapsed graph the escape event is `some o ↔ none`, Russo's formula applies, and a
closed pivotal pair for that event is exactly a pair from `u ∈ S` with `o ↔ u` to a vertex
outside `S`. The factorisation `P(S = T, o ↔_T u) = P(S = T) τ_T(o,u)` of
`WiredDerivative.lean` finishes the computation.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-! ### Closed pivotal pairs on a finite graph with a ghost -/

section Ghost

variable {L : Type*}

/-- A vertex outside the unexplored set `T` is joined to the ghost. -/
theorem mem_conn_none_of_outside {σ : Config (Option L)} {T : Set L}
    (hσ : ∀ u : L, σ ∉ conn (some u) none ↔ u ∈ T) {b : Option L}
    (hb : ∀ w, b = some w → w ∉ T) : σ ∈ conn b none := by
  cases b with
  | none => exact SimpleGraph.Reachable.refl _
  | some w =>
    by_contra h
    exact hb w rfl ((hσ w).1 h)

/-- **Closed pivotal pairs.** If `T` is the set of vertices not joined to the ghost and
`o ∈ T`, a pair is closed and pivotal for `some o ↔ none` exactly when it joins a vertex
`u ∈ T` with `some o ↔ some u` to a vertex outside `T`. -/
theorem closed_pivotal_conn_none_iff {σ : Config (Option L)} {T : Set L} {o : L} (hoT : o ∈ T)
    (hσ : ∀ u : L, σ ∉ conn (some u) none ↔ u ∈ T) (z : Sym2 (Option L)) :
    ((insert z σ ∈ conn (some o) none ∧ σ \ {z} ∉ conn (some o) none) ∧ z ∉ σ) ↔
      ∃ u ∈ T, ∃ b : Option L, (∀ w, b = some w → w ∉ T) ∧ z = s(some u, b) ∧
        σ ∈ conn (some o) (some u) := by
  have ho : σ ∉ conn (some o) none := (hσ o).2 hoT
  -- a vertex joined to `some o` is `some u` with `u ∈ T`
  have hin : ∀ a : Option L, σ ∈ conn (some o) a → ∃ u ∈ T, a = some u := by
    intro a ha
    cases a with
    | none => exact absurd ha ho
    | some u =>
      refine ⟨u, ?_, rfl⟩
      by_contra hu
      exact ho (conn_trans ha (not_not.1 fun h => hu ((hσ u).1 h)))
  -- a vertex joined to the ghost is outside `T`
  have hout : ∀ b : Option L, σ ∈ conn none b → ∀ w, b = some w → w ∉ T := by
    rintro b hb w rfl hw
    exact (hσ w).2 hw (by rw [conn_symm]; exact hb)
  induction z using Sym2.ind with
  | h a b =>
    constructor
    · rintro ⟨hpiv, hz⟩
      by_cases hab : a = b
      · exact absurd hpiv (not_pivotal_conn_of_isDiag σ _ _ (Sym2.mk_isDiag_iff.2 hab))
      have hpiv' := (pivotal_conn_iff σ (some o) none a b hab).1 hpiv
      rw [sdiff_singleton_eq_self hz] at hpiv'
      rcases hpiv'.2 with ⟨hoa, hb⟩ | ⟨hob, ha⟩
      · obtain ⟨u, hu, rfl⟩ := hin a hoa
        refine ⟨u, hu, b, ?_, rfl, hoa⟩
        exact hout b hb
      · obtain ⟨u, hu, rfl⟩ := hin b hob
        refine ⟨u, hu, a, ?_, Sym2.eq_swap, hob⟩
        exact hout a ha
    · rintro ⟨u, hu, c, hc, hz, hou⟩
      have hcn : σ ∈ conn c none := mem_conn_none_of_outside hσ hc
      have hne : some u ≠ c := by
        rintro rfl
        exact hc u rfl hu
      have hzσ : s(a, b) ∉ σ := by
        intro hzσ
        rw [hz] at hzσ
        exact ho (conn_trans hou (conn_trans (mem_conn_of_mem hne hzσ) hcn))
      refine ⟨⟨?_, by rwa [sdiff_singleton_eq_self hzσ]⟩, hzσ⟩
      rw [hz]
      have h1 : insert s(some u, c) σ ∈ conn (some o) (some u) :=
        conn_mono (subset_insert _ _) hou
      have h2 : insert s(some u, c) σ ∈ conn (some u) c :=
        mem_conn_of_mem hne (mem_insert _ _)
      have h3 : insert s(some u, c) σ ∈ conn c none := conn_mono (subset_insert _ _) hcn
      exact conn_trans h1 (conn_trans h2 h3)

/-- Two pairs from `T` to the outside of `T` coincide only if their ends coincide. -/
theorem eq_of_boundary_pair_eq {T : Set L} {u u' : L} {b b' : Option L} (hu : u ∈ T)
    (hb' : ∀ w, b' = some w → w ∉ T) (h : (s(some u, b) : Sym2 (Option L)) = s(some u', b')) :
    u = u' ∧ b = b' := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨Option.some_injective _ h1, h2⟩
  · exact absurd hu (hb' u h1.symm)

open Classical in
/-- **The closed pivotal event on `{S = T}`, pair by pair.** Its probability is the
probability of `{S = T} ∩ {o ↔ u}` when the pair is `s(some u, b)` with `u ∈ T` and `b`
outside `T`, and zero otherwise. -/
theorem measureReal_closed_pivotal_inter [Fintype L] (μ : Measure (Config (Option L)))
    {T : Set L} {o : L} (hoT : o ∈ T) (z : Sym2 (Option L)) :
    μ.real {σ | ((insert z σ ∈ conn (some o) none ∧ σ \ {z} ∉ conn (some o) none) ∧ z ∉ σ) ∧
        ∀ u : L, σ ∉ conn (some u) none ↔ u ∈ T} =
      ∑ p : L × Option L, if p.1 ∈ T ∧ ∀ w, p.2 = some w → w ∉ T then
        (if z = s(some p.1, p.2) then
          μ.real {σ | (∀ u : L, σ ∉ conn (some u) none ↔ u ∈ T) ∧ σ ∈ conn (some o) (some p.1)}
          else 0) else 0 := by
  by_cases hex : ∃ p : L × Option L, (p.1 ∈ T ∧ ∀ w, p.2 = some w → w ∉ T) ∧ z = s(some p.1, p.2)
  · obtain ⟨p, hp, hz⟩ := hex
    rw [Fintype.sum_eq_single p, ite_eq_left hp, ite_eq_left hz]
    · congr 1
      ext σ
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h, hσ⟩
        obtain ⟨u, hu, b, hb, hz', hou⟩ := (closed_pivotal_conn_none_iff hoT hσ z).1 h
        obtain ⟨rfl, -⟩ := eq_of_boundary_pair_eq hu hp.2 (hz'.symm.trans hz)
        exact ⟨hσ, hou⟩
      · rintro ⟨hσ, hou⟩
        exact ⟨(closed_pivotal_conn_none_iff hoT hσ z).2 ⟨p.1, hp.1, p.2, hp.2, hz, hou⟩, hσ⟩
    · intro p' hp'
      by_cases hc : p'.1 ∈ T ∧ ∀ w, p'.2 = some w → w ∉ T
      · rw [ite_eq_left hc, ite_eq_right]
        intro hz'
        obtain ⟨h1, h2⟩ := eq_of_boundary_pair_eq hc.1 hp.2 (hz'.symm.trans hz)
        exact hp' (Prod.ext h1 h2)
      · rw [ite_eq_right hc]
  · push Not at hex
    have hset : {σ : Config (Option L) |
        ((insert z σ ∈ conn (some o) none ∧ σ \ {z} ∉ conn (some o) none) ∧ z ∉ σ) ∧
          ∀ u : L, σ ∉ conn (some u) none ↔ u ∈ T} = ∅ := by
      ext σ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h hσ
      obtain ⟨u, hu, b, hb, hz, -⟩ := (closed_pivotal_conn_none_iff hoT hσ z).1 h
      exact hex (u, b) ⟨hu, hb⟩ hz
    rw [hset, measureReal_empty, Finset.sum_eq_zero]
    intro p _
    split_ifs with hc hz
    · exact absurd hz (hex p hc)
    · rfl
    · rfl

/-- **Closed pivotality is independent of the tested pair.** -/
theorem prodBernoulli_real_closed_pivotal [Fintype L] (p : Sym2 (Option L) → unitInterval)
    (A : Set (Config (Option L))) (z : Sym2 (Option L)) :
    (prodBernoulli p).real {σ | (insert z σ ∈ A ∧ σ \ {z} ∉ A) ∧ z ∉ σ} =
      (1 - (p z : ℝ)) * (prodBernoulli p).real {σ | insert z σ ∈ A ∧ σ \ {z} ∉ A} := by
  have h := prodBernoulli_real_open_pivotal p A z
  have hs := measureReal_inter_add_sdiff (μ := prodBernoulli p)
    (s := {σ : Config (Option L) | insert z σ ∈ A ∧ σ \ {z} ∉ A})
    (Set.toFinite {σ : Config (Option L) | z ∈ σ}).measurableSet
  have e1 : {σ : Config (Option L) | insert z σ ∈ A ∧ σ \ {z} ∉ A} ∩ {σ | z ∈ σ} =
      {σ | (insert z σ ∈ A ∧ σ \ {z} ∉ A) ∧ z ∈ σ} := rfl
  have e2 : {σ : Config (Option L) | insert z σ ∈ A ∧ σ \ {z} ∉ A} \ {σ | z ∈ σ} =
      {σ | (insert z σ ∈ A ∧ σ \ {z} ∉ A) ∧ z ∉ σ} := rfl
  rw [e1, e2, h] at hs
  linarith

end Ghost

/-! ### Partition by the unexplored set and Russo's formula on the ghost graph -/

section Partition

variable {V : Type*} (Λ : Finset V)

open Classical in
/-- **Partition by the unexplored set.** Off `{some o ↔ none}` the events
`{u ∉ S ↔ ...}` indexed by `T ⊆ Λ` with `o ∈ T` partition the configurations of the ghost
graph. -/
theorem measureReal_eq_sum_unexplored (μ : Measure (Config (Option (Λ : Set V))))
    [IsFiniteMeasure μ] (o : (Λ : Set V)) {X : Set (Config (Option (Λ : Set V)))}
    (hX : ∀ σ ∈ X, σ ∉ conn (some o) none) :
    μ.real X = ∑ T ∈ Λ.powerset.filter (fun T => (o : V) ∈ T),
      μ.real {σ | σ ∈ X ∧ ∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T} := by
  rw [← measureReal_biUnion_finset]
  · congr 1
    ext σ
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · intro hσ
      refine ⟨Λ.filter (fun v => ∃ h : v ∈ Λ, σ ∉ conn (some ⟨v, h⟩) none), ?_, hσ, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.filter_subset _ _, o.2, o.2, hX σ hσ⟩
      · intro u
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨u.2, u.2, h⟩, fun ⟨_, _, h⟩ => h⟩
    · rintro ⟨T, -, hσ, -⟩
      exact hσ
  · intro T hT T' hT' hne
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT hT'
    refine Set.disjoint_left.2 fun σ h h' => hne ?_
    ext v
    constructor
    · intro hv
      exact (h'.2 ⟨v, hT.1 hv⟩).1 ((h.2 ⟨v, hT.1 hv⟩).2 hv)
    · intro hv
      exact (h.2 ⟨v, hT'.1 hv⟩).1 ((h'.2 ⟨v, hT'.1 hv⟩).2 hv)
  · intro T _
    exact (Set.toFinite _).measurableSet

open Classical in
/-- **Russo's formula on the ghost graph, summed by the unexplored set.** The derivative of
`P(some o ↔ none)` is the sum over `T` and over pairs from `u ∈ T` to a vertex outside `T`
of the intensity of the pair times `P(S = T, some o ↔ some u)`. -/
theorem hasDerivWithinAt_ghost_escape (JE : Sym2 (Option (Λ : Set V)) → ℝ≥0)
    (o : (Λ : Set V)) {β : ℝ} (hβ : 0 ≤ β) :
    HasDerivWithinAt
      (fun b : ℝ => (law (intensityProfile JE b.toNNReal)).real (conn (some o) none))
      (∑ T ∈ Λ.powerset.filter (fun T => (o : V) ∈ T), ∑ p : ↥(Λ : Set V) × Option ↥(Λ : Set V),
        if (p.1 : V) ∈ T ∧ ∀ w : (Λ : Set V), p.2 = some w → (w : V) ∉ T then
          (JE s(some p.1, p.2) : ℝ) * (law (intensityProfile JE β.toNNReal)).real
            {σ | (∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T) ∧
              σ ∈ conn (some o) (some p.1)}
        else 0) (Ici 0) β := by
  have h := FiniteProfile.event_intensity_real_hasDerivWithinAt
    (E := Sym2 (Option (Λ : Set V))) (fun z => (JE z : ℝ)) β
    (fun b => intensityProfile JE b.toNNReal) (Ici 0)
    (fun z => intensityProfile_toNNReal_coe JE hβ z)
    (fun b hb z => intensityProfile_toNNReal_coe JE (mem_Ici.1 hb) z)
    (A := conn (some o) none) (fun _ _ h hx => conn_mono h hx)
  unfold law
  convert h using 1
  set μ := prodBernoulli (intensityProfile JE β.toNNReal)
  have hz (z : Sym2 (Option (Λ : Set V))) :
      ((JE z : ℝ) * Real.exp (-β * JE z)) *
        μ.real {σ | insert z σ ∈ conn (some o) none ∧ σ \ {z} ∉ conn (some o) none} =
      ∑ T ∈ Λ.powerset.filter (fun T => (o : V) ∈ T), ∑ p : ↥(Λ : Set V) × Option ↥(Λ : Set V),
        (JE z : ℝ) * if (p.1 : V) ∈ T ∧ ∀ w : (Λ : Set V), p.2 = some w → (w : V) ∉ T then
          (if z = s(some p.1, p.2) then
            μ.real {σ | (∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T) ∧
              σ ∈ conn (some o) (some p.1)} else 0) else 0 := by
    have hcl := prodBernoulli_real_closed_pivotal (intensityProfile JE β.toNNReal)
      (conn (some o) none) z
    rw [intensityProfile_toNNReal_coe JE hβ z, sub_sub_cancel] at hcl
    rw [mul_assoc, ← hcl, measureReal_eq_sum_unexplored Λ μ o (fun σ hσ => ?_),
      Finset.mul_sum]
    · refine Finset.sum_congr rfl fun T hT => ?_
      rw [Finset.mem_filter] at hT
      have := measureReal_closed_pivotal_inter μ (T := {u : (Λ : Set V) | (u : V) ∈ T})
        (o := o) hT.2 z
      simp only [mem_ofPred_eq] at this
      rw [← Finset.mul_sum, ← this]
      rfl
    · intro hc
      exact hσ.1.2 (by rwa [sdiff_singleton_eq_self hσ.2])
  symm
  rw [Finset.sum_congr rfl fun z _ => hz z]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hc
  · simp [mul_ite, Finset.sum_ite_eq']
  · simp

end Partition

/-! ### Back to the original graph -/

section Translate

variable {V : Type*} (Λ : Finset V) (π : V → Option (Λ : Set V))

open Classical in
/-- The event `{S = T}` is the pull-back of the ghost event "exactly `T` is not joined to
the ghost". -/
theorem collapse_preimage_unexplored
    (hπ : ∀ v, π v = if h : v ∈ (Λ : Set V) then some ⟨v, h⟩ else none)
    {T : Finset V} (hT : T ⊆ Λ) :
    (fun ω : Config V => {z : Sym2 (Option (Λ : Set V)) | ∃ e ∈ ω, Sym2.map π e = z ∧
        ¬ z.IsDiag}) ⁻¹'
      {σ | ∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T} =
      {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, collapse_mem_conn_none_iff π hπ, not_not]
  constructor
  · intro h
    ext v
    simp only [mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hvΛ, hv⟩
      exact (h ⟨v, hvΛ⟩).1 hv
    · intro hv
      exact ⟨hT hv, (h ⟨v, hT hv⟩).2 hv⟩
  · intro h u
    have := Set.ext_iff.1 h u
    simp only [mem_ofPred_eq, Finset.mem_coe] at this
    exact ⟨fun hu => this.1 ⟨u.2, hu⟩, fun hu => (this.2 hu).2⟩

open Classical in
/-- On `{S = T}` a connection between two vertices of `T` is a connection inside `T`. -/
theorem mem_conn_iff_localConn_of_unexplored_eq {ω : Config V} {T : Finset V}
    (hS : {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)) {o u : V} (ho : o ∈ T)
    (hu : u ∈ T) :
    ω ∈ conn o u ↔ ((openGraph ω).induce (T : Set V)).Reachable ⟨o, ho⟩ ⟨u, hu⟩ := by
  constructor
  · intro h
    have hcl : cluster ω o ⊆ T :=
      cluster_subset_of_boundary_closed (boundary_closed_of_unexplored_eq hS) ho
    obtain ⟨w⟩ := h
    have hw : ∀ v ∈ w.support, v ∈ (T : Set V) := fun v hv => hcl ⟨w.takeUntil v hv⟩
    exact ⟨w.induce (T : Set V) hw⟩
  · exact conn_of_localConn ω (T : Set V) ⟨o, ho⟩ ⟨u, hu⟩

open Classical in
/-- The event `{S = T, o ↔_T u}` is the pull-back of the ghost event
`{S = T, some o ↔ some u}`. -/
theorem collapse_preimage_unexplored_conn
    (hπ : ∀ v, π v = if h : v ∈ (Λ : Set V) then some ⟨v, h⟩ else none)
    {T : Finset V} (hT : T ⊆ Λ) {o u : V} (ho : o ∈ T) (hu : u ∈ T) :
    (fun ω : Config V => {z : Sym2 (Option (Λ : Set V)) | ∃ e ∈ ω, Sym2.map π e = z ∧
        ¬ z.IsDiag}) ⁻¹'
      {σ | (∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T) ∧
        σ ∈ conn (some ⟨o, hT ho⟩) (some ⟨u, hT hu⟩)} =
      {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V) ∧
        ((openGraph ω).induce (T : Set V)).Reachable ⟨o, ho⟩ ⟨u, hu⟩} := by
  ext ω
  have hpre := Set.ext_iff.1 (collapse_preimage_unexplored Λ π hπ hT) ω
  simp only [mem_preimage, mem_ofPred_eq] at hpre ⊢
  constructor
  · rintro ⟨hY, hc⟩
    have hS := hpre.1 hY
    refine ⟨hS, (mem_conn_iff_localConn_of_unexplored_eq Λ hS ho hu).1 ?_⟩
    exact (collapse_mem_conn_some_iff π hπ ω _ _ ((hY ⟨o, hT ho⟩).2 ho)).1 hc
  · rintro ⟨hS, hc⟩
    have hY := hpre.2 hS
    refine ⟨hY, ?_⟩
    exact (collapse_mem_conn_some_iff π hπ ω _ _ ((hY ⟨o, hT ho⟩).2 ho)).2
      ((mem_conn_iff_localConn_of_unexplored_eq Λ hS ho hu).2 hc)

open Classical in
/-- **The ghost weight of a vertex of `T`.** Summing the ghost intensities of the pairs from
`u ∈ T` to the vertices outside `T` gives `∑_{v ∉ T} J(u,v)`. -/
theorem sum_ghost_intensity_outside
    (hπ : ∀ v, π v = if h : v ∈ (Λ : Set V) then some ⟨v, h⟩ else none)
    (J : Sym2 V → ℝ≥0) {u₀ : (Λ : Set V)}
    (hJ : Summable fun v => (J s((u₀ : V), v) : ℝ)) {T : Finset V} (hT : T ⊆ Λ)
    (hu : (u₀ : V) ∈ T) :
    ∑ b : Option (Λ : Set V), (if ∀ w : (Λ : Set V), b = some w → (w : V) ∉ T then
        ((∑' k : {e : Sym2 V // Sym2.map π e = s(some u₀, b) ∧ ¬ (s(some u₀, b)).IsDiag},
          J k : ℝ≥0) : ℝ) else 0) =
      ∑' v, if v ∈ T then 0 else (J s((u₀ : V), v) : ℝ) := by
  rw [Fintype.sum_option]
  simp only [reduceCtorEq, false_implies, implies_true, ite_true, Option.some.injEq,
    forall_eq', ghost_intensity_boundary π hπ J u₀]
  have hin : ∀ w : (Λ : Set V), (if (w : V) ∉ T then
      ((∑' k : {e : Sym2 V // Sym2.map π e = s(some u₀, some w) ∧
        ¬ (s(some u₀, some w)).IsDiag}, J k : ℝ≥0) : ℝ) else 0) =
      if (w : V) ∈ Λ then (if (w : V) ∈ T then 0 else (J s((u₀ : V), w) : ℝ)) else 0 := by
    intro w
    rw [ite_eq_left (show (w : V) ∈ Λ from w.2)]
    by_cases hw : (w : V) ∈ T
    · simp [hw]
    · have hne : u₀ ≠ w := fun h => hw (h ▸ hu)
      rw [ghost_intensity_internal π hπ J hne]
      simp [hw]
  rw [Finset.sum_congr rfl fun w _ => hin w,
    Finset.sum_finset_coe (fun v => if v ∈ Λ then
      (if v ∈ T then 0 else (J s((u₀ : V), v) : ℝ)) else 0) Λ]
  have hsplit : (fun v => if v ∈ T then 0 else (J s((u₀ : V), v) : ℝ)) =
      fun v => ((Λ : Set V)ᶜ.indicator (fun v => (J s((u₀ : V), v) : ℝ)) v +
        if v ∈ Λ then (if v ∈ T then 0 else (J s((u₀ : V), v) : ℝ)) else 0) := by
    funext v
    by_cases hvT : v ∈ T
    · simp [hvT, hT hvT]
    · by_cases hvΛ : v ∈ Λ <;> simp [hvT, hvΛ]
  rw [hsplit, Summable.tsum_add (hJ.indicator _) (summable_of_ne_finset_zero (s := Λ)
    fun v hv => by simp [hv]), ← tsum_subtype, NNReal.coe_tsum,
    tsum_eq_sum (s := Λ) fun v hv => by simp [hv]]

end Translate

/-! ### The derivative formula and the differential inequality -/

section Main

variable {V : Type*} [Countable V]

open Classical in
/-- **Derivative of the escape probability, within `[0, ∞)`.** For a finite domain `Λ ∋ o` and
`J` with summable rows, the escape probability `f(β) = P_β(K_o ⊄ Λ)` has derivative
`∑_{T ⊆ Λ, o ∈ T} P_β(S = T) ∑_{u ∈ T} τ_{T,β}(o,u) ∑_{v ∉ T} J(u,v)` within `[0, ∞)` at
every `β ≥ 0`; at `β = 0` this is the right derivative. -/
theorem hasDerivWithinAt_law_escape (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (Λ : Finset V) {o : V} (ho : o ∈ Λ)
    {β : ℝ} (hβ : 0 ≤ β) :
    HasDerivWithinAt
      (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ})
      (∑ T ∈ Λ.powerset.filter (fun T => o ∈ T),
        (law (intensityProfile J β.toNNReal)).real
            {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} *
          ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
              (localConn (T : Set V) o u) *
            ∑' v, if v ∈ T then 0 else (J s(u, v) : ℝ))
      (Ici 0) β := by
  set π : V → Option (Λ : Set V) :=
    fun v => if h : v ∈ (Λ : Set V) then some ⟨v, h⟩ else none
  have hπ : ∀ v, π v = if h : v ∈ (Λ : Set V) then some ⟨v, h⟩ else none := fun v => rfl
  set JE : Sym2 (Option (Λ : Set V)) → ℝ≥0 :=
    fun z => ∑' k : {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag}, J k
  have hfib := ghost_fibre_summable π hπ J (fun u => (hJ u).subtype _)
  have hreal : ∀ (b : ℝ≥0) (A : Set (Config (Option (Λ : Set V)))),
      (law (intensityProfile JE b)).real A = (law (intensityProfile J b)).real
        ((fun ω : Config V => {z : Sym2 (Option (Λ : Set V)) | ∃ e ∈ ω, Sym2.map π e = z ∧
          ¬ z.IsDiag}) ⁻¹' A) := by
    intro b A
    rw [← law_map_collapse π J b hfib, measureReal_def, measureReal_def,
      Measure.map_apply (measurable_collapse π) (Set.toFinite A).measurableSet]
  set o' : (Λ : Set V) := ⟨o, ho⟩
  have hf : (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real
      {ω | ¬ cluster ω o ⊆ Λ}) =
      fun b => (law (intensityProfile JE b.toNNReal)).real (conn (some o') none) := by
    funext b
    rw [hreal]
    congr 1
    ext ω
    exact (collapse_mem_conn_none_iff π hπ ω o').symm
  rw [hf]
  convert hasDerivWithinAt_ghost_escape Λ JE o' hβ using 1
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  set P := (law (intensityProfile J β.toNNReal)).real
    {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)}
  set τ : V → ℝ := fun u => (law (intensityProfile J β.toNNReal)).real
    (localConn (T : Set V) o u)
  set R : V → ℝ := fun u => ∑' v, if v ∈ T then 0 else (J s(u, v) : ℝ)
  have hterm : ∀ u : (Λ : Set V),
      (∑ b : Option (Λ : Set V),
        if (u : V) ∈ T ∧ ∀ w : (Λ : Set V), b = some w → (w : V) ∉ T then
          (JE s(some u, b) : ℝ) * (law (intensityProfile JE β.toNNReal)).real
            {σ | (∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T) ∧
              σ ∈ conn (some o') (some u)}
        else 0) =
      if (u : V) ∈ T then P * (τ u * R u) else 0 := by
    intro u
    by_cases huT : (u : V) ∈ T
    · rw [ite_eq_left huT]
      have hE : (law (intensityProfile JE β.toNNReal)).real
          {σ | (∀ u : (Λ : Set V), σ ∉ conn (some u) none ↔ (u : V) ∈ T) ∧
            σ ∈ conn (some o') (some u)} = P * τ u := by
        rw [hreal]
        have hpre := collapse_preimage_unexplored_conn Λ π hπ hT.1 hT.2 huT
        rw [hpre]
        have hτ : localConn (T : Set V) o u =
            {ω | ((openGraph ω).induce (T : Set V)).Reachable ⟨o, hT.2⟩ ⟨u, huT⟩} := by
          ext ω
          simp only [mem_ofPred_eq]
          exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hT.2, huT, h⟩⟩
        simp only [P, τ, hτ, measureReal_def]
        rw [law_unexplored_eq_inter_localConn _ Λ T hT.2 huT, ENNReal.toReal_mul]
      have hsum := sum_ghost_intensity_outside Λ π hπ J (u₀ := u) (hJ u) hT.1 huT
      simp only [huT, true_and]
      rw [hE]
      calc (∑ b : Option (Λ : Set V), if ∀ w : (Λ : Set V), b = some w → (w : V) ∉ T then
              (JE s(some u, b) : ℝ) * (P * τ u) else 0)
          = (∑ b : Option (Λ : Set V), if ∀ w : (Λ : Set V), b = some w → (w : V) ∉ T then
              (JE s(some u, b) : ℝ) else 0) * (P * τ u) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun b _ => ?_
            split_ifs <;> simp
        _ = P * (τ u * R u) := by
            rw [hsum]
            ring
    · rw [ite_eq_right huT]
      exact Finset.sum_eq_zero fun b _ => by simp [huT]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun u _ => hterm u,
    Finset.sum_finset_coe (fun v => if v ∈ T then P * (τ v * R v) else 0) Λ,
    Finset.sum_ite_mem, Finset.inter_eq_right.2 hT.1, Finset.mul_sum]

open Classical in
/-- **Derivative of the escape probability.** At every `β > 0` the escape probability is
differentiable with the derivative of `hasDerivWithinAt_law_escape`. -/
theorem hasDerivAt_law_escape (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (Λ : Finset V) {o : V} (ho : o ∈ Λ)
    {β : ℝ} (hβ : 0 < β) :
    HasDerivAt
      (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ})
      (∑ T ∈ Λ.powerset.filter (fun T => o ∈ T),
        (law (intensityProfile J β.toNNReal)).real
            {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} *
          ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
              (localConn (T : Set V) o u) *
            ∑' v, if v ∈ T then 0 else (J s(u, v) : ℝ)) β :=
  (hasDerivWithinAt_law_escape J hJ Λ ho hβ.le).hasDerivAt (Ici_mem_nhds hβ)

open Classical in
/-- The events `{S = T}`, `T ⊆ Λ`, `o ∈ T`, partition `{K_o ⊆ Λ}`. -/
theorem sum_law_unexplored_eq (q : Sym2 V → unitInterval) (Λ : Finset V) {o : V}
    (ho : o ∈ Λ) :
    ∑ T ∈ Λ.powerset.filter (fun T => o ∈ T),
        (law q).real {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} =
      1 - (law q).real {ω | ¬ cluster ω o ⊆ Λ} := by
  have hcover : {ω : Config V | cluster ω o ⊆ Λ} =
      ⋃ T ∈ Λ.powerset.filter (fun T => o ∈ T),
        {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop, Finset.mem_filter,
      Finset.mem_powerset]
    constructor
    · intro h
      refine ⟨Λ.filter (fun v => cluster ω v ⊆ Λ), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · exact Finset.mem_filter.2 ⟨ho, h⟩
      · ext v
        simp
    · rintro ⟨T, ⟨-, hoT⟩, hS⟩
      have : o ∈ {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} := by
        rw [hS]
        exact hoT
      exact this.2
  have hm : MeasurableSet {ω : Config V | cluster ω o ⊆ Λ} := by
    rw [hcover]
    exact Finset.measurableSet_biUnion _ fun T _ => measurableSet_unexplored_eq _ _
  have hc : {ω : Config V | ¬ cluster ω o ⊆ Λ} = {ω | cluster ω o ⊆ Λ}ᶜ := rfl
  rw [hc, measureReal_compl hm, probReal_univ, sub_sub_cancel, hcover,
    measureReal_biUnion_finset]
  · intro T _ T' _ hne
    refine Set.disjoint_left.2 fun ω h h' => hne ?_
    exact Finset.coe_injective (h.symm.trans h')
  · exact fun T _ => measurableSet_unexplored_eq _ _

open Classical in
/-- **Finite-size differential inequality, with an arbitrary lower bound.** If every
`Φ_β(o,T) = ∑_{u ∈ T} τ_{T,β}(o,u) ∑_{v ∉ T} q_β(u,v)` is at least `m`, then
`f'(β) ≥ (1 - f(β))/β · m`. -/
theorem law_escape_derivative_ge (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (Λ : Finset V) {o : V} (ho : o ∈ Λ)
    {β : ℝ} (hβ : 0 < β) {m : ℝ}
    (hm : ∀ T ∈ Λ.powerset.filter (fun T => o ∈ T),
      m ≤ ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
          (localConn (T : Set V) o u) *
        ∑' v, if v ∈ T then 0 else (intensityProfile J β.toNNReal s(u, v) : ℝ)) :
    (1 - (law (intensityProfile J β.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ}) / β * m ≤
      ∑ T ∈ Λ.powerset.filter (fun T => o ∈ T),
        (law (intensityProfile J β.toNNReal)).real
            {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} *
          ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
              (localConn (T : Set V) o u) *
            ∑' v, if v ∈ T then 0 else (J s(u, v) : ℝ) := by
  rw [← sum_law_unexplored_eq _ Λ ho, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_le_sum fun T hT => ?_
  rw [div_mul_eq_mul_div, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  rw [div_le_iff₀' hβ]
  refine (hm T hT).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  have hle : ∀ v, (if v ∈ T then 0 else (intensityProfile J β.toNNReal s(u, v) : ℝ)) ≤
      β * (if v ∈ T then 0 else (J s(u, v) : ℝ)) := by
    intro v
    split_ifs
    · simp
    · rw [intensityProfile_toNNReal_coe J hβ.le]
      linarith [Real.add_one_le_exp (-β * J s(u, v))]
  have hsJ : Summable fun v => β * (if v ∈ T then 0 else (J s(u, v) : ℝ)) := by
    refine Summable.mul_left β ((hJ u).of_nonneg_of_le (fun v => ?_) (fun v => ?_))
    · split_ifs <;> simp
    · split_ifs <;> simp
  have hsq : Summable fun v => (if v ∈ T then 0 else (intensityProfile J β.toNNReal s(u, v) : ℝ)) :=
    hsJ.of_nonneg_of_le (fun v => by split_ifs <;> simp [unitInterval.nonneg]) hle
  rw [← tsum_mul_left]
  exact hsq.tsum_le_tsum hle hsJ

open Classical in
/-- **Finite-size differential inequality.** For `β > 0`,
`f'(β) ≥ (1 - f(β))/β · min_{T ⊆ Λ, o ∈ T} Φ_β(o,T)`. -/
theorem deriv_law_escape_ge (J : Sym2 V → ℝ≥0)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (Λ : Finset V) {o : V} (ho : o ∈ Λ)
    {β : ℝ} (hβ : 0 < β) :
    (1 - (law (intensityProfile J β.toNNReal)).real {ω | ¬ cluster ω o ⊆ Λ}) / β *
        (Λ.powerset.filter (fun T => o ∈ T)).inf'
          ⟨{o}, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 ho),
            Finset.mem_singleton_self o⟩⟩
          (fun T => ∑ u ∈ T, (law (intensityProfile J β.toNNReal)).real
            (localConn (T : Set V) o u) *
            ∑' v, if v ∈ T then 0 else (intensityProfile J β.toNNReal s(u, v) : ℝ)) ≤
      deriv (fun b : ℝ => (law (intensityProfile J b.toNNReal)).real
        {ω | ¬ cluster ω o ⊆ Λ}) β := by
  rw [(hasDerivAt_law_escape J hJ Λ ho hβ).deriv]
  exact law_escape_derivative_ge J hJ Λ ho hβ fun T hT => Finset.inf'_le _ hT

end Main

/-! ### Non-vacuity -/

/-- The smallest case: `Λ = {false}` in `Bool`, with `J` supported on the one
pair `s(false, true)`. Rows are finite sums, so every hypothesis holds, at every `β > 0`. -/
example {β : ℝ} (hβ : 0 < β) :
    ∃ d, HasDerivAt (fun b : ℝ => (law (intensityProfile
        (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0) b.toNNReal)).real
          {ω | ¬ cluster ω false ⊆ (({false} : Finset Bool) : Set Bool)}) d β :=
  ⟨_, hasDerivAt_law_escape _ (fun _ => Summable.of_finite) {false}
    (Finset.mem_singleton_self _) hβ⟩

/-- The differential inequality in the same case, at every `β > 0`. -/
example {β : ℝ} (hβ : 0 < β) :=
  deriv_law_escape_ge (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0)
    (fun _ => Summable.of_finite) {false} (Finset.mem_singleton_self _) hβ

/-- On `Bool`, if the one proper pair is closed, the open graph has no edge. -/
theorem bool_openGraph_eq_bot {ω : Config Bool} (hω : s(false, true) ∉ ω) :
    openGraph ω = ⊥ := by
  ext x y
  rw [openGraph_adj_iff]
  simp only [SimpleGraph.bot_adj, iff_false, not_and]
  intro h hxy
  cases x <;> cases y <;> simp_all [Sym2.eq_swap]

/-- On `Bool`, the cluster of `false` stays in `{false}` exactly when `s(false, true)` is
closed. -/
theorem bool_cluster_false_subset_iff (ω : Config Bool) :
    cluster ω false ⊆ (({false} : Finset Bool) : Set Bool) ↔ s(false, true) ∉ ω := by
  constructor
  · intro h hω
    have : true ∈ cluster ω false :=
      ((openGraph_adj_iff ω false true).2 ⟨hω, by decide⟩).reachable
    simpa using h this
  · intro hω v hv
    simp only [cluster, bool_openGraph_eq_bot hω, SimpleGraph.reachable_bot] at hv
    subst hv
    simp

/-- **The formula evaluated.** In the smallest case the right-hand
side of `hasDerivAt_law_escape` is `P(S = {false}) · τ(false,false) · J(false,true) =
e^{-β} · 1 · 1`. -/
example {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun b : ℝ => (law (intensityProfile
        (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0) b.toNNReal)).real
          {ω | ¬ cluster ω false ⊆ (({false} : Finset Bool) : Set Bool)}) (Real.exp (-β)) β := by
  set J : Sym2 Bool → ℝ≥0 := fun e => if e = s(false, true) then 1 else 0
  have h := hasDerivAt_law_escape J (fun _ => Summable.of_finite) {false}
    (Finset.mem_singleton_self _) hβ
  convert h using 1
  rw [Finset.sum_filter, show ({false} : Finset Bool).powerset = {∅, {false}} by decide,
    Finset.sum_pair (Finset.singleton_ne_empty false).symm]
  rw [ite_eq_right (Finset.notMem_empty false), ite_eq_left (Finset.mem_singleton_self false),
    zero_add, Finset.sum_singleton]
  have hS : {ω : Config Bool | {v | v ∈ (({false} : Finset Bool) : Set Bool) ∧
      cluster ω v ⊆ (({false} : Finset Bool) : Set Bool)} = (({false} : Finset Bool) : Set Bool)}
      = {ω | s(false, true) ∈ ω}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, ← bool_cluster_false_subset_iff]
    constructor
    · intro h
      have : false ∈ {v | v ∈ (({false} : Finset Bool) : Set Bool) ∧
          cluster ω v ⊆ (({false} : Finset Bool) : Set Bool)} := by rw [h]; simp
      exact this.2
    · intro h
      ext v
      simp only [Finset.coe_singleton, mem_singleton_iff, mem_ofPred_eq, and_iff_left_iff_imp]
      rintro rfl
      simpa using h
  have hτ : localConn (({false} : Finset Bool) : Set Bool) false false = univ := by
    ext ω
    simp
  rw [hS, hτ, probReal_univ, one_mul, tsum_fintype, Fintype.sum_bool,
    measureReal_compl (measurableSet_mem _), probReal_univ, measureReal_def, law,
    prodBernoulli_setOf_mem]
  simp [J, intensityProfile_toNNReal_coe _ hβ.le]

/-- In the same case the escape probability itself is `1 - e^{-β}` for `β ≥ 0`, so the
formula above is `d/dβ (1 - e^{-β})`. -/
example {β : ℝ} (hβ : 0 ≤ β) :
    (law (intensityProfile (fun e : Sym2 Bool => if e = s(false, true) then 1 else 0)
        β.toNNReal)).real {ω | ¬ cluster ω false ⊆ (({false} : Finset Bool) : Set Bool)} =
      1 - Real.exp (-β) := by
  simp only [bool_cluster_false_subset_iff, not_not]
  rw [measureReal_def, law, prodBernoulli_setOf_mem]
  simp [intensityProfile_toNNReal_coe _ hβ]

/-- And `e^{-β}` is the derivative of `1 - e^{-β}`. -/
example {β : ℝ} : HasDerivAt (fun b : ℝ => 1 - Real.exp (-b)) (Real.exp (-β)) β := by
  simpa using ((Real.hasDerivAt_exp (-β)).comp β (hasDerivAt_neg β)).const_sub 1

end PercLib.Percolation.Bond
