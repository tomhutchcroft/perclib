/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16: the law of a bond configuration collapsed along a vertex map, and
the wiring of the exterior of a domain into one ghost vertex. No upstream proof is copied, no
definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.Wiring.BoundaryLaw
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Probability.Characterization

/-! # Collapsing a bond configuration along a vertex map

For `π : V → W` the collapsed configuration of `ω : Config V` is the set of off-diagonal
pairs `z` of `W` that are images of open pairs of `ω`,
`{z | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}`. A pair `z` is open there exactly when one
pair of its fibre `{e | Sym2.map π e = z ∧ ¬ z.IsDiag}` is open. The fibres are disjoint, so
in the intensity family the collapsed configuration is again a Bernoulli configuration, with
intensity the sum of `J` over the fibre (`law_map_collapse`).

For a domain `Λ ⊆ V` and the map `V → Option Λ` sending the exterior to `none`, the vertex
`none` is a ghost wired to the whole exterior: `some u` is joined to `none` exactly when the
cluster of `u` leaves `Λ` (`collapse_mem_conn_none_iff`), and away from the ghost
connections inside `Λ` are the original ones (`collapse_mem_conn_some_iff`).
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V W : Type*}

/-- Membership in the collapsed configuration is the opening of one pair of the fibre. -/
theorem mem_collapse_iff (π : V → W) (ω : Config V) (z : Sym2 W) :
    z ∈ {z : Sym2 W | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag} ↔
      ∃ k : {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag}, (k : Sym2 V) ∈ ω := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨⟨e, h⟩, he⟩
  · rintro ⟨⟨e, h⟩, he⟩
    exact ⟨e, he, h⟩

/-- **Collapsing maps open paths to open paths.** -/
theorem reachable_collapse (π : V → W) (ω : Config V) {x y : V}
    (h : (openGraph ω).Reachable x y) :
    (openGraph {z : Sym2 W | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}).Reachable
      (π x) (π y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact .refl _
  | @tail b c _ hbc ih =>
    refine ih.trans ?_
    by_cases hπ : π b = π c
    · rw [hπ]
    · rw [openGraph_adj_iff] at hbc
      refine SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨⟨s(b, c), hbc.1, rfl, ?_⟩, hπ⟩)
      simpa [Sym2.mk_isDiag_iff] using hπ

/-! ### Wiring the exterior of a domain into a ghost vertex -/

section Ghost

variable {Λ : Set V} [DecidablePred (· ∈ Λ)] (π : V → Option Λ)

/-- The ghost map sends a vertex to `some` of itself exactly in the domain. -/
theorem ghost_eq_some_iff (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    {v : V} {w : Λ} : π v = some w ↔ v = w := by
  rw [hπ v]
  constructor
  · intro h
    split_ifs at h with hv
    · exact congrArg Subtype.val (Option.some_injective _ h)
  · rintro rfl
    simp

/-- The ghost map sends exactly the exterior to `none`. -/
theorem ghost_eq_none_iff (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    {v : V} : π v = none ↔ v ∉ Λ := by
  rw [hπ v]
  split_ifs with hv <;> simp [hv]

/-- **Lifting ghost paths.** A collapsed path from `some u` either reflects an open path
from `u` to the exterior, or ends at `some w` with `u` joined to `w`. -/
theorem collapse_reachable_lift (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (ω : Config V) (u : Λ) {b : Option Λ}
    (h : (openGraph {z : Sym2 (Option Λ) | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}).Reachable
      (some u) b) :
    (∃ y ∉ Λ, ω ∈ conn (u : V) y) ∨ ∃ w : Λ, b = some w ∧ ω ∈ conn (u : V) w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inr ⟨u, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail c d _ hcd ih =>
    rcases ih with hl | ⟨w, rfl, hw⟩
    · exact Or.inl hl
    · rw [openGraph_adj_iff] at hcd
      obtain ⟨⟨e, he, hmap, -⟩, hne⟩ := hcd
      have key : ∃ x y : V, s(x, y) ∈ ω ∧ π x = some w ∧ π y = d := by
        induction e using Sym2.ind with
        | h x y =>
          rcases Sym2.eq_iff.1 hmap with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact ⟨x, y, he, hx, hy⟩
          · exact ⟨y, x, Sym2.eq_swap ▸ he, hy, hx⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := key
      have hxw : x = w := (ghost_eq_some_iff π hπ).1 hx
      have hne' : x ≠ y := by
        rintro rfl
        exact hne (hx.symm.trans hy)
      have hwy : ω ∈ conn (w : V) y := hxw ▸ mem_conn_of_mem hne' hxy
      have huy : ω ∈ conn (u : V) y := conn_trans hw hwy
      by_cases hyΛ : y ∈ Λ
      · refine Or.inr ⟨⟨y, hyΛ⟩, ?_, huy⟩
        rw [← hy, hπ y]
        simp [hyΛ]
      · exact Or.inl ⟨y, hyΛ, huy⟩

/-- **The ghost detects escape.** `some u` is joined to the ghost in the collapsed
configuration exactly when the cluster of `u` leaves `Λ`. -/
theorem collapse_mem_conn_none_iff (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (ω : Config V) (u : Λ) :
    {z : Sym2 (Option Λ) | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag} ∈ conn (some u) none ↔
      ¬ cluster ω u ⊆ Λ := by
  constructor
  · intro h hsub
    rcases collapse_reachable_lift π hπ ω u h with ⟨y, hy, huy⟩ | ⟨w, hw, -⟩
    · exact hy (hsub huy)
    · exact Option.some_ne_none w hw.symm
  · intro h
    obtain ⟨y, hy, hyΛ⟩ := not_subset.1 h
    have := reachable_collapse π ω hy
    rwa [(ghost_eq_some_iff π hπ).2 rfl, (ghost_eq_none_iff π hπ).2 hyΛ] at this

/-- **Away from the ghost, connections are unchanged.** -/
theorem collapse_mem_conn_some_iff
    (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none) (ω : Config V) (u w : Λ)
    (hu : {z : Sym2 (Option Λ) | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag} ∉
      conn (some u) none) :
    {z : Sym2 (Option Λ) | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag} ∈ conn (some u) (some w) ↔
      ω ∈ conn (u : V) w := by
  constructor
  · intro h
    rcases collapse_reachable_lift π hπ ω u h with ⟨y, hy, huy⟩ | ⟨w', hw', huw⟩
    · exact absurd ((collapse_mem_conn_none_iff π hπ ω u).2
        fun hsub => hy (hsub huy)) hu
    · rwa [Option.some_injective _ hw']
  · intro h
    have := reachable_collapse π ω h
    rwa [(ghost_eq_some_iff π hπ).2 rfl, (ghost_eq_some_iff π hπ).2 rfl] at this

/-- The ghost fibre of a pair `s(some u, none)` is the set of pairs from `u` to the
exterior. -/
theorem ghost_fibre_boundary (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (u : Λ) (e : Sym2 V) :
    (Sym2.map π e = s(some u, none) ∧ ¬ (s(some u, none) : Sym2 (Option Λ)).IsDiag) ↔
      ∃ y ∉ Λ, e = s((u : V), y) := by
  induction e using Sym2.ind with
  | h x y =>
    have hnd : ¬ (s(some u, none) : Sym2 (Option Λ)).IsDiag := by simp
    simp only [hnd, not_false_eq_true, and_true, Sym2.map_mk, Sym2.eq_iff]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · refine ⟨y, (ghost_eq_none_iff π hπ).1 hy, ?_⟩
        rw [(ghost_eq_some_iff π hπ).1 hx]
        simp
      · refine ⟨x, (ghost_eq_none_iff π hπ).1 hx, ?_⟩
        rw [(ghost_eq_some_iff π hπ).1 hy]
        simp
    · rintro ⟨z, hz, he⟩
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨(ghost_eq_some_iff π hπ).2 rfl, (ghost_eq_none_iff π hπ).2 hz⟩
      · exact Or.inr ⟨(ghost_eq_none_iff π hπ).2 hz, (ghost_eq_some_iff π hπ).2 rfl⟩

/-- The ghost fibre of a pair `s(some a, some b)` with `a ≠ b` is the single pair
`s(a, b)`. -/
theorem ghost_fibre_internal (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    {a b : Λ} (hab : a ≠ b) (e : Sym2 V) :
    (Sym2.map π e = s(some a, some b) ∧ ¬ (s(some a, some b) : Sym2 (Option Λ)).IsDiag) ↔
      e = s((a : V), b) := by
  induction e using Sym2.ind with
  | h x y =>
    have hnd : ¬ (s(some a, some b) : Sym2 (Option Λ)).IsDiag := by simpa using hab
    simp only [hnd, not_false_eq_true, and_true, Sym2.map_mk, Sym2.eq_iff,
      ghost_eq_some_iff π hπ]

/-- The pairs from `u` to the exterior are in bijection with the ghost fibre of
`s(some u, none)`. -/
theorem ghost_boundary_bijective (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (u : Λ) :
    Function.Bijective (fun y : (Λᶜ : Set V) =>
      (⟨s((u : V), y), (ghost_fibre_boundary π hπ u _).2 ⟨y, y.2, rfl⟩⟩ :
        {e : Sym2 V // Sym2.map π e = s(some u, none) ∧
          ¬ (s(some u, none) : Sym2 (Option Λ)).IsDiag})) := by
  constructor
  · intro y y' h
    have h' := congrArg Subtype.val h
    simp only [Sym2.eq_iff, true_and] at h'
    rcases h' with h' | ⟨h₁, h₂⟩
    · exact Subtype.ext h'
    · exact Subtype.ext (h₂.trans h₁)
  · rintro ⟨e, he⟩
    obtain ⟨y, hy, rfl⟩ := (ghost_fibre_boundary π hπ u e).1 he
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **The ghost intensity of a boundary pair** is the exterior row sum. -/
theorem ghost_intensity_boundary (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (J : Sym2 V → ℝ≥0) (u : Λ) :
    ∑' k : {e : Sym2 V // Sym2.map π e = s(some u, none) ∧
        ¬ (s(some u, none) : Sym2 (Option Λ)).IsDiag}, J k =
      ∑' y : (Λᶜ : Set V), J s((u : V), y) :=
  ((Equiv.ofBijective _ (ghost_boundary_bijective π hπ u)).tsum_eq (fun k => J k)).symm

/-- **The ghost intensity of an internal pair** is its intensity. -/
theorem ghost_intensity_internal (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (J : Sym2 V → ℝ≥0) {a b : Λ} (hab : a ≠ b) :
    ∑' k : {e : Sym2 V // Sym2.map π e = s(some a, some b) ∧
        ¬ (s(some a, some b) : Sym2 (Option Λ)).IsDiag}, J k = J s((a : V), b) := by
  have hk : ∀ k : {e : Sym2 V // Sym2.map π e = s(some a, some b) ∧
      ¬ (s(some a, some b) : Sym2 (Option Λ)).IsDiag}, (k : Sym2 V) = s((a : V), b) :=
    fun k => (ghost_fibre_internal π hπ hab k).1 k.2
  let k₀ : {e : Sym2 V // Sym2.map π e = s(some a, some b) ∧
      ¬ (s(some a, some b) : Sym2 (Option Λ)).IsDiag} :=
    ⟨s((a : V), b), (ghost_fibre_internal π hπ hab _).2 rfl⟩
  rw [tsum_eq_single k₀ fun k hk' => absurd (Subtype.ext ((hk k).trans (hk k₀).symm)) hk']

/-- **Summable ghost fibres.** If every vertex of `Λ` has a summable exterior row, every
ghost fibre is summable. -/
theorem ghost_fibre_summable (hπ : ∀ v, π v = if h : v ∈ Λ then some ⟨v, h⟩ else none)
    (J : Sym2 V → ℝ≥0) (hJ : ∀ u : Λ, Summable fun y : (Λᶜ : Set V) => (J s((u : V), y) : ℝ))
    (z : Sym2 (Option Λ)) :
    Summable fun k : {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag} => (J k : ℝ) := by
  have hb : ∀ u : Λ, Summable fun k : {e : Sym2 V // Sym2.map π e = s(some u, none) ∧
      ¬ (s(some u, none) : Sym2 (Option Λ)).IsDiag} => (J k : ℝ) := by
    intro u
    rw [← (Equiv.ofBijective _ (ghost_boundary_bijective π hπ u)).summable_iff]
    exact hJ u
  induction z using Sym2.ind with
  | h a b =>
    cases a with
    | none =>
      cases b with
      | none =>
        have : IsEmpty {e : Sym2 V // Sym2.map π e = s(none, none) ∧
            ¬ (s(none, none) : Sym2 (Option Λ)).IsDiag} := ⟨fun k => k.2.2 (by simp)⟩
        exact Summable.of_finite
      | some b =>
        rw [Sym2.eq_swap]
        exact hb b
    | some a =>
      cases b with
      | none => exact hb a
      | some b =>
        by_cases hab : a = b
        · subst hab
          have : IsEmpty {e : Sym2 V // Sym2.map π e = s(some a, some a) ∧
              ¬ (s(some a, some a) : Sym2 (Option Λ)).IsDiag} := ⟨fun k => k.2.2 (by simp)⟩
          exact Summable.of_finite
        · have : Subsingleton {e : Sym2 V // Sym2.map π e = s(some a, some b) ∧
              ¬ (s(some a, some b) : Sym2 (Option Λ)).IsDiag} :=
            ⟨fun k k' => Subtype.ext (((ghost_fibre_internal π hπ hab k).1 k.2).trans
              ((ghost_fibre_internal π hπ hab k').1 k'.2).symm)⟩
          exact Summable.of_finite

end Ghost

variable [Countable V]

/-- The collapsed configuration is a measurable function of the configuration. -/
theorem measurable_collapse (π : V → W) :
    Measurable (fun ω : Config V => {z : Sym2 W | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}) := by
  refine measurable_set_iff.mpr fun z => ?_
  have : (fun ω : Config V => z ∈ {z : Sym2 W | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}) =
      fun ω => ∃ k : {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag}, (k : Sym2 V) ∈ ω :=
    funext fun ω => propext (mem_collapse_iff π ω z)
  rw [this]
  exact Measurable.exists fun k => measurable_set_mem _

omit [Countable V] in
/-- **All pairs of a summable family closed.** In the intensity family the probability that
every pair of an injective family is closed is `exp(-β ∑ J)`. -/
theorem law_all_closed_exponential {K : Type*} [Countable K] (e : K → Sym2 V)
    (he : Function.Injective e) (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (hs : Summable fun k => (J (e k) : ℝ)) :
    law (intensityProfile J β) {ω | ∀ k, e k ∉ ω} =
      ENNReal.ofReal (Real.exp (-(β : ℝ) * ∑' k, (J (e k) : ℝ))) := by
  have h := law_map_injective_coordinates (intensityProfile J β) e he
  have hm : MeasurableSet (Set.pi Set.univ (fun _ : K => ({False} : Set Prop))) :=
    MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_singleton _)
  have h1 := congrArg (fun μ : Measure (K → Prop) =>
    μ (Set.pi Set.univ (fun _ => ({False} : Set Prop)))) h
  rw [Measure.map_apply (by fun_prop) hm, Measure.infinitePi_pi_of_countable _
    (Set.to_countable _) (fun _ _ => measurableSet_singleton _)] at h1
  rw [tprod_univ (f := fun k : K =>
    bernoulliMeasure True False (intensityProfile J β (e k)) {False})] at h1
  have hf (k : K) : bernoulliMeasure True False (intensityProfile J β (e k)) {False} =
      ENNReal.ofReal (Real.exp (-(β : ℝ) * J (e k))) := by
    rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) rfl,
      ← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [intensityProfile]
  have h2 : law (intensityProfile J β) {ω | ∀ k, e k ∉ ω} =
      ∏' k, ENNReal.ofReal (Real.exp (-(β : ℝ) * J (e k))) := by
    rw [← tprod_congr hf, ← h1]
    congr 1
    ext ω
    simp
  rw [h2]
  have ht := (Real.continuous_exp.tendsto _).comp (hs.hasSum.mul_left (-(β : ℝ)))
  have ht' := (ENNReal.continuous_ofReal.tendsto _).comp ht
  have hp : HasProd (fun k => ENNReal.ofReal (Real.exp (-(β : ℝ) * J (e k))))
      (ENNReal.ofReal (Real.exp (-(β : ℝ) * ∑' k, (J (e k) : ℝ)))) := by
    unfold HasProd
    convert ht' using 1
    funext F
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    simp [Function.comp]
  exact hp.tprod_eq

/-- **The collapsed law.** In the intensity family, collapsing along `π` gives the intensity
family on `W` whose intensity at `z` is the sum of `J` over the fibre of `z`; the fibre of a
loop is empty. Summability of `J` on each fibre is explicit. -/
theorem law_map_collapse (π : V → W) (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (hJ : ∀ z : Sym2 W,
      Summable fun k : {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag} => (J k : ℝ)) :
    (law (intensityProfile J β)).map
        (fun ω => {z : Sym2 W | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}) =
      law (intensityProfile
        (fun z => ∑' k : {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag}, J k) β) := by
  set K : Sym2 W → Type _ := fun z => {e : Sym2 V // Sym2.map π e = z ∧ ¬ z.IsDiag}
  have hinj : Function.Injective (fun a : (z : Sym2 W) × K z => (a.2 : Sym2 V)) := by
    rintro ⟨z, k⟩ ⟨z', k'⟩ h
    simp only at h
    have hz : z = z' := k.2.1.symm.trans ((congrArg (Sym2.map π) h).trans k'.2.1)
    subst hz
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))
  have hind := law_iIndepFun_injective_blocks (intensityProfile J β)
    (fun a : (z : Sym2 W) × K z => (a.2 : Sym2 V)) hinj
  have hm (z : Sym2 W) : Measurable (fun f : K z → Prop => ∃ k, f k) :=
    Measurable.exists fun k => measurable_pi_apply k
  have hc := hind.comp (fun z (f : K z → Prop) => ∃ k, f k) hm
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hc
  unfold law
  rw [map_prodBernoulli_eq_iff _ (measurable_collapse π)]
  intro F
  have hpre : (fun ω : Config V => {z : Sym2 W | ∃ e ∈ ω, Sym2.map π e = z ∧ ¬ z.IsDiag}) ⁻¹'
      {σ | (F : Set (Sym2 W)) ⊆ σ} =
      ⋂ z ∈ F, (fun (ω : Config V) => ∃ k : K z, (k : Sym2 V) ∈ ω) ⁻¹' {True} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iInter, mem_singleton_iff, eq_iff_iff,
      iff_true]
    constructor
    · intro h z hz
      exact (mem_collapse_iff π ω z).1 (h hz)
    · intro h z hz
      exact (mem_collapse_iff π ω z).2 (h z hz)
  have h := hc F (sets := fun _ => {True}) (fun _ _ => measurableSet_singleton _)
  simp only [Function.comp_def] at h
  rw [hpre]
  refine h.trans (Finset.prod_congr rfl fun z _ => ?_)
  have hcl := law_all_closed_exponential (fun k : K z => (k : Sym2 V)) Subtype.val_injective
    J β (hJ z)
  have hcompl : (fun (ω : Config V) => ∃ k : K z, (k : Sym2 V) ∈ ω) ⁻¹' {True} =
      {ω | ∀ k : K z, (k : Sym2 V) ∉ ω}ᶜ := by
    ext ω
    simp
  have hmeas : MeasurableSet {ω : Config V | ∀ k : K z, (k : Sym2 V) ∉ ω} := by
    have : {ω : Config V | ∀ k : K z, (k : Sym2 V) ∉ ω} =
        ⋂ k : K z, {ω | (k : Sym2 V) ∉ ω} := by
      ext ω
      simp
    rw [this]
    exact MeasurableSet.iInter fun k => (measurableSet_setOfPred.2 (measurable_set_mem _)).compl
  change prodBernoulli (intensityProfile J β) _ = _
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  change 1 - law (intensityProfile J β) _ = _
  rw [hcl, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  congr 1
  simp [intensityProfile, NNReal.coe_tsum, K]


/-! ### Non-vacuity -/

-- The identity collapse of `Bool`: the hypotheses of `law_map_collapse` hold at every
-- intensity, since every fibre has at most one element.
example (J : Sym2 Bool → ℝ≥0) (β : ℝ≥0) :
    (law (intensityProfile J β)).map
        (fun ω => {z : Sym2 Bool | ∃ e ∈ ω, Sym2.map id e = z ∧ ¬ z.IsDiag}) =
      law (intensityProfile
        (fun z => ∑' k : {e : Sym2 Bool // Sym2.map id e = z ∧ ¬ z.IsDiag}, J k) β) :=
  law_map_collapse id J β fun _ => Summable.of_finite

-- The ghost of the domain `{false}` in `Bool`: the cluster of `false` leaves the domain
-- exactly when `false` is joined to the ghost.
open Classical in
example (ω : Config Bool) :
    {z : Sym2 (Option ({false} : Set Bool)) | ∃ e ∈ ω,
        Sym2.map (fun v => if h : v ∈ ({false} : Set Bool) then some ⟨v, h⟩ else none) e = z ∧
          ¬ z.IsDiag} ∈ conn (some ⟨false, rfl⟩) none ↔
      ¬ cluster ω false ⊆ ({false} : Set Bool) :=
  collapse_mem_conn_none_iff (Λ := ({false} : Set Bool)) _ (fun _ => rfl) ω ⟨false, rfl⟩

end PercLib.Percolation.Bond
