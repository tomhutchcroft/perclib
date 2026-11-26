/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original proofs on the canonical bond interface; no upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.TwoPaths
public import PercLib.Percolation.Bond.Lace.Coefficients.Coefficients
public import PercLib.Probability.DisjointOccurrenceAlgebra

/-!
# A deleted-bond diagram for the first positive lace coefficient

A connection to a doubly connected pair first meets two disjoint paths at a
branch vertex. Splitting the path it meets gives four disjoint open arms,
without an extra factor for the choice of path. The branch arm retains the
deleted bond. All endpoint coincidences are permitted; the initial diagonal
double connection is retained exactly.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem first_contact {G : SimpleGraph V} {a x : V} (r : G.Walk a x)
    (S : Set V) (hx : x ∈ S) :
    ∃ b ∈ S, ∃ t : G.Walk a b,
      ∀ f ∈ t.edges, ∃ v ∈ f, v ∉ S := by
  induction r with
  | nil => exact ⟨_, hx, .nil, by simp⟩
  | @cons a c x hac r ih =>
    by_cases ha : a ∈ S
    · exact ⟨a, ha, .nil, by simp⟩
    obtain ⟨b, hb, t, ht⟩ := ih hx
    refine ⟨b, hb, .cons hac t, ?_⟩
    intro f hf
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨a, by simp, ha⟩
    · exact ht f hf

private theorem four_arms_of_paths {ω : Config V} {x u a b : V} (e : Sym2 V)
    (p q : (openGraph ω).Walk x u) (t : (openGraph (ω \ {e})).Walk a b)
    (hp : p.IsPath) (hpq : p.edges.Disjoint q.edges)
    (hpt : p.edges.Disjoint t.edges) (hqt : q.edges.Disjoint t.edges)
    (hb : b ∈ p.support) :
    ω ∈ disjointOccurrence
      (disjointOccurrence (disjointOccurrence (conn x b) (conn b u)) (conn x u))
      {η : Config V | η \ {e} ∈ conn b a} := by
  have hdel : IsUpperSet {η : Config V | η \ {e} ∈ conn b a} :=
    fun _ _ h hη => conn_mono (sdiff_subset_sdiff_left h) hη
  apply (mem_disjointOccurrence_three_iff
    (isUpperSet_disjointOccurrence (isUpperSet_conn x b) (isUpperSet_conn b u))
    (isUpperSet_conn x u) hdel ω).mpr
  refine ⟨{f | f ∈ p.edges}, {f | f ∈ q.edges}, {f | f ∈ t.edges},
    List.finite_toSet _, List.finite_toSet _, List.finite_toSet _,
    Set.disjoint_left.mpr (fun _ hf hg => hpq hf hg),
    Set.disjoint_left.mpr (fun _ hf hg => hpt hf hg),
    Set.disjoint_left.mpr (fun _ hf hg => hqt hf hg),
    fun _ hf => mem_of_mem_edges_openGraph p hf,
    fun _ hf => mem_of_mem_edges_openGraph q hf,
    fun _ hf => (mem_of_mem_edges_openGraph t hf).1, ?_, edges_mem_conn q, ?_⟩
  · apply (mem_disjointOccurrence_iff_open
      (isUpperSet_conn x b) (isUpperSet_conn b u) _).mpr
    refine ⟨{f | f ∈ (p.takeUntil b hb).edges}, {f | f ∈ (p.dropUntil b hb).edges},
      List.finite_toSet _, List.finite_toSet _, ?_,
      p.edges_takeUntil_subset_edges hb, p.edges_dropUntil_subset_edges hb,
      edges_mem_conn _, edges_mem_conn _⟩
    exact Set.disjoint_left.mpr
      (fun _ hf hg => hp.isTrail.disjoint_edges_takeUntil_dropUntil hb hf hg)
  · have he : e ∉ {f | f ∈ t.edges} := by
      intro he
      exact (mem_of_mem_edges_openGraph t he).2 (mem_singleton e)
    change {f | f ∈ t.edges} \ {e} ∈ conn b a
    rw [sdiff_singleton_eq_self he, conn_symm b a]
    exact edges_mem_conn t

/-- A doubly connected pair and an additional deleted-bond connection admit
four disjoint arms. The fourth arm still avoids the specified bond. -/
theorem doubleConn_inter_deleted_subset_four_arms (x u a : V) (e : Sym2 V) :
    doubleConn x u ∩ {ω : Config V | ω \ {e} ∈ conn x a} ⊆
      ⋃ b, disjointOccurrence
        (disjointOccurrence (disjointOccurrence (conn x b) (conn b u)) (conn x u))
        {ω : Config V | ω \ {e} ∈ conn b a} := by
  intro ω h
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn h.1
  obtain ⟨r⟩ := (show (openGraph (ω \ {e})).Reachable x a from h.2).symm
  let S : Set V := {v | v ∈ p.support ∨ v ∈ q.support}
  obtain ⟨b, hb, t, ht⟩ := first_contact r S (Or.inl p.start_mem_support)
  have hout {f : Sym2 V} (hf : f ∈ t.edges) : ¬ (f ∈ p.edges ∨ f ∈ q.edges) := by
    obtain ⟨v, hvf, hv⟩ := ht f hf
    intro hmem
    exact hv (hmem.elim
      (fun h => Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges h hvf))
      (fun h => Or.inr (SimpleGraph.Walk.mem_support_of_mem_edges h hvf)))
  have hpt : p.edges.Disjoint t.edges := fun _ hf hg => hout hg (Or.inl hf)
  have hqt : q.edges.Disjoint t.edges := fun _ hf hg => hout hg (Or.inr hf)
  apply mem_iUnion.mpr
  refine ⟨b, ?_⟩
  rcases hb with hb | hb
  · exact four_arms_of_paths e p q t hp hpq hpt hqt hb
  · exact four_arms_of_paths e q p t hq hpq.symm hqt hpt hb

/-- A constant-one bound for the outer layer of the first positive coefficient.
It keeps the deleted-bond two-point function on the branch arm. -/
theorem law_doubleConn_inter_deleted_le [Countable V]
    (q : Sym2 V → unitInterval) (x u a : V) (e : Sym2 V) :
    law q (doubleConn x u ∩ {ω : Config V | ω \ {e} ∈ conn x a}) ≤
      ∑' b, tau q x u * tau q x b * tau q b u *
        law q {ω : Config V | ω \ {e} ∈ conn b a} := by
  refine (measure_mono (doubleConn_inter_deleted_subset_four_arms x u a e)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun b => ?_))
  have hdel : IsUpperSet {ω : Config V | ω \ {e} ∈ conn b a} :=
    fun _ _ h hω => conn_mono (sdiff_subset_sdiff_left h) hω
  have h1 := countable_profile_bk q (isUpperSet_conn x b) (isUpperSet_conn b u)
  have h2 := countable_profile_bk q
    (isUpperSet_disjointOccurrence (isUpperSet_conn x b) (isUpperSet_conn b u))
    (isUpperSet_conn x u)
  have h3 := countable_profile_bk q
    (isUpperSet_disjointOccurrence
      (isUpperSet_disjointOccurrence (isUpperSet_conn x b) (isUpperSet_conn b u))
      (isUpperSet_conn x u)) hdel
  refine h3.trans ((mul_le_mul' (h2.trans (mul_le_mul' h1 le_rfl)) le_rfl).trans_eq ?_)
  change ((tau q x b * tau q b u) * tau q x u) * _ = _
  ac_rfl

/-- The initial diagonal double connection is certain, so its contribution
requires no branch-vertex sum. -/
theorem law_doubleConn_inter_deleted_self (q : Sym2 V → unitInterval)
    (x a : V) (e : Sym2 V) :
    law q (doubleConn x x ∩ {ω : Config V | ω \ {e} ∈ conn x a}) =
      law q {ω : Config V | ω \ {e} ∈ conn x a} := by
  rw [doubleConn_self, univ_inter]

private theorem measure_pi_two_rect (q : Sym2 V → unitInterval)
    (A B : Set (Config V)) :
    (Measure.pi (fun _ : Fin 2 => law q)) {ω | ω 0 ∈ A ∧ ω 1 ∈ B} =
      law q A * law q B := by
  have hs : {ω : Fin 2 → Config V | ω 0 ∈ A ∧ ω 1 ∈ B} =
      Set.pi univ ![A, B] := by
    ext ω
    simp [Set.mem_pi, Fin.forall_fin_two]
  rw [hs, Measure.pi_pi, Fin.prod_univ_two]
  rfl

/-- The two layers of the first coefficient are separated by a union over the
vertex where the second-layer path meets the first-layer deleted cluster. -/
theorem coefficientEvent_one_subset_iUnion (x y : V) (b : Fin 1 → V × V) :
    coefficientEvent x y b ⊆ ⋃ a : V,
      {ω : Fin 2 → Config V |
        ω 0 ∈ doubleConn x (b 0).1 ∩
          {η : Config V | η \ {s((b 0).1, (b 0).2)} ∈ conn x a} ∧
        ω 1 ∈ disjointOccurrence (conn (b 0).2 a) (conn a y)} := by
  intro ω h
  obtain ⟨h0, h1⟩ := (mem_coefficientEvent_one_iff x y b ω).mp h
  have ht := throughSet_subset_iUnion_disjointOccurrence
    (cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y
    (laceEPrime_subset_throughSet _ _ _ h1)
  obtain ⟨a, ha⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨a, ⟨h0, a.property⟩, ha⟩

/-- A two-layer bound retaining the exact joint probability in the initial
layer. BK is applied only to increasing connection events in the next layer. -/
theorem coefficientEvent_one_probability_le [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (b : Fin 1 → V × V) :
    (Measure.pi (fun _ : Fin 2 => law q)) (coefficientEvent x y b) ≤
      ∑' a, law q (doubleConn x (b 0).1 ∩
        {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn x a}) *
        (tau q (b 0).2 a * tau q a y) := by
  refine (measure_mono (coefficientEvent_one_subset_iUnion x y b)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun a => ?_))
  rw [measure_pi_two_rect]
  exact mul_le_mul' le_rfl
    (countable_profile_bk q (isUpperSet_conn (b 0).2 a) (isUpperSet_conn a y))

/-- A constant-one explicit first-coefficient diagram. The `x=u` contribution
is exact in the first layer; elsewhere the branch arm retains bond deletion. -/
theorem coefficientEvent_one_probability_le_diagram [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (b : Fin 1 → V × V) :
    (Measure.pi (fun _ : Fin 2 => law q)) (coefficientEvent x y b) ≤
      ∑' a,
        (if x = (b 0).1 then
          law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn x a}
        else ∑' z, tau q x (b 0).1 * tau q x z * tau q z (b 0).1 *
          law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn z a}) *
        (tau q (b 0).2 a * tau q a y) := by
  refine (coefficientEvent_one_probability_le q x y b).trans
    (ENNReal.tsum_le_tsum fun a => mul_le_mul' ?_ le_rfl)
  by_cases h : x = (b 0).1
  · rw [ite_eq_left h]
    simpa only [← h] using
      (law_doubleConn_inter_deleted_self q x a s(x, (b 0).2)).le
  · simpa [h] using
      law_doubleConn_inter_deleted_le q x (b 0).1 a s((b 0).1, (b 0).2)

/-- The actual first lace coefficient is bounded by the deleted-bond diagram,
with no assumed diagram input or finiteness hypothesis. The existing
off-diagonal kernel removes loop weights exactly. -/
theorem laceCoefficient_one_le_diagram [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    laceCoefficient q 1 x y ≤ ∑' u, ∑' v,
      offDiagonal (fun r t : V => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) u v *
        ∑' a,
          (if x = u then law q {ω : Config V | ω \ {s(u, v)} ∈ conn x a}
          else ∑' z, tau q x u * tau q x z * tau q z u *
            law q {ω : Config V | ω \ {s(u, v)} ∈ conn z a}) *
          (tau q v a * tau q a y) := by
  let F : V × V → ℝ≥0∞ := fun uv =>
    offDiagonal (fun r t : V => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) uv.1 uv.2 *
      ∑' a,
        (if x = uv.1 then law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn x a}
        else ∑' z, tau q x uv.1 * tau q x z * tau q z uv.1 *
          law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn z a}) *
        (tau q uv.2 a * tau q a y)
  calc
    laceCoefficient q 1 x y ≤ ∑' b : Fin 1 → V × V, F (b 0) := by
      unfold laceCoefficient
      apply ENNReal.tsum_le_tsum
      intro b
      change (∏ i : Fin 1,
        offDiagonal (fun r t : V => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞))
          (b i).1 (b i).2) * _ ≤ _
      rw [Fin.prod_univ_one]
      exact mul_le_mul' le_rfl (coefficientEvent_one_probability_le_diagram q x y b)
    _ = ∑' uv : V × V, F uv := (Equiv.funUnique (Fin 1) (V × V)).tsum_eq F
    _ = ∑' u, ∑' v, F (u, v) := ENNReal.tsum_prod'

example [Countable V] (q : Sym2 V → unitInterval) (x a : V) (e : Sym2 V) :
    law q (doubleConn x x ∩ {ω : Config V | ω \ {e} ∈ conn x a}) =
      law q {ω : Config V | ω \ {e} ∈ conn x a} :=
  law_doubleConn_inter_deleted_self q x a e

end PercLib.Percolation.Bond.Lace
