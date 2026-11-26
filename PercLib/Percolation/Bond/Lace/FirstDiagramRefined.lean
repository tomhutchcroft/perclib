/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original proofs on the canonical bond interface; no upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.FirstDiagram
public import PercLib.Percolation.Bond.Lace.FirstPivotal

/-!
# Additional deletion in the first lace diagram

When the deleted bond meets the doubly connected endpoint, both the arm from
the root to the branch vertex and the outgoing branch arm can avoid it.
The endpoint case is handled by choosing the other disjoint path if needed.
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

private theorem four_arms_of_paths_deleted_prefix {ω : Config V} {x u a b : V}
    (e : Sym2 V) (p q : (openGraph ω).Walk x u)
    (t : (openGraph (ω \ {e})).Walk a b)
    (hp : p.IsPath) (hpq : p.edges.Disjoint q.edges)
    (hpt : p.edges.Disjoint t.edges) (hqt : q.edges.Disjoint t.edges)
    (hb : b ∈ p.support) (he : e ∉ (p.takeUntil b hb).edges) :
    ω ∈ disjointOccurrence
      (disjointOccurrence
        (disjointOccurrence {η : Config V | η \ {e} ∈ conn x b} (conn b u))
        (conn x u))
      {η : Config V | η \ {e} ∈ conn b a} := by
  have hdel (r s : V) : IsUpperSet {η : Config V | η \ {e} ∈ conn r s} :=
    fun _ _ h hη => conn_mono (sdiff_subset_sdiff_left h) hη
  apply (mem_disjointOccurrence_three_iff
    (isUpperSet_disjointOccurrence (hdel x b) (isUpperSet_conn b u))
    (isUpperSet_conn x u) (hdel b a) ω).mpr
  refine ⟨{f | f ∈ p.edges}, {f | f ∈ q.edges}, {f | f ∈ t.edges},
    List.finite_toSet _, List.finite_toSet _, List.finite_toSet _,
    Set.disjoint_left.mpr (fun _ hf hg => hpq hf hg),
    Set.disjoint_left.mpr (fun _ hf hg => hpt hf hg),
    Set.disjoint_left.mpr (fun _ hf hg => hqt hf hg),
    fun _ hf => mem_of_mem_edges_openGraph p hf,
    fun _ hf => mem_of_mem_edges_openGraph q hf,
    fun _ hf => (mem_of_mem_edges_openGraph t hf).1, ?_, edges_mem_conn q, ?_⟩
  · apply (mem_disjointOccurrence_iff_open (hdel x b) (isUpperSet_conn b u) _).mpr
    refine ⟨{f | f ∈ (p.takeUntil b hb).edges}, {f | f ∈ (p.dropUntil b hb).edges},
      List.finite_toSet _, List.finite_toSet _, ?_,
      p.edges_takeUntil_subset_edges hb, p.edges_dropUntil_subset_edges hb,
      ?_, edges_mem_conn _⟩
    · exact Set.disjoint_left.mpr
        (fun _ hf hg => hp.isTrail.disjoint_edges_takeUntil_dropUntil hb hf hg)
    · change {f | f ∈ (p.takeUntil b hb).edges} \ {e} ∈ conn x b
      rw [sdiff_singleton_eq_self (show e ∉ {f | f ∈ (p.takeUntil b hb).edges} from he)]
      exact edges_mem_conn _
  · have he' : e ∉ {f | f ∈ t.edges} := by
      intro he'
      exact (mem_of_mem_edges_openGraph t he').2 (mem_singleton e)
    change {f | f ∈ t.edges} \ {e} ∈ conn b a
    rw [sdiff_singleton_eq_self he', conn_symm b a]
    exact edges_mem_conn t

/-- If the deleted bond meets the doubly connected endpoint, the two branch
arms can both avoid it. No endpoint-distinctness assumption is needed. -/
theorem doubleConn_inter_deleted_subset_four_arms_endpoint (x u v a : V) :
    doubleConn x u ∩ {ω : Config V | ω \ {s(u, v)} ∈ conn x a} ⊆
      ⋃ b, disjointOccurrence
        (disjointOccurrence
          (disjointOccurrence {ω : Config V | ω \ {s(u, v)} ∈ conn x b} (conn b u))
          (conn x u))
        {ω : Config V | ω \ {s(u, v)} ∈ conn b a} := by
  intro ω h
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn h.1
  obtain ⟨r⟩ := (show (openGraph (ω \ {s(u, v)})).Reachable x a from h.2).symm
  let S : Set V := {w | w ∈ p.support ∨ w ∈ q.support}
  obtain ⟨b, hb, t, ht⟩ := first_contact r S (Or.inl p.start_mem_support)
  have hout {f : Sym2 V} (hf : f ∈ t.edges) : ¬ (f ∈ p.edges ∨ f ∈ q.edges) := by
    obtain ⟨w, hwf, hw⟩ := ht f hf
    intro hmem
    exact hw (hmem.elim
      (fun h => Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges h hwf))
      (fun h => Or.inr (SimpleGraph.Walk.mem_support_of_mem_edges h hwf)))
  have hpt : p.edges.Disjoint t.edges := fun _ hf hg => hout hg (Or.inl hf)
  have hqt : q.edges.Disjoint t.edges := fun _ hf hg => hout hg (Or.inr hf)
  apply mem_iUnion.mpr
  refine ⟨b, ?_⟩
  by_cases hbu : b = u
  · subst b
    by_cases he : s(u, v) ∈ p.edges
    · apply four_arms_of_paths_deleted_prefix s(u, v) q p t hq hpq.symm hqt hpt
        q.end_mem_support
      exact fun hf => hpq he (q.edges_takeUntil_subset_edges q.end_mem_support hf)
    · apply four_arms_of_paths_deleted_prefix s(u, v) p q t hp hpq hpt hqt
        p.end_mem_support
      exact fun hf => he (p.edges_takeUntil_subset_edges p.end_mem_support hf)
  · rcases hb with hb | hb
    · apply four_arms_of_paths_deleted_prefix s(u, v) p q t hp hpq hpt hqt hb
      intro he
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hb (Ne.symm hbu)
        (SimpleGraph.Walk.mem_support_of_mem_edges he (Sym2.mem_mk_left u v))
    · apply four_arms_of_paths_deleted_prefix s(u, v) q p t hq hpq.symm hqt hpt hb
      intro he
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hq hb (Ne.symm hbu)
        (SimpleGraph.Walk.mem_support_of_mem_edges he (Sym2.mem_mk_left u v))

/-- The endpoint-specific diagram retains deletion on both branch arms. -/
theorem law_doubleConn_inter_deleted_le_endpoint [Countable V]
    (q : Sym2 V → unitInterval) (x u v a : V) :
    law q (doubleConn x u ∩ {ω : Config V | ω \ {s(u, v)} ∈ conn x a}) ≤
      ∑' b, tau q x u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn x b} *
        tau q b u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn b a} := by
  refine (measure_mono (doubleConn_inter_deleted_subset_four_arms_endpoint x u v a)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun b => ?_))
  have hdel (r s : V) : IsUpperSet {ω : Config V | ω \ {s(u, v)} ∈ conn r s} :=
    fun _ _ h hω => conn_mono (sdiff_subset_sdiff_left h) hω
  have h1 := countable_profile_bk q (hdel x b) (isUpperSet_conn b u)
  have h2 := countable_profile_bk q
    (isUpperSet_disjointOccurrence (hdel x b) (isUpperSet_conn b u)) (isUpperSet_conn x u)
  have h3 := countable_profile_bk q
    (isUpperSet_disjointOccurrence
      (isUpperSet_disjointOccurrence (hdel x b) (isUpperSet_conn b u))
      (isUpperSet_conn x u)) (hdel b a)
  refine h3.trans ((mul_le_mul' (h2.trans (mul_le_mul' h1 le_rfl)) le_rfl).trans_eq ?_)
  change ((_ * tau q b u) * tau q x u) * _ = _
  ac_rfl

/-- An independent cap keeps the original double connection after deletion.
Taking the minimum can improve the four-arm diagram, for example on a tree. -/
theorem law_doubleConn_inter_deleted_le_min [Countable V]
    (q : Sym2 V → unitInterval) (x u v a : V) :
    law q (doubleConn x u ∩ {ω : Config V | ω \ {s(u, v)} ∈ conn x a}) ≤
      min (tau q x u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn x u})
        (∑' b, tau q x u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn x b} *
          tau q b u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn b a}) := by
  exact le_min ((measure_mono inter_subset_left).trans
    (law_doubleConn_le_tau_mul_deleted q x u s(u, v)))
    (law_doubleConn_inter_deleted_le_endpoint q x u v a)

/-- If the starting point belongs to the required set, every pivotal would be
an earlier cutting pair. Thus the surviving event is exactly double connection. -/
theorem laceEPrime_eq_doubleConn_of_left_mem {A : Set V} {x : V} (hx : x ∈ A) (y : V) :
    laceEPrime A x y = doubleConn x y := by
  rw [← laceEPrime_univ]
  simp only [laceEPrime, throughSet_eq_conn_of_left_mem hx, throughSet_univ]

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

/-- Contact at the starting point of the next layer supplies a full double
connection. If that point is outside the deleted cluster, the contact differs
from it. This retains the no-earlier-pivotal condition in the first diagram. -/
theorem coefficientEvent_one_subset_iUnion_refined (x y : V) (b : Fin 1 → V × V) :
    coefficientEvent x y b ⊆ ⋃ a : V,
      {ω : Fin 2 → Config V |
        ω 0 ∈ doubleConn x (b 0).1 ∩
          {η : Config V | η \ {s((b 0).1, (b 0).2)} ∈ conn x a} ∧
        ω 1 ∈ if a = (b 0).2 then doubleConn (b 0).2 y
          else disjointOccurrence (conn (b 0).2 a) (conn a y)} := by
  intro ω h
  obtain ⟨h0, h1⟩ := (mem_coefficientEvent_one_iff x y b ω).mp h
  by_cases hv : (b 0).2 ∈ cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x
  · refine mem_iUnion.mpr ⟨(b 0).2, ⟨h0, hv⟩, ?_⟩
    rw [ite_eq_left rfl, ← laceEPrime_eq_doubleConn_of_left_mem hv y]
    exact h1
  · have ht := throughSet_subset_iUnion_disjointOccurrence
      (cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x) (b 0).2 y
      (laceEPrime_subset_throughSet _ _ _ h1)
    obtain ⟨a, ha⟩ := mem_iUnion.mp ht
    have hne : (a : V) ≠ (b 0).2 := by
      intro h
      exact hv ((congrArg (fun z : V =>
        z ∈ cluster (ω 0 \ {s((b 0).1, (b 0).2)}) x) h).mp a.property)
    exact mem_iUnion.mpr ⟨a, ⟨h0, a.property⟩, by simpa only [ite_eq_right hne] using ha⟩

/-- A sharper first-event diagram combines three gains: the exact initial
diagonal, two deleted branch arms with an independent double-connection cap,
and a deleted double-connection bound when contact is at the next root. -/
theorem coefficientEvent_one_probability_le_refined_diagram [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (b : Fin 1 → V × V) :
    (Measure.pi (fun _ : Fin 2 => law q)) (coefficientEvent x y b) ≤
      ∑' a,
        (if x = (b 0).1 then
          law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn x a}
        else min (tau q x (b 0).1 *
            law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn x (b 0).1})
          (∑' z, tau q x (b 0).1 *
            law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn x z} *
            tau q z (b 0).1 *
            law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn z a})) *
        (if a = (b 0).2 then tau q (b 0).2 y *
          law q {ω : Config V | ω \ {s((b 0).1, (b 0).2)} ∈ conn (b 0).2 y}
        else tau q (b 0).2 a * tau q a y) := by
  refine (measure_mono (coefficientEvent_one_subset_iUnion_refined x y b)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun a => ?_))
  rw [measure_pi_two_rect]
  apply mul_le_mul'
  · by_cases h : x = (b 0).1
    · rw [ite_eq_left h]
      simpa only [← h] using
        (law_doubleConn_inter_deleted_self q x a s(x, (b 0).2)).le
    · simpa only [ite_eq_right h] using
        law_doubleConn_inter_deleted_le_min q x (b 0).1 (b 0).2 a
  · by_cases h : a = (b 0).2
    · simpa only [ite_eq_left h] using
        law_doubleConn_le_tau_mul_deleted q (b 0).2 y s((b 0).1, (b 0).2)
    · simp only [ite_eq_right h]
      exact countable_profile_bk q (isUpperSet_conn (b 0).2 a) (isUpperSet_conn a y)

/-- The first positive lace coefficient with the retained endpoint and deleted
bond gains. All terms are explicit two-point probabilities and their one-bond
deletions; loop weights vanish by the canonical off-diagonal kernel. -/
theorem laceCoefficient_one_le_refined_diagram [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    laceCoefficient q 1 x y ≤ ∑' u, ∑' v,
      offDiagonal (fun r t : V => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) u v *
        ∑' a,
          (if x = u then law q {ω : Config V | ω \ {s(u, v)} ∈ conn x a}
          else min (tau q x u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn x u})
            (∑' z, tau q x u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn x z} *
              tau q z u * law q {ω : Config V | ω \ {s(u, v)} ∈ conn z a})) *
          (if a = v then tau q v y * law q {ω : Config V | ω \ {s(u, v)} ∈ conn v y}
          else tau q v a * tau q a y) := by
  let F : V × V → ℝ≥0∞ := fun uv =>
    offDiagonal (fun r t : V => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) uv.1 uv.2 *
      ∑' a,
        (if x = uv.1 then law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn x a}
        else min (tau q x uv.1 * law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn x uv.1})
          (∑' z, tau q x uv.1 * law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn x z} *
            tau q z uv.1 * law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn z a})) *
        (if a = uv.2 then tau q uv.2 y *
          law q {ω : Config V | ω \ {s(uv.1, uv.2)} ∈ conn uv.2 y}
        else tau q uv.2 a * tau q a y)
  calc
    laceCoefficient q 1 x y ≤ ∑' b : Fin 1 → V × V, F (b 0) := by
      unfold laceCoefficient
      apply ENNReal.tsum_le_tsum
      intro b
      change (∏ i : Fin 1,
        offDiagonal (fun r t : V => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞))
          (b i).1 (b i).2) * _ ≤ _
      rw [Fin.prod_univ_one]
      exact mul_le_mul' le_rfl (coefficientEvent_one_probability_le_refined_diagram q x y b)
    _ = ∑' uv : V × V, F uv := (Equiv.funUnique (Fin 1) (V × V)).tsum_eq F
    _ = ∑' u, ∑' v, F (u, v) := ENNReal.tsum_prod'

/-- Deleting the sole off-diagonal pair leaves only reflexive connections. -/
theorem bool_deleted_conn (ω : Config Bool) (x y : Bool) :
    ω \ {s(false, true)} ∈ conn x y ↔ x = y := by
  have hG : openGraph (ω \ {s(false, true)}) = ⊥ := by
    ext a b
    cases a <;> cases b <;> simp [openGraph_adj_iff, Sym2.eq_swap]
  rw [mem_conn_iff, hG, SimpleGraph.reachable_bot]

/-- The deleted two-point function on two vertices is the diagonal indicator. -/
theorem law_bool_deleted (q : Sym2 Bool → unitInterval) (x y : Bool) :
    law q {ω : Config Bool | ω \ {s(false, true)} ∈ conn x y} =
      if x = y then 1 else 0 := by
  simp_rw [bool_deleted_conn]
  by_cases h : x = y <;> simp [h]

private theorem bool_conn_cross_eq_mem :
    (conn false true : Set (Config Bool)) = {ω | s(false, true) ∈ ω} := by
  ext ω
  constructor
  · rintro ⟨r⟩
    cases r with
    | @cons a b c hab r =>
      cases b
      · exact ((openGraph_adj_iff ω false false).mp hab).2 rfl |>.elim
      · exact ((openGraph_adj_iff ω false true).mp hab).1
  · exact mem_conn_of_mem (by decide)

/-- The off-diagonal two-point function on two vertices is the bond probability. -/
theorem tau_bool_cross (q : Sym2 Bool → unitInterval) :
    tau q false true = (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) := by
  rw [tau, bool_conn_cross_eq_mem]
  exact prodBernoulli_setOf_mem q _

/-- The first deleted cluster on two vertices is the singleton root. -/
theorem bool_deleted_cluster (ω : Config Bool) :
    cluster (ω \ {s(false, true)}) false = {false} := by
  ext a
  rw [mem_cluster_iff, bool_deleted_conn]
  simp only [mem_singleton_iff, eq_comm]

/-- On two vertices, reaching the other singleton admits no earlier cut. -/
theorem laceEPrime_singleton_bool :
    laceEPrime {false} true false = conn true false := by
  ext ω
  constructor
  · intro h
    exact throughSet_subset_conn _ _ _ h.1
  · intro hc
    refine ⟨?_, ?_⟩
    · rwa [throughSet_eq_conn_of_right_mem (mem_singleton false)]
    · intro h
      obtain ⟨u, v, hp, ht⟩ := by simpa only [mem_iUnion, mem_inter_iff] using h
      cases u
      · exact hp.2.1 hp.2.2.1
      · simp at ht

/-- On two vertices the refined diagram equals the square of the sole bond
probability. Diagonal profile values are arbitrary. -/
theorem first_refined_diagram_bool (q : Sym2 Bool → unitInterval) :
    (∑' u, ∑' v,
      offDiagonal (fun r t : Bool => (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) u v *
        ∑' a,
          (if false = u then law q {ω : Config Bool | ω \ {s(u, v)} ∈ conn false a}
          else min (tau q false u * law q {ω : Config Bool | ω \ {s(u, v)} ∈ conn false u})
            (∑' z, tau q false u * law q {ω : Config Bool | ω \ {s(u, v)} ∈ conn false z} *
              tau q z u * law q {ω : Config Bool | ω \ {s(u, v)} ∈ conn z a})) *
          (if a = v then tau q v false * law q {ω : Config Bool | ω \ {s(u, v)} ∈ conn v false}
          else tau q v a * tau q a false)) =
      (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)^2 := by
  have ht : tau q true false = (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) := by
    rw [tau_comm]
    exact tau_bool_cross q
  simp [tsum_fintype, offDiagonal, Sym2.eq_swap,
    law_bool_deleted, ht, tau_bool_cross, tau_self, pow_two]

/-- The first coefficient attains the refined diagram on two vertices.
For a positive bond probability this proves the universal prefactor one is
optimal, without an asymptotic or a restriction on diagonal profile values. -/
theorem laceCoefficient_one_bool (q : Sym2 Bool → unitInterval) :
    laceCoefficient q 1 false false =
      (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞)^2 := by
  apply le_antisymm
  · have ht : tau q true false = (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) := by
      rw [tau_comm]
      exact tau_bool_cross q
    simpa [tsum_fintype, offDiagonal, Sym2.eq_swap,
      law_bool_deleted, ht, tau_bool_cross, tau_self, pow_two] using
      laceCoefficient_one_le_refined_diagram q false false
  · let b₀ : Fin 1 → Bool × Bool := fun _ => (false, true)
    have hevent : coefficientEvent false false b₀ =
        {ω : Fin 2 → Config Bool | ω 0 ∈ (univ : Set (Config Bool)) ∧
          s(false, true) ∈ ω 1} := by
      ext ω
      rw [mem_coefficientEvent_one_iff]
      simp [b₀, bool_deleted_cluster, laceEPrime_singleton_bool,
        conn_symm true false, bool_conn_cross_eq_mem]
    have hprob : (Measure.pi (fun _ : Fin 2 => law q)) (coefficientEvent false false b₀) =
        (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) := by
      rw [hevent]
      change (Measure.pi (fun _ : Fin 2 => law q))
        {ω | ω 0 ∈ (univ : Set (Config Bool)) ∧
          ω 1 ∈ {η : Config Bool | s(false, true) ∈ η}} = _
      rw [measure_pi_two_rect, measure_univ, one_mul]
      exact prodBernoulli_setOf_mem q _
    have hle := ENNReal.le_tsum (f := fun b : Fin 1 → Bool × Bool =>
      (∏ i, offDiagonal (fun r t : Bool =>
        (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin 2 => law q)) (coefficientEvent false false b)) b₀
    have hw : (∏ i, offDiagonal (fun r t : Bool =>
        (unitInterval.toNNReal (q s(r, t)) : ℝ≥0∞)) (b₀ i).1 (b₀ i).2) =
        (unitInterval.toNNReal (q s(false, true)) : ℝ≥0∞) := by
      rw [Fin.prod_univ_one]
      simp [b₀, offDiagonal]
    rw [hw, hprob] at hle
    simpa only [laceCoefficient, pow_two] using hle

example : laceCoefficient (fun _ : Sym2 Bool => 1) 1 false false = 1 := by
  simp [laceCoefficient_one_bool]

end PercLib.Percolation.Bond.Lace
