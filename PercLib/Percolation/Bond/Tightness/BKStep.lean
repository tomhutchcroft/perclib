/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Source motivation: T. Hutchcroft, arXiv:2008.11197v2,
§2.1, proof of Theorem 2.3. No source text or code is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Tightness.FromBK
public import PercLib.Probability.CountableBK
public import PercLib.Combinatorics.TreeSplitting

/-! # The BK step for the largest cluster intersection

`tightnessBK : TightnessBK V` for every countable `V`, on the reading `k ≥ 1` (see
`Tightness/Defs.lean`; the definition in `Tightness/Defs.lean` is used unchanged), and the corollary
`universalTightness : UniversalTightness V`. Each conjunct of both statements is also a named lemma
(`law_three_pow_mul_le_maxClusterIntersection_le`, `law_three_pow_mul_le_clusterIntersection_le`,
`law_mul_tightnessScale_le_maxClusterIntersection_le`,
`law_maxClusterIntersection_lt_mul_tightnessScale_le`,
`law_mul_tightnessScale_le_clusterIntersection_le`); downstream code uses those.

On `{3^k λ ≤ |K_u ∩ Λ|}` take finitely many open edges carrying the cluster of `u`
on `Λ`, keep the non-loop edges reachable from `u`, and split them with
`exists_connected_split` into at least `3^(k-1) + 1` edge-disjoint connected pieces, each
with at least `λ` vertices of `Λ`. The piece through `u` witnesses `{λ ≤ |K_u ∩ Λ|}` and
the others witness `{λ ≤ max}`, so the event lies in an iterated disjoint occurrence and
the multi-event BK inequality `countable_profile_bk_foldl` applies. Disjoint occurrence
uses finite certificates, so no separate exhaustion step is needed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set SimpleGraph
open scoped ENNReal

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-! ### Monotonicity -/

theorem clusterIntersection_mono (Λ : Finset V) {ω ω' : Config V} (h : ω ⊆ ω') (u : V) :
    clusterIntersection Λ ω u ≤ clusterIntersection Λ ω' u :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ (cluster_mono h u))
    (Λ.finite_toSet.subset Set.inter_subset_right)

theorem clusterIntersection_le_max (Λ : Finset V) (ω : Config V) {v : V} (hv : v ∈ Λ) :
    clusterIntersection Λ ω v ≤ maxClusterIntersection Λ ω :=
  Finset.le_sup (f := fun v => (cluster ω v ∩ (Λ : Set V)).ncard) hv

theorem isUpperSet_real_le_clusterIntersection (Λ : Finset V) (u : V) (l : ℝ) :
    IsUpperSet {ω : Config V | l ≤ (clusterIntersection Λ ω u : ℝ)} :=
  fun _ _ h (hω : l ≤ _) => show l ≤ _ from le_trans hω
      (by exact_mod_cast clusterIntersection_mono Λ h u)

theorem isUpperSet_real_le_maxClusterIntersection (Λ : Finset V) (l : ℝ) :
    IsUpperSet {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)} :=
  fun _ _ h (hω : l ≤ _) => show l ≤ _ from le_trans hω
      (by exact_mod_cast maxClusterIntersection_mono Λ h)

/-! ### Iterated disjoint occurrence from disjoint finite witnesses -/

/-- Iterated disjoint occurrence is monotone in its first event. -/
theorem foldl_disjointOccurrence_mono_left {ι : Type*} (Bs : List (Set (Set ι)))
    {A A' : Set (Set ι)} (h : A ⊆ A') :
    Bs.foldl disjointOccurrence A ⊆ Bs.foldl disjointOccurrence A' := by
  induction Bs generalizing A A' with
  | nil => exact h
  | cons B Bs ih => exact ih (disjointOccurrence_mono h subset_rfl)

/-- If `ω` contains pairwise disjoint finite sets `F ∈ A` and `G i ∈ B` (`i < n`), with `A`
and `B` increasing, then `ω` lies in the `n`-fold iterated disjoint occurrence of `B`
after `A`. -/
theorem mem_foldl_replicate_disjointOccurrence {ι : Type*} {B : Set (Set ι)}
    (hB : IsUpperSet B) {ω : Set ι} (n : ℕ) {A : Set (Set ι)} (hA : IsUpperSet A)
    (F : Set ι) (G : Fin n → Set ι) (hFf : F.Finite) (hGf : ∀ i, (G i).Finite)
    (hFω : F ⊆ ω) (hGω : ∀ i, G i ⊆ ω) (hFA : F ∈ A) (hGB : ∀ i, G i ∈ B)
    (hFG : ∀ i, Disjoint F (G i)) (hGG : Pairwise fun i j => Disjoint (G i) (G j)) :
    ω ∈ (List.replicate n B).foldl disjointOccurrence A := by
  induction n generalizing A F with
  | zero => exact hA hFω hFA
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons]
    refine ih (isUpperSet_disjointOccurrence hA hB) (F ∪ G 0) (fun i => G i.succ)
      (hFf.union (hGf 0)) (fun i => hGf _) (Set.union_subset hFω (hGω 0)) (fun i => hGω _)
      ?_ (fun i => hGB _) (fun i => ?_) (fun i j hij => hGG (Fin.succ_injective _ |>.ne hij))
    · exact (mem_disjointOccurrence_iff_open hA hB _).2 ⟨F, G 0, hFf, hGf 0, hFG 0,
        Set.subset_union_left, Set.subset_union_right, hFA, hGB 0⟩
    · exact Set.disjoint_union_left.2 ⟨hFG _, hGG (Fin.succ_ne_zero i).symm⟩

/-! ### Graph bookkeeping -/

/-- Discarding loops does not change the graph of an edge set. -/
theorem fromEdgeSet_filter_not_isDiag [DecidablePred fun e : Sym2 V => ¬ e.IsDiag]
    (S : Finset (Sym2 V)) :
    fromEdgeSet ((S.filter fun e => ¬ e.IsDiag : Finset (Sym2 V)) : Set (Sym2 V)) =
      fromEdgeSet (S : Set (Sym2 V)) := by
  ext v w
  simp only [fromEdgeSet_adj, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe,
    Sym2.mk_isDiag_iff]
  tauto

/-- A vertex joined to a different vertex is an endpoint of a non-loop edge. -/
theorem exists_nondiag_mem_of_reachable_ne {S : Set (Sym2 V)} {a v : V}
    (h : (fromEdgeSet S).Reachable a v) (hne : a ≠ v) : ∃ e ∈ S, ¬ e.IsDiag ∧ a ∈ e := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h _ =>
    obtain ⟨h1, h2⟩ := (fromEdgeSet_adj _).1 h
    exact ⟨_, h1, by simpa using h2, Sym2.mem_mk_left _ _⟩

/-! ### The combinatorial step -/

/-- **The splitting step.** If `|K_u ∩ Λ| ≥ 3^k λ` with `k ≥ 1` and `λ ≥ 1`, then the
configuration lies in the iterated disjoint occurrence of `3^(k-1)` copies of
`{λ ≤ max}` after `{λ ≤ |K_u ∩ Λ|}`. -/
theorem mem_foldl_of_three_pow_le_clusterIntersection (Λ : Finset V) (u : V) {l : ℝ}
    (hl : 1 ≤ l) {k : ℕ} (hk : 1 ≤ k) {ω : Config V}
    (hω : (3 : ℝ) ^ k * l ≤ (clusterIntersection Λ ω u : ℝ)) :
    ω ∈ (List.replicate (3 ^ (k - 1))
        {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)}).foldl disjointOccurrence
      {ω : Config V | l ≤ (clusterIntersection Λ ω u : ℝ)} := by
  classical
  set N := clusterIntersection Λ ω u with hNdef
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have h3kN : (3 : ℝ) ^ k ≤ N := le_trans (le_mul_of_one_le_right h3k.le hl) hω
  -- a finite open edge set carrying the cluster of `u` on `Λ`
  obtain ⟨F, hFω, hFN⟩ := exists_finset_of_cluster_tail (ω := ω) u Λ N le_rfl
  set E' : Finset (Sym2 V) :=
    F.filter (fun e => ∃ w ∈ e, (fromEdgeSet (F : Set (Sym2 V))).Reachable u w) with hE'
  set E : Finset (Sym2 V) := E'.filter (fun e => ¬ e.IsDiag) with hE
  have hEF : E ⊆ F := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hreach : ∀ x, (∃ e ∈ E, x ∈ e) → (fromEdgeSet (E : Set (Sym2 V))).Reachable u x := by
    rintro x ⟨e, he, hxe⟩
    rw [hE, fromEdgeSet_filter_not_isDiag]
    exact reachable_filter_reachable F u ⟨e, Finset.mem_of_mem_filter _ he, hxe⟩
  have hconn : ∀ x y, (∃ e ∈ E, x ∈ e) → (∃ e ∈ E, y ∈ e) →
      (fromEdgeSet (E : Set (Sym2 V))).Reachable x y :=
    fun x y hx hy => (hreach x hx).symm.trans (hreach y hy)
  have hdiag : ∀ e ∈ E, ¬ e.IsDiag := fun e he => (Finset.mem_filter.1 he).2
  -- the marked vertices
  set A : Finset V := Λ.filter (· ∈ cluster (F : Config V) u) with hAdef
  have hAcard : N ≤ A.card := by
    have hAset : ((A : Set V)) = cluster (F : Config V) u ∩ (Λ : Set V) := by
      ext a; simp [hAdef, and_comm]
    rw [← Set.ncard_coe_finset, hAset]
    exact hFN
  have hNA : (3 : ℝ) ^ k ≤ (A.card : ℝ) := h3kN.trans (by exact_mod_cast hAcard)
  have hNA' : 3 ^ k ≤ A.card := by exact_mod_cast hNA
  -- an endpoint condition for vertices of the cluster of `u` in `F`
  have hend : ∀ a, a ∈ cluster (F : Config V) u → a ≠ u → ∃ e ∈ E, a ∈ e := by
    intro a ha hau
    have ha' : (fromEdgeSet (F : Set (Sym2 V))).Reachable u a := ha
    obtain ⟨e, heF, hed, hae⟩ := exists_nondiag_mem_of_reachable_ne ha'.symm hau
    exact ⟨e, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨heF, a, hae, ha'⟩, hed⟩, hae⟩
  have huE : ∃ e ∈ E, u ∈ e := by
    have h1 : 1 < A.card := lt_of_lt_of_le (by
      have : 3 ≤ 3 ^ k := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega) hNA'
    obtain ⟨b, hbA, hbu⟩ := Finset.exists_mem_ne h1 u
    have hb : (fromEdgeSet (F : Set (Sym2 V))).Reachable u b := (Finset.mem_filter.1 hbA).2
    obtain ⟨e, heF, hed, hue⟩ := exists_nondiag_mem_of_reachable_ne hb hbu.symm
    exact ⟨e, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨heF, u, hue, Reachable.rfl⟩, hed⟩,
      hue⟩
  have hAE : ∀ a ∈ A, ∃ e ∈ E, a ∈ e := by
    intro a haA
    by_cases hau : a = u
    · exact hau ▸ huE
    · exact hend a (Finset.mem_filter.1 haA).2 hau
  -- split
  obtain ⟨C, hCcard, hCE, -, hCdisj, hCpiece, hCcov⟩ :=
    exists_connected_split E hdiag hconn A hAE k hk hNA'
  -- each piece carries at least `λ` marked vertices
  have hlP : ∀ P ∈ C, l ≤ ((A.filter fun a => ∃ e ∈ P, a ∈ e).card : ℝ) := by
    intro P hP
    refine le_trans ?_ (hCpiece P hP).2.2.1
    rw [le_div_iff₀ h3k]
    calc l * 3 ^ k = 3 ^ k * l := mul_comm _ _
      _ ≤ N := hω
      _ ≤ A.card := by exact_mod_cast hAcard
  -- the marked vertices of a connected piece lie in one cluster of the piece
  have hcount : ∀ P ∈ C, ∀ x, (∃ e ∈ P, x ∈ e) →
      (A.filter fun a => ∃ e ∈ P, a ∈ e).card ≤ clusterIntersection Λ (P : Config V) x := by
    intro P hP x hx
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard (fun a ha => ?_) (Λ.finite_toSet.subset Set.inter_subset_right)
    obtain ⟨haA, hae⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
    exact ⟨(hCpiece P hP).2.1 x a hx hae, (Finset.mem_filter.1 haA).1⟩
  have hFin : ∀ P ∈ C, (P : Config V) ⊆ ω := fun P hP =>
    (Finset.coe_subset.2 ((hCE P hP).trans hEF)).trans hFω
  -- the piece through `u`
  obtain ⟨Pu, hPu, huPu⟩ := hCcov u huE
  have hPuB : (Pu : Config V) ∈ {ω : Config V | l ≤ (clusterIntersection Λ ω u : ℝ)} :=
    (hlP Pu hPu).trans (by exact_mod_cast hcount Pu hPu u huPu)
  have hPmax : ∀ P ∈ C,
      (P : Config V) ∈ {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)} := by
    intro P hP
    have hpos : 0 < (A.filter fun a => ∃ e ∈ P, a ∈ e).card := by
      have := (hlP P hP)
      exact_mod_cast lt_of_lt_of_le zero_lt_one (hl.trans this)
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
    obtain ⟨haA, hae⟩ := Finset.mem_filter.1 ha
    refine (hlP P hP).trans ?_
    exact_mod_cast (hcount P hP a hae).trans
      (clusterIntersection_le_max Λ _ (Finset.mem_filter.1 haA).1)
  -- choose `3^(k-1)` other pieces
  obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (s := C.erase Pu)
    (n := 3 ^ (k - 1)) (by rw [Finset.card_erase_of_mem hPu]; omega)
  set G : Fin (3 ^ (k - 1)) → Finset (Sym2 V) :=
    fun i => (D.equivFin.symm (Fin.cast hDcard.symm i) : Finset (Sym2 V)) with hG
  have hGD : ∀ i, G i ∈ D := fun i => (D.equivFin.symm _).2
  have hGC : ∀ i, G i ∈ C.erase Pu := fun i => hDC (hGD i)
  refine mem_foldl_replicate_disjointOccurrence
    (isUpperSet_real_le_maxClusterIntersection Λ l) _
    (isUpperSet_real_le_clusterIntersection Λ u l) (Pu : Set (Sym2 V))
    (fun i => (G i : Set (Sym2 V))) (Finset.finite_toSet _) (fun i => Finset.finite_toSet _)
    (hFin Pu hPu) (fun i => hFin _ (Finset.mem_of_mem_erase (hGC i))) hPuB
    (fun i => hPmax _ (Finset.mem_of_mem_erase (hGC i))) (fun i => ?_) (fun i j hij => ?_)
  · have h := Finset.mem_erase.1 (hGC i)
    exact Finset.disjoint_coe.2 (hCdisj hPu h.2 (Ne.symm h.1))
  · have hne : G i ≠ G j := by
      intro h
      have h' := Subtype.ext h
      exact hij (Fin.cast_injective _ (D.equivFin.symm.injective h'))
    exact Finset.disjoint_coe.2
      (hCdisj (Finset.mem_of_mem_erase (hGC i)) (Finset.mem_of_mem_erase (hGC j)) hne)

/-! ### The BK step -/

/-- The multi-event BK inequality for `3^(k-1)` copies of `{λ ≤ max}` and one upper set. -/
private theorem law_foldl_replicate_le [Countable V] (q : Sym2 V → unitInterval)
    (Λ : Finset V) (l : ℝ) (n : ℕ) {B : Set (Config V)} (hB : IsUpperSet B) :
    law q ((List.replicate n {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)}).foldl
        disjointOccurrence B) ≤
      law q B * law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ n := by
  have h := countable_profile_bk_foldl q
    (List.replicate n {ω : Config V | l ≤ (maxClusterIntersection Λ ω : ℝ)})
    (fun C hC => (List.eq_of_mem_replicate hC) ▸
      isUpperSet_real_le_maxClusterIntersection Λ l) hB
  rwa [List.map_replicate, List.prod_replicate] at h

/-- **The BK step for the largest intersection** (Hutchcroft, arXiv:2008.11197v2,
Theorem 2.3, first bound, reading `k ≥ 1`):
`P(max ≥ 3^k λ) ≤ P(max ≥ λ)^(3^(k-1) + 1)` for `λ ≥ 1` and `k ≥ 1`. -/
theorem law_three_pow_mul_le_maxClusterIntersection_le [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {l : ℝ} (hl : 1 ≤ l)
    {k : ℕ} (hk : 1 ≤ k) :
    law q {ω | (3 : ℝ) ^ k * l ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
      law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ (3 ^ (k - 1) + 1) := by
  refine le_trans (measure_mono ?_) ((law_foldl_replicate_le q Λ l (3 ^ (k - 1))
    (isUpperSet_real_le_maxClusterIntersection Λ l)).trans_eq (pow_succ' _ _).symm)
  intro ω hω
  obtain ⟨v, hvΛ, hv⟩ := Finset.exists_mem_eq_sup Λ hΛ
    (fun v => (cluster ω v ∩ (Λ : Set V)).ncard)
  have hω' : (3 : ℝ) ^ k * l ≤ (clusterIntersection Λ ω v : ℝ) := by
    have : maxClusterIntersection Λ ω = clusterIntersection Λ ω v := hv
    rw [← this]; exact hω
  refine foldl_disjointOccurrence_mono_left _ (fun η hη => ?_)
    (mem_foldl_of_three_pow_le_clusterIntersection Λ v hl hk hω')
  exact show l ≤ _ from le_trans (show l ≤ (clusterIntersection Λ η v : ℝ) from hη)
    (by exact_mod_cast clusterIntersection_le_max Λ η hvΛ)

/-- **The BK step for one cluster** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.3, second
bound, reading `k ≥ 1`):
`P(|K_u ∩ Λ| ≥ 3^k λ) ≤ P(max ≥ λ)^(3^(k-1)) · P(|K_u ∩ Λ| ≥ λ)` for `λ ≥ 1`, `k ≥ 1`. -/
theorem law_three_pow_mul_le_clusterIntersection_le [Countable V]
    (q : Sym2 V → unitInterval) (Λ : Finset V) (u : V) {l : ℝ} (hl : 1 ≤ l)
    {k : ℕ} (hk : 1 ≤ k) :
    law q {ω | (3 : ℝ) ^ k * l ≤ (clusterIntersection Λ ω u : ℝ)} ≤
      law q {ω | l ≤ (maxClusterIntersection Λ ω : ℝ)} ^ (3 ^ (k - 1)) *
        law q {ω | l ≤ (clusterIntersection Λ ω u : ℝ)} := by
  refine le_trans (measure_mono fun ω hω =>
    mem_foldl_of_three_pow_le_clusterIntersection Λ u hl hk hω) ?_
  rw [mul_comm]
  exact law_foldl_replicate_le q Λ l _ (isUpperSet_real_le_clusterIntersection Λ u l)

/-- **The BK step** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.3, reading `k ≥ 1`) for every
countable vertex type and every profile. -/
@[tag "JGZB"]
theorem tightnessBK (V : Type*) [Countable V] : TightnessBK V := fun q Λ hΛ _l hl _k hk =>
  ⟨law_three_pow_mul_le_maxClusterIntersection_le q hΛ hl hk,
    fun u => law_three_pow_mul_le_clusterIntersection_le q Λ u hl hk⟩

/-! ### Universal tightness -/

/-- **The upper tail** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.2, first bound):
`P(max ≥ a M) ≤ exp(-a/9)` for `a ≥ 1`, where `M = tightnessScale q Λ`. -/
theorem law_mul_tightnessScale_le_maxClusterIntersection_le [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {a : ℝ} (ha : 1 ≤ a) :
    law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (maxClusterIntersection Λ ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-a / 9)) :=
  law_mul_tightnessScale_le_maxClusterIntersection_le_of_bk q hΛ
    (fun _l hl _k hk => law_three_pow_mul_le_maxClusterIntersection_le q hΛ hl hk) ha

/-- **The lower tail** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.2, second bound):
`P(max < ε M) ≤ 27 ε` for `0 < ε ≤ 1`, where `M = tightnessScale q Λ`. -/
theorem law_maxClusterIntersection_lt_mul_tightnessScale_le [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    law q {ω | (maxClusterIntersection Λ ω : ℝ) < ε * (tightnessScale q Λ : ℝ)} ≤
      ENNReal.ofReal (27 * ε) :=
  law_maxClusterIntersection_lt_mul_tightnessScale_le_of_bk q hΛ
    (fun _l hl _k hk => law_three_pow_mul_le_maxClusterIntersection_le q hΛ hl hk) hε hε1

/-- **The rooted tail** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.2, third bound):
`P(|K_u ∩ Λ| ≥ a M) ≤ e · P(|K_u ∩ Λ| ≥ M) · exp(-a/9)` for `a ≥ 1`, where
`M = tightnessScale q Λ`. -/
theorem law_mul_tightnessScale_le_clusterIntersection_le [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {a : ℝ}
    (ha : 1 ≤ a) :
    law q {ω | a * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} ≤
      ENNReal.ofReal (Real.exp 1) *
        law q {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} *
        ENNReal.ofReal (Real.exp (-a / 9)) :=
  law_mul_tightnessScale_le_clusterIntersection_le_of_bk q hΛ u
    (fun _l hl _k hk => law_three_pow_mul_le_clusterIntersection_le q Λ u hl hk) ha

/-- **Universal tightness** (Hutchcroft, arXiv:2008.11197v2, Theorem 2.2) for every
countable vertex type and every profile. -/
@[tag "C5Q9"]
theorem universalTightness (V : Type*) [Countable V] : UniversalTightness V := fun q _Λ hΛ =>
  ⟨fun _a ha => law_mul_tightnessScale_le_maxClusterIntersection_le q hΛ ha,
    fun _ε hε hε1 => law_maxClusterIntersection_lt_mul_tightnessScale_le q hΛ hε hε1,
    fun u _a ha => law_mul_tightnessScale_le_clusterIntersection_le q hΛ u ha⟩

/-! ### Non-vacuity -/

example : TightnessBK Unit := tightnessBK Unit

example : TightnessBK Bool := tightnessBK Bool

/-- `Fin 3`, `Λ = univ`, `k = 1`, `λ = 1`, any profile. -/
example (q : Sym2 (Fin 3) → unitInterval) :
    law q {ω | (3 : ℝ) ^ 1 * 1 ≤ (maxClusterIntersection Finset.univ ω : ℝ)} ≤
      law q {ω | (1 : ℝ) ≤ (maxClusterIntersection Finset.univ ω : ℝ)} ^ (3 ^ (1 - 1) + 1) :=
  (tightnessBK (Fin 3) q Finset.univ Finset.univ_nonempty 1 le_rfl 1 le_rfl).1

end PercLib.Percolation.Bond
