/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original transport proofs for the canonical lace events, coefficients, and
remainders; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.FirstPivotal
public import PercLib.Percolation.Bond.Lace.Remainder.Remainder
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.Transport.Reindexing
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Equivariance of the canonical lace coefficients

## Main results

Vertex bijections transport every event in the independent-layer definitions.
When the bond profile is preserved, the product measures and directed-bond
weights are preserved as well. Coefficient and remainder invariance therefore
follow from their definitions, without additional invariance assumptions.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V W : Type*}

theorem image_sym2Map_sdiff_singleton (e : V ≃ W) (ω : Config V) (u v : V) :
    Sym2.map e '' (ω \ {s(u, v)}) = (Sym2.map e '' ω) \ {s(e u, e v)} := by
  classical
  rw [Set.image_sdiff (Sym2.map.injective e.injective), Set.image_singleton, Sym2.map_mk]

theorem image_sym2Map_insert (e : V ≃ W) (ω : Config V) (u v : V) :
    Sym2.map e '' insert s(u, v) ω = insert s(e u, e v) (Sym2.map e '' ω) := by
  classical
  rw [Set.image_insert_eq, Sym2.map_mk]

/-- Induced-domain connections are carried along a vertex equivalence. -/
theorem image_localConn_iff (e : V ≃ W) (ω : Config V) (S : Set V) (x y : S) :
    ((openGraph (Sym2.map e '' ω)).induce (e '' S)).Reachable
      ⟨e x, mem_image_of_mem e x.property⟩ ⟨e y, mem_image_of_mem e y.property⟩ ↔
      ((openGraph ω).induce S).Reachable x y := by
  classical
  let φ : openGraph ω ≃g openGraph (Sym2.map e '' ω) :=
    ⟨e, fun {a b} => openGraph_image_adj_iff e ω a b⟩
  let ψ := φ.induce (show Set.BijOn φ S (e '' S) from e.bijOn_image)
  exact SimpleGraph.Iso.reachable_iff (φ := ψ) (u := x) (v := y)

/-- Transport also preserves the endpoint membership conditions of an
induced-domain connection. -/
theorem image_conn_in_set_iff (e : V ≃ W) (ω : Config V) (S : Set V) (x y : V) :
    (∃ hx : e x ∈ e '' S, ∃ hy : e y ∈ e '' S,
      ((openGraph (Sym2.map e '' ω)).induce (e '' S)).Reachable ⟨e x, hx⟩ ⟨e y, hy⟩) ↔
      ∃ hx : x ∈ S, ∃ hy : y ∈ S,
        ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  constructor
  · rintro ⟨hx, hy, h⟩
    have hx' : x ∈ S := e.injective.mem_set_image.mp hx
    have hy' : y ∈ S := e.injective.mem_set_image.mp hy
    exact ⟨hx', hy', (image_localConn_iff e ω S ⟨x, hx'⟩ ⟨y, hy'⟩).mp h⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨mem_image_of_mem e hx, mem_image_of_mem e hy,
      (image_localConn_iff e ω S ⟨x, hx⟩ ⟨y, hy⟩).mpr h⟩

theorem image_mem_throughSet_iff (e : V ≃ W) (ω : Config V) (A : Set V) (x y : V) :
    Sym2.map e '' ω ∈ throughSet (e '' A) (e x) (e y) ↔ ω ∈ throughSet A x y := by
  classical
  rw [mem_throughSet_iff, mem_throughSet_iff]
  refine and_congr (image_mem_conn_iff e ω x y) (not_congr ?_)
  rw [← e.image_compl A]
  exact image_conn_in_set_iff e ω Aᶜ x y

theorem image_mem_orientedPivotal_iff (e : V ≃ W) (ω : Config V) (x y u v : V) :
    Sym2.map e '' ω ∈ orientedPivotal (e x) (e y) (e u) (e v) ↔
      ω ∈ orientedPivotal x y u v := by
  classical
  simp only [orientedPivotal, mem_ofPred_eq, ← image_sym2Map_insert,
    ← image_sym2Map_sdiff_singleton, image_mem_conn_iff]

theorem image_mem_laceEPrime_iff (e : V ≃ W) (ω : Config V) (A : Set V) (x y : V) :
    Sym2.map e '' ω ∈ laceEPrime (e '' A) (e x) (e y) ↔ ω ∈ laceEPrime A x y := by
  classical
  simp only [laceEPrime, mem_sdiff, mem_iUnion, mem_inter_iff]
  refine and_congr (image_mem_throughSet_iff e ω A x y) (not_congr ?_)
  constructor
  · rintro ⟨u, v, hp, ht⟩
    refine ⟨e.symm u, e.symm v, ?_, ?_⟩
    · exact (image_mem_orientedPivotal_iff e ω x y (e.symm u) (e.symm v)).mp
        (by simpa only [e.apply_symm_apply] using hp)
    · exact (image_mem_throughSet_iff e ω A x (e.symm u)).mp
        (by simpa only [e.apply_symm_apply] using ht)
  · rintro ⟨u, v, hp, ht⟩
    exact ⟨e u, e v, (image_mem_orientedPivotal_iff e ω x y u v).mpr hp,
      (image_mem_throughSet_iff e ω A x u).mpr ht⟩

theorem image_mem_doubleConn_iff (e : V ≃ W) (ω : Config V) (x y : V) :
    Sym2.map e '' ω ∈ doubleConn (e x) (e y) ↔ ω ∈ doubleConn x y := by
  classical
  simpa only [Set.image_univ_of_surjective e.surjective, laceEPrime_univ] using
    image_mem_laceEPrime_iff e ω univ x y

private theorem map_fin_cases {n : ℕ} (f : V → W) (x : V) (b : Fin n → V)
    (i : Fin (n + 1)) : Fin.cases (f x) (fun j => f (b j)) i = f (Fin.cases x b i) := by
  classical
  exact Fin.cases rfl (fun _ => rfl) i

private theorem map_fin_lastCases {n : ℕ} (f : V → W) (x : V) (b : Fin n → V)
    (i : Fin (n + 1)) : Fin.lastCases (f x) (fun j => f (b j)) i = f (Fin.lastCases x b i) := by
  classical
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
  · simp only [Fin.lastCases_castSucc]

/-- Relabelling each configuration and each directed pair preserves the
canonical positive coefficient event. -/
theorem image_mem_coefficientEvent_iff (e : V ≃ W) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (ω : Fin (n + 2) → Config V) :
    (fun i => Sym2.map e '' ω i) ∈
      coefficientEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2)) ↔
        ω ∈ coefficientEvent x y b := by
  classical
  change (_ ∧ ∀ i, _) ↔ (_ ∧ ∀ i, _)
  refine and_congr (image_mem_doubleConn_iff e (ω 0) x (b 0).1) (forall_congr' fun i => ?_)
  simp only [map_fin_cases, map_fin_lastCases, ← image_sym2Map_sdiff_singleton,
    cluster_image, image_mem_laceEPrime_iff]

/-- The terminal through-set test in the remainder transports along with all
earlier no-cutting tests. -/
theorem image_mem_remainderEvent_iff (e : V ≃ W) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) (ω : Fin (n + 2) → Config V) :
    (fun i => Sym2.map e '' ω i) ∈
      remainderEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2)) ↔
        ω ∈ remainderEvent x y b := by
  classical
  change (_ ∧ ∀ i, _) ↔ (_ ∧ ∀ i, _)
  refine and_congr (image_mem_doubleConn_iff e (ω 0) x (b 0).1) (forall_congr' fun i => ?_)
  split_ifs <;> simp only [map_fin_cases, map_fin_lastCases,
    ← image_sym2Map_sdiff_singleton, cluster_image,
    image_mem_throughSet_iff, image_mem_laceEPrime_iff]

/-- A profile-preserving vertex permutation preserves every finite family of
independent configurations. -/
theorem measurePreserving_laceLayers (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (m : ℕ) :
    MeasurePreserving (fun ω : Fin m → Config V => fun i => Sym2.map e '' ω i)
      (Measure.pi (fun _ : Fin m => law q)) (Measure.pi (fun _ : Fin m => law q)) :=
  measurePreserving_pi _ _ fun _ =>
    ⟨measurable_image_sym2Map e, prodBernoulli_map_image_sym2_invariant q e hq⟩

theorem law_doubleConn_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (x y : V) :
    law q (doubleConn (e x) (e y)) = law q (doubleConn x y) := by
  classical
  have hmap : (law q).map (fun ω => Sym2.map e '' ω) = law q :=
    prodBernoulli_map_image_sym2_invariant q e hq
  calc
    law q (doubleConn (e x) (e y)) =
        ((law q).map (fun ω => Sym2.map e '' ω)) (doubleConn (e x) (e y)) := by rw [hmap]
    _ = law q ((fun ω => Sym2.map e '' ω) ⁻¹' doubleConn (e x) (e y)) :=
      map_image_sym2Map_apply e (law q) _
    _ = law q (doubleConn x y) := by
      congr 1
      ext ω
      exact image_mem_doubleConn_iff e ω x y

theorem piZero_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (x y : V) :
    piZero q (e x) (e y) = piZero q x y := by
  classical
  simp only [piZero, e.injective.eq_iff, law_doubleConn_apply_equiv q e hq]

theorem coefficientEvent_probability_apply_equiv [Countable V]
    (q : Sym2 V → unitInterval) (e : V ≃ V) (hq : ∀ a, q (Sym2.map e a) = q a)
    {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q))
      (coefficientEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2))) =
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b) := by
  classical
  have hpre : (fun ω : Fin (n + 2) → Config V => fun i => Sym2.map e '' ω i) ⁻¹'
      coefficientEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2)) =
        coefficientEvent x y b := by
    ext ω
    exact image_mem_coefficientEvent_iff e x y b ω
  rw [← (measurePreserving_laceLayers q e hq (n + 2)).measure_preimage
    (measurableSet_coefficientEvent (e x) (e y) _).nullMeasurableSet, hpre]

theorem remainderEvent_probability_apply_equiv [Countable V]
    (q : Sym2 V → unitInterval) (e : V ≃ V) (hq : ∀ a, q (Sym2.map e a) = q a)
    {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q))
      (remainderEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2))) =
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (remainderEvent x y b) := by
  classical
  have hpre : (fun ω : Fin (n + 2) → Config V => fun i => Sym2.map e '' ω i) ⁻¹'
      remainderEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2)) =
        remainderEvent x y b := by
    ext ω
    exact image_mem_remainderEvent_iff e x y b ω
  rw [← (measurePreserving_laceLayers q e hq (n + 2)).measure_preimage
    (measurableSet_remainderEvent (e x) (e y) _).nullMeasurableSet, hpre]

theorem offDiagonal_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (u v : V) :
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) (e u) (e v) =
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v := by
  classical
  have hp : q s(e u, e v) = q s(u, v) := by simpa only [Sym2.map_mk] using hq s(u, v)
  simp only [offDiagonal_apply, e.injective.eq_iff, hp]

/-- Canonical lace coefficients are invariant under every profile-preserving
vertex permutation. The bond sequence is reindexed by the same permutation. -/
theorem laceCoefficient_apply_equiv [Countable V]
    (q : Sym2 V → unitInterval) (e : V ≃ V) (hq : ∀ a, q (Sym2.map e a) = q a)
    (n : ℕ) (x y : V) : laceCoefficient q n (e x) (e y) = laceCoefficient q n x y := by
  classical
  cases n with
  | zero => exact piZero_apply_equiv q e hq x y
  | succ n =>
    unfold laceCoefficient
    dsimp only
    let eb : (Fin (n + 1) → V × V) ≃ (Fin (n + 1) → V × V) :=
      Equiv.piCongrRight fun _ => Equiv.prodCongr e e
    rw [← eb.tsum_eq]
    apply tsum_congr
    intro b
    change (∏ i, offDiagonal (fun a c : V => (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞))
        (e (b i).1) (e (b i).2)) *
        (Measure.pi (fun _ : Fin (n + 2) => law q))
          (coefficientEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2))) = _
    simp only [offDiagonal_apply_equiv q e hq,
      coefficientEvent_probability_apply_equiv q e hq]

/-- The canonical nonnegative remainder has the same profile symmetries. -/
theorem laceRemainder_apply_equiv [Countable V]
    (q : Sym2 V → unitInterval) (e : V ≃ V) (hq : ∀ a, q (Sym2.map e a) = q a)
    (n : ℕ) (x y : V) : laceRemainder q n (e x) (e y) = laceRemainder q n x y := by
  classical
  unfold laceRemainder
  let eb : (Fin (n + 1) → V × V) ≃ (Fin (n + 1) → V × V) :=
    Equiv.piCongrRight fun _ => Equiv.prodCongr e e
  rw [← eb.tsum_eq]
  apply tsum_congr
  intro b
  change (∏ i, offDiagonal (fun a c : V => (unitInterval.toNNReal (q s(a, c)) : ℝ≥0∞))
      (e (b i).1) (e (b i).2)) *
      (Measure.pi (fun _ : Fin (n + 2) => law q))
        (remainderEvent (e x) (e y) (fun i => (e (b i).1, e (b i).2))) = _
  simp only [offDiagonal_apply_equiv q e hq, remainderEvent_probability_apply_equiv q e hq]

section Translation

variable {G : Type*} [AddGroup G] [Countable G]

theorem laceCoefficient_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (n : ℕ) (x y g : G) :
    laceCoefficient q n (x + g) (y + g) = laceCoefficient q n x y := by
  classical
  apply laceCoefficient_apply_equiv q (Equiv.addRight g)
  intro a
  induction a using Sym2.ind with
  | _ u v => exact hq u v g

theorem laceRemainder_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (n : ℕ) (x y g : G) :
    laceRemainder q n (x + g) (y + g) = laceRemainder q n x y := by
  classical
  apply laceRemainder_apply_equiv q (Equiv.addRight g)
  intro a
  induction a using Sym2.ind with
  | _ u v => exact hq u v g

/-- A translation-invariant coefficient is the canonical kernel rooted at zero. -/
theorem laceCoefficient_eq_rooted (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (n : ℕ) (x y : G) :
    laceCoefficient q n x y = laceCoefficient q n 0 (y - x) := by
  classical
  simpa only [add_neg_cancel, sub_eq_add_neg] using
    (laceCoefficient_add_right q hq n x y (-x)).symm

theorem laceRemainder_eq_rooted (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (n : ℕ) (x y : G) :
    laceRemainder q n x y = laceRemainder q n 0 (y - x) := by
  classical
  simpa only [add_neg_cancel, sub_eq_add_neg] using
    (laceRemainder_add_right q hq n x y (-x)).symm

end Translation

section Evenness

variable {G : Type*} [AddCommGroup G] [Countable G]

omit [Countable G] in
/-- For unordered bonds, translation invariance also implies reflection
invariance of the profile. -/
theorem profile_neg_eq_of_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (a : Sym2 G) :
    q (Sym2.map (Equiv.neg G) a) = q a := by
  classical
  induction a using Sym2.ind with
  | _ x y =>
    have h := hq (-x) (-y) (x + y)
    have hx : -x + (x + y) = y := by simp only [neg_add_cancel_left]
    have hy : -y + (x + y) = x := by rw [add_comm x y, neg_add_cancel_left]
    rw [hx, hy] at h
    change q s(-x, -y) = q s(x, y)
    exact h.symm.trans (congrArg q Sym2.eq_swap)

/-- The actual positive lace kernels are even; this is not an assumed
symmetry of an abstract coefficient sequence. -/
theorem laceCoefficient_neg (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (n : ℕ) (x : G) :
    laceCoefficient q n 0 (-x) = laceCoefficient q n 0 x := by
  classical
  simpa only [Equiv.neg_apply, neg_zero] using
    laceCoefficient_apply_equiv q (Equiv.neg G) (profile_neg_eq_of_add_right q hq) n 0 x

theorem laceRemainder_neg (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (n : ℕ) (x : G) :
    laceRemainder q n 0 (-x) = laceRemainder q n 0 x := by
  classical
  simpa only [Equiv.neg_apply, neg_zero] using
    laceRemainder_apply_equiv q (Equiv.neg G) (profile_neg_eq_of_add_right q hq) n 0 x

end Evenness

end PercLib.Percolation.Bond.Lace
