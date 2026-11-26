/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original proofs of the actual finite-layer coefficient bounds.
No diagram estimate is assumed as an input.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Prefix
public import PercLib.Percolation.Bond.Lace.Diagrams.Basic
public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedBounds
public import PercLib.Percolation.Bond.Lace.Diagrams.Contraction
public import PercLib.Percolation.Bond.Lace.InteriorDiagram
public import PercLib.Percolation.Bond.Lace.Remainder.Recurrence

/-! # From the actual coefficient events to the pair-state diagrams -/

@[expose] public section
noncomputable section
open Set MeasureTheory PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem law_four_le [Countable V] (q : Sym2 V → unitInterval)
    {A B C D : Set (Config V)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hC : IsUpperSet C) (hD : IsUpperSet D) {a b c d : ℝ≥0∞}
    (ha : law q A ≤ a) (hb : law q B ≤ b) (hc : law q C ≤ c) (hd : law q D ≤ d) :
    law q (disjointOccurrence (disjointOccurrence (disjointOccurrence A B) C) D) ≤
      a * b * c * d := by
  have h1 := (countable_profile_bk q hA hB).trans (mul_le_mul' ha hb)
  have h2 := (countable_profile_bk q (isUpperSet_disjointOccurrence hA hB) hC).trans
    (mul_le_mul' h1 hc)
  exact (countable_profile_bk q
    (isUpperSet_disjointOccurrence (isUpperSet_disjointOccurrence hA hB) hC) hD).trans
    (mul_le_mul' h2 hd)

private theorem law_interior_geometry_le [Countable V]
    (q : Sym2 V → unitInterval) (v u a z t w : V) (e : Sym2 V) :
    law q (disjointOccurrence
        (disjointOccurrence
          (disjointOccurrence (disjointOccurrence (conn t w) (conn w u))
            (disjointOccurrence (conn t z) (conn z u))) (conn v t))
        {ω : Config V | ω \ {e} ∈ conn w a} ∪
      (if w = t then ∅ else
        disjointOccurrence
          (disjointOccurrence
            (disjointOccurrence (disjointOccurrence (conn v w) (conn w t))
              (disjointOccurrence (conn t z) (conn z u))) (conn t u))
          {ω : Config V | ω \ {e} ∈ conn w a})) ≤
      ((tau q t w * tau q w u) * (tau q t z * tau q z u) * tau q v t +
        if w = t then 0 else
          (tau q v w * tau q w t) * (tau q t z * tau q z u) * tau q t u) *
        law q {ω : Config V | ω \ {e} ∈ conn w a} := by
  refine (measure_union_le _ _).trans ?_
  rw [add_mul]
  have hD : IsUpperSet {ω : Config V | ω \ {e} ∈ conn w a} :=
    fun _ _ h hω => conn_mono (sdiff_subset_sdiff_left h) hω
  apply add_le_add
  · exact law_four_le q
      (isUpperSet_disjointOccurrence (isUpperSet_conn t w) (isUpperSet_conn w u))
      (isUpperSet_disjointOccurrence (isUpperSet_conn t z) (isUpperSet_conn z u))
      (isUpperSet_conn v t) hD
      (countable_profile_bk q (isUpperSet_conn t w) (isUpperSet_conn w u))
      (countable_profile_bk q (isUpperSet_conn t z) (isUpperSet_conn z u)) le_rfl le_rfl
  · by_cases hwt : w = t
    · simp [hwt]
    · simp only [ite_eq_right hwt]
      exact law_four_le q
        (isUpperSet_disjointOccurrence (isUpperSet_conn v w) (isUpperSet_conn w t))
        (isUpperSet_disjointOccurrence (isUpperSet_conn t z) (isUpperSet_conn z u))
        (isUpperSet_conn t u) hD
        (countable_profile_bk q (isUpperSet_conn v w) (isUpperSet_conn w t))
        (countable_profile_bk q (isUpperSet_conn t z) (isUpperSet_conn z u)) le_rfl le_rfl

/-- The last marked prefix layer is bounded by independent product rectangles
obtained from the interior six-arm containment. -/
theorem markedPrefix_snoc_probability_le [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x : V)
    (b : Fin n → V × V) (d c : V × V) (a : V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q))
      (coefficientPrefixEvent x c.1 (n + 1) (Fin.snoc b d) ∩
        {ω | ω (Fin.last (n + 1)) \ {s(c.1, c.2)} ∈
          conn (Fin.cases x (fun j => ((Fin.snoc b d : Fin (n + 1) → V × V) j).2)
            (Fin.last (n + 1))) a}) ≤
      ∑' z, ∑' t, ∑' w,
        (Measure.pi (fun _ : Fin (n + 1) => law q))
          (coefficientPrefixEvent x d.1 n b ∩
            {ω | ω (Fin.last n) \ {s(d.1, d.2)} ∈
              conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z}) *
        ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
          if w = t then 0 else
            (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} := by
  let P : V → Set (Fin (n + 1) → Config V) := fun z =>
    coefficientPrefixEvent x d.1 n b ∩
      {ω | ω (Fin.last n) \ {s(d.1, d.2)} ∈
        conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z}
  let F : V → V → V → Set (Config V) := fun z t w =>
    disjointOccurrence
      (disjointOccurrence
        (disjointOccurrence (disjointOccurrence (conn t w) (conn w c.1))
          (disjointOccurrence (conn t z) (conn z c.1))) (conn d.2 t))
      {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} ∪
    (if w = t then ∅ else
      disjointOccurrence
        (disjointOccurrence
          (disjointOccurrence (disjointOccurrence (conn d.2 w) (conn w t))
            (disjointOccurrence (conn t z) (conn z c.1))) (conn t c.1))
        {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a})
  rw [measure_layers_eq_prod_snoc q (measurableSet_markedPrefix x (n + 1) (Fin.snoc b d) c a)]
  have hsub :
      {p : (Fin (n + 1) → Config V) × Config V |
        Fin.snoc p.1 p.2 ∈ coefficientPrefixEvent x c.1 (n + 1) (Fin.snoc b d) ∩
          {ω | ω (Fin.last (n + 1)) \ {s(c.1, c.2)} ∈
            conn (Fin.cases x (fun j => ((Fin.snoc b d : Fin (n + 1) → V × V) j).2)
              (Fin.last (n + 1))) a}} ⊆ ⋃ z, ⋃ t, ⋃ w, P z ×ˢ F z t w := by
    intro p hp
    obtain ⟨hpre, hinter⟩ := (mem_markedPrefix_snoc_iff x b d c a p.1 p.2).mp hp
    have hg : p.2 ∈ ⋃ z : cluster (p.1 (Fin.last n) \ {s(d.1, d.2)})
        (Fin.cases x (fun j => (b j).2) (Fin.last n)), ⋃ t, ⋃ w, F z t w := by
      generalize (cluster (p.1 (Fin.last n) \ {s(d.1, d.2)})
        (Fin.cases x (fun j => (b j).2) (Fin.last n)) : Set V) = A at hinter ⊢
      exact @laceEPrime_inter_deleted_subset_iUnion_interior V
        A d.2 c.1 a s(c.1, c.2) p.2 hinter
    obtain ⟨z, hz⟩ := mem_iUnion.mp hg
    obtain ⟨t, ht⟩ := mem_iUnion.mp hz
    obtain ⟨w, hw⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨t,
      mem_iUnion.mpr ⟨w, ⟨hpre, z.property⟩, hw⟩⟩⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans
    (ENNReal.tsum_le_tsum fun z => (measure_iUnion_le _).trans
      (ENNReal.tsum_le_tsum fun t => (measure_iUnion_le _).trans
        (ENNReal.tsum_le_tsum fun w => ?_))))
  rw [Measure.prod_prod]
  simpa only [mul_assoc] using
    mul_le_mul' (le_refl ((Measure.pi (fun _ : Fin (n + 1) => law q)) (P z)))
      (law_interior_geometry_le q d.2 c.1 a z t w s(c.1, c.2))

/-- Summing the interior rectangles over the earlier bond sequence gives an
actual recurrence bound for marked coefficient prefixes. -/
theorem markedCoefficient_succ_le_six_arms [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V) (c : V × V) (a : V) :
    markedCoefficient q (n + 1) x c a ≤
      ∑' d : V × V, ∑' z, ∑' t, ∑' w,
        markedCoefficient q n x d z *
          offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) d.1 d.2 *
        ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
          if w = t then 0 else
            (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
  let W : (Fin n → V × V) → ℝ≥0∞ := fun b => ∏ i, J (b i).1 (b i).2
  let M : (Fin n → V × V) → (V × V) → V → ℝ≥0∞ := fun b d z =>
    (Measure.pi (fun _ : Fin (n + 1) => law q))
      (coefficientPrefixEvent x d.1 n b ∩
        {ω | ω (Fin.last n) \ {s(d.1, d.2)} ∈
          conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z})
  let T : (V × V) → V → V → V → ℝ≥0∞ := fun d z t w =>
    ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
      if w = t then 0 else
        (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1) *
      law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a}
  have hsplit : markedCoefficient q (n + 1) x c a =
      ∑' d : V × V, ∑' b : Fin n → V × V,
        W b * J d.1 d.2 * (Measure.pi (fun _ : Fin (n + 2) => law q))
          (coefficientPrefixEvent x c.1 (n + 1) (Fin.snoc b d) ∩
            {ω | ω (Fin.last (n + 1)) \ {s(c.1, c.2)} ∈
              conn (Fin.cases x (fun j => ((Fin.snoc b d : Fin (n + 1) → V × V) j).2)
                (Fin.last (n + 1))) a}) := by
    unfold markedCoefficient
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => V × V)).tsum_eq,
      ENNReal.tsum_prod']
    apply tsum_congr
    intro d
    apply tsum_congr
    intro b
    change (∏ i, J ((Fin.snoc b d : Fin (n + 1) → V × V) i).1
      ((Fin.snoc b d : Fin (n + 1) → V × V) i).2) * _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.snocEquiv, Equiv.coe_fn_mk]
    rfl
  rw [hsplit]
  calc
    _ ≤ ∑' d : V × V, ∑' b : Fin n → V × V,
        W b * J d.1 d.2 * (∑' z, ∑' t, ∑' w, M b d z * T d z t w) := by
      apply ENNReal.tsum_le_tsum
      intro d
      apply ENNReal.tsum_le_tsum
      intro b
      apply mul_le_mul' le_rfl
      simpa only [M, T, mul_assoc] using markedPrefix_snoc_probability_le q x b d c a
    _ = ∑' d : V × V, ∑' z, ∑' t, ∑' w,
        markedCoefficient q n x d z * J d.1 d.2 * T d z t w := by
      apply tsum_congr
      intro d
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro z
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro t
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro w
      change (∑' b : Fin n → V × V, W b * J d.1 d.2 * (M b d z * T d z t w)) =
        (∑' b : Fin n → V × V, W b * M b d z) * J d.1 d.2 * T d z t w
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro b
      ac_rfl
    _ = _ := by
      apply tsum_congr
      intro d
      apply tsum_congr
      intro z
      apply tsum_congr
      intro t
      apply tsum_congr
      intro w
      dsimp only [T, J]
      ac_rfl

/-- Every actual marked prefix is bounded by the iterated pair-state row,
followed by its specified deleted outgoing connection. -/
theorem markedCoefficient_le_diagramIterate [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V) (c : V × V) (a : V) :
    markedCoefficient q n x c a ≤ ∑' w,
      diagramIterate q x n (w, c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} := by
  induction n generalizing c a with
  | zero =>
    exact markedCoefficient_zero_le_diagramInitial q x c a
  | succ n ih =>
    change markedCoefficient q (n + 1) x c a ≤ ∑' w,
      (∑' p, diagramIterate q x n p * diagramTransfer q p (w, c.1)) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a}
    refine (markedCoefficient_succ_le_six_arms q n x c a).trans ?_
    refine le_trans ?_ (le_of_eq
      (marked_successor_contraction q (diagramIterate q x n) c.1 a s(c.1, c.2)))
    apply ENNReal.tsum_le_tsum
    intro d
    apply ENNReal.tsum_le_tsum
    intro z
    apply ENNReal.tsum_le_tsum
    intro t
    apply ENNReal.tsum_le_tsum
    intro w
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' (ih d z) le_rfl) le_rfl) le_rfl

/-- Actual positive lace coefficients obey the explicit deleted pair-state
diagram at every order. Both the interior geometry and the independent-layer
probability bound are proved; no diagram hypothesis is assumed. -/
@[tag "3W0M"]
theorem laceCoefficient_succ_le_laceDiagram [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) :
    laceCoefficient q (n + 1) x y ≤ laceDiagram q n x y := by
  refine (laceCoefficient_succ_le_tsum_marked_terminal q n x y).trans ?_
  change _ ≤ ∑' p, diagramIterate q x n p * diagramTerminal q p y
  refine le_trans ?_ (le_of_eq
    (marked_terminal_contraction q (diagramIterate q x n) y))
  apply ENNReal.tsum_le_tsum
  intro c
  apply ENNReal.tsum_le_tsum
  intro z
  apply ENNReal.tsum_le_tsum
  intro t
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul'
    (markedCoefficient_le_diagramIterate q n x c z) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl

end PercLib.Percolation.Bond.Lace
