/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Prefix
public import PercLib.Percolation.Bond.Lace.Diagrams.Basic
public import PercLib.Percolation.Bond.Lace.FirstDiagram
public import PercLib.Percolation.Bond.Lace.TerminalDiagram
public import PercLib.Percolation.Bond.Lace.Remainder.Recurrence

/-!
# The initial marked layer and final terminal extraction

The initial marked probability keeps its certain diagonal contribution exactly.
The final layer is bounded by the proved terminal four-arm event. These lemmas
support the all-order coefficient-diagram induction without assuming its result.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- With no earlier bond, the marked prefix is exactly the joint event in its
single initial configuration. -/
theorem markedCoefficient_zero_eq [Countable V]
    (q : Sym2 V → unitInterval) (x : V) (c : V × V) (a : V) :
    markedCoefficient q 0 x c a =
      law q (doubleConn x c.1 ∩ {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn x a}) := by
  unfold markedCoefficient
  simp only [Fin.prod_univ_zero, one_mul]
  rw [tsum_eq_single (fun i : Fin 0 => Fin.elim0 i)
    (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
  have hm : MeasurableSet
      (doubleConn x c.1 ∩ {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn x a}) :=
    (measurableSet_doubleConn x c.1).inter ((measurableSet_conn x a).preimage (by fun_prop))
  change (Measure.pi (fun _ : Fin 1 => law q))
    ((Function.eval (0 : Fin 1)) ⁻¹'
      (doubleConn x c.1 ∩ {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn x a})) = _
  exact (measurePreserving_eval (fun _ : Fin 1 => law q) 0).measure_preimage hm.nullMeasurableSet

/-- The initial marked probability is bounded by the initial pair-state
factor followed by the retained deleted-bond connection. -/
theorem markedCoefficient_zero_le_diagramInitial [Countable V]
    (q : Sym2 V → unitInterval) (x : V) (c : V × V) (a : V) :
    markedCoefficient q 0 x c a ≤ ∑' w,
      diagramInitial q x (w, c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} := by
  rw [markedCoefficient_zero_eq]
  by_cases hc : c.1 = x
  · simp [hc, diagramInitial]
  · refine (law_doubleConn_inter_deleted_le q x c.1 a s(c.1, c.2)).trans_eq ?_
    apply tsum_congr
    intro w
    simp only [diagramInitial, hc, ite_false]
    ac_rfl

private theorem law_terminal_arms_le [Countable V]
    (q : Sym2 V → unitInterval) (v z t y : V) :
    law q (disjointOccurrence
      (disjointOccurrence (disjointOccurrence (conn t z) (conn z y)) (conn t y))
      (conn v t)) ≤ tau q v t * tau q t z * tau q t y * tau q z y := by
  have h1 := countable_profile_bk q (isUpperSet_conn t z) (isUpperSet_conn z y)
  have h2 := countable_profile_bk q
    (isUpperSet_disjointOccurrence (isUpperSet_conn t z) (isUpperSet_conn z y))
    (isUpperSet_conn t y)
  have h3 := countable_profile_bk q
    (isUpperSet_disjointOccurrence
      (isUpperSet_disjointOccurrence (isUpperSet_conn t z) (isUpperSet_conn z y))
      (isUpperSet_conn t y)) (isUpperSet_conn v t)
  refine h3.trans ((mul_le_mul' (h2.trans (mul_le_mul' h1 le_rfl)) le_rfl).trans_eq ?_)
  change ((tau q t z * tau q z y) * tau q t y) * tau q v t = _
  ac_rfl

/-- For a fixed bond sequence, the terminal four-arm event is independent
of the marked prefix probability in the preceding configurations. -/
theorem coefficientEvent_snoc_probability_le_marked_terminal [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V)
    (b : Fin n → V × V) (c : V × V) :
    (Measure.pi (fun _ : Fin (n + 2) => law q))
      (coefficientEvent x y (Fin.snoc b c)) ≤ ∑' z, ∑' t,
        (Measure.pi (fun _ : Fin (n + 1) => law q))
          (coefficientPrefixEvent x c.1 n b ∩
            {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
              conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z}) *
        (tau q c.2 t * tau q t z * tau q t y * tau q z y) := by
  let M : V → Set (Fin (n + 1) → Config V) := fun z =>
    coefficientPrefixEvent x c.1 n b ∩
      {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
        conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z}
  let G : V → V → Set (Config V) := fun z t => disjointOccurrence
    (disjointOccurrence (disjointOccurrence (conn t z) (conn z y)) (conn t y))
    (conn c.2 t)
  have hsub : {p : (Fin (n + 1) → Config V) × Config V |
      Fin.snoc p.1 p.2 ∈ coefficientEvent x y (Fin.snoc b c)} ⊆
      ⋃ z : V, ⋃ t : V, M z ×ˢ G z t := by
    intro p hp
    obtain ⟨hpre, hlast⟩ := (mem_coefficientEvent_snoc_prefix_iff x y b c p.1 p.2).mp hp
    have ht := laceEPrime_subset_iUnion_terminal _ c.2 y hlast
    obtain ⟨z, hz⟩ := mem_iUnion.mp ht
    obtain ⟨t, ht⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨t, ⟨hpre, z.property⟩, ht⟩⟩
  rw [measure_layers_eq_prod_snoc q
    (measurableSet_coefficientEvent x y (Fin.snoc b c))]
  refine (measure_mono hsub).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun z =>
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun t => ?_)))
  rw [Measure.prod_prod]
  exact mul_le_mul' le_rfl (law_terminal_arms_le q c.2 z t y)

/-- The actual coefficient is bounded by its exact marked prefixes and the
constant-one terminal four-arm factor. No interior diagram estimate is assumed. -/
theorem laceCoefficient_succ_le_tsum_marked_terminal [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) :
    laceCoefficient q (n + 1) x y ≤ ∑' c : V × V, ∑' z, ∑' t,
      markedCoefficient q n x c z *
        offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) c.1 c.2 *
          tau q c.2 t * tau q t z * tau q t y * tau q z y := by
  let J : V → V → ℝ≥0∞ :=
    offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
  let W : (Fin n → V × V) → ℝ≥0∞ := fun b => ∏ i, J (b i).1 (b i).2
  let M : (Fin n → V × V) → (V × V) → V → ℝ≥0∞ := fun b c z =>
    (Measure.pi (fun _ : Fin (n + 1) => law q))
      (coefficientPrefixEvent x c.1 n b ∩
        {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
          conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z})
  let T : (V × V) → V → V → ℝ≥0∞ := fun c z t =>
    tau q c.2 t * tau q t z * tau q t y * tau q z y
  have hsplit : laceCoefficient q (n + 1) x y =
      ∑' c : V × V, ∑' b : Fin n → V × V,
        W b * J c.1 c.2 * (Measure.pi (fun _ : Fin (n + 2) => law q))
          (coefficientEvent x y (Fin.snoc b c)) := by
    change (∑' b : Fin (n + 1) → V × V,
      (∏ i, J (b i).1 (b i).2) *
        (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b)) = _
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => V × V)).tsum_eq,
      ENNReal.tsum_prod']
    apply tsum_congr
    intro c
    apply tsum_congr
    intro b
    change (∏ i, J ((Fin.snoc b c : Fin (n + 1) → V × V) i).1
      ((Fin.snoc b c : Fin (n + 1) → V × V) i).2) * _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.snocEquiv, Equiv.coe_fn_mk]
    rfl
  rw [hsplit]
  calc
    _ ≤ ∑' c : V × V, ∑' b : Fin n → V × V,
        W b * J c.1 c.2 * (∑' z, ∑' t, M b c z * T c z t) := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply ENNReal.tsum_le_tsum
      intro b
      exact mul_le_mul' le_rfl
        (coefficientEvent_snoc_probability_le_marked_terminal q x y b c)
    _ = ∑' c : V × V, ∑' z, ∑' t,
        markedCoefficient q n x c z * J c.1 c.2 * T c z t := by
      apply tsum_congr
      intro c
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro z
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro t
      change (∑' b : Fin n → V × V, W b * J c.1 c.2 * (M b c z * T c z t)) =
        (∑' b : Fin n → V × V, W b * M b c z) * J c.1 c.2 * T c z t
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro b
      ac_rfl
    _ = _ := by
      apply tsum_congr
      intro c
      apply tsum_congr
      intro z
      apply tsum_congr
      intro t
      dsimp only [T, J]
      ac_rfl

end PercLib.Percolation.Bond.Lace
