/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original termwise consequences of the canonical lace diagram bounds;
no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Tuple.Basic
public import PercLib.Percolation.Bond.Lace.Diagrams.Coefficients
public import PercLib.Percolation.Bond.Lace.Diagrams.Bounds
public import PercLib.Percolation.Bond.ProfileRegularity

/-!
# A summable common envelope for individual coefficient tuples

## Main results

Every weighted finite-layer probability is bounded by its actual tuple diagram.
The tuple diagrams are monotone in the bond profile, although the coefficient
events need not be. Summing the tuple diagrams gives exactly the existing
pair-state lace diagram, with no change in constants or deleted connectors.

Finite initial, transfer, and terminal norms give a summable envelope at each
fixed order. A transfer norm below one gives a common summable envelope over
all positive orders, tuples, and endpoints. No limit-sum interchange is assumed
or asserted here.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The exact weighted marked-prefix probability is bounded before any sum over
its ordered tuple is taken. -/
theorem weighted_markedPrefix_probability_le_markedTupleDiagram [Countable V]
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V)
    (b : Fin n → V × V) (c : V × V) (a : V) :
    (∏ i, offDiagonal (fun u v : V =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin (n + 1) => law q))
        (coefficientPrefixEvent x c.1 n b ∩
          {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
            conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) a}) ≤
      markedTupleDiagram q x n b c a := by
  classical
  induction n generalizing c a with
  | zero =>
    have heq : markedCoefficient q 0 x c a =
        (∏ i, offDiagonal (fun u v : V =>
          (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (b i).1 (b i).2) *
          (Measure.pi (fun _ : Fin 1 => law q))
            (coefficientPrefixEvent x c.1 0 b ∩
              {ω | ω (Fin.last 0) \ {s(c.1, c.2)} ∈
                conn (Fin.cases x (fun j => (b j).2) (Fin.last 0)) a}) := by
      unfold markedCoefficient
      exact tsum_eq_single b (fun b' hb' => (hb' (Subsingleton.elim _ _)).elim)
    rw [← heq]
    exact markedCoefficient_zero_le_diagramInitial q x c a
  | succ n ih =>
    refine Fin.snocCases (fun b d => ?_) b
    let J : V → V → ℝ≥0∞ := offDiagonal
      (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
    let W : ℝ≥0∞ := ∏ i, J (b i).1 (b i).2
    let M (z : V) : ℝ≥0∞ :=
      (Measure.pi (fun _ : Fin (n + 1) => law q))
        (coefficientPrefixEvent x d.1 n b ∩
          {ω | ω (Fin.last n) \ {s(d.1, d.2)} ∈
            conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z})
    let H (z t w : V) : ℝ≥0∞ :=
      ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
        if w = t then 0 else
          (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1)
    let D (w : V) : ℝ≥0∞ := law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a}
    rw [markedTupleDiagram_snoc, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    refine (mul_le_mul' (le_refl (W * J d.1 d.2))
      (markedPrefix_snoc_probability_le q x b d c a)).trans ?_
    change W * J d.1 d.2 * (∑' z, ∑' t, ∑' w, M z * H z t w * D w) ≤
      ∑' z, ∑' t, ∑' w, markedTupleDiagram q x n b d z * J d.1 d.2 * H z t w * D w
    simp_rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro z
    apply ENNReal.tsum_le_tsum
    intro t
    apply ENNReal.tsum_le_tsum
    intro w
    calc
      _ = (W * M z) * J d.1 d.2 * H z t w * D w := by ac_rfl
      _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' (ih b d z) le_rfl) le_rfl) le_rfl

/-- A fixed ordered coefficient tuple has the explicit nonnegative diagram
envelope, including every bond weight and the final endpoint. -/
theorem weighted_coefficientEvent_probability_le_coefficientTupleDiagram [Countable V]
    (q : Sym2 V → unitInterval) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) :
    (∏ i, offDiagonal (fun u v : V =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b) ≤
      coefficientTupleDiagram q x y b := by
  classical
  refine Fin.snocCases (fun b c => ?_) b
  let J : V → V → ℝ≥0∞ := offDiagonal
    (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
  let W : ℝ≥0∞ := ∏ i, J (b i).1 (b i).2
  let M (z : V) : ℝ≥0∞ :=
    (Measure.pi (fun _ : Fin (n + 1) => law q))
      (coefficientPrefixEvent x c.1 n b ∩
        {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
          conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) z})
  rw [coefficientTupleDiagram_snoc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  refine (mul_le_mul' (le_refl (W * J c.1 c.2))
    (coefficientEvent_snoc_probability_le_marked_terminal q x y b c)).trans ?_
  change W * J c.1 c.2 * (∑' z, ∑' t,
      M z * (tau q c.2 t * tau q t z * tau q t y * tau q z y)) ≤
    ∑' z, ∑' t, markedTupleDiagram q x n b c z * J c.1 c.2 *
      tau q c.2 t * tau q t z * tau q t y * tau q z y
  simp_rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro z
  apply ENNReal.tsum_le_tsum
  intro t
  calc
    _ = (W * M z) * J c.1 c.2 * tau q c.2 t * tau q t z * tau q t y * tau q z y := by
      ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul'
      (weighted_markedPrefix_probability_le_markedTupleDiagram q n x b c z)
        le_rfl) le_rfl) le_rfl) le_rfl) le_rfl

/-- Summing marked tuple envelopes gives exactly the existing iterated row
followed by its deleted outgoing connection. -/
theorem tsum_markedTupleDiagram (q : Sym2 V → unitInterval)
    (n : ℕ) (x : V) (c : V × V) (a : V) :
    (∑' b : Fin n → V × V, markedTupleDiagram q x n b c a) =
      ∑' w, diagramIterate q x n (w, c.1) *
        law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a} := by
  classical
  induction n generalizing c a with
  | zero =>
    rw [tsum_eq_single (fun i : Fin 0 => Fin.elim0 i)
      (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
    rfl
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => V × V)).tsum_eq,
      ENNReal.tsum_prod']
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, markedTupleDiagram_snoc]
    let J : V → V → ℝ≥0∞ := offDiagonal
      (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
    let H (d : V × V) (z t w : V) : ℝ≥0∞ :=
      ((tau q t w * tau q w c.1) * (tau q t z * tau q z c.1) * tau q d.2 t +
        if w = t then 0 else
          (tau q d.2 w * tau q w t) * (tau q t z * tau q z c.1) * tau q t c.1)
    let D (w : V) : ℝ≥0∞ := law q {ω : Config V | ω \ {s(c.1, c.2)} ∈ conn w a}
    calc
      (∑' d : V × V, ∑' b : Fin n → V × V, ∑' z, ∑' t, ∑' w,
          markedTupleDiagram q x n b d z * J d.1 d.2 * H d z t w * D w) =
        ∑' d : V × V, ∑' z, ∑' t, ∑' w,
          (∑' b : Fin n → V × V, markedTupleDiagram q x n b d z) *
            J d.1 d.2 * H d z t w * D w := by
        apply tsum_congr
        intro d
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro z
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro t
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro w
        simp_rw [ENNReal.tsum_mul_right]
      _ = _ := by
        simp_rw [ih]
        exact marked_successor_contraction q (diagramIterate q x n) c.1 a s(c.1, c.2)

/-- Summing the envelope over complete ordered tuples gives exactly the
canonical pair-state lace diagram, with the target still fixed. -/
theorem tsum_coefficientTupleDiagram (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) :
    (∑' b : Fin (n + 1) → V × V, coefficientTupleDiagram q x y b) =
      laceDiagram q n x y := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => V × V)).tsum_eq,
    ENNReal.tsum_prod']
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, coefficientTupleDiagram_snoc]
  let J : V → V → ℝ≥0∞ := offDiagonal
    (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
  calc
    (∑' c : V × V, ∑' b : Fin n → V × V, ∑' z, ∑' t,
        markedTupleDiagram q x n b c z * J c.1 c.2 *
          tau q c.2 t * tau q t z * tau q t y * tau q z y) =
      ∑' c : V × V, ∑' z, ∑' t,
        (∑' b : Fin n → V × V, markedTupleDiagram q x n b c z) * J c.1 c.2 *
          tau q c.2 t * tau q t z * tau q t y * tau q z y := by
      apply tsum_congr
      intro c
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro z
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro t
      simp_rw [ENNReal.tsum_mul_right]
    _ = _ := by
      simp_rw [tsum_markedTupleDiagram]
      exact marked_terminal_contraction q (diagramIterate q x n) y

/-- Deleting the same bond in two coupled profiles preserves the monotonicity
of the connection probability. -/
theorem law_deleted_conn_mono [Countable V]
    {q q' : Sym2 V → unitInterval} (hqq' : q ≤ q') (e : Sym2 V) (x y : V) :
    law q {ω : Config V | ω \ {e} ∈ conn x y} ≤
      law q' {ω : Config V | ω \ {e} ∈ conn x y} :=
  prodBernoulli_mono_event q q' hqq'
    ((measurableSet_conn x y).preimage (measurable_diff_singleton e))
    (fun _ _ hω hconn => conn_mono (sdiff_subset_sdiff_left hω) hconn)

/-- The initial diagram, including its exact diagonal branch, is monotone
in the bond profile. -/
theorem diagramInitial_mono_profile [Countable V]
    {q q' : Sym2 V → unitInterval} (hqq' : q ≤ q') (x : V) (p : V × V) :
    diagramInitial q x p ≤ diagramInitial q' x p := by
  classical
  by_cases hp : p.2 = x
  · simp only [diagramInitial, ite_eq_left hp]
    exact le_rfl
  · simp only [diagramInitial, ite_eq_right hp]
    exact mul_le_mul' (mul_le_mul' (tau_mono hqq' x p.1) (tau_mono hqq' x p.2))
      (tau_mono hqq' p.1 p.2)

private theorem offDiagonal_bond_weight_mono
    {q q' : Sym2 V → unitInterval} (hqq' : q ≤ q') (u v : V) :
    offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v ≤
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q' s(a, b)) : ℝ≥0∞)) u v := by
  classical
  by_cases huv : u = v
  · simp [offDiagonal, huv]
  · simp only [offDiagonal, ite_eq_right (Ne.symm huv)]
    apply ENNReal.coe_le_coe.mpr
    rw [← NNReal.coe_le_coe, unitInterval.coe_toNNReal, unitInterval.coe_toNNReal]
    exact hqq' s(u, v)

/-- Each marked tuple envelope is monotone in the profile. The random sets
of the actual prefix event are not compared monotonically. -/
theorem markedTupleDiagram_mono [Countable V]
    {q q' : Sym2 V → unitInterval} (hqq' : q ≤ q')
    (n : ℕ) (x : V) (b : Fin n → V × V) (c : V × V) (a : V) :
    markedTupleDiagram q x n b c a ≤ markedTupleDiagram q' x n b c a := by
  classical
  induction n generalizing c a with
  | zero =>
    exact ENNReal.tsum_le_tsum fun r =>
      mul_le_mul' (diagramInitial_mono_profile hqq' x (r, c.1))
        (law_deleted_conn_mono hqq' s(c.1, c.2) r a)
  | succ n ih =>
    refine Fin.snocCases (fun b d => ?_) b
    rw [markedTupleDiagram_snoc, markedTupleDiagram_snoc]
    refine ENNReal.tsum_le_tsum fun z => ENNReal.tsum_le_tsum fun t =>
      ENNReal.tsum_le_tsum fun w => ?_
    refine mul_le_mul' (mul_le_mul' (mul_le_mul' (ih b d z)
      (offDiagonal_bond_weight_mono hqq' d.1 d.2)) ?_)
      (law_deleted_conn_mono hqq' s(c.1, c.2) w a)
    apply add_le_add
    · exact mul_le_mul'
        (mul_le_mul' (mul_le_mul' (tau_mono hqq' t w) (tau_mono hqq' w c.1))
          (mul_le_mul' (tau_mono hqq' t z) (tau_mono hqq' z c.1)))
        (tau_mono hqq' d.2 t)
    · split_ifs
      · exact le_rfl
      · exact mul_le_mul'
          (mul_le_mul' (mul_le_mul' (tau_mono hqq' d.2 w) (tau_mono hqq' w t))
            (mul_le_mul' (tau_mono hqq' t z) (tau_mono hqq' z c.1)))
          (tau_mono hqq' t c.1)

/-- The complete tuple diagram is a monotone nonnegative envelope. -/
theorem coefficientTupleDiagram_mono [Countable V]
    {q q' : Sym2 V → unitInterval} (hqq' : q ≤ q')
    {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    coefficientTupleDiagram q x y b ≤ coefficientTupleDiagram q' x y b := by
  classical
  refine Fin.snocCases (fun b c => ?_) b
  rw [coefficientTupleDiagram_snoc, coefficientTupleDiagram_snoc]
  exact ENNReal.tsum_le_tsum fun z => ENNReal.tsum_le_tsum fun t =>
    mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul'
      (markedTupleDiagram_mono hqq' n x b c z)
      (offDiagonal_bond_weight_mono hqq' c.1 c.2))
      (tau_mono hqq' c.2 t)) (tau_mono hqq' t z)) (tau_mono hqq' t y))
      (tau_mono hqq' z y)

/-- One upper-profile diagram bounds every actual weighted tuple probability
at smaller profiles, without assuming monotonicity of the coefficient event. -/
theorem weighted_coefficientEvent_probability_le_upper_coefficientTupleDiagram [Countable V]
    {q q₀ : Sym2 V → unitInterval} (hqq₀ : q ≤ q₀) {n : ℕ} (x y : V)
    (b : Fin (n + 1) → V × V) :
    (∏ i, offDiagonal (fun u v : V =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b) ≤
      coefficientTupleDiagram q₀ x y b :=
  (weighted_coefficientEvent_probability_le_coefficientTupleDiagram q x y b).trans
    (coefficientTupleDiagram_mono hqq₀ x y b)

/-- The full tuple-and-endpoint envelope has the same geometric bound as
the existing diagram, with no extra prefactor. -/
theorem coefficientTupleDiagram_mass_le_geometric
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) :
    (∑' b : Fin (n + 1) → V × V, ∑' y, coefficientTupleDiagram q x y b) ≤
      (∑' p, diagramInitial q x p) * ρ ^ n * κ := by
  rw [ENNReal.tsum_comm]
  simp_rw [tsum_coefficientTupleDiagram]
  exact laceDiagram_mass_le_geometric q x ρ κ hρ hκ n

/-- Finite diagram norms give a genuinely finite joint envelope mass at
each fixed order; a contraction hypothesis is unnecessary here. -/
theorem coefficientTupleDiagram_mass_ne_top_of_finite_diagram_bounds
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V) (ρ κ : ℝ≥0∞)
    (hρfinite : ρ ≠ ⊤) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    (∑' b : Fin (n + 1) → V × V, ∑' y, coefficientTupleDiagram q x y b) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hinitial (ENNReal.pow_ne_top hρfinite)) hκfinite)
    (coefficientTupleDiagram_mass_le_geometric q n x ρ κ hρ hκ)

/-- The real upper-profile envelope is summable jointly in the fixed-order
bond tuple and endpoint. -/
theorem summable_coefficientTupleDiagram_toReal_of_finite_diagram_bounds
    (q : Sym2 V → unitInterval) (n : ℕ) (x : V) (ρ κ : ℝ≥0∞)
    (hρfinite : ρ ≠ ⊤) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    Summable (fun p : (Fin (n + 1) → V × V) × V =>
      (coefficientTupleDiagram q x p.2 p.1).toReal) := by
  apply ENNReal.summable_toReal
  rw [ENNReal.tsum_prod']
  exact coefficientTupleDiagram_mass_ne_top_of_finite_diagram_bounds
    q n x ρ κ hρfinite hκfinite hρ hκ hinitial

/-- Contraction gives the exact geometric upper bound on the envelope
summed over all positive orders, tuples, and endpoints. -/
theorem tsum_coefficientTupleDiagram_mass_le
    (q : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ) :
    (∑' n : ℕ, ∑' b : Fin (n + 1) → V × V, ∑' y,
      coefficientTupleDiagram q x y b) ≤
        (∑' p, diagramInitial q x p) * (1 - ρ)⁻¹ * κ := by
  have heq (n : ℕ) :
      (∑' b : Fin (n + 1) → V × V, ∑' y, coefficientTupleDiagram q x y b) =
        ∑' y, laceDiagram q n x y := by
    rw [ENNReal.tsum_comm]
    simp_rw [tsum_coefficientTupleDiagram]
  simp_rw [heq]
  exact tsum_laceDiagram_mass_le q x ρ κ hρ hκ

/-- A subunit transfer norm and finite initial and terminal norms make the
explicit common envelope summable over all its indices. -/
theorem tsum_coefficientTupleDiagram_mass_ne_top
    (q : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    (∑' n : ℕ, ∑' b : Fin (n + 1) → V × V, ∑' y,
      coefficientTupleDiagram q x y b) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hinitial
      (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hρone)))) hκfinite)
    (tsum_coefficientTupleDiagram_mass_le q x ρ κ hρ hκ)

/-- The real envelope is summable on the countable disjoint union of the
positive-order tuple-and-endpoint spaces. -/
theorem summable_coefficientTupleDiagram_toReal
    (q : Sym2 V → unitInterval) (x : V) (ρ κ : ℝ≥0∞)
    (hρone : ρ < 1) (hκfinite : κ ≠ ⊤)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hκ : ∀ p, (∑' y, diagramTerminal q p y) ≤ κ)
    (hinitial : (∑' p, diagramInitial q x p) ≠ ⊤) :
    Summable (fun p : Σ n : ℕ, (Fin (n + 1) → V × V) × V =>
      (coefficientTupleDiagram q x p.2.2 p.2.1).toReal) := by
  apply ENNReal.summable_toReal
  rw [ENNReal.tsum_sigma']
  simp_rw [ENNReal.tsum_prod']
  exact tsum_coefficientTupleDiagram_mass_ne_top q x ρ κ hρone hκfinite hρ hκ hinitial

end PercLib.Percolation.Bond.Lace
