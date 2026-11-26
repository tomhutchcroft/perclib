/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Source motivation: M. Aizenman and C. M. Newman, J.
Stat. Phys. 36 (1984), the moment bounds from the tree-graph inequalities, and the wiki statement
Y84V. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.TreeGraph.BranchPoint
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # All cluster moments under a uniform susceptibility bound (Y84V)

With `M ≥ χ(x)` for every `x` and `m ≥ 1`,
`E|K_o|^m ≤ (2m-3)‼ χ(o) M^(2m-2)` (with `(-1)‼ = 1`, which is `0‼` in `ℕ`).

* `lintegral_encard_pow_eq_tsum`: `E|K_o|^m = ∑_{x ∈ V^m} P(o ↔ x_i ∀ i)`.
* `tsum_law_mul_law`: `∑_x P(z ↔ x_A) P(z ↔ x_(Aᶜ)) = E|K_z|^|A| E|K_z|^(m-|A|)`.
* `lintegral_encard_pow_le_branch`: the branch-point recursion
  `E|K_o|^m ≤ ∑_z τ(o,z) ∑_{A ∋ 0, A ⊊ [m]} E|K_z|^|A| E|K_z|^(m-|A|)`.
* `sum_branch_doubleFactorial`: `t_m = ∑_{A ∋ 0, A ⊊ [m]} t_|A| t_(m-|A|)` for
  `t_m = (2m-3)‼`, proved through Catalan numbers.
* `lintegral_encard_pow_le`: the bound, by strong induction on `m`.

**Strengthening, stated explicitly.** The usual statement assumes `M = ⨆ x, χ(x) < ⊤`. The bound is
proved for every `M` with `χ(x) ≤ M` for all `x`, finite or not (in `ℝ≥0∞` it is trivial
when `M = ⊤` and `m ≥ 2`), and `lintegral_encard_pow_le_iSup` is the form with `M = ⨆ x, χ(x)` and
the finiteness hypothesis omitted.
-/

@[expose] public section
noncomputable section

open MeasureTheory Finset Nat
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-! ### The double-factorial identity -/

/-- `(k+1)! C_k = 2^k (2k-1)‼`. -/
theorem succ_factorial_mul_catalan (k : ℕ) :
    (k + 1)! * catalan k = 2 ^ k * (2 * k - 1)‼ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h1 : (2 * k)! = 2 ^ k * k ! * (2 * k - 1)‼ := by
    have := factorial_eq_mul_doubleFactorial (2 * k - 1)
    rw [show 2 * k - 1 + 1 = 2 * k by omega, doubleFactorial_two_mul] at this
    exact this
  have h2 : (k + 1) * catalan k * k ! * k ! = (2 * k)! := by
    rw [succ_mul_catalan_eq_centralBinom, centralBinom_eq_two_mul_choose]
    have := choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rwa [show 2 * k - k = k by omega] at this
  have h3 : ((k + 1)! * catalan k) * k ! = (2 ^ k * (2 * k - 1)‼) * k ! := by
    calc ((k + 1)! * catalan k) * k ! = (k + 1) * catalan k * k ! * k ! := by
          rw [factorial_succ]; ring
      _ = 2 ^ k * k ! * (2 * k - 1)‼ := h2.trans h1
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_right (factorial_pos k) h3

/-- `2 ∑_{k ≤ n} (k+1) C_k C_(n-k) = (n+2) C_(n+1)`. -/
theorem two_mul_sum_succ_catalan (n : ℕ) :
    2 * ∑ k ∈ range (n + 1), (k + 1) * (catalan k * catalan (n - k)) =
      (n + 2) * catalan (n + 1) := by
  rw [two_mul, catalan_succ, ← Finset.sum_range (fun i => catalan i * catalan (n - i)),
    Finset.mul_sum]
  conv_lhs => arg 2; rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]
  have : n - k + 1 + (k + 1) = n + 2 := by omega
  calc (k + 1) * (catalan k * catalan (n - k)) + (n - k + 1) * (catalan (n - k) * catalan k)
      = (n - k + 1 + (k + 1)) * (catalan k * catalan (n - k)) := by ring
    _ = _ := by rw [this]

/-- `∑_{k ≤ n} C(n+1,k) (2k-1)‼ (2(n-k)-1)‼ = (2n+1)‼`. -/
theorem sum_choose_doubleFactorial (n : ℕ) :
    ∑ k ∈ range (n + 1), (n + 1).choose k * ((2 * k - 1)‼ * (2 * (n - k) - 1)‼) =
      (2 * (n + 1) - 1)‼ := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ (n + 1) by positivity)
  have hterm : ∀ k ∈ range (n + 1), 2 ^ (n + 1) * ((n + 1).choose k *
      ((2 * k - 1)‼ * (2 * (n - k) - 1)‼)) =
      2 * (n + 1)! * ((k + 1) * (catalan k * catalan (n - k))) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have e1 := succ_factorial_mul_catalan k
    have e2 := succ_factorial_mul_catalan (n - k)
    have e3 := choose_mul_factorial_mul_factorial (show k ≤ n + 1 by omega)
    rw [show n + 1 - k = n - k + 1 by omega, factorial_succ (n - k)] at e3
    have hp : 2 ^ (n + 1) = 2 * 2 ^ k * 2 ^ (n - k) := by
      rw [mul_assoc, ← pow_add, ← pow_succ']; congr 1; omega
    -- multiply through by `k! (n-k)!`-free identities
    have : 2 ^ (n + 1) * ((n + 1).choose k * ((2 * k - 1)‼ * (2 * (n - k) - 1)‼)) =
        2 * (n + 1).choose k * ((2 ^ k * (2 * k - 1)‼) * (2 ^ (n - k) * (2 * (n - k) - 1)‼)) := by
      rw [hp]; ring
    rw [this, ← e1, ← e2, factorial_succ k]
    calc 2 * (n + 1).choose k * ((k + 1) * k ! * catalan k * ((n - k + 1)! * catalan (n - k)))
        = 2 * ((n + 1).choose k * k ! * ((n - k + 1) * (n - k)!)) * ((k + 1) *
            (catalan k * catalan (n - k))) := by rw [factorial_succ (n - k)]; ring
      _ = _ := by rw [e3]
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_assoc,
    mul_left_comm 2, two_mul_sum_succ_catalan]
  have := succ_factorial_mul_catalan (n + 1)
  rw [← this, factorial_succ (n + 1)]
  ring

/-- The binary-tree count `t_m = (2m-3)‼` satisfies
`t_m = ∑_{A ∋ 0, A ⊊ [m]} t_|A| t_(m-|A|)`, here with `m = n + 2`. -/
theorem sum_branch_doubleFactorial (n : ℕ) :
    ∑ A ∈ (univ : Finset (Fin (n + 2))).powerset.filter
        (fun A => 0 ∈ A ∧ (univ \ A).Nonempty),
      (2 * A.card - 3)‼ * (2 * (n + 2 - A.card) - 3)‼ = (2 * (n + 2) - 3)‼ := by
  classical
  set S : Finset (Fin (n + 2)) := univ.erase 0 with hS
  have h0S : (0 : Fin (n + 2)) ∉ S := Finset.notMem_erase 0 _
  have hScard : S.card = n + 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rfl
  have huniv : (univ : Finset (Fin (n + 2))) = insert 0 S :=
    (Finset.insert_erase (Finset.mem_univ _)).symm
  rw [Finset.sum_filter, huniv, Finset.sum_powerset_insert h0S]
  have h0 : ∀ t ∈ S.powerset,
      (if (0 : Fin (n + 2)) ∈ t ∧ (insert 0 S \ t).Nonempty
        then (2 * t.card - 3)‼ * (2 * (n + 2 - t.card) - 3)‼ else 0) = 0 := by
    intro t ht
    rw [ite_eq_right_iff]
    rintro ⟨h, -⟩
    exact absurd (Finset.mem_powerset.1 ht h) h0S
  rw [Finset.sum_eq_zero h0, zero_add]
  have h1 : ∀ t ∈ S.powerset,
      (if (0 : Fin (n + 2)) ∈ insert 0 t ∧ (insert 0 S \ insert 0 t).Nonempty
        then (2 * (insert 0 t).card - 3)‼ * (2 * (n + 2 - (insert 0 t).card) - 3)‼ else 0) =
      (fun k => if k < n + 1 then (2 * k - 1)‼ * (2 * (n - k) - 1)‼ else 0) t.card := by
    intro t ht
    have ht' := Finset.mem_powerset.1 ht
    have h0t : (0 : Fin (n + 2)) ∉ t := fun h => h0S (ht' h)
    have hcard : (insert 0 t).card = t.card + 1 := Finset.card_insert_of_notMem h0t
    have hle : t.card ≤ n + 1 := hScard ▸ Finset.card_le_card ht'
    have hne : (insert 0 S \ insert 0 t).Nonempty ↔ t.card < n + 1 := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
      constructor
      · intro h
        by_contra hc
        have heq : t = S := Finset.eq_of_subset_of_card_le ht' (by omega)
        exact h (heq ▸ subset_rfl)
      · intro h hsub
        have := Finset.card_le_card hsub
        rw [hcard, Finset.card_insert_of_notMem h0S] at this
        omega
    simp only [Finset.mem_insert_self, true_and, hne, hcard]
    split_ifs with hk
    · congr 2; omega
    · rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_powerset_apply_card
    (fun k => if k < n + 1 then (2 * k - 1)‼ * (2 * (n - k) - 1)‼ else 0), hScard,
    Finset.sum_range_succ]
  simp only [lt_irrefl, ↓reduceIte, smul_eq_mul, mul_zero, add_zero]
  rw [show 2 * (n + 2) - 3 = 2 * (n + 1) - 1 by omega, ← sum_choose_doubleFactorial n]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range.1 hk, ↓reduceIte]

/-! ### Moments as sums over tuples -/

variable {V : Type*}

/-- A sum over `m`-tuples of a product splits into a product of sums. -/
theorem tsum_fin_prod (m : ℕ) (f : Fin m → V → ℝ≥0∞) :
    ∑' x : Fin m → V, ∏ i, f i (x i) = ∏ i, ∑' v, f i v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← (Fin.consEquiv fun _ => V).tsum_eq]
    have key : ∀ c : V × (Fin m → V), ∏ i, f i ((Fin.consEquiv fun _ => V) c i) =
        f 0 c.1 * ∏ i, f i.succ (c.2 i) := by
      intro c; rw [Fin.prod_univ_succ]; rfl
    rw [tsum_congr key, Fin.prod_univ_succ, ← ih fun i => f i.succ, ← ENNReal.tsum_mul_right]
    calc ∑' c : V × (Fin m → V), f 0 c.1 * ∏ i, f i.succ (c.2 i)
        = ∑' v, ∑' y : Fin m → V, f 0 v * ∏ i, f i.succ (y i) :=
          ENNReal.tsum_prod (f := fun v (y : Fin m → V) => f 0 v * ∏ i, f i.succ (y i))
      _ = _ := tsum_congr fun v => ENNReal.tsum_mul_left

/-- The indicator of `{z ↔ x_i ∀ i ∈ A}` is the product of the indicators. -/
theorem indicator_forall_conn_eq_prod {m : ℕ} (z : V) (x : Fin m → V) (A : Finset (Fin m))
    (ω : Config V) :
    {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator (fun _ => (1 : ℝ≥0∞)) ω =
      ∏ i ∈ A, (conn z (x i)).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases h : ω ∈ {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}
  · rw [Set.indicator_of_mem h]
    exact (Finset.prod_eq_one fun i hi => Set.indicator_of_mem (h i hi) _).symm
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_ofPred_eq, not_forall] at h
    obtain ⟨i, hi, hω⟩ := h
    exact (Finset.prod_eq_zero hi (Set.indicator_of_notMem hω _)).symm

theorem measurableSet_forall_conn [Countable V] {m : ℕ} (z : V) (x : Fin m → V)
    (A : Finset (Fin m)) : MeasurableSet {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)} := by
  have h : {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)} = ⋂ i ∈ A, conn z (x i) := by
    ext η; simp
  rw [h]
  exact Finset.measurableSet_biInter A fun i _ => measurableSet_conn _ _

/-- `|K_o|^m = ∑_{x ∈ V^m} 1{o ↔ x_i ∀ i}`. -/
theorem encard_pow_eq_tsum (ω : Config V) (o : V) (m : ℕ) :
    ((cluster ω o).encard : ℝ≥0∞) ^ m = ∑' x : Fin m → V,
      {η : Config V | ∀ i ∈ (univ : Finset (Fin m)), η ∈ conn o (x i)}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [encard_cluster_eq_tsum, ← Fin.prod_const,
    ← tsum_fin_prod m fun _ v => (conn o v).indicator (fun _ => (1 : ℝ≥0∞)) ω]
  exact tsum_congr fun x => (indicator_forall_conn_eq_prod o x univ ω).symm

/-- **Moments as tuple sums.** `E|K_o|^m = ∑_{x ∈ V^m} P(o ↔ x_i ∀ i)`. -/
theorem lintegral_encard_pow_eq_tsum [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (m : ℕ) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q =
      ∑' x : Fin m → V, law q {ω | ∀ i ∈ (univ : Finset (Fin m)), ω ∈ conn o (x i)} := by
  simp_rw [encard_pow_eq_tsum]
  rw [lintegral_tsum fun x => (measurable_const.indicator
    (measurableSet_forall_conn o x univ)).aemeasurable]
  exact tsum_congr fun x => lintegral_indicator_one (measurableSet_forall_conn o x univ)

theorem measurable_encard_pow [Countable V] (z : V) (n : ℕ) :
    Measurable fun ω : Config V => ((cluster ω z).encard : ℝ≥0∞) ^ n :=
  ((Measurable.of_discrete (f := ((↑) : ℕ∞ → ℝ≥0∞))).comp
    (measurable_encard_cluster z)).pow_const n

/-- Pointwise factorisation over a split of the indices. -/
theorem tsum_indicator_mul_indicator {m : ℕ} (z : V) (A : Finset (Fin m))
    (ω ω' : Config V) :
    ∑' x : Fin m → V,
      {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        {η : Config V | ∀ i ∈ univ \ A, η ∈ conn z (x i)}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω' =
      ((cluster ω z).encard : ℝ≥0∞) ^ A.card * ((cluster ω' z).encard : ℝ≥0∞) ^ (m - A.card) := by
  classical
  set F : Fin m → V → ℝ≥0∞ := fun i v =>
    if i ∈ A then (conn z v).indicator (fun _ => (1 : ℝ≥0∞)) ω
    else (conn z v).indicator (fun _ => (1 : ℝ≥0∞)) ω' with hF
  have h1 : ∀ x : Fin m → V,
      {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        {η : Config V | ∀ i ∈ univ \ A, η ∈ conn z (x i)}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω' = ∏ i, F i (x i) := by
    intro x
    rw [indicator_forall_conn_eq_prod, indicator_forall_conn_eq_prod,
      ← Finset.compl_eq_univ_sdiff, ← Finset.prod_mul_prod_compl A]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [hF, hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [hF, Finset.mem_compl.1 hi]
  have hc : m - A.card = Aᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]
  rw [tsum_congr h1, tsum_fin_prod, ← Finset.prod_mul_prod_compl A, hc,
    encard_cluster_eq_tsum, encard_cluster_eq_tsum, ← Finset.prod_const, ← Finset.prod_const]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hF, hi]
  · exact Finset.prod_congr rfl fun i hi => by simp [hF, Finset.mem_compl.1 hi]

/-- **Factorisation over a split.**
`∑_x P(z ↔ x_A) P(z ↔ x_(Aᶜ)) = E|K_z|^|A| · E|K_z|^(m-|A|)`. -/
theorem tsum_law_mul_law [Countable V] (q : Sym2 V → unitInterval) (z : V) {m : ℕ}
    (A : Finset (Fin m)) :
    ∑' x : Fin m → V, law q {ω | ∀ i ∈ A, ω ∈ conn z (x i)} *
        law q {ω | ∀ i ∈ univ \ A, ω ∈ conn z (x i)} =
      (∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ A.card ∂law q) *
        ∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ (m - A.card) ∂law q := by
  have hmA := fun x => measurableSet_forall_conn (V := V) z x A
  have hmB := fun x => measurableSet_forall_conn (V := V) z x (univ \ A)
  have hiA : ∀ x : Fin m → V, Measurable
      ({η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator fun _ => (1 : ℝ≥0∞)) :=
    fun x => measurable_const.indicator (hmA x)
  have hiB : ∀ x : Fin m → V, Measurable
      ({η : Config V | ∀ i ∈ univ \ A, η ∈ conn z (x i)}.indicator fun _ => (1 : ℝ≥0∞)) :=
    fun x => measurable_const.indicator (hmB x)
  have h1 : ∀ x : Fin m → V, law q {ω | ∀ i ∈ A, ω ∈ conn z (x i)} *
      law q {ω | ∀ i ∈ univ \ A, ω ∈ conn z (x i)} =
      ∫⁻ ω, {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        law q {ω | ∀ i ∈ univ \ A, ω ∈ conn z (x i)} ∂law q := by
    intro x
    rw [lintegral_mul_const _ (hiA x)]
    congr 1
    exact (lintegral_indicator_one (hmA x)).symm
  rw [tsum_congr h1, ← lintegral_tsum fun x => ((hiA x).mul_const _).aemeasurable,
    ← lintegral_mul_const _ (measurable_encard_pow z _)]
  refine lintegral_congr fun ω => ?_
  have h2 : ∀ x : Fin m → V,
      {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        law q {ω | ∀ i ∈ univ \ A, ω ∈ conn z (x i)} =
      ∫⁻ ω', {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        {η : Config V | ∀ i ∈ univ \ A, η ∈ conn z (x i)}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω' ∂law q := by
    intro x
    rw [lintegral_const_mul _ (hiB x)]
    congr 1
    exact (lintegral_indicator_one (hmB x)).symm
  rw [tsum_congr h2, ← lintegral_tsum fun x => ((hiB x).const_mul _).aemeasurable,
    ← lintegral_const_mul _ (measurable_encard_pow z _)]
  exact lintegral_congr fun ω' => tsum_indicator_mul_indicator z A ω ω'

/-! ### The branch-point recursion -/

/-- **The recursion.** For `m = n + 2`,
`E|K_o|^m ≤ ∑_z τ(o,z) ∑_{A ∋ 0, A ⊊ [m]} E|K_z|^|A| E|K_z|^(m-|A|)`. -/
theorem lintegral_encard_pow_le_branch [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (n : ℕ) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (n + 2) ∂law q ≤
      ∑' z, tau q o z * ∑ A ∈ (univ : Finset (Fin (n + 2))).powerset.filter
          (fun A => 0 ∈ A ∧ (univ \ A).Nonempty),
        (∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ A.card ∂law q) *
          ∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ (n + 2 - A.card) ∂law q := by
  rw [lintegral_encard_pow_eq_tsum]
  refine (ENNReal.tsum_le_tsum fun x => law_forall_conn_le q x univ
    (by rw [Finset.card_univ, Fintype.card_fin]; omega) (Finset.mem_univ 0) o).trans_eq ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [ENNReal.tsum_mul_left, tsum_law_mul_law]

/-! ### All moments (Y84V) -/

/-- **All cluster moments under a uniform susceptibility bound**. If `χ(x) ≤ M` for
every `x`, then for every `m ≥ 1` and every `o`,
`E|K_o|^m ≤ (2m-3)‼ · χ(o) · M^(2m-2)` (with `(2·1-3)‼ = 0‼ = 1` in `ℕ`). -/
theorem lintegral_encard_pow_le [Countable V] (q : Sym2 V → unitInterval) {M : ℝ≥0∞}
    (hM : ∀ x, chi q x ≤ M) (m : ℕ) (hm : 1 ≤ m) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q ≤
      (((2 * m - 3)‼ : ℕ) : ℝ≥0∞) * chi q o * M ^ (2 * m - 2) := by
  induction m using Nat.strong_induction_on generalizing o with
  | _ m ih =>
  obtain ⟨n, rfl⟩ | rfl : (∃ n, m = n + 2) ∨ m = 1 := by
    rcases m with _ | _ | n
    · omega
    · exact Or.inr rfl
    · exact Or.inl ⟨n, rfl⟩
  swap
  · simp [chi]
  refine (lintegral_encard_pow_le_branch q o n).trans ?_
  have hbound : ∀ z, ∀ A ∈ (univ : Finset (Fin (n + 2))).powerset.filter
      (fun A => 0 ∈ A ∧ (univ \ A).Nonempty),
      (∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ A.card ∂law q) *
        ∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ (n + 2 - A.card) ∂law q ≤
      ((((2 * A.card - 3)‼ : ℕ) : ℝ≥0∞) * (((2 * (n + 2 - A.card) - 3)‼ : ℕ) : ℝ≥0∞)) *
        M ^ (2 * (n + 2) - 2) := by
    intro z A hA
    obtain ⟨-, h0, hne⟩ := Finset.mem_filter.1 hA
    have ha1 : 1 ≤ A.card := Finset.card_pos.2 ⟨0, h0⟩
    have ha2 : A.card < n + 2 := by
      have := Finset.card_pos.2 hne
      rw [Finset.card_univ_sdiff, Fintype.card_fin] at this
      omega
    have key : ∀ k, 1 ≤ k → k < n + 2 →
        ∫⁻ ω, ((cluster ω z).encard : ℝ≥0∞) ^ k ∂law q ≤
          (((2 * k - 3)‼ : ℕ) : ℝ≥0∞) * M ^ (2 * k - 1) := by
      intro k hk1 hk2
      refine (ih k hk2 hk1 z).trans ?_
      calc (((2 * k - 3)‼ : ℕ) : ℝ≥0∞) * chi q z * M ^ (2 * k - 2)
          ≤ (((2 * k - 3)‼ : ℕ) : ℝ≥0∞) * M * M ^ (2 * k - 2) :=
            mul_le_mul' (mul_le_mul' le_rfl (hM z)) le_rfl
        _ = (((2 * k - 3)‼ : ℕ) : ℝ≥0∞) * M ^ (2 * k - 1) := by
            rw [mul_assoc, show 2 * k - 1 = (2 * k - 2) + 1 by omega, _root_.pow_succ']
    have hp : M ^ (2 * A.card - 1) * M ^ (2 * (n + 2 - A.card) - 1) =
        M ^ (2 * (n + 2) - 2) := by
      rw [← pow_add]; congr 1; omega
    calc _ ≤ ((((2 * A.card - 3)‼ : ℕ) : ℝ≥0∞) * M ^ (2 * A.card - 1)) *
          ((((2 * (n + 2 - A.card) - 3)‼ : ℕ) : ℝ≥0∞) * M ^ (2 * (n + 2 - A.card) - 1)) :=
          mul_le_mul' (key _ ha1 ha2) (key _ (by omega) (by omega))
      _ = _ := by rw [← hp]; ring
  refine (ENNReal.tsum_le_tsum fun z =>
    mul_le_mul' le_rfl (Finset.sum_le_sum (hbound z))).trans_eq ?_
  rw [ENNReal.tsum_mul_right.symm.trans (tsum_congr fun z => by rw [← Finset.sum_mul])
    |>.symm, ← chi_eq_tsum_tau]
  have hsum := sum_branch_doubleFactorial n
  have hcast : ∑ A ∈ (univ : Finset (Fin (n + 2))).powerset.filter
      (fun A => 0 ∈ A ∧ (univ \ A).Nonempty),
      (((2 * A.card - 3)‼ : ℕ) : ℝ≥0∞) * (((2 * (n + 2 - A.card) - 3)‼ : ℕ) : ℝ≥0∞) =
      (((2 * (n + 2) - 3)‼ : ℕ) : ℝ≥0∞) := by
    rw [← hsum]; push_cast; rfl
  rw [hcast]
  ring

/-- The cluster moment bound with `M = ⨆ x, χ(x)`; finiteness of `M` is not needed. -/
theorem lintegral_encard_pow_le_iSup [Countable V] (q : Sym2 V → unitInterval) (m : ℕ)
    (hm : 1 ≤ m) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q ≤
      (((2 * m - 3)‼ : ℕ) : ℝ≥0∞) * chi q o * (⨆ x, chi q x) ^ (2 * m - 2) :=
  lintegral_encard_pow_le q (fun x => le_iSup (fun x => chi q x) x) m hm o

/-! ### Non-vacuity -/

/-- At `m = 1` the bound is the identity `E|K_o| = χ(o)`. -/
example [Countable V] (q : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ 1 ∂law q = chi q o := by
  simp [chi]

/-- `m = 2` on two vertices: `E|K|² ≤ χ(o) M²`. -/
example (q : Sym2 Bool → unitInterval) :
    ∫⁻ ω, ((cluster ω false).encard : ℝ≥0∞) ^ 2 ∂law q ≤
      chi q false * (⨆ x, chi q x) ^ 2 := by
  simpa using lintegral_encard_pow_le_iSup q 2 (by norm_num) false

/-- `m = 3` on `ℤ` for every profile: `E|K|³ ≤ 3 χ(o) M⁴`. -/
example (q : Sym2 ℤ → unitInterval) :
    ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ 3 ∂law q ≤
      3 * chi q 0 * (⨆ x, chi q x) ^ 4 := by
  have h := lintegral_encard_pow_le_iSup q 3 (by norm_num) 0
  have h3 : ((2 * 3 - 3)‼ : ℕ) = 3 := by decide
  rw [h3] at h
  simpa using h

end PercLib.Percolation.Bond
