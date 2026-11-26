/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21: a minimal model of branching random walk on a discrete state
space (generation configurations as a Markov chain built with the Ionescu-Tulcea theorem) and
the first-moment formulas for its occupation counts. Standard mathematics; no upstream proof is
copied and no Input is introduced.
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# First moments of branching random walk

Let `S` carry the discrete σ-algebra, let `P` be a Markov kernel on `S` and let `ξ` be a
probability measure on `ℕ` (the offspring law) with mean `m = ∫⁻ k, k ∂ξ ∈ [0, ∞]`.
A configuration is a finite list of particle positions. One step replaces every particle at
`z` by an independent `ξ`-distributed number of children, each placed independently according
to `P z`. The generation process started from one particle at `x` is the Markov chain with this
transition kernel (`brwMeasure ξ P x`, a measure on `ℕ → Config S`), and `(ω n).count y` is the
number `N_n(y)` of generation-`n` particles at `y`.

## Main definitions

* `Config S`: finite configurations, with the discrete σ-algebra.
* `iidLaw ν k`, `childLaw ξ P z`, `stepLaw ξ P c`: the laws of `k` i.i.d. positions, of the
  children of one particle at `z`, and of the next generation of a configuration `c`.
* `brwMeasure ξ P x`: the law of the generation process of branching random walk from `x`.

## Main results

* `lintegral_brwMeasure_succ`: the Markov property of the generation process.
* `lintegral_sum_map_brwMeasure`: `E_x ∑_{particles u of generation n} f(u) = mⁿ (Pⁿ f)(x)`.
* `lintegral_count_brwMeasure`: `E_x N_n(y) = mⁿ Pⁿ(x, y)`.
* `lintegral_occupation_brwMeasure`: `E_x ∑ₙ N_n(y) = ∑ₙ mⁿ Pⁿ(x, y)`.
* `lintegral_occupation_brwMeasure_of_mean_eq_one`: at `m = 1` this is the Green function.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace PercLib.Probability.BranchingRandomWalk

/-- A finite configuration of particles: the list of their positions (the order is irrelevant
for counts). It carries the discrete σ-algebra. -/
def Config (S : Type*) : Type _ := List S

variable {S : Type*}

instance : MeasurableSpace (Config S) := ⊤

instance : DiscreteMeasurableSpace (Config S) := ⟨fun _ => trivial⟩

instance [Countable S] : Countable (Config S) := inferInstanceAs (Countable (List S))

/-- The configuration with the given list of positions. -/
def Config.ofList (l : List S) : Config S := l

/-- The list of positions of a configuration. -/
def Config.toList (c : Config S) : List S := c

@[simp]
theorem Config.toList_ofList (l : List S) : (Config.ofList l).toList = l := rfl

@[simp]
theorem Config.ofList_toList (c : Config S) : Config.ofList c.toList = c := rfl

/-- The number of particles of a configuration at `y`. -/
def Config.count [DecidableEq S] (y : S) (c : Config S) : ℕ := c.toList.count y

@[simp]
theorem Config.count_ofList [DecidableEq S] (y : S) (l : List S) :
    (Config.ofList l).count y = l.count y := rfl

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The law of the positions of `k` independent particles, each with law `ν`. -/
def iidLaw (ν : Measure S) : ℕ → Measure (Config S)
  | 0 => Measure.dirac (Config.ofList [])
  | k + 1 => (iidLaw ν k).bind fun c => ν.map fun z => Config.ofList (z :: c.toList)

/-- The law of the children of one particle at `z`: their number has law `ξ` and, given it,
their positions are independent with law `P z`. -/
def childLaw (ξ : Measure ℕ) (P : Kernel S S) (z : S) : Measure (Config S) :=
  ξ.bind fun k => iidLaw (P z) k

/-- The law of the next generation of a configuration: the particles reproduce independently
according to `childLaw`. -/
def stepLaw (ξ : Measure ℕ) (P : Kernel S S) : List S → Measure (Config S)
  | [] => Measure.dirac (Config.ofList [])
  | z :: l => (childLaw ξ P z).bind fun a =>
      (stepLaw ξ P l).map fun b => Config.ofList (a.toList ++ b.toList)

/-- The one-generation transition kernel of branching random walk. -/
def stepKernel (ξ : Measure ℕ) (P : Kernel S S) : Kernel (Config S) (Config S) where
  toFun c := stepLaw ξ P c.toList
  measurable' := Measurable.of_discrete

omit [DiscreteMeasurableSpace S] in
theorem stepKernel_apply (ξ : Measure ℕ) (P : Kernel S S) (c : Config S) :
    stepKernel ξ P c = stepLaw ξ P c.toList := rfl

omit [DiscreteMeasurableSpace S] in
theorem isProbabilityMeasure_iidLaw (ν : Measure S) [IsProbabilityMeasure ν] :
    ∀ k, IsProbabilityMeasure (iidLaw ν k)
  | 0 => by rw [iidLaw]; infer_instance
  | k + 1 => by
    have := isProbabilityMeasure_iidLaw ν k
    rw [iidLaw]
    exact isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
      (ae_of_all _ fun _ => inferInstance)

omit [DiscreteMeasurableSpace S] in
theorem isProbabilityMeasure_childLaw (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S)
    [IsMarkovKernel P] (z : S) : IsProbabilityMeasure (childLaw ξ P z) :=
  isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    (ae_of_all _ fun k => isProbabilityMeasure_iidLaw (P z) k)

omit [DiscreteMeasurableSpace S] in
theorem isProbabilityMeasure_stepLaw (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S)
    [IsMarkovKernel P] : ∀ c, IsProbabilityMeasure (stepLaw ξ P c)
  | [] => by rw [stepLaw]; infer_instance
  | z :: l => by
    have := isProbabilityMeasure_stepLaw ξ P l
    have := isProbabilityMeasure_childLaw ξ P z
    rw [stepLaw]
    exact isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
      (ae_of_all _ fun _ => inferInstance)

instance (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S) [IsMarkovKernel P] :
    IsMarkovKernel (stepKernel ξ P) :=
  ⟨fun c => isProbabilityMeasure_stepLaw ξ P c.toList⟩

/-- The transition kernel from the history up to generation `n` (which only looks at
generation `n`). -/
def genKernel (ξ : Measure ℕ) (P : Kernel S S) (n : ℕ) :
    Kernel (Π _ : Iic n, Config S) (Config S) :=
  (stepKernel ξ P).comap (fun h => h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (genKernel ξ P n) := by
  unfold genKernel; infer_instance

/-- **Branching random walk** from one particle at `x`: the law of the sequence of generation
configurations, the Markov chain with transition kernel `stepKernel ξ P` started at `[x]`. -/
def brwMeasure (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : Measure (ℕ → Config S) :=
  Kernel.traj (X := fun _ => Config S) (genKernel ξ P) 0 (fun _ => Config.ofList [x])

instance (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    IsProbabilityMeasure (brwMeasure ξ P x) := by
  unfold brwMeasure; exact IsMarkovKernel.isProbabilityMeasure _

/-! ### First moments of one step -/

theorem lintegral_sum_map_iidLaw (ν : Measure S) [IsProbabilityMeasure ν] (f : S → ℝ≥0∞) :
    ∀ k : ℕ, ∫⁻ c, (c.toList.map f).sum ∂iidLaw ν k = k * ∫⁻ z, f z ∂ν
  | 0 => by simp [iidLaw, lintegral_dirac]
  | k + 1 => by
    have := isProbabilityMeasure_iidLaw ν k
    rw [iidLaw, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable]
    simp_rw [lintegral_map Measurable.of_discrete Measurable.of_discrete,
      Config.toList_ofList, List.map_cons, List.sum_cons]
    simp_rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_sum_map_iidLaw ν f k]
    push_cast
    ring

theorem lintegral_sum_map_childLaw (ξ : Measure ℕ) (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ≥0∞) (z : S) :
    ∫⁻ c, (c.toList.map f).sum ∂childLaw ξ P z =
      (∫⁻ k, (k : ℝ≥0∞) ∂ξ) * ∫⁻ y, f y ∂P z := by
  rw [childLaw, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  simp_rw [lintegral_sum_map_iidLaw]
  exact lintegral_mul_const _ Measurable.of_discrete

theorem lintegral_sum_map_stepLaw (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S)
    [IsMarkovKernel P] (f : S → ℝ≥0∞) :
    ∀ c : List S, ∫⁻ b, (b.toList.map f).sum ∂stepLaw ξ P c =
      (c.map fun z => (∫⁻ k, (k : ℝ≥0∞) ∂ξ) * ∫⁻ y, f y ∂P z).sum
  | [] => by simp [stepLaw, lintegral_dirac]
  | z :: l => by
    have := isProbabilityMeasure_stepLaw ξ P l
    have := isProbabilityMeasure_childLaw ξ P z
    rw [stepLaw, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable]
    simp_rw [lintegral_map Measurable.of_discrete Measurable.of_discrete,
      Config.toList_ofList, List.map_append, List.sum_append]
    simp_rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_sum_map_stepLaw ξ P f l]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_sum_map_childLaw, List.map_cons, List.sum_cons]

/-! ### The generation process -/

variable {ξ : Measure ℕ} [IsProbabilityMeasure ξ] {P : Kernel S S} [IsMarkovKernel P]

omit [DiscreteMeasurableSpace S] in
/-- Generation `0` is the single particle at `x`. -/
theorem lintegral_brwMeasure_zero (x : S) (g : Config S → ℝ≥0∞) :
    ∫⁻ ω, g (ω 0) ∂brwMeasure ξ P x = g (Config.ofList [x]) := by
  have hm : Measurable fun ω : ℕ → Config S => g (ω 0) :=
    (Measurable.of_discrete (f := g)).comp (measurable_pi_apply 0)
  unfold brwMeasure
  rw [Kernel.lintegral_traj _ hm]
  simp [Function.updateFinset]

omit [DiscreteMeasurableSpace S] in
/-- **Markov property** of the generation process: given the history up to generation `n`,
generation `n + 1` has law `stepLaw ξ P (ω n)`. -/
theorem lintegral_brwMeasure_succ [Countable S] (x : S) (n : ℕ)
    (G : (Π _ : Iic n, Config S) → Config S → ℝ≥0∞) :
    ∫⁻ ω, G (frestrictLe n ω) (ω (n + 1)) ∂brwMeasure ξ P x =
      ∫⁻ ω, ∫⁻ c, G (frestrictLe n ω) c ∂stepLaw ξ P (ω n).toList ∂brwMeasure ξ P x := by
  have hG : Measurable (Function.uncurry G) := measurable_of_countable _
  have hr := measurable_frestrictLe (X := fun _ : ℕ => Config S) n
  have m1 : Measurable fun ω : ℕ → Config S => G (frestrictLe n ω) (ω (n + 1)) :=
    hG.comp (hr.prodMk (measurable_pi_apply (n + 1)))
  have m2 : Measurable fun ω : ℕ → Config S =>
      ∫⁻ c, G (frestrictLe n ω) c ∂stepLaw ξ P (ω n).toList :=
    (measurable_of_countable (fun p : (Π _ : Iic n, Config S) × Config S =>
      ∫⁻ c, G p.1 c ∂stepLaw ξ P p.2.toList)).comp (hr.prodMk (measurable_pi_apply n))
  unfold brwMeasure
  rw [← Kernel.traj_comp_partialTraj (Nat.zero_le n), Kernel.lintegral_comp _ _ _ m1,
    Kernel.lintegral_comp _ _ _ m2]
  refine lintegral_congr fun h => ?_
  rw [Kernel.lintegral_traj h m1, Kernel.lintegral_traj h m2]
  have e1 : ∀ ω : ℕ → Config S, frestrictLe n (Function.updateFinset ω (Iic n) h) = h := by
    intro ω; funext i; simp [frestrictLe, Function.updateFinset, i.2]
  have e2 : ∀ ω : ℕ → Config S, Function.updateFinset ω (Iic n) h (n + 1) = ω (n + 1) := by
    intro ω; simp [Function.updateFinset]
  have e3 : ∀ ω : ℕ → Config S,
      Function.updateFinset ω (Iic n) h n = h ⟨n, mem_Iic.2 le_rfl⟩ := by
    intro ω; simp [Function.updateFinset]
  simp only [e1, e2, e3]
  rw [lintegral_const, measure_univ, mul_one,
    ← lintegral_map (f := G h) Measurable.of_discrete (measurable_pi_apply (n + 1)),
    ← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
  rfl

omit [DiscreteMeasurableSpace S] in
/-- One-generation step for a functional of the current generation. -/
theorem lintegral_brwMeasure_succ' [Countable S] (x : S) (n : ℕ) (g : Config S → ℝ≥0∞) :
    ∫⁻ ω, g (ω (n + 1)) ∂brwMeasure ξ P x =
      ∫⁻ ω, ∫⁻ c, g c ∂stepLaw ξ P (ω n).toList ∂brwMeasure ξ P x :=
  lintegral_brwMeasure_succ x n fun _ c => g c

/-! ### First moments -/

/-- `E_x ∑_{u ∈ generation n} f(position of u) = mⁿ ∫ f d(Pⁿ x)`. -/
theorem lintegral_sum_map_brwMeasure [Countable S] (x : S) (n : ℕ) (f : S → ℝ≥0∞) :
    ∫⁻ ω, ((ω n).toList.map f).sum ∂brwMeasure ξ P x =
      (∫⁻ k, (k : ℝ≥0∞) ∂ξ) ^ n * ∫⁻ y, f y ∂(P ^ n) x := by
  induction n generalizing f with
  | zero =>
    rw [lintegral_brwMeasure_zero x (fun c => (c.toList.map f).sum)]
    rw [pow_zero, pow_zero, one_mul]
    change _ = ∫⁻ y, f y ∂(Kernel.id x)
    simp [Kernel.id_apply, lintegral_dirac]
  | succ n ih =>
    rw [lintegral_brwMeasure_succ' x n (fun c => (c.toList.map f).sum)]
    simp_rw [lintegral_sum_map_stepLaw]
    rw [ih, add_comm n 1, Kernel.pow_add, pow_one, Kernel.lintegral_comp _ _ _
      Measurable.of_discrete, lintegral_const_mul _ Measurable.of_discrete, pow_add, pow_one]
    ring

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem natCast_count_eq_sum_map [DecidableEq S] (y : S) :
    ∀ l : List S, (l.count y : ℝ≥0∞) = (l.map (({y} : Set S).indicator 1)).sum
  | [] => by simp
  | z :: l => by
    rw [List.count_cons, List.map_cons, List.sum_cons, ← natCast_count_eq_sum_map y l]
    by_cases h : z = y <;> simp [h, add_comm]

/-- **First moment of the generation counts**: `E_x N_n(y) = mⁿ Pⁿ(x, y)`. -/
theorem lintegral_count_brwMeasure [Countable S] [DecidableEq S] (x y : S) (n : ℕ) :
    ∫⁻ ω, ((ω n).count y : ℝ≥0∞) ∂brwMeasure ξ P x =
      (∫⁻ k, (k : ℝ≥0∞) ∂ξ) ^ n * (P ^ n) x {y} := by
  simp_rw [Config.count, natCast_count_eq_sum_map y]
  rw [lintegral_sum_map_brwMeasure, lintegral_indicator_one (measurableSet_singleton y)]

/-- **First moment of the occupation count**: `E_x ∑ₙ N_n(y) = ∑ₙ mⁿ Pⁿ(x, y)`. -/
theorem lintegral_occupation_brwMeasure [Countable S] [DecidableEq S] (x y : S) :
    ∫⁻ ω, ∑' n, ((ω n).count y : ℝ≥0∞) ∂brwMeasure ξ P x =
      ∑' n, (∫⁻ k, (k : ℝ≥0∞) ∂ξ) ^ n * (P ^ n) x {y} := by
  have hm : ∀ n, AEMeasurable (fun ω : ℕ → Config S => ((ω n).count y : ℝ≥0∞))
      (brwMeasure ξ P x) := fun n =>
    ((Measurable.of_discrete (f := fun c : Config S => (c.count y : ℝ≥0∞))).comp
      (measurable_pi_apply n)).aemeasurable
  rw [lintegral_tsum hm]
  simp_rw [lintegral_count_brwMeasure]

/-- At criticality `m = 1` the expected occupation is the Green function `∑ₙ Pⁿ(x, y)`. -/
theorem lintegral_occupation_brwMeasure_of_mean_eq_one [Countable S] [DecidableEq S]
    (hm : ∫⁻ k, (k : ℝ≥0∞) ∂ξ = 1) (x y : S) :
    ∫⁻ ω, ∑' n, ((ω n).count y : ℝ≥0∞) ∂brwMeasure ξ P x = ∑' n, (P ^ n) x {y} := by
  simp [lintegral_occupation_brwMeasure, hm]

end PercLib.Probability.BranchingRandomWalk
