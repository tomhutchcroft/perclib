/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Cluster applications of the mass-transport principle on a countable group. New for this
project; no upstream proof is copied. Mathematical reference: the mass-transport principle
for invariant random graphs on groups (e.g. Lyons–Peres, *Probability on Trees and Networks*,
Ch. 8).
-/
module

public import PercLib.Probability.MassTransport
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.RootIndependence

/-!
# Mass transport inside clusters

A countable group `Γ` acts on a measure space `(Ω, μ)` by measure-preserving maps `act g`, and
`G : Ω → Config Γ` is a measurable random graph on `Γ` that is equivariant:
`G (act g ω) = Sym2.map (g * ·) '' G ω`. The space `Ω` may carry auxiliary marks.

## Main results

* `lintegral_indicator_cluster_finite_eq_average`: for an equivariant `f : Ω → Γ → [0, ∞]`,
  `E[f(ω, 1); |K_1| < ∞] = E[|K_1|⁻¹ ∑_{x ∈ K_1} f(ω, x); |K_1| < ∞]`; the bond-percolation
  instance is `lintegral_indicator_cluster_finite_eq_average_law`.
* `measure_mem_selection_eq_lintegral_inv_encard`: an equivariant rule selecting exactly one
  vertex of every finite cluster (and none in infinite clusters) selects `1` with probability
  `E[|K_1|⁻¹; |K_1| < ∞]`.
* `ae_notMem_of_cluster_infinite`: an equivariant set meeting each infinite cluster in at most
  one vertex almost surely meets no infinite cluster.
* `not_exists_selection_of_measure_cluster_infinite_ne_zero`: if infinite clusters occur with
  positive probability, no equivariant rule selects exactly one vertex of each of them.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

open PercLib.Probability

section Translate

variable {Γ : Type*} [Group Γ]

/-- Cluster membership is carried along left multiplication. -/
theorem mem_cluster_image_mul_left_iff (ω : Config Γ) (g x y : Γ) :
    g * y ∈ cluster (Sym2.map (g * ·) '' ω) (g * x) ↔ y ∈ cluster ω x :=
  image_mem_conn_iff (Equiv.mulLeft g) ω x y

/-- Cluster volumes are carried along left multiplication. -/
theorem encard_cluster_image_mul_left (ω : Config Γ) (g x : Γ) :
    (cluster (Sym2.map (g * ·) '' ω) (g * x)).encard = (cluster ω x).encard :=
  encard_cluster_image (Equiv.mulLeft g) ω x

/-- Infinite clusters are carried along left multiplication. -/
theorem cluster_image_mul_left_infinite_iff (ω : Config Γ) (g x : Γ) :
    (cluster (Sym2.map (g * ·) '' ω) (g * x)).Infinite ↔ (cluster ω x).Infinite :=
  cluster_image_infinite_iff (Equiv.mulLeft g) ω x

/-- Finite clusters are carried along left multiplication. -/
theorem cluster_image_mul_left_finite_iff (ω : Config Γ) (g x : Γ) :
    (cluster (Sym2.map (g * ·) '' ω) (g * x)).Finite ↔ (cluster ω x).Finite := by
  rw [← Set.not_infinite, ← Set.not_infinite, cluster_image_mul_left_infinite_iff]

end Translate

/-- A sum of a constant over a set, written with an indicator. -/
theorem tsum_indicator_const_eq_encard_mul {α : Type*} (s : Set α) (c : ℝ≥0∞) :
    ∑' y, s.indicator (fun _ => c) y = s.encard * c := by
  rw [← tsum_subtype s (fun _ => c), ENNReal.tsum_set_const]

variable {Γ Ω : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Averaging over finite clusters.** For an invariant law with an equivariant random graph
`G` and an equivariant `f : Ω → Γ → [0, ∞]`, the expectation of `f(ω, 1)` on `{|K_1| < ∞}`
equals the expectation of the cluster average `|K_1|⁻¹ ∑_{x ∈ K_1} f(ω, x)` on the same
event. -/
theorem lintegral_indicator_cluster_finite_eq_average
    (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (G : Ω → Config Γ) (hG : Measurable G)
    (hGact : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω)
    (f : Ω → Γ → ℝ≥0∞) (hf : ∀ x, Measurable fun ω => f ω x)
    (hfact : ∀ g ω x, f (act g ω) (g * x) = f ω x) :
    ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator (fun ω => f ω 1) ω ∂μ =
      ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator
        (fun ω => ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹ *
          ∑' x, (cluster (G ω) 1).indicator (f ω) x) ω ∂μ := by
  classical
  set t : Ω → Γ → Γ → ℝ≥0∞ := fun ω x y =>
    if (cluster (G ω) x).Finite ∧ y ∈ cluster (G ω) x then
      f ω x * ((cluster (G ω) x).encard : ℝ≥0∞)⁻¹ else 0 with ht
  have hmeas : ∀ x y, Measurable fun ω => t ω x y := by
    intro x y
    have h1 : MeasurableSet {ω | (cluster (G ω) x).Finite ∧ y ∈ cluster (G ω) x} := by
      have h := ((measurableSet_cluster_infinite x).compl.preimage hG).inter
        ((measurableSet_conn x y).preimage hG)
      convert h using 1
      ext ω
      simp [Set.not_infinite, mem_cluster_iff]
    refine Measurable.ite h1 ((hf x).mul ?_) measurable_const
    exact (Measurable.of_discrete (f := fun n : ℕ∞ => ((n : ℝ≥0∞))⁻¹)).comp
      ((measurable_encard_cluster x).comp hG)
  have hinv : ∀ ω g x y, t (act g ω) (g * x) (g * y) = t ω x y := by
    intro ω g x y
    simp only [ht, hGact, hfact, cluster_image_mul_left_finite_iff,
      mem_cluster_image_mul_left_iff, encard_cluster_image_mul_left]
  have hout : ∀ ω, ∑' y, t ω 1 y =
      {ω | (cluster (G ω) 1).Finite}.indicator (fun ω => f ω 1) ω := by
    intro ω
    by_cases hfin : (cluster (G ω) 1).Finite
    · rw [Set.indicator_of_mem (show ω ∈ {ω | (cluster (G ω) 1).Finite} from hfin)]
      have hne0 : ((cluster (G ω) 1).encard : ℝ≥0∞) ≠ 0 := by
        simpa using (Set.nonempty_of_mem (mem_cluster_self (G ω) 1)).encard_pos.ne'
      have hnetop : ((cluster (G ω) 1).encard : ℝ≥0∞) ≠ ⊤ := by
        simpa using hfin.encard_lt_top.ne
      calc ∑' y, t ω 1 y = ∑' y, (cluster (G ω) 1).indicator
            (fun _ => f ω 1 * ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹) y := by
            congr 1
            funext y
            by_cases hy : y ∈ cluster (G ω) 1 <;> simp [ht, hfin, hy]
        _ = f ω 1 := by
            rw [tsum_indicator_const_eq_encard_mul, mul_comm, mul_assoc,
              ENNReal.inv_mul_cancel hne0 hnetop, mul_one]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | (cluster (G ω) 1).Finite} from hfin)]
      simp [ht, hfin]
  have hin : ∀ ω, ∑' x, t ω x 1 = {ω | (cluster (G ω) 1).Finite}.indicator
      (fun ω => ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹ *
        ∑' x, (cluster (G ω) 1).indicator (f ω) x) ω := by
    intro ω
    have hpt : ∀ x, t ω x 1 = if (cluster (G ω) 1).Finite ∧ x ∈ cluster (G ω) 1 then
        f ω x * ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹ else 0 := by
      intro x
      by_cases hx : x ∈ cluster (G ω) 1
      · have hK : cluster (G ω) x = cluster (G ω) 1 := (cluster_eq_of_mem_conn hx).symm
        simp only [ht, hK, mem_cluster_self, hx, and_true]
      · have h1 : (1 : Γ) ∉ cluster (G ω) x := fun h => hx h.symm
        simp [ht, h1, hx]
    simp_rw [hpt]
    by_cases hfin : (cluster (G ω) 1).Finite
    · rw [Set.indicator_of_mem (show ω ∈ {ω | (cluster (G ω) 1).Finite} from hfin), mul_comm,
        ← ENNReal.tsum_mul_right]
      congr 1
      funext x
      by_cases hx : x ∈ cluster (G ω) 1 <;> simp [hfin, hx]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | (cluster (G ω) 1).Finite} from hfin)]
      simp [hfin]
  exact (lintegral_congr fun ω => (hout ω).symm).trans
    ((lintegral_mass_transport act hact t hmeas hinv).trans (lintegral_congr hin))

/-- Finite-cluster averaging for bond percolation with a left-invariant profile on a countable
group (the instance `Ω = Config Γ`, `G = id`). -/
theorem lintegral_indicator_cluster_finite_eq_average_law (q : Sym2 Γ → unitInterval)
    (hq : ∀ g x y : Γ, q s(g * x, g * y) = q s(x, y))
    (f : Config Γ → Γ → ℝ≥0∞) (hf : ∀ x, Measurable fun ω => f ω x)
    (hfact : ∀ g ω x, f (Sym2.map (g * ·) '' ω) (g * x) = f ω x) :
    ∫⁻ ω, {ω | (cluster ω 1).Finite}.indicator (fun ω => f ω 1) ω ∂law q =
      ∫⁻ ω, {ω | (cluster ω 1).Finite}.indicator
        (fun ω => ((cluster ω 1).encard : ℝ≥0∞)⁻¹ *
          ∑' x, (cluster ω 1).indicator (f ω) x) ω ∂law q :=
  lintegral_indicator_cluster_finite_eq_average (fun g ω => Sym2.map (g * ·) '' ω)
    (measurePreserving_image_sym2Map_mul_left q hq) id measurable_id (fun _ _ => rfl) f hf hfact

/-- **Selecting one vertex per finite cluster.** If an equivariant measurable rule `S` selects
exactly one vertex of every finite cluster and no vertex of an infinite cluster, then
`P(1 ∈ S) = E[|K_1|⁻¹; |K_1| < ∞]`. -/
theorem measure_mem_selection_eq_lintegral_inv_encard
    (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (G : Ω → Config Γ) (hG : Measurable G)
    (hGact : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω)
    (S : Ω → Set Γ) (hS : ∀ x, MeasurableSet {ω | x ∈ S ω})
    (hSact : ∀ g ω x, g * x ∈ S (act g ω) ↔ x ∈ S ω)
    (hS_fin : ∀ ω x, (cluster (G ω) x).Finite → ∃! y, y ∈ cluster (G ω) x ∧ y ∈ S ω)
    (hS_inf : ∀ ω x, (cluster (G ω) x).Infinite → x ∉ S ω) :
    μ {ω | (1 : Γ) ∈ S ω} = ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator
      (fun ω => ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹) ω ∂μ := by
  classical
  have h := lintegral_indicator_cluster_finite_eq_average act hact G hG hGact
    (fun ω x => {ω | x ∈ S ω}.indicator 1 ω) (fun x => measurable_one.indicator (hS x))
    (by intro g ω x; simp only [Set.indicator_apply, Set.mem_ofPred_eq, hSact, Pi.one_apply])
  rw [← lintegral_indicator_one (hS 1)]
  refine (lintegral_congr fun ω => ?_).trans (h.trans (lintegral_congr fun ω => ?_))
  · by_cases h1 : (1 : Γ) ∈ S ω
    · have hfin : (cluster (G ω) 1).Finite := by
        by_contra hinf
        exact hS_inf ω 1 hinf h1
      simp [Set.indicator_apply, h1, hfin]
    · simp [Set.indicator_apply, h1]
  · by_cases hfin : (cluster (G ω) 1).Finite
    · obtain ⟨y, ⟨hyK, hyS⟩, huniq⟩ := hS_fin ω 1 hfin
      have hsum : ∑' x, (cluster (G ω) 1).indicator
          (fun x => {ω | x ∈ S ω}.indicator (1 : Ω → ℝ≥0∞) ω) x = 1 := by
        have : (fun x => (cluster (G ω) 1).indicator
            (fun x => {ω | x ∈ S ω}.indicator (1 : Ω → ℝ≥0∞) ω) x) =
            fun x => if x = y then 1 else 0 := by
          funext x
          by_cases hxy : x = y
          · subst hxy
            simp [Set.indicator_apply, hyK, hyS]
          · have : ¬ (x ∈ cluster (G ω) 1 ∧ x ∈ S ω) := fun hx => hxy (huniq x hx)
            simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, hxy, ite_false]
            split_ifs <;> tauto
        rw [this, tsum_ite_eq]
      rw [Set.indicator_of_mem (show ω ∈ {ω | (cluster (G ω) 1).Finite} from hfin),
        Set.indicator_of_mem (show ω ∈ {ω | (cluster (G ω) 1).Finite} from hfin), hsum,
        mul_one]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | (cluster (G ω) 1).Finite} from hfin),
        Set.indicator_of_notMem (show ω ∉ {ω | (cluster (G ω) 1).Finite} from hfin)]

/-- **No equivariant representative of an infinite cluster.** Under a finite invariant measure,
an equivariant measurable set `R` that meets every infinite cluster in at most one vertex
almost surely contains no vertex of any infinite cluster. -/
theorem ae_notMem_of_cluster_infinite [IsFiniteMeasure μ]
    (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (G : Ω → Config Γ) (hG : Measurable G)
    (hGact : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω)
    (R : Ω → Set Γ) (hR : ∀ x, MeasurableSet {ω | x ∈ R ω})
    (hRact : ∀ g ω x, g * x ∈ R (act g ω) ↔ x ∈ R ω)
    (hR_inf : ∀ ω x, (cluster (G ω) x).Infinite → (R ω ∩ cluster (G ω) x).Subsingleton) :
    ∀ᵐ ω ∂μ, ∀ x, (cluster (G ω) x).Infinite → x ∉ R ω := by
  classical
  set E : Γ → Set Ω := fun x => {ω | x ∈ R ω ∧ (cluster (G ω) x).Infinite} with hE
  have hEmeas : ∀ x, MeasurableSet (E x) := fun x =>
    (hR x).inter ((measurableSet_cluster_infinite x).preimage hG)
  set t : Ω → Γ → Γ → ℝ≥0∞ := fun ω x y =>
    if (cluster (G ω) x).Infinite ∧ y ∈ cluster (G ω) x ∧ y ∈ R ω then 1 else 0 with ht
  have hmeas : ∀ x y, Measurable fun ω => t ω x y := fun x y =>
    Measurable.ite (((measurableSet_cluster_infinite x).preimage hG).inter
      (((measurableSet_conn x y).preimage hG).inter (hR y))) measurable_const measurable_const
  have hinv : ∀ ω g x y, t (act g ω) (g * x) (g * y) = t ω x y := by
    intro ω g x y
    simp only [ht, hGact, hRact, cluster_image_mul_left_infinite_iff,
      mem_cluster_image_mul_left_iff]
  have hout : ∀ ω, ∑' y, t ω 1 y ≤ 1 := by
    intro ω
    by_cases hinf : (cluster (G ω) 1).Infinite
    · calc ∑' y, t ω 1 y = ∑' y, (R ω ∩ cluster (G ω) 1).indicator (fun _ => (1 : ℝ≥0∞)) y := by
            congr 1
            funext y
            by_cases hy : y ∈ cluster (G ω) 1 <;> by_cases hyR : y ∈ R ω <;>
              simp [ht, hinf, hy, hyR]
        _ = (R ω ∩ cluster (G ω) 1).encard := by
            rw [tsum_indicator_const_eq_encard_mul, mul_one]
        _ ≤ 1 := by
            exact_mod_cast Set.encard_le_one_iff_subsingleton.mpr (hR_inf ω 1 hinf)
    · simp [ht, hinf]
  have hin : ∀ ω, ∑' x, t ω x 1 = (E 1).indicator (fun _ => ⊤) ω := by
    intro ω
    have hpt : ∀ x, t ω x 1 =
        if (1 ∈ R ω ∧ (cluster (G ω) 1).Infinite) ∧ x ∈ cluster (G ω) 1 then 1 else 0 := by
      intro x
      by_cases hx : x ∈ cluster (G ω) 1
      · have hK : cluster (G ω) x = cluster (G ω) 1 := (cluster_eq_of_mem_conn hx).symm
        simp only [ht, hK, mem_cluster_self, hx, true_and, and_true]
        by_cases h1 : (1 : Γ) ∈ R ω <;> simp [h1]
      · have h1 : (1 : Γ) ∉ cluster (G ω) x := fun h => hx h.symm
        simp [ht, h1, hx]
    simp_rw [hpt]
    by_cases hω : (1 : Γ) ∈ R ω ∧ (cluster (G ω) 1).Infinite
    · rw [Set.indicator_of_mem (show ω ∈ E 1 from hω)]
      have : (fun x => if ((1 : Γ) ∈ R ω ∧ (cluster (G ω) 1).Infinite) ∧
          x ∈ cluster (G ω) 1 then (1 : ℝ≥0∞) else 0) =
          (cluster (G ω) 1).indicator (fun _ => 1) := by
        funext x
        simp [Set.indicator_apply, hω]
      rw [this, tsum_indicator_const_eq_encard_mul, mul_one, hω.2.encard_eq]
      rfl
    · rw [Set.indicator_of_notMem (show ω ∉ E 1 from hω)]
      simp [hω]
  have hE1 : μ (E 1) = 0 := by
    have hle : ∫⁻ ω, ∑' x, t ω x 1 ∂μ ≤ μ Set.univ := by
      rw [← lintegral_mass_transport act hact t hmeas hinv, ← lintegral_one]
      exact lintegral_mono hout
    rw [lintegral_congr hin, lintegral_indicator_const (hEmeas 1)] at hle
    by_contra h
    rw [ENNReal.top_mul h] at hle
    exact measure_ne_top μ _ (top_le_iff.mp hle)
  have hpre : ∀ x, act x ⁻¹' E x = E 1 := by
    intro x
    ext ω
    have h1 := hRact x ω 1
    have h2 := cluster_image_mul_left_infinite_iff (G ω) x 1
    rw [mul_one] at h1 h2
    simp only [hE, Set.mem_preimage, Set.mem_ofPred_eq, hGact, h1, h2]
  have hEx : ∀ x, μ (E x) = 0 := fun x => by
    rw [← (hact x).measure_preimage (hEmeas x).nullMeasurableSet, hpre, hE1]
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (hEx x)
  simp only [Set.mem_ofPred_eq, not_imp, not_not] at hω
  exact ⟨hω.2, hω.1⟩

/-- If infinite clusters occur with positive measure (under a finite invariant measure), no
equivariant measurable rule selects exactly one vertex of every infinite cluster. -/
theorem not_exists_selection_of_measure_cluster_infinite_ne_zero [IsFiniteMeasure μ]
    (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (G : Ω → Config Γ) (hG : Measurable G)
    (hGact : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω)
    (h : μ {ω | ∃ x, (cluster (G ω) x).Infinite} ≠ 0) :
    ¬ ∃ R : Ω → Set Γ, (∀ x, MeasurableSet {ω | x ∈ R ω}) ∧
      (∀ g ω x, g * x ∈ R (act g ω) ↔ x ∈ R ω) ∧
      ∀ ω x, (cluster (G ω) x).Infinite → ∃! y, y ∈ cluster (G ω) x ∧ y ∈ R ω := by
  rintro ⟨R, hR, hRact, hRone⟩
  have hsub : ∀ ω x, (cluster (G ω) x).Infinite → (R ω ∩ cluster (G ω) x).Subsingleton := by
    intro ω x hx a ha b hb
    obtain ⟨y, _, hy⟩ := hRone ω x hx
    exact (hy a ⟨ha.2, ha.1⟩).trans (hy b ⟨hb.2, hb.1⟩).symm
  have hae := ae_notMem_of_cluster_infinite act hact G hG hGact R hR hRact hsub
  apply h
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hae)
  obtain ⟨x, hx⟩ := hω
  obtain ⟨y, ⟨hyK, hyR⟩, -⟩ := hRone ω x hx
  rw [Set.mem_ofPred_eq]
  intro hall
  have hKy : cluster (G ω) y = cluster (G ω) x := (cluster_eq_of_mem_conn hyK).symm
  exact hall y (hKy ▸ hx) hyR

end PercLib.Percolation.Bond
