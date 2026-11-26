/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs (the sibling-block recursion), written on 2026-11-20. No upstream proof is copied and no
definition is added.
-/
module

public import PercLib.Models.HierarchicalAmplificationStep
public import PercLib.Percolation.Bond.CrossEdge
public import PercLib.Percolation.Bond.Tightness.TruncatedMean
public import PercLib.Percolation.Bond.WindowPartition

/-!
# The sibling-block recursion (Hutchcroft, arXiv:2103.17013v1, Lemma 2.8)

On the hierarchical lattice `ℕ →₀ (Fin d → ZMod L)`, write `h z = z.support.sup Nat.succ`,
`Λ_m = {h ≤ m}` and `q_m` for `q_β = intensityProfile J β` restricted to the pairs inside
`Λ_m`. Let `M_n` be the quantile `tightnessScale q_n Λ_n` and
`a_n = E_{q_n} |K_0 ∩ Λ_n|`. If `M_n² ≤ (A/β) L^{(d+α)n}`, then

`∑_{x ∈ Λ_{n+1} \ Λ_n} P_{q_{n+1}}(0 ↔ x) ≥ k β L^{-αn} a_n²`,
`k = (c/4) e^{-T} L^{-(d+α)}`, `T = c A 99² L^{-(d+α)}`

(`sum_shell_tau_ge`). For each `x` of the shell, the level-`n` block `x + Λ_n` of `x` is
disjoint from `Λ_n`; the cluster `C` of `0` in `Λ_n` and the cluster `D` of `x` in `x + Λ_n`
are independent, and `D` has the law of `C` translated. Every pair between the two blocks is
open with probability at least `1 - e^{-r}`, `r = β c L^{-(d+α)(n+1)}`, so by the
cross-edge estimate (`lintegral_crossEdge_ge_exp`) and the truncation at `99 M_n`
(`lintegral_clusterIntersection_div_two_le`)
`P(0 ↔ x) ≥ E[1 - e^{-r|C||D|}] ≥ r e^{-T} E[min(|C|, 99M_n)]² ≥ r e^{-T} a_n² / 4`.
The shell has at least `L^{dn}` points.

Auxiliary statements: the restriction transfer `lintegral_comp_inter_eq`, the translation
invariance `law_restrict_level_ball_map_addLeft` and the inequality
`mul_exp_neg_mul_min_le_one_sub_exp`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models

open PercLib.Percolation.Bond

/-- `1 - e^{-r a b} ≥ r e^{-T} min(a,t) min(b,t)` when `r ≥ 0` and `r t² ≤ T`. -/
theorem mul_exp_neg_mul_min_le_one_sub_exp {r T : ℝ} (hr : 0 ≤ r) {a b t : ℕ}
    (ht : r * (t : ℝ) ^ 2 ≤ T) :
    r * Real.exp (-T) * (((min a t : ℕ) : ℝ) * ((min b t : ℕ) : ℝ)) ≤
      1 - Real.exp (-(r * a * b)) := by
  have ha1 : ((min a t : ℕ) : ℝ) ≤ t := by exact_mod_cast min_le_right a t
  have hb1 : ((min b t : ℕ) : ℝ) ≤ t := by exact_mod_cast min_le_right b t
  have ha2 : ((min a t : ℕ) : ℝ) ≤ a := by exact_mod_cast min_le_left a t
  have hb2 : ((min b t : ℕ) : ℝ) ≤ b := by exact_mod_cast min_le_left b t
  have ha0 : (0 : ℝ) ≤ ((min a t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ ((min b t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs0 : 0 ≤ r * (((min a t : ℕ) : ℝ) * ((min b t : ℕ) : ℝ)) := by positivity
  have hsT : r * (((min a t : ℕ) : ℝ) * ((min b t : ℕ) : ℝ)) ≤ T := by
    refine le_trans ?_ ht
    have := mul_le_mul ha1 hb1 hb0 (Nat.cast_nonneg t)
    nlinarith
  have hsab : r * (((min a t : ℕ) : ℝ) * ((min b t : ℕ) : ℝ)) ≤ r * a * b := by
    have := mul_le_mul ha2 hb2 hb0 (Nat.cast_nonneg a)
    nlinarith
  set s := r * (((min a t : ℕ) : ℝ) * ((min b t : ℕ) : ℝ)) with hs
  have h1 : s * Real.exp (-s) ≤ 1 - Real.exp (-s) := by
    have h := Real.add_one_le_exp s
    have he : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-s)
    nlinarith
  calc r * Real.exp (-T) * (((min a t : ℕ) : ℝ) * ((min b t : ℕ) : ℝ))
      = s * Real.exp (-T) := by rw [hs]; ring
    _ ≤ s * Real.exp (-s) := by
        gcongr
    _ ≤ 1 - Real.exp (-s) := h1
    _ ≤ 1 - Real.exp (-(r * a * b)) := by
        gcongr

/-- **Restriction transfer.** The expectation of a function of `ω ∩ W` under `law p` is its
expectation under the law of `p` restricted to `W`. -/
theorem lintegral_comp_inter_eq {V : Type*} (p : Sym2 V → unitInterval) (W : Set (Sym2 V))
    [DecidablePred (· ∈ W)] {f : Config V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (ω ∩ W) ∂law p = ∫⁻ ω, f ω ∂law (fun e => if e ∈ W then p e else 0) := by
  unfold law
  rw [← PercLib.Probability.prodBernoulli_map_inter p W, lintegral_map hf (by fun_prop)]

section Hierarchical

variable {d L : ℕ}

open Classical in
/-- **Translation invariance of a ball-restricted law.** For a translation-invariant kernel and
`x` in the level-`m` ball, translating by `x` preserves the law of `q_β` restricted to the
pairs inside that ball. -/
theorem law_restrict_level_ball_map_addLeft (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)) (β : ℝ≥0) (m : ℕ)
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ m) :
    (law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}.sym2
        then intensityProfile J β e else 0)).map
      (fun ω => Sym2.map (Equiv.addLeft x) '' ω) =
      law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m}.sym2
        then intensityProfile J β e else 0) := by
  unfold law
  refine PercLib.Probability.prodBernoulli_map_image_sym2_invariant _ _ fun e => ?_
  have hiff : ∀ z : ℕ →₀ (Fin d → ZMod L),
      (x + z).support.sup Nat.succ ≤ m ↔ z.support.sup Nat.succ ≤ m := by
    intro z
    constructor
    · intro h
      have := level_sub_le_of_mem_level_ball hx h
      rwa [add_sub_cancel_left] at this
    · intro h
      exact (level_add_le_max x z).trans (max_le hx h)
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, Equiv.coe_addLeft, Set.mk_mem_sym2_iff, mem_ofPred_eq, hiff]
    split_ifs
    · apply Subtype.ext
      change 1 - Real.exp (-(β : ℝ) * (J s(x + a, x + b) : ℝ)) =
        1 - Real.exp (-(β : ℝ) * (J s(a, b) : ℝ))
      rw [add_comm x a, add_comm x b, hJt]
    · rfl

open Classical in
/-- **Sibling-pair step** (Hutchcroft, arXiv:2103.17013v1, Lemma 2.8, one pair of blocks). Let
`J` be translation invariant, `h x = n + 1`, and let `r ≥ 0` satisfy `r ≤ β J(u, v)` for every
`u ∈ Λ_n` and `v ∈ x + Λ_n`. With `M_n = tightnessScale q_n Λ_n`, if `r (99 M_n)² ≤ T` then

`r e^{-T} (a_n / 2)² ≤ τ_{n+1}(0, x)`.

The clusters of `0` in `Λ_n` and of `x` in `x + Λ_n` are independent, the second has the law of
the first translated, and the cross-edge estimate (`lintegral_crossEdge_ge_exp`) with the
truncation at `99 M_n` (`lintegral_clusterIntersection_div_two_le`) gives the bound. This is
the one-point step of `sum_shell_tau_ge`. -/
theorem ofReal_mul_div_two_sq_le_tau_of_level_eq_succ [NeZero L]
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (β : ℝ≥0) (n : ℕ) {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = n + 1)
    {r T : ℝ} (hr0 : 0 ≤ r)
    (hrJ : ∀ u v, u.support.sup Nat.succ ≤ n → (v - x).support.sup Nat.succ ≤ n →
      r ≤ (β : ℝ) * (J s(u, v) : ℝ))
    (hrt : r * ((99 * tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℕ) : ℝ) ^ 2 ≤ T) :
    ENNReal.ofReal (r * Real.exp (-T)) *
        ((∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)) / 2) ^ 2 ≤
      tau (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n + 1}.sym2 then intensityProfile J β e else 0) 0 x := by
  set q := intensityProfile J β with hq_def
  set qn : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval := fun e =>
    if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2 then q e else 0
    with hqn
  set q1 : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval := fun e =>
    if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n + 1}.sym2 then q e else 0
    with hq1
  set S := (finite_level_ball (A := Fin d → ZMod L) n).toFinset with hS
  set M := tightnessScale qn S with hM_def
  set a := ∫⁻ ω, (clusterIntersection S ω 0 : ℝ≥0∞) ∂law qn with ha
  set t := 99 * M with ht
  have hSmem : ∀ z, z ∈ S ↔ z.support.sup Nat.succ ≤ n := fun z => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  have hScoe : (S : Set (ℕ →₀ (Fin d → ZMod L))) = {z | z.support.sup Nat.succ ≤ n} :=
    Set.Finite.coe_toFinset _
  have hx1 : x.support.sup Nat.succ ≤ n + 1 := hx.le
  have hx0 : ¬ x.support.sup Nat.succ ≤ n := by omega
  -- truncation at `99 M_n` (R7 at the root)
  have hR7 : a / 2 ≤ ∫⁻ ω, ((min (clusterIntersection S ω 0) t : ℕ) : ℝ≥0∞) ∂law qn := by
    have h := lintegral_clusterIntersection_div_two_le qn ⟨0, (hSmem 0).2 (by simp)⟩ 0
    exact le_of_le_of_eq h (lintegral_congr fun ω => (Nat.mono_cast.map_min).symm)
  -- the sibling block `x + Λ_n`
  set σ := Equiv.addLeft x with hσ
  set Tb := S.map σ.toEmbedding with hTb
  have hTmem : ∀ y, y ∈ Tb ↔ (y - x).support.sup Nat.succ ≤ n := fun y => by
    rw [← Finset.mem_coe, hTb, hσ, hS, coe_map_addLeft_level_ball]; rfl
  have hdisj : Disjoint S Tb := Finset.disjoint_left.2 fun y hyS hyT => hx0 (by
    have := level_sub_le_of_mem_level_ball ((hTmem y).1 hyT) ((hSmem y).1 hyS)
    rwa [sub_sub_cancel] at this)
  have hSsub : ∀ y ∈ S, y.support.sup Nat.succ ≤ n + 1 := fun y hy =>
    ((hSmem y).1 hy).trans (Nat.le_succ n)
  have hTsub : ∀ y ∈ Tb, y.support.sup Nat.succ ≤ n + 1 := fun y hy => by
    have h := level_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le (((hTmem y).1 hy).trans (Nat.le_succ n)) hx1)
  set PS : Set (Sym2 (ℕ →₀ (Fin d → ZMod L))) := (S : Set _).sym2 with hPS
  set PT : Set (Sym2 (ℕ →₀ (Fin d → ZMod L))) := (Tb : Set _).sym2 with hPT
  have hPSfin : PS.Finite := by
    rw [hPS, ← Finset.coe_sym2]; exact Finset.finite_toSet _
  have hPTfin : PT.Finite := by
    rw [hPT, ← Finset.coe_sym2]; exact Finset.finite_toSet _
  have hPST : Disjoint PS PT := by
    refine Set.disjoint_left.2 fun e he he' => ?_
    induction e using Sym2.ind with
    | _ u v =>
      exact Finset.disjoint_left.1 hdisj (Set.mk_mem_sym2_iff.1 he).1
        (Set.mk_mem_sym2_iff.1 he').1
  set W := PS ∪ PT with hW
  let C : Config (ℕ →₀ (Fin d → ZMod L)) → Finset (ℕ →₀ (Fin d → ZMod L)) := fun ω =>
    S.filter (· ∈ cluster (ω ∩ PS) 0)
  let D : Config (ℕ →₀ (Fin d → ZMod L)) → Finset (ℕ →₀ (Fin d → ZMod L)) := fun ω =>
    Tb.filter (· ∈ cluster (ω ∩ PT) x)
  have hWST : ∀ u ∈ S, ∀ v ∈ Tb, s(u, v) ∉ W := by
    intro u hu v hv he
    rcases he with he | he
    · exact Finset.disjoint_left.1 hdisj (Set.mk_mem_sym2_iff.1 he).2 hv
    · exact Finset.disjoint_left.1 hdisj hu (Set.mk_mem_sym2_iff.1 he).1
  have hWS : ∀ ω : Config (ℕ →₀ (Fin d → ZMod L)), ω ∩ W ∩ PS = ω ∩ PS := fun ω => by
    rw [inter_assoc, inter_eq_right.2 subset_union_left]
  have hWT : ∀ ω : Config (ℕ →₀ (Fin d → ZMod L)), ω ∩ W ∩ PT = ω ∩ PT := fun ω => by
    rw [inter_assoc, inter_eq_right.2 subset_union_right]
  have hC : ∀ ω, C ω = C (ω ∩ W) := fun ω => by simp only [C, hWS]
  have hD : ∀ ω, D ω = D (ω ∩ W) := fun ω => by simp only [D, hWT]
  -- every pair between the two blocks is open with probability at least `1 - e^{-r}`
  have hq_cross : ∀ u ∈ S, ∀ v ∈ Tb, 1 - Real.exp (-r) ≤ (q1 s(u, v) : ℝ) := by
    intro u hu v hv
    have hmem1 : s(u, v) ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n + 1}.sym2 :=
      Set.mk_mem_sym2_iff.2 ⟨hSsub u hu, hTsub v hv⟩
    have hq1uv : q1 s(u, v) = q s(u, v) := by simp only [hq1, hmem1, ↓reduceIte]
    rw [hq1uv]
    change 1 - Real.exp (-r) ≤ 1 - Real.exp (-(β : ℝ) * (J s(u, v) : ℝ))
    have hrJ' := hrJ u v ((hSmem u).1 hu) ((hTmem v).1 hv)
    have := Real.exp_le_exp.2 (show -(β : ℝ) * (J s(u, v) : ℝ) ≤ -r by linarith)
    linarith
  have hcross := lintegral_crossEdge_ge_exp q1 hdisj (hPSfin.union hPTfin) hWST
    (H := fun _ => 1) (fun _ => rfl) hC hD (fun _ => Finset.filter_subset _ _)
    (fun _ => Finset.filter_subset _ _) hq_cross
  rw [setLIntegral_one] at hcross
  -- the cross event joins `0` to `x`
  have hEconn : {ω | ∃ u ∈ C ω, ∃ v ∈ D ω, s(u, v) ∈ ω} ⊆ conn 0 x := by
    rintro ω ⟨u, hu, v, hv, huv⟩
    simp only [C, D, Finset.mem_filter] at hu hv
    have h1 : ω ∈ conn 0 u := conn_mono inter_subset_left hu.2
    have h2 : ω ∈ conn x v := conn_mono inter_subset_left hv.2
    have hne : u ≠ v := fun h => Finset.disjoint_left.1 hdisj hu.1 (h ▸ hv.1)
    exact conn_trans (conn_trans h1 (mem_conn_of_mem hne huv)) (by rw [conn_symm]; exact h2)
  -- the truncated sizes
  let X : Config (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun ω =>
    ((min (clusterIntersection S (ω ∩ PS) 0) t : ℕ) : ℝ≥0∞)
  let Y : Config (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun ω =>
    ((min (clusterIntersection Tb (ω ∩ PT) x) t : ℕ) : ℝ≥0∞)
  have hXdet : ∀ ω, X ω = X (ω ∩ PS) := fun ω => by simp only [X, inter_assoc, inter_self]
  have hYdet : ∀ ω, Y ω = Y (ω ∩ PT) := fun ω => by simp only [Y, inter_assoc, inter_self]
  have hXm : Measurable X := measurable_of_determined_finite hPSfin hXdet
  have hYm : Measurable Y := measurable_of_determined_finite hPTfin hYdet
  have hpt : ∀ ω, ENNReal.ofReal (r * Real.exp (-T)) * (X ω * Y ω) ≤
      (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (1 - Real.exp (-(r * (C ω).card * (D ω).card))) := by
    intro ω
    have hcC : (C ω).card = clusterIntersection S (ω ∩ PS) 0 :=
      (clusterIntersection_eq_card_filter _ _ _).symm
    have hcD : (D ω).card = clusterIntersection Tb (ω ∩ PT) x :=
      (clusterIntersection_eq_card_filter _ _ _).symm
    simp only [X, Y, one_mul, hcC, hcD]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (min _ t),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg hr0 (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (mul_exp_neg_mul_min_le_one_sub_exp hr0 hrt)
  -- the law of `X` is that of the truncated root cluster under `q_n`
  have hXint : ∫⁻ ω, X ω ∂law q1 =
      ∫⁻ ω, ((min (clusterIntersection S ω 0) t : ℕ) : ℝ≥0∞) ∂law qn := by
    have hres : (fun e => if e ∈ PS then q1 e else 0) = qn := by
      funext e
      by_cases he : e ∈ PS
      · have hen : e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2 := by
          rwa [hPS, hScoe] at he
        have he1 : e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n + 1}.sym2 := by
          induction e using Sym2.ind with
          | _ u v =>
            obtain ⟨hu, hv⟩ := Set.mk_mem_sym2_iff.1 hen
            exact Set.mk_mem_sym2_iff.2 ⟨le_trans hu (Nat.le_succ n),
              le_trans hv (Nat.le_succ n)⟩
        simp only [hq1, hqn, he, he1, hen, ↓reduceIte]
      · have hen : e ∉ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2 := by
          rwa [hPS, hScoe] at he
        simp only [hqn, he, hen, ↓reduceIte]
    rw [← hres]
    exact lintegral_comp_inter_eq q1 PS (f := fun ω =>
      ((min (clusterIntersection S ω 0) t : ℕ) : ℝ≥0∞))
      ((Measurable.of_discrete (f := fun k : ℕ => ((min k t : ℕ) : ℝ≥0∞))).comp
        (measurable_clusterIntersection S 0))
  -- the law of `Y` is that of `X`, by translation
  have hYint : ∫⁻ ω, Y ω ∂law q1 = ∫⁻ ω, X ω ∂law q1 := by
    have hσlaw := law_restrict_level_ball_map_addLeft J hJt β (n + 1) hx1
    have hσm : Measurable (fun ω : Config (ℕ →₀ (Fin d → ZMod L)) =>
        Sym2.map (Equiv.addLeft x) '' ω) := by
      apply measurable_set_iff.mpr
      intro e
      simp_rw [mem_image_sym2Map_iff]
      exact measurable_set_mem _
    conv_lhs => rw [← hσlaw]
    rw [lintegral_map hYm hσm]
    refine lintegral_congr fun ω => ?_
    simp only [X, Y]
    congr 2
    have hPTimg : PT = Sym2.map σ '' PS := by
      rw [hPT, hPS, hTb, Finset.coe_map, Equiv.coe_toEmbedding, Set.sym2_image]
    rw [hPTimg, ← Set.image_inter (Sym2.map.injective σ.injective)]
    rw [show x = σ 0 by simp [hσ]]
    unfold clusterIntersection
    rw [hTb, Finset.coe_map, Equiv.coe_toEmbedding, cluster_image, ← Set.image_inter σ.injective,
      Set.ncard_image_of_injective _ σ.injective]
  -- assembly at the point `x`
  calc ENNReal.ofReal (r * Real.exp (-T)) * (a / 2) ^ 2
      ≤ ENNReal.ofReal (r * Real.exp (-T)) *
          ((∫⁻ ω, X ω ∂law q1) * ∫⁻ ω, Y ω ∂law q1) := by
        rw [hYint, ← sq, hXint]
        gcongr
    _ = ENNReal.ofReal (r * Real.exp (-T)) * ∫⁻ ω, X ω * Y ω ∂law q1 := by
        rw [lintegral_mul_of_determined q1 hPST hXm hYm hXdet hYdet]
    _ = ∫⁻ ω, ENNReal.ofReal (r * Real.exp (-T)) * (X ω * Y ω) ∂law q1 :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ ω, (fun _ => (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (1 - Real.exp (-(r * (C ω).card * (D ω).card))) ∂law q1 :=
        lintegral_mono hpt
    _ ≤ law q1 {ω | ∃ u ∈ C ω, ∃ v ∈ D ω, s(u, v) ∈ ω} := hcross
    _ ≤ tau q1 0 x := measure_mono hEconn

open Classical in
/-- **Sibling-block recursion** (Hutchcroft, arXiv:2103.17013v1, Lemma 2.8, recursion part). On
`ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `d ≥ 1`, let `c, α, β > 0` and let `J` be translation
invariant with `J(u, v) ≥ c L^{-(d+α) h(v-u)}` for `u ≠ v`. Write `q_m` for `intensityProfile J β`
restricted to the pairs inside `Λ_m = {h ≤ m}`, `M_n` for the quantile `tightnessScale q_n Λ_n` and
`a_n = E_{q_n} |K_0 ∩ Λ_n|`. If `M_n² ≤ (A/β) L^{(d+α)n}`, then

`k β L^{-αn} a_n² ≤ ∑_{x ∈ Λ_{n+1} \ Λ_n} P_{q_{n+1}}(0 ↔ x)`

with `k = (c/4) e^{-T} L^{-(d+α)}` and `T = c A 99² L^{-(d+α)}`. The constant depends only on
`d, L, α, c, A`. -/
theorem sum_shell_tau_ge [NeZero L] (hL : 2 ≤ L) (hd : 1 ≤ d) {α c A : ℝ} (hα : 0 < α)
    (hc : 0 < c) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {β : ℝ≥0} (hβ : 0 < β) (n : ℕ)
    (hM : (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤ A / β * (L : ℝ) ^ (((d : ℝ) + α) * n)) :
    ENNReal.ofReal (c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
        (L : ℝ) ^ (-((d : ℝ) + α)) * β * (L : ℝ) ^ (-(α * n))) *
      (∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)) ^ 2 ≤
      ∑ x ∈ (finite_level_ball (n + 1)).toFinset \ (finite_level_ball n).toFinset,
        tau (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n + 1}.sym2 then intensityProfile J β e else 0) 0 x := by
  set q := intensityProfile J β with hq_def
  set qn : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval := fun e =>
    if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}.sym2 then q e else 0
    with hqn
  set q1 : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval := fun e =>
    if e ∈ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n + 1}.sym2 then q e else 0
    with hq1
  set S := (finite_level_ball (A := Fin d → ZMod L) n).toFinset with hS
  set B1 := (finite_level_ball (A := Fin d → ZMod L) (n + 1)).toFinset with hB1
  set M := tightnessScale qn S with hM_def
  set a := ∫⁻ ω, (clusterIntersection S ω 0 : ℝ≥0∞) ∂law qn with ha
  set t := 99 * M with ht
  have hSmem : ∀ z, z ∈ S ↔ z.support.sup Nat.succ ≤ n := fun z => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  have hB1mem : ∀ z, z ∈ B1 ↔ z.support.sup Nat.succ ≤ n + 1 := fun z => by
    rw [hB1, Set.Finite.mem_toFinset]; rfl
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hda : (0 : ℝ) ≤ (d : ℝ) + α := by positivity
  -- the constants
  set r : ℝ := (β : ℝ) * (c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1)))) with hr_def
  set T0 : ℝ := c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)) with hT0
  have hr0 : 0 ≤ r := by positivity
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hrt : r * (t : ℝ) ^ 2 ≤ T0 := by
    have hcomb : (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) *
        (L : ℝ) ^ (((d : ℝ) + α) * n) = (L : ℝ) ^ (-((d : ℝ) + α)) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hM' : (M : ℝ) ^ 2 ≤ A / β * (L : ℝ) ^ (((d : ℝ) + α) * n) := hM
    calc r * (t : ℝ) ^ 2
        = ((β : ℝ) * c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) * 99 ^ 2) *
            (M : ℝ) ^ 2 := by rw [ht, hr_def]; push_cast; ring
      _ ≤ ((β : ℝ) * c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) * 99 ^ 2) *
            (A / β * (L : ℝ) ^ (((d : ℝ) + α) * n)) :=
          mul_le_mul_of_nonneg_left hM' (by positivity)
      _ = c * A * 99 ^ 2 * ((L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) *
            (L : ℝ) ^ (((d : ℝ) + α) * n)) := by
          field_simp
      _ = T0 := by rw [hcomb]
  -- one point of the shell
  have hpoint : ∀ x ∈ B1 \ S,
      ENNReal.ofReal (r * Real.exp (-T0)) * (a / 2) ^ 2 ≤ tau q1 0 x := by
    intro x hx
    rw [Finset.mem_sdiff, hB1mem, hSmem] at hx
    refine ofReal_mul_div_two_sq_le_tau_of_level_eq_succ J hJt β n (by omega) hr0
      (fun u v hu hv => ?_) hrt
    have hv1 : v.support.sup Nat.succ ≤ n + 1 := by
      have h := level_add_le_max (v - x) x
      rw [sub_add_cancel] at h
      exact h.trans (max_le (hv.trans (Nat.le_succ n)) hx.1)
    have huv : u ≠ v := fun h => hx.2 (by
      have := level_sub_le_of_mem_level_ball hv (h ▸ hu)
      rwa [sub_sub_cancel] at this)
    have hlev : (((v - u).support.sup Nat.succ : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast level_sub_le_of_mem_level_ball (hu.trans (Nat.le_succ n)) hv1
    have hpow : (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) ≤
        (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hpow hc.le).trans (hJ u v huv))
      β.coe_nonneg
  -- the shell has at least `L^{dn}` points
  have hcard : (L : ℝ) ^ ((d : ℝ) * n) ≤ ((B1 \ S).card : ℝ) := by
    have hSB : S ⊆ B1 := fun z hz => (hB1mem z).2 (((hSmem z).1 hz).trans (Nat.le_succ n))
    have hc1 : (B1 \ S).card = (L ^ d) ^ (n + 1) - (L ^ d) ^ n := by
      rw [Finset.card_sdiff_of_subset hSB, hB1, hS, card_toFinset_level_ball,
        card_toFinset_level_ball]
    have hLd : 2 ≤ L ^ d := le_trans hL (Nat.le_self_pow (by omega) L)
    have hc2 : (L ^ d) ^ n ≤ (B1 \ S).card := by
      rw [hc1, pow_succ]
      have : 2 * (L ^ d) ^ n ≤ (L ^ d) ^ n * L ^ d := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ hLd
      omega
    have hc3 : (L : ℝ) ^ ((d : ℝ) * n) = (((L ^ d) ^ n : ℕ) : ℝ) := by
      rw [Real.rpow_mul hL0.le]; push_cast; rw [Real.rpow_natCast, Real.rpow_natCast]
    rw [hc3]
    exact_mod_cast hc2
  -- the final comparison
  have hreal : 4 * (c / 4 * Real.exp (-T0) * (L : ℝ) ^ (-((d : ℝ) + α)) * β *
      (L : ℝ) ^ (-(α * n))) ≤ ((B1 \ S).card : ℝ) * (r * Real.exp (-T0)) := by
    have hid : (L : ℝ) ^ ((d : ℝ) * n) * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) =
        (L : ℝ) ^ (-((d : ℝ) + α)) * (L : ℝ) ^ (-(α * n)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
    calc 4 * (c / 4 * Real.exp (-T0) * (L : ℝ) ^ (-((d : ℝ) + α)) * β * (L : ℝ) ^ (-(α * n)))
        = (L : ℝ) ^ ((d : ℝ) * n) * (r * Real.exp (-T0)) := by
          rw [hr_def]
          have := hid
          linear_combination (-(c * Real.exp (-T0) * β)) * this
      _ ≤ ((B1 \ S).card : ℝ) * (r * Real.exp (-T0)) := by
          gcongr
  have ha2 : a ^ 2 = (a / 2) ^ 2 * 4 := by
    have h2 : a / 2 * 2 = a := ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    conv_lhs => rw [← h2]
    rw [mul_pow]; norm_num
  calc ENNReal.ofReal (c / 4 * Real.exp (-T0) * (L : ℝ) ^ (-((d : ℝ) + α)) * β *
        (L : ℝ) ^ (-(α * n))) * a ^ 2
      = ENNReal.ofReal (4 * (c / 4 * Real.exp (-T0) * (L : ℝ) ^ (-((d : ℝ) + α)) * β *
          (L : ℝ) ^ (-(α * n)))) * (a / 2) ^ 2 := by
        rw [ha2, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num), ENNReal.ofReal_ofNat]; ring
    _ ≤ ENNReal.ofReal (((B1 \ S).card : ℝ) * (r * Real.exp (-T0))) * (a / 2) ^ 2 := by
        gcongr
    _ = ∑ x ∈ B1 \ S, ENNReal.ofReal (r * Real.exp (-T0)) * (a / 2) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ∑ x ∈ B1 \ S, tau q1 0 x := Finset.sum_le_sum hpoint

end Hierarchical

end PercLib.Models
