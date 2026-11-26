/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's runaway, block-restricted quantile, power-law kernel and
critical boundary flux theorems, and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
No upstream code is copied and no definition is added. Mathematical reference: T. Hutchcroft,
arXiv:2103.17013v1, Proposition 2.2 at `β = β_c` (in the squared form its proof gives) and
Proposition 2.12(ii) (with the coefficient `β_c` that the flux argument gives).
-/
module

public import PercLib.Models.HierarchicalRunaway
public import PercLib.Models.HierarchicalSibling
public import PercLib.Percolation.Bond.Tightness.RestrictQuantile
public import PercLib.Percolation.Bond.Tightness.MomentRatio
public import PercLib.Percolation.Bond.FiniteSetCriterion

/-!
# The hierarchical lattice at the critical point

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}`,
`β_c = β_c(0) = rootCriticalIntensity J 0`, `q_n(β)` for `intensityProfile J β` restricted to
the pairs inside `Λ_n`, `M_n(β) = tightnessScale q_n(β) Λ_n` and
`a_n(β) = E_{q_n(β)} |K_0 ∩ Λ_n|`, all spelled as in `sum_shell_tau_ge`. With `c, α, ℓ` as in
`tightnessScale_hierarchical_amplification`, `A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`.

## Main results

* `mem_cluster_inter_sym2_iff`: the cluster of `o ∈ D` in `ω ∩ D.sym2` is the set of points
  joined to `o` inside `D` in `ω`.
* `lintegral_clusterIntersection_restrict_eq_sum`: for a finite `S ∋ o`,
  `E_{q|S} |K_o ∩ S| = ∑_{u ∈ S} P_q(o ↔ u inside S)`.
* `rootCriticalIntensity_pos_of_powerLaw`: `β_c(x) > 0` for a power-law upper bound.
* `toNNReal_rootCriticalIntensity_mul_sq_tightnessScale_le` (Prop. 2.2 at `β_c`):
  `β_c M_n(β_c)² ≤ A L^{(d+α)n}` for every `n`.
* `rootCriticalIntensity_mem_Ioo_and_mul_sq_tightnessScale_le`: the same together with
  `0 < β_c < ∞`, under two-sided power-law bounds and `0 < α < d`.
* `ofReal_le_lintegral_clusterIntersection_at_rootCriticalIntensity` (Prop. 2.12(ii),
  corrected): `(L^α - 1) / (β_c C (1 - L^{-d})) L^{αn} ≤ a_n(β_c)` for every `n`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-! ### Clusters of a block-restricted configuration -/

section General

variable {V : Type*}

/-- **Clusters of `ω ∩ D.sym2`.** For `o ∈ D`, a point is in the cluster of `o` in
`ω ∩ D.sym2` exactly when it is joined to `o` inside `D` in `ω`. -/
theorem mem_cluster_inter_sym2_iff (ω : Config V) {D : Set V} {o : V} (ho : o ∈ D) (u : V) :
    u ∈ cluster (ω ∩ D.sym2) o ↔
      ω ∈ localConn D o u := by
  constructor
  · intro h
    change (openGraph (ω ∩ D.sym2)).Reachable o u at h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ⟨ho, ho, SimpleGraph.Reachable.refl _⟩
    | @tail z w _ hzw ih =>
      obtain ⟨_, hz, hr⟩ := ih
      rw [openGraph_adj_iff] at hzw
      obtain ⟨⟨hmem, hsym⟩, hne⟩ := hzw
      have hw : w ∈ D := (Set.mk_mem_sym2_iff.1 hsym).2
      refine ⟨ho, hw, hr.trans (SimpleGraph.Adj.reachable ?_)⟩
      rw [SimpleGraph.induce_adj, openGraph_adj_iff]
      exact ⟨hmem, hne⟩
  · rintro ⟨_, hu, h⟩
    let φ : (openGraph ω).induce D →g openGraph (ω ∩ D.sym2) :=
      { toFun := Subtype.val
        map_rel' := fun {a b} hab => by
          rw [SimpleGraph.induce_adj, openGraph_adj_iff] at hab
          rw [openGraph_adj_iff]
          exact ⟨⟨hab.1, Set.mk_mem_sym2_iff.2 ⟨a.2, b.2⟩⟩, hab.2⟩ }
    exact h.map φ

/-- **Expected restricted cluster size as a sum of internal connections.** For a finite set
`S ∋ o` (written `D` as a set), the expected size of `K_o ∩ S` under the profile restricted to
the pairs inside `S` is `∑_{u ∈ S} P_q(o ↔ u inside S)`. -/
theorem lintegral_clusterIntersection_restrict_eq_sum [Countable V]
    (q : Sym2 V → unitInterval) (S : Finset V) {D : Set V} (hS : (S : Set V) = D)
    [DecidablePred (· ∈ D.sym2)] {o : V} (ho : o ∈ S) :
    ∫⁻ ω, (clusterIntersection S ω o : ℝ≥0∞) ∂law (fun e => if e ∈ D.sym2 then q e else 0) =
      ∑ u ∈ S, law q (localConn (S : Set V) o u) := by
  subst hS
  classical
  rw [← lintegral_comp_inter_eq q _ (measurable_clusterIntersection_ennreal S o)]
  have hpt : ∀ ω : Config V, (clusterIntersection S (ω ∩ (S : Set V).sym2) o : ℝ≥0∞) =
      ∑ u ∈ S, (localConn (S : Set V) o u).indicator 1 ω := by
    intro ω
    rw [clusterIntersection_eq_card_filter, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [mem_cluster_inter_sym2_iff ω (Finset.mem_coe.2 ho) u, Set.indicator_apply,
      Pi.one_apply, mem_localConn]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun u _ =>
    (measurable_one.indicator (measurableSet_localConn _ o u))]
  exact Finset.sum_congr rfl fun u _ => lintegral_indicator_one (measurableSet_localConn _ o u)

end General

variable {d L : ℕ}

/-! ### Prop. 2.2 at the threshold -/

/-- **Positive threshold.** Under a power-law upper bound `J(u, v) ≤ C L^{-(d+α) h(v - u)}`,
`β_c(x) > 0` at every root. No sign condition on `C` and no condition on `d` is needed. -/
theorem rootCriticalIntensity_pos_of_powerLaw [NeZero L] (hL : 2 ≤ L) {α C : ℝ}
    (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (x : ℕ →₀ (Fin d → ZMod L)) :
    0 < rootCriticalIntensity J x := by
  set K : ℝ := C * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1)
  have hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤
      ((K.toNNReal : ℝ≥0) : ℝ≥0∞) := fun v => rowSum_le_of_powerLaw hL hα J hJ v
  have h := inv_le_rootCriticalIntensity J K.toNNReal (fun v => by convert hrow v) x
  exact (ENNReal.inv_pos.2 ENNReal.coe_ne_top).trans_le h

open Classical in
/-- **Prop. 2.2 at the threshold** (2XJX, endpoint part; Hutchcroft, arXiv:2103.17013v1,
Prop. 2.2 at `β = β_c`, squared form). Under the hypotheses of
`sq_tightnessScale_lt_of_lt_rootCriticalIntensity`, for every `n`,
`β_c M_n(β_c)² ≤ A L^{(d+α)n}` with `A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`. When `β_c ∈ {0, ∞}`
the left side is `0`. -/
theorem toNNReal_rootCriticalIntensity_mul_sq_tightnessScale_le [NeZero L] (hL : 2 ≤ L)
    {α c : ℝ} (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJs : ∀ u, Summable fun v => (J s(u, v) : ℝ))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) (n : ℕ) :
    ((rootCriticalIntensity J 0).toNNReal : ℝ) *
        (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then
            intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0)
          (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
      (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) *
        (L : ℝ) ^ (((d : ℝ) + α) * n) := by
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)
    with hA_def
  set b : ℝ≥0 := (rootCriticalIntensity J 0).toNNReal with hb_def
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hX : 0 < (L : ℝ) ^ (((d : ℝ) + α) * n) := Real.rpow_pos_of_pos (by linarith) _
  have hA : 0 < A := by
    have hN : (1 : ℝ) ≤ (L : ℝ) ^ (d * ℓ) := one_le_pow₀ hL1.le
    have hlog : 0 < Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) :=
      Real.log_pos (by nlinarith)
    rw [hA_def]
    positivity
  rcases eq_zero_or_pos b with hb | hb
  · rw [hb, NNReal.coe_zero, zero_mul]
    positivity
  have hne : rootCriticalIntensity J 0 ≠ ⊤ := by
    intro h
    rw [hb_def, h, ENNReal.toNNReal_top] at hb
    exact lt_irrefl _ hb
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball n).toFinset with hS_def
  have hSD : ({z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} : Set _) = (S : Set _) :=
    (Set.Finite.coe_toFinset _).symm
  simp only [hSD]
  refine restrict_quantile_sq_bound_at_endpoint J S subset_rfl hb fun a ha hab => ?_
  have hab' : (a : ℝ≥0∞) < rootCriticalIntensity J 0 := by
    rw [← ENNReal.coe_toNNReal hne]
    exact ENNReal.coe_lt_coe.2 hab
  have h := sq_tightnessScale_lt_of_lt_rootCriticalIntensity hL hc hα J hJt hJ hJs hexp hℓ ha
    hab' n
  rw [← hA_def] at h
  simp only [hSD] at h
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rw [div_mul_eq_mul_div, lt_div_iff₀ ha0] at h
  rw [mul_comm]
  convert h.le using 4
  congr 1
  ext z
  simp [hS_def]

open Classical in
/-- **Prop. 2.2 at the threshold, with `0 < β_c < ∞`** (2XJX, endpoint part): for a
translation-invariant kernel with `c L^{-(d+α)h} ≤ J ≤ C L^{-(d+α)h}` off the diagonal and
`0 < α < d`, `β_c ∈ (0, ∞)` and `β_c M_n(β_c)² ≤ A L^{(d+α)n}` for every `n`. -/
theorem rootCriticalIntensity_mem_Ioo_and_mul_sq_tightnessScale_le [NeZero L] (hL : 2 ≤ L)
    {α c C : ℝ} (hc : 0 < c) (hα : 0 < α) (hαd : α < d)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) :
    rootCriticalIntensity J 0 ∈ Set.Ioo 0 ⊤ ∧ ∀ n : ℕ,
      ((rootCriticalIntensity J 0).toNNReal : ℝ) *
          (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then
              intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0)
            (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
        (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) *
          (L : ℝ) ^ (((d : ℝ) + α) * n) := by
  have hJs := summable_of_powerLaw hL hα J hJu
  exact ⟨⟨rootCriticalIntensity_pos_of_powerLaw hL hα J hJu 0,
      rootCriticalIntensity_hierarchical_lt_top hL hc hα hαd J hJt hJ hJs⟩,
    toNNReal_rootCriticalIntensity_mul_sq_tightnessScale_le hL hc hα J hJt hJ hJs hexp hℓ⟩

/-! ### Prop. 2.12(ii) at the threshold -/

open Classical in
/-- **Prop. 2.12(ii), corrected** (FF30, flux part; Hutchcroft, arXiv:2103.17013v1,
Prop. 2.12(ii), with the coefficient `β_c` that the flux argument gives): for a
translation-invariant kernel with `J(u, v) ≤ C L^{-(d+α) h(v - u)}` off the diagonal, for every
`n`, `(L^α - 1) / (β_c C (1 - L^{-d})) · L^{αn} ≤ a_n(β_c) = E_{q_n(β_c)} |K_0 ∩ Λ_n|`.
When `β_c = ∞` the left side is `0`. -/
theorem ofReal_le_lintegral_clusterIntersection_at_rootCriticalIntensity [NeZero L]
    (hL : 2 ≤ L) {α C : ℝ} (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (n : ℕ) :
    ENNReal.ofReal (((L : ℝ) ^ α - 1) /
        ((rootCriticalIntensity J 0).toReal * C * (1 - (L : ℝ) ^ (-(d : ℝ)))) *
          (L : ℝ) ^ (α * n)) ≤
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then
            intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0) := by
  set βc := rootCriticalIntensity J 0 with hβc_def
  rcases eq_or_ne βc ⊤ with htop | htop
  · rw [htop, ENNReal.toReal_top, zero_mul, zero_mul, div_zero, zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball n).toFinset with hS_def
  have hmemS : ∀ v : ℕ →₀ (Fin d → ZMod L), v ∈ S ↔ v.support.sup Nat.succ ≤ n := fun v => by
    simp [hS_def]
  have h0S : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ S := by simp [hmemS]
  rw [lintegral_clusterIntersection_restrict_eq_sum _ S (Set.Finite.coe_toFinset _) h0S]
  set P : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun u =>
    law (intensityProfile J βc.toNNReal) (localConn (S : Set _) 0 u)
    with hP_def
  have hflux := one_le_boundaryFlux_at_rootCriticalIntensity J
    (transitive_of_powerLaw_translationInvariant J hJt)
    (fun u => by convert (rowSum_le_of_powerLaw hL hα J hJ u).trans_lt ENNReal.ofReal_lt_top)
    (lt_top_iff_ne_top.2 htop) S h0S
  set K : ℝ := C * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) / ((L : ℝ) ^ α - 1)
    with hK_def
  have hrow : ∀ u ∈ S, (∑' v, if v ∈ S then 0 else (J s(u, v) : ℝ≥0∞)) ≤ ENNReal.ofReal K := by
    intro u hu
    refine le_of_eq_of_le (tsum_congr fun v => ?_)
      (tsum_level_gt_le_of_powerLaw hL hα J hJ n ((hmemS u).1 hu))
    by_cases hv : v.support.sup Nat.succ ≤ n
    · simp only [(hmemS v).2 hv, not_lt.2 hv, ↓reduceIte]
    · have : v ∉ S := fun h => hv ((hmemS v).1 h)
      simp only [this, not_le.1 hv, ↓reduceIte]
  have h1 : 1 ≤ βc * (∑ u ∈ S, P u) * ENNReal.ofReal K := by
    refine (hflux.1.trans hflux.2).trans ?_
    rw [mul_assoc, Finset.sum_mul]
    exact mul_le_mul' le_rfl (Finset.sum_le_sum fun u hu =>
        mul_le_mul' le_rfl (by convert hrow u hu))
  change _ ≤ ∑ u ∈ S, P u
  set a := ∑ u ∈ S, P u with ha_def
  rcases eq_or_ne a ⊤ with hat | hat
  · rw [hat]
    exact le_top
  set βr := βc.toReal with hβr
  set ar := a.toReal with har
  rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_toReal hat, ← hβr, ← har,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg), ENNReal.one_le_ofReal] at h1
  rw [← ENNReal.ofReal_toReal hat, ← har]
  refine ENNReal.ofReal_le_ofReal ?_
  have hβr0 : 0 ≤ βr := ENNReal.toReal_nonneg
  have har0 : 0 ≤ ar := ENNReal.toReal_nonneg
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
  have hpos : 0 < βr * K := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hK : βr * K = βr * C * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) /
      ((L : ℝ) ^ α - 1) := by
    rw [hK_def]; ring
  have hD : 0 < βr * C * (1 - (L : ℝ) ^ (-(d : ℝ))) := by
    have hLn : 0 < (L : ℝ) ^ (-(α * n)) := Real.rpow_pos_of_pos hL0 _
    rw [hK] at hpos
    have := (div_pos_iff_of_pos_right hLa).1 hpos
    exact (mul_pos_iff_of_pos_right hLn).1 this
  have heq : ((L : ℝ) ^ α - 1) / (βr * C * (1 - (L : ℝ) ^ (-(d : ℝ)))) * (L : ℝ) ^ (α * n) =
      1 / (βr * K) := by
    have hLp : (L : ℝ) ^ (α * n) ≠ 0 := (Real.rpow_pos_of_pos hL0 _).ne'
    rw [hK]
    field_simp
    rw [← Real.rpow_add hL0, add_neg_cancel, Real.rpow_zero]
  rw [heq, div_le_iff₀ hpos]
  linarith

end PercLib.Models

/-! ### Non-vacuity (D-5) -/
section Witnesses

open PercLib.Models

open Classical in
/-- `L = 2`, `d = 3`, `α = 1`, `c = C = 1` and the kernel `J(u, v) = 2^{-4 j}` when `u, v` first
share a level-`j` block: the threshold is in `(0, ∞)`, so both endpoint bounds are informative,
and for some amplification scale `ℓ` both hold for every `n`. -/
example : ∃ J : Sym2 (ℕ →₀ (Fin 3 → ZMod 2)) → ℝ≥0, ∃ ℓ : ℕ,
    rootCriticalIntensity J 0 ∈ Set.Ioo 0 ⊤ ∧ ∀ n : ℕ,
      ((rootCriticalIntensity J 0).toNNReal : ℝ) *
          (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin 3 → ZMod 2) |
            z.support.sup Nat.succ ≤ n}.sym2 then
              intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0)
            (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
        (4 / 1) * ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * ℓ) *
          Real.log (2 * (((2 : ℕ) : ℝ) ^ (3 * ℓ)) ^ 2) * ((2 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) + 1) * n) ∧
      ENNReal.ofReal ((((2 : ℕ) : ℝ) ^ (1 : ℝ) - 1) /
          ((rootCriticalIntensity J 0).toReal * 1 * (1 - ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ)))) *
            ((2 : ℕ) : ℝ) ^ ((1 : ℝ) * n)) ≤
        ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin 3 → ZMod 2) |
            z.support.sup Nat.succ ≤ n}.sym2 then
              intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0) := by
  let k : (ℕ →₀ (Fin 3 → ZMod 2)) → ℝ≥0 := fun z =>
    ((2 : ℝ) ^ (-(4 * ((z.support.sup Nat.succ : ℕ) : ℝ)))).toNNReal
  obtain ⟨J, hJ⟩ := exists_sym2_kernel k (fun z => by simp only [k, Finsupp.support_neg])
  have hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v) := by
    intro x u v
    rw [hJ, hJ, add_sub_add_right_eq_sub]
  have hval : ∀ u v : ℕ →₀ (Fin 3 → ZMod 2), (J s(u, v) : ℝ) = 1 * ((2 : ℕ) : ℝ) ^
      (-((((3 : ℕ) : ℝ) + 1) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) := by
    intro u v
    rw [hJ]
    simp only [k, one_mul, Real.coe_toNNReal _ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    norm_num
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale (L := 2) (d := 3) le_rfl one_pos
    (by norm_num)
  have h := rootCriticalIntensity_mem_Ioo_and_mul_sq_tightnessScale_le le_rfl one_pos one_pos
    (by norm_num) J hJt (fun u v _ => (hval u v).ge) (fun u v _ => (hval u v).le) hexp hℓ
  exact ⟨J, ℓ, h.1, fun n => ⟨h.2 n,
    ofReal_le_lintegral_clusterIntersection_at_rootCriticalIntensity le_rfl one_pos J hJt
      (fun u v _ => (hval u v).le) n⟩⟩

end Witnesses
