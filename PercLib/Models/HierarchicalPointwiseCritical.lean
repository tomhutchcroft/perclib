/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, from this library's runaway, threshold endpoint, restricted
susceptibility, pointwise sibling and translation theorems, and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied and no definition is added.
Mathematical reference: T. Hutchcroft, *The critical two-point function for long-range
percolation on the hierarchical lattice*, arXiv:2103.17013v1, Propositions 2.2, 2.7, 2.10 and
2.12 (pointwise form, without radial symmetry).
-/
module

public import PercLib.Models.HierarchicalPointwise
public import PercLib.Models.HierarchicalEndpoint
public import PercLib.Models.HierarchicalRunaway
public import PercLib.Models.HierarchicalPowerKernel
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.SusceptibilityContinuity
public import PercLib.Percolation.Bond.Tightness.RestrictQuantile

/-!
# Pointwise two-point bounds at a general endpoint intensity

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}`,
`q = intensityProfile J b`, `q_n` for `q` restricted to the pairs inside `Λ_n`,
`a_n = E_{q_n} |K_0 ∩ Λ_n|`, `τ_n(0, x) = P_q(0 ↔ x inside Λ_n)` and `τ = tau q`. The kernel
`J` is translation invariant, with `c L^{-(d+α) h(v-u)} ≤ J(u, v) ≤ C₀ L^{-(d+α) h(v-u)}` off the
diagonal; it need not be radial. The intensity `b > 0` is an endpoint: the susceptibility of the
origin is finite at every `β ∈ (a, b)`.

* The endpoint quantile bound `b M_n(b)² ≤ A L^{(d+α)n}` follows from the strict bound below `b`
  and left continuity of the quantile in a finite block.
* A boundary-flux inequality `b ∑_{u ∈ Λ_n} τ_n(0,u) ∑_{v ∉ Λ_n} J(u,v) ≥ 1` gives
  `a_n ≥ (L^α - 1)/(b C₀ (1 - L^{-d})) L^{αn}`.
* With the restricted-susceptibility bound `a_n ≤ C' L^{αn}`, the pointwise sibling lower bound
  and the outer-shell plus first-exit upper bounds give, for `h x = n ≥ 1`,
  `c₁ L^{-(d-α)n} ≤ τ_n(0,x) ≤ τ(0,x) ≤ C₁ L^{-(d-α)n}`.

## Main results

* `mul_sq_tightnessScale_le_of_chi_lt_top`: the endpoint quantile bound at a general `b`.
* `ofReal_le_lintegral_clusterIntersection_of_boundaryFlux`: the lower block mean from flux.
* `exists_ofReal_le_law_localConn_of_boundaryFlux`: the pointwise lower bound.
* `exists_tau_le_of_chi_lt_top`: the pointwise upper bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Models

open PercLib.Percolation.Bond

variable {d L : ℕ} [NeZero L]

open Classical in
/-- **Prop. 2.2 at an endpoint** (squared form). If `J` is translation invariant with
`J(u, v) ≥ c L^{-(d+α) h(v-u)}` off the diagonal, `ℓ` is an amplification scale, `a < b` and
`χ_β(0) < ∞` for every `β ∈ (a, b)`, then for every `n`,
`b M_n(b)² ≤ A L^{(d+α)n}` with `A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`. -/
theorem mul_sq_tightnessScale_le_of_chi_lt_top (hL : 2 ≤ L) {α c : ℝ} (hc : 0 < c)
    (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) (n : ℕ) :
    (b : ℝ) * (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
      (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) *
        (L : ℝ) ^ (((d : ℝ) + α) * n) := by
  have hb : 0 < b := lt_of_le_of_lt zero_le hab
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball n).toFinset with hS_def
  have hSD : ({z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} : Set _) = (S : Set _) :=
    (Set.Finite.coe_toFinset _).symm
  simp only [hSD]
  refine restrict_quantile_sq_bound_at_endpoint J S subset_rfl hb fun a' ha' hab' => ?_
  obtain ⟨β, hβ1, hβ2⟩ := exists_between (max_lt hab hab')
  have hχ' : chi (intensityProfile J a') 0 < ⊤ :=
    (chi_mono (fun e => intensityProfile_mono J
      ((le_max_right a a').trans hβ1.le) e) 0).trans_lt
      (hχ β ((le_max_left a a').trans_lt hβ1) hβ2)
  have h := sq_tightnessScale_lt_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ ha' hχ' n
  simp only [hSD] at h
  have ha0 : (0 : ℝ) < a' := by exact_mod_cast ha'
  rw [div_mul_eq_mul_div, lt_div_iff₀ ha0] at h
  rw [mul_comm]
  convert h.le using 4
  congr 1
  ext z
  simp [hS_def]

open Classical in
/-- **Prop. 2.12(ii) at a general intensity** (lower block mean from boundary flux). If
`J(u, v) ≤ C L^{-(d+α) h(v-u)}` off the diagonal and
`1 ≤ b ∑_{u ∈ Λ_n} P_b(0 ↔ u inside Λ_n) ∑_{v ∉ Λ_n} J(u, v)`, then
`(L^α - 1)/(b C (1 - L^{-d})) L^{αn} ≤ a_n(b)`. -/
theorem ofReal_le_lintegral_clusterIntersection_of_boundaryFlux (hL : 2 ≤ L) {α C : ℝ}
    (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (b : ℝ≥0) (n : ℕ)
    (hflux : 1 ≤ (b : ℝ≥0∞) * ∑ u ∈ (finite_level_ball n).toFinset,
      law (intensityProfile J b)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 u) *
      ∑' v, (if v ∈ (finite_level_ball n).toFinset then 0 else (J s(u, v) : ℝ≥0∞))) :
    ENNReal.ofReal (((L : ℝ) ^ α - 1) / ((b : ℝ) * C * (1 - (L : ℝ) ^ (-(d : ℝ)))) *
          (L : ℝ) ^ (α * n)) ≤
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0) := by
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball n).toFinset with hS_def
  have hmemS : ∀ v : ℕ →₀ (Fin d → ZMod L), v ∈ S ↔ v.support.sup Nat.succ ≤ n := fun v => by
    simp [hS_def]
  have h0S : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ S := by simp [hmemS]
  have hSD : ({z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} : Set _) = (S : Set _) :=
    (Set.Finite.coe_toFinset _).symm
  rw [lintegral_clusterIntersection_restrict_eq_sum _ S (Set.Finite.coe_toFinset _) h0S]
  rw [hSD] at hflux
  set P : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun u =>
    law (intensityProfile J b) (localConn (S : Set _) 0 u) with hP_def
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
  have h1 : 1 ≤ (b : ℝ≥0∞) * (∑ u ∈ S, P u) * ENNReal.ofReal K := by
    refine hflux.trans ?_
    rw [mul_assoc, Finset.sum_mul]
    exact mul_le_mul' le_rfl (Finset.sum_le_sum fun u hu =>
        mul_le_mul' le_rfl (by convert hrow u hu))
  change _ ≤ ∑ u ∈ S, P u
  set a := ∑ u ∈ S, P u with ha_def
  rcases eq_or_ne a ⊤ with hat | hat
  · rw [hat]
    exact le_top
  set ar := a.toReal with har
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_toReal hat, ← har,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg b), ← ENNReal.ofReal_mul
      (mul_nonneg (NNReal.coe_nonneg b) ENNReal.toReal_nonneg), ENNReal.one_le_ofReal] at h1
  rw [← ENNReal.ofReal_toReal hat, ← har]
  refine ENNReal.ofReal_le_ofReal ?_
  set βr : ℝ := (b : ℝ) with hβr
  have hβr0 : 0 ≤ βr := NNReal.coe_nonneg b
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

omit [NeZero L] in
/-- If some kernel satisfies `c L^{-(d+α)h} ≤ J ≤ C L^{-(d+α)h}` off the diagonal on a lattice
with `d ≥ 1`, then `c ≤ C`. -/
theorem le_of_powerLaw_envelope (hL : 2 ≤ L) (hd : 1 ≤ d) {α c C : ℝ}
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) :
    c ≤ C := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Fact (1 < L) := ⟨by omega⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : ℕ →₀ (Fin d → ZMod L))
  exact le_of_mul_le_mul_right ((hJ 0 v hv.symm).trans (hJu 0 v hv.symm))
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < L by omega)) _)

open Classical in
/-- **Pointwise lower bound at an endpoint** (Hutchcroft, arXiv:2103.17013v1, Lemma 2.8 and
Prop. 2.12, pointwise form). Let `J` be translation invariant with
`c L^{-(d+α)h} ≤ J ≤ C₀ L^{-(d+α)h}` off the diagonal, `0 < α < d`, `a < b`, `χ_β(0) < ∞` for
`β ∈ (a, b)`, and `1 ≤ b ∑_{u ∈ Λ_n} τ_n(0,u) ∑_{v ∉ Λ_n} J(u,v)` for every `n`. Then there is
`c₁ > 0` with `c₁ L^{-(d-α)n} ≤ P_b(0 ↔ x inside Λ_n)` whenever `h x = n ≥ 1`. -/
theorem exists_ofReal_le_law_localConn_of_boundaryFlux (hL : 2 ≤ L) (hd : 1 ≤ d)
    {α c C₀ : ℝ} (hc : 0 < c) (hα : 0 < α) (hαd : α < d)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤)
    (hflux : ∀ n : ℕ, 1 ≤ (b : ℝ≥0∞) * ∑ u ∈ (finite_level_ball n).toFinset,
      law (intensityProfile J b)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 u) *
      ∑' v, (if v ∈ (finite_level_ball n).toFinset then 0 else (J s(u, v) : ℝ≥0∞))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ →₀ (Fin d → ZMod L),
      x.support.sup Nat.succ = n →
      ENNReal.ofReal (c₁ * (L : ℝ) ^ (-((d : ℝ) - α) * n)) ≤
        law (intensityProfile J b)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) := by
  have hb0 : 0 < b := lt_of_le_of_lt zero_le hab
  have hβr : (0 : ℝ) < b := by exact_mod_cast hb0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hC₀ : 0 < C₀ := hc.trans_le (le_of_powerLaw_envelope hL hd J hJ hJu)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) *
    Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) with hA_def
  set k : ℝ := c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) with hk_def
  have hk0 : 0 < k := by rw [hk_def]; positivity
  have hdpos : (0 : ℝ) < d := hα.trans hαd
  have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
  have hLd : 0 < 1 - (L : ℝ) ^ (-(d : ℝ)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith))
  set β₀ : ℝ := ((L : ℝ) ^ α - 1) / (C₀ * (1 - (L : ℝ) ^ (-(d : ℝ)))) with hβ₀_def
  have hβ₀ : 0 < β₀ := by rw [hβ₀_def]; positivity
  refine ⟨k * β₀ ^ 2 * (L : ℝ) ^ (-(2 * α)) / b, by positivity, fun n hn x hx => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hM : (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J b e else 0)
      (finite_level_ball m).toFinset : ℝ) ^ 2 ≤ A / b * (L : ℝ) ^ (((d : ℝ) + α) * m) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hβr, mul_comm]
    exact mul_sq_tightnessScale_le_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ hab hχ m
  have hlow := ofReal_mul_sq_le_tau_of_level_eq (by omega : 1 ≤ L) hα.le hc J hJt hJ hb0 m hM hx
  rw [tau_restrict_eq_law_localConn _ _ (by simp)] at hlow
  have hend := ofReal_le_lintegral_clusterIntersection_of_boundaryFlux hL hα J hJu b m (hflux m)
  have hend' : ENNReal.ofReal (β₀ / b * (L : ℝ) ^ (α * m)) ≤
      ∫⁻ ω, (clusterIntersection (finite_level_ball m).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J b e else 0) := by
    refine le_of_eq_of_le ?_ hend
    rw [hβ₀_def]
    congr 2
    field_simp
  refine le_trans ?_ ((mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hend' 2)).trans hlow)
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e1 : (L : ℝ) ^ (-(((d : ℝ) + α) * ((m : ℝ) + 1))) * ((L : ℝ) ^ (α * m)) ^ 2 =
      (L : ℝ) ^ (-(2 * α)) * (L : ℝ) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) := by
    rw [sq, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  calc k * β₀ ^ 2 * (L : ℝ) ^ (-(2 * α)) / b * (L : ℝ) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ))
      = k * β₀ ^ 2 / b * ((L : ℝ) ^ (-(2 * α)) *
          (L : ℝ) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ))) := by ring
    _ = k * β₀ ^ 2 / b * ((L : ℝ) ^ (-(((d : ℝ) + α) * ((m : ℝ) + 1))) *
          ((L : ℝ) ^ (α * m)) ^ 2) := by rw [e1]
    _ = k * b * (L : ℝ) ^ (-(((d : ℝ) + α) * ((m : ℝ) + 1))) *
          (β₀ / b * (L : ℝ) ^ (α * m)) ^ 2 := by
        field_simp

open Classical in
/-- **Pointwise upper bound at an endpoint** (Hutchcroft, arXiv:2103.17013v1, Props. 2.7 and
2.10, pointwise form). Let `J` be translation invariant with
`c L^{-(d+α)h} ≤ J ≤ C₀ L^{-(d+α)h}` off the diagonal, `0 < α < d`, `a < b` and `χ_β(0) < ∞`
for `β ∈ (a, b)`. Then there is `C₁ > 0` with `τ_b(0, x) ≤ C₁ L^{-(d-α)n}` whenever
`h x = n ≥ 1`. -/
theorem exists_tau_le_of_chi_lt_top (hL : 2 ≤ L) (hd : 1 ≤ d)
    {α c C₀ : ℝ} (hc : 0 < c) (hα : 0 < α) (hαd : α < d)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ →₀ (Fin d → ZMod L),
      x.support.sup Nat.succ = n →
      tau (intensityProfile J b) 0 x ≤ ENNReal.ofReal (C₁ * (L : ℝ) ^ (-((d : ℝ) - α) * n)) := by
  have hb0 : 0 < b := lt_of_le_of_lt zero_le hab
  have hβr : (0 : ℝ) < b := by exact_mod_cast hb0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hC₀ : 0 < C₀ := hc.trans_le (le_of_powerLaw_envelope hL hd J hJ hJu)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) *
    Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) with hA_def
  have hM : ∀ m : ℕ, (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J b e else 0)
      (finite_level_ball m).toFinset : ℝ) ^ 2 ≤ A / b * (L : ℝ) ^ (((d : ℝ) + α) * m) := by
    intro m
    rw [div_mul_eq_mul_div, le_div_iff₀ hβr, mul_comm]
    exact mul_sq_tightnessScale_le_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ hab hχ m
  set C' : ℝ := (L : ℝ) ^ α / (c / 4 * Real.exp (-(c * A * 99 ^ 2 *
    (L : ℝ) ^ (-((d : ℝ) + α)))) * (L : ℝ) ^ (-((d : ℝ) + α)) * b) with hC'_def
  have hC'0 : 0 < C' := by rw [hC'_def]; positivity
  have hLpow : ∀ x : ℝ, ((L : ℝ≥0∞) ^ x) = ENNReal.ofReal ((L : ℝ) ^ x) := fun x => by
    rw [← ENNReal.ofReal_rpow_of_pos hL0, ENNReal.ofReal_natCast]
  have hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J b)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤
        ENNReal.ofReal C' * (L : ℝ≥0∞) ^ (α * m) := by
    intro m
    rw [tsum_law_localConn_level_ball_eq_lintegral, hLpow, ← ENNReal.ofReal_mul hC'0.le]
    exact lintegral_clusterIntersection_le_of_sq_tightnessScale_le hL hd hα hc J hJt hJ hb0 hM m
  have hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤
      ENNReal.ofReal C₀ *
        (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℕ)) := by
    intro u v huv
    rw [← ENNReal.ofReal_coe_nnreal, hLpow, ← ENNReal.ofReal_mul hC₀.le, neg_mul]
    exact ENNReal.ofReal_le_ofReal (hJu u v huv)
  have hLne0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hLtop : (L : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top L
  set G : ℝ≥0∞ := (b : ℝ≥0∞) * ENNReal.ofReal C₀ * ENNReal.ofReal C' ^ 2 *
    (L : ℝ≥0∞) ^ (-(d : ℝ)) * (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ with hG
  have hGtop : G ≠ ⊤ :=
    powerLaw_const_ne_top hL hαd b ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  set X : ℝ≥0∞ := (b : ℝ≥0∞) * ENNReal.ofReal C₀ * ENNReal.ofReal C' ^ 2 *
    (L : ℝ≥0∞) ^ (-α) with hX
  have hXtop : X ≠ ⊤ := by
    rw [hX, hLpow]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top
  refine ⟨(X + G).toReal + 1, by positivity, fun n hn x hx => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := tau_le_localConn_ball_add_powerLaw_of_translationInvariant J hJt (by omega : 1 ≤ L)
    hα hαd (ENNReal.ofReal C₀) hK b (ENNReal.ofReal C') hμ hx.le
  have h2 := law_localConn_ball_succ_le_of_level_eq J hJt
    (fun j : ℕ => ENNReal.ofReal C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * j)) hK
    (antitone_powerLaw_level (by omega) (by positivity) _) b m hx
  have key : (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ)) * (L : ℝ≥0∞) ^ (α * (m : ℝ)) *
      (L : ℝ≥0∞) ^ (α * ((m + 1 : ℕ) : ℝ)) =
      (L : ℝ≥0∞) ^ (-α) * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) := by
    rw [← ENNReal.rpow_add _ _ hLne0 hLtop, ← ENNReal.rpow_add _ _ hLne0 hLtop,
      ← ENNReal.rpow_add _ _ hLne0 hLtop]
    congr 1
    push_cast
    ring
  have h3 : law (intensityProfile J b)
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 x) ≤
      X * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) := by
    refine h2.trans ?_
    calc _ ≤ (b : ℝ≥0∞) *
          (ENNReal.ofReal C₀ * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) *
          (ENNReal.ofReal C' * (L : ℝ≥0∞) ^ (α * (m : ℝ))) *
          (ENNReal.ofReal C' * (L : ℝ≥0∞) ^ (α * ((m + 1 : ℕ) : ℝ))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hμ m)) (hμ (m + 1))
      _ = (b : ℝ≥0∞) * ENNReal.ofReal C₀ * ENNReal.ofReal C' ^ 2 *
          ((L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ)) * (L : ℝ≥0∞) ^ (α * (m : ℝ)) *
            (L : ℝ≥0∞) ^ (α * ((m + 1 : ℕ) : ℝ))) := by ring
      _ = X * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) := by
          rw [key, hX]
          ring
  calc tau (intensityProfile J b) 0 x
      ≤ X * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) +
          G * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) :=
        h1.trans (add_le_add h3 le_rfl)
    _ = (X + G) * (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) := (add_mul _ _ _).symm
    _ ≤ ENNReal.ofReal ((X + G).toReal + 1) *
          (L : ℝ≥0∞) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)) := by
        gcongr
        exact (ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨hXtop, hGtop⟩)).symm.le.trans
          (ENNReal.ofReal_le_ofReal (by linarith))
    _ = ENNReal.ofReal (((X + G).toReal + 1) *
          (L : ℝ) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ))) := by
        rw [hLpow, ← ENNReal.ofReal_mul (by positivity)]

end PercLib.Models
