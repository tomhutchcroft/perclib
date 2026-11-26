/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's sibling-block recursion, endpoint quantile bound, outer-shell
first-exit bound and power-law kernel tails, and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied and no definition is added.
Mathematical reference: T. Hutchcroft, *The critical two-point function for long-range
percolation on the hierarchical lattice*, arXiv:2103.17013v1, Propositions 2.7, 2.10 and 2.12.
-/
module

public import PercLib.Models.HierarchicalRestrictedSusc
public import PercLib.Models.HierarchicalPointwise
public import PercLib.Models.HierarchicalRunawayInterval
public import PercLib.Models.HierarchicalPowerKernel
public import PercLib.Percolation.Bond.SusceptibilityContinuity
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Conditional hierarchical two-point bounds at a general endpoint

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}`,
`q = intensityProfile J b`, `q_n` for `q` restricted to the pairs inside `Λ_n`,
`a_n = E_{q_n} |K_0 ∩ Λ_n|` and `τ_n(0, x) = P_q(0 ↔ x inside Λ_n)`. The kernel is translation
invariant with `J(u, v) ≥ c L^{-(d+α) h(v-u)}` off the diagonal, `0 < α < d`, and the endpoint
`b` satisfies `χ(β) < ∞` for `β ∈ (a, b)`, `a < b`.

The endpoint quantile bound (`sq_tightnessScale_le_of_chi_lt_top_on_Ioo`) feeds the sibling-block
recursion (`sum_shell_tau_ge`) and the deterministic runaway
(`lintegral_clusterIntersection_le_of_sq_tightnessScale_le`). Under an upper kernel bound
`J ≤ C₀ L^{-(d+α)h}`, the boundary flux at `Λ_n` bounds `a_n` below by a multiple of `L^{αn}`;
the pointwise sibling bound then gives the lower two-point bound, and summing the outer-shell
first-exit bound over the scales `m ≥ n` gives the upper one.

## Main results

* `exists_restricted_mean_sq_le_succ_of_chi_lt_top`: `a_{n+1} ≥ k L^{-αn} a_n²` for a fixed
  `k > 0`.
* `exists_restricted_mean_le_of_chi_lt_top`: `a_n ≤ C' L^{αn}` for a fixed `C' > 0`.
* `one_le_mul_restricted_mean_of_boundaryFlux`: the boundary flux at `Λ_n` gives
  `1 ≤ β D L^{-αn} a_n` with `D = C₀ (1 - L^{-d}) / (L^α - 1)`.
* `ofReal_le_law_localConn_of_boundaryFlux`: the pointwise lower bound
  `c₁ L^{-(d-α)(n+1)} ≤ τ_{n+1}(0, x)` for `h x = n + 1`.
* `tau_le_of_restricted_mean_le`: the pointwise upper bound `τ(0, x) ≤ C₁ L^{-(d-α)n}` for
  `h x = n ≥ 1`, from `a_m ≤ C' L^{αm}`.
* `exists_law_localConn_bounds_of_boundaryFlux`: the two-sided pointwise bounds at `b`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

/-! ### Restricted means at the endpoint -/

open Classical in
/-- **Quadratic recursion of the restricted means at an endpoint** (Hutchcroft,
arXiv:2103.17013v1, Lemma 2.8). For `L ≥ 2`, `c > 0`, `0 < α < d`, a translation-invariant `J`
with `J(u, v) ≥ c L^{-(d+α) h(v-u)}` off the diagonal, and `a < b` with `χ(β) < ∞` for every
`β ∈ (a, b)`, there is `k > 0` with `a_{n+1}(b) ≥ k L^{-αn} a_n(b)²` for every `n`. -/
theorem exists_restricted_mean_sq_le_succ_of_chi_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) :
    ∃ k : ℝ, 0 < k ∧ ∀ n : ℕ,
      ENNReal.ofReal (k * (L : ℝ) ^ (-(α * n))) *
          (∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
            ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
              z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0)) ^ 2 ≤
        ∫⁻ ω, (clusterIntersection (finite_level_ball (n + 1)).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n + 1}.sym2 then intensityProfile J b e else 0) := by
  have hd : 1 ≤ d := by
    have : (0 : ℝ) < d := hα.trans hαd
    exact_mod_cast this
  have hb : 0 < b := lt_of_le_of_lt zero_le hab
  have hb' : (0 : ℝ) < b := hb
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  refine ⟨c / 4 * Real.exp (-(c * ((4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) *
      Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)) * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
      (L : ℝ) ^ (-((d : ℝ) + α)) * b, mul_pos (by positivity) hb', fun n => ?_⟩
  exact (sum_shell_tau_ge hL hd hα hc J hJt hJ hb n
    (sq_tightnessScale_le_of_chi_lt_top_on_Ioo hL hc hα J hJt hJ hexp hℓ hab hχ n le_rfl)).trans
    (sum_shell_tau_le_lintegral_clusterIntersection _ n)

open Classical in
/-- **Upper bound on the restricted means at an endpoint** (Hutchcroft, arXiv:2103.17013v1,
Prop. 2.7). Under the hypotheses of `exists_restricted_mean_sq_le_succ_of_chi_lt_top` there is
`C' > 0` with `a_n(b) ≤ C' L^{αn}` for every `n`. -/
theorem exists_restricted_mean_le_of_chi_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ,
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J b e else 0) ≤
        ENNReal.ofReal (C' * (L : ℝ) ^ (α * n)) := by
  have hd : 1 ≤ d := by
    have : (0 : ℝ) < d := hα.trans hαd
    exact_mod_cast this
  have hb : 0 < b := lt_of_le_of_lt zero_le hab
  have hb' : (0 : ℝ) < b := hb
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  exact ⟨_, div_pos (Real.rpow_pos_of_pos hL0 α) (mul_pos (by positivity) hb'),
    lintegral_clusterIntersection_le_of_sq_tightnessScale_le hL hd hα hc J hJt hJ hb
      (fun m => sq_tightnessScale_le_of_chi_lt_top_on_Ioo hL hc hα J hJt hJ hexp hℓ hab hχ m
        le_rfl)⟩

/-! ### The boundary flux and the lower bound -/

open Classical in
/-- **Boundary flux bounds the restricted mean below.** If `J(u, v) ≤ C₀ L^{-(d+α) h(v-u)}`
off the diagonal and `1 ≤ β ∑_{u ∈ Λ_n} τ_n(0, u) ∑_{v ∉ Λ_n} J(u, v)`, then
`1 ≤ β D L^{-αn} a_n(β)` with `D = C₀ (1 - L^{-d}) / (L^α - 1)`. -/
theorem one_le_mul_restricted_mean_of_boundaryFlux [NeZero L] (hL : 2 ≤ L) {α C₀ : ℝ}
    (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (β : ℝ≥0) (n : ℕ)
    (hflux : 1 ≤ (β : ℝ≥0∞) * ∑ u ∈ (finite_level_ball n).toFinset,
      law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 u) *
        ∑' v, if n < v.support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0) :
    1 ≤ (β : ℝ≥0∞) * ENNReal.ofReal (C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) /
        ((L : ℝ) ^ α - 1)) *
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0) := by
  rw [← tsum_law_localConn_level_ball_eq_lintegral,
    tsum_eq_sum (s := (finite_level_ball n).toFinset) (fun z hz => by
      rw [localConn_of_notMem_right (by simpa using hz), measure_empty]), mul_assoc]
  refine hflux.trans ?_
  gcongr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [mul_comm]
  gcongr
  exact tsum_level_gt_le_of_powerLaw hL hα J hJu n (by simpa using hu)

open Classical in
/-- **Pointwise lower bound from the boundary flux** (Hutchcroft, arXiv:2103.17013v1,
Prop. 2.12, lower half). Under the hypotheses of `ofReal_mul_sq_le_tau_of_level_eq` at scale `n`
(quantile bound `M_n(β)² ≤ (A/β) L^{(d+α)n}`), with `J(u, v) ≤ C₀ L^{-(d+α) h(v-u)}` and the
boundary flux at `Λ_n`, for every `x` with `h x = n + 1`,
`c₁ L^{-(d-α)(n+1)} ≤ τ_{n+1}(0, x)` where `c₁ = k' L^{-2α} / (β D²)`, `k' = (c/4) e^{-T}`,
`T = c A 99² L^{-(d+α)}` and `D = C₀ (1 - L^{-d}) / (L^α - 1)`. -/
theorem ofReal_le_law_localConn_of_boundaryFlux [NeZero L] (hL : 2 ≤ L) {α c A C₀ : ℝ}
    (hα : 0 < α) (hc : 0 < c) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    {β : ℝ≥0} (hβ : 0 < β) (n : ℕ)
    (hM : (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤ A / β * (L : ℝ) ^ (((d : ℝ) + α) * n))
    (hflux : 1 ≤ (β : ℝ≥0∞) * ∑ u ∈ (finite_level_ball n).toFinset,
      law (intensityProfile J β)
          (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 u) *
        ∑' v, if n < v.support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0)
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = n + 1) :
    ENNReal.ofReal (c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
        (L : ℝ) ^ (-(2 * α)) /
        (β * (C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1)) ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - α) * ((n : ℝ) + 1)))) ≤
      law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n + 1} 0 x) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hβ' : (0 : ℝ) < β := hβ
  have hstep := ofReal_mul_sq_le_tau_of_level_eq (by omega) hα.le hc J hJt hJ hβ n hM hx
  rw [tau_restrict_eq_law_localConn _ _ (by simp)] at hstep
  refine le_trans ?_ hstep
  have hfl := one_le_mul_restricted_mean_of_boundaryFlux hL hα J hJu β n hflux
  set D : ℝ := C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1) with hD_def
  set k : ℝ := c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) with hk_def
  set Am := ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
    ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0) with hAm
  have hAm_ne : Am ≠ ⊤ := lintegral_clusterIntersection_ne_top _ _ _
  have hk : 0 < k := by rw [hk_def]; positivity
  have hDL_def : C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * n)) / ((L : ℝ) ^ α - 1) =
      D * (L : ℝ) ^ (-(α * n)) := by rw [hD_def]; ring
  rw [hDL_def] at hfl
  have hLn : 0 < (L : ℝ) ^ (-(α * n)) := Real.rpow_pos_of_pos hL0 _
  have hD : 0 < D := by
    by_contra hD
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hD) hLn.le),
      mul_zero, zero_mul] at hfl
    exact absurd hfl (by norm_num)
  -- the flux in real form
  have hfl' : 1 ≤ β * (D * (L : ℝ) ^ (-(α * n))) * Am.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top) hAm_ne) hfl
    rwa [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (by positivity)] at h
  set s : ℝ := β * (D * (L : ℝ) ^ (-(α * n))) with hs_def
  have hs : 0 < s := by positivity
  have has : 1 / s ≤ Am.toReal := by rw [div_le_iff₀ hs]; linarith
  rw [← ENNReal.ofReal_toReal hAm_ne, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) =
      (L : ℝ) ^ (-(2 * α)) * (L : ℝ) ^ (-(((d : ℝ) - α) * ((n : ℝ) + 1))) *
        ((L : ℝ) ^ (-(α * n))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  calc k * (L : ℝ) ^ (-(2 * α)) / (β * D ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - α) * ((n : ℝ) + 1)))
      = k * β * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) * (1 / s) ^ 2 := by
        rw [hpow, hs_def]
        field_simp
    _ ≤ k * β * (L : ℝ) ^ (-(((d : ℝ) + α) * ((n : ℝ) + 1))) * Am.toReal ^ 2 := by
        gcongr

/-! ### The upper bound -/

open Classical in
/-- **Pointwise upper bound from the restricted means** (Hutchcroft, arXiv:2103.17013v1,
Prop. 2.12, upper half). Let `J` be translation invariant with
`J(u, v) ≤ C₀ L^{-(d+α) h(v-u)}` off the diagonal, `C₀ > 0`, `0 < α < d`, and suppose
`a_m(β) ≤ C' L^{αm}` for every `m`. Then for every `x` with `h x = n ≥ 1`,
`τ(0, x) ≤ C₁ L^{-(d-α)n}` with `C₁ = β C₀ C'² L^{-α} / (1 - L^{-(d-α)})`.
Summing the first-exit bound `τ_{m+1}(0,x) ≤ τ_m(0,x) + β C₀ L^{-(d+α)(m+1)} a_m a_{m+1}` over
`m ≥ n - 1`, starting from `τ_{n-1}(0, x) = 0`, and passing to the increasing limit. -/
theorem tau_le_of_restricted_mean_le [NeZero L] (hL : 2 ≤ L) {α C₀ C' : ℝ}
    (hα : 0 < α) (hαd : α < d) (hC₀ : 0 < C₀) (hC' : 0 ≤ C')
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (β : ℝ≥0)
    (ha : ∀ m : ℕ, ∫⁻ ω, (clusterIntersection (finite_level_ball m).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0) ≤
        ENNReal.ofReal (C' * (L : ℝ) ^ (α * m)))
    {n : ℕ} (hn : 1 ≤ n) {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ = n) :
    tau (intensityProfile J β) 0 x ≤
      ENNReal.ofReal (β * C₀ * C' ^ 2 * (L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-((d : ℝ) - α))) *
        (L : ℝ) ^ (-(((d : ℝ) - α) * n))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  set q := intensityProfile J β with hq
  set r : ℝ := (L : ℝ) ^ (-((d : ℝ) - α)) with hr_def
  set G : ℝ := β * C₀ * C' ^ 2 * (L : ℝ) ^ (-α) with hG_def
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hL0 _).le
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have hG : 0 ≤ G := by rw [hG_def]; positivity
  have hrpow : ∀ m : ℕ, r ^ m = (L : ℝ) ^ (-(((d : ℝ) - α) * m)) := fun m => by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    ring_nf
  set K : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * j))) with hK_def
  have hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤ K ((v - u).support.sup Nat.succ) :=
    fun u v huv => by
      rw [hK_def, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hJu u v huv)
  have hKa : Antitone K := fun i j hij => by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1.le ?_) hC₀.le)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  set P : ℕ → ℝ≥0∞ := fun m =>
    law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 x) with hP
  have hmu : ∀ m : ℕ, ∑' z, law q
      (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤
        ENNReal.ofReal (C' * (L : ℝ) ^ (α * m)) := fun m => by
    rw [tsum_law_localConn_level_ball_eq_lintegral]
    exact ha m
  have hinc : ∀ m : ℕ, (β : ℝ≥0∞) * K (m + 1) *
      (∑' z, law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z)) *
      (∑' z, law q
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} 0 z)) ≤
      ENNReal.ofReal (G * r ^ (m + 1)) := fun m => by
    refine (mul_le_mul' (mul_le_mul' le_rfl (hmu m)) (hmu (m + 1))).trans (le_of_eq ?_)
    rw [hK_def, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hrpow]
    congr 1
    rw [hG_def]
    have e1 : (L : ℝ) ^ (-(((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) * (L : ℝ) ^ (α * (m : ℕ)) *
        (L : ℝ) ^ (α * ((m + 1 : ℕ) : ℝ)) =
        (L : ℝ) ^ (-α) * (L : ℝ) ^ (-(((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ))) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1
      push_cast
      ring
    calc (β : ℝ) * (C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ)))) *
          (C' * (L : ℝ) ^ (α * (m : ℕ))) * (C' * (L : ℝ) ^ (α * ((m + 1 : ℕ) : ℝ)))
        = β * C₀ * C' ^ 2 * ((L : ℝ) ^ (-(((d : ℝ) + α) * ((m + 1 : ℕ) : ℝ))) *
            (L : ℝ) ^ (α * (m : ℕ)) * (L : ℝ) ^ (α * ((m + 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [e1]; ring
  have hclaim : ∀ m : ℕ, P m ≤ ENNReal.ofReal (G * ∑ i ∈ Finset.Ico n (m + 1), r ^ i) := by
    intro m
    induction m with
    | zero =>
      have hx0 : x ∉ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ 0} := by
        simp only [Set.mem_ofPred_eq, hx]; omega
      simp only [hP, localConn_of_notMem_right hx0, measure_empty]
      exact zero_le
    | succ m ih =>
      by_cases hnm : n ≤ m + 1
      · have h1 := law_localConn_ball_succ_le_add_of_translationInvariant J hJt K hK hKa β m
          (x := x) (by omega)
        refine h1.trans ((add_le_add ih (hinc m)).trans (le_of_eq ?_))
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), Finset.sum_Ico_succ_top
          (by omega : n ≤ m + 1), mul_add]
      · have hx0 : x ∉ {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m + 1} := by
          simp only [Set.mem_ofPred_eq, hx]; omega
        simp only [hP, localConn_of_notMem_right hx0, measure_empty]
        exact zero_le
  rw [tau_eq_iSup_localConn q (S := fun m => {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ m}) (fun i j hij z hz => le_trans hz hij)
      (fun v => ⟨v.support.sup Nat.succ,
        show v.support.sup Nat.succ ≤ v.support.sup Nat.succ from le_rfl⟩) 0 x]
  refine iSup_le fun m => (hclaim m).trans (ENNReal.ofReal_le_ofReal ?_)
  calc G * ∑ i ∈ Finset.Ico n (m + 1), r ^ i ≤ G * (r ^ n / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) hG
    _ = _ := by rw [← hrpow n]; ring

/-! ### Two-sided pointwise bounds -/

open Classical in
/-- **Conditional hierarchical two-point bounds** (Hutchcroft, arXiv:2103.17013v1,
Props. 2.10 and 2.12, at a general endpoint). For `L ≥ 2`, `c > 0`, `0 < α < d`, a
translation-invariant `J` with `c L^{-(d+α)h(v-u)} ≤ J(u, v) ≤ C₀ L^{-(d+α)h(v-u)}` off the
diagonal, `a < b` with `χ(β) < ∞` for `β ∈ (a, b)`, and the boundary flux
`b ∑_{u ∈ Λ_n} τ_n(0, u) ∑_{v ∉ Λ_n} J(u, v) ≥ 1` for every `n`, there are `c₁, C₁ > 0` with
`c₁ L^{-(d-α)n} ≤ τ_n(0, x) ≤ τ(0, x) ≤ C₁ L^{-(d-α)n}` whenever `h x = n ≥ 1`. -/
theorem exists_law_localConn_bounds_of_boundaryFlux [NeZero L] (hL : 2 ≤ L) {α c C₀ : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
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
        ∑' v, if n < v.support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ →₀ (Fin d → ZMod L),
      x.support.sup Nat.succ = n →
      ENNReal.ofReal (c₁ * (L : ℝ) ^ (-(((d : ℝ) - α) * n))) ≤
          law (intensityProfile J b)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) ∧
        law (intensityProfile J b)
            (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x) ≤
          tau (intensityProfile J b) 0 x ∧
        tau (intensityProfile J b) 0 x ≤
          ENNReal.ofReal (C₁ * (L : ℝ) ^ (-(((d : ℝ) - α) * n))) := by
  have hb : 0 < b := lt_of_le_of_lt zero_le hab
  have hb' : (0 : ℝ) < b := hb
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  obtain ⟨C', hC', hC'a⟩ := exists_restricted_mean_le_of_chi_lt_top hL hc hα hαd J hJt hJ hab hχ
  -- a positive upper constant
  set C₁' : ℝ := max C₀ 1 with hC₁'
  have hC₁'pos : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hJu' : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₁' * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) :=
    fun u v huv => (hJu u v huv).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_pos_of_pos hL0 _).le)
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)
    with hA_def
  set D : ℝ := C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1) with hD_def
  -- `D > 0` follows from the flux at scale `0`
  have hD : D ≠ 0 := by
    intro hD0
    have h := one_le_mul_restricted_mean_of_boundaryFlux hL hα J hJu b 0 (hflux 0)
    have : C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * ((0 : ℕ) : ℝ))) /
        ((L : ℝ) ^ α - 1) = 0 := by
      rw [show C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) * (L : ℝ) ^ (-(α * ((0 : ℕ) : ℝ))) /
        ((L : ℝ) ^ α - 1) = D * (L : ℝ) ^ (-(α * ((0 : ℕ) : ℝ))) by rw [hD_def]; ring, hD0,
        zero_mul]
    rw [this, ENNReal.ofReal_zero, mul_zero, zero_mul] at h
    exact absurd h (by norm_num)
  refine ⟨c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
      (L : ℝ) ^ (-(2 * α)) / (b * D ^ 2),
    b * C₁' * C' ^ 2 * (L : ℝ) ^ (-α) / (1 - (L : ℝ) ^ (-((d : ℝ) - α))),
    by positivity, ?_, fun n hn x hx => ⟨?_, law_localConn_le_tau _ _ 0 x,
      tau_le_of_restricted_mean_le hL hα hαd hC₁'pos hC'.le J hJt hJu' b hC'a hn hx⟩⟩
  · have hr1 : (L : ℝ) ^ (-((d : ℝ) - α)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
    have : 0 < 1 - (L : ℝ) ^ (-((d : ℝ) - α)) := by linarith
    positivity
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := ofReal_le_law_localConn_of_boundaryFlux hL hα hc J hJt hJ hJu hb m
      (sq_tightnessScale_le_of_chi_lt_top_on_Ioo hL hc hα J hJt hJ hexp hℓ hab hχ m le_rfl)
      (hflux m) hx
    convert h using 3
    push_cast
    ring

end PercLib.Models
