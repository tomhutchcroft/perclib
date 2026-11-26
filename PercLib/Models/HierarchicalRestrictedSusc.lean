/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's sibling-block recursion, threshold endpoint and power-law kernel
theorems, and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is
copied and no definition is added. Mathematical reference: T. Hutchcroft, arXiv:2103.17013v1,
Proposition 2.7 (proved at `β = β_c` directly, from the quantile bound at the threshold).
-/
module

public import PercLib.Models.HierarchicalEndpoint
public import PercLib.Percolation.Bond.Tightness.Hyperscaling

/-!
# The restricted susceptibility at the critical point

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}`, `q_n(β)`
for `intensityProfile J β` restricted to the pairs inside `Λ_n`,
`M_n(β) = tightnessScale q_n(β) Λ_n` and `a_n(β) = E_{q_n(β)} |K_0 ∩ Λ_n|`, all spelled as in
`sum_shell_tau_ge`.

The sibling-block recursion `a_{n+1} ≥ k β L^{-αn} a_n²` and the volume bound `a_n ≤ L^{dn}`
force `a_n ≤ (L^α / (k β)) L^{αn}`: with `y_n = k β L^{-α(n+1)} a_n` one has `y_{n+1} ≥ y_n²`
and `y_n ≤ (k β L^{-α}) (L^{d-α})^n`, and a sequence that squares at each step but grows at most
exponentially stays at most `1`. At `β = β_c` the quantile hypothesis is the endpoint bound
and `β_c ≥ (L^α - 1)/(C (1 - L^{-d}))`, so the constant depends only on `d, L, α, c, C`.
Monotonicity in `β` is not used.

## Main results

* `le_one_of_sq_le_succ_of_le_mul_pow`: if `y_n² ≤ y_{n+1}` and `y_n ≤ K R^n` with `R ≥ 0`, then
  `y_n ≤ 1` for every `n`.
* `sum_shell_tau_le_lintegral_clusterIntersection`: the shell sum of `P_{q_{n+1}}(0 ↔ x)` is at
  most `a_{n+1}`.
* `lintegral_clusterIntersection_le_of_sq_tightnessScale_le` (Prop. 2.7 at a general `β`): if
  `M_n(β)² ≤ (A/β) L^{(d+α)n}` for every `n`, then `a_n(β) ≤ (L^α / (k β)) L^{αn}` for every `n`,
  with `k = (c/4) e^{-T} L^{-(d+α)}` and `T = c A 99² L^{-(d+α)}`.
* `exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity` (Prop. 2.7): there is
  `C' > 0` depending only on `d, L, α, c, C` such that `a_n(β_c) ≤ C' L^{αn}` for every `n` and
  every translation-invariant `J` with `c L^{-(d+α)h} ≤ J ≤ C L^{-(d+α)h}` off the diagonal.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-! ### A sequence that squares at each step -/

/-- **Deterministic runaway.** A real sequence with `y_n² ≤ y_{n+1}` and `y_n ≤ K R^n` for some
`R ≥ 0` satisfies `y_n ≤ 1` for every `n`: once `y_m > 1`, `y_{m+j} ≥ y_m^{2^j}` outgrows every
exponential. -/
theorem le_one_of_sq_le_succ_of_le_mul_pow {y : ℕ → ℝ} {K R : ℝ} (hR : 0 ≤ R)
    (hsq : ∀ n, y n ^ 2 ≤ y (n + 1)) (hle : ∀ n, y n ≤ K * R ^ n) (n : ℕ) : y n ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  set R' := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := zero_lt_one.trans_le hR'1
  have hK : 0 ≤ K := by
    by_contra hK
    have := hle n
    nlinarith [pow_nonneg hR n]
  have hle' : ∀ m, y m ≤ K * R' ^ m := fun m =>
    (hle m).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR (le_max_left _ _) m) hK)
  -- `y_n^{2^j} ≤ y_{n+j}`
  have hy0 : 0 ≤ y n := zero_le_one.trans hcon.le
  have hpow : ∀ j, y n ^ 2 ^ j ≤ y (n + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y n ^ 2 ^ (j + 1) = (y n ^ 2 ^ j) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ y (n + j) ^ 2 := pow_le_pow_left₀ (pow_nonneg hy0 _) ih 2
        _ ≤ y (n + (j + 1)) := hsq (n + j)
  -- a scale `p` with `Q = y_n^{2^p} > R'`
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt R' hcon
  set Q := y n ^ 2 ^ p with hQ
  have hQR : R' < Q := hp.trans_le (pow_le_pow_right₀ hcon.le (Nat.lt_two_pow_self).le)
  have hQ1 : 1 ≤ Q := hR'1.trans hQR.le
  -- `Q^j ≤ K R'^{n+p} R'^j` for every `j`
  have hj : ∀ j, Q ^ j ≤ K * R' ^ (n + p) * R' ^ j := by
    intro j
    calc Q ^ j ≤ Q ^ 2 ^ j := pow_le_pow_right₀ hQ1 (Nat.lt_two_pow_self).le
      _ = y n ^ 2 ^ (p + j) := by rw [hQ, ← pow_mul, ← pow_add]
      _ ≤ y (n + (p + j)) := hpow (p + j)
      _ ≤ K * R' ^ (n + (p + j)) := hle' _
      _ = K * R' ^ (n + p) * R' ^ j := by rw [← add_assoc, pow_add, mul_assoc]
  obtain ⟨j, hjQ⟩ := pow_unbounded_of_one_lt (K * R' ^ (n + p)) ((one_lt_div hR'0).2 hQR)
  have h := hj j
  rw [div_pow, lt_div_iff₀ (pow_pos hR'0 j)] at hjQ
  linarith

variable {d L : ℕ}

/-! ### Prop. 2.7 -/

open Classical in
/-- **Shell sum and the next block mean.** `∑_{x ∈ Λ_{n+1} \ Λ_n} P_{q_{n+1}}(0 ↔ x) ≤ a_{n+1}`,
for any profile `q` restricted to the pairs inside `Λ_{n+1}`. -/
theorem sum_shell_tau_le_lintegral_clusterIntersection [NeZero L]
    (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval) (n : ℕ) :
    ∑ x ∈ (finite_level_ball (n + 1)).toFinset \ (finite_level_ball n).toFinset,
        tau (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n + 1}.sym2 then q e else 0) 0 x ≤
      ∫⁻ ω, (clusterIntersection (finite_level_ball (n + 1)).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n + 1}.sym2 then q e else 0) := by
  rw [lintegral_clusterIntersection_eq_sum_tau]
  exact Finset.sum_le_sum_of_subset Finset.sdiff_subset

open Classical in
/-- **Prop. 2.7 at a general intensity** (Hutchcroft, arXiv:2103.17013v1, Prop. 2.7, from the
sibling-block recursion and the volume bound). Under the hypotheses of `sum_shell_tau_ge`, if
`M_n(β)² ≤ (A/β) L^{(d+α)n}` for every `n`, then for every `n`

`a_n(β) = E_{q_n(β)} |K_0 ∩ Λ_n| ≤ (L^α / (k β)) L^{αn}`,

with `k = (c/4) e^{-T} L^{-(d+α)}` and `T = c A 99² L^{-(d+α)}`. -/
theorem lintegral_clusterIntersection_le_of_sq_tightnessScale_le [NeZero L] (hL : 2 ≤ L)
    (hd : 1 ≤ d) {α c A : ℝ} (hα : 0 < α) (hc : 0 < c) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {β : ℝ≥0} (hβ : 0 < β)
    (hM : ∀ n : ℕ, (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤ A / β * (L : ℝ) ^ (((d : ℝ) + α) * n))
    (n : ℕ) :
    ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0) ≤
      ENNReal.ofReal ((L : ℝ) ^ α / (c / 4 * Real.exp (-(c * A * 99 ^ 2 *
        (L : ℝ) ^ (-((d : ℝ) + α)))) * (L : ℝ) ^ (-((d : ℝ) + α)) * β) * (L : ℝ) ^ (α * n)) := by
  set k : ℝ := c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
    (L : ℝ) ^ (-((d : ℝ) + α)) with hk_def
  set a : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, (clusterIntersection (finite_level_ball m).toFinset ω 0 :
      ℝ≥0∞) ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0) with ha_def
  change a n ≤ _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hk : 0 < k := by rw [hk_def]; positivity
  set ρ : ℝ := (L : ℝ) ^ α with hρ_def
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hL0 α
  have hρn : ∀ m : ℕ, (L : ℝ) ^ (α * m) = ρ ^ m := fun m => by
    rw [hρ_def, Real.rpow_mul hL0.le, Real.rpow_natCast]
  have hne : ∀ m, a m ≠ ⊤ := fun m => lintegral_clusterIntersection_ne_top _ _ _
  -- the volume bound
  have hvol : ∀ m, (a m).toReal ≤ ((L : ℝ) ^ d) ^ m := by
    intro m
    have h : a m ≤ (((L ^ d) ^ m : ℕ) : ℝ≥0∞) := by
      rw [← card_toFinset_level_ball (d := d) (L := L) m]
      calc a m ≤ ∫⁻ _, ((finite_level_ball (A := Fin d → ZMod L) m).toFinset.card : ℝ≥0∞)
            ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
              z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0) :=
            lintegral_mono fun ω => Nat.cast_le.2 (clusterIntersection_le_card _ ω 0)
        _ = _ := by simp
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
    simpa using this
  -- the recursion, in real numbers
  have hrec : ∀ m : ℕ, k * β * (ρ ^ m)⁻¹ * (a m).toReal ^ 2 ≤ (a (m + 1)).toReal := by
    intro m
    have h := (sum_shell_tau_ge hL hd hα hc J hJt hJ hβ m (hM m)).trans
      (sum_shell_tau_le_lintegral_clusterIntersection (intensityProfile J β) m)
    have h' := ENNReal.toReal_mono (hne (m + 1)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow,
      Real.rpow_neg hL0.le (α * m), hρn, ← hk_def] at h'
    exact h'
  -- the runaway
  set y : ℕ → ℝ := fun m => k * β * (ρ ^ (m + 1))⁻¹ * (a m).toReal with hy_def
  have hsq : ∀ m, y m ^ 2 ≤ y (m + 1) := by
    intro m
    calc y m ^ 2 = k * β * (ρ ^ (m + 2))⁻¹ * (k * β * (ρ ^ m)⁻¹ * (a m).toReal ^ 2) := by
          rw [hy_def]; field_simp; ring
      _ ≤ k * β * (ρ ^ (m + 2))⁻¹ * (a (m + 1)).toReal :=
          mul_le_mul_of_nonneg_left (hrec m) (by positivity)
      _ = y (m + 1) := by rw [hy_def]
  have hgrow : ∀ m, y m ≤ k * β / ρ * ((L : ℝ) ^ d / ρ) ^ m := by
    intro m
    calc y m ≤ k * β * (ρ ^ (m + 1))⁻¹ * ((L : ℝ) ^ d) ^ m :=
          mul_le_mul_of_nonneg_left (hvol m) (by positivity)
      _ = k * β / ρ * ((L : ℝ) ^ d / ρ) ^ m := by rw [div_pow, pow_succ]; field_simp
  have hy1 := le_one_of_sq_le_succ_of_le_mul_pow (by positivity) hsq hgrow n
  rw [← ENNReal.ofReal_toReal (hne n)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hρn]
  have hkβ : 0 < k * β := by positivity
  change k * β * (ρ ^ (n + 1))⁻¹ * (a n).toReal ≤ 1 at hy1
  rw [mul_comm (k * β), mul_assoc, inv_mul_le_iff₀ (pow_pos hρ _), mul_one, pow_succ,
    ← le_div_iff₀' hkβ] at hy1
  calc (a n).toReal ≤ ρ ^ n * ρ / (k * β) := hy1
    _ = ρ / (k * β) * ρ ^ n := by ring

open Classical in
/-- **Prop. 2.7** (655W, upper half; Hutchcroft, arXiv:2103.17013v1, Prop. 2.7, proved at
`β = β_c`). For `L ≥ 2`, `0 < α < d` and `c, C > 0` there is `C' > 0`, depending only on
`d, L, α, c, C`, such that for every translation-invariant kernel `J` with
`c L^{-(d+α) h(v-u)} ≤ J(u, v) ≤ C L^{-(d+α) h(v-u)}` for `u ≠ v` and every `n`,

`a_n(β_c) = E_{q_n(β_c)} |K_0 ∩ Λ_n| ≤ C' L^{αn}`,

where `β_c = rootCriticalIntensity J 0`. -/
theorem exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity [NeZero L]
    (hL : 2 ≤ L) {α c C : ℝ} (hc : 0 < c) (hC : 0 < C) (hα : 0 < α) (hαd : α < d) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
      (∀ x u v, J s(u + x, v + x) = J s(u, v)) →
      (∀ u v, u ≠ v →
        c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
          J s(u, v)) →
      (∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
        C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
      ∀ n : ℕ, ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ n}.sym2 then
              intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0) ≤
        ENNReal.ofReal (C' * (L : ℝ) ^ (α * n)) := by
  have hd : 1 ≤ d := by
    have : (0 : ℝ) < d := hα.trans hαd
    exact_mod_cast this
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)
    with hA_def
  set k : ℝ := c / 4 * Real.exp (-(c * A * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
    (L : ℝ) ^ (-((d : ℝ) + α)) with hk_def
  set β₀ : ℝ := ((L : ℝ) ^ α - 1) / (C * (1 - (L : ℝ) ^ (-(d : ℝ)))) with hβ₀_def
  have hk : 0 < k := by rw [hk_def]; positivity
  have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
  have hLd : 0 < 1 - (L : ℝ) ^ (-(d : ℝ)) := by
    rw [sub_pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hL1 (by
      have : (0 : ℝ) < d := hα.trans hαd
      linarith)
  have hβ₀ : 0 < β₀ := by rw [hβ₀_def]; positivity
  refine ⟨(L : ℝ) ^ α / (k * β₀), by positivity, fun J hJt hJ hJu n => ?_⟩
  obtain ⟨⟨hpos, htop⟩, hM⟩ :=
    rootCriticalIntensity_mem_Ioo_and_mul_sq_tightnessScale_le hL hc hα hαd J hJt hJ hJu hexp hℓ
  set β := (rootCriticalIntensity J 0).toNNReal with hβ_def
  have hβ : 0 < β := ENNReal.toNNReal_pos hpos.ne' htop.ne
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hM' : ∀ m : ℕ, (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0)
      (finite_level_ball m).toFinset : ℝ) ^ 2 ≤ A / β * (L : ℝ) ^ (((d : ℝ) + α) * m) := by
    intro m
    rw [div_mul_eq_mul_div, le_div_iff₀ hβ0, mul_comm]
    exact hM m
  have hββ₀ : β₀ ≤ β := by
    have h := ofReal_le_rootCriticalIntensity_of_powerLaw hL hα J hJu 0
    rw [ENNReal.ofReal_le_iff_le_toReal htop.ne] at h
    rwa [hβ_def, ENNReal.coe_toNNReal_eq_toReal]
  refine (lintegral_clusterIntersection_le_of_sq_tightnessScale_le hL hd hα hc J hJt hJ hβ hM'
    n).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← hk_def]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hL0.le _) (by positivity)
    (mul_le_mul_of_nonneg_left hββ₀ hk.le)

end PercLib.Models

/-! ### Non-vacuity (D-5) -/
section Witnesses

open PercLib.Models

open Classical in
/-- `L = 2`, `d = 3`, `α = 1`, `c = C = 1` and the kernel `J(u, v) = 2^{-4 j}` when `u, v` first
share a level-`j` block: the kernel satisfies all three hypotheses on `J` of
`exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity`, so the bound applies to it. -/
example : ∃ J : Sym2 (ℕ →₀ (Fin 3 → ZMod 2)) → ℝ≥0,
    (∀ x u v, J s(u + x, v + x) = J s(u, v)) ∧
    (∀ u v, u ≠ v → (1 : ℝ) * ((2 : ℕ) : ℝ) ^ (-((((3 : ℕ) : ℝ) + 1) *
      (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v)) ∧
    (∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤ (1 : ℝ) * ((2 : ℕ) : ℝ) ^ (-((((3 : ℕ) : ℝ) + 1) *
      (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) ∧
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ,
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin 3 → ZMod 2) |
            z.support.sup Nat.succ ≤ n}.sym2 then
              intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0) ≤
        ENNReal.ofReal (C' * ((2 : ℕ) : ℝ) ^ ((1 : ℝ) * n)) := by
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
  obtain ⟨C', hC', h⟩ := exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity
    (d := 3) (L := 2) le_rfl one_pos one_pos one_pos (by norm_num)
  exact ⟨J, hJt, fun u v _ => (hval u v).ge, fun u v _ => (hval u v).le, C', hC',
    h J hJt (fun u v _ => (hval u v).ge) (fun u v _ => (hval u v).le)⟩

end Witnesses
