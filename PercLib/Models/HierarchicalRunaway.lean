/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's hierarchical amplification, truncated-mean and sharpness
theorems, and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is
copied and no definition is added. Mathematical reference: T. Hutchcroft, arXiv:2103.17013v1,
Proposition 2.2 (for `β < β_c`, in the squared form its proof gives) and Corollary 2.3.
-/
module

public import PercLib.Models.HierarchicalPowerKernel
public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Percolation.Bond.ProfileRegularity

/-!
# The runaway argument on the hierarchical lattice

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}`, `q_n` for
`q_β = intensityProfile J β` restricted to the pairs inside `Λ_n`, and `M_n(β)` for the quantile
`tightnessScale q_n Λ_n`, all spelled as in `tightnessScale_hierarchical_amplification`. With
`c, α, ℓ` as there, let `A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`.

## Main results

* `lintegral_clusterIntersection_le_chi`: for profiles `q ≤ q'`, `E_q|K_u ∩ Λ| ≤ χ(q', u)`.
* `ofReal_sq_tightnessScale_div_le_mul_chi`: `M_n² / (4e) ≤ L^{dn} χ(q_β, 0)`.
* `sq_tightnessScale_lt_of_chi_lt_top` (Prop. 2.2 for finite susceptibility): if `β > 0` and
  `χ(q_β, 0) < ∞`, then `M_n(β)² < (A/β) L^{(d+α)n}` for every `n`. Otherwise the
  amplification step, iterated, forces `M_m² ≥ (A/β) L^{(d+α)m}` along `m = n + kℓ`, against
  `M_m² ≤ 4e L^{dm} χ` and `α > 0`.
* `sq_tightnessScale_lt_of_lt_rootCriticalIntensity` (Prop. 2.2 for `β < β_c`): the same
  under `β < β_c(0)`, for kernels with summable rows (sharpness).
* `rootCriticalIntensity_hierarchical_le` (Cor. 2.3): `β_c(0) ≤ A/4`, from `n = 0`, where `M_0 = 2`.
* `rootCriticalIntensity_hierarchical_lt_top`: `β_c(0) < ∞` when `0 < α < d`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- **Restricted intersections are bounded by the susceptibility.** For profiles `q ≤ q'`, a
finite set `Λ` and a root `u`, `E_q |K_u ∩ Λ| ≤ χ(q', u)`. -/
theorem lintegral_clusterIntersection_le_chi {V : Type*} [Countable V]
    {q q' : Sym2 V → unitInterval} (h : q ≤ q') (Λ : Finset V) (u : V) :
    ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ∂(law q) ≤ chi q' u := by
  refine (lintegral_mono fun ω => ?_).trans (chi_mono h u)
  have hfin : (cluster ω u ∩ (Λ : Set V)).Finite := Λ.finite_toSet.subset Set.inter_subset_right
  rw [clusterIntersection, ← ENat.toENNReal_coe, ENat.toENNReal_le, hfin.cast_ncard_eq]
  exact Set.encard_le_encard Set.inter_subset_left

variable {d L : ℕ}

open Classical in
/-- **Ball quantile and susceptibility** ((2.2) of the hierarchical source, with the restricted
cluster bounded by the full one): `M_n² / (4e) ≤ L^{dn} χ(q_β, 0)`. -/
theorem ofReal_sq_tightnessScale_div_le_mul_chi [NeZero L]
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v)) (β : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal ((tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 / (4 * Real.exp 1)) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞) * chi (intensityProfile J β) 0 := by
  refine (le_card_mul_lintegral_clusterIntersection_levelBall J hJt β n).trans
    (mul_le_mul' le_rfl (lintegral_clusterIntersection_le_chi (fun e => ?_) _ 0))
  split_ifs
  · exact le_rfl
  · exact unitInterval.nonneg _

/-- The amplification hypothesis `e^{-L^{dℓ}/(8e)} ≤ 1/4` forces `ℓ ≥ 1`. -/
theorem one_le_of_exp_neg_pow_le {ℓ : ℕ}
    (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4) : 1 ≤ ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | h
  · exfalso
    rw [mul_zero, pow_zero] at hexp
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hx : 1 / (8 * Real.exp 1) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [Real.add_one_le_exp (-(1 / (8 * Real.exp 1)))]
  · exact h

open Classical in
/-- **Prop. 2.2 below the threshold, susceptibility form** (2XJX, strict part; Hutchcroft,
arXiv:2103.17013v1, Prop. 2.2, squared form). Under the hypotheses of
`tightnessScale_hierarchical_amplification`, if `β > 0` and `χ(q_β, 0) < ∞`, then for every `n`,
`M_n(β)² < (A/β) L^{(d+α)n}` with `A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`. -/
theorem sq_tightnessScale_lt_of_chi_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {β : ℝ≥0} (hβ : 0 < β) (hχ : chi (intensityProfile J β) 0 < ⊤) (n : ℕ) :
    (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 <
      (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
        (L : ℝ) ^ (((d : ℝ) + α) * n) := by
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)
    with hA_def
  set M : ℕ → ℕ := fun m => tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0)
      (finite_level_ball m).toFinset with hM_def
  change (M n : ℝ) ^ 2 < A / β * (L : ℝ) ^ (((d : ℝ) + α) * n)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hℓ1 : 1 ≤ ℓ := one_le_of_exp_neg_pow_le hexp
  have hA : 0 < A := by
    have hN : (1 : ℝ) ≤ (L : ℝ) ^ (d * ℓ) := one_le_pow₀ hL1.le
    have hlog : 0 < Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) :=
      Real.log_pos (by nlinarith)
    rw [hA_def]
    positivity
  by_contra hcon
  rw [not_lt] at hcon
  -- iterate the amplification step
  have hiter : ∀ k : ℕ, A / β * (L : ℝ) ^ (((d : ℝ) + α) * ((n + k * ℓ : ℕ) : ℝ)) ≤
      (M (n + k * ℓ) : ℝ) ^ 2 := by
    intro k
    induction k with
    | zero => simpa using hcon
    | succ k ih =>
      have h := tightnessScale_hierarchical_amplification hL hc hα J hJt hJ hexp hℓ hβ
        (n + k * ℓ) ih
      rw [show n + (k + 1) * ℓ = n + k * ℓ + ℓ by ring]
      convert h using 3
      push_cast
      ring
  -- the susceptibility bound
  set X : ℝ := (chi (intensityProfile J β) 0).toReal with hX
  have hup : ∀ m : ℕ, (M m : ℝ) ^ 2 ≤ 4 * Real.exp 1 * ((L : ℝ) ^ d) ^ m * X := by
    intro m
    have h := ofReal_sq_tightnessScale_div_le_mul_chi J hJt β m
    rw [← ENNReal.ofReal_toReal hχ.ne, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg),
      div_le_iff₀ (by positivity)] at h
    push_cast at h
    rw [← hX] at h
    linarith
  -- `L^{α k}` is unbounded
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow hL1 hα)).eventually_gt_atTop (4 * Real.exp 1 * X * β / A)).exists
  have hm := (hiter k).trans (hup (n + k * ℓ))
  set m := n + k * ℓ with hm_def
  have hsplit : (L : ℝ) ^ (((d : ℝ) + α) * (m : ℝ)) =
      ((L : ℝ) ^ d) ^ m * ((L : ℝ) ^ α) ^ m := by
    rw [Real.rpow_mul hL0.le, Real.rpow_add hL0, Real.rpow_natCast, mul_pow, Real.rpow_natCast]
  have hkm : ((L : ℝ) ^ α) ^ k ≤ ((L : ℝ) ^ α) ^ m :=
    pow_le_pow_right₀ (Real.one_le_rpow hL1.le hα.le) (by rw [hm_def]; nlinarith)
  rw [hsplit] at hm
  have hLd : 0 < ((L : ℝ) ^ d) ^ m := by positivity
  have h1 : A / β * ((L : ℝ) ^ α) ^ m ≤ 4 * Real.exp 1 * X := by
    have : ((L : ℝ) ^ d) ^ m * (A / β * ((L : ℝ) ^ α) ^ m) ≤
        ((L : ℝ) ^ d) ^ m * (4 * Real.exp 1 * X) := by nlinarith
    exact le_of_mul_le_mul_left this hLd
  rw [div_lt_iff₀ hA] at hk
  have h2 : A * ((L : ℝ) ^ α) ^ m ≤ 4 * Real.exp 1 * X * β := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hβ0] at h1
    exact h1
  have h3 : A * ((L : ℝ) ^ α) ^ k ≤ A * ((L : ℝ) ^ α) ^ m := mul_le_mul_of_nonneg_left hkm hA.le
  linarith

open Classical in
/-- **Prop. 2.2 below the threshold** (2XJX, strict part; Hutchcroft, arXiv:2103.17013v1,
Prop. 2.2, squared form): for a kernel with summable rows, every `0 < β < β_c(0)` and every `n`,
`M_n(β)² < (A/β) L^{(d+α)n}`. Summable rows follow from a power-law upper bound
(`summable_of_powerLaw`). -/
theorem sq_tightnessScale_lt_of_lt_rootCriticalIntensity [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJs : ∀ u, Summable fun v => (J s(u, v) : ℝ))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {β : ℝ≥0} (hβ : 0 < β) (hβc : (β : ℝ≥0∞) < rootCriticalIntensity J 0) (n : ℕ) :
    (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 <
      (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
        (L : ℝ) ^ (((d : ℝ) + α) * n) :=
  sq_tightnessScale_lt_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ hβ
    (chi_lt_top_of_lt_rootCriticalIntensity J
      (transitive_of_powerLaw_translationInvariant J hJt) hJs hβc) n

/-- **Corollary 2.3** (FF30, upper half; Hutchcroft, arXiv:2103.17013v1, Cor. 2.3): for a kernel
with summable rows, `β_c(0) ≤ A/4` with `A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`. This is
`sq_tightnessScale_lt_of_lt_rootCriticalIntensity` at `n = 0`, where `Λ_0 = {0}` and
`M_0 = 2`. -/
theorem rootCriticalIntensity_hierarchical_le [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJs : ∀ u, Summable fun v => (J s(u, v) : ℝ))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) :
    rootCriticalIntensity J 0 ≤ ENNReal.ofReal
      ((4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / 4) := by
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)
    with hA_def
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hA : 0 < A := by
    have hN : (1 : ℝ) ≤ (L : ℝ) ^ (d * ℓ) := one_le_pow₀ hL1.le
    have hlog : 0 < Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) :=
      Real.log_pos (by nlinarith)
    rw [hA_def]
    positivity
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨β, hβl, hβu⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
  have hβA : A / 4 < β := by
    rwa [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top,
      ENNReal.coe_toReal] at hβl
  have hβ0 : (0 : ℝ) < β := by linarith
  have h := sq_tightnessScale_lt_of_lt_rootCriticalIntensity hL hc hα J hJt hJ hJs hexp hℓ
    (by exact_mod_cast hβ0) hβu 0
  have hball0 : (finite_level_ball (A := Fin d → ZMod L) 0).toFinset = {0} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton, Nat.le_zero,
      level_eq_zero_iff]
  rw [hball0, tightnessScale_singleton, ← hA_def] at h
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h
  rw [lt_div_iff₀ hβ0] at h
  push_cast at h
  linarith

/-- **`β_c < ∞`** (FF30, upper half): for `0 < α < d` and a translation-invariant kernel with
summable rows and `J(u, v) ≥ c L^{-(d+α) h(v - u)}`, the threshold at the origin is finite. -/
theorem rootCriticalIntensity_hierarchical_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJs : ∀ u, Summable fun v => (J s(u, v) : ℝ)) :
    rootCriticalIntensity J 0 < ⊤ := by
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  exact (rootCriticalIntensity_hierarchical_le hL hc hα J hJt hJ hJs hexp hℓ).trans_lt
    ENNReal.ofReal_lt_top

end PercLib.Models

/-! ### Non-vacuity (D-5) -/
section Witnesses

open PercLib.Models

/-- `L = 2`, `d = 3`, `α = 1`, `c = 1` and the kernel `J(u, v) = 2^{-4 j}` when `u, v` first share
a level-`j` block: it is translation invariant, has summable rows, satisfies the lower bound with
equality, and has a finite threshold. -/
example : ∃ J : Sym2 (ℕ →₀ (Fin 3 → ZMod 2)) → ℝ≥0,
    (∀ x u v, J s(u + x, v + x) = J s(u, v)) ∧
    (∀ u v, u ≠ v → (1 : ℝ) * ((2 : ℕ) : ℝ) ^ (-((((3 : ℕ) : ℝ) + 1) *
      (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v)) ∧
    (∀ u, Summable fun v => (J s(u, v) : ℝ)) ∧
    rootCriticalIntensity J 0 < ⊤ := by
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
  have hJl : ∀ u v, u ≠ v → (1 : ℝ) * ((2 : ℕ) : ℝ) ^ (-((((3 : ℕ) : ℝ) + 1) *
      (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v) :=
    fun u v _ => (hval u v).ge
  have hJs := summable_of_powerLaw (d := 3) (L := 2) le_rfl one_pos J fun u v _ => (hval u v).le
  exact ⟨J, hJt, hJl, hJs, rootCriticalIntensity_hierarchical_lt_top le_rfl one_pos one_pos
    (by norm_num) J hJt hJl hJs⟩

end Witnesses
