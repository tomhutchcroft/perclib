/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's restricted-susceptibility, sibling-block, threshold endpoint,
runaway and translation theorems, and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
No upstream code is copied and no definition is added. Mathematical reference: T. Hutchcroft,
*The critical two-point function for long-range percolation on the hierarchical lattice*,
arXiv:2103.17013v1, Theorem 1.1 (assembly on p. 15).
-/
module

public import PercLib.Models.Hierarchical.Defs
public import PercLib.Models.HierarchicalRestrictedSusc
public import PercLib.Models.HierarchicalTranslation

/-!
# Averaged critical two-point bounds on the hierarchical lattice

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ`, `Λ_n = {h ≤ n}`,
`β_c = rootCriticalIntensity J 0` and `a_n = E_{β_c} |K_0 ∩ Λ_n|` for the cluster of the profile
restricted to the pairs inside `Λ_n`. The two halves of Theorem 1.1 come from bounds on `a_n`:

* lower bound: the sibling-block recursion at `n - 1` and `β_c` gives
  `∑_{h x = n} P(0 ↔ x inside Λ_n) ≥ k β_c L^{-α(n-1)} a_{n-1}²`, and the flux bound
  `a_{n-1} ≥ (L^α - 1)/(β_c C (1 - L^{-d})) L^{α(n-1)}` turns this into a multiple of
  `L^{αn} / β_c`;
* upper bound: `a_m ≤ C' L^{αm}` for every `m` and the first-exit reduction give
  `∑_{h x ≤ n} τ(0,x) ≤ (C' + β_c C C'² L^{-d} (1 - L^{-(d-α)})⁻¹) L^{αn}`.

Both constants are made uniform in `J` through `(L^α - 1)/(C (1 - L^{-d})) ≤ β_c ≤ A/4`, with
`A` the constant of the amplification step, which depends only on `d, L, α, c`.

## Main results

* `tau_restrict_eq_law_localConn`: the two-point function of the profile restricted to the pairs
  inside `D` is the probability of connection inside `D`.
* `tsum_law_localConn_level_ball_eq_lintegral`: `∑' z, P(0 ↔ z inside Λ_n) = a_n`.
* `hierarchicalTwoPointAveraged`: Theorem 1.1, `HierarchicalTwoPointAveraged d L α c C`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- **Connection under a restricted profile.** For `x ∈ D`, the two-point function of the profile
restricted to the pairs inside `D` is the probability that `x` and `y` are joined inside `D`. -/
theorem tau_restrict_eq_law_localConn {V : Type*} [Countable V] (q : Sym2 V → unitInterval)
    (D : Set V) [DecidablePred (· ∈ D.sym2)] {x : V} (hx : x ∈ D) (y : V) :
    tau (fun e => if e ∈ D.sym2 then q e else 0) x y = law q (localConn D x y) := by
  rw [tau, law_restrict_apply q D.sym2 (measurableSet_conn x y)]
  congr 1
  ext ω
  exact mem_cluster_inter_sym2_iff ω hx y

variable {d L : ℕ}

open Classical in
/-- **Block mean as a sum of internal connections.** `∑' z, P_q(0 ↔ z inside Λ_n)` is the
expected size of `K_0 ∩ Λ_n` under `q` restricted to the pairs inside `Λ_n`. -/
theorem tsum_law_localConn_level_ball_eq_lintegral [NeZero L]
    (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval) (n : ℕ) :
    ∑' z, law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 z) =
      ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then q e else 0) := by
  have hS := (finite_level_ball (A := Fin d → ZMod L) n).coe_toFinset
  rw [lintegral_clusterIntersection_restrict_eq_sum q _ hS (by simp), hS]
  refine tsum_eq_sum fun z hz => ?_
  rw [localConn_of_notMem_right (by simpa using hz), measure_empty]

open Classical in
/-- **Theorem 1.1 of arXiv:2103.17013v1 (averaged critical two-point bounds).** For `d ≥ 1`,
`L ≥ 2`, `0 < α < d` and `0 < c` there are `a, A > 0`, depending only on `d, L, α, c, C`,
such that every translation-invariant kernel with
`c L^{-(d+α) h(v-u)} ≤ J(u,v) ≤ C L^{-(d+α) h(v-u)}` off the diagonal has `β_c < ∞` and, for
every `n ≥ 1`,
`a L^{-(d-α)n} ≤ L^{-dn} ∑_{h x = n} P_{β_c}(0 ↔ x inside Λ_n)
  ≤ L^{-dn} ∑_{h x ≤ n} τ_{β_c}(0,x) ≤ A L^{-(d-α)n}`.
If `C < c` no kernel satisfies both bounds, since the lattice has a pair `u ≠ v`. -/
@[tag "J98J"]
theorem hierarchicalTwoPointAveraged (d L : ℕ) (α c C : ℝ) :
    HierarchicalTwoPointAveraged d L α c C := by
  intro hd hL hα hαd hc
  have : NeZero L := ⟨by omega⟩
  have : Fact (1 < L) := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain hCc | hcC := lt_or_ge C c
  · refine ⟨1, 1, one_pos, one_pos, fun J _ hJl hJu => absurd ?_ hCc.not_ge⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : ℕ →₀ (Fin d → ZMod L))
    exact le_of_mul_le_mul_right ((hJl 0 v hv.symm).trans (hJu 0 v hv.symm))
      (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < L by omega)) _)
  have hC : 0 < C := hc.trans_le hcC
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  set Aℓ : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) *
    Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) with hAℓ
  have hAℓ0 : 0 < Aℓ := by
    have hN : (1 : ℝ) ≤ (L : ℝ) ^ (d * ℓ) := one_le_pow₀ hL1.le
    have hlog : 0 < Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) := Real.log_pos (by nlinarith)
    rw [hAℓ]
    positivity
  set k : ℝ := c / 4 * Real.exp (-(c * Aℓ * 99 ^ 2 * (L : ℝ) ^ (-((d : ℝ) + α)))) *
    (L : ℝ) ^ (-((d : ℝ) + α)) with hk
  have hk0 : 0 < k := by rw [hk]; positivity
  have hLa : 0 < (L : ℝ) ^ α - 1 := sub_pos.2 (Real.one_lt_rpow hL1 hα)
  have hdpos : (0 : ℝ) < d := hα.trans hαd
  have hLd : 0 < 1 - (L : ℝ) ^ (-(d : ℝ)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith))
  have hLda : 0 < 1 - (L : ℝ) ^ (-((d : ℝ) - α)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith))
  set b : ℝ := ((L : ℝ) ^ α - 1) / (C * (1 - (L : ℝ) ^ (-(d : ℝ)))) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  obtain ⟨C', hC'0, hC'⟩ :=
    exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity hL hc hC hα hαd
  set Dc : ℝ := Aℓ / 4 * C * C' ^ 2 * (L : ℝ) ^ (-(d : ℝ)) *
    (1 - (L : ℝ) ^ (-((d : ℝ) - α)))⁻¹ with hDc
  have hDc0 : 0 < Dc := by
    rw [hDc]
    have := Real.rpow_pos_of_pos hL0 (-(d : ℝ))
    positivity
  have hρ0 : 0 < (L : ℝ) ^ α := Real.rpow_pos_of_pos hL0 α
  refine ⟨4 * k * b ^ 2 / (Aℓ * (L : ℝ) ^ α), C' + Dc, by positivity, by positivity,
    fun J hJt hJl hJu => ?_⟩
  intro q
  obtain ⟨⟨hpos, htop⟩, hM⟩ :=
    rootCriticalIntensity_mem_Ioo_and_mul_sq_tightnessScale_le hL hc hα hαd J hJt hJl hJu hexp hℓ
  set β := (rootCriticalIntensity J 0).toNNReal with hβ
  have hβ0 : 0 < β := ENNReal.toNNReal_pos hpos.ne' htop.ne
  have hβr : (0 : ℝ) < β := by exact_mod_cast hβ0
  have hβA : (β : ℝ) ≤ Aℓ / 4 := by
    have h := rootCriticalIntensity_hierarchical_le hL hc hα J hJt hJl
      (summable_of_powerLaw hL hα J hJu) hexp hℓ
    rw [hβ, ENNReal.coe_toNNReal_eq_toReal]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hM' : ∀ m : ℕ, (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0)
      (finite_level_ball m).toFinset : ℝ) ^ 2 ≤ Aℓ / β * (L : ℝ) ^ (((d : ℝ) + α) * m) := by
    intro m
    rw [div_mul_eq_mul_div, le_div_iff₀ hβr, mul_comm]
    exact hM m
  have hLpow : ∀ x : ℝ, ((L : ℝ≥0∞) ^ x) = ENNReal.ofReal ((L : ℝ) ^ x) := fun x => by
    rw [← ENNReal.ofReal_rpow_of_pos hL0, ENNReal.ofReal_natCast]
  have hsplit : ∀ j : ℕ, (L : ℝ) ^ (-((d : ℝ) - α) * j) =
      (L : ℝ) ^ (α * j) * ((L : ℝ) ^ (d * j))⁻¹ := fun j => by
    rw [show ((L : ℝ) ^ (d * j)) = (L : ℝ) ^ ((d : ℝ) * j) by
        rw [← Real.rpow_natCast]; push_cast; rfl,
      ← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]
    congr 1
    ring
  have hLnat : ∀ j : ℕ, ((L : ℝ≥0∞) ^ j) = ENNReal.ofReal ((L : ℝ) ^ j) := fun j => by
    rw [ENNReal.ofReal_pow hL0.le, ENNReal.ofReal_natCast]
  refine ⟨htop, fun n hn => ⟨?_, ?_, ?_⟩⟩
  · -- lower bound
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hshell := sum_shell_tau_ge hL hd hα hc J hJt hJl hβ0 m (hM' m)
    have hend := ofReal_le_lintegral_clusterIntersection_at_rootCriticalIntensity hL hα J hJt
      hJu m
    have hend' : ENNReal.ofReal (b / β * (L : ℝ) ^ (α * m)) ≤
        ∫⁻ ω, (clusterIntersection (finite_level_ball m).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
            z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0) := by
      refine le_of_eq_of_le ?_ hend
      congr 2
      rw [hb, hβ, ENNReal.coe_toNNReal_eq_toReal]
      field_simp
    set E : ℝ := (L : ℝ) ^ (α * m) with hE
    have hE0 : 0 < E := Real.rpow_pos_of_pos hL0 _
    set P : ℝ := (L : ℝ) ^ (d * (m + 1)) with hP
    have hP0 : 0 < P := pow_pos hL0 _
    calc ENNReal.ofReal (4 * k * b ^ 2 / (Aℓ * (L : ℝ) ^ α) *
          (L : ℝ) ^ (-((d : ℝ) - α) * ((m + 1 : ℕ) : ℝ)))
        ≤ ((L : ℝ≥0∞) ^ (d * (m + 1)))⁻¹ *
            ENNReal.ofReal (k * β * (L : ℝ) ^ (-(α * m)) * (b / β * E) ^ 2) := by
          rw [hLnat, ← ENNReal.ofReal_inv_of_pos hP0, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hsplit, Real.rpow_neg hL0.le,
            show α * ((m + 1 : ℕ) : ℝ) = α * m + α by push_cast; ring,
            Real.rpow_add hL0, ← hE, ← hP]
          have h4 : 4 / Aℓ ≤ 1 / (β : ℝ) := by
            rw [div_le_div_iff₀ hAℓ0 hβr]
            linarith
          calc 4 * k * b ^ 2 / (Aℓ * (L : ℝ) ^ α) * (E * (L : ℝ) ^ α * P⁻¹)
              = k * b ^ 2 * E * P⁻¹ * (4 / Aℓ) := by field_simp
            _ ≤ k * b ^ 2 * E * P⁻¹ * (1 / β) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
            _ = P⁻¹ * (k * β * E⁻¹ * (b / β * E) ^ 2) := by field_simp
      _ ≤ ((L : ℝ≥0∞) ^ (d * (m + 1)))⁻¹ *
            (ENNReal.ofReal (k * β * (L : ℝ) ^ (-(α * m))) *
              (∫⁻ ω, (clusterIntersection (finite_level_ball m).toFinset ω 0 : ℝ≥0∞)
                ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
                  z.support.sup Nat.succ ≤ m}.sym2 then intensityProfile J β e else 0)) ^ 2) := by
          refine mul_le_mul' le_rfl ?_
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
          exact mul_le_mul' le_rfl (pow_le_pow_left₀ (zero_le) hend' 2)
      _ ≤ ((L : ℝ≥0∞) ^ (d * (m + 1)))⁻¹ *
            ∑ x ∈ (finite_level_ball (m + 1)).toFinset \ (finite_level_ball m).toFinset,
              tau (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
                z.support.sup Nat.succ ≤ m + 1}.sym2 then intensityProfile J β e else 0) 0 x :=
          mul_le_mul' le_rfl hshell
      _ = _ := by
          congr 1
          symm
          rw [tsum_eq_sum (s := (finite_level_ball (m + 1)).toFinset \
            (finite_level_ball m).toFinset)]
          · refine Finset.sum_congr rfl fun x hx => ?_
            have hx' : x.support.sup Nat.succ = m + 1 := by
              simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx
              omega
            rw [ite_eq_left hx', tau_restrict_eq_law_localConn _ _ (by simp)]
            rfl
          · intro x hx
            refine ite_eq_right fun hx' => ?_
            apply hx
            simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
            omega
  · -- the shell sum is at most the ball sum
    refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun x => ?_)
    split_ifs with h1 h2 h2
    · exact measure_mono (localConn_subset_conn _ 0 x)
    · omega
    · exact zero_le
    · exact le_rfl
  · -- upper bound
    have hμ : ∀ m : ℕ, ∑' z, law (intensityProfile J β)
        (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 z) ≤
          ENNReal.ofReal C' * (L : ℝ≥0∞) ^ (α * m) := by
      intro m
      rw [tsum_law_localConn_level_ball_eq_lintegral, hLpow, ← ENNReal.ofReal_mul hC'0.le]
      exact hC' J hJt hJl hJu m
    have hK : ∀ u v, u ≠ v → (J s(u, v) : ℝ≥0∞) ≤
        ENNReal.ofReal C * (L : ℝ≥0∞) ^ (-((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℕ)) := by
      intro u v huv
      rw [← ENNReal.ofReal_coe_nnreal, hLpow, ← ENNReal.ofReal_mul hC.le, neg_mul]
      exact ENNReal.ofReal_le_ofReal (hJu u v huv)
    have hup := tsum_tau_ball_le_of_translationInvariant J hJt (by omega : 1 ≤ L) hα hαd
      (ENNReal.ofReal C) hK β (ENNReal.ofReal C') hμ n
    have hG : (β : ℝ≥0∞) * ENNReal.ofReal C * ENNReal.ofReal C' ^ 2 * (L : ℝ≥0∞) ^ (-(d : ℝ)) *
        (1 - (L : ℝ≥0∞) ^ (-((d : ℝ) - α)))⁻¹ =
        ENNReal.ofReal (β * C * C' ^ 2 * (L : ℝ) ^ (-(d : ℝ)) *
          (1 - (L : ℝ) ^ (-((d : ℝ) - α)))⁻¹) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := β), hLpow, hLpow, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (Real.rpow_nonneg hL0.le _), ← ENNReal.ofReal_inv_of_pos hLda,
        ← ENNReal.ofReal_pow hC'0.le, ← ENNReal.ofReal_mul hβr.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
    rw [hG, hLpow, ← ENNReal.ofReal_mul hC'0.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at hup
    refine (mul_le_mul' le_rfl hup).trans ?_
    rw [hLnat, ← ENNReal.ofReal_inv_of_pos (pow_pos hL0 _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsplit]
    have hD : β * C * C' ^ 2 * (L : ℝ) ^ (-(d : ℝ)) * (1 - (L : ℝ) ^ (-((d : ℝ) - α)))⁻¹ ≤ Dc := by
      rw [hDc]
      have := Real.rpow_pos_of_pos hL0 (-(d : ℝ))
      gcongr
    have hE0 : 0 < (L : ℝ) ^ (α * n) := Real.rpow_pos_of_pos hL0 _
    have hP0 : 0 < (L : ℝ) ^ (d * n) := pow_pos hL0 _
    calc ((L : ℝ) ^ (d * n))⁻¹ * (C' * (L : ℝ) ^ (α * n) +
          β * C * C' ^ 2 * (L : ℝ) ^ (-(d : ℝ)) * (1 - (L : ℝ) ^ (-((d : ℝ) - α)))⁻¹ *
            (L : ℝ) ^ (α * n))
        = (C' + β * C * C' ^ 2 * (L : ℝ) ^ (-(d : ℝ)) * (1 - (L : ℝ) ^ (-((d : ℝ) - α)))⁻¹) *
            ((L : ℝ) ^ (α * n) * ((L : ℝ) ^ (d * n))⁻¹) := by ring
      _ ≤ (C' + Dc) * ((L : ℝ) ^ (α * n) * ((L : ℝ) ^ (d * n))⁻¹) := by gcongr

end PercLib.Models
