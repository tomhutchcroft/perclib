/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's averaged critical two-point theorem, ball-sum identities and
finite-volume susceptibility identity, and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied and no definition is added.
Mathematical reference: T. Hutchcroft, *The critical two-point function for long-range
percolation on the hierarchical lattice*, arXiv:2103.17013v1, Theorem 1.1.
-/
module

public import PercLib.Models.HierarchicalTwoPointAveraged
public import PercLib.Models.HierarchicalBallSums
public import PercLib.Percolation.Bond.BoundaryContraction

/-!
# Critical susceptibility in a hierarchical ball

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ` and `Λ_n = {h ≤ n}`, a ball
with `L ^ (d n)` points. Under the hypotheses of the averaged critical two-point theorem
(`hierarchicalTwoPointAveraged`), at the critical intensity `β_c` both the expected mass
`E|K_0 ∩ Λ_n|` of the full cluster in the ball and the expected size `E|K_0^{Λ_n}|` of the
cluster formed by open paths inside `Λ_n` are of order `L^{αn}`, uniformly in `n ≥ 0`, with
constants depending only on `d, L, α, c, C`.

## Main results

* `tsum_law_localConn_le_tsum_tau`: `∑_v P(x ↔ v inside S) ≤ ∑_{v ∈ S} τ(x, v)`.
* `ennreal_pow_mul_ofReal_rpow_neg`: `L^{dn} · a L^{-(d-α)n} = a L^{αn}` in `ℝ≥0∞`.
* `hierarchicalBallSusceptibility_bounds`: the two volumes and their comparison in one chain.
* `hierarchicalBallSusceptibility_cluster_inter`: `E|K_0 ∩ Λ_n| ≍ L^{αn}`.
* `hierarchicalBallSusceptibility_localCluster`: `E|K_0^{Λ_n}| ≍ L^{αn}`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-- **Restricted connections are bounded by connections in the set.** For every profile, the
expected number of `v` joined to `x` inside `S` is at most `∑_{v ∈ S} τ(x, v)`. -/
theorem tsum_law_localConn_le_tsum_tau {V : Type*} (q : Sym2 V → unitInterval) (S : Set V)
    [DecidablePred (· ∈ S)] (x : V) :
    ∑' v, law q (localConn S x v) ≤ ∑' v, if v ∈ S then tau q x v else 0 := by
  refine ENNReal.tsum_le_tsum fun v => ?_
  split_ifs with hv
  · exact measure_mono (localConn_subset_conn S x v)
  · rw [localConn_of_notMem_right hv, measure_empty]

end PercLib.Percolation.Bond

namespace PercLib.Models

/-- `L^{dn} · ofReal (a L^{-(d-α)n}) = ofReal (a L^{αn})` for `0 < L`. -/
theorem ennreal_pow_mul_ofReal_rpow_neg {L : ℕ} (hL : 0 < L) (d n : ℕ) (a α : ℝ) :
    (L : ℝ≥0∞) ^ (d * n) * ENNReal.ofReal (a * (L : ℝ) ^ (-((d : ℝ) - α) * n)) =
      ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hL']
  congr 2
  push_cast
  ring

open Classical in
/-- **Critical ball volumes on the hierarchical lattice.** Under the hypotheses of
`hierarchicalTwoPointAveraged` there are `a, A > 0`, depending only on `d, L, α, c, C`, such that
for every such kernel `β_c < ∞` and, for every `n ≥ 0`,
`a L^{αn} ≤ E_{β_c}|K_0^{Λ_n}| ≤ E_{β_c}|K_0 ∩ Λ_n| ≤ A L^{αn}`, where `K_0^{Λ_n}` is the
cluster of `0` formed by open paths inside `Λ_n`. -/
theorem hierarchicalBallSusceptibility_bounds (d L : ℕ) (α c C : ℝ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    (hα : 0 < α) (hαd : α < d) (hc : 0 < c) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
        (∀ x u v, J s(u + x, v + x) = J s(u, v)) →
        (∀ u v, u ≠ v →
          c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
            (J s(u, v) : ℝ)) →
        (∀ u v, u ≠ v →
          (J s(u, v) : ℝ) ≤
            C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
        let q := intensityProfile J (rootCriticalIntensity J 0).toNNReal
        rootCriticalIntensity J 0 < ⊤ ∧
        ∀ n : ℕ,
          ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) ≤
              ∫⁻ ω, ((localCluster ω
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0).encard : ℝ≥0∞)
                ∂law q ∧
            ∫⁻ ω, ((localCluster ω
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0).encard : ℝ≥0∞)
                ∂law q ≤
              ∫⁻ ω, ((cluster ω 0 ∩
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
                ∂law q ∧
            ∫⁻ ω, ((cluster ω 0 ∩
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
                ∂law q ≤
              ENNReal.ofReal (A * (L : ℝ) ^ (α * n)) := by
  have : NeZero L := ⟨by omega⟩
  have hL0 : 0 < L := by omega
  obtain ⟨a, A, ha, hA, hJ98⟩ := hierarchicalTwoPointAveraged d L α c C hd hL hα hαd hc
  refine ⟨min a 1, max A 1, lt_min ha one_pos, lt_max_of_lt_right one_pos,
    fun J hTI hlow hup => ?_⟩
  intro q
  obtain ⟨hβ, hbd⟩ := hJ98 J hTI hlow hup
  refine ⟨hβ, fun n => ?_⟩
  have hK : ∫⁻ ω, ((cluster ω 0 ∩
      {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).encard : ℝ≥0∞) ∂law q =
      ∑' x : ℕ →₀ (Fin d → ZMod L),
        (if x.support.sup Nat.succ ≤ n then tau q 0 x else 0) := by
    simpa using lintegral_encard_cluster_inter_ball q 0 n
  rw [hK, lintegral_encard_induce]
  refine ⟨?_, tsum_law_localConn_le_tsum_tau q _ 0, ?_⟩
  · rcases n.eq_zero_or_pos with rfl | hn
    · calc ENNReal.ofReal (min a 1 * (L : ℝ) ^ (α * ((0 : ℕ) : ℝ)))
            ≤ 1 := by simp
        _ = law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ 0} 0 0) := by
            rw [localConn_self (by simp), measure_univ]
        _ ≤ _ := ENNReal.le_tsum (f := fun v => law q (localConn
            {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ 0} 0 v)) 0
    · obtain ⟨h1, -, -⟩ := hbd n hn
      have hne0 : (L : ℝ≥0∞) ^ (d * n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL0.ne')
      have hnet : (L : ℝ≥0∞) ^ (d * n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top L)
      refine le_trans ?_ (ENNReal.tsum_le_tsum (f := fun x : ℕ →₀ (Fin d → ZMod L) =>
        if x.support.sup Nat.succ = n then
          law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x)
        else 0) fun x => by split_ifs <;> simp)
      calc ENNReal.ofReal (min a 1 * (L : ℝ) ^ (α * n))
            ≤ ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (min_le_left a 1) (by positivity))
        _ = (L : ℝ≥0∞) ^ (d * n) * ENNReal.ofReal (a * (L : ℝ) ^ (-((d : ℝ) - α) * n)) :=
            (ennreal_pow_mul_ofReal_rpow_neg hL0 d n a α).symm
        _ ≤ (L : ℝ≥0∞) ^ (d * n) * (((L : ℝ≥0∞) ^ (d * n))⁻¹ *
              ∑' x : ℕ →₀ (Fin d → ZMod L), if x.support.sup Nat.succ = n then
                law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0 x)
              else 0) := by gcongr; exact h1
        _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hnet, one_mul]
  · rcases n.eq_zero_or_pos with rfl | hn
    · rw [tsum_eq_single 0 fun x hx =>
        ite_eq_right_iff.2 fun h => absurd ((level_eq_zero_iff x).1 (Nat.le_zero.1 h)) hx]
      simp [tau_self]
    · obtain ⟨-, -, h3⟩ := hbd n hn
      have hne0 : (L : ℝ≥0∞) ^ (d * n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL0.ne')
      have hnet : (L : ℝ≥0∞) ^ (d * n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top L)
      calc _ = (L : ℝ≥0∞) ^ (d * n) * (((L : ℝ≥0∞) ^ (d * n))⁻¹ *
              ∑' x : ℕ →₀ (Fin d → ZMod L),
                (if x.support.sup Nat.succ ≤ n then tau q 0 x else 0)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hnet, one_mul]
        _ ≤ (L : ℝ≥0∞) ^ (d * n) * ENNReal.ofReal (A * (L : ℝ) ^ (-((d : ℝ) - α) * n)) :=
            by gcongr
        _ = ENNReal.ofReal (A * (L : ℝ) ^ (α * n)) := ennreal_pow_mul_ofReal_rpow_neg hL0 d n A α
        _ ≤ ENNReal.ofReal (max A 1 * (L : ℝ) ^ (α * n)) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity))

/-- **Full-cluster susceptibility in a hierarchical ball.** Under the hypotheses of the averaged
critical two-point theorem there are `a, A > 0`, depending only on `d, L, α, c, C`, such that for
every such kernel `β_c < ∞` and `a L^{αn} ≤ E_{β_c}|K_0 ∩ Λ_n| ≤ A L^{αn}` for every `n ≥ 0`. -/
@[tag "V4QQ"]
theorem hierarchicalBallSusceptibility_cluster_inter (d L : ℕ) (α c C : ℝ) (hd : 1 ≤ d)
    (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
        (∀ x u v, J s(u + x, v + x) = J s(u, v)) →
        (∀ u v, u ≠ v →
          c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
            (J s(u, v) : ℝ)) →
        (∀ u v, u ≠ v →
          (J s(u, v) : ℝ) ≤
            C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
        let q := intensityProfile J (rootCriticalIntensity J 0).toNNReal
        rootCriticalIntensity J 0 < ⊤ ∧
        ∀ n : ℕ,
          ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) ≤
              ∫⁻ ω, ((cluster ω 0 ∩
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
                ∂law q ∧
            ∫⁻ ω, ((cluster ω 0 ∩
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n}).encard : ℝ≥0∞)
                ∂law q ≤
              ENNReal.ofReal (A * (L : ℝ) ^ (α * n)) := by
  obtain ⟨a, A, ha, hA, h⟩ := hierarchicalBallSusceptibility_bounds d L α c C hd hL hα hαd hc
  refine ⟨a, A, ha, hA, fun J hTI hlow hup => ?_⟩
  obtain ⟨hβ, hn⟩ := h J hTI hlow hup
  exact ⟨hβ, fun n => ⟨(hn n).1.trans (hn n).2.1, (hn n).2.2⟩⟩

/-- **Restricted-cluster susceptibility in a hierarchical ball.** Under the hypotheses of the
averaged critical two-point theorem there are `a, A > 0`, depending only on `d, L, α, c, C`, such
that for every such kernel `β_c < ∞` and `a L^{αn} ≤ E_{β_c}|K_0^{Λ_n}| ≤ A L^{αn}` for every
`n ≥ 0`, where `K_0^{Λ_n}` is the cluster of `0` formed by open paths inside `Λ_n`. -/
@[tag "YWTU"]
theorem hierarchicalBallSusceptibility_localCluster (d L : ℕ) (α c C : ℝ) (hd : 1 ≤ d)
    (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
      ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
        (∀ x u v, J s(u + x, v + x) = J s(u, v)) →
        (∀ u v, u ≠ v →
          c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤
            (J s(u, v) : ℝ)) →
        (∀ u v, u ≠ v →
          (J s(u, v) : ℝ) ≤
            C * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ)))) →
        let q := intensityProfile J (rootCriticalIntensity J 0).toNNReal
        rootCriticalIntensity J 0 < ⊤ ∧
        ∀ n : ℕ,
          ENNReal.ofReal (a * (L : ℝ) ^ (α * n)) ≤
              ∫⁻ ω, ((localCluster ω
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0).encard : ℝ≥0∞)
                ∂law q ∧
            ∫⁻ ω, ((localCluster ω
                {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} 0).encard : ℝ≥0∞)
                ∂law q ≤
              ENNReal.ofReal (A * (L : ℝ) ^ (α * n)) := by
  obtain ⟨a, A, ha, hA, h⟩ := hierarchicalBallSusceptibility_bounds d L α c C hd hL hα hαd hc
  refine ⟨a, A, ha, hA, fun J hTI hlow hup => ?_⟩
  obtain ⟨hβ, hn⟩ := h J hTI hlow hup
  exact ⟨hβ, fun n => ⟨(hn n).1, (hn n).2.1.trans (hn n).2.2⟩⟩

end PercLib.Models
