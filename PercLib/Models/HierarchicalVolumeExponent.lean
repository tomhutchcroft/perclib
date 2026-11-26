/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's boundary-flux criterion at the root critical intensity,
finite-window hyperscaling and power-law kernel tails, and pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied and no definition is added.
Mathematical reference: T. Hutchcroft, *The critical two-point function for long-range
percolation on the hierarchical lattice*, arXiv:2103.17013v1, Corollary 1.5.
-/
module

public import PercLib.Models.HierarchicalTwoPointConditional
public import PercLib.Percolation.Bond.Transport

/-!
# A constraint on the hierarchical volume-tail exponent

On `V = ℕ →₀ (Fin d → ZMod L)` write `h z = z.support.sup Nat.succ` and `Λ_m = {h ≤ m}`. Let
`J` be translation invariant with `c L^{-(d+α)h(v-u)} ≤ J(u, v) ≤ C₀ L^{-(d+α)h(v-u)}` off the
diagonal, `0 < α < d`, and let `β_c = rootCriticalIntensity J 0`.

The boundary flux at `β_c` bounds the block mean `E_{β_c} |K_0^{Λ_m}|` below by a multiple of
`L^{αm}`. If the critical tail satisfies `P(|K_0| ≥ n) ≤ A n^{-θ}`, finite-window hyperscaling
bounds the same mean above by a multiple of `L^{dm(1-θ)/(1+θ)}`; so `d(1-θ)/(1+θ) ≥ α`, that is
`θ ≤ (d-α)/(d+α)`. Applied to every `θ < 1/δ` this gives `δ ≥ (d+α)/(d-α)`.

## Main results

* `law_encard_cluster_eq_of_translationInvariant`: cluster-volume events have the same
  probability at every root.
* `le_of_law_le_encard_cluster_le_rpow`: a critical tail bound `P(|K_0| ≥ n) ≤ A n^{-θ}` with
  `0 ≤ θ < 1` forces `θ ≤ (d-α)/(d+α)`.
* `div_le_of_law_le_encard_cluster_eq_rpow`: a logarithmic tail exponent
  `P(|K_0| ≥ n) = n^{-1/δ + o(1)}` at `β_c` satisfies `δ ≥ (d+α)/(d-α)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

/-- **Root independence of cluster-volume events.** For a translation-invariant kernel,
`P_β(P(|K_u|)) = P_β(P(|K_0|))` for every predicate `P` on volumes and every root `u`. -/
theorem law_encard_cluster_eq_of_translationInvariant
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (β : ℝ≥0) (P : ℕ∞ → Prop) (u : ℕ →₀ (Fin d → ZMod L)) :
    law (intensityProfile J β) {ω | P (cluster ω u).encard} =
      law (intensityProfile J β) {ω | P (cluster ω 0).encard} := by
  have h := law_map_image_of_invariant (q := intensityProfile J β) (Equiv.addRight u)
    (fun e => by
      simp only [intensityProfile, map_addRight_eq_of_translationInvariant J hJt u e])
  conv_lhs => rw [← h]
  rw [map_image_sym2Map_apply]
  congr 1
  ext ω
  have h0 : (Equiv.addRight u) 0 = u := by simp
  have := encard_cluster_image (Equiv.addRight u) ω 0
  rw [h0] at this
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [this]

open Classical in
/-- **Tail exponents at the critical intensity are at most `(d-α)/(d+α)`** (Hutchcroft,
arXiv:2103.17013v1, Cor. 1.5, probability part). For `L ≥ 2`, `c > 0`, `0 < α < d`, a
translation-invariant `J` with `c L^{-(d+α)h(v-u)} ≤ J(u, v) ≤ C₀ L^{-(d+α)h(v-u)}` off the
diagonal, if `P_{β_c}(|K_0| ≥ n) ≤ A n^{-θ}` for every `n ≥ 1` with `A ≥ 0`, `0 ≤ θ < 1`, then
`θ ≤ (d-α)/(d+α)`. -/
theorem le_of_law_le_encard_cluster_le_rpow [NeZero L] (hL : 2 ≤ L) {α c C₀ A θ : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (htail : ∀ n : ℕ, 1 ≤ n →
      law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
          {ω | (n : ℕ∞) ≤ (cluster ω 0).encard} ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-θ))) :
    θ ≤ ((d : ℝ) - α) / (d + α) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  obtain ⟨ℓ, -, hexp, hℓ⟩ := exists_amplification_scale hL hα hαd
  have hJs := summable_of_powerLaw hL hα J hJu
  have hfin : rootCriticalIntensity J 0 < ⊤ :=
    (rootCriticalIntensity_hierarchical_le hL hc hα J hJt hJ hJs hexp hℓ).trans_lt
      ENNReal.ofReal_lt_top
  set b : ℝ≥0 := (rootCriticalIntensity J 0).toNNReal with hb_def
  have hb' : (b : ℝ≥0∞) = rootCriticalIntensity J 0 := ENNReal.coe_toNNReal hfin.ne
  set q := intensityProfile J b with hq
  have hT : ∀ x y : ℕ →₀ (Fin d → ZMod L),
      ∃ σ : (ℕ →₀ (Fin d → ZMod L)) ≃ (ℕ →₀ (Fin d → ZMod L)),
        σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := fun x y =>
    ⟨Equiv.addRight (y - x), by simp, map_addRight_eq_of_translationInvariant J hJt _⟩
  have hrow : ∀ u, rowSum (fun e => (J e : ℝ≥0∞)) u < ⊤ := fun u =>
    (rowSum_le_of_powerLaw hL hα J hJu u).trans_lt ENNReal.ofReal_lt_top
  -- the window tails
  have hwin : ∀ (m : ℕ) (u : ℕ →₀ (Fin d → ZMod L)) (n : ℕ), 1 ≤ n →
      law q {ω | n ≤ clusterIntersection (finite_level_ball m).toFinset ω u} ≤
        ENNReal.ofReal (A * (n : ℝ) ^ (-θ)) := by
    intro m u n hn
    refine le_trans (measure_mono fun ω hω => ?_)
      ((law_encard_cluster_eq_of_translationInvariant J hJt b (fun k => (n : ℕ∞) ≤ k) u).le.trans
        (htail n hn))
    simp only [Set.mem_ofPred_eq, clusterIntersection] at hω ⊢
    have hfi : (cluster ω u ∩ ((finite_level_ball (A := Fin d → ZMod L) m).toFinset :
        Set (ℕ →₀ (Fin d → ZMod L)))).Finite :=
      Set.Finite.inter_of_right (Finset.finite_toSet _) _
    calc (n : ℕ∞) ≤ ((cluster ω u ∩ ((finite_level_ball (A := Fin d → ZMod L) m).toFinset :
          Set _)).ncard : ℕ∞) := by exact_mod_cast hω
      _ = (cluster ω u ∩ ((finite_level_ball (A := Fin d → ZMod L) m).toFinset :
          Set _)).encard := hfi.cast_ncard_eq
      _ ≤ (cluster ω u).encard := Set.encard_le_encard Set.inter_subset_left
  -- constants
  set H : ℝ := ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9)) *
    (4 * Real.exp 1 * ((1 - θ)⁻¹ + 9 * Real.exp (8 / 9))) ^ ((1 - θ) / (1 + θ)) *
      A ^ (2 / (1 + θ)) with hH
  set D : ℝ := C₀ * (1 - (L : ℝ) ^ (-(d : ℝ))) / ((L : ℝ) ^ α - 1) with hD
  set t : ℝ := (1 - θ)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 (by linarith)
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  set e : ℝ := (1 - θ) / (1 + θ) with he
  -- the key inequality at every scale
  have hkey : ∀ m : ℕ, 1 ≤ (b : ℝ) * D * H * ((L : ℝ) ^ ((d : ℝ) * e - α)) ^ m := by
    intro m
    set S := (finite_level_ball (A := Fin d → ZMod L) m).toFinset with hS
    have hSc : (S : Set (ℕ →₀ (Fin d → ZMod L))) =
        {z | z.support.sup Nat.succ ≤ m} := Set.Finite.coe_toFinset _
    have h0S : (0 : ℕ →₀ (Fin d → ZMod L)) ∈ S := by simp [hS]
    have hfl := one_le_boundaryFlux_at_rootCriticalIntensity J hT hrow hfin S h0S
    have hflux : 1 ≤ (b : ℝ≥0∞) * ∑ u ∈ S,
        law q (localConn {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ m} 0 u) *
          ∑' v, if m < v.support.sup Nat.succ then (J s(u, v) : ℝ≥0∞) else 0 := by
      refine (hfl.1.trans hfl.2).trans (le_of_eq ?_)
      rw [hb', hSc]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      congr 1
      refine tsum_congr fun v => ?_
      by_cases hv : m < v.support.sup Nat.succ
      · have : v ∉ S := fun h => absurd ((Set.Finite.mem_toFinset _).1 h) (not_le.2 hv)
        simp [this, hv]
      · have : v ∈ S := (Set.Finite.mem_toFinset _).2 (not_lt.1 hv)
        simp [this, hv]
    have h1 := one_le_mul_restricted_mean_of_boundaryFlux hL hα J hJu b m hflux
    have hmean : ∫⁻ ω, (clusterIntersection S ω 0 : ℝ≥0∞)
        ∂law (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ m}.sym2 then q e else 0) ≤ ∑ v ∈ S, tau q 0 v := by
      rw [← tsum_law_localConn_level_ball_eq_lintegral, tsum_eq_sum (s := S) (fun z hz => by
        rw [localConn_of_notMem_right (by simpa [hS] using hz), measure_empty])]
      exact Finset.sum_le_sum fun v _ => law_localConn_le_tau _ _ 0 v
    have hhyp := sum_tau_le_of_window_tail q ⟨0, h0S⟩ hA hθ0 hθ1 (hwin m) 0
    rw [card_toFinset_level_ball] at hhyp
    have h2 := h1.trans (mul_le_mul' le_rfl (hmean.trans hhyp))
    rw [← ENNReal.ofReal_coe_nnreal, mul_assoc, ← ENNReal.ofReal_mul' (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal] at h2
    refine h2.trans (le_of_eq ?_)
    have hpow : (L : ℝ) ^ (-(α * m)) * (((L ^ d) ^ m : ℕ) : ℝ) ^ e =
        ((L : ℝ) ^ ((d : ℝ) * e - α)) ^ m := by
      rw [← Real.rpow_natCast ((L : ℝ) ^ ((d : ℝ) * e - α)), ← Real.rpow_mul hL0.le,
        show (((L ^ d) ^ m : ℕ) : ℝ) = (L : ℝ) ^ ((d : ℝ) * m) by
          rw [Real.rpow_mul hL0.le]; push_cast; rw [Real.rpow_natCast, Real.rpow_natCast],
        ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      congr 1
      ring
    rw [← hpow, hD, hH, he]
    ring
  -- contradiction as `m → ∞` unless `d e ≥ α`
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hde : (d : ℝ) * e - α < 0 := by
    have h1θ : 0 < 1 + θ := by linarith
    have hdα : 0 < (d : ℝ) + α := by linarith
    rw [he, mul_div_assoc', sub_neg, div_lt_iff₀ h1θ]
    rw [div_lt_iff₀ hdα] at hlt
    nlinarith
  have hr0 : 0 ≤ (L : ℝ) ^ ((d : ℝ) * e - α) := (Real.rpow_pos_of_pos hL0 _).le
  have hr1 : (L : ℝ) ^ ((d : ℝ) * e - α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 hde
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul ((b : ℝ) * D * H)
  rw [mul_zero] at hlim
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  exact absurd (hkey m) (not_le.2 hm)

open Classical in
/-- **Volume-tail exponent obstruction** (Hutchcroft, arXiv:2103.17013v1, Cor. 1.5). In the
setting of `le_of_law_le_encard_cluster_le_rpow`, if the critical tail has a finite positive
logarithmic exponent `δ`, `P_{β_c}(|K_0| ≥ n) = n^{-1/δ + ε(n)}` for `n ≥ 1` with `ε(n) → 0`,
then `δ ≥ (d+α)/(d-α)`. -/
theorem div_le_of_law_le_encard_cluster_eq_rpow [NeZero L] (hL : 2 ≤ L) {α c C₀ δ : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hαd : α < d) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJu : ∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
      C₀ * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))))
    (hδ : 0 < δ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (htail : ∀ n : ℕ, 1 ≤ n →
      law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
          {ω | (n : ℕ∞) ≤ (cluster ω 0).encard} = ENNReal.ofReal ((n : ℝ) ^ (-1 / δ + ε n))) :
    ((d : ℝ) + α) / (d - α) ≤ δ := by
  have hdα : 0 < (d : ℝ) - α := by linarith
  have hdα' : 0 < (d : ℝ) + α := by linarith
  by_contra hlt
  replace hlt := not_le.1 hlt
  set θ₀ : ℝ := ((d : ℝ) - α) / (d + α) with hθ₀
  have hθ₀0 : 0 < θ₀ := div_pos hdα hdα'
  have hθ₀1 : θ₀ < 1 := by rw [hθ₀, div_lt_one hdα']; linarith
  have hθ₀δ : θ₀ < 1 / δ := by
    rw [hθ₀, lt_div_iff₀ hδ, div_mul_eq_mul_div, div_lt_one hdα']
    rw [lt_div_iff₀ hdα] at hlt
    linarith
  set θ : ℝ := (θ₀ + min (1 / δ) 1) / 2 with hθ
  have hθa : θ₀ < θ := by
    have := lt_min hθ₀δ hθ₀1
    rw [hθ]; linarith
  have hθb : θ < 1 / δ := by
    have := min_le_left (1 / δ) 1
    have := lt_min hθ₀δ hθ₀1
    rw [hθ]; linarith
  have hθc : θ < 1 := by
    have := min_le_right (1 / δ) 1
    have := lt_min hθ₀δ hθ₀1
    rw [hθ]; linarith
  -- eventually the exponent is at most `-θ`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hε.eventually (gt_mem_nhds (sub_pos.2 hθb)))
  set N' : ℕ := max N 1 with hN'
  have hN'1 : (1 : ℝ) ≤ N' := by exact_mod_cast le_max_right N 1
  have hθ0 : 0 ≤ θ := hθ₀0.le.trans hθa.le
  have hA1 : 1 ≤ (N' : ℝ) ^ θ := Real.one_le_rpow hN'1 hθ0
  have htail' : ∀ n : ℕ, 1 ≤ n →
      law (intensityProfile J (rootCriticalIntensity J 0).toNNReal)
          {ω | (n : ℕ∞) ≤ (cluster ω 0).encard} ≤
        ENNReal.ofReal ((N' : ℝ) ^ θ * (n : ℝ) ^ (-θ)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    by_cases hnN : N' ≤ n
    · rw [htail n hn]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (n : ℝ) ^ (-1 / δ + ε n) ≤ (n : ℝ) ^ (-θ) := by
            refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
            have := hN n (le_trans (le_max_left N 1) hnN)
            rw [neg_div]
            linarith
        _ ≤ (N' : ℝ) ^ θ * (n : ℝ) ^ (-θ) :=
            le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) hA1
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hn0 _)]
      exact Real.rpow_le_rpow hn0.le (by exact_mod_cast (not_le.1 hnN).le) hθ0
  have := le_of_law_le_encard_cluster_le_rpow hL hc hα hαd J hJt hJ hJu
    (by positivity : (0 : ℝ) ≤ (N' : ℝ) ^ θ) hθ0 hθc htail'
  linarith

end PercLib.Models
