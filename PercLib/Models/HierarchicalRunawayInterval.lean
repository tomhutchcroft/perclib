/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs from this library's runaway and block-restricted quantile theorems, and pinned
mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream code is copied and no definition
is added. Mathematical reference: T. Hutchcroft, *The critical two-point function for long-range
percolation on the hierarchical lattice*, arXiv:2103.17013v1, Proposition 2.2 (in the squared
form its proof gives).
-/
module

public import PercLib.Models.HierarchicalRunaway
public import PercLib.Percolation.Bond.Tightness.RestrictQuantile
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Models.HierarchicalPowerKernel

/-!
# The runaway bound up to the end of an interval of finite susceptibility

On `V = ℕ →₀ (Fin d → ZMod L)` let `R_n(β)` be the quantile `tightnessScale` of the origin's
level-`n` block under the profile at intensity `β` restricted to that block, and let
`A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})` be the constant of the amplification step. The runaway
bound `sq_tightnessScale_lt_of_chi_lt_top` gives `R_n(β)² < (A/β) L^{(d+α)n}` whenever
`χ(β) < ∞`. Here it is carried to the right end `b` of an interval `(a, b)` on which the
susceptibility is finite, and below it: `R_n(β)² ≤ (A/b) L^{(d+α)n}` for every `β ≤ b`.

## Main results

* `tightnessScale_restrict_intensityProfile_mono`: a block-restricted quantile is monotone in
  the intensity.
* `sq_tightnessScale_le_of_chi_lt_top_on_Ioo`: the bound up to and at the endpoint.
* `summable_of_rowSum_ne_top`: a finite off-diagonal row sum gives a summable row.
* `rowSum_pos_hierarchical`: the lower bound on the kernel makes every row sum positive.
* `sq_tightnessScale_le_at_rootCriticalIntensity`: `R_n(β_c)² ≤ (A/β_c) L^{(d+α)n}`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-- **The block-restricted intensity quantile is monotone in the intensity.** -/
theorem tightnessScale_restrict_intensityProfile_mono {V : Type*} [Countable V] [DecidableEq V]
    (J : Sym2 V → ℝ≥0) (S : Finset V) [DecidablePred (· ∈ (S : Set V).sym2)] {Λ : Finset V}
    (hΛ : Λ ⊆ S) {β β' : ℝ≥0} (h : β ≤ β') :
    tightnessScale (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J β e else 0) Λ ≤
      tightnessScale (fun e => if e ∈ (S : Set V).sym2 then intensityProfile J β' e else 0) Λ := by
  rw [tightnessScale_restrict_intensityProfile J β S hΛ,
    tightnessScale_restrict_intensityProfile J β' S hΛ]
  exact tightnessScale_mono_finite _ fun e => intensityProfile_mono _ h e

/-- **A finite off-diagonal row sum gives a summable row.** -/
theorem summable_of_rowSum_ne_top {V : Type*} (J : Sym2 V → ℝ≥0) {u : V}
    (h : rowSum (fun e => (J e : ℝ≥0∞)) u ≠ ⊤) : Summable fun v => (J s(u, v) : ℝ) := by
  classical
  rw [rowSum_def] at h
  refine NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 (ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨h, ENNReal.coe_ne_top (r := J s(u, u))⟩) ?_))
  calc ∑' v, (J s(u, v) : ℝ≥0∞)
      ≤ ∑' v, ((if v = u then 0 else (J s(u, v) : ℝ≥0∞)) +
          if v = u then (J s(u, u) : ℝ≥0∞) else 0) :=
        ENNReal.tsum_le_tsum fun v => by split_ifs with hv <;> simp [hv]
    _ = _ := by rw [ENNReal.tsum_add, tsum_ite_eq]

end PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

open Classical in
/-- **The runaway bound up to the end of an interval of finite susceptibility** (Hutchcroft,
arXiv:2103.17013v1, Prop. 2.2, squared form). Under the hypotheses of
`sq_tightnessScale_lt_of_chi_lt_top`, if `a < b` and `χ(β) < ∞` for every `β ∈ (a, b)`, then
for every `n` and every `β ≤ b`, `R_n(β)² ≤ (A/b) L^{(d+α)n}` with
`A = (4/c) L^{(d+α)ℓ} log(2 L^{2dℓ})`. -/
theorem sq_tightnessScale_le_of_chi_lt_top_on_Ioo [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    {a b : ℝ≥0} (hab : a < b)
    (hχ : ∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤)
    (n : ℕ) {β : ℝ≥0} (hβb : β ≤ b) :
    (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
      (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / b *
        (L : ℝ) ^ (((d : ℝ) + α) * n) := by
  set A : ℝ := (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2)
    with hA_def
  set S : Finset (ℕ →₀ (Fin d → ZMod L)) := (finite_level_ball n).toFinset with hS_def
  have hSD : ({z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n} : Set _) = (S : Set _) :=
    (Set.Finite.coe_toFinset _).symm
  set M : ℝ≥0 → ℕ := fun β => tightnessScale (fun e => if e ∈ (S : Set _).sym2 then
    intensityProfile J β e else 0) S with hM_def
  have hMeq : ∀ β : ℝ≥0, tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
      z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
      (finite_level_ball n).toFinset = M β := by
    intro β
    simp only [hM_def]
    congr 1
    funext e
    simp only [hSD]
  have hmono : Monotone M := fun β β' h =>
    tightnessScale_restrict_intensityProfile_mono J S subset_rfl h
  have hb : 0 < b := zero_le.trans_lt hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hend : (b : ℝ) * (M b : ℝ) ^ 2 ≤ A * (L : ℝ) ^ (((d : ℝ) + α) * n) := by
    refine restrict_quantile_sq_bound_at_endpoint J S subset_rfl hb fun a' ha' ha'b => ?_
    obtain ⟨β', hβ'1, hβ'2⟩ := exists_between (max_lt hab ha'b)
    have hβ'0 : (0 : ℝ) < β' := by exact_mod_cast ha'.trans_le ((le_max_right a a').trans hβ'1.le)
    have hs := sq_tightnessScale_lt_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ
      (by exact_mod_cast hβ'0) (hχ β' ((le_max_left a a').trans_lt hβ'1) hβ'2) n
    rw [hMeq, ← hA_def, div_mul_eq_mul_div, lt_div_iff₀ hβ'0] at hs
    have hle : (M a' : ℝ) ≤ M β' :=
      Nat.cast_le.2 (hmono ((le_max_right a a').trans hβ'1.le))
    have ha'le : (a' : ℝ) ≤ β' := by exact_mod_cast (le_max_right a a').trans hβ'1.le
    calc (a' : ℝ) * (M a' : ℝ) ^ 2 ≤ β' * (M β' : ℝ) ^ 2 := by gcongr
      _ ≤ _ := by rw [mul_comm]; exact hs.le
  rw [hMeq, div_mul_eq_mul_div, le_div_iff₀ hb', mul_comm]
  calc (b : ℝ) * (M β : ℝ) ^ 2 ≤ b * (M b : ℝ) ^ 2 := by
        gcongr
        exact hmono hβb
    _ ≤ _ := hend

/-- **Row sums are positive.** If `J(u, v) ≥ c L^{-(d+α) h(v - u)}` off the diagonal with
`c > 0` and the lattice has a second point (`d ≥ 1`, `L ≥ 2`), every off-diagonal row sum is
positive. -/
theorem rowSum_pos_hierarchical (hd : 1 ≤ d) (hL : 2 ≤ L) {α c : ℝ} (hc : 0 < c)
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (u : ℕ →₀ (Fin d → ZMod L)) :
    0 < rowSum (fun e => (J e : ℝ≥0∞)) u := by
  classical
  have : Fact (1 < L) := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := exists_ne u
  have hJv : (0 : ℝ) < J s(u, v) := (mul_pos hc (Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < L by omega)) _)).trans_le (hJ u v hv.symm)
  rw [rowSum_def]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum v)
  simp only [hv, ↓reduceIte]
  exact ENNReal.coe_pos.2 (by exact_mod_cast hJv)

open Classical in
/-- **The runaway bound at the threshold, divided form** (Hutchcroft, arXiv:2103.17013v1,
Prop. 2.2 at `β = β_c`). Under the hypotheses of `sq_tightnessScale_lt_of_chi_lt_top`, with
summable rows and `0 < β_c < ∞`, `R_n(β_c)² ≤ (A/β_c) L^{(d+α)n}` for every `n`. -/
theorem sq_tightnessScale_le_at_rootCriticalIntensity [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    (hJs : ∀ u, Summable fun v => (J s(u, v) : ℝ))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ))
    (hβc : 0 < (rootCriticalIntensity J 0).toNNReal) (n : ℕ) :
    (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
        z.support.sup Nat.succ ≤ n}.sym2 then
          intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0)
        (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
      (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) /
        (rootCriticalIntensity J 0).toNNReal * (L : ℝ) ^ (((d : ℝ) + α) * n) := by
  have hne : rootCriticalIntensity J 0 ≠ ⊤ := fun h => by
    rw [h, ENNReal.toNNReal_top] at hβc
    exact lt_irrefl _ hβc
  refine sq_tightnessScale_le_of_chi_lt_top_on_Ioo hL hc hα J hJt hJ hexp hℓ hβc
    (fun β _ hβ => chi_lt_top_of_lt_rootCriticalIntensity J
      (transitive_of_powerLaw_translationInvariant J hJt) hJs ?_) n le_rfl
  rw [← ENNReal.coe_toNNReal hne]
  exact ENNReal.coe_lt_coe.2 hβ

end PercLib.Models
