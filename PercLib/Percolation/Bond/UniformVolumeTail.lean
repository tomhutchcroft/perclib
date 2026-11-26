/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against the pinned mathlib. Mathematical content: summing
the tree-graph moment bounds `E|K_o|^{j+1} ≤ (2j-1)!! χ_o M^{2j}` with the binomial series of
`(1 - z)^{-1/2}` and `1 - (1 - z)^{1/2}`, then Markov's inequality. No upstream proof is copied,
no definition is added and no Input is introduced.
-/
module

public import PercLib.Probability.ExponentialMoments
public import PercLib.Percolation.Bond.TreeGraph.Moments
public import PercLib.Percolation.Bond.RowSum

/-!
# Exponential cluster-volume bounds under uniform susceptibility

For an independent bond model on a countable vertex set with `M = ⨆ x, χ(x) < ∞`, the
tree-graph bound gives the two-parameter moment hypothesis `E X^m ≤ (2m-3)!! a M^{2m-2}`
(`m ≥ 1`) for `X = |K_o|` with `a = χ(o)`; no transitivity is used. The general bounds
under that hypothesis (`PercLib.Probability.lintegral_mul_exp_le_of_moment_le` and its
companions in `PercLib.Probability.ExponentialMoments`) then give the weighted and ordinary
exponential moments and the tails of `|K_o|`, with the prefactor `χ(o)` and the scale `M`
kept apart.

## Main results

* `PercLib.Percolation.Bond.lintegral_mul_exp_encard_cluster_le`,
  `PercLib.Percolation.Bond.lintegral_exp_encard_cluster_le`,
  `PercLib.Percolation.Bond.law_encard_cluster_ge_le_min`,
  `PercLib.Percolation.Bond.law_encard_cluster_ge_le_exp`: exponential moments and tails of
  the cluster volume.
-/

@[expose] public section

open Real Filter MeasureTheory Set
open scoped Nat ENNReal

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*} [Countable V]

omit [Countable V] in
/-- Under `⨆ x, χ(x) < ∞`, the susceptibility at every vertex is finite. -/
theorem chi_ne_top_of_iSup_ne_top (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) : chi q o ≠ ⊤ :=
  ne_top_of_le_ne_top hM (le_iSup (fun x => chi q x) o)

/-- With finite susceptibility at `o`, the real cluster volume `|K_o|` (read through
`ℕ∞.toNat`) agrees almost surely with the extended cluster volume. -/
theorem ae_ofReal_encard_toNat_cluster_eq (q : Sym2 V → unitInterval) (o : V)
    (ho : chi q o ≠ ⊤) :
    ∀ᵐ ω ∂law q, ENNReal.ofReal ((cluster ω o).encard.toNat : ℝ) =
      ((cluster ω o).encard : ℝ≥0∞) := by
  have hmeas : Measurable fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster o)
  filter_upwards [ae_lt_top hmeas ho] with ω hω
  have h : (cluster ω o).encard ≠ ⊤ := (ENat.toENNReal_lt_top.1 hω).ne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
  simp [← hm]

/-- The real cluster volume `|K_o|` (read through `ℕ∞.toNat`) is measurable. -/
theorem measurable_encard_toNat_cluster (o : V) :
    Measurable fun ω : Config V => ((cluster ω o).encard.toNat : ℝ) :=
  (measurable_of_countable (fun n : ℕ∞ => (n.toNat : ℝ))).comp (measurable_encard_cluster o)

/-- **Cluster moments, real form.** With `M = ⨆ x, χ(x) < ∞`, the real cluster volume
satisfies `E|K_o|^m ≤ (2m−3)!! χ(o) M^{2m−2}` for every `m ≥ 1`. -/
theorem lintegral_ofReal_encard_toNat_cluster_pow_le (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) (m : ℕ) (hm : 1 ≤ m) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ m) ∂law q ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * (chi q o).toReal *
        (⨆ x, chi q x).toReal ^ (2 * m - 2)) := by
  have ho := chi_ne_top_of_iSup_ne_top q o hM
  calc ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ m) ∂law q
      ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q := lintegral_mono fun ω => by
        rw [ENNReal.ofReal_pow (Nat.cast_nonneg _)]
        refine pow_le_pow_left₀ zero_le ?_ m
        rcases eq_or_ne (cluster ω o).encard ⊤ with h | h
        · simp [h]
        · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
          simp [← hk]
    _ ≤ _ := lintegral_encard_pow_le_iSup q m hm o
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_toReal ho,
          ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM]

/-- `1 ≤ χ(o) ≤ M` in real form, for `M = ⨆ x, χ(x) < ∞`. -/
theorem one_le_toReal_chi_le_toReal_iSup (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) :
    1 ≤ (chi q o).toReal ∧ (chi q o).toReal ≤ (⨆ x, chi q x).toReal := by
  have ho := chi_ne_top_of_iSup_ne_top q o hM
  refine ⟨?_, ENNReal.toReal_mono hM (le_iSup (fun x => chi q x) o)⟩
  simpa using ENNReal.toReal_mono ho (one_le_chi q o)

/-- On the almost sure event of a finite cluster, `|K_o| ≥ n` in `ℝ≥0∞` and in `ℝ` agree. -/
theorem law_ofReal_le_encard_cluster_le (q : Sym2 V → unitInterval) (o : V)
    (ho : chi q o ≠ ⊤) (n : ℝ) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      law q {ω | n ≤ ((cluster ω o).encard.toNat : ℝ)} := by
  refine measure_mono_ae ((ae_ofReal_encard_toNat_cluster_eq q o ho).mono fun ω h hω => ?_)
  have hω' : ENNReal.ofReal n ≤ ENNReal.ofReal ((cluster ω o).encard.toNat : ℝ) := by
    rw [h]; exact hω
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).1 hω'

/-- **Weighted exponential moment of the cluster volume.** With `M = ⨆ x, χ(x) < ∞` and
`0 ≤ s < (2M²)⁻¹`: `E[|K_o| e^{s|K_o|}] ≤ χ(o) / √(1 − 2sM²)`. -/
theorem lintegral_mul_exp_encard_cluster_le (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s < (2 * (⨆ x, chi q x).toReal ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) *
        exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law q ≤
      ENNReal.ofReal ((chi q o).toReal / sqrt (1 - 2 * s * (⨆ x, chi q x).toReal ^ 2)) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact lintegral_mul_exp_le_of_moment_le (measurable_encard_toNat_cluster o)
    (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
    (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hs hs1

/-- **Ordinary exponential moment of the cluster volume.** With `M = ⨆ x, χ(x) < ∞` and
`0 ≤ s ≤ (2M²)⁻¹` (endpoint included): `E e^{s|K_o|} ≤ 1 + (χ(o)/M²)(1 − √(1 − 2sM²))`. -/
theorem lintegral_exp_encard_cluster_le (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ (2 * (⨆ x, chi q x).toReal ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law q ≤
      ENNReal.ofReal (1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2 *
        (1 - sqrt (1 - 2 * s * (⨆ x, chi q x).toReal ^ 2))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact lintegral_exp_le_of_moment_le (measurable_encard_toNat_cluster o)
    (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
    (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hs hs1

/-- `P(|K_o| ≥ n) ≤ (√2 χ(o)/n) e^{−n/(4M²)}` for real `n > 0`, with `M = ⨆ x, χ(x) < ∞`. -/
theorem law_encard_cluster_ge_le_sqrt_two_mul (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {n : ℝ} (hn : 0 < n) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (sqrt 2 * (chi q o).toReal / n *
        exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2)))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) n).trans
    (measure_le_le_sqrt_two_mul_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hn)

/-- **Cluster-volume tails.** With `M = ⨆ x, χ(x) < ∞`, for every real `n > 0`,
`P(|K_o| ≥ n) ≤ min{1, (√2 χ(o)/n) e^{−n/(4M²)}, (1 + χ(o)/M²) e^{−n/(2M²)}}`. -/
theorem law_encard_cluster_ge_le_min (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {n : ℝ} (hn : 0 < n) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (min 1 (min (sqrt 2 * (chi q o).toReal / n *
          exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2))))
        ((1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2) *
          exp (-(n / (2 * (⨆ x, chi q x).toReal ^ 2)))))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) n).trans
    (measure_le_le_min_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hn)

/-- **Pure exponential cluster-volume tail.** With `M = ⨆ x, χ(x) < ∞`,
`P(|K_o| ≥ n) ≤ e^{−n/(4M²)}` whenever `n ≥ 4M² log(1 + χ(o)/M²)`. -/
theorem law_encard_cluster_ge_le_exp (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {n : ℝ}
    (hn : 4 * (⨆ x, chi q x).toReal ^ 2 *
      log (1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2) ≤ n) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2)))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) n).trans
    (measure_le_le_exp_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hn)

/-! ### Non-vacuity -/

/-- The zero profile has `χ ≡ 1`, so `⨆ x, χ(x) < ∞` and the tail bound applies, here with
`χ(o) = M = 1` on `ℤ`. -/
example (n : ℝ) (hn : 0 < n) :
    law (fun _ : Sym2 ℤ => (0 : unitInterval))
        {ω | ENNReal.ofReal n ≤ ((cluster ω (0 : ℤ)).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (min 1 (min (sqrt 2 * 1 / n * exp (-(n / (4 * 1 ^ 2))))
        ((1 + 1 / 1 ^ 2) * exp (-(n / (2 * 1 ^ 2)))))) := by
  have h1 : ∀ x : ℤ, chi (fun _ : Sym2 ℤ => (0 : unitInterval)) x = 1 :=
    chi_eq_one_of_offDiagonal_zero _ fun _ _ _ => rfl
  have hM : (⨆ x, chi (fun _ : Sym2 ℤ => (0 : unitInterval)) x) = 1 := by simp [h1]
  have h := law_encard_cluster_ge_le_min (fun _ : Sym2 ℤ => (0 : unitInterval)) 0
    (by rw [hM]; exact ENNReal.one_ne_top) hn
  rwa [hM, h1, ENNReal.toReal_one] at h

end PercLib.Percolation.Bond
