/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, branch `work/yujinhkim-critical-lrp-orchestration`,
file(s) `PercLib/Probability/Exploration/Envelope.lean`; added at source revision
`d5e0763c9187ea85e4877ae4f6a19ab0b58c1c4d`,
supplied under its Apache-2.0 header.
The forbidden `set_option autoImplicit false` was removed (the build enforces it), and the
elementary API lemmas were separated from the six source theorems.
-/
module

public import PercLib.Probability.Exploration.Envelope.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Scalar exploration-envelope bounds

Monotonicity of the recursive envelope, its explicit `1 / (m * λ)` bound, and existence of an
admissible `λ > 1` when `0 < m < 1`. Additional elementary API lemmas concern positivity,
one-step monotonicity and the combined existence/bound formulation.

These real-analytic results are ingredients for a frontier-exploration estimate, not a cluster
moment theorem. Mathematical reference: the uniform-row-sum exploration outline, Lemmas 5.1–5.2.
-/

@[expose] public section

open PercLib.Probability.ExplorationEnvelope

namespace PercLib.Probability.ExplorationEnvelope

/-! ## `Exploration/Envelope.lean` (verbatim statements) -/

variable {m lam : ℝ}

/-- `PROOF.md` Lemma 5.1 (lower half): every envelope entry is at least `1`. -/
theorem one_le_envelope (hm : 0 ≤ m) (hlam : 1 ≤ lam) (n : ℕ) : 1 ≤ envelope m lam n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [envelope_succ, envelopeStep]
    refine Real.one_le_exp ?_
    have h1 : (1 : ℝ) ≤ lam * envelope m lam n := by
      simpa using mul_le_mul hlam ih (by norm_num) (by linarith)
    exact mul_nonneg hm (by linarith)

/-- `PROOF.md` Lemma 5.1: the envelope sequence is nondecreasing. -/
theorem envelope_le_succ (hm : 0 ≤ m) (hlam : 1 ≤ lam) (n : ℕ) :
    envelope m lam n ≤ envelope m lam (n + 1) := by
  induction n with
  | zero =>
    rw [envelope_zero, envelope_succ, envelopeStep, envelope_zero]
    refine Real.one_le_exp ?_
    have h1 : (1 : ℝ) ≤ lam * 1 := by simpa using hlam
    exact mul_nonneg hm (by linarith)
  | succ n ih =>
    rw [envelope_succ, envelope_succ, envelopeStep, envelopeStep]
    refine Real.exp_le_exp.mpr ?_
    have h2 : lam * envelope m lam n ≤ lam * envelope m lam (n + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) hm

/-- `PROOF.md` Lemma 5.1: the envelope sequence is monotone. -/
theorem envelope_monotone (hm : 0 ≤ m) (hlam : 1 ≤ lam) : Monotone (envelope m lam) :=
  monotone_nat_of_le_succ (envelope_le_succ hm hlam)

/-- The induction used in `PROOF.md` Proposition 5.3 and Lemma 5.2: any `u ≥ 1` fixed by one step
of the recursion bounds the whole envelope sequence. -/
theorem envelope_le_of_step_le (hm : 0 ≤ m) (hlam : 1 ≤ lam) {u : ℝ} (hu : 1 ≤ u)
    (hstep : envelopeStep m lam u ≤ u) (n : ℕ) : envelope m lam n ≤ u := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [envelope_succ, envelopeStep]
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    have h2 : lam * envelope m lam n ≤ lam * u :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) hm

/-- `PROOF.md` Lemma 5.2: for `0 < m ≤ 1`, `1 ≤ λ` and `m λ ≤ e^{m-1}`, the explicit candidate
`u = 1/(m λ)` is a supersolution of the recursion, hence bounds the whole sequence. -/
theorem envelope_le_inv_mul (hm : 0 < m) (hm1 : m ≤ 1) (hlam : 1 ≤ lam)
    (hcond : m * lam ≤ Real.exp (m - 1)) (n : ℕ) :
    envelope m lam n ≤ 1 / (m * lam) := by
  have hmpos : (0 : ℝ) < m * lam := by nlinarith
  have hle1 : m * lam ≤ 1 := by
    have h2 : Real.exp (m - 1) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    linarith
  refine envelope_le_of_step_le hm.le hlam ?_ ?_ n
  · have h := one_div_le_one_div_of_le hmpos hle1
    rwa [one_div_one] at h
  · rw [envelopeStep]
    have harg : m * (lam * (1 / (m * lam)) - 1) = 1 - m := by field_simp
    rw [harg]
    have he : Real.exp (1 - m) = 1 / Real.exp (m - 1) := by
      rw [show (1 : ℝ) - m = -(m - 1) by ring, Real.exp_neg, one_div]
    rw [he]
    exact one_div_le_one_div_of_le hmpos hcond

/-- For `0 < m < 1` there is `λ > 1` with `m λ ≤ e^{m-1}`, so the hypothesis of `PROOF.md`
Theorem 1 with `λ > 1` is satisfiable. -/
theorem exists_admissible_lambda (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ m * lam ≤ Real.exp (m - 1) := by
  have hmlog : Real.log m < m - 1 := Real.log_lt_sub_one_of_pos hm (ne_of_lt hm1)
  have hmexp : m < Real.exp (m - 1) := by
    calc m = Real.exp (Real.log m) := (Real.exp_log hm).symm
      _ < Real.exp (m - 1) := Real.exp_lt_exp.mpr hmlog
  refine ⟨(1 + Real.exp (m - 1) / m) / 2, ?_, ?_⟩
  · have : 1 < Real.exp (m - 1) / m := by rw [lt_div_iff₀ hm]; linarith
    linarith
  · have hkey : Real.exp (m - 1) / m * m = Real.exp (m - 1) := by field_simp
    nlinarith

/-- port_added: the envelope step is strictly positive (the conversion `ENNReal.ofReal` at the
call sites `CriticalLRP/Exploration/BFS/Poisson/Assemble.lean` needs nonnegativity, not merely
this positivity). -/
theorem envelopeStep_pos (m lam u : ℝ) : 0 < envelopeStep m lam u := Real.exp_pos _

/-- port_added: nonnegativity of the envelope step, the side condition for `ENNReal.ofReal`. -/
theorem envelopeStep_nonneg (m lam u : ℝ) : 0 ≤ envelopeStep m lam u :=
  (envelopeStep_pos m lam u).le

/-- port_added: `1 ≤ envelopeStep m lam u` as soon as `0 ≤ m` and `1 ≤ λ u`; this is the
step-level form of `one_le_envelope` used when the recursion is unrolled one step at a time. -/
theorem one_le_envelopeStep (hm : 0 ≤ m) {u : ℝ} (hu : 1 ≤ lam * u) :
    1 ≤ envelopeStep m lam u := by
  rw [envelopeStep]
  exact Real.one_le_exp (mul_nonneg hm (by linarith))

/-! ## Additions required by the ported call sites (not in the source file)

These are marked `port_added` in the documentation string: they are *new* statements, not
source statements, and are listed separately in `INVENTORY.md` so that interface review can
accept or reject them.  Each one is a combination or a one-line corollary of the source
results, added because the downstream `CriticalLRP` call sites
(`Exploration/BFS/HighTemperature/Moment/Natural.lean`, `CriticalLRP/IntensityMoments.lean`,
`CriticalLRP/PowerLawHighTemp/Tail.lean`) use `exists_admissible_lambda` and
`envelope_le_inv_mul` in immediate succession, and because the step function's monotonicity in
`u` is what makes `envelope_le_of_step_le` a supersolution argument rather than a curiosity. -/

/-- port_added: every envelope entry is strictly positive. -/
theorem envelope_pos (hm : 0 ≤ m) (hlam : 1 ≤ lam) (n : ℕ) : 0 < envelope m lam n :=
  lt_of_lt_of_le zero_lt_one (one_le_envelope hm hlam n)

/-- port_added: `envelopeStep m lam` is monotone in its last argument (for `0 ≤ m`, `0 ≤ lam`). -/
theorem envelopeStep_mono (hm : 0 ≤ m) (hlam : 0 ≤ lam) :
    Monotone (envelopeStep m lam) := by
  intro u v huv
  rw [envelopeStep, envelopeStep]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (by linarith [mul_le_mul_of_nonneg_left huv hlam]) hm)

/-- port_added: the combined interface actually consumed downstream — for `0 < m < 1` there is a
single `λ > 1` with `m λ ≤ e^{m-1}` *and* the resulting uniform envelope bound
`∀ n, u_n ≤ 1/(m λ)`.  This is `exists_admissible_lambda` composed with `envelope_le_inv_mul`;
it is the form in which `PROOF.md` Theorem 1's hypothesis is invoked. -/
theorem exists_admissible_lambda_envelope_bound (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ m * lam ≤ Real.exp (m - 1) ∧
      ∀ n : ℕ, envelope m lam n ≤ 1 / (m * lam) := by
  obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, hcond, fun n => envelope_le_inv_mul hm hm1.le hlam.le hcond n⟩

end PercLib.Probability.ExplorationEnvelope
