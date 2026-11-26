---
id: abelian-field-asymptotics
title: Exact Abelian asymptotics of the field transform of a power tail
difficulty: hard
kind: interface
labels: []
---

# Exact Abelian asymptotics of the field transform of a power tail

## Goal
Prove wiki assertion **FZQQ** (article `sharpness-exercises`) and tag it: for a variable `T` on
`{1, 2, …, ∞}` with `P(T ≥ n) ∼ A n^{−α}`, the transform `m(γ) = E[1 − (1 − γ)^T]` behaves like
`A Γ(1−α) γ^α`, `A γ log(1/γ)` or `γ E T` as `γ ↓ 0` according as `α < 1`, `α = 1`, `α > 1`;
under a logarithmic tail exponent, `m(γ) = γ^{min(α,1) + o(1)}`.

## Target
Let `T : Ω → ℕ∞` be measurable with `T ≥ 1`, under a probability measure, `A > 0`, `α > 0`, and
`m(γ) = E[1 − (1 − γ)^T]` for `γ ∈ (0,1)`, with `(1 − γ)^∞ = 0`.
1. If `P(T ≥ n) ∼ A n^{−α}` as `n → ∞`, then `P(T = ∞) = 0`; for `α > 1`, `E T < ∞`; and as
   `γ → 0⁺`, `m(γ) ∼ A Γ(1−α) γ^α` (`0 < α < 1`), `m(γ) ∼ A γ log(1/γ)` (`α = 1`),
   `m(γ) ∼ γ E T` (`α > 1`).
2. If `log P(T ≥ n) / log n → −α`, then `log m(γ) / log γ → min(α, 1)` as `γ → 0⁺`.

Sketch of the transform and of one conclusion (spelling free; `Real.Gamma`, `~[𝓝[>] 0]`):
```lean
-- inline: m γ = ∫ ω, (if T ω = ⊤ then 1 else 1 - (1 - γ) ^ (T ω).toNat) ∂μ
theorem field_isEquivalent_of_tail_lt_one {α A : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (htail : (fun n : ℕ => (μ {ω | (n : ℕ∞) ≤ T ω}).toReal) ~[atTop]
      fun n => A * (n : ℝ) ^ (-α)) :
    (fun γ : ℝ => ∫ ω, (if T ω = ⊤ then 1 else 1 - (1 - γ) ^ (T ω).toNat) ∂μ) ~[𝓝[>] 0]
      fun γ => A * Real.Gamma (1 - α) * γ ^ α
```
Intended proof (article): with `h = −log(1 − γ) ∼ γ`, the tail identity
`m(γ) = (e^h − 1) Σ_{n≥1} e^{−hn} P(T ≥ n)` reduces everything to Abelian theorems for
`Σ b_n e^{−hn}`, which the library has: `tsum_exp_isEquivalent_of_isEquivalent`,
`tendsto_rpow_mul_tsum_exp_of_isEquivalent`, `tsum_exp_isEquivalent_log_of_isEquivalent`
(`PercLib/Analysis/AbelianSums.lean`). The tail series of the ghost transform is tagged as `0NVH`
and the `α < 1` tail–transform equivalence as `3C2F` (`PercLib/Probability/GhostTransform.lean`,
`PercLib/Probability/Tags/GhostTransform.lean`); reuse them rather than re-deriving the series.

Tagged statement: the conjunction of 1 and 2.

## Owned files
- New `PercLib/Analysis/AbelianField.lean` (area lemmas).
- New `PercLib/Analysis/Tags/AbelianField.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Analysis/AbelianSums.lean`, `PercLib/Probability/GhostTransform.lean`,
`PercLib/Probability/Tags/GhostTransform.lean`, `PercLib/Probability/TailSums.lean`, mathlib; wiki
assertions FZQQ, 0NVH, 3C2F.

## Stop condition
FZQQ tagged and proved, modules built with `--wfail`; or the statement is found false or
under-hypothesised as written (report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
