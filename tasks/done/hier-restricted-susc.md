---
id: hier-restricted-susc
title: Restricted susceptibility bound at the critical point on the hierarchical lattice
difficulty: medium
kind: proof-only
labels: []
---

# Restricted susceptibility bound at the critical point on the hierarchical lattice

## Goal
Prove Proposition 2.7 of arXiv:2103.17013v1 at `β = β_c`: the expected size of the origin's
cluster inside the ball `Λ_n`, for the model restricted to `Λ_n`, is at most a constant times
`L^{αn}`, with a constant that does not depend on the kernel. This is the upper half of wiki
assertion 655W and the last missing ingredient of Theorem 1.1 of that paper (the statement
`HierarchicalTwoPointAveraged` in `PercLib/Models/Hierarchical/Defs.lean`).

## Target
Setting (as in `PercLib/Models/HierarchicalSibling.lean`): `V = ℕ →₀ (Fin d → ZMod L)`, level
`h z = z.support.sup Nat.succ`, ball `Λ_n = {h ≤ n}`; `J` translation invariant with
`c L^{−(d+α) h(v−u)} ≤ J(u,v) ≤ C L^{−(d+α) h(v−u)}` for `u ≠ v`; `d ≥ 1`, `L ≥ 2`,
`0 < α < d`, `0 < c ≤ C`; `β_c = rootCriticalIntensity J 0`; `q_n` the profile
`intensityProfile J β_c` restricted to pairs inside `Λ_n`; `a_n = E_{q_n} |K_0 ∩ Λ_n|`
(`∫⁻ ω, clusterIntersection (finite_level_ball n).toFinset ω 0 ∂law q_n`).

**Statement.** There is `C' < ∞` depending only on `d, L, α, c, C` (quantified **before** `J`)
such that `a_n ≤ C' L^{αn}` for every `n`. Sketch:
```lean
theorem exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity
    [NeZero L] (hL : 2 ≤ L) (hd : 1 ≤ d) {α c C : ℝ} (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hcC : c ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
      (∀ x u v, J s(u + x, v + x) = J s(u, v)) →
      (∀ u v, u ≠ v → c * (L : ℝ) ^ (-(((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℝ)))
        ≤ J s(u, v)) →
      (∀ u v, u ≠ v → (J s(u, v) : ℝ) ≤
        C * (L : ℝ) ^ (-(((d : ℝ) + α) * ((v - u).support.sup Nat.succ : ℝ)))) →
      ∀ n : ℕ, ∫⁻ ω, (clusterIntersection (finite_level_ball n).toFinset ω 0 : ℝ≥0∞)
          ∂law (fun e => if e ∈ {z | z.support.sup Nat.succ ≤ n}.sym2 then
            intensityProfile J (rootCriticalIntensity J 0).toNNReal e else 0)
        ≤ ENNReal.ofReal (C' * (L : ℝ) ^ (α * n))
```

**Proof route** (from the paper; monotonicity in `β` is not needed). At `β_c`:
- the quantile bound `β_c M_n(β_c)² ≤ A L^{(d+α)n}` with `0 < β_c < ∞`
  (`rootCriticalIntensity_mem_Ioo_and_mul_sq_tightnessScale_le`,
  `PercLib/Models/HierarchicalEndpoint.lean`; choose `ℓ` from `d, L, α` only);
- the sibling recursion `k β L^{−αn} a_n² ≤ Σ_{h x = n+1} τ_{q_{n+1}}(0,x) ≤ a_{n+1}`
  (`sum_shell_tau_ge`, `PercLib/Models/HierarchicalSibling.lean`), with `k = k(d,L,α,c,A)`;
- the trivial bound `a_{n+1} ≤ |Λ_{n+1}| = L^{d(n+1)}`;
- `β_c` bounded below in terms of `d, L, α, C` (`ofReal_le_rootCriticalIntensity_of_powerLaw`,
  `PercLib/Models/HierarchicalPowerKernel.lean`).
Put `y_n = k β_c L^{−αn} a_n / L^{αn}`-type normalisation so that `y_{n+1} ≥ y_n²` while
`y_n ≤ K L^{(d−α)n}`; a deterministic runaway lemma then forces `y_n ≤ 1` for all `n`.
State that runaway lemma separately, for real sequences, at the generality its proof supports.

## Owned files
- New `PercLib/Models/HierarchicalRestrictedSusc.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Models/HierarchicalEndpoint.lean`, `HierarchicalSibling.lean`,
  `HierarchicalPowerKernel.lean`, `HierarchicalRunaway.lean`, `HierarchicalTranslation.lean`,
  `HierarchicalGeometry.lean`, `PercLib/Percolation/Bond/CrossEdge.lean`,
  `PercLib/Percolation/Bond/Tightness/*`.
- arXiv:2103.17013v1, Proposition 2.7, Lemma 2.8, Proposition 2.12 (note that Proposition
  2.12(ii) as printed has constant 1; the library's corrected form carries a factor `1/β_c`).

## Stop condition
The bound is proved with `C'` uniform in `J` as stated, and the module builds with `--wfail`;
or a gap is found (report the statement, the missing hypothesis and a counterexample if any).
Never weaken the uniformity in `J`.

## Hand-off
Pull request description: the theorem with its full signature and the explicit `C'`; the
runaway lemma; searches; build result. A follow-up task (Theorem 1.1, proving
`HierarchicalTwoPointAveraged`) becomes startable once this merges.
