/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the binary-tree-percolation article.
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.BinaryTreeArm
public import PercLib.Models.BinaryTreeAsymptotics
public import PercLib.Models.BinaryTreeMoments

/-!
# Percolation on the rooted binary tree: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `binaryTree_critical_isEquivalent`
* `binaryTree_arm_and_two_point`
* `binaryTree_law_card_uniform_and_nearCritical`
* `binaryTree_moments_asymptotics`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics Real PercLib.Probability
  PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

/-- At `p = 1/2`, `P(|K| = n) ~ n^{-3/2}/√π` and `P(|K| ≥ n) ~ 2 n^{-1/2}/√π`. -/
@[tag "AAZS"]
theorem binaryTree_critical_isEquivalent (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) :
    (fun n : ℕ => (law q {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal)
      ~[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) / √π) ∧
    (fun n : ℕ => (law q {ω | (n : ℕ∞) ≤ (cluster ω []).encard}).toReal)
      ~[atTop] (fun n : ℕ => 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) / √π) :=
  ⟨binaryTree_law_card_isEquivalent p q hq hp, binaryTree_law_le_encard_isEquivalent p q hq hp⟩

/-- At `p = 1/2` (any diagonal), `r_n = P(the root cluster reaches generation n)`
satisfies `r_0 = 1`, `r_{n+1} = r_n - r_n^2/4` and `r_n ~ 4/n`; and for every `p` and all
`x, y`, `τ(x,y) = p^{d(x,y)}`. -/
@[tag "NDIC"]
theorem binaryTree_arm_and_two_point :
    (∀ q : Sym2 (List (Fin 2)) → unitInterval, (∀ e, ¬ e.IsDiag → q e =
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0) →
      (law q {ω | ∃ w ∈ cluster ω [], w.length = 0}).toReal = 1 ∧
      (∀ n : ℕ, (law q {ω | ∃ w ∈ cluster ω [], w.length = n + 1}).toReal =
        (law q {ω | ∃ w ∈ cluster ω [], w.length = n}).toReal -
          (law q {ω | ∃ w ∈ cluster ω [], w.length = n}).toReal ^ 2 / 4) ∧
      (fun n : ℕ => (law q {ω | ∃ w ∈ cluster ω [], w.length = n}).toReal)
        ~[atTop] (fun n : ℕ => 4 / (n : ℝ))) ∧
    (∀ (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval),
      (∀ e, ¬ e.IsDiag → q e =
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
          else 0) →
      ∀ x y : List (Fin 2), tau q x y = (unitInterval.toNNReal p : ℝ≥0∞) ^
        (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).dist x y) :=
  ⟨fun q hq => ⟨binaryTree_law_reach_depth_zero q hq, binaryTree_law_reach_depth_succ q hq,
      binaryTree_law_reach_depth_isEquivalent q hq⟩,
    fun p q hq x y => tau_kTree_eq_pow p q (fun u w huw => hq s(u, w) (by simpa using huw)) x y⟩

/-- For `0 < p < 1`, `P_p(|K| = n) ~ (1-p)/(p√π) n^{-3/2} (4p(1-p))^n` with relative error
depending only on `n`, hence uniformly in `p`; and if `p_n = 1/2 + ε_n` with `ε_n → 0` and
`n ε_n^4 → 0`, then
`P_{p_n}(|K| = n) ~ n^{-3/2} e^{-4nε_n^2}/√π`. -/
@[tag "V5OZ"]
theorem binaryTree_law_card_uniform_and_nearCritical :
    (∀ q : unitInterval → Sym2 (List (Fin 2)) → unitInterval,
      (∀ p e, ¬ e.IsDiag → q p e =
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
          else 0) →
      (∀ p : unitInterval, (p : ℝ) ∈ Set.Ioo 0 1 → ∀ n : ℕ, 1 ≤ n →
        (law (q p) {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal /
          ((1 - (p : ℝ)) / ((p : ℝ) * √π) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n) =
          (catalan n : ℝ) / 4 ^ n / ((n : ℝ) ^ (-(3 / 2 : ℝ)) / √π)) ∧
      TendstoUniformlyOn (fun (n : ℕ) (p : unitInterval) =>
        (law (q p) {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal /
          ((1 - (p : ℝ)) / ((p : ℝ) * √π) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n))
        (fun _ => 1) atTop {p : unitInterval | (p : ℝ) ∈ Set.Ioo 0 1}) ∧
    (∀ (pn : ℕ → unitInterval) (q : ℕ → Sym2 (List (Fin 2)) → unitInterval),
      (∀ n e, ¬ e.IsDiag → q n e =
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          pn n else 0) →
      Tendsto (fun n => (pn n : ℝ) - 1 / 2) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => (n : ℝ) * ((pn n : ℝ) - 1 / 2) ^ 4) atTop (𝓝 0) →
      (fun n : ℕ => (law (q n) {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal)
        ~[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-4 * n * ((pn n : ℝ) - 1 / 2) ^ 2) / √π)) :=
  ⟨fun q hq => ⟨fun _ hp _ hn => binaryTree_law_card_ratio_eq q hq hp hn,
      binaryTree_law_card_tendstoUniformlyOn q hq⟩, fun pn q hq h1 h2 =>
    binaryTree_law_card_nearCritical_isEquivalent pn q hq h1 h2⟩

/-- For the moments `M_s(p) = ∑_{n ≥ 1} n^s P_p(|K| = n)` and
`λ = -log(4p(1-p))`, as `p → 1/2`, `p ≠ 1/2`: `M_s ~ Γ(s-1/2) λ^{-(s-1/2)}/√π` for `s > 1/2`;
`M_{1/2} ~ log(1/λ)/√π`; for `s < 1/2`, `M_s(1/2) < ∞` and `M_s(p) → M_s(1/2)`;
`M_{s+1}/M_s ~ (s-1/2)/(4(p-1/2)^2)` for `s > 1/2`; and `λ ~ 4(p-1/2)^2`. -/
@[tag "GGVG"]
theorem binaryTree_moments_asymptotics (q : ℝ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ (p : ℝ) (hp : p ∈ unitInterval), ∀ e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨p, hp⟩ : unitInterval) else 0) :
    (∀ s : ℝ, 1 / 2 < s →
      (fun p : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)
      ~[𝓝[≠] (1 / 2)]
      fun p => Gamma (s - 1 / 2) * (-log (4 * p * (1 - p))) ^ (-(s - 1 / 2)) / √π) ∧
    ((fun p : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
        (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)
      ~[𝓝[≠] (1 / 2)]
      fun p => log (1 / -log (4 * p * (1 - p))) / √π) ∧
    (∀ s : ℝ, s < 1 / 2 →
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ s *
        (law (q (1 / 2)) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal) ∧
      Tendsto (fun p : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal)
        (𝓝[≠] (1 / 2))
        (𝓝 (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q (1 / 2)) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal))) ∧
    (∀ s : ℝ, 1 / 2 < s →
      (fun p : ℝ => (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (s + 1) *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal) /
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
          (law (q p) {ω | (cluster ω []).ncard = n + 1 ∧ (cluster ω []).Finite}).toReal))
      ~[𝓝[≠] (1 / 2)]
      fun p => (s - 1 / 2) / (4 * (p - 1 / 2) ^ 2)) ∧
    ((fun p : ℝ => -log (4 * p * (1 - p))) ~[𝓝[≠] (1 / 2)] fun p => 4 * (p - 1 / 2) ^ 2) :=
  ⟨fun _ hs => binaryTree_moment_isEquivalent_of_gt q hq hs,
    binaryTree_moment_isEquivalent_half q hq,
    fun _ hs => binaryTree_moment_tendsto_of_lt q hq hs,
    fun _ hs => binaryTree_moment_ratio_isEquivalent q hq hs, lambda_isEquivalent⟩

end PercLib.Models
