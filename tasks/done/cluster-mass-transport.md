---
id: cluster-mass-transport
title: Mass transport inside clusters - finite-cluster averaging and no invariant representative
difficulty: medium
kind: interface
labels: []
---

# Mass transport inside clusters: finite-cluster averaging and no invariant representative

## Goal
Prove wiki assertions **4SZ9** and **O0TO** (article `mass-transport`) and tag them. Both are
applications of the expected mass-transport principle (`K5ZX`, `X5NY`, proved in
`PercLib/Probability/MassTransport.lean`) to an invariant random graph on a countable group:
averaging an equivariant quantity over a finite cluster does not change its mean, and no
equivariant rule picks a single vertex out of an infinite cluster. They share one setting and
one set of helper lemmas, so they form one task.

## Target
Setting: a countable group `Γ`, a probability space `(Ω, μ)` (`μ` a probability measure, matching
the wiki's "under an invariant random-graph-and-mark law"; 4SZ9 may be stated for any measure
`μ`, O0TO needs `IsProbabilityMeasure μ`), measure-preserving maps
`act g : Ω → Ω` (as in `lintegral_mass_transport`), and a measurable random configuration
`G : Ω → Config Γ` that is equivariant: `G (act g ω) = Sym2.map (g * ·) '' G ω`. (Auxiliary marks
live in `Ω`.) Write `K_x(ω) = cluster (G ω) x`.

**4SZ9.** Let `f : Ω → Γ → ℝ≥0∞` be measurable in `ω` and equivariant,
`f (act g ω) (g * x) = f ω x`. Then
`E[f(·,1); |K_1| < ∞] = E[|K_1|⁻¹ Σ_{x ∈ K_1} f(·,x); |K_1| < ∞]`.
In particular, for a measurable equivariant set `R : Ω → Set Γ` that meets every finite
cluster in exactly one vertex and no infinite cluster,
`μ(1 ∈ R) = E[|K_1|⁻¹; |K_1| < ∞]`.

**O0TO.** If `R : Ω → Set Γ` is measurable and equivariant and meets each infinite cluster in at
most one vertex, then almost surely `R` contains no vertex of an infinite cluster. Hence, if
infinite clusters exist with positive probability, no such `R` meets every infinite cluster in
exactly one vertex.

Sketch (4SZ9, main identity; spelling free):
```lean
theorem lintegral_indicator_finite_eq_lintegral_average {Γ Ω : Type*} [Group Γ] [Countable Γ]
    [MeasurableSpace Ω] {μ : Measure Ω} (act : Γ → Ω → Ω)
    (hact : ∀ g, MeasurePreserving (act g) μ μ) (G : Ω → Config Γ) (hG : Measurable G)
    (hGeq : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω)
    (f : Ω → Γ → ℝ≥0∞) (hf : ∀ x, Measurable fun ω => f ω x)
    (hfeq : ∀ g ω x, f (act g ω) (g * x) = f ω x) :
    ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator (fun ω => f ω 1) ω ∂μ =
      ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator
        (fun ω => ((cluster (G ω) 1).ncard : ℝ≥0∞)⁻¹ * ∑' x, (cluster (G ω) 1).indicator (f ω) x)
        ω ∂μ
```
Write "exactly one" with `∃!`, not with `ncard` (which is `0` on infinite sets). Bond percolation
with a left-invariant profile is the special case `law_mass_transport`; add it as a corollary if
cheap. Measurability of cluster events: `measurableSet_conn`, `measurableSet_cluster_infinite`
(`PercLib/Percolation/Bond/Basic.lean`).

Tagged statements: one per tag, each the full assertion (4SZ9 with its selection corollary;
O0TO with its consequence).

## Owned files
- New `PercLib/Probability/MassTransportClusters.lean` (area lemmas).
- New `PercLib/Probability/Tags/MassTransportClusters.lean` (the two tagged statements only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/MassTransport.lean`, `PercLib/Percolation/Bond/Basic.lean`,
`PercLib/Percolation/Bond/ClusterPartition.lean`, mathlib; wiki assertions 4SZ9, O0TO, K5ZX,
X5NY.

## Stop condition
Both tagged and proved, modules built with `--wfail`. If one of the two is found false or
under-hypothesised as written, report it and finish the other.

## Hand-off
Pull request description: both tagged statements in full, the area lemmas, what was searched,
build result.
