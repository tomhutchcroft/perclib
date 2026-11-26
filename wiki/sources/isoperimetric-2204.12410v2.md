# Bäumler–Berger: isoperimetric critical bounds

Source: *Isoperimetric lower bounds for critical exponents for long-range percolation*, [arXiv:2204.12410v2](https://arxiv.org/html/2204.12410v2), 28 October 2023. Journal locator: *Annales de l’Institut Henri Poincaré, Probabilités et Statistiques* **60** (2024), 721–730, [DOI 10.1214/22-AIHP1342](https://doi.org/10.1214/22-AIHP1342). The mathematical comparison here uses the preprint, not unchecked journal formulas.

Read on 17 November 2026: all mathematical sections 1–2 in versioned HTML. The boundary lemma, profile and harmonic-sum estimate were also checked in extracted PDF text on printed pp.8–10. No visual-PDF audit. Bibliographic references identify inputs; this map does not claim to have audited every cited paper.

| Passage | Wiki treatment | Scope |
|---|---|---|
| Section1: model and exponent conventions | [Article setup](../articles/isoperimetric-lower-bounds.md#section-profile), [BNQK](../articles/isoperimetric-lower-bounds.md#section-exponents) | Symmetric translation-invariant summable intensities; finite critical intensity is explicit. Norm equivalence transports the fixed-norm upper bound to the supremum norm. |
| Theorems1.1–1.2 | BNQK | Separate cluster-tail and two-point exponent consequences; logarithmic limits are handled with strictly weaker exponents before taking a limit. |
| Figures1–2 and crossover discussion | Historical context | Predictions and source-era literature descriptions are not new theorems or claims about today's research status. |
| Theorem2.1 | [12NL](../articles/finite-set-hyperscaling.md#section-rooted-damping) | Existing finite-witness splitting proof gives maximum and rooted intersection damping. For induced finite-box clusters, apply it after deleting exterior bonds. |
| Lemmas2.2–2.3 and equation(7) | [UVQ6](../articles/finite-set-hyperscaling.md#section-window-tails), with BNQK | Existing quantitative window proof supplies both scales; no duplicate assertion. A truncated-mean bound gives a tail bound by monotonicity. |
| Lemma2.4 and equation(8) | Article setup and BNQK | Internal connectivity is bounded by unrestricted connectivity. The arbitrary-root version uses a translated cube contained in a cube of twice the radius. |
| Section2.2 boundary geometry | [31X5](../articles/isoperimetric-lower-bounds.md#section-surface) | Exact pair count and two-sided shell comparison explain the transition at alpha=1. |
| Equation(11) | [R84Z](../articles/boundary-laws.md#section-critical-flux) | Existing proof uses continuity, the finite-size criterion and transitivity. |
| Lemma2.5 | [PTM2](../articles/isoperimetric-lower-bounds.md#section-profile),31X5 | Direct crossing count for each displacement gives the bound for an arbitrary summable bond profile. |
| Proposition2.6 | [VVB0](../articles/isoperimetric-lower-bounds.md#section-critical) | Lower bound already holds for the internal root cluster, hence also for the unrestricted box intersection. |
| Proposition2.7 | BNQK | Window hyperscaling and the preceding lower bound yield the exponent inequality. |
| Discussion after Proposition2.6 | [0BJP](../articles/isoperimetric-lower-bounds.md#section-matching) | Matching averages for alpha<1; at alpha=1 the logarithmic growth exponent is fixed but a logarithmic comparison gap remains. No pointwise assertion. |

For the finite-window step, if the truncated mean of the full cluster is bounded by C N^(1-theta), then the tail at N is at most C N^(-theta). Translation gives this bound at every root; intersection with a finite window only reduces the size. UVQ6 then gives the quantile scale |Lambda|^(1/(1+theta)) and the root-mean scale |Lambda|^((1-theta)/(1+theta)), with explicit constants. This reuses an existing proof rather than inferring tightness from a one-point first-moment estimate. The logarithmic tail law is only used through exponents below its limit.

The [provisional erratum](../errata/baumler-berger-isoperimetric-2022.json) concerns the zero logarithmic factor at n=1. Using log(en) throughout gives the same asymptotic statements. It is recorded, alongside the canonical WIKI handoff. The historical missing logarithm in the v1 abstract is corrected in v2 and is not entered as a current fault.

The written proof of the critical lower bound assumes a finite critical point. It does not infer one from an upper kernel envelope, nor from a nonzero kernel alone. The matching-average corollary uses globally two-sided power bounds with alpha<d, so the existing power-law transition theorem supplies this hypothesis. More general support or eventual-envelope formulations need their own hypotheses checked.

Formal correspondence remains pending. The new tags have no compiled association. The finite-size and rooted-damping dependencies are mathematical proofs already in the wiki; their presence is not a certificate that the new isoperimetric theorem is formalized.
