# Sharp hierarchical upper bounds: the full-space comparison

Read the introduction and all of section 2 of [arXiv:2202.07634v2 HTML](https://arxiv.org/html/2202.07634v2), 16 November 2026. The [26-page PDF](https://arxiv.org/pdf/2202.07634v2) was compared at the five passages recorded below, not throughout. The PDF title date is 28 July 2022; the HTML displays 24 August 2026. The journal reference is J. Math. Phys. 63, 113301 (2022), [doi:10.1063/5.0088450](https://doi.org/10.1063/5.0088450).

The journal typesetting was not compared in this pass; the errata locators refer to the specified arXiv renditions.

Theorem 1.1 assumes a symmetric, translation-invariant kernel with finite row sum and a lower power-law envelope at every nonzero displacement, with 0 < alpha < d. It bounds full-space connections averaged over a cube; it is not a pointwise bound and is stronger than the same estimate for paths constrained to the cube. The radial application checks both the norm conversion and the finitely many small displacements.

| Source passage | Treatment |
| --- | --- |
| Section 2.1 and (2.8)–(2.9) | [EKDO](../articles/hierarchical-comparison.md#section-decomposition) defines compatible translated grids, independent hierarchical layers, restricted full clusters, quantiles and goodness. |
| Lemmas 2.1 and 2.3; Proposition 2.2 | [F2G0](../articles/hierarchical-comparison.md#section-good-hierarchy) uses closed goodness conditions and compactness. Its continuity proof couples every restricted law below the same finite full cluster. |
| Lemma 2.6; Proposition 2.4; Corollary 2.5 | [27T8](../articles/hierarchical-comparison.md#section-maximum) controls dependent child maxima by universal tightness, then uses independent parent edges. The growth contradiction keeps the level-dependent threshold. |
| Lemmas 2.8–2.9; Proposition 2.7 | [2P4M](../articles/hierarchical-comparison.md#section-restricted) gives cap retention, Harris factorization and a second growth contradiction. |
| Lemma 2.11; Corollary 2.12 | [F9QT](../articles/hierarchical-comparison.md#section-selection) controls all ancestor sums by finite counting and compactness, without assigning transitivity to the restricted law. |
| Lemma 2.10; Theorem 1.1 proof | [MRZO](../articles/hierarchical-comparison.md#section-full-space) uses BK on distinct layer coordinates, the geometric series with factor 16^k, interior cube averaging, and the critical limit. |

The proofs use the wiki's finite-witness BK extension, universal intersection bounds and summable-kernel sharpness. They do not import Gladkov's inequality or a triangle condition. [The radial application](../articles/hierarchical-comparison.md#section-radial-input) supplies the critical window premise in the [Part III good-scale assembly](../articles/cutoff-hydrodynamics.md#section-model-good-scales); Gladkov's finite theorem remains a separate input there.

Five [provisional errata](../errata/hutchcroft-hierarchical-upper-2022.json) concern the digit exponent in the grid definition, the mismatch equality in the continuity coupling, the initial scale in the maximum contradiction, one omitted squared selection factor, and the support restriction of a parent layer. The corresponding PDF text on printed pages 7, 11, 14, 16 and 21 was compared. The corrected constructions retain Theorem 1.1. Source-author confirmation and compiled correspondence are not claimed.

Section 3, including the improved volume-tail exponent of Corollary 1.4, and section 4's open problems remain unread beyond the introductory statements and the opening of section 3. Their full proofs are not supplied by this map. The existing weaker critical-tail theorem is preserved and is sufficient for the polynomial cutoff input already used in Part III.

The next dependency pass supplies the finite Gladkov theorem in [C7UK](../articles/adaptive-three-point.md#section-three-point), from a complete proof of adaptive BK and stopped DFS witness geometry. The existing countable extension remains unchanged. See the [decision-tree source map](sources/gladkov-decision-trees-2408.08457v1.md) for the proof boundary and two provisional source corrections. The same dependency pass also supplies the [higher-order product inequality](../articles/adaptive-three-point.md#section-higher-order) by stopping with one mark unvisited. The planar improvement, all-scale fictitious estimates and later hydrodynamics remain outside this proof.


## Reading update, 17 November 2026

Sections 3 and 4 have now been read in the same versioned HTML, superseding the earlier unread-work note. No additional PDF or journal comparison was performed in this pass.

[GW20](../articles/finite-set-hyperscaling.md#section-spatial-average-tail) proves a general spatial-average-to-volume-tail transfer. The required probability input is already written in [BYEO](../articles/stopped-exploration.md#section-endpoint-environments), including the constant in the source's Theorem3.1. The lattice action and finite edge-orbit rows are checked explicitly. The proof keeps the squared amplitude through Cauchy–Schwarz and closes a finite least-amplitude quadratic; it needs finite susceptibility, not an exponential tail, to start.

[QV5S](../articles/hierarchical-comparison.md#section-improved-volume-tail) combines this transfer with MRZO and sharpness, then passes to criticality through finite witnesses. This supplies Corollary1.4 and section3. Its square-root intensity prefactor implies the source's stated prefactor by27T8; this is an additional estimate, not an erratum. The final subcritical consequences reuse I328.

Section4 records research directions: matching spatial lower bounds (Problem4.1); a nonperturbative triangle estimate (4.3); pointwise and Fourier bounds (4.4–4.5); near-critical comparison (4.6); and universality (4.7). These are the source's questions, not assertions here about their current research status. Remark4.2 points to Bäumler–Berger; that paper's exact hypotheses remain a separate reading task. The new volume proof settles none of these questions.

All five existing provisional errata are unchanged. No new source fault was diagnosed. The source correspondence is still pending, and the proof additions assert no compiled association.


## Matching lower bounds: reading update

The previously separate Bäumler–Berger task is now treated in the [versioned reading map](sources/isoperimetric-2204.12410v2.md). PTM2/VVB0 give the box lower bound from a power-law upper envelope and a finite critical point. 0BJP combines it with MRZO for globally comparable kernels: internal and unrestricted box means have order n^alpha for alpha<1. At alpha=1<d their logarithmic exponent is one, with a logarithmic comparison gap retained. No pointwise lower bound or general localization result follows merely from this average.
