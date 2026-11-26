# Long-range II: initial reading map

Inspected [versioned HTML](https://arxiv.org/html/2508.18808v1), 15 November 2026.
Selected [PDF text](https://arxiv.org/pdf/2508.18808v1) also inspected, 15 November 2026: pp. 3 and 8–11. Its title date is 27 August 2025; the HTML displays 24 August 2026. Full rendition equivalence and full-paper coverage remain unverified. Locators are not assertion tags.

| Locators | Topic | Wiki disposition |
| --- | --- | --- |
| PDF pp. 3, 8–9; §II.1.1 | Kernel and cutoff conventions | Compare [soft cutoff](../articles/spatial-cutoff-moments.md) |
| PDF pp. 10–11; Definition II.1.3, Theorems II.1.5/II.1.7 | Localization/two-point source candidates | [Quoted scope](../articles/cutoff-localization.md#section-quoted-regimes); correspondence unreviewed |
| §II.4.1; Lemma II.4.4 | Localization | [Conditional criterion](../articles/cutoff-localization.md); model proof outstanding |
| §II.4.2–II.4.3 | Hydrodynamics | [Conditional all-scale argument](../articles/cutoff-hydrodynamics.md#section-all-scales); model inputs outstanding |
| II.5.3–II.5.6 | Mesoscopic mass | [Conditional synthesis](../articles/mesoscopic-tail-transfer.md#section-power-law-criterion); localization and damping remain inputs |
| II.5.8; (II.5.10) | Tail comparison | [Explicit sufficient transfer](../articles/mesoscopic-tail-transfer.md#section-transfer) |
| §II.5.3; Proposition II.5.9, Lemma II.5.11 | Multipoint lower bound | [Cluster extension and local-mass persistence](../articles/multipoint-trees.md#section-cluster-extension), followed by [separated-scale joining](../articles/multipoint-trees.md#section-long-range-gluing); full model-input correspondence remains open |

The introduction to §II.1.2 includes a discontinuous endpoint at alpha=d.
Our fractional-tail transfer instead assumes alpha<d. Do not erase that distinction.
Earlier chapters, the general-kernel application of higher-point geometry, slightly subcritical results, references and
unnumbered arguments still need correspondence work. This map is not a claim of
formalization or a substitute for the paper's hypotheses.

The §II.5.3 HTML proof was read on 15 November 2026. Its displayed tower identity has mismatched intersection ranges in its first equality; [the provisional erratum](../errata/hutchcroft-lrp-2.json) records the correction and its formalization consequence. The corrected recurrence keeps all mass events and adds one joining event at a time. No failure of Proposition II.5.9 is asserted.


## Correlation-length proof inputs, 16 November 2026

The [PDF text](https://arxiv.org/pdf/2508.18808v1), printed pp. 18–23, and the corresponding [HTML §II.2](https://arxiv.org/html/2508.18808v1#S2) have now been read through the random-box argument. The earlier map remains a record of its narrower pass. This extension does not claim full-paper coverage.

| Passage | Input or deduction | Wiki treatment |
| --- | --- | --- |
| Lemma II.2.1; Definition II.2.2 | All finite correlation-length moments versus rapid pointwise cutoff decay | [AUAE](../articles/cutoff-localization.md#section-pointwise) makes the common decreasing envelope and its quantifiers explicit. |
| (II.2.2); Lemma II.2.3 | Lower cutoff susceptibility comes from Part I; one spatial moment plus the averaged bound gives the matching upper order | Lower bound retained as an input. The averaged theorem is distinct from a pointwise theorem. |
| Corollary II.2.4 | Localization excludes alpha>d; alpha=d forces critical percolation | Endpoint scope retained; no continuous-transition assumption is inserted. |
| Proposition II.2.5 | Russo/BK derivative bound, spatial tail summation and an initial exponential cutoff estimate | AUAE retains local absolute continuity and the derivative inequality as hypotheses. At alpha=d use probability at most one for large cutoffs; the divergent integral is recorded as a provisional proof-boundary erratum. |
| Lemma II.2.6; converse in Lemma II.2.1 | Rapid decay controls every spatial moment | Shell summation divided by the cutoff susceptibility lower bound. |
| Lemma II.2.8; Proposition II.2.7 | Averaged exit weight produces a good box; disjoint exits preserve the final pointwise factor | [YUHF](../articles/cutoff-localization.md#section-random-boxes) supplies the proof. Its exit sum uses opening probabilities, bounded by the paper's intensity weights. |

The pointwise input is independently cited in Part II as [51, Theorem 1.4]: [arXiv:2404.07276v1](https://arxiv.org/html/2404.07276v1), whose statement was inspected. It assumes a symmetric summable translation-invariant kernel with two-sided power-law bounds and alpha<1. Part II's averaged input [55] is a different paper, [Sharp hierarchical upper bounds](https://doi.org/10.1063/5.0088450). Neither external proof is supplied merely by the random-box calculation. The derivative inequality, initial cutoff decay and Part I susceptibility estimate must likewise be matched before certifying the full source application.

A separate PDF text check on printed p. 55 confirms the intersection mismatch already recorded for Proposition II.5.9. Its existing [erratum](../errata/hutchcroft-lrp-2.json) retains the correction, tags, Lean-impact description and provisional status. The new alpha=d entry also awaits author confirmation. No visual PDF comparison, compiled association or independent correspondence verdict is inferred.


## Higher-point geometry, 16 November 2026

The full text of HTML §II.3 was read, with targeted PDF text comparisons on printed pp. 29–31. Figures and the external decision-tree theorem were not visually or independently verified in this pass. The earlier exposition is preserved; the following table records its relationship to this source.

| Source passage | Argument | Wiki disposition |
| --- | --- | --- |
| Theorem II.3.1; Remarks II.3.2–II.3.3 | Higher-order inequality via two continuations of a stopped depth-first search | Uses Gladkov's decision-tree BK theorem, not ordinary disjoint occurrence in a single configuration. Retained as the explicit input to C4A5 and 2GTM. The smaller constant at the end of the proof implies the stated larger constant. |
| (II.3.1)–(II.3.2) | Four-point matching expression | [2GTM](../articles/multipoint-trees.md#section-four-point) supplies the algebra, including the maximum over matchings and zero probabilities. |
| (II.3.3) | Recursive multigraph expansion | [L3HA](../articles/multipoint-trees.md#section-regular-multigraphs) now proves the algebra: integer powers balance degree 2^(n-2), the overlapping pairwise unions ensure connectivity, and finite graph counts absorb multiplicities. |
| Corollary II.3.4 | Power-law pair bound propagated through the three-part recursion | [C4A5](../articles/multipoint-trees.md#section-recursive-geometry) retains positivity of the decay exponent; the lattice nonpositive-exponent case is trivial. |
| Definition II.3.5; (II.3.6); Lemma II.3.6 | Sweep, spread and insertion products | [CS13](../articles/multipoint-trees.md#section-sweep) retains the root diameter; [0VKF](../articles/multipoint-trees.md#section-spread) proves both comparisons with explicit cardinality constants in every finite metric space. |
| Lemma II.3.7; (II.3.7)–(II.3.8) | Sweep compared with the recursive distance quantity | [ESZG/WDGK](../articles/multipoint-trees.md#section-sweep) give an independent ultrametric proof. The source insertion product must use strictly earlier points. |
| Corollary II.3.8 | Geometric probability bound | C4A5 and WDGK give the conditional conclusion; the intermediate raw-product exponent needs its additional factor one half. |
| Proposition II.3.9 | Möbius covariance of the recursive quantity | [9YE6](../articles/multipoint-trees.md#section-recursive-geometry) proves the recursion rule; N76U supplies the distance identity with finite final endpoints. Keep signed determinant separate from absolute Jacobian. |

Three local formula corrections are recorded in the [provisional errata](../errata/hutchcroft-lrp-2.json): the self-distance in (II.3.8), the intermediate exponent in Corollary II.3.8, and the inversion conventions in Proposition II.3.9. The corrected arguments retain their stated conclusions. These text comparisons do not certify the external decision-tree input, the underlying decision-tree proof, full source correspondence or a Lean implementation.


## Volume moments and weak localization, 16 November 2026

HTML §II.4.1 was read through its final largest-cluster argument. PDF text comparisons cover the moment summation and second-moment barrier on printed pp. 33–37. This is a text check, not visual PDF verification.

| Passage | Wiki argument | Remaining input |
| --- | --- | --- |
| Lemma II.4.6; (II.4.2)–(II.4.4) | [1EWL](../articles/multipoint-trees.md#section-multigraph-moments): connected elimination, positive fractional exponents, path decomposition of the spatial weight, and repeated-position partitions | Higher-point inequality and a common rapidly decaying two-point envelope |
| Lemma II.4.7; (II.4.5)–(II.4.7) | 1EWL proves the third-moment ratio by translation of rooted tuples and Cauchy–Schwarz | The same four-point input; no general nonunimodular conclusion |
| Theorem II.4.3; Lemma II.4.4 | [SOHR](../articles/cutoff-localization.md#section-low-dimensional-moments): truncated Harris bound, absolutely continuous barrier, size bias and spatial tail summation | Russo/mass-transport derivative identity, its regularity and the sharp Part I susceptibility coefficient |
| Theorem II.4.2 under CL; (II.4.16) | Source deduction inspected: compare localized second and first moments to the largest-cluster scale | Universal tightness moment comparison and the averaged largest-cluster upper bound remain separate |

The graph ordering omitted before applying the positive-exponent row estimate is recorded in the [provisional errata](../errata/hutchcroft-lrp-2.json). The repair also handles nonadjacent marked pairs in the weighted sum. The source conclusions are preserved. SOHR uses the strict gap d<3 alpha and does not assert the critical-dimensional endpoint. No source-author confirmation, independent correspondence review or compiled association is inferred.


## Differential errors and all-scale quantiles, 16 November 2026

HTML §§II.4.2–II.4.3 were read through the all-scale proof, with PDF text comparisons on printed pp. 38–42 and a check of the kernel normalization in §II.1.1. The source proof now has the following explicit components in the wiki.

| Passage | Wiki component | Scope |
| --- | --- | --- |
| (II.4.8)–(II.4.10) | [1AC7](../articles/harris-inequality.md#section-finite-cluster-gap) | Conditions on an almost surely finite first cluster; the unrestricted correlation theorem remains separate. |
| (II.4.17)–(II.4.19) | [GG8B](../articles/cutoff-hydrodynamics.md#section-exact-cutoff-equations) | Derives the identities from mixed Russo and mass transport under local rate bounds and finite cutoff susceptibility. |
| Lemmas II.4.9–II.4.11; Proposition II.4.8 | [A3G0](../articles/cutoff-hydrodynamics.md#section-localization-errors), together with XB1X | Localized second, third and fourth moments plus rooted damping supply the two error bounds. First-moment asymptotics and regular variation under Hydro follow from the existing ODE argument. |
| (II.4.26)–(II.4.28); Theorem II.4.2 | LQ6Y, YEVN, NS0Q and A3G0 | Quantile lower moments, a last good scale and the strict exponent gap give the bound at every sufficiently large radius. Quantile continuity is unnecessary. |

The exact coefficient in (II.4.27) is a [provisional erratum](../errata/hutchcroft-lrp-2.json): the pure power replaces the kernel derivative before the asymptotic step. Retaining that derivative preserves the following argument. The susceptibility order, rooted universal damping and source-level correspondence remain obligations; this extension does not infer them from wCL. No public-repository transfer, compiled association or author confirmation is involved.


## Closing the window-moment implications, 16 November 2026

[79SD](../articles/cutoff-localization.md#section-weak-first-moment) proves the first-moment comparison and dimension endpoint in Lemma II.4.9 / Corollary II.4.10, retaining divergence and the averaged full-law bound as premises. [AS7A](../articles/cutoff-hydrodynamics.md#section-window-scaling) proves the recentered window-moment argument of Corollary II.4.12, read in the HTML through the end of §II.4. The lower bound uses the cutoff at half scale; the upper bound uses the full-law quantile. Only localized orders transfer to full cutoff moments.

The [source assembly](../articles/cutoff-hydrodynamics.md#section-source-assembly) identifies the pre-existing general hierarchy 09EI, collision identity 6H7C, deficit bounds NJF3 and localized ratios 0WAE. It also connects the universal rooted-damping proof already supplied in the window-tightness article. Thus damping is not an unproved external step for these independent-bond applications, although the conditional analytic statements retain it as a reusable premise. This informal proof connection is separate from compiled tag correspondence. Full source applications still require the averaged critical bound, divergent cutoff susceptibility and the specified localization hypothesis.


## Mesoscopic truncations and annular mass, 16 November 2026

The HTML statements and proofs in §§II.5.1–II.5.2 were read, with targeted PDF text checks on printed pp. 47–52. Theorem II.5.2's small-volume quantifier was also checked in the HTML and on PDF p. 46. These are text comparisons, not a visual PDF review.

| Passage | Wiki treatment | Scope |
| --- | --- | --- |
| Lemmas II.5.4–II.5.6 | D7A5, OP4X and 6H7C, with the [source reconciliation](../articles/mesoscopic-tail-transfer.md#section-fixed-truncation-source) | Fixed truncation, exact derivative rate and sufficiently large propagation radii |
| Proposition II.5.3 | KKGL | One excessive radius creates a fixed-truncation interval with excessive second-moment growth; no uncontrolled epsilon-dependent comparison constant |
| Theorem II.5.7 and Proposition II.5.8 | ZWQ3 and the existing cutoff criterion | Positive fractional tail exponent; the discontinuous endpoint is separate |
| Theorem II.5.2(1) | [SOG8](../articles/mesoscopic-tail-transfer.md#section-small-window-mass) | Direct tail integration, explicit delta power and rho=0 included |
| Theorem II.5.2(2), (II.5.8)–(II.5.13) | [L6K3](../articles/mesoscopic-tail-transfer.md#section-annular-mass) and [ghost-deficit discussion](../articles/mesoscopic-tail-transfer.md#section-ghost-deficit-scope) | Independent added layer, fractional full tail and arbitrarily small cutoff spatial tails; uniform integer n>=3, alpha<d |

Four provisional entries record the propagation normalization/radius scope, the final truncation comparison, the small-window proof displays, and the annular statement/proof scope. The source's all-n annular quantifier has an isolated-root obstruction in the actual summable-intensity model. At alpha=d only the intermediate outside-mass bound is ruled out by positive infinite-cluster probability; no counterexample to a large-n annular statement is claimed. Each entry identifies its workaround and the corresponding obligations for Lean. All await Tom's confirmation; no compiled association is inferred.


## Susceptibility and localization below criticality, 16 November 2026

The HTML proofs of Lemma II.6.1 and Proposition II.6.2 were read and compared with PDF text on printed pp. 56–58. [04ZI](../articles/cutoff-localization.md#section-subcritical-susceptibility) keeps the full susceptibility in the reciprocal bound, including the infinite case. [KA3B](../articles/cutoff-localization.md#section-subcritical-spatial) derives the countable spatial derivative with the correctly centered joining ball. The estimate of the pth power of three lengths gives the required differential inequality directly, without induction on p, and the proof makes its constants uniform in beta.

The hypotheses retain critical cutoff susceptibility and spatial upper bounds, monotone cutoff convergence and the uniform derivative rate. Spatial tails and the lower local mean up to the susceptibility scale follow. These inputs alone are not presented as a complete two-point crossover theorem: the far-field derivative integration and the joining-edge lower estimate remain separate. One provisional erratum groups the dummy-radius, ball-center and forcing-constant display corrections; it records the corresponding formal obligations without changing a pre-existing tagged statement.


## Two-point crossover, 16 November 2026

The statements and proofs of Lemmas II.6.3–II.6.5 and the conclusions of Theorems II.1.7/II.1.14 were read in the versioned HTML and compared with PDF text on printed pp. 58–61. This is a text comparison, not visual PDF review. The proof in the wiki is conditional on its listed derivative, localization, window-moment and higher-Gladkov inputs; source inspection does not certify that every source formulation has the same hypotheses.

| Passage | Wiki treatment | Scope |
| --- | --- | --- |
| Lemma II.6.3 | [TFKR](../articles/cutoff-localization.md#section-two-point-upper) | Correct two-point factors; R<=8xi separated before integration; finite and infinite full susceptibility |
| Lemma II.6.5 | [9ZEL](../articles/multipoint-trees.md#section-separated-window-mass) | Distinct window centers, maximum over matching estimates, repeated marked vertices and regularized short distances |
| Lemma II.6.4, (II.6.3)–(II.6.5) | [NI07](../articles/cutoff-localization.md#section-two-point-lower) | Uniform beta bounded away from zero; independent added bonds; disjoint-cluster factorial second moment; direct-bond case when the chosen radius is below one |
| Theorems II.1.7 and II.1.14 | Combined conditional upper/lower route | The source's identification of its model assumptions with all displayed inputs remains distinct from the implication proved here |

Two provisional entries record the upper-proof indices/range and the lower-proof window/radius scope. The lower proof uses the rapid-decay overlap estimate directly, without assuming it is bounded by a multiple of the actual cutoff two-point probability. The old statements, tags and entries are preserved, and all diagnoses await Tom's confirmation. The next unrecorded passage is the volume-distribution argument in section II.6.2; dependencies on Parts I and III require their own pinned readings.


## Subcritical volume distribution, 16 November 2026

Section II.6.2 was read through the end of the proof of Theorem II.1.15 in the versioned HTML and compared with PDF text on printed pp. 61–64. The theorem statement in section II.1.3 was also checked. The wiki supplies the following conditional implications without promoting the paper's cross-volume inputs to proved assertions.

| Passage | Wiki treatment | Retained obligations |
| --- | --- | --- |
| Lemma II.6.6; (II.6.6), (II.6.8) and (II.6.9) | Critical cutoff moments, critical tail and susceptibility/volume-scale relation are explicit premises | The low-dimensional route uses Part II Theorem II.4.3 and Lemma II.4.6; the high- and critical-dimensional routes cite Part I Theorem I.1.6 and Part III Theorem III.1.2, with the alternatives I.1.15 and III.1.11 mentioned for moment comparability. Their hypotheses need separate pinned readings. |
| Lemma II.6.7 | [T5JS](../articles/cutoff-scaling.md#section-subcritical-moment-upper) | Cutoff derivative hierarchy, local absolute continuity and initial critical moment comparison; the highest-order summand is absorbed before induction |
| Theorem II.1.15, second-moment lower bound | [XANO](../articles/cutoff-scaling.md#section-subcritical-volume-tail) | Monotone cap in place of truncation; exact tail integral; positive power 1-rho, including rho=0; bounded logarithms regularized |
| Theorem II.1.15, volume tails and (II.6.11) | XANO and [IK5Y](../articles/cutoff-scaling.md#section-moment-continuity) | Uniform higher moments give rapid decay but no exponential rate; the lower proof uses size bias, moment continuity and a separate bounded-threshold case |

One provisional entry records the invalid truncation comparison and tail-sum identification, together with a cap-based repair. The elementary counterexample concerns those general probability inferences, not the percolation theorem. The conditional argument through section II.6.2 is now recorded. Identifying every critical input across Parts I–III with the same model, cutoff and normalization remains separate source-reconciliation work, and all diagnoses await Tom's confirmation.


The cross-volume statement comparison has now been carried out at the same v1 pins: [Part I](sources/long-range-I-2508.18807v1.md) and [Part III](sources/long-range-III-2508.18809v1.md). The [article's input table](../articles/cutoff-scaling.md#section-volume-inputs) records the common soft cutoff and separates critical moment comparability, the precise critical logarithm and the full critical tail. In low dimension the two-sided ratio needs Theorem II.4.3, not Lemma II.4.6 alone. Across all three regimes, substitution verifies X comparable to Z times the critical tail at Z. This closes the notation and scale comparison; it does not discharge the model-specific derivative, hydrodynamic or second-order inputs.

## The higher-order probability input, 16 November 2026

Re-read Theorem II.3.1, Remarks II.3.2–II.3.3 and the complete proof through its final display in the versioned HTML. No additional PDF comparison is claimed. [9KP0](../articles/adaptive-three-point.md#section-many-witnesses) supplies the nontrivial marked partition, including attachments at either endpoint of the active DFS path. [5BQO](../articles/adaptive-three-point.md#section-higher-order) proves the sum bound and the stronger coefficient 2(n-1)^2(2^(n-2)-1) at the end of the source proof, then passes to countable models. This implies its stated coefficient four. [MTVN](../articles/adaptive-three-point.md#section-four-point) gives the resulting four-point matching bound with prefactor 186624. The earlier statements and constants are retained. The higher-order inequality is no longer an unproved probability input to the linked geometric and localization arguments; their other hypotheses remain as stated.


## The pointwise upper input,17November2026

The earlier cited pointwise input now has a [written upper-bound proof](../articles/pointwise-long-range.md#section-critical), with its own [source map](sources/pointwise-2404.07276v1.md). TGF9 follows from translated-box exits, the analytic contraction PIZX and the already proved averaged upper bound MRZO. It therefore supplies YUHF's pointwise upper hypothesis without using (CL). The cutoff susceptibility lower bound remains separate. The pointwise lower half, near-critical source theorem and all model-specific correspondence checks are not inferred from this update.
