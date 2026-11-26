# Long-range III: main results and initial dependency map

Inspected selected passages of [arXiv:2508.18809v1 HTML](https://arxiv.org/html/2508.18809v1) and [PDF text](https://arxiv.org/pdf/2508.18809v1), 16 November 2026: the introduction and §III.2.1, together with the statements of §III.2.2. The PDF has 105 pages and a title date of 27 August 2025; the HTML displays 24 August 2026. The two renditions have not been compared throughout. Printed PDF page numbers below are locators, not assertion tags.

## Scope of the comparison

The model assumptions are in §III.1.1, especially (III.1.4): a radial decreasing differentiable kernel with logarithmically integrable relative derivative error. Theorems III.1.2, III.1.6 and III.1.8 assume d = 3α < 6; Theorem III.1.11 assumes d = 3α. Do not transfer the former results to nearest-neighbour percolation in dimension six.

The table separates what was read from what our articles establish. A link records a useful comparison, not an identification of statements, a proof of the source theorem or a compiled correspondence.

| Source locator | Topic | Existing exposition and remaining work |
| --- | --- | --- |
| Theorem III.1.2 | Critical volume tail, with logarithmic exponent 1/4 | [Power-log transfer](../articles/marginal-ode.md#section-tail) proves an analytic implication under explicit moment and comparison inputs. Those inputs still have to be established in the critical-dimensional model. |
| Theorem III.1.6 | Integrated stable-superprocess limit | [Cutoff removal](../articles/size-biased-laws.md#section-cutoff-removal) and [moment identification](../articles/size-biased-laws.md#section-local-moment-identification) provide conditional measure-theoretic steps. They do not supply the critical model's spatial diagrams or identify its normalization constants. |
| Theorem III.1.8, PDF p. 9 | Two- and three-point functions; three distinct points | [Tree bounds](../articles/multipoint-trees.md#section-multipoint) and [the product inequality](../articles/multipoint-trees.md#section-gladkov) do not establish the logarithmic improvement. Our [separated-scale joining argument](../articles/multipoint-trees.md#section-long-range-gluing) retains its stated geometric inputs. |
| Theorem III.1.11 and Remark III.1.12, PDF p. 12 | Hydrodynamics; proposed quantitative rate remains conjectural | [The definition](../articles/cutoff-hydrodynamics.md#section-scale) uses full-cluster intersections with a finite window. The article's subsequent contradiction proves failure of hydrodynamics below 3α under moment equations; it does not prove the critical-dimensional theorem. |
| §III.1.3, PDF pp. 13–16 | Proof overview | The existing [slowly varying moment hierarchy](../articles/marginal-ode.md#section-slow-moments) keeps its differential errors as inputs. A scalar ODE argument does not verify their probabilistic bounds. |
| §III.2.1, (III.2.1)–(III.2.4), PDF pp. 16–17 | Moment and susceptibility-derivative bounds | Compare [cluster moments](../articles/multipoint-trees.md#section-moments) and [finite-volume differentiation](../articles/integrated-susceptibility.md#section-finite-derivative). Preserve the latter's closed-pivotal convention and its separate limiting argument. |
| Lemmas III.2.1–III.2.2, PDF pp. 17–20 | Complementary derivative inequalities | [The exploration score](../articles/stopped-exploration.md#section-score) gives a locally Lipschitz, almost-everywhere derivative bound for positive intensity, with finite integer truncation first. Its untruncated result assumes a finite second moment on an open interval. [Four mean-field conditions](../articles/integrated-lower-tails.md#section-four-conditions) retain their endpoint hypotheses and are not a literal transcription of these source statements. |
| §III.2.2, Lemmas III.2.4–III.2.5, PDF pp. 20–21 | Chemical-distance comparisons | [Intrinsic geometry](../articles/intrinsic-geometry.md#section-distance) fixes the distance convention but does not prove the entire equivalence here. Chemical distance must not be replaced by a count of pivotal edges. The existing backbone occurrence remains separate; reverse BK is still FIXER's issue. |

## Remaining reading and correspondence

The contents and introductory outline identify the next passages to inspect: §III.3 (p. 23), §III.4 (p. 47), §III.5 (p. 69) and §III.6 (p. 76). Their proofs have not been audited in this map. Bibliographic dependencies, unnumbered arguments and the remainder of §III.2.2 also remain.

For the next pass, first record the precise model inputs that our conditional articles lack; then compare each with its source proof. Do not extend the [high-dimensional polynomial moment result](../articles/spatial-cutoff-moments.md) to equality d = 3α, or count an analytic consequence twice as both an input and its verification. The [existing backbone occurrence](../articles/backbone-connections.md#section-moment-lower) is preserved without assigning a second occurrence to an unrelated assertion.

No assertion tag, source verdict or formal status is allocated by this reading map. Any source fault confirmed during further comparison belongs in the existing errata workflow, with a precise rendition and locator and a provisional status until Tom confirms it.


## Inputs to the subcritical volume argument, 16 November 2026

Rechecked the versioned HTML at III.1.1–III.1.3, especially the common kernel and cutoff assumptions, Theorem III.1.11, and (III.1.16)–(III.1.19). PDF text was also checked at the kernel assumptions (p. 5) and inverse-log calculation (p. 15), alongside the earlier introductory reading recorded above.

Theorem III.1.11 supplies hydrodynamics at d=3 alpha. Together with Part I Theorem I.1.15 it supplies critical cutoff moment comparability; it does not determine the logarithmic factor. At d=3 alpha<6, the second-moment ratio in (III.1.18) is r^(2 alpha)/sqrt(log r), whereas Theorem III.1.2 gives the full n^(-1/2)(log n)^(1/4) tail. These are the distinct inputs used in the [subcritical volume proof](../articles/cutoff-scaling.md#section-volume-inputs). Matching the common norm, derivative normalization and soft cutoff is necessary before using them; reading their statements does not verify the hydrodynamic and second-order probabilistic estimates.

The prose between (III.1.18) and (III.1.19) has two logarithmic sign mismatches, also present in the PDF text. The [new source erratum](../errata/hutchcroft-lrp-3.json) records them provisionally. The [direct inversion](../articles/marginal-ode.md#section-inverse-log-source) preserves the final positive-quarter-power tail and its coefficient. No assertion that Theorem III.1.2 is false follows from this local repair. The substantive proof queue remains the probabilistic inputs in sections III.3–III.6, rather than a second copy of the scalar ODE calculation.


## Chemical distances, 16 November 2026

Read the proof of section III.2.2 in full in the versioned HTML and compared its equations with PDF text on printed pp. 20–23. Also read the intrinsic-distance reduction at the start of the proof of Lemma III.6.18, through (III.6.39), on printed p. 99. This extends the initial statement-only reading; it is not a reading of all of section III.6.

| Passage | Wiki treatment | Scope |
| --- | --- | --- |
| Lemma III.2.4(1), (III.2.8) | [SBMG](../articles/intrinsic-geometry.md#section-distance-moments) | All integer distance moments by ordered marks on a shortest path and iterated BK; connected vertices only |
| Lemma III.2.4(3) | [NMYK](../articles/intrinsic-geometry.md#section-open-pivotal-rate) | Open-pivotal rate at every positive finite-susceptibility parameter; derivative identification on an open finite-susceptibility interval, with continuity justified |
| Lemma III.2.5, (III.2.9)–(III.2.10) | [OCMG](../articles/intrinsic-geometry.md#section-distance-derivative-lower) | Complete argument with the constant 64, the marked probability law, unqueried frontier, countable conditioning and distinct pivotal edges |
| Proof of Lemma III.6.18 through (III.6.39) | [T9LZ](../articles/intrinsic-geometry.md#section-negligible-distances) | Uniform contrapositive and interpolation; critical second-moment suppression and the score bound remain inputs |
| Lemma III.2.4(2) | Source read; no new wiki proof claimed | The geodesic-event/Reimer argument is separate from the increasing connection-event BK bounds proved here |
| Lemma III.6.18 after (III.6.39) and subsequent diagrams | Not supplied by this extension | Spatial weights, selected-geodesic normalization, spatial moment inputs and the diagram estimates need their own comparison |

The lower derivative proof defines candidate edges from the last intrinsic layer to the revealed exterior cluster. Earlier-layer edges to that cluster are already closed, whereas the last-layer edges have not been queried. It bounds their total weight by an edge-disjoint witness sum without identifying that sum with a shortest path or a pivotal count. No new source fault or author confirmation is claimed. The existing provisional erratum and reverse-BK ownership are unchanged.


## The first good-scale argument, 16 November 2026

Read versioned HTML section III.3.1 through the proof of Corollary III.3.12, together with the preceding modified-family definition and outline. The two appended wiki proofs cover the selection and integration arguments below. This pass has not compared the entire subsection with the PDF and does not establish its model inputs merely by citing them.

| Passage | Treatment or remaining input |
| --- | --- |
| Modified family before Proposition III.3.1 | Both intensity and cutoff increase; the intensity derivative of beta_c(1-lambda r^(-alpha)) includes alpha. The lambda=0 family is kept separate. |
| Lemma III.3.5 | Polynomial cutoff moments are an input to [X57A](../articles/cutoff-hydrodynamics.md#section-good-scale-alternative). The source reduces them to critical volume tails and off-critical susceptibility control; source-normalization and endpoint application remain to be reconciled. |
| Dyadic counting after Lemma III.3.5 | X57A proves simultaneous doubling for four functions by summing logarithmic increments in four residue classes. It does not infer every-scale doubling. |
| Lemma III.3.6 and (III.3.1) | The spatial-cutoff derivative, Harris separation and Gladkov mixed-window estimate are the route to the capped derivative input. The source proof has been read; no unconditional new model theorem is asserted here. |
| Proposition III.3.7 | Compare [F75G](../articles/integrated-lower-tails.md#section-family), which keeps continuity and the range of the susceptibility explicit. The full off-critical finite-threshold statement remains to be reconciled. |
| Lemmas III.3.8–III.3.9 and Corollary III.3.10 | X57A assumes eventual reverse doubling and the capped integral estimate in the range d>=3 alpha. Bounded-radius endpoints and the wider range printed for Corollary III.3.10 are not inferred from the preceding lemma's narrower range. |
| Lemma III.3.11, (III.3.7)–(III.3.12) | X57A supplies the monotone radius, retained first moment, composed doubling and the whole-interval alternative, including equality d=3 alpha. The two tree-graph moment bounds remain explicit hypotheses. |
| Proof of Lemma III.3.4 | [1BO9](../articles/cutoff-hydrodynamics.md#section-good-scale-susceptibility) proves the analytic implication from the two derivative inequalities. A separate small-susceptibility case justifies absorption of the linear error. The lambda factor is unnecessary on intervals with the third-moment bound. |
| Corollary III.3.12 | [AGX4](../articles/cutoff-hydrodynamics.md#section-modified-reciprocal) now supplies the reciprocal comparison and finiteness implication under explicit uniform derivative and good-interval hypotheses. |

The input family may vary with lambda, but a common set of polynomial exponents and common constants in the displayed premises are required for the wiki's uniform conclusion. None of these arguments proves the model's critical-dimensional second-moment suppression, all-scale fictitious estimates, or final hydrodynamic contradiction. Those remain the next substantive source obligations. No erratum is promoted or newly established by this conditional treatment.


The chain-rule display in the proof of Lemma III.3.4 and the reciprocal display in Corollary III.3.12 were subsequently compared with PDF text on printed p. 33, and the final finiteness argument was read through p. 34. [Two provisional entries](../errata/hutchcroft-lrp-3.json) record the missing alpha and the reciprocal denominator/integration variable. These are local calculus corrections with the same intended conclusions. AGX4 supplies the complete reciprocal implication, including a separate lambda=0 case. The preceding whole-subsection PDF comparison limitation still applies.


## Model inputs for the good-scale argument, 16 November 2026

Re-read the versioned HTML proofs of Lemmas III.3.5–III.3.9, Proposition III.3.7, equation (III.3.1), and Corollary III.3.10. This pass follows the mathematical dependencies rather than assuming the earlier conditional statements already apply to the model. No additional whole-subsection PDF comparison is claimed.

| Passage | New proof and exact scope |
| --- | --- |
| Lemma III.3.5 | [I328](../articles/stopped-exploration.md#section-polynomial-tail) converts the critical polynomial tail into polynomial off-critical susceptibility; [DR1W](../articles/cutoff-hydrodynamics.md#section-polynomial-cutoff) proves the actual radial cutoff domination and all moment bounds. |
| Proposition III.3.7 | [XU1Y](../articles/integrated-lower-tails.md#section-offcritical-cap) covers real caps and infinite susceptibility, using continuity only while susceptibility is finite. |
| Equation (III.3.1) | [BIXQ](../articles/multipoint-trees.md#section-gladkov-window) proves the mixed-window summation from the cited finite Gladkov theorem. |
| Lemma III.3.6 | [KPBJ](../articles/cutoff-hydrodynamics.md#section-capped-cutoff-derivative) proves the derivative error estimate with the sharp critical spatial-window bound explicit. The weaker average in KXV3 is insufficient for that premise. |
| Lemma III.3.8 | [C0OR](../articles/cutoff-hydrodynamics.md#section-modified-lower) includes the normalization of the unit ball and a direct derivative of the modified kernel; the uniform lower bound follows from the reciprocal integral. |
| Lemma III.3.9 and Corollary III.3.10 | [N3OC](../articles/cutoff-hydrodynamics.md#section-model-reverse-doubling) gives uniform eventual reverse doubling and the capped integral for d >= 3 alpha. All-radius endpoints and the corollary's wider printed range are not claimed. |
| Mixed tree bound in Lemma III.3.11 | [9WYX](../articles/multipoint-trees.md#section-mixed-third-moment) supplies m3 <= 3 chi^2 m2 by retaining a three-point event in the four-mark BK decomposition. |
| Intensity derivative in Lemma III.3.4 | [VW2E](../articles/stopped-exploration.md#section-moment-derivative-lower) sums the ghost-tail differential inequality; the linear error and positive-intensity domain remain explicit. |

The [model assembly](../articles/cutoff-hydrodynamics.md#section-model-good-scales) now proves the good-scale susceptibility conclusion from the sharp critical window bound and the cited finite Gladkov theorem. Polynomial moments, mixed tree moments, modified susceptibility growth, reverse doubling, and the capped integral are no longer separate unverified model premises in that assembly. The sharp critical window theorem, the finite Gladkov theorem, and the all-scale and hydrodynamic arguments in sections III.3.2–III.6 remain substantive obligations. This extends, rather than silently rewrites, the earlier conditional treatment. No erratum status or source-author confirmation changes.


The next dependency pass supplies the sharp critical spatial-window estimate through [MRZO](../articles/hierarchical-comparison.md#section-full-space). The [2022 source map](sources/sharp-hierarchical-upper-2202.07634v2.md) records the full section 2 reading, its proof decomposition and five provisional local corrections. The positive radial kernel meets its all-displacement lower envelope by norm equivalence and a finite small-displacement check. This removes the window premise as an outstanding model obligation in X8F6, while retaining the finite Gladkov theorem and the all-scale/hydrodynamic work as separate obligations.

The next dependency pass supplies the finite Gladkov theorem in [C7UK](../articles/adaptive-three-point.md#section-three-point), from a complete proof of adaptive BK and stopped DFS witness geometry. The existing countable extension remains unchanged. See the [decision-tree source map](sources/gladkov-decision-trees-2408.08457v1.md) for the proof boundary and two provisional source corrections. The same dependency pass also supplies the [higher-order product inequality](../articles/adaptive-three-point.md#section-higher-order) by stopping with one mark unvisited. The planar improvement, all-scale fictitious estimates and later hydrodynamics remain outside this proof.

## Derivative transport and simultaneous scales, 16 November 2026

Read the modified-condition definitions at the start of section III.3 and section III.3.2 through the proof of Lemma III.3.16 in the versioned HTML. Compared the three corrected passages below with PDF text on printed pp. 35–37. The full proof of Lemma III.3.17 and the subsequent all-scale susceptibility argument remain to be completed.

| Source passage | Wiki proof and scope |
| --- | --- |
| Section III.3, modified hydrodynamic condition | [CXTO](../articles/cutoff-hydrodynamics.md#section-modified-quantiles) distinguishes the inclusive observation ball, proper neighbours in the derivative, the positive-parameter condition and its ordinary zero-parameter counterpart. |
| Equation (III.3.14) | [7QDN](../articles/cutoff-hydrodynamics.md#section-mixed-window-quantile) derives the mixed moment by Cauchy–Schwarz, rooted damping, the fourth-moment tree bound and the sharp window estimate. |
| Equation (III.3.15) | [5FCO](../articles/integrated-susceptibility.md#section-two-cluster-transport) gives the independent-layer transport of two distinct clusters, with the outside continuation endpoints retained. Countable passage uses dominated convergence, since the distinct-cluster indicator is not monotone under exhaustion. |
| Lemma III.3.15 | [1AQ4](../articles/cutoff-hydrodynamics.md#section-cutoff-derivative-transport) proves the increment-row bound and transports the normalized intensity derivative to a smaller cutoff. |
| Lemma III.3.14 | [0HMO](../articles/cutoff-hydrodynamics.md#section-synchronized-scales) finds simultaneous low-susceptibility and large-quantile scales using an absolutely continuous band-crossing argument. It needs no continuity of the quantile or attained last scale. |
| Lemma III.3.16 | [SQGG](../articles/cutoff-hydrodynamics.md#section-fictitious-derivative) proves the all-scale derivative lower bound with an explicit lower-order error. For positive lambda its initial lower-limit factor is lambda^(12). |

The last two results retain failure of the modified hydrodynamic condition as an explicit counterfactual hypothesis. They do not yet prove the uniform derivative lower bound or the susceptibility upper bound in Proposition III.3.13. Three appended [provisional errata](../errata/hutchcroft-lrp-3.json) concern the last-quantile-scale definition and limsup, the exit endpoints and increment summation indices, and the sign of the twelfth power of lambda. Existing entries, statements and article bodies are preserved; no source-author confirmation or compiled association is inferred.

## Completing the all-scale susceptibility argument

Read the remaining proof of Lemma III.3.17, Lemma III.3.18 and the proof of Proposition III.3.13 in the versioned HTML. The cap-radius display in the last proof was also compared with PDF text on printed p. 40; a whole-subsection PDF comparison is not claimed.

[X9SE](../articles/cutoff-hydrodynamics.md#section-fictitious-polynomial) bounds gaps between good dyadic scales by a constant times log(2/lambda). Its counting keeps four overlapping dyadic increments for each of four monotone functions; enlarging the fixed doubling threshold absorbs the resulting factor sixteen. [0NU2](../articles/cutoff-hydrodynamics.md#section-fictitious-critical-cap) then fixes one small positive lambda to integrate the capped reciprocal up to the critical intensity. This does not assume a radius threshold uniform in lambda.

[BTM3](../articles/cutoff-hydrodynamics.md#section-fictitious-moment-orders) proves the sharp susceptibility and second-moment orders at every radius at least one, and the uniform derivative lower bound beyond a common large radius. A small cutoff can have no positive bonds, so no positive derivative lower bound is asserted there. The source's cap substitution needs the radius exponent alpha, not twice alpha; the appended entry is provisional. Failure of the modified hydrodynamic condition remains the explicit counterfactual assumption throughout. The mesoscopic conclusions beginning at III.3.19 and the final hydrodynamic contradiction remain unfinished.

## Critical-dimensional mesoscopic negligibility

Read section III.3.3 in the versioned HTML, from Lemma III.3.19 through the proof of Lemma III.3.20, and re-read the bounded-cap derivative statement of Lemma III.2.2. Selected PDF text for the unbiasing, selected-radius and Riccati formulas on printed pp. 41–45 was compared; this is not a comparison of every line of the subsection.

| Passage | Wiki treatment |
| --- | --- |
| Lemma III.2.2; (III.3.26)–(III.3.27) | [89T0](../articles/stopped-exploration.md#section-real-cap-score) extends the existing integer-cap score estimate to every positive real cap, with a harmless factor sqrt(2). Integrated passage proves the modified-path inequality without an assumed infinite-model chain rule. |
| Lemma III.3.21 | [2Z34](../articles/mesoscopic-tail-transfer.md#section-fictitious-lower-tail) retains the same event when removing size bias, the biased mean in the square root, and a separate bounded-radius case. Continuity of the ratio suffices; monotonicity is not assumed. |
| Lemma III.3.22 | [2HXZ](../articles/mesoscopic-tail-transfer.md#section-fictitious-cap-deficit) supplies an eventual selected-scale estimate with a strict deficit. The law, normalization and moving cap use the selected radius; its smaller fixed cap may then be propagated. |
| Lemma III.3.23 | [19IN](../articles/mesoscopic-tail-transfer.md#section-riccati-linear-error) gives the corrected Riccati denominator for an absolutely continuous function and a linear error exponent strictly smaller than alpha. |
| Lemma III.3.19 | [Q7O9](../articles/mesoscopic-tail-transfer.md#section-fictitious-negligibility) proves negligibility at every radius. The cap is fixed while integrating, the target radius is arbitrary, and the last intensity comparison is made at that same cutoff. |
| Lemmas III.3.24–III.3.25 | [XHJ4](../articles/mesoscopic-tail-transfer.md#section-fictitious-cubic-moments) removes the parameter loss in the second moment, including the zero-parameter critical cutoff law. |
| Lemma III.3.20 | Read, but its full threshold range and cutoff-to-full tail comparison are not claimed by this extension. Uniform cubic moments directly give a lower tail only below half the biased mean; a constant multiple of the radius scale must not silently be replaced by coefficient one. |

The model assumptions and the counterfactual failure of modified hydrodynamics remain explicit. This completes the negligibility and cubic-moment portion, not the final contradiction or the full paper. The earlier low-dimensional negligibility theorem excludes this endpoint; the new score and deficit argument supplies the missing critical-dimensional mechanism. Three appended [provisional source entries](../errata/hutchcroft-lrp-3.json) record local formula corrections. Every older source entry and mathematical statement is preserved. None of these corrections has source-author confirmation or a new compiled association.


The subsequent [tail transfer 40HT](../articles/mesoscopic-tail-transfer.md#section-fictitious-full-tail) supplies the full critical square-root tail and a uniform upper bound for every cutoff. It makes the ghost error small directly from the capped mean, without assuming an untruncated critical cutoff mean of order r^alpha. The lower cutoff tail is proved for n <= a r^(2 alpha), where a is a fixed positive constant. Thus the cutoff-to-full comparison is now supplied, but the coefficient-one cutoff range printed in Lemma III.3.20 remains a distinct obligation. No source erratum about that remaining range is asserted merely because this proof gives a smaller window.


## Opening the gluing argument

Read versioned HTML section III.4.1 through Lemma III.4.4's proof and the opening reduction of case 1 of Lemma III.4.1. Compared Lemma III.4.2's statement and the coupling passage with PDF text on printed pp. 48–49. The later proof of III.4.1 and sections III.4.2 onward have not been supplied by this pass.

| Passage | Wiki treatment and limits |
| --- | --- |
| Geodesic choice before III.4.2 | [BN7Z](../articles/intrinsic-geometry.md#section-consistent-geodesics) chooses paths measurably and equivariantly, with the additional property that a path retained by a subgraph remains selected. |
| Lemma III.4.2; (III.4.2)–(III.4.3) | [XFCJ](../articles/intrinsic-geometry.md#section-restricted-cluster-comparison) proves the comparison for downward-closed classes and finite moments. It supplies the normalized center law and the conditional exterior-resampling coupling. |
| Arbitrary class in III.4.2 | [OTH1](../articles/intrinsic-geometry.md#section-restricted-cluster-counterexample) disproves that scope on ordinary radial lattice percolation at small positive intensity. The [provisional erratum](../errata/hutchcroft-lrp-3.json) gives the counterexample and a repair for the downward-closed classes used in the source. |
| Lemma III.4.3 | [X86B](../articles/intrinsic-geometry.md#section-reimer-path-conversion) proves the signed-witness argument and countable limit **conditional on finite nonmonotone Reimer**. That theorem is not supplied by the existing increasing-event BK proof. |
| Equation (III.4.4) | [69N5](../articles/cutoff-hydrodynamics.md#section-fictitious-large-cluster-vertices) proves abundance using conditional exterior independence, the sharp window estimate and Chebyshev. It retains the large-radius threshold. |
| Lemma III.4.4 | [20LA](../articles/cutoff-hydrodynamics.md#section-fictitious-local-pair-surplus) proves the locally large distinct-cluster contribution at critical intensity by a bounded cover and root averaging. The previously established smaller cutoff-tail window suffices. |

The restricted-cluster correction is independent of the reverse-BK investigation, which remains FIXER's. Its lattice counterexample concerns the unrestricted claim in III.4.2; it is not a counterexample to the later downward-closed application. The new entry remains provisional pending Tom. No claim of the full supremum-over-forbidden-sets gluing statement, a proof of general Reimer, or the final hydrodynamic contradiction is made.


## Completing the conditional gluing lemma

Read both cases of Lemma III.4.1 through the end of Case 2 in versioned HTML. Compared the local-surplus radius, the Case-1 error and band displays, the extra Case-2 class constraint and (III.4.10) with PDF text on printed pp. 52–58. This pass supplies a complete proof of the gluing lemma **conditional on finite nonmonotone Reimer**, which remains a separate literature input.

| Passage | Wiki treatment and limits |
| --- | --- |
| Combining III.4.2–III.4.3; error before (III.4.9) | [JY26](../articles/cutoff-hydrodynamics.md#section-gluing-uniform-error) gives an o(r^alpha) loss uniform over all deterministic forbidden sets and downward-closed classes on bounded-susceptibility scales. It keeps the normalization that actually tends to zero. |
| III.4.1(1); (III.4.5)–(III.4.9) | [9CER](../articles/cutoff-hydrodynamics.md#section-gluing-bounded-susceptibility) mixes finitely many cover centres into the measure, retains the radius-2r local intersection, proves the differential band argument and obtains a common strict deficit on an unbounded bounded-susceptibility set. No maximizing forbidden set is assumed to exist. |
| III.4.1(2); (III.4.10) | [F42K](../articles/cutoff-hydrodynamics.md#section-gluing-divergent-susceptibility) retains only the averaged cap. Uniform cubic moments supply the intensity gain at every sufficiently large radius; a good-scale density argument is unnecessary. The initial radius and error may depend on the fixed parameter, while the positive gain is uniform for small parameters. |
| Sequence used at the opening of III.4.5 | The strict deficit permits a multiplicatively separated subsequence and a smaller cap coefficient with the stated cubic slack. The multi-scale probability bound itself is not proved by this selection. |

Three appended [provisional errata](../errata/hutchcroft-lrp-3.json) record the window-radius mismatch, normalization/band corrections and modified-law constraint/derivative issue. The counterfactual failure assumption remains explicit in all three new assertions. All earlier reading-map entries are preserved as records of their respective passes. Sections III.4.2 onward, the final contradiction, the independent general Reimer proof and the coefficient-one cutoff-tail range remain unfinished. Reverse BK remains FIXER's.


## Many common good scales

Read the proof of Lemma III.4.5 in versioned HTML and compared its scale selection, normalized recurrence and second-cluster filtration with PDF text on printed pp. 59–62. Four assertions now supply the missing-row coefficient and a complete proof of III.4.5, retaining finite nonmonotone Reimer through the earlier gluing premise.

| Passage | Wiki treatment and limits |
| --- | --- |
| Equation (III.4.1) | [NE2Q](../articles/cutoff-hydrodynamics.md#section-missing-intensity-coefficient) proves the exact missing-intensity coefficient by Tonelli, normalized lattice counting and monotone convergence. |
| Conditional comparison (III.4.13) | [WKM2](../articles/intrinsic-geometry.md#section-conditional-cluster-growth) proves the independent-exterior and residual-boundary law for a finite cluster history. The last-exit argument permits a decreasing volume test without applying increasing BK to it. |
| Scale construction and (III.4.12) | [2YIE](../articles/cutoff-hydrodynamics.md#section-many-scales-single-cluster) keeps the weighted tail budget, deficit-dependent separation, arbitrary deleted domain, bounded root shift and arbitrary terminal radius. A generating-function identity bounds the number of small scales without assuming independence between them. |
| Both alternatives of III.4.5 | [QXP9](../articles/cutoff-hydrodynamics.md#section-many-scales-two-clusters) conditions on the first cluster's finite history. The uniform exterior-domain estimate applies to the now fixed subset of root-good scales and gives exponential suppression of distinct cluster pairs with almost all scales bad. |

Two appended [provisional errata](../errata/hutchcroft-lrp-3.json) record the scale-recursion and second-cluster conditioning repairs, including the distinction between the liminf alternatives and the proof's printed limsup split. The new result concerns randomly centred averaged volumes. The recentering theorem III.4.6, the weak-interaction estimate and the final hydrodynamic contradiction remain unfinished. No general Reimer proof, new Lean correspondence or source-author confirmation is inferred.


## Recentring and the modified hydrodynamic contradiction

Read Lemma III.4.6 and the proof of Proposition III.3.1 through its conclusion in versioned HTML. Compared the recentering calculation, scale-count threshold, merger suppression and joining interval with PDF text on printed pp. 63–67. This pass completes the proof of **modified** hydrodynamics, conditional on the finite nonmonotone Reimer theorem used earlier. It does not yet transfer the result to ordinary critical hydrodynamics.

| Passage | Wiki treatment and limits |
| --- | --- |
| Recentring estimate III.4.14–III.4.16 | [43QA](../articles/cutoff-hydrodynamics.md#section-quantitative-recentering) proves the stronger quantitative bound by deterministic counting in an invariant finite-mean cluster partition. It is uniform over every centre law and retains all translated radii. |
| Lemma III.4.6 | [LHT3](../articles/cutoff-hydrodynamics.md#section-many-rooted-good-scales) combines recentering, conditional terminal extension and the correct bad-scale threshold. The sequence can have ratio at least 64, with a uniform block bound at every later terminal radius. |
| Suppressed process and III.4.18 | [7IVI](../articles/intrinsic-geometry.md#section-suppressed-merger-likelihood) proves a finite-state integrated-hazard identity by comparing partition-history likelihoods. Its product-moment bound uses ordinary increasing BK on disjoint rooted-tree witnesses. |
| Proposition III.3.1; III.4.17–III.4.18 | [L3TC](../articles/cutoff-hydrodynamics.md#section-modified-hydrodynamic-theorem) uses joining windows [32s,64s], finite induced-box exhaustion and dominated summation of the intensity derivative. The final lower bound uses the cubic estimate including lambda=0, so no positive-parameter-only derivative statement is extended to that endpoint. |

Three appended [provisional errata](../errata/hutchcroft-lrp-3.json) record the recentering radii/Markov factor, scale-count threshold and joining cutoff window. Source-author confirmation and a general Reimer proof remain separate. Lemma III.4.7, the modified-to-critical transfer in Theorem III.1.11, the later three-point and vertex-factor arguments, and the other previously listed source gaps remain unfinished. Reverse BK stays with FIXER.


## The ordinary hydrodynamic transfer

Read Lemma III.4.7 and the concluding proof of Theorem III.1.11 in versioned HTML and compared PDF printed pp. 67–68. Four assertions now supply this transfer, retaining finite nonmonotone Reimer when the earlier modified theorem is used.

| Passage | Wiki treatment and limits |
| --- | --- |
| Uniform translated-window means used in the proof | [MTUQ](../articles/connection-kernels.md#section-translated-window-mean) uses connection-kernel positivity to pass from the centred mean bound to a uniform bound over centres. No monotonicity of the two-point function in distance is assumed. |
| Lemma III.4.7 | [9JTA](../articles/cutoff-hydrodynamics.md#section-local-moment-transport) retains the two transformed window centres in the mixed term. Finite-box Russo and integral Gronwall give the local-moment transport for cutoffs at or below critical intensity, with almost-everywhere derivative statements. |
| Modified susceptibility upper bound and critical asymptotic | [5CV7](../articles/cutoff-hydrodynamics.md#section-hydrodynamic-susceptibility) first confines the normalized susceptibility using good scales and a forbidden downward crossing, then integrates its reciprocal. The limit in the modification parameter is taken after the radius limit. |
| Theorem III.1.11, concluding moment/quantile transfer | [BCKB](../articles/cutoff-hydrodynamics.md#section-ordinary-hydrodynamic-theorem) transports the vanishing local second moment to critical intensity at bounded exponential cost, then uses partition counting to prove the ordinary condition. No alpha<2 restriction is needed for this result. |

One further [provisional erratum](../errata/hutchcroft-lrp-3.json) records the transformed-window discrepancy. The conditional prose chain through Theorem III.1.11 is now complete; a general finite Reimer proof, the quantitative rate conjecture, the later three-point and vertex-factor sections, and the other previously listed source gaps remain separate. This creates no new Lean proof or reviewed source association. Reverse BK remains FIXER's.


## First-connection machinery for the three-point estimate

Read the opening of Section III.5.1, including (III.5.1)–(III.5.7), in versioned HTML and compared the PDF, printed pp. 69–71. The following four assertions supply the first-connection identities and the stopped-growth step, with the stronger weighted-moment estimates still separate.

| Passage | Wiki treatment and limits |
| --- | --- |
| First-connection differentiation | [88ZH](../articles/intrinsic-geometry.md#section-first-connection-identity) proves the finite crossing-edge compensator directly from partition histories. Each unordered crossing edge is counted once. |
| Stopped exterior used for (III.5.7) | [DTOX](../articles/intrinsic-geometry.md#section-first-connection-growth) disintegrates over internal exponential clocks. The stopped root history leaves a fresh exterior and memoryless boundary residuals; this is not asserted for the full graph history. |
| Definitions and exact derivative of the stopped spatial moments | [FMUH](../articles/multipoint-trees.md#section-radial-first-connection) proves the lattice identity by finite-box stabilization and integrable domination. The initial radius lies below the smallest nonzero lattice distance. |
| Equation (III.5.7) | [JDX7](../articles/multipoint-trees.md#section-radial-stopped-growth) proves the weighted growth inequality using the omitted intensity row, last-exit paths and the binomial expansion. |

These are finite-cutoff identities and bounds. Lemma III.5.2 and Proposition III.5.1 are not yet completed here: their quantitative spatial mixed moments must retain the vertex factor V, and the rapid-tail and stopped-moment estimates must still be proved. The earlier crude multigraph bound does not discharge that input. No new Lean proof or reviewed source association is claimed, and the existing provisional errata remain provisional.


## Spatial upper moments and the rapid tail

The spatial input to (III.5.1) is now proved for the normalized radial model under the sharp susceptibility equivalent, with alpha<2. At critical dimension that equivalent is supplied by the earlier conditional hydrodynamic chain. The sharper volume-moment input remains separate.

| Passage | Wiki treatment and limits |
| --- | --- |
| Even spatial moments used in (III.5.1) | [WKJR](../articles/spatial-cutoff-moments.md#section-even-spatial-upper-hierarchy) applies BK before expanding the nonnegative target weight. Symmetry cancels odd terms and leaves leading coefficient two. |
| Spatial scale r when alpha<2 | [YU52](../articles/spatial-cutoff-moments.md#section-radial-spatial-upper-moments) uses the sharp susceptibility coefficient in an upper-ODE induction. It proves all fixed spatial upper moments for arbitrary normalized norms, without requiring spatial equivalents. |
| Equation (III.5.1), using Part I Lemma I.5.27 | [AR3F](../articles/spatial-cutoff-moments.md#section-vertex-factor-mixed-upper) supplies the norm-power reduction retaining V. Its volume-moment premise remains explicit; Part I Proposition I.4.20 and the required critical probabilistic estimates are not inferred from the analytic hierarchy alone. |
| Equation (III.5.2) | [3M2Y](../articles/multipoint-trees.md#section-rapid-weighted-tail) constructs one positive decreasing envelope from all polynomial tail bounds. For higher marked orders it retains AR3F's volume input. |

Compared the tail display in versioned HTML and the PDF, printed p. 69, and Part I Lemma I.5.27 in versioned HTML. A [provisional index erratum](../errata/hutchcroft-lrp-3.json) records the unbound first factor in (III.5.2), repaired by starting the remaining product at two. The n=1 first-moment spatial tail has no additional volume premise. The higher-volume input, quantitative stopped-moment estimates and final three-point theorem remain unfinished. No Lean proof or reviewed source association is added.


## The critical volume input is supplied

The volume premise left explicit in AR3F and 3M2Y is now supplied for d=3 alpha under the susceptibility and ordinary hydrodynamic conclusions of BCKB. The conditional dependence on finite nonmonotone Reimer remains visible through L3TC. Read the needed Part I passages in versioned HTML, Lemma I.4.16, the critical case of Proposition I.4.15, and the upper induction in Proposition I.4.20.

| Passage | Wiki treatment and limits |
| --- | --- |
| Part I Lemma I.4.16 | [65MV](../articles/multipoint-trees.md#section-generalized-tree-moments) groups edge-disjoint internal stars into three-point factors and sums the resulting incidence tree. It preserves m2 factors in higher moments. |
| Part I Proposition I.4.15, critical case | [121D](../articles/cutoff-hydrodynamics.md#section-critical-second-moment-variation) uses the sixth-moment bound and rooted window damping to make the second-moment error vanish. It proves slow variation of V with an explicit tail ratio bound. |
| Part I (I.4.19), supplying Part III (III.5.1)–(III.5.2) | [RM79](../articles/cutoff-hydrodynamics.md#section-critical-volume-upper) uses only the upper hierarchy to obtain the needed volume-moment bound. Together with YU52, AR3F and 3M2Y this supplies both weighted input estimates at critical dimension when alpha<2. |

The full higher-moment equivalents are stronger than the upper bounds needed here and have not been asserted. The quantitative stopped-moment estimates, the final three-point theorem and the vertex-factor computation still remain. No new Lean correspondence is claimed.


## The critical three-point estimate is completed

For d=3 alpha and alpha<2, the chain now proves the averaged weighted bound of Lemma III.5.2 and the cutoff/full-model bound of Proposition III.5.1. Sharp susceptibility and ordinary hydrodynamics are supplied by BCKB, conditionally on the explicitly retained finite nonmonotone Reimer premise through L3TC. No new moment hypothesis is introduced in the closing argument.

| Passage | Wiki treatment and limits |
| --- | --- |
| Equations (III.5.3)–(III.5.6) | [7GBI](../articles/multipoint-trees.md#section-critical-stopped-moments) controls the stopped moments on both sides of the separation scale. It starts below the shortest lattice distance and retains the small-radius contribution. |
| Lemma III.5.2 | [2CQ5](../articles/multipoint-trees.md#section-critical-averaged-three-point) combines the stopped estimates with JDX7. A strictly negative exponent makes the near integral finite even at degree zero; the far estimate costs only a polynomial that the rapid envelope absorbs. |
| Proposition III.5.1 and (III.5.8)–(III.5.10) | [8JMB](../articles/multipoint-trees.md#section-critical-three-point-bound) counts each two-component merger once and treats all three root pairings. The weighted averaged bound provides every far-tail power; integration gives the distance exponents and rapid cutoff decay. Finite path witnesses give the full critical limit without finite full-model susceptibility. |

The exact two separation scales are retained: the vertex factor is evaluated at the minimum pair distance, while the cutoff tail is evaluated at the maximum pair distance divided by the cutoff. The result is proved for arbitrary normalized norms in the stated critical-dimension range. The general above-critical assembly, the remaining refinements in Section III.5, and Section III.6's vertex-factor computation are still separate. All existing source errata remain provisional and unchanged. No new Lean proof or reviewed source association is asserted.


## Critical three-point comparison and lower bound

The critical upper bound now has its matching lower bound. The following additions retain the finite nonmonotone Reimer dependency of the hydrodynamic input and leave source correspondences pending review.

| Passage | Wiki treatment and limits |
| --- | --- |
| Remark III.5.3 and (III.5.11), PDF pp. 73–74 | [54OK](../articles/multipoint-trees.md#section-three-point-convolution) proves the tree-convolution comparison for arbitrary norms when d>2 alpha. Its kernel has an explicit finite diagonal value. At d=3 alpha, the tree and three-point product upper expressions have the same distance powers. |
| Part I Proposition I.4.20, used in §III.5.2 | [326J](../articles/cutoff-hydrodynamics.md#section-critical-volume-equivalents) proves the critical volume-moment equivalents and the size-biased volume limit. Its truncated-mass conclusion supplies the previously missing small-mass input. |
| (III.5.12) and Lemma III.5.5, PDF pp. 74–75 | [3N3Q](../articles/multipoint-trees.md#section-critical-local-mass) gives the required local-mass probability and conditional persistence with one fixed dilated ball. The paper instead invokes Theorem I.5.21 and Corollary I.5.22 for a unit-ball statement. The dilation is retained, not silently identified with that statement. |
| Proposition III.5.4 and (III.5.13)–(III.5.15), PDF pp. 74–76 | [KBOM](../articles/multipoint-trees.md#section-critical-three-point-lower) supplies the critical lower bound with all local-mass inputs proved. Conditional Harris handles the dependence on later mass events. Fixed, sufficiently long fresh-edge intervals handle possible flat kernel segments at bounded radii. |

Thus the full three-point function at d=3 alpha, alpha<2 is comparable to V at the minimum separation times the two stated distance powers. The vertex-factor equivalent, the general higher-point lower bound in Remark III.5.6, and the general above-critical assembly remain unfinished. The unit-ball spatial limit has not been proved by this alternative route. No source erratum is added or promoted, and no new Lean result is asserted.


## Critical marked sets and the start of the vertex-factor calculation

[3K2W](../articles/multipoint-trees.md#section-critical-marked-set) proves the critical case of Remark III.5.6, including the individual vertex factors in (III.5.16). The proof works for every rooted tree, orders the marks by their sweep radii and reserves one fresh-edge interval for each parent edge. Conditional Harris preserves the mass requirements at later scales. The estimate already holds at a finite cutoff depending only on the diameter and cardinality. For two or three marks it reduces to the existing distance powers. The above-critical case and the conjectured matching upper bound remain separate.

Read the versioned HTML from the start of III.6 through the proof of Proposition III.6.2 conditional on Theorem III.6.6. Compared the normalization in (III.6.13) and the following unit-ball calculation with PDF p. 83. This does not constitute an audit of the later proof of Theorem III.6.6.

| Passage | Wiki treatment and remaining input |
| --- | --- |
| Remark III.6.5 | [5J3U](../articles/cutoff-hydrodynamics.md#section-critical-vertex-lower) proves the lower logarithmic order directly from the exact deficit difference and the fourth-moment upper bound. Its explicit constant is not optimal. |
| (III.6.10) | The same theorem proves that V tends to zero when alpha<2, using a fixed dilated ball and the rooted window estimate. |
| Lemma III.6.3 and the scalar integration step | [09N5](../articles/marginal-ode.md#section-asymptotic) already gives an integrable-error ODE argument. [OP8F](../articles/marginal-ode.md#section-asymptotic) instead cancels the two exact moment equations and integrates the deficit gap, without a separate second-order susceptibility expansion. No duplicate analytic theorem is added. |
| Theorem III.6.6 and (III.6.15)–(III.6.16) | The [remaining-input discussion](../articles/cutoff-hydrodynamics.md#section-critical-deficit-gap) records the two normalized deficit measures, the needed weak limits and their implication for the gap constant. These interacting-cluster limits, their moment-determinacy step and the triple-interaction error are still unproved in this wiki. Ordinary volume equivalents alone do not imply them. |

A new [provisional erratum](../errata/hutchcroft-lrp-3.json) records that (III.6.13) prints a fourth susceptibility power while its subsequent unit-ball calculation uses a fifth power. Both HTML and PDF contain the mismatch. The fifth power agrees with the algebra of (III.6.15); this consistency check does not prove Theorem III.6.6. All earlier source records and provisional statuses are retained. The new prose proofs remain conditional on the existing finite nonmonotone Reimer input and do not create Lean results.


[GL6S](../articles/cutoff-hydrodynamics.md#section-critical-deficit-tightness) now supplies Lemma III.6.9 at d=3 alpha, alpha<2. Common-cluster domination and the existing mixed moments give the fifth and seventh susceptibility powers, uniformly bounded polynomial moments and rapid tails. Consequently the normalized deficit measures are tight and polynomial integrals pass along weak subsequences. The proof of Lemma III.6.9 was read in the versioned HTML. The exact derivative identities in III.6.10, the triple-interaction approximation III.6.11 and the merging-term equivalents III.6.12 remain the next probabilistic inputs to audit and establish; their moment limits are not consequences of tightness.


## Exact deficit equations and unweighted mergers

[B5NA](../articles/cutoff-hydrodynamics.md#section-two-root-deficit-derivatives) now proves Lemma III.6.10 for the radial cutoff model. It derives the signed two-root generator before using reflection, counts root-cluster mergers once, and justifies the countable limit on every compact radius interval. The kernel derivative multiplies the formula, so flat kernel segments cause no division by zero. No hydrodynamic or critical-dimension assumption is needed for these exact identities.

[HV5B](../articles/cutoff-hydrodynamics.md#section-critical-merging-mass) proves the degree-zero part of Lemma III.6.12 at d=3 alpha, alpha<2, and gives the same mass-transport argument for every fixed positive integer root-volume power. The total merging terms have coefficients one and three. Their common-cluster error is a vanishing fraction of the product by the existing volume equivalents and V -> 0, without a spatial scaling limit. The source's nonconstant polynomial weights remain untreated by this argument.

The versioned HTML proof of III.6.10 and the III.6.12 calculation were read. Lemma III.6.11 still requires a full audit and proof of its triple-interaction approximation; this is not removed by the exact identities or unweighted merger equivalents. No additional source erratum or Lean result is asserted in this extension.


## Critical geodesics and the two collision diagrams

[V7V5](../articles/intrinsic-geometry.md#section-critical-weighted-geodesics) proves the critical case of Lemma III.6.18. It supplies the pivotal-rate input from the second-moment suppression, including the intensity-neighborhood and continuity argument needed at beta_c. The path vertex count is chemical distance plus one. The unbound target in the source display was checked against both HTML and PDF and is recorded as a provisional index erratum.

[SE64](../articles/intrinsic-geometry.md#section-critical-double-path-hit) proves the independent-cluster double-hit diagram used for Lemma III.6.15. [BX1G](../articles/multipoint-trees.md#section-critical-three-point-product) proves the double three-point diagram used for Lemma III.6.16. Both arguments sum every spatial-weight placement, and BX1G treats the coincident-root term separately before using the off-diagonal bound. These are critical-dimension results under the existing sharp susceptibility and ordinary hydrodynamic hypotheses, whose model verification retains finite nonmonotone Reimer as an explicit dependency.

The coupling law, the deterministic cut-event reductions, interception, and the final decoupling estimates in III.6.11 remain to be proved. The diagram bounds alone do not supply that lemma or the deficit-measure limits. Nonconstant spatial merging equivalents are also still needed. No new Lean correspondence or confirmed source correction is asserted.


The subsequent audit found a further issue in the displayed bound for III.6.17. [ZGVN](../articles/intrinsic-geometry.md#section-interception-diagram) proves that its degree-zero unrestricted sum is infinite: the root-cluster mark is disconnected from the rest of the diagram, leaving infinitely many equal positive translated contributions. Both HTML and PDF have this display. The new erratum is provisional and concerns the proof step, not the theorem's truth.

[IEOH](../articles/intrinsic-geometry.md#section-interception-diagram) supplies a negligible diagram with that mark retained on the intercepted path, using fifth mixed moments and weighted geodesic bounds. A valid reduction from the coupled cut event to this or another finite diagram is still required. In particular, a path chosen after deletion cannot silently be assigned the law of the original independent geodesic.


## The weighted merging terms now have their spatial input

[AL0I](../articles/spatial-cutoff-moments.md#section-critical-spatial-tree-limits) proves the required single-cluster spatial moments at critical dimension for an arbitrary normalized norm, from the existing sharp susceptibility and ordinary hydrodynamic inputs. [J2QW](../articles/cutoff-hydrodynamics.md#section-critical-weighted-mergers) then proves both spatially weighted equivalents of Lemma III.6.12. The source proof of that lemma was read; the wiki keeps the observation window explicit in the independent product and derives its uniform-ball limit by Riemann sums.

The two coefficients are convolution densities kappa^4*1_B and (kappa^4+2 kappa^5)*1_B, giving masses one and three. Signed polynomials are handled by additive errors and never by division by a possibly zero moment. The common-cluster error has relative order O(V^2). The unresolved III.6.11 coupling/interception and decoupling steps still prevent identification of the two interacting-cluster deficit measures. Existing source errata remain provisional and unchanged.


## Conditional deficit hierarchy and logarithmic coefficient

[ENWJ](../articles/cutoff-hydrodynamics.md#section-conditional-deficit-moments) gives a complete conditional proof of both deficit polynomial limits from two explicitly stated asymptotic ODEs. It counts labelled linear factors, uses the positive gaps alpha+p and 2alpha+p, and identifies the constants by the existing resolvent chain identity. [RDLW](../articles/cutoff-hydrodynamics.md#section-conditional-deficit-amplitude) then proves weak convergence and the logarithmic amplitude, including moment determinacy, positivity of 2*integral_B kappa^4 and exact cancellation of the equal origin atoms.

The two ODEs are additional probabilistic hypotheses. The unresolved III.6.11 coupling/interception/decoupling argument is not inferred from the merger or single-cluster results. This completes the analytic implication, not an unconditional proof of the final percolation theorem.

A further provisional erratum records the mismatch between the forcing terms printed in Lemma III.6.13 and those in III.6.12 and the later proof: kappa^3 versus kappa^4 in the first, and 3kappa^4 versus kappa^4+2kappa^5 in the second. Both HTML and PDF were compared. Quadratic tests distinguish them even though their total masses agree. No source-author confirmation or compiled Lean result is asserted.


## Cluster coupling and the first two cut errors

[DR5Q](../articles/finite-transcripts.md#section-cluster-splicing) proves the product-law claim in the three-cluster construction by conditioning on countably many finite cluster records. It permits an infinite boundary, repeated roots and degenerate edge probabilities. The coupled cuts are exactly the third independent configuration's deletion events for A, C and A union B, where B is the second cluster restricted off A and B is contained in C.

[KF1W](../articles/intrinsic-geometry.md#section-coupled-redundancy) now supplies the critical version of III.6.15, including its coupling-to-diagram reduction. [RIH3 and 1P14](../articles/multipoint-trees.md#section-joint-cut-witnesses) supply the deterministic witnesses and the critical version of III.6.16. The former uses a minimal separator in the finite union of two avoiding paths; the latter applies BK to the resulting disjoint edge witnesses and invokes the existing double three-point bound. All nonnegative integer spatial weights are included.

Both HTML and PDF repeat one of the path-avoidance conditions in the opening sentence of the III.6.16 proof. A provisional erratum records the two distinct conditions, and distinguishes edge disjointness from vertex disjointness. No counterexample to the lemma or author confirmation is asserted.

These additions close the coupling, redundancy and joint-cut obligations previously left open above. The separate III.6.17 interception estimate and final decoupling remain unresolved. Consequently ENWJ/RDLW still require their explicit deficit ODE hypotheses; no unconditional final vertex-factor equivalent is claimed.


## The other cluster powers in the cut estimates

[DVHL](../articles/intrinsic-geometry.md#section-powered-double-hit) extends the redundancy diagram to arbitrary powers of the first two root clusters and an arbitrary extra power of the independent third cluster. Cauchy–Schwarz under target counting retains the appropriate vertex factor in the path moments. [CWM1](../articles/multipoint-trees.md#section-powered-joint-cut) extends the joint-cut estimate to arbitrary first and second root powers when the third-cluster power is one.

[JG0C](../articles/cutoff-hydrodynamics.md#section-triple-root-transport) proves the exact change of root and independent target-tuple representation of the triple-interaction term. It verifies that the source powers p1 and p2 exchange roles, and proves absolute summability of the integrated signed polynomial coefficients. The new cut bounds have the required error scale for (p1,p2,p3)=(0,1,1),(0,2,1),(1,1,1).

The case (0,1,2) is a loss of ordered pairs of targets. Its two single cuts can remove different coordinates. [6IJQ](../articles/intrinsic-geometry.md#section-tuple-redundancy) controls this contribution using two original geodesics and completes redundancy for every target-tuple power. The joint-cut estimate with an extra third-cluster factor, interception and final decoupling remain open. This extension does not certify the printed right side of III.6.11 or remove the explicit ODE hypotheses from ENWJ/RDLW. All 90 existing errata remain provisional and unchanged.


## Joint cuts with the full third-cluster power

[RT01](../articles/multipoint-trees.md#section-higher-marked-kernels) proves the higher marked-kernel product bound needed when III.6.16 carries extra third-cluster marks. The spatial three-point estimate gives an Lq bound for every fixed 2 ≤ q < 3. Hölder then uses the exact sums of higher kernels, which are mixed volume moments, to retain the full vertex-factor power. The diagonal is included using the established logarithmic lower bound on V.

[AK2E](../articles/multipoint-trees.md#section-weighted-disjoint-witnesses) supplies the matching probability bound: a finite forest assigns extra labelled marks to either of two disjoint connected witnesses, after which BK gives a binomial sum of marked connection products. [B9Z5](../articles/multipoint-trees.md#section-tuple-joint-cuts) combines these facts and the minimal-separator construction to control joint cuts of every target tuple, with relative error O(V²). Repeated targets and zero first/second cluster exponents are included.

Together with 6IJQ, this closes the redundancy and joint-cut contributions for every power triple required in III.6.10, including (0,1,2). Interception and final decoupling remain open; the corrected deficit ODEs in ENWJ and their consequences in RDLW are still conditional. No new source error is diagnosed, and all 90 provisional errata are retained without change.


## The final single-cut decoupling

[PGVH](../articles/intrinsic-geometry.md#section-marked-single-path) supplies critical one-path estimates with a spatial mark on the path, at its target, or elsewhere in its cluster. [ZYSL](../articles/cutoff-hydrodynamics.md#section-single-cut-decoupling) uses these estimates to prove both factorizations stated without details at the end of the proof of III.6.11, for every cluster power needed after the change of root.

The loss from replacing the restricted second cluster by its independent original cluster is expanded into lost target tuples. Original geodesics record the necessary intersections, giving summable diagrams on the exact source scale. A separate, smaller correction restores the restricted marginal in the first factorization. The proof includes signed polynomial tests, spatial weights, repeated marks and zero first/second cluster exponents.

The completed redundancy, joint-cut and decoupling estimates do not replace that input, so ENWJ/RDLW and the final logarithmic equivalent remain conditional. No new erratum is diagnosed; all 90 provisional entries remain unchanged.


## Interception proof repair — 17 November 2026

[LK8Z](../articles/intrinsic-geometry.md#section-interception-repair) proves the deterministic surviving-path inclusion supplied by FIXER. [O10I/R6CI](../articles/intrinsic-geometry.md#section-interception-moments) retain the second-geodesic mark, use two ordinary BK connections in the third copy, and evaluate every spatial-weight placement. The source conclusion holds for all nonnegative integer p,q at and above the upper critical dimension, with alpha<2. Earlier source moments and chemical-distance bounds are named explicitly; no final logarithmic asymptotic is used.

This supersedes the earlier pending status of the mathematical interception gap. The divergent dropped-link display remains a provisional erratum. IEOH remains separate and is not asserted to bound the coupled event. The [dependency update](../articles/cutoff-hydrodynamics.md#section-interception-update) distinguishes this repair from the complete triple-interaction assembly and Lean obligations; ENWJ/RDLW retain their hypotheses. Versioned HTML was checked at Lemma III.6.17 and (III.6.39), and Part I Lemma I.5.27 was checked for the moment inputs. No new visual-PDF or compilation claim.
