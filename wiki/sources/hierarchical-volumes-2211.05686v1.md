# Critical cluster volumes on the hierarchical lattice

Read the introduction and all of section 2 of [arXiv:2211.05686v1](https://arxiv.org/html/2211.05686v1), 17 November 2026. The 85-page [PDF](https://arxiv.org/pdf/2211.05686v1) was compared in extracted text at the initial coalescent transition display and equation (2.1), printed pages 15–16; no visual-PDF audit was performed. The [2025 journal version](https://doi.org/10.1112/plms.70023) has not been compared.

The paper works with an exact power-law radial kernel, with a fixed geometric-series normalization. Its introduction explicitly leaves broader kernel extensions to further work. That broader statement is not justified merely by citing this paper; this is a scope boundary, not a diagnosed counterexample or a new erratum.

| Source passage | Written treatment |
| --- | --- |
| Section 1.1, exact radial kernel and block layers | [VI3Y](../articles/hierarchical-block-coalescent.md#section-exact-block-layers) proves the independent-layer construction, the missing ancestor intensity in a finite block, and the increasing finite-witness limit. |
| Section 2, transition display and (2.1); Remark 2.2 | [Z960](../articles/multiplicative-coalescent.md#section-block-coalescent) derives the finite generator; the intermediate independent-bond law, including zero intensity without dividing by the terminal time, is in [the exact block process](../articles/hierarchical-block-coalescent.md#section-definitions). |
| Lemma 2.3 and (2.4) | [22H8](../articles/multiplicative-coalescent.md#section-coalescent-moments) proves every mixed-moment equation explicitly, retaining the diagonal and merger corrections. |
| (2.2)–(2.3), (2.5)–(2.7) | [54V4](../articles/hierarchical-block-coalescent.md#section-coalescent-gluing) proves the full multinomial recursion across independent children and the identity with rooted moments. |
| Component-size determination after (2.4) | [W8PB](../articles/multiplicative-coalescent.md#section-size-determination) gives a finite Vandermonde and polynomial-interpolation proof. It determines the size multiset, not the labelled partition. |

The initial holding-probability display double counts the merger rate if its pair sum is read, consistently with the next display, as ordered. The following generator already includes the correct factor. The [provisional erratum](../errata/hutchcroft-hierarchical-volumes-2022.json) gives the complete local repair and the Lean obligation. The moment identities are unaffected.

The introduction also states matching low-dimensional volume tails in Theorem1.2, high-dimensional moment equivalents in Theorem1.4, and critical-dimensional moment and tail results in Theorems1.6–1.7. These statements were read to identify the proof targets. Their later proofs in sections4–6 have not been audited in this pass. In particular, the finite equations here do not establish asymptotic factorization, hydrodynamics, the logarithmic correction, or the transfer from block moments to full-cluster tails. Section3's universal estimates should be matched to the wiki's existing universal-tightness proofs before adding new material. Section7's research questions have not yet been inventoried.

The construction and all five new assertions are written mathematics only. No compiled association with the Lean repository is claimed. The existing conditional hierarchical upper bounds and all earlier universal estimates are preserved.


## Norm tightness and the first concentration estimates

Reading update, 17 November 2026: all of section 3 and the arguments for Lemmas 4.6–4.7, Proposition 4.5, Lemma 4.8 and Corollary 4.9 have now been read in versioned HTML. The section 3 boundary displays and (3.12) were compared with extracted PDF text on printed pages 22–24. This extends the earlier reading boundary; no visual-PDF or journal audit was performed.

| Source passage | Treatment |
| --- | --- |
| Theorem 3.1; Lemma 3.3 | Existing [DMI0/12NL](../articles/finite-set-hyperscaling.md#section-splitting) already give the marked splitter and maximum/rooted estimates. No duplicate proof was added. |
| Theorem 3.2, Corollary 3.4, Lemma 3.5 | [3109](../articles/finite-set-hyperscaling.md#section-norm-tightness) combines pieces from different clusters, keeps the isolated-mark contribution, and supplies the finite-witness countable passage and real-quantile argument. Constants are uniform in the norm index. |
| Corollary 3.7 and (3.12) | [25TW](../articles/finite-set-hyperscaling.md#section-norm-moments) proves power-sum moment bounds, mixed comparisons and uniform integrability for fixed indices. [X2A4](../articles/hierarchical-block-coalescent.md#section-coalescent-concentration) gives the intermediate-block and child-quantile consequences. |
| Lemmas 4.6–4.7 | [25Z4](../articles/cluster-partitions.md#section-cluster-covariance) proves the conditional-complement comparison and covariance bound, also for finite windows on countable graphs. |
| Proposition 4.5, Lemma 4.8 and Corollary 4.9 | [X2A4](../articles/hierarchical-block-coalescent.md#section-coalescent-concentration) gives the exact mean-equation error and concentration criterion. The critical mean lower bound and hydrodynamic condition remain explicit separate inputs. |

Equation (3.12) overstates uniformity in the moment index. Its counterexample occurs inside a fixed critical hierarchical model, at increasingly small positive level-one times. The repaired gamma-factor estimate retains every fixed-index comparison needed here. Positive amplification scales, weak atomic-quantile bounds and the level-zero singleton are also made explicit. These are two new [provisional entries](../errata/hutchcroft-hierarchical-volumes-2022.json), with complete local repairs. They do not diagnose a failure of the matching tail results.

The next analytic tasks are to justify the critical lower mean estimate for the truncated block law, then the reciprocal-mean recursion and higher moment asymptotics. The opening of section 4 and the displayed mean recursion have been inspected, but their full proof correspondence is not claimed here. The later hydrodynamic and tail arguments, and the comparable-kernel extension beyond the paper's exact law, remain open coverage tasks.


## Critical means and the reciprocal recursion

Reading update, 17 November 2026: the opening of section 4 and all of section 4.1 are now read. The theorem coefficients on printed pages 9–10 and the reciprocal proof on printed pages 29–31 were checked in extracted PDF text against the versioned HTML. The journal's full-text link returned its abstract, so this update does not compare the journal formulas or claim visual-PDF inspection.

| Source passage | Treatment |
| --- | --- |
| Theorem 4.1 and (4.4) | [2VXH](../articles/hierarchical-runaway.md#section-critical-block-means) proves the critical mean bounds for the truncated block law. Boundary flux first controls the induced full graph; an independent ancestor-layer comparison transfers the lower bound to the truncated graph. |
| Proposition 4.2 and the high-dimensional case of Proposition 4.5 | [6WO3](../articles/hierarchical-runaway.md#section-high-dimensional-maximum) proves the maximum estimate and hydrodynamics for d greater than 3 alpha, with a quantitative variance/error bound. |
| Lemma 4.10, Corollaries 4.11 and 4.13 | [W2VN](../articles/hierarchical-runaway.md#section-reciprocal-mean) proves the exact reciprocal series, sharp lower bound and uniform mean equivalent under hydrodynamics. The discarded terminal reciprocal is bounded above. |
| Theorems 1.4 and 1.6 at p=1 | The source's terminal cluster requires coefficient (L^alpha-1)/beta_c. The smaller printed coefficient belongs to the initial coalescent time. The exact lower bound already rules out that smaller terminal asymptotic. |

The first-moment normalization and local reciprocal-proof defects are recorded as two [provisional errata](../errata/hutchcroft-hierarchical-volumes-2022.json), with complete local repairs in the private source issue. Their relationship to formalization is explicit; none has a compiled association or source-author confirmation. The later higher-moment coefficients have not been corrected by analogy.

The remaining section 4 task starts at section 4.2: second and higher moment equivalents and their constants. Critical-dimensional hydrodynamics, the matching volume-tail arguments and sections 5–7 remain coverage work. The generic real moment-ratio inequalities already appear in [the exponential-moment article](../articles/exponential-moments.md#section-real-ratio-source); they do not need a duplicate treatment.


## Second and higher moments

Reading update, 17 November 2026: sections 4.2–4.3 are now fully read in versioned HTML, completing the section 4 audit. The disputed second-moment exponent, heuristic half-factor and higher-moment scale recurrence were checked in extracted PDF text on printed pages 31, 34 and 38. No journal-formula or visual-PDF comparison is claimed.

| Source passage | Treatment |
| --- | --- |
| Proposition 4.14 and Corollary 4.15 | [I7HB](../articles/hierarchical-runaway.md#section-second-moment) proves the time ratio, growth exponent, positive high-dimensional amplitude and quantitative error. It also rules out hydrodynamics below the critical dimension. |
| Lemma 4.18 and Proposition 4.17 | [ANYT](../articles/hierarchical-runaway.md#section-higher-moment-ratios) proves the double-factorial identity and a stable exact equation for the normalized moment. Exact gluing gives contraction with gap p-3. |
| Corollary 4.19 | [KPCV](../articles/hierarchical-runaway.md#section-all-moment-concentration) gives covariance negligibility, convergence in every fixed finite Lr and factorization of finite mixed moments. |
| Theorem 1.4 | [FY23](../articles/hierarchical-runaway.md#section-rooted-moment-equivalents) proves all high-dimensional rooted moment equivalents with the terminal coefficient. The same moment ratios and the existing general moment theorem give a volume-biased squared-normal limit. |

The scale exponent in the high-dimensional second-moment statement and the scale/contraction exponents at the end of the higher-moment proof require local repairs. The earlier heuristic coefficient recurrence also drops a half-factor; p=4 detects it immediately. Two new [provisional entries](../errata/hutchcroft-hierarchical-volumes-2022.json) record the repairs and formalization obligations. All prior entries are preserved. The first-moment correction can now be propagated through the full high-dimensional moment family, with its second-moment constant explicitly defined.

The next source task is section 5.1: the pointwise low-dimensional maximum lower bound. Its theorem statement has been read, but its proof and the remaining sections 5–7 have not been audited here. Failure of hydrodynamics alone does not give that lower bound. Critical-dimensional hydrodynamics and the critical second-moment logarithmic amplitude remain separate inputs, and no comparable-kernel extension is inferred.


## Low-dimensional scales, tails and vector norms

Reading update, 17 November 2026: all of sections 5.1–5.3 have now been read in versioned HTML. The disputed maximum-growth display, capped-merger maximization, block normalization, scale indices and endpoint norm calculation were compared with extracted PDF text on printed pages 41 and 45–48. No journal-formula or visual-PDF comparison is claimed.

| Source passage | Treatment |
| --- | --- |
| Theorem 5.1 and Corollary 5.2 | [Q8JZ](../articles/hierarchical-runaway.md#section-low-dimensional-maximum) bounds all runs of small maxima and proves the pointwise maximum scale and all fixed real moments. |
| Lemmas 5.4 and 5.6; Corollary 5.5 | [RHK3](../articles/hierarchical-runaway.md#section-capped-block-moments) gives the capped generator and third-moment drift, then a correctly indexed finite backward iteration. |
| Proposition 5.3 | [L3QJ](../articles/hierarchical-runaway.md#section-mesoscopic-negligibility) proves the stronger capped estimate by excluding a fixed window of excessive third-moment growth, with small scales explicit. |
| Theorem 1.2 and (5.7) | [ZDDE](../articles/hierarchical-runaway.md#section-low-dimensional-tail) gives matching full-cluster tails, the finite-block lower bound and an exponential cutoff. The red/blue ghost argument uses the proved mesoscopic input. |
| Corollary 1.15 | [THZF](../articles/hierarchical-runaway.md#section-low-dimensional-vector-tightness) proves tightness above the sharp norm threshold and norm divergence in probability at the endpoint. |

Four new [provisional errata](../errata/hutchcroft-hierarchical-volumes-2022.json) record repairs of the growth/child bookkeeping, capped-merger maximization, capped normalization/scale indices, and norm-threshold tail calculation. The last also supplies the probability argument missing from an inference based only on diverging expectations. All theorem conclusions are preserved.

The conclusions here require the exact radial model and d/3<alpha<d; the capped generator and backward propagation themselves hold throughout 0<alpha<d. Section 5.4 has been read only through Theorem 5.7, Proposition 5.8 and Lemma 5.9. The proof that every limiting coordinate is positive remains next, followed by critical-dimensional hydrodynamics and logarithmic amplitudes in section 6 and the remaining section 7. No comparable-kernel extension is inferred.


## Every fixed cluster rank and positive limiting coordinates

Reading update, 17 November 2026: section 5.4 has now been fully read in versioned HTML. The backward maximum and connection calculations were compared with extracted PDF text on printed pages 51–53. No journal-formula or visual-PDF comparison is claimed.

| Source passage | Treatment |
| --- | --- |
| Lemma 5.9 | [O7W9](../articles/hierarchical-runaway.md#section-backward-maximum) retains the block-volume factor in the third-moment derivative and comparison, then propagates a maximum lower bound backwards. |
| Connection estimate in Proposition 5.8 | [OAE2](../articles/hierarchical-runaway.md#section-selected-cluster-connections) supplies the two higher-layer escape factors and an explicit shell convolution. It selects one maximum with a deterministic tie rule and handles selection by Harris. |
| Proposition 5.8 | [YUJ9](../articles/hierarchical-runaway.md#section-many-large-clusters) proves a single high-probability event with any fixed number of large components throughout the coalescent level. |
| Theorem 5.7 and limit discussion after Corollary 1.15 | [ADJZ](../articles/hierarchical-runaway.md#section-positive-limit-coordinates) gives every fixed-rank volume scale in low dimension and positivity of every coordinate of every weak subsequential limit. |

Two new [provisional errata](../errata/hutchcroft-hierarchical-volumes-2022.json) record the missing volume factor in Lemma 5.9 and the endpoint count in (5.24). Merely restoring the endpoint count does not yield the claimed decay: the repaired argument charges the first and last higher-layer edges of the connecting path. The deterministic selection proof averages one chosen maximum, avoiding the separate assertion about the mass of all tied maxima. No failure of the theorem is claimed.

All of section 5 is now supplied with written proofs. The general many-cluster implication holds throughout 0<alpha<d; its unconditional fixed-rank conclusion uses d/3<alpha<d. No unique limiting law is identified. Section 6.1 has been read only through the statement of Lemma 6.2: the critical hydrodynamic contradiction, moment amplitudes and later sections remain to be completed.


## Hydrodynamics at the critical dimension

Reading update, 17 November 2026: section 6.1 has now been fully read in versioned HTML. The corrected passages were compared with extracted PDF text on printed pages 54–61. No journal-formula or visual-PDF comparison is claimed.

| Source passage | Treatment |
| --- | --- |
| Lemma 6.3, finite-volume application | [LHKO](../articles/hierarchical-runaway.md#section-finite-mean-derivative) sends ghost intensity to zero in finite OSSS and sums the resulting tail derivatives. |
| Lemma 6.2 and terminal good scales | [NHNY](../articles/hierarchical-runaway.md#section-critical-capped-scales) proves the critical capped alternative, with a fixed-cap backward argument and a strict third-moment growth contradiction. It separately transfers smallness to terminal rooted volumes. |
| Conditional growth before (6.13) | [837P](../articles/hierarchical-runaway.md#section-conditional-two-cluster-growth) retains both first-edge escape factors and constants independent of the cap and tolerance. |
| (6.14)–(6.17) | [EH4L](../articles/hierarchical-runaway.md#section-suppressed-layer-edges) conditions on a finite transcript and charges uninspected next-layer edges between the previous clusters. BK on disjoint witnesses bounds the weighted smaller-cluster product. |
| Theorem 6.1 | [UL8V](../articles/hierarchical-runaway.md#section-critical-hydrodynamics) proves hydrodynamics at d=3alpha and discharges that premise in the earlier moment-ratio, concentration and volume-biased results. |

Three new [provisional errata](../errata/hutchcroft-hierarchical-volumes-2022.json) record the cap sign, upper-limit and drift bookkeeping; the rooted normalization and terminal-time transfer; and the suppressed-edge index and conditioning. The proof keeps the source's strategy and conclusion. The corrected survival exponent has the additional fixed factor L^(-(d+alpha)), which preserves the contradiction.

Sections 2–5 and the critical hydrodynamic argument are now supplied with written proofs. The finite-volume form of Lemma 6.3 is all this application uses; no infinite Dini-derivative claim is added. The opening and elementary recursion lemma of section 6.2 have been read, but critical logarithmic amplitudes, covariance asymptotics, the critical volume tail and section 7 remain. The squared-normal biased limit is now unconditional at the critical dimension, while the scale converting it to logarithmic moment amplitudes still needs the later covariance calculation.


## Covariance asymptotics and critical amplitudes

Reading update, 17 November 2026: sections 6.2–6.3 are now fully read in versioned HTML. The disputed calculations were compared with extracted PDF text on printed pages 62, 64–66 and 70–74. No journal-formula or visual-PDF comparison is claimed.

| Source passage | Treatment |
| --- | --- |
| Lemma 6.11; Theorem 6.12 as used here | [I2YU](../articles/hierarchical-runaway.md#section-cluster-fourth-moment) proves the ordered-discovery dependence statement by cluster conditioning, then the finite-valued convex comparison and a sufficient fourth-moment bound with coefficient three. The general unbounded-variable theorem is not added. |
| Lemma 6.9 | [C1BP](../articles/multiplicative-coalescent.md#section-norm-covariance-equations) gives both exact covariance equations; independent-child gluing is [after 54V4](../articles/hierarchical-block-coalescent.md#section-coalescent-gluing). |
| Propositions 6.5 and 6.10 | [LWRN](../articles/hierarchical-runaway.md#section-leading-norm-correlations) controls every remainder and proves the two covariance constants by stable ratio equations. |
| Corollaries 6.6–6.7 | [5B41](../articles/hierarchical-runaway.md#section-first-mean-correction) supplies the geometric domination needed for the future-scale series and corrects the terminal endpoint of the time integral. |
| Lemma 6.4 | [S23T](../articles/hierarchical-runaway.md#section-polynomial-recursion) proves the general decay law by inverse-power increments. |
| Theorem 1.6 and critical biased scaling | [WQ7B](../articles/hierarchical-runaway.md#section-critical-logarithmic-amplitudes) recomputes the logarithmic amplitudes from the exact corrected mean series, then converts initial block moments to terminal rooted moments. |
| Remark 6.14 | The standard-normal fluctuation assertion remains a conjecture. Its even kth moment is (k-1)!!, not (2k-1)!!. |

Four new [provisional errata](../errata/hutchcroft-hierarchical-volumes-2022.json) include a substantive correction to the amplitude in the cited version. The time integral from u to 1 must vanish at u=1; the printed expression does not. The corrected mean profile also satisfies exact gluing at the two time endpoints. Its integrated decrement is positive even when its pointwise integrand changes sign. The resulting exponents agree with the source, while the terminal moment constants are c1=(1-q)/(beta_c q) and D=1/[2 sqrt(beta_c q(1+q+q²))], q=L^-alpha.

The fourth-moment repair proves a sufficient bound with coefficient three and does not claim a counterexample to the sharper printed inequality. All correspondences remain pending. The critical volume-tail proof in section 6.4 has been read through HTML2593 but not yet supplied; its remaining optimization, endpoint conventions and section 7 are next. The fluctuation conjecture and the general unbounded-variable version of the cited convex-comparison theorem remain outside the proved assertions.


## Critical full-cluster tails and the closing questions

Reading update, 17 November 2026: all of section 6.4 and section 7 has been read through HTML2662. The tail proof was compared with extracted PDF text at printed pages 75–77, and Theorem 1.7's threshold range was checked at printed page 10. Section 6.4 now has the following written treatment.

| Source passage | Treatment |
| --- | --- |
| Lemma 6.15 | [9GFG](../articles/hierarchical-runaway.md#section-critical-small-volume) proves the uniform small-volume mean bound from the biased limit, with the finite initial segment and level zero handled explicitly. |
| (6.30)–(6.32) | [F62A](../articles/hierarchical-runaway.md#section-critical-ghost-absorption) conditions on the truncated cluster and uses the last omitted-layer edge before an outside green connection. The row sum includes higher-layer copies within the same block. Both comparison constants are retained when choosing the absorption tolerance. |
| Theorem 1.7 and (6.33) | [FMVJ](../articles/hierarchical-runaway.md#section-critical-volume-tail) proves matching full-volume tails, explicitly balances the integer level, and interpolates the lower bound between successive levels. It also gives the small-intensity ghost equivalent up to constants and the exact positive-moment threshold. |

The bound is proportional to m^(-1/2)(log m)^(1/4) for m>=2. Its proof uses the corrected block-moment amplitudes only through positive comparison constants, so the logarithmic exponent is unchanged. A new [provisional erratum](../errata/hutchcroft-hierarchical-volumes-2022.json) records the undefined level-zero scale and the incorrect all-positive-intensity range after optimization. The source's Theorem 1.7 already has the correct threshold restriction. The unparenthesized logarithm in the scale choice is made explicit, without diagnosing a separate error on typography alone.

Section 7 is a source-era discussion of possible periodic-block limits, low-dimensional renormalization fixed points, other universality classes, and conformal invariance. Conjecture 7.1 asks for convergence of the critical orbit to a nonzero fixed point; Problems 7.3–7.4 ask for a nonzero fixed point and a characterization of the percolation limit among such points. These are recorded as the cited version's questions, not as a claim about their present research status. Its exact quotient-kernel construction, the Feller input for the coalescent map, and the topology of orbit convergence still need separate audits before being stated as wiki assertions. The spin-system comparison is background and does not supply an input to the proved tail theorem.

All main proof sections 2–6 now have written treatments within the stated scopes. The general unbounded form of the convex-comparison theorem, Gaussian fluctuation conjecture, exact section 7 constructions and comparable-kernel extensions remain distinct coverage tasks. Formal associations are still pending.


## Periodic blocks and renormalization

Reading update, 17 November 2026: section 7's constructions have been compared with extracted PDF text on printed pages 77–80. The external coalescent input was checked in Aldous, *Brownian excursions, critical random graphs and the multiplicative coalescent*, [Proposition 5, p.818](https://doi.org/10.1214/aop/1024404421), with its state-space definition at p.814 and proof in section 4.2, pp.836–843. This remains an explicit cited theorem; no visual-PDF audit or independent reconstruction of the infinite-state coalescent theorem is claimed.

| Source passage | Treatment |
| --- | --- |
| Section 7.1, quotient kernel and final coalescent time | [YY9S](../articles/hierarchical-block-coalescent.md#section-periodic-block-kernel) uses the quotient by the tail subgroup and computes the constant q/(1-q). This preserves the intended shell calculation. Periodic cluster-size predictions remain conjectural source discussion. |
| Section 7.2, definition and continuity of the map on cluster laws | [7VHT](../articles/hierarchical-runaway.md#section-renormalization-map) proves continuity of ranked combination and uses the cited Feller kernel to obtain continuity on probability laws. It verifies every scaling factor in the orbit identity. |
| Critical-parameter characterization and Remark 7.2 | [NIXH](../articles/hierarchical-runaway.md#section-critical-orbit-topology) proves the zero-limit criterion using sharpness and a uniform critical probability bound. Above and at the critical dimension, the sup norm vanishes while squared l2 norm tends to L^alpha-1; the laws are therefore not tight in l2. The corresponding norms diverge for p<2 and vanish for p>2. |
| Conjecture 7.1 | Low-dimensional tightness and positivity of limiting coordinates are already proved. A limit of the entire orbit would be fixed by continuity, but convergence of that orbit is not asserted. |
| Section 7.2, spin-system comparison | [YXL0](../articles/hierarchical-runaway.md#section-spin-comparison) gives the negative-gradient identity, the exact ordered-pair block recursion, a finite partition-function domain and the Gaussian fixed point. Non-Gaussian fixed-point and universality discussions remain attributed background. |

Two new [provisional errata](../errata/hutchcroft-hierarchical-volumes-2022.json) distinguish the finite coordinate subgroup from the tail subgroup defining the quotient, and align the spin energy's sign, pair convention and normalization domain. The topology discussion is stated through explicit coordinate and norm limits; no separate error is diagnosed from the source's use of the word “vague”.

The percolation map is defined on all probability laws on nonnegative decreasing square-summable sequences by the cited coalescent theorem. The spin map has an integrability restriction, already visible for Gaussian inputs. These are different state spaces and constructions. Problems 7.3–7.4, periodic scaling predictions and conformal-invariance expectations remain the cited version's research questions; this map does not assert their current status or solutions. All sections 2–7 now have written treatments or explicitly identified inputs and conjectural scope. General unbounded convex comparison, the fluctuation conjecture, model extensions and the journal-version audit remain separate tasks.


## Finite-window consequences of ordered discovery

The finite-valued comparison in the written [I2YU proof](../articles/hierarchical-runaway.md#section-cluster-fourth-moment) now has a separate finite-window extension, [WR5S](../articles/cluster-partitions.md#section-window-convex-comparison). It counts each full-cluster intersection at its first observed vertex. The joint-tail inequality passes through finite-edge exhaustion because the partition of a finite window eventually stabilizes, even if the full clusters are infinite. Convex comparison with independent copies gives a centered exponential bound for every real parameter.

[SARI](../articles/cluster-partitions.md#section-window-concentration) deduces a Gaussian lower tail with moment bound E S_(2p), and Bennett and Bernstein upper tails with a deterministic bound on each observed block's pth power. For squared mass, E S_4=o((E S_2)^2) gives the stated relative lower-tail estimate without a largest-block assumption. A random largest block cannot be substituted for the deterministic upper-tail bound.

These are new deductions from the existing written proof, not statements attributed to the paper or to the Lean library. No new source passage or paper correction is claimed; the existing provisional errata are unchanged. All discovery variables remain bounded, so this extension does not settle the general unbounded-variable comparison. Independent mathematical review and formalisation remain pending.


## Integrable comparison and countable sums

Reading update, 20 November 2026: Theorem 6.12 and Remark 6.13 in section 6.3 were re-read in the versioned HTML, lines 2411–2426. Shao's publisher page at [DOI 10.1023/A:1007849609234](https://doi.org/10.1023/A:1007849609234) was checked for its abstract and bibliographic record; its subscription-only full text was not read in this pass. No new PDF or journal-version audit is claimed.

[3NBK](../articles/hierarchical-runaway.md#section-integrable-convex-comparison) now supplies the signed, integrable version of the comparison, allowing infinite positive convex expectations. It approximates each pair consisting of the preceding sum and the next increment, rather than assuming the dependence condition survives truncation of all increments. The proof then uses induction for convex Lipschitz tests and increasing supporting-affine approximants. [OCZT](../articles/hierarchical-runaway.md#section-summable-convex-comparison) adds the countable-sum consequence under summability of absolute first moments, with the convergence argument supplied explicitly.

This closes the integrable part of the comparison task left open in the earlier reading updates. Nonintegrable increments and conditionally convergent series remain outside the proved scope; the stronger assumptions for maximal-process comparisons have not been audited. Explicit first-moment assumptions are a scope choice, not a newly diagnosed source error. Existing provisional errata and all earlier tagged statements are unchanged. Independent mathematical review and formalisation remain pending.


## Published-version comparison

Reading update, 20 November 2026: the [publisher record](https://doi.org/10.1112/plms.70023) identifies the journal article in *Proceedings of the London Mathematical Society* 130(1), e70023 (2025), first published on 6 January 2025. [Caltech's repository record](https://authors.library.caltech.edu/records/yvmkn-8m670) identifies an openly available published PDF. These bibliographic records were inspected, but the PDF could not be retrieved during this pass. No journal formula, proof or page was compared.

The source's [errata record](../errata/hutchcroft-hierarchical-volumes-2022.json) now distinguishes the checked arXiv v1 passages from this pending journal comparison. All 23 diagnoses, their repair assessments and their provisional status are unchanged. It remains necessary to compare each affected passage before deciding whether a report also applies to the published article or has already been resolved there.


## Weak limits and the variance deficit

Reading update, 20 November 2026: Theorem 6.12 and Remarks 6.13–6.14 were re-read in the versioned HTML, lines 2418–2426 and 2515–2520. The published-version download remains inaccessible and the journal comparison remains pending; no new journal passage was read.

[MDB8](../articles/hierarchical-runaway.md#section-convex-weak-limits) proves that convex comparison survives weak limits when the independent comparison is uniformly integrable. This extends the earlier countable-sum passage whenever these limit hypotheses can be checked, without requiring absolute first-moment summability. Uniform integrability of squares and a vanishing second-moment gap identify the two limiting laws.

[25Z0](../articles/hierarchical-runaway.md#section-gaussian-comparison-criterion) gives a sufficient Gaussian criterion for ordered discovery sums: a Lindeberg bound on the individual centered contributions and a dependent variance asymptotic to the sum of their marginal variances. Its proof supplies the independent triangular-array limit, then uses convex comparison and the preceding rigidity lemma. Without the variance condition, only convex domination of subsequential limits by a Gaussian is obtained.

These are additional deductions, not statements attributed to the paper. The two model estimates are not proved here for hierarchical critical percolation. In particular, Remark 6.14 remains unresolved, and convergence of moments above order two is not claimed. All existing provisional errata and earlier tagged statements are unchanged. Independent review and formalisation remain pending.


## The independent comparison has the wrong variance for squared mass

Reading update, 20 November 2026: Proposition 6.5 and the ordered-discovery setup in Lemma 6.11 were re-read in the versioned HTML, lines 2185–2192 and 2427–2433. The journal-version comparison remains pending.

[VH4M](../articles/hierarchical-runaway.md#section-hierarchical-discovery-comparison) verifies the independent Lindeberg condition for every fixed integer power p≥2 in the critical exact model with d≥3α. Transitivity bounds the sum of squared discovery means by f_p f_(p+1)/L^(dn), which is negligible compared with f_(2p). The independent variance is therefore asymptotic to f_(2p), and the higher-moment equivalents give the required vanishing Lyapunov ratio. The bounds are uniform over intermediate time and deterministic vertex order.

For p=2, [Q7QG](../articles/hierarchical-runaway.md#section-hierarchical-discovery-variance-gap) combines this with LWRN's two-thirds variance equivalent. The variance-matching condition proposed in 25Z0 fails: the actual variance is asymptotically one third smaller than the independent comparison variance. Standardized subsequential limits have mean zero and variance one and are dominated in convex order by a Gaussian of variance three halves, giving exponential tail and moment bounds for those limit laws.

This resolves the checks left open in the preceding update for squared-mass discovery, without resolving Remark 6.14. The sufficient theorem 25Z0 remains valid, but cannot identify the hierarchical limit through this comparison. No new erratum, journal audit, higher-moment convergence or comparable-kernel extension is claimed. All older statements and provisional diagnoses are preserved; independent review and formalisation remain pending.


## Fixed moments of fluctuation subsequences

Reading update, 20 November 2026: the arXiv record still lists only v1. The author publication list links that preprint and the journal record; the Caltech public PDF again could not be read through its download route. No published passage was compared, so the journal-version audit remains pending.

[9FO5](../articles/hierarchical-runaway.md#section-independent-comparison-moments) proves an independent triangular-array moment lemma by grouping a fixed moment expansion into set partitions. Pair partitions survive; singleton blocks vanish and higher blocks are negligible. The proof includes the collision estimate for distinct pair indices, and transfers uniform integrability of every fixed power to variables dominated in convex order.

[V7MP](../articles/hierarchical-runaway.md#section-hierarchical-fluctuation-moments) applies this to the existing critical exact hierarchical estimates. For fixed integers p≥2 and j≥3, the ratio f_(pj)/f_(2p)^(j/2) is asymptotic to a fixed constant times (nu²/mu³)^(j/2−1), hence tends uniformly to zero. Independent discovery sums have Gaussian limits in every fixed moment. Actual power-sum fluctuations have uniformly integrable powers of every fixed order, so all their moments pass along any weakly convergent subsequence. Variance-normalized squared-mass fluctuations satisfy the corresponding Gaussian upper bounds with variance three halves.

This strengthens the preceding update's moment conclusions, without identifying the actual limit law. In particular, a separate proof of Gaussian distributional convergence would now imply all fixed Gaussian moments. The variance deficit remains nonnegligible, no exponential-moment convergence follows, and the estimates are not uniform in growing moment indices. No new source erratum, journal-formula audit, comparable-kernel extension or compiled association is claimed. All previous text and provisional errata are preserved; independent mathematical review remains pending.


## Gaussian limit for squared mass

Reading update, 20 November 2026: Proposition 6.5 and Remark 6.14 were re-read in the versioned HTML, lines 2474–2520. The latter proposes Gaussian fluctuations for the power sums; the new argument below concerns only p=2. The published-version comparison remains pending.

[J0DE](../articles/hierarchical-runaway.md#section-squared-mass-gaussian-limit) gives a complete centered-moment argument for the actual squared mass in the critical exact hierarchical model with d≥3α. The finite generator retains both the derivative of the mean and the diagonal subtractions. V7MP's fixed-order bounds control nonlinear drift and higher jump powers; concentration of the third power sum identifies the quadratic forcing. After normalization by 2 nu²/mu, the moment equation has the Gaussian recurrence. The exact independent-child multinomial formula supplies the initial values across levels and a second contraction.

This identifies a standard-normal distributional limit after division by the actual standard deviation, uniformly over the choice of intermediate times, and proves convergence of all fixed integer and absolute moments. It strengthens the preceding updates specifically for p=2 without changing the established one-third independent-discovery variance gap. General powers, joint or process limits, comparable kernels and exponential-moment convergence remain outside the result. The proof is an additional deduction, not a theorem attributed to the paper; independent mathematical review and Lean formalisation remain pending. All older reading records and provisional errata are preserved.


## Joint Gaussian limit for integer powers

Development update, 20 November 2026: [MFGT](../articles/hierarchical-runaway.md#section-joint-power-gaussian-limit) extends the preceding squared-mass argument to every fixed finite collection of integer powers p≥2, at a common intermediate time, in the critical exact model with d≥3α. The version scope remains the cited preprint's Remark 6.14; no new published-version comparison is claimed.

Normalize S_p−f_p by b_p=sqrt(mu)(nu/mu)^(p−1). The limiting Gaussian covariance is Sigma_(p,q)=(2p+2q−5)!!−(2p−3)!!(2q−3)!!. The proof derives the triangular centered drift and simultaneous jump moments from the finite generator. Uniform moment bounds make all higher jump terms negligible. A formal power-series identity verifies the covariance at every fixed pair of indices; a mixed-moment induction combines decay within a level with exact independent-child gluing. The argument bounds products of the transition matrices, rather than inferring contraction in a particular norm from their eigenvalues.

All fixed mixed moments converge uniformly over time, as do fixed absolute moments of real linear combinations. Each integer power sum divided by its actual standard deviation has a standard-normal limit. The actual variance divided by f_(2p) tends to 1−((2p−3)!!)^2/(4p−5)!!; in particular, the established 2/3 ratio for squared mass remains unchanged. The covariance matrix is positive definite and differs from the independent discovery comparison.

This is an additional deduction, not a theorem attributed to the paper. Noninteger powers, indices growing with scale, joint limits at several times, process limits, comparable kernels and exponential-moment convergence are not proved. Independent mathematical review, the journal-version comparison and Lean formalisation remain pending. The existing moment-index erratum now links MFGT and distinguishes its local notation fix from this separate, substantial proof. Its provisional status and found/notation classification are unchanged, as are all other errata. The earlier J0DE proof also receives a typographical correction: the missing backslash in one displayed convergence arrow is restored, with no change to its statement or argument.


## Gaussian dependence across finitely many times

Development update, 20 November 2026: [OQV3](../articles/hierarchical-runaway.md#section-multitime-power-gaussian-limit) identifies the joint law of the normalized integer power sums at finitely many times within a single coalescent layer. It uses the existing finite generator and moment estimates, not a newly read passage or a new journal comparison.

The deterministic clock is tau(u)=−log(1−(1−L^(−alpha))u). In this clock the limit is a stationary Gaussian Markov law with the drift A and marginal covariance Sigma from MFGT. Its covariance between clock times s≤t is Sigma exp(A-transpose(t−s)). In particular, the variance-normalized squared-mass covariance tends to sqrt(phi(v)/phi(u)) for u≤v, where phi(u)=1−(1−L^(−alpha))u.

The proof strengthens the normalized polynomial generator estimate to every fixed Lr, constructs the Gaussian transition covariances from the Lyapunov identity, and uses a backward transition polynomial to cancel the drift. Multiplication by past observations is justified by unconditional moment bounds and Hölder's inequality; no conditional hydrodynamic estimate is assumed. Repeated elimination of the last observation proves all fixed mixed moments. Gaussian moment determination and uniform integrability give the laws and fixed absolute moments of real linear combinations, uniformly over the ordered time tuples. Coincident times and the critical dimension d=3alpha are included.

This extends the common-time statement in the preceding update. Tightness in a path space, dependence across nested levels, noninteger or growing powers, comparable kernels and exponential-moment convergence remain separate. Independent mathematical review, the published-version comparison and Lean formalisation remain pending. All earlier statements, source records and provisional errata are preserved.


## Functional Gaussian convergence within a level

Development update, 20 November 2026: [Q4PO](../articles/hierarchical-runaway.md#section-functional-power-gaussian-limit) supplies the path-space step left open in OQV3. For each fixed finite collection of integer powers in the critical exact hierarchical model with d≥3alpha, the rescaled coalescent trajectories converge in Skorokhod J1 to the continuous time-changed stationary Gaussian process with the previously identified drift and covariance. Linear interpolations on any refining uniform grids converge in the uniform topology.

The proof retains the exact deterministic centering and scale in the drift. Its uniformly bounded fourth drift moment and squared bracket density, together with an O(eta) fourth jump rate, imply a maximal increment bound C(h²+eta h). This estimate is proved using the compensated fourth-power identity and Doob's inequality, rather than assuming a functional central limit theorem. A union bound gives an interpolation error probability C delta^(-4)(1/m+eta); the fixed-grid Gaussian laws then identify the path limit. The largest jump vanishes, and the supremum fourth moments are bounded, giving supremum-moment convergence for every order strictly below four.

No new source passage was read for this deduction. It resolves the within-level path-tightness limitation of the preceding update, while retaining the restrictions to fixed integer powers, the exact model and one level. Joint dependence across nested levels, comparable kernels, growing indices and exponential moments are not claimed. Independent mathematical review, the journal-version comparison and Lean formalisation remain pending. Every prior tagged statement, reading record and source erratum is unchanged.


## Gaussian dependence on a finite tree of blocks

Development update, 20 November 2026: [F7Q2](../articles/hierarchical-runaway.md#section-nested-power-gaussian-limit) couples the within-layer path limits across any fixed tree of nested blocks in the critical exact model, including d=3alpha. The block at each node uses its own truncated layers. A parent's initial normalized vector is exactly Q^(-1/2) times the sum of its terminal child vectors; its limiting dynamics add a fresh Gaussian innovation independent of the descendants.

The proof reveals descendants before ancestors and applies the existing backward polynomial identity in an enlarged filtration. Unconditional moment bounds control the weighted generator error, so no conditional hydrodynamic estimate is introduced. Independent leaves determine the joint Gaussian laws; marginal path tightness gives convergence in a finite product of Skorokhod spaces. All fixed observation moments converge, and supremum moments converge below order four. The explicit ancestor covariance gives terminal squared-mass correlation L^(-(d+alpha)h/2) at a fixed separation of h levels.

No new source passage or erratum is claimed. This resolves fixed nested-level dependence left open by the preceding update, while retaining fixed depth and fixed integer powers. Increasing depth, comparable kernels, noninteger or growing powers, exponential moments and full-law block restrictions remain outside the result. Independent mathematical review, the published-version comparison and Lean formalisation remain pending. Every earlier statement, reading record and provisional erratum is preserved.


## All fixed moments of the path supremum

Development update, 20 November 2026: [NC7F](../articles/hierarchical-runaway.md#section-gaussian-path-moments) removes the below-four restriction from the supremum-moment conclusions of Q4PO and F7Q2. The existing high-order jump estimates give maximal 2m-th increments bounded by C_m(h^m+epsilon_n^(m-1)h). The proof derives the martingale inequality from its compensated polynomial identity, interpolates intermediate jump rates and absorbs the maximum term by Young's inequality. It uses unconditional bounds throughout.

Every fixed positive supremum moment now converges for one layer and each fixed finite tree, and the uniform interpolation error tends to zero in each such moment. Expectations of continuous path observables with polynomial growth converge as well. No bound uniform in moment order, exponential-moment conclusion, growing-depth result or model extension follows. The earlier finite-dimensional and path statements remain unchanged. This is an additional deduction, with no new source passage or erratum; independent mathematical review, the journal comparison and Lean formalisation remain pending.
