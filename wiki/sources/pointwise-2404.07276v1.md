# Pointwise long-range estimates: reading map

Source: Tom Hutchcroft, [arXiv:2404.07276v1](https://arxiv.org/html/2404.07276v1), *Pointwise two-point function estimates and a non-pertubative proof of mean-field critical behaviour for long-range percolation*. The submission metadata says10April2024; the HTML title date says24August2026. This map fixes the v1 identifier without claiming that every rendition is identical.

Read on17November2026: the introduction and all of section2.1 in HTML. The random-box and analytic-bootstrap proof displays were compared with extracted [PDF text](https://arxiv.org/pdf/2404.07276v1) on printed pp.7–10. No visual-PDF or journal-version audit. The opening statements of section2.2 were read, but its proof, sections2.3–2.4 and the cited near-critical asymptotic paper remain separate tasks.

| Passage | Wiki treatment | Scope |
|---|---|---|
| Theorem1.1 | Pending application | Triangle and mean-field consequences require the later source proofs and comparison with existing diagram/quantitative-triangle articles. |
| Conjecture1.3; crossover discussion | Historical source statement | No new proof or current-status claim. |
| Theorem1.4; Proposition2.1 | [TGF9](../articles/pointwise-long-range.md#section-critical) | Upper half proved from the existing averaged theorem. Pointwise lower half remains separate. |
| Theorem1.5; Remarks1.6–1.7 | Statement read | Half-susceptibility radius and near-critical range retained. The critical upper bound alone does not prove the far-field crossover. |
| Lemma2.2 | [0VB3](../articles/pointwise-long-range.md#section-translated) | Actual opening probabilities and explicit centre-count factor. The probability decomposition does not require alpha<1. |
| Proposition2.1 proof | [PIZX](../articles/pointwise-long-range.md#section-bootstrap) | Analytic contraction with an independent averaged-bound premise; short shells supply the alpha<1 restriction. |
| Use in Long-rangeII §II.2.2 | [Localization dependency](../articles/pointwise-long-range.md#section-localization) | TGF9 supplies YUHF's pointwise upper input for dominated cutoffs. The cutoff susceptibility lower bound is separate. |

The [provisional errata](../errata/hutchcroft-pointwise-2024.json) record the translated-centre intervals/domain and the far-shell exponent/induction ranges. The repaired proof retains the pointwise upper-bound conclusion. The corrections are recorded as a separate source section; no new issue or PR is opened.

The lower critical kernel envelope supplies the nontrivial transition and MRZO's averaged upper bound. PIZX uses only an upper bound on centred spatial sums and the translated-box inequality; it does not use localization or pointwise lower estimates. This breaks the potential circularity in treating the earlier pointwise theorem as an input to YUHF. All source correspondences and compiled associations remain pending.


## Near-critical upper bound: continuation on 17 November 2026

All of section 2.2 has now been read in HTML and compared with extracted PDF text on printed pp.10–12 (PDF indices9–11). This completes the upper-bound tasks left pending above. Section 2.3 has been read in HTML; its later displays and section 2.4 still need a separate detailed PDF audit and reconciliation with the existing diagram and lower-bound articles.

| Passage | Wiki treatment | Scope |
|---|---|---|
| Lemma 2.4 | [AXYA](../articles/pointwise-long-range.md#section-half-susceptibility) | Proves the stronger internal-mean implication using PTM2, 31X5 and YLZV. |
| Corollary 2.5; Proposition 2.3 | [6G4B](../articles/pointwise-long-range.md#section-half-susceptibility) | Both kernel bounds retained. Susceptibility and internal box means are compared with the half-mass radius, including the initial scale. |
| Lemma 2.6 | [SFR0](../articles/pointwise-long-range.md#section-two-crossings) | Weighted row sums and separated three-kernel convolution for 0<alpha<1; the regularized origin is included. |
| Proposition 2.3 / proof headed Theorem 1.5 | [CQK2](../articles/pointwise-long-range.md#section-near-critical-upper) | The uniform crossover upper bound follows by a finite-amplitude contraction, two independently averaged boxes and finite-path approximation. |

The nearest-neighbour kernel on the one-dimensional lattice disproves Corollary 2.5 under its upper-only envelope. The repaired statement uses the two-sided hypotheses already present in Proposition 2.3. A second provisional entry records the long-edge event's missing terminal vertex, the centre near x, and the short-edge constraint needed for the middle convolution. Both are appended to the same source's [errata](../errata/hutchcroft-pointwise-2024.json), linked.

CQK2 establishes the source's upper half directly. It does not discharge the derivative or cutoff assumptions of TFKR, identify two different correlation-length definitions, prove a pointwise lower bound, or certify a Lean association. All correspondence records remain pending.


## Matching lower bound and triangle diagram, same continuation

The remaining proof sections 2.3–2.4 have now been compared with extracted PDF text on printed pp.13–15 (PDF indices12–14), including the intermediate triangle displays and every joining-edge moment step. This supersedes the later-PDF task noted above. No visual-PDF or journal comparison is claimed.

| Passage | Wiki treatment | Scope |
|---|---|---|
| Proposition 2.8 | [TQ77](../articles/pointwise-long-range.md#section-near-critical-lower) | Confined pointwise lower bound, uniformly for beta_c/2<=beta<=beta_c, with a separate direct-bond treatment of bounded radii. |
| Theorems 1.4–1.5, two-point estimates | TGF9, CQK2 and TQ77 | Matching critical and near-critical two-point bounds are now proved under the global two-sided power envelope and alpha<1. |
| Section 2.3 through (2.7) | [RCTO](../articles/pointwise-long-range.md#section-triangle-crossover) | Triangle bounded above, logarithmic in the half-mass radius, or bounded by its power; finite critical triangle when d>3alpha. |
| Theorem 1.1 consequences; Remark 2.7 | Further cited-input task | The polynomial susceptibility bound needed to replace log xi by log of distance to criticality, quantitative triangle consequences and exponent comparison inequalities require separate reconciliation. The printed beta-to-infinity in Remark 2.7 is a limiting-parameter typo; the argument concerns beta increasing to beta_c. Historical conjectures are not current-status claims. |

Two more provisional entries record the joining-pair count/internal-mean issue and the triangle prefactor/radial-range issue. The original two entries and the two near-critical upper entries are preserved. All six source entries remain provisional. The lower proof uses 12NL and BZDZ, already written in the wiki, rather than leaving universal tightness as an unproved premise. The critical-window quantile is bounded directly by MRZO and ordered-pair counting.

The primary two-point arguments are now covered in prose. This does not mean every external theorem invoked by the source is proved here, nor that the paper's main theorems have compiled Lean associations. The model uses the supremum norm; equivalence with other fixed norms changes constants but not exponents.


## Quantitative consequences and Remark 2.7

Theorem 1.1 and the closing paragraph of section 2.3 are now reconciled with the corrected triangle inequality already proved in the wiki. Remark 2.7 was checked against extracted PDF text on printed p.14 (PDF index13), lines1066–1094. This completes the consequences left pending above, within the explicit hypotheses below; no visual-PDF or journal comparison is claimed.

| Passage | Wiki treatment | Scope |
|---|---|---|
| Section 2.3: logarithm of the half-mass radius versus parameter distance | [GQJY](../articles/integrated-susceptibility.md#section-self-diagram), [A3S7](../articles/pointwise-long-range.md#section-mean-field-consequences) | Directly integrate the corrected square with a diagram bounded by a logarithm of susceptibility. The first polynomial estimate justifies the logarithm conversion; no additional cited polynomial-susceptibility theorem is required for this application. |
| Theorem 1.1 | A3S7 and [QW2L](../articles/integrated-lower-tails.md#section-logarithmic-pointwise) | Matching mean-field bounds above the critical dimension. At d=3alpha<3, triangle O(log(1/epsilon)), susceptibility between epsilon^-1 and epsilon^-1 log²(1/epsilon), critical tail between n^-1/2 log^-2(n) and n^-1/2 log²(n), and density between epsilon and epsilon log²(1/epsilon). |
| Remark 2.7, susceptibility | [YYSP](../articles/pointwise-long-range.md#section-near-mean-field) | Same power alpha/(2d-5alpha), with beta increasing to the finite beta_c and the corrected square. Gamma is bounded only if its defining limit exists. |
| Remark 2.7, limiting exponents | LKWW in the same section | For alpha<4d/11, entropy and integrated-tail estimates bound any existing delta and order exponent. This neighbourhood suffices to squeeze all three exponents to their mean-field values as alpha decreases to d/3. No monotonicity or existence assertion. |

The additional provisional [source entry](../errata/hutchcroft-pointwise-2024.json) corrects the limiting parameter and records how the already identified stronger-numerator issue is bypassed. All six earlier entries are preserved. The argument normalizes the intensity row and retains its derivative factor, obtains local absolute continuity and endpoint divergence from the existing proofs, and distinguishes integrated from pointwise lower tails.

The primary two-point theorems, Theorem 1.1 and the stated limiting-exponent consequences now have written proofs within the global two-sided power-law hypotheses and alpha<1. This does not reproduce every external reference or settle the paper's conjectures. In particular, the predicted exact logarithmic corrections remain predictions rather than consequences of the displayed bounds. Source correspondences and compiled Lean associations remain pending.
