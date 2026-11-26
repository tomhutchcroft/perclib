# Decision-tree inequalities and the finite three-point theorem

Read the introduction and sections 2 through 6.2 of Nikita Gladkov, [Percolation Inequalities and Decision Trees, arXiv:2408.08457v1](https://arxiv.org/html/2408.08457v1), 15 August 2024, on 16 November 2026. The [20-page PDF](https://arxiv.org/pdf/2408.08457v1) was compared at Theorem 4.3, Theorem 5.2, Corollary 5.3 and the two proofs in section 6 (printed pp. 6–9). This was a text comparison, not visual PDF review. No later version or journal rendition was compared.

The [wiki proof](../articles/adaptive-three-point.md) uses an invertible swap for the hybrid law, a four-case comparison for adaptive BK, and a leafwise second moment for the stopped exploration. Its DFS is specified recursively, including the open-edge test and complete processing before backtracking. It keeps separate copies of every independently resampled edge.

| Source result | Wiki proof |
| --- | --- |
| Lemma 3.1 | [Q3MP](../articles/adaptive-three-point.md#section-hybrid): predictable coordinate swaps preserve product weights, including endpoint probabilities. |
| Theorem 3.2 | [26TT](../articles/adaptive-three-point.md#section-harris): deepest-node removal works for increasing or decreasing events of the same direction. |
| Definition 4.2; Theorem 4.3 | [7LLO](../articles/adaptive-three-point.md#section-bk): witnesses may overlap only outside the shared set. |
| Theorem 5.2; Corollary 5.3 | [LNMI](../articles/adaptive-three-point.md#section-stopped): an exact leaf sum for independent completions and a lower bound for monotone adaptive continuations. |
| Section 6.2, stopped DFS geometry | [VN5Z](../articles/adaptive-three-point.md#section-dfs): completed branches force the continuation paths to meet the active stack through unshared edges. |
| Theorem 6.2, (13)–(14) | [C7UK](../articles/adaptive-three-point.md#section-three-point): the factor-eight product bound and the companion union bound, with zero-probability cases included. |

The [two provisional errata](../errata/gladkov-decision-trees-2024.json) concern contradictory bit states in the proof of Theorem 4.3 and the reversed inequalities in Corollary 5.3. Both are accompanied by a replacement argument; the second includes a finite counterexample to the displayed direction. No author confirmation or compiled correspondence is inferred from this reading.

The [existing countable extension](../articles/multipoint-trees.md#section-gladkov) now has its finite input proved. The resulting three-point theorem supplies the mixed-window input to the [radial good-scale argument](../articles/cutoff-hydrodynamics.md#section-good-scale-inputs-complete). The same article extends the stopped-tree geometry to prove the [higher-order inequality](../articles/adaptive-three-point.md#section-higher-order) from Part II, Theorem II.3.1; that extension is tracked in the [Part II source map](sources/long-range-II-2508.18808v1.md).

The planar improvement in section 6.1 was read to understand the comparison with the general graph proof; its planar geometry has not been supplied as a wiki theorem. Section 6.3 and sections 7–10 remain outside this reading and proof map. The later asymmetric, coloured, and multiple-path inequalities therefore remain coverage obligations.


## Three-vertex separation: section 7 completed

Sections 7.1–7.3 have now been read in the versioned HTML and compared with extracted PDF text on printed pp.11–13 (PDF indices10–12). Lemma 1.2 and Theorem 1.3 in the introduction were also checked. The wiki supplies the previously cited three-tree inclusion and the complete partition-probability calculation. This supersedes the section 7 gap above; the planar improvement, section 6.3 and sections 8–10 remain separate.

| Source result | Wiki proof | Scope |
|---|---|---|
| Lemma 7.1; Algorithms 3–5 | [HKLH](../articles/adaptive-three-point.md#section-three-resamplings) | Full cluster boundaries identify the three shared sets. A first-hit path proves the inclusion; complementary hybrids give the probability lower bound. |
| Lemma 1.2, (2); (17) | [VPUL](../articles/adaptive-three-point.md#section-separation-inequality) | Intended asymmetric form with intersections, zero-denominator conventions and a countable-graph passage. |
| Theorem 1.3; section 7.3 one-split implication | [QY7X](../articles/adaptive-three-point.md#section-rare-partitions) | Explicit epsilon-cubed/4 threshold for two rare split partitions, and a separate square-root error bound for one rare split. |
| Section 7.3 numerical bound | [5EMI](../articles/adaptive-three-point.md#section-extreme-partition-cap) | Two monotonicity calculations justify the cubic bound 0.3556691089... on min(all-connected, all-separated). Sharpness only for the relaxed probability inequalities is distinguished from percolation realizability. |

One additional provisional [erratum](../errata/gladkov-decision-trees-2024.json) groups the reversed first coupling bound, the unjustified equality substitutions and the union/intersection notation. The path with two probability-one-half edges disproves the first displayed direction, and complete K4 at probability one half makes the Cauchy–Schwarz step strict. The corrected argument preserves Theorem 1.3 and the numerical bound. The literal union formulation is weaker; it does not justify the partition identities used by the proof.

No visual-PDF or journal comparison is claimed: the screenshot service was unavailable and a direct PDF download returned HTTP403, while the primary HTML and extracted PDF were accessible and agreed on these displays. The new proofs apply to countable independent bond models with three distinct marks, without local finiteness or finite susceptibility. Correspondence records remain pending and no compiled Lean association is inferred.


## General comparisons and coloured configurations: section 8 completed

Section 8 was subsequently read in full in HTML and compared with extracted PDF text on printed pp.13–17 (PDF indices12–16), through Remark 8.8. This supersedes the section 8 gap above. All proofs below concern finitely many coordinates, as in the decision-tree setup; the preceding three-vertex separation results have their own countable extension.

| Source passage | Wiki treatment | Scope |
|---|---|---|
| Main Lemma8.1 | [9GXY](../articles/adaptive-three-point.md#section-sampling-comparison) | Conditional induction and integration of the section inequality; replaces the reversed law difference without identifying different paths. |
| Theorems8.2 and8.4 | [3CE7](../articles/adaptive-three-point.md#section-capacity-comparison) | The printed binomial capacity law is false for the claimed comparison. The exact admissible tail constraints and a maximal replacement law are proved, also for finite unions of witness pairs. |
| Theorem8.3 | 3CE7 with zero double-capacity probability | Complete proof of the finite-family BK comparison from the same section argument. |
| Theorems8.5–8.6 | [F2TD](../articles/adaptive-three-point.md#section-colour-comparison) | Normalized parity laws, full pairwise independence and adaptive triple comparison; finite coloured-percolation consequence included. |
| Theorem8.7 | [JOJ1](../articles/adaptive-three-point.md#section-triple-mixtures) | Explicit section masses prove the coordinatewise mixture comparison. |
| Remark8.8 | Model distinction and external-source boundary | A two-coordinate calculation distinguishes product mixtures from mixtures of whole configurations. The separate Richards-paper proof diagnosis and present status of its conjecture have not been independently audited. |

Three further provisional errata record the reversed general comparison formula, the false capacity-law statement and the parity-law normalization/support. The capacity entry includes an exact one-coordinate counterexample and a proved replacement; it is not merely a notational correction. All earlier entries are preserved. The source now has six provisional entries, with this follow-up appended. No new compiled association is asserted. The planar improvement, section6.3 and sections9–10 remain separate coverage obligations.


## Common-face exploration, decay and the final questions

Sections 6.1, 6.3 and 9–10 have now been read in the versioned HTML and compared with the extracted PDF, printed pp.8–10 and17–18. This supersedes the planar and multiple-path gaps above. The wiki proves the geometric exploration step rather than assuming that arbitrary DFS preserves the residual path count.

| Source passage | Wiki treatment | Scope |
|---|---|---|
| Algorithm2; planar searches in sections6.1 and9 | [KPT4](../articles/adaptive-three-point.md#section-planar-peeling) | Outermost-path proof, uncrossing of edge-disjoint families, complete leaf replay, cut vertices and repeated face-boundary visits. |
| Theorem6.1; Remark6.3 | [8XA9](../articles/adaptive-three-point.md#section-planar-three-point) | Factor two, strengthened to a denominator of one plus the largest pair probability by finite-family adaptive BK. |
| Theorems1.5 and9.1 | [YQEG](../articles/adaptive-three-point.md#section-planar-multipaths) | Full allocation of shared and unshared paths, including zero cases and countable common-face exhaustions. |
| Corollary6.5 | [9ZC5](../articles/adaptive-three-point.md#section-three-point-decay) | Correct pair-distance consequence and separated-triple bound. The printed negative-exponent diameter claim has an exact counterexample on the infinite line. |
| Section10, Poisson example | [TIKW](../articles/adaptive-three-point.md#section-poisson-paths) | Tail inversion with extended endpoints and a proof of the binomial route limit; the path success probability is specified. |
| Conjectures1.4,10.1,10.2 | Historical inventory after TIKW | Clearly distinguished from the proved common-face inequalities and the two-rare-partition consequence. No current-status claim. |

Two further provisional [errata](../errata/gladkov-decision-trees-2024.json) record the planar proof's equality/search conventions and the false diameter-only corollary. The former preserves the theorem and includes a strict triangle calculation; the latter replaces the conclusion with a proved bound retaining pair separation. The source now has eight provisional entries. Both follow-ups belong, pending Tom's confirmation.

The main finite decision-tree, three-point, separation, sampling and common-face multiple-path results now have written proofs or explicit corrected replacements in this map. This does not complete every external implication cited by the paper. Remark6.4's randomized DFS balance, section6.3's RSW/scaling-limit assertions and numerical constants, and Remark8.8's Richards/Sahi discussion still require their own primary-source proofs or reconciliation. The source conjectures are not claimed resolved. All new correspondence records remain pending; no new Lean association, journal comparison or visual-PDF review is inferred.


## The randomized DFS input in Remark 6.4

Remark6.4 is now supplied by the primary [Gladkov–Pak maze source](sources/gladkov-pak-mazes-2408.00978v1.md). [KRU2](../articles/adaptive-three-point.md#section-fair-dfs) proves the pivot involution under the necessary degree-three and leaf hypotheses. [04ZU](../articles/adaptive-three-point.md#section-balanced-bond-search) makes those hypotheses available for arbitrary finite bond models through a fixed connectivity-preserving expansion, before sampling the bonds. This supersedes the randomized-DFS gap recorded above.

[TWYR](../articles/adaptive-three-point.md#section-balanced-three-point) includes the seed in the stopped transcript and proves the source's displayed bound. It also retains the finite-family subtraction, giving `(1+4r_b)t²<=8r_b tau_ac tau_bc`, with the analogous c-bound, and passes to countable graphs through finite witnesses. The argument does not claim ordinary uniform-neighbour DFS is balanced on an arbitrary unsplit graph. The existing eight provisional errata are unchanged. External RSW/scaling-limit assertions and the Richards/Sahi discussion remain separate obligations.


## Primary-source reconciliation of Remark8.8

The [Richards map](sources/richards-higher-correlation-math0410155v1.md) now identifies the discrete conditioning gap, with the exact missing covariance identity and a sign example in ICQP. This is recorded provisionally, not as a counterexample to the global inequality. The [Sahi map](sources/sahi-higher-correlation-2008.md) supplies the all-order positive-cumulation theorem and its genuine restriction; the [Lieb–Sahi map](sources/lieb-sahi-higher-correlation-2107.09838v2.md) supplies the three-function square proof. These complete the previously deferred primary-source reconciliation, while the general conjecture's current status and the remaining all-n square/rectangle proofs stay separate. JOJ1's coordinatewise mixture theorem is unchanged. External RSW/scaling inputs remain queued.


The same continuation also completes the main general-order arguments of Lieb–Sahi: [rectangle positivity](../articles/adaptive-three-point.md#section-rectangle-correlations), [all-order two-chain positivity](../articles/adaptive-three-point.md#section-two-chain-all-orders), and [formal-series equivalence](../articles/adaptive-three-point.md#section-correlation-equivalence). The unrestricted many-coordinate conjecture is still not used as an input.


## Scaling claims reconciled with the primary references

Section6.3 now has written proofs of [K8A1/UQ4B](../articles/critical-exponents.md#section-planar-three-point-scales), retaining the smallest pair scale, and [6BFG](../articles/adaptive-three-point.md#section-supercritical-separation), retaining uniqueness. RSW itself remains the cited input WD31.

The [boundary citation correction](../errata/gladkov-decision-trees-2024.json#boundary-scaling-scope) is provisional. [Beliaev–Izyurov](sources/beliaev-izyurov-1011.5822v3.md) and [Conijn](sources/conijn-factorization-1502.04387v3.md) prove triangular-site results with two boundary marks and one bulk mark, not the square-bond/all-boundary assertion attributed to them. XCYH proves the constant calculation; JM5A remains a cited scaling theorem.

The bulk announcement now has an exact later reference, [Ang–Cai–Sun–Wu v4](sources/ang-cai-sun-wu-2107.01788v4.md). R9NU records its triangular-site theorem, keeping the [Delfino–Viti prediction](sources/delfino-viti-1009.1314v1.md) and [SZK numerical/CFT evidence](sources/simmons-ziff-kleban-0811.3080v1.md) distinct. External SLE/CLE proofs and square-bond universality remain uncovered; no formal association is asserted.
