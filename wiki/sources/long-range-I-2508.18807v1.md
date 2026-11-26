# Long-range I: spatial-limit reading map

Inspected [versioned HTML](https://arxiv.org/html/2508.18807v1), 15–16 November 2026, concentrating on §I.5.2–I.5.4. The arXiv version line is dated August 2025 while the rendered title displays August 2026. The PDF rendition has not been compared in this pass. This is a partial correspondence map, not a claim of full source coverage or formalization.

| Locators | Topic | Wiki disposition |
| --- | --- | --- |
| Definition I.5.1 | Four alternatives for the spatial theory | Retain the source’s kernel assumptions and model-specific alternatives; no unrestricted dimension claim |
| (I.5.16)–(I.5.20), Definition I.5.16 | Bounded-jump cutoff motion, exponential stopping and displacement kernel | [MWZ7](../articles/spatial-cutoff-moments.md#section-displacement-kernel); separate from full stable motion |
| Lemma I.5.17 | Existence of a displacement density | Fourier proof in MWZ7; [provisional first-moment-weight erratum](../errata/hutchcroft-lrp-1.json) |
| Proposition I.5.14 and Lemma I.5.27 | One-point moments and absolute mixed-moment bounds | [LDR1](../articles/spatial-cutoff-moments.md#section-displacement-asymptotics) proves the normalized Euclidean case above three alpha; [VMEJ](../articles/spatial-cutoff-moments.md#section-mixed-moment-bounds) gives the general size-bias bound |
| Lemma I.5.26 | Signed ODE estimate | [2KB9](../articles/marginal-ode.md#section-signed-forcing), with no prior O(h) assumption; provisional derivative-line typo recorded |
| Lemma I.5.28 | Exact mixed-moment differentiation | [1K61](../articles/spatial-cutoff-moments.md#section-mixed-russo) proves the two-cluster identity and countable-volume passage; the wrong cluster index in the HTML display is recorded provisionally |
| Lemma I.5.29 | Asymptotic factorization | [2VIE](../articles/spatial-cutoff-moments.md#section-high-dimensional-factorization) proves the d > 3 alpha error estimate under the stated absolute moment bounds; the missing radius power is recorded provisionally. Other model alternatives remain separate |
| Proposition I.5.30 | Diagram recurrences | [IX97](../articles/spatial-cutoff-moments.md#section-diagram-recurrence) gives a generating-function proof, including the general norm-ball normalization |
| Theorem I.5.21 | Polynomial mixed-moment asymptotics | [GY8M](../articles/spatial-cutoff-moments.md#section-mixed-hierarchy) closes the conditional induction. [HBLN](../articles/spatial-cutoff-moments.md#section-high-dimensional-mixed-limit) supplies its inputs for the Euclidean model with d > 3 alpha under 7F5O's endpoint assumptions |
| Corollary I.5.22 | Size-biased cutoff random-measure limit | Y3SX supplies tightness and moment determinacy once the polynomial asymptotics hold |
| Theorem I.5.24 and Remark I.5.23 | CRT scaling convention and reduced edge lengths | [45EB](../articles/size-biased-laws.md#section-reduced-tree-mixture) proves the chi-square/gamma mixture; the unit-mass reduced-tree distribution and spatial construction remain cited inputs |
| §I.5.4, opening normalization | Cutoff radius versus spatial radius | [57FJ](../articles/spatial-cutoff-moments.md#section-physical-normalization); provisional scale-index erratum |
| (I.5.49)–(I.5.50) | Added cluster mass and ghost comparison | [AYPN/L9YJ](../articles/size-biased-laws.md#section-added-mass) prove the last-exit comparison and the ordered regular-variation limit |
| Proof of Theorems I.1.9 and I.1.17 | Transfer of the cutoff double limit and large-volume conditioning | [BB3O](../articles/size-biased-laws.md#section-cutoff-removal) separates rare-event normalization, cutoff convergence and the no-atom condition |
| (I.1.11), Lemma I.5.34 | Factorial compact-test moments | [5VYE](../articles/spatial-cutoff-moments.md#section-green-moments) proves the continuum binary-tree integral bound under the stated Green-kernel bound and moment formula |
| Lemma I.5.32 | Spatial tightness | [ALO4](../articles/spatial-cutoff-moments.md#section-full-spatial-tightness) combines one fixed cutoff second moment with the added-mass estimate |
| Lemma I.5.35 | Resolvent rescaling to the Green kernel | [42PB](../articles/spatial-cutoff-moments.md#section-kernel-rescaling) proves domination and local L1 convergence for the normalized isotropic jump process and nondegenerate Brownian motion; general-norm estimates remain to be checked |
| Lemma I.5.36 | Canonical diagram limit and scale constants | [DX2Y](../articles/size-biased-laws.md#section-cutoff-ratio-laws) derives the fixed-ratio measure by undoing bias, with the factor 4 and all spatial Jacobians retained |
| Lemma I.5.37 and proof of Lemma I.5.33 | Local moments to total-mass-weighted laws | [W9BP](../articles/size-biased-laws.md#section-local-moment-identification) weights first by a local mass, then uses spatial tightness to obtain the canonical double limit |

The first part of §I.5.3 distinguishes integrated moment asymptotics from conjectural pointwise multipoint equivalents. Preserve that distinction. The source’s inverse-total-mass moment formula corresponds to ordinary size-biased moment measures after inserting one additional constant test; Y3SX makes that shift explicit.

The reconstruction of §I.5.4 separates the cutoff mixed-moment asymptotics, full volume tail, omitted-edge row estimate, fixed-cutoff second spatial moments, and existence and moment formula of the intended canonical measure. In the normalized Euclidean d > 3 alpha model, HBLN, 26NT, C4E9 and Z11O now supply the percolation inputs under 7F5O; existence and the moment formula of the canonical measure remain cited construction inputs. Those inputs are not inferred solely from volume moments. The isotropic kernel calculation is not a verification of every general-norm case in Definition I.5.1. No Lean scaling-limit theorem is claimed.


## Integral-tail normalization

A separate reading of the [versioned HTML](https://arxiv.org/html/2508.18807v1), Lemma I.2.10, on 16 November 2026 confirms the coefficient discrepancy reported. For index alpha below minus one, the tail coefficient is -1/(alpha+1), not 1/(1-alpha): the power s^(-2) already distinguishes them. The [provisional erratum](../errata/hutchcroft-lrp-1.json) gives the dominated-convergence repair and records the corresponding unmerged Lean statement at its inspected commit. This is the integral-tail theorem, separate from the fractional-index Laplace-tail equivalence [SLGY](../articles/regular-variation.md#section-karamata). No existing assertion is changed, and the PDF rendition, later editions and author confirmation remain unchecked at this location.


## PDF passage checks, 16 November 2026

The [versioned PDF](https://arxiv.org/pdf/2508.18807v1) was checked by text extraction at the six provisional errata locations below. These checks supersede the earlier unchecked-PDF notes for these passages only. Page numbers are the printed numbers, starting with the title page as page 1. No later edition, full-paper comparison or author confirmation is inferred.

| Location | Printed page | Result of the PDF text check |
| --- | --- | --- |
| Lemma I.2.10 | 26 | The tail coefficient is also 1/(1-alpha) for alpha below minus one; the recorded repair remains necessary. |
| Lemma I.5.17 | 72 | The weight is located, but extraction does not resolve whether the 2 is a norm subscript or a square. The first-moment diagnosis remains tied to the HTML; visual PDF verification is outstanding. |
| Lemma I.5.26 | 83 | The integral uses h(s)/s; the first derivative equality also omits the denominator r. |
| Lemma I.5.28 | 85 | The marked vertices are all summed over K; the comparison display (I.5.35) on the same page separates the two clusters. |
| Lemma I.5.29; (I.5.44) | 85; 91 | The earlier formula lacks the radius power that is explicit in the later recurrence. |
| Opening of §I.5.4 | 93 | The indices are also printed as -alpha and 2 alpha after the spatial change of variable. |

The [six errata records](../errata/hutchcroft-lrp-1.json) retain their corrections, Lean-impact descriptions and provisional status. The PDF title page is dated 27 August 2025, unlike the HTML title's 2026 date noted in the first pass; this rendition difference is not evidence of a separately verified revision.


The review retains the corrected constant and records tail measurability in the revised interface. This updates the earlier repair-request status, not the erratum’s provisional status; WIKI has not compiled that head, and integration of its dependency chain remains separate.


## Inputs to the subcritical volume argument, 16 November 2026

The HTML statements of Definitions I.1.3/I.1.5 and Theorems I.1.6/I.1.15/I.1.17 were read together with the PDF text at I.1.5 (pp. 7–8), I.1.6 (p. 10), and I.1.15/I.1.16 (p. 17). This is a statement and normalization comparison, not a new audit of the proofs of Parts I and III.

For Part II's high-dimensional correlation-length regime, d>3 alpha and alpha<2, Theorem I.1.6 supplies the critical cutoff moments and full half-power tail. The kernel is radial decreasing with a logarithmically integrable relative derivative error; its derivative constant and norm-ball volume are normalized to one. The cutoff integrates the derivative up to r, and beta_c remains the full-kernel critical point. Theorem I.1.15 under hydrodynamics supplies moment comparability at d=3 alpha without determining the slowly varying factor; the latter needs Part III's second-order analysis. The superprocess scale in I.1.17 is one quarter of the second-to-first moment ratio, whereas the subcritical volume scale uses the full ratio.

The [input table](../articles/cutoff-scaling.md#section-volume-inputs) separates these roles. A new [provisional erratum](../errata/hutchcroft-lrp-1.json) records the inverse-log sign in Remark I.1.16, confirmed in both text renditions. The [inverse calculation](../articles/marginal-ode.md#section-inverse-log-source) supplies the correction without changing QKHV's existing statement or claiming the model-specific transfer hypotheses have been proved.


## Critical upper-moment inputs for Part III

The generalized tree bound [65MV](../articles/multipoint-trees.md#section-generalized-tree-moments) now proves Lemma I.4.16 by retaining nonadjacent three-edge stars as three-point events. Under sharp cutoff susceptibility and ordinary hydrodynamics at d=3 alpha, [121D](../articles/cutoff-hydrodynamics.md#section-critical-second-moment-variation) proves the regular-variation conclusion of Proposition I.4.15. The upper hierarchy [RM79](../articles/cutoff-hydrodynamics.md#section-critical-volume-upper) then proves (I.4.19) without assuming the full higher-order factorization errors. These hypotheses are supplied by the Part III conditional hydrodynamic chain, with finite nonmonotone Reimer still explicit. This supplies the volume input of the norm-power mixed-moment reduction [AR3F](../articles/spatial-cutoff-moments.md#section-vertex-factor-mixed-upper); [YU52](../articles/spatial-cutoff-moments.md#section-radial-spatial-upper-moments) supplies its spatial input when alpha<2 for arbitrary normalized norms. Matching higher-moment equivalents and the later scaling-limit claims remain separate.


## Critical higher volume moments

[326J](../articles/cutoff-hydrodynamics.md#section-critical-volume-equivalents) completes the critical case of Proposition I.4.20. The upper bounds in RM79 are used at order 2p+2 to control the common-cluster deficit in (I.4.21); the normalized error tends to zero under ordinary hydrodynamics. The stable ratio equation then gives every double-factorial equivalent. The existing size-biased moment theorem yields a squared-normal limit and uniform negligibility of truncated mass relative to m2/chi. This does not assert a spatial random-measure limit or compute the vertex factor. The supply of the critical hydrodynamic hypotheses remains conditional on finite nonmonotone Reimer through BCKB.


## Critical general-norm spatial limits

[YHNS](../articles/spatial-cutoff-moments.md#section-critical-spatial-factorization) now supplies Lemma I.5.29 at d=3 alpha, alpha<2 under sharp cutoff susceptibility and ordinary hydrodynamics. The previously proved V -> 0 makes the unrestricted common-cluster error O(V^2) relative to the leading derivative scale; the proof keeps every labelled split and the joining radius power.

[AL0I](../articles/spatial-cutoff-moments.md#section-critical-spatial-tree-limits) supplies the one-point ODE boundary, then applies the existing mixed-hierarchy induction and moment-determinacy theorem. This completes the critical general-norm instances of Theorem I.5.21 and Corollary I.5.22 under those explicit model inputs. The existing conditional model verification retains finite nonmonotone Reimer. This is a single-cluster spatial law; no Part III interacting deficit limit or compiled result follows from it. The source's I.5.29 proof for Cases 1 and 4 was read for this extension; no new source erratum is diagnosed.
