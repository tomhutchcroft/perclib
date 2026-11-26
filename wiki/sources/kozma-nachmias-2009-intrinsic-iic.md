# Kozma–Nachmias: intrinsic IIC volume and resistance

The primary source is Gady Kozma and Asaf Nachmias, *The Alexander–Orbach conjecture holds in high dimensions*, Inventiones mathematicae 178, 635–654 (2009), [DOI](https://doi.org/10.1007/s00222-009-0208-4). This map checks Section 2 of [arXiv:0806.1442v2](https://arxiv.org/pdf/0806.1442v2), printed pp.10–15 / PDF indices9–14, in extracted text. The publisher version and visual pages have not been compared. This is scoped coverage, not a full-paper reading claim.

| Source locator | Wiki treatment |
|---|---|
| Lemma 2.2, pp.11–12 | The existing [short-path tree bound](articles/incipient-cluster-limits.md#section-short-tree), 0HRJ, contains the three-branch moment argument. KIGU and Z78U already provide the limiting first moment and a stronger exponential upper-volume tail under their explicit hypotheses. |
| Lemma 2.3, p.12 | [KGPE](articles/incipient-cluster-limits.md#section-boundary-density) makes the stopped exploration explicit. Under susceptibility bias, expected residual cluster mass is bounded by boundary size times susceptibility, plus the finite explored mass. Under distant-point conditioning, the analogous comparison has the stated fixed-shift ratio constant L. [RG3Z](articles/incipient-cluster-limits.md#section-quadratic-volume) selects the first small positive sphere and obtains the lower tail of order epsilon. Positivity excludes extinct critical clusters. |
| Lemma 2.5, p.13 | [3FTE](articles/incipient-cluster-limits.md#section-history-transfer) proves the square-root event comparison for the susceptibility-biased and ratio-controlled distant-point limits. Averaging limiting sphere means precedes the threshold split; the chosen radius is deterministic. |
| Lemmas 2.4 and 2.6, pp.13–14 | [POD2](articles/incipient-cluster-limits.md#section-intrinsic-resistance) gives the cutset energy proof and bounds the total number of extendible crossing bonds directly. Each residual graph is treated with the uniform subgraph arm bound, never with an unsupported monotonicity assertion for intrinsic sphere events. The maximum-degree factor is retained in the explicit constant. |
| Theorem 2.1 and the conclusion of Section 2, pp.11,14–15 | The source invokes a separate random-walk theorem of Barlow–Járai–Kumagai–Slade. The wiki does not invoke or prove that input here. Spectral dimension, walk displacement and heat-kernel conclusions remain separate. |

The source's Section 2 uses distant-point conditioning under spatial two-point estimates. The susceptibility-biased extension is proved separately in KGPE and uses no spatial estimate: finite triangle supplies the critical tail and linear ball mean, while the existing uniform subgraph arm theorem supplies the arm bound. The almost-sure volume and resistance exponents are deductions from the displayed tails. They hold for every cylinder limit with the stated hypotheses and do not prove uniqueness, full-sequence convergence, equality of constructions or one-endedness.

The filtration reveals bonds incident to the preceding intrinsic ball and leaves the current sphere's internal bonds unexposed. This fixes the precise independence used in the exploration without treating the paper's ball notation as a new erratum. No new error in a published paper, author confirmation, compiled association or independent audit is claimed. Section 3.1's reverse-BK argument remains outside this work and with FIXER.


## Return probabilities from the intrinsic estimates

The random-walk task left separate above is now partly completed in [331W/KGNK/NNW7](articles/iic-random-walk.md#section-green-exit). Killed Green functions give the mean-exit bounds, a lazy spectral estimate gives the upper return bound, and survival inside a ball gives the lower return bound. An explicit binomial comparison transfers the logarithmic exponent to ordinary walk at even times. [IXCJ](articles/iic-random-walk.md#section-iic-spectral-dimension) applies this argument to RG3Z/POD2, proving recurrence, quenched mean exit exponent three and spectral dimension four thirds. The [primary random-walk map](sources/barlow-jarai-kumagai-slade-2007-walk.md) identifies the checked passages. Sample-path displacement and range, annealed estimates and full IIC identification remain separate; no new erratum or formal status is asserted.


## Pathwise consequences

[HJKG](articles/iic-random-walk.md#section-iic-paths) now supplies the pathwise consequences left separate above: exit exponent three, maximum-distance exponent one third and vertex-range exponent two thirds. LCUN/7WII/YIJB give the hitting, exit-tail and missed-volume proofs, with degree mass distinguished from vertex cardinality. The fixed-time displacement exponent holds in walk probability, not almost surely. Annealed heat-kernel estimates and identification of IIC constructions remain separate; no prior erratum or formal status is changed.


## Averaged walk estimates from the established geometry

[G85Z](articles/iic-random-walk.md#section-iic-annealed) now proves annealed return probabilities of order $n^{-2/3}$, mean exit times of order $r^3$, and a mean intrinsic displacement lower bound of order $n^{1/3}$ for the same susceptibility-biased and ratio-controlled distant-point limits. The upper return proof uses RG3Z's linear lower-volume tail through a threshold-dependent radius; it does not assume an inverse-volume moment or average an almost-sure logarithmic limit. The BJKS source map records the additional primary-source passages read. Equality of IIC constructions, a matching upper mean-displacement bound and limiting constants remain separate.


## Quantitative joint walk laws

[YWT9](articles/iic-random-walk.md#section-iic-tightness) now turns the established volume and resistance tails into tightness at intrinsic displacement scale $n^{1/3}$ and exit scale $r^3$, under the joint environment-and-walk law. The maximum-distance tail has the sufficient power $3/47$, and the fast-exit bound has power $1/47$. Positive and negative moment ranges are stated explicitly; the negative displacement moments use one plus distance. These are written deductions from the existing finite-triangle geometry, with the distant-point ratio assumption retained. They do not assert optimal tail powers, a matching upper mean-displacement bound or equality of IIC constructions.


## Range at the intrinsic volume scale

[PSNV](articles/iic-random-walk.md#section-iic-range-moments) now combines the established geometric tails with a quantitative hitting argument to control the visited-vertex range on the $n^{2/3}$ scale. Positive and inverse moments have two-sided bounds for $-3/23<p<3/94$, for both walks. The proof uses Z78U's exponential upper-volume tail and keeps the distant-point ratio hypothesis; no identification of incipient laws or new source correction is asserted.
