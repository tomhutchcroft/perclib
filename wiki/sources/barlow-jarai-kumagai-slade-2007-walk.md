# Barlow–Járai–Kumagai–Slade: random-walk estimates

Primary source: *Random walk on the incipient infinite cluster for oriented percolation in high dimensions*, [author manuscript dated 31 August 2007](https://www.kurims.kyoto-u.ac.jp/~kumagai/iic.pdf), later published in Communications in Mathematical Physics 278, 385–431 (2008), [DOI](https://doi.org/10.1007/s00220-007-0410-4). The reading covers the deterministic estimates in Sections 2.1.1–2.1.2, printed pp.10–15 / PDF indices10–15, in extracted text. No publisher-version or visual-page comparison is claimed.

| Locator | Written treatment |
|---|---|
| (2.17)–(2.22), pp.11–12 | [331W](articles/iic-random-walk.md#section-green-exit) derives the finite Dirichlet Green identity and the exit bounds, including the lower bound from energy along a shortest path. |
| Lemma 2.4, p.12 | [KGNK](articles/iic-random-walk.md#section-return-bounds) retains the supremum mean exit time in the survival lower bound. |
| Proposition 2.5 and (2.32)–(2.34), pp.14–15 | KGNK uses a lazy spectral operator for the upper estimate and a semigroup/Cauchy–Schwarz argument for the lower estimate. [NNW7](articles/iic-random-walk.md#section-deterministic-exponents) supplies explicit binomial comparisons with ordinary even-time returns. |

The source normalizes the heat kernel by vertex degree. The article keeps that convention and converts the IIC's cardinality-volume estimate to degree volume before applying the deterministic implication. [IXCJ](articles/iic-random-walk.md#section-iic-spectral-dimension) uses the wiki's existing finite-triangle geometry for susceptibility-biased and ratio-controlled distant-point limits.

The written proof establishes recurrence, quenched mean exit-time exponent three and spectral dimension four thirds. The sharper lower tail of the exit time, sample-path displacement and range, annealed estimates, and the source's oriented-percolation construction are outside this map. No new erratum, complete-paper reading, independent audit or compiled association is claimed.


## Pathwise exit times and range

The reading now also includes Lemma 2.3 and the return-through-root argument (2.25)–(2.28), printed pp.11–13; Theorems 1.5(c) and 1.6, pp.4–5; and the proof of Theorem 1.6, pp.20–21. [LCUN](articles/iic-random-walk.md#section-nearby-hitting) proves the required hitting estimates by a finite Green dipole identity. [7WII](articles/iic-random-walk.md#section-pathwise-exit) combines them with the established geometric exponents to give summable exit tails and pathwise limits. It separately proves fixed-time displacement convergence in probability.

[YIJB](articles/iic-random-walk.md#section-pathwise-range) bounds the expected degree mass missed in a smaller ball before exit, then transfers the resulting lower bound to deterministic times. The maximum-degree condition is retained when converting degree range to cardinality, as required by Theorem 1.6(b). [HJKG](articles/iic-random-walk.md#section-iic-paths) applies these arguments to the existing finite-triangle incipient geometry. These logarithmic-exponent proofs do not reproduce the source's sharper logarithmic corrections, annealed estimates or oriented-percolation construction. No new source erratum is asserted.


## Averaged return and exit estimates

The additional reading covers Assumption 1.2(1)–(3) and Theorem 1.4 (1.14)–(1.16), printed p.4 / PDF index3, together with its proof in Section 2.2, printed p.19 / PDF index18. The source averages a fixed-radius estimate using an inverse-volume moment. The wiki instead uses the linear small-volume probability bound already proved for its incipient limits: [VFZN](articles/iic-random-walk.md#section-annealed-upper) chooses radius proportional to time times the return-kernel threshold and integrates the resulting cubic tail. This does not assert the source's stronger inverse-volume hypothesis.

[Z0P0](articles/iic-random-walk.md#section-annealed-two-sided) obtains the lower return bound on a positive-probability event controlling resistance and volume at two radii, and gives averaged mean exit times of cubic order. [5QU6](articles/iic-random-walk.md#section-annealed-displacement) proves the small-displacement estimate and mean-displacement lower bound by two applications of Cauchy–Schwarz. [G85Z](articles/iic-random-walk.md#section-iic-annealed) checks these hypotheses for the existing finite-triangle incipient limits. Return moments are bounded through every power strictly below three. The source's oriented-percolation construction, a mean-displacement upper bound, limiting constants and identification of IIC constructions are not supplied. This scoped extracted-text reading does not claim a visual or publisher-version comparison, or a new source erratum.

Pagination clarification: the PDF indices are zero-based and the manuscript's printed pages start at one. Earlier passages in this map that equated those two numbers should be read with that offset; their equation and theorem locators are unchanged.


## Quantitative walk tightness and moments

The additional reading covers Theorem 1.3 (1.12)–(1.13), printed p.4 / PDF index3; the $22/3$ loss tracked after (2.36), printed p.16 / PDF index15; the discussion preceding Example 2.6, printed p.17 / PDF index16; and the proof of Theorem 1.3, especially (2.42)–(2.43), printed pp.18–19 / PDF indices17–18. [C2KR](articles/iic-random-walk.md#section-annealed-escape-tail) reconstructs a uniform quantitative escape bound from the earlier root-return argument. It balances the probability of the four failed geometric conditions against the conditional escape probability. [J75E](articles/iic-random-walk.md#section-annealed-walk-moments) integrates both tails, with explicit open moment ranges and the added one needed for negative displacement moments.

For the incipient limits already treated here, [YWT9](articles/iic-random-walk.md#section-iic-tightness) obtains a maximum-distance upper tail with power $3/47$ and a fast-exit lower tail with power $1/47$. These powers come from the wiki's calculation with resistance-tail exponent one half; they are not quoted as the source's optimal exponents. The resulting tightness and fractional moments leave the upper mean-displacement estimate separate, consistent with the source's warning about that step. No example graph, new source erratum, visual/publisher comparison or complete oriented-percolation theorem is supplied.


## Quantitative range bounds

The reading revisits Theorem 1.6 (1.23)–(1.24), printed p.6 / PDF index5, and its proof after (2.48)–(2.49), printed pp.21–22 / PDF indices20–21. [JC9J](articles/iic-random-walk.md#section-range-tails) quantifies the missed-volume argument at a fixed time. [E3IN](articles/iic-random-walk.md#section-range-volume-tail) uses an exponential volume tail to improve the positive moment range, and [PSNV](articles/iic-random-walk.md#section-iic-range-moments) applies both results to the wiki's incipient limits. The powers and moment ranges are deductions here, not quoted source conclusions. The bounded-degree conversion is retained. No new erratum or upper mean-range estimate is claimed; the apparent equality in the source's lower-range display remains unverified without a visual or publisher-version comparison.



## All positive moments at intrinsic exit

[VI2M](articles/iic-random-walk.md#section-slow-exit-moments) iterates the already proved supremum mean-exit bound over deterministic time blocks on each fixed graph. Averaging over the exponential upper-volume tail gives a square-root exponential slow-exit bound, all positive moments, and a joint exponential bound with volume. The proof uses neither an inverse-volume moment nor an independence assertion about the geometry and the walk.

[RA7K](articles/iic-random-walk.md#section-range-at-exit) applies the existing missed-volume argument directly at the exit time. No late-exit error is then needed. Its lower-tail power is beta/(3 beta+2), with the floor and small-radius cases included. The range includes the first boundary vertex; ordinary and lazy walks visit the same set at their respective exits under the holding-time coupling.

[OBBT](articles/iic-random-walk.md#section-iic-stopped-moments) gives all positive exit and stopped-range moments on the existing finite-triangle incipient limits. The negative ranges are p > -1/47 for exit time and p > -1/7 for stopped range, with bounded degree used for cardinality. These are further deductions from the written estimates, not newly read source passages or asserted source statements. Upper means of displacement and range at a deterministic time, IIC identification, and optimal endpoints remain separate. No new erratum, independent audit or Lean verification is recorded.


## Inverse moments at a fixed time

[ZY62](articles/iic-random-walk.md#section-inverse-maximum) converts the slow-exit tail into an exponential moment of the normalized maximum to power -3/2. [GCYB](articles/iic-random-walk.md#section-improved-range-lower-tail) chooses a smaller radius so that its exit precedes the observation time except with a sufficiently small probability; it preserves the stopped-range lower-tail exponent with a logarithmic loss. Integer radii and empty lower-tail events are handled explicitly.

[PDSN](articles/iic-random-walk.md#section-iic-inverse-moments) applies these deductions to the existing incipient limits. It extends maximum moments to all negative orders and fixed-time range moments to p > -1/7, keeping the existing upper restrictions on positive orders. This is not a newly read source passage or a new erratum. It does not claim the paper states these estimates, supply positive first-moment upper bounds, or identify the incipient constructions. The final position is distinguished from the path maximum using the return lower bound already written in the wiki. Independent mathematical review and Lean verification remain pending.


## Quadratic small displacement and inverse-position moments

[05B3](articles/iic-random-walk.md#section-adjacent-kernel-energy) averages adjacent ordinary kernels before applying the spectral energy estimate. [9JIV](articles/iic-random-walk.md#section-quadratic-small-displacement) combines this estimate with a second volume moment to obtain quadratic annealed small-ball bounds. The matching lower bound uses the existing return and resistance estimates; radius one and the parity of ordinary walk are handled separately.

[FPDW](articles/iic-random-walk.md#section-iic-inverse-position-transition) applies these bounds to the existing finite-triangle incipient limits. Inverse position moments have displacement scaling below order two, a logarithmic correction at order two, and return-probability scaling above order two. This completes the inverse-position orders under the stated hypotheses, while positive first-moment upper bounds and IIC identification remain separate. These are further deductions from the written inputs, not newly read source passages, assertions that the paper states these results, or new errata. Independent mathematical review and Lean verification remain pending.


## Root occupation and return times

[Y2C3](articles/iic-random-walk.md#section-root-visit-renewal) proves fixed-chain occupation bounds from ordered visit times and the renewal generating function, allowing defective returns. [7UZM](articles/iic-random-walk.md#section-root-occupation-resistance) tests the lazy resolvent with the killed voltage and compares it to a finite time horizon. Exponential upper volume and lower resistance tails then control small root occupation, without an inverse-volume hypothesis.

[ZZC8](articles/iic-random-walk.md#section-iic-root-local-time) obtains root visit-count moments for -3/4<p<3 and the almost-sure visit/return-time exponents on the existing finite-triangle incipient limits. The excluded moment endpoints are not claimed optimal. This is a further written deduction from the existing geometric and spectral inputs, not a newly read passage, a statement attributed to the paper, or a new erratum. Independent mathematical review and Lean verification remain pending.


## Occupation tails and return-time moments

[6UKZ](articles/iic-random-walk.md#section-occupation-tail-transfer) sums the polynomial return-probability tail through an event integral, without independence across times, and transfers it to occupation by the fixed-chain exponential estimate. [KMWL](articles/iic-random-walk.md#section-iic-occupation-endpoints) gives cubic upper tails for the incipient root visit count and its quenched mean. It also supplies upper and lower bounds at moment orders 3 and -3/4 and beyond; the endpoint logarithms are not claimed necessary.

[2XZU](articles/iic-random-walk.md#section-iic-return-time-moments) inverts the visit count to obtain successive-return tails and moments on the scale m^3 for -1<p<1/4, including the integer-time cutoff. Reversing excursion paths proves that moments of order at least one are infinite on each infinite recurrent cluster. These are further deductions from the written return, volume and resistance estimates, not newly read source statements or new errata. Independent mathematical review and Lean verification remain pending.


## Stationary root bias and range

[K11N](articles/iic-random-walk.md#section-iic-degree-bias) proves marked reversibility of susceptibility-biased cylinder limits after degree bias. The finite-parameter identity uses translation invariance and the equality of cluster sizes across an open edge; only bounded cylinder functions are passed to the limit. [VFDK](articles/iic-random-walk.md#section-stationary-range-identities) then gives the exact mean-range/first-return identity and collision identities, retaining the displacement marks and avoiding an independence assumption for overlapping occupation counts.

[BP8X](articles/iic-random-walk.md#section-iic-stationary-range) obtains a cubic lower tail for the range, inverse range moments of every order below three, an endpoint upper bound with a logarithm, and a mean-range upper bound of order n^(3/4) log(n)^(1/4). The n^(2/3) mean upper bound is still not proved. These conclusions are restricted to susceptibility-biased limits and do not identify them with distant-point limits. They are further deductions from existing written inputs, not newly read source statements, claimed source theorems or new errata. Independent mathematical review and Lean verification remain pending.
