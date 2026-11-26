# Hara: the spatial bootstrap and its Fourier bridge

Read Sections 3.4–3.5 and 4.1.1–4.1.2 of the [author-hosted published paper](https://www2.math.kyushu-u.ac.jp/~hara/papers/AOP_36_530.pdf), printed pp.560–564 and 567–569, in extracted text. The figures have not been visually checked. This is a partial reading of the spatial argument.

| Locator | Reconciliation |
|---|---|
| Lemma 4.1; (4.10)–(4.11) | [2ZOB](articles/fourier-spatial-moment-bridge.md#section-derivatives) proves the integer-order derivative estimate, including mixed derivatives, with a positive denominator regularization. |
| (4.4), (4.9), (4.12) | [1165](articles/fourier-spatial-moment-bridge.md#section-decay) justifies the critical integration by parts by L1 convergence; it does not assume an absolutely convergent two-point Fourier series. |
| (4.5)–(4.7), (4.13) | [BNKQ](articles/fourier-spatial-moment-bridge.md#section-convolutions) identifies the weighted spatial sums using positive Fejer multipliers and Holder bounds. |
| Starting moment in the iterative argument | [CMEX](articles/fourier-spatial-moment-bridge.md#section-percolation) supplies quadratic spatial decay and the fourth-weighted bubble from the completed critical Fourier bootstrap. This does not give a fourth moment of the lace coefficients. |
| Sections 3.4–3.5; Lemmas 1.7–1.8 | The two-mark estimate and separated-long-segment reduction remain unfinished in the wiki. The source uses additional middle-diagram estimates; the existing one-mark bounds do not replace them. |

Fractional-order estimates and the remaining spatial iteration are separate. No new source correction, numerical dimension threshold or compiled association is claimed.

## Two marked routes in the first coefficient

[5EWK](articles/two-mark-first-coefficients.md#section-diagram) gives an explicit nine-placement calculation for the eight-edge first-coefficient diagram. [0TO3](articles/two-mark-first-coefficients.md#section-critical) combines it with the critical Fourier bridge to prove fourth moments and fourth-weighted critical continuity for orders zero and one, without a spatial decay hypothesis. This supplies the low-order cases mentioned after Hara (3.15). The uniform two-mark estimate over all lace orders, the separated-long-segment reduction and the full spatial iteration remain unfinished. No new erratum is asserted.

## Qualitative all-order moment gain by planar Fourier bounds

[VPUS](articles/planar-lace-moments.md#section-planar) bounds rooted plane diagrams from their bounded faces. [KOTM](articles/planar-lace-moments.md#section-moments) applies mixed L3/L12 norms to arbitrary positions of two marks and retains geometric decay in the lace order. [GIN9](articles/planar-lace-moments.md#section-dimension) supplies moments of any prescribed fixed order in sufficiently large dimension, weighted critical continuity and a relative quadratic Fourier remainder. This closes the qualitative moment step by a different argument from Hara Section 3.4. It does not reproduce the sharper dimension range, the separated-long-segment proof or the full spatial asymptotic. No new source error is asserted.

## Completing the qualitative spatial asymptotic

[LS5S](articles/planar-pointwise-lace.md#section-deletion) controls the fixed-endpoint diagram after removing one edge from each outer route. Its cut argument excludes unrooted components, and at most ten Fourier factors remain after the original face variables are integrated. [8F9A](articles/planar-pointwise-lace.md#section-pointwise) extracts two long edges and gives a summable all-order pointwise bound with twice the assumed spatial exponent. [KF2I](articles/planar-pointwise-lace.md#section-gaussian) combines moment doubling, that estimate and the signed Gaussian theorem to prove the critical spatial asymptotic, including the $2/d$ remainder exponent, in sufficiently large dimension.

This is an independent planar Fourier alternative to Section 3.5. The explicit $d\ge60$ condition covers only the moment arithmetic and must be combined with the unspecified Fourier bootstrap and connector-smallness thresholds. No numerical dimension range, new source erratum or Lean verification is claimed.

## Real coordinate weights by symmetric differences

Read Lemma 4.2 and (4.16)–(4.17), printed pp.569–570, and the representations (4.39)–(4.53) in Section 4.3, printed pp.574–577, in extracted text. This is a selected reading of the fractional argument.

[AOKO](articles/fractional-fourier-weights.md#section-multiplier) constructs the absolute fractional multiplier as an Lp norm integral of symmetric differences. [65QV](articles/fractional-fourier-weights.md#section-quotient) gives the weighted density under an absolute input moment K and p(2+s)<d, for s<K, with the even-integer endpoint stated separately. [ODMM](articles/fractional-fourier-weights.md#section-convolutions) proves real-weighted convolution identities when 2 ell + sum s_r < d. The method proves Lp bounds directly; it does not reproduce (4.17), the sharper middle-diagram estimates or a non-even input-moment endpoint. No source correction or formal-status promotion.

## The exact input-moment endpoint

Read Section 4.1.4, (4.23)–(4.29), printed pp.571–573, in extracted text. [2SC4](articles/fractional-fourier-weights.md#section-integrated-modulus) bounds integrated Fourier differences by the exact absolute moment. [ENZ7](articles/fractional-fourier-weights.md#section-endpoint) isolates the highest quotient derivatives and supplies the density for the full real input weight K, including odd integers, under p(2+K)<d. The real-weighted convolution argument therefore now allows weights equal to K. This closes the input-moment endpoint left open in the preceding entry. The source's directional estimates and sharper middle-diagram analysis remain separate; no new source erratum or formal-status promotion is claimed.

## Real-order moments and the final dimension arithmetic

Re-read Section 3.4, (3.11)–(3.15), printed pp.560–562, in extracted text. [PCOC](articles/planar-lace-moments.md#section-real-moments) now applies the endpoint density to the two marked routes at every real input order K≥2; Parseval handles order zero, and the same plane bound handles order one. [6N01](articles/planar-lace-moments.md#section-real-range) gives all moments s<2(d−6)/3 under the critical Fourier hypotheses and connector smallness. [QKEC](articles/planar-pointwise-lace.md#section-real-closure) closes the spatial argument by choosing (d+2)/4<K<(d−6)/3, an interval available for d>30. This improves the internal arithmetic from the previous even-order choice. It does not verify the probabilistic hypotheses at d=31 or reproduce the source's sharper marked-diagram bounds. No new erratum or formal-status change.

## The weighted middle integral

Read (1.17), (4.8), (4.14) and (4.20), printed pp.534, 568–570, in extracted text. [U7QM](articles/fractional-fourier-weights.md#section-middle-integral) bounds the unweighted two-frequency core by Young's inequality: it is uniformly bounded for d≥8 and belongs to every finite Lq space at d=7. [5PWM](articles/fractional-fourier-weights.md#section-middle-diagram) identifies the eight-factor spatial diagram with its absolutely convergent Fourier integral using positive heat smoothing. Under the stated quotient and moment hypotheses it is uniformly finite for 0≤β≤K and β<d−2, including real and exact input weights. This is an additional sufficient estimate, not a correction to the source. The directional bound (4.17), other marked-diagram decompositions and numerical dimension thresholds remain separate.

## The directional fractional estimate

[MAT0](articles/fractional-fourier-weights.md#section-directional) now gives a pointwise majorant for each positive noninteger weight s with ceil(s)≤K and s+2<d. Splitting the symmetric-difference integral at the frequency distance gives a bound which implies Hara (4.17), without using the source fractional integration kernels. Its integer-input hypothesis is retained explicitly; ENZ7 remains the separate Lp endpoint when only the noninteger moment itself is available. The other marked-diagram decompositions and numerical dimension range remain separate. No source erratum or formal-status change.

## Ordered faces and the three-bridge bound

Re-read Sections 3.4–3.5, printed pp.560–564, and inspect Figure 4 on p.561. [7TNU](articles/planar-lace-moments.md#section-ordered-faces) gives an independent refinement of the SJIL strip: integrate block faces before connector faces, leaving at most four factors at each step. [5T90](articles/planar-lace-moments.md#section-ninth-moments) then uses marked L^(18/7) and unmarked L9 norms and reaches every moment s<7d/9−4. [RCF3](articles/planar-pointwise-lace.md#section-three-bridges) shows that the two-edge deletion leaves at most three bridges. [CP1T](articles/planar-pointwise-lace.md#section-ninth-closure) closes the spatial arithmetic for d>18. The critical Fourier hypotheses and ninth-norm connector smallness remain explicit; no numerical verification at d=19 or source erratum is claimed. The source's spatial peeling and its constants remain separate correspondence work.

## Weighted rows with the original small-triangle condition

[SL9H](articles/planar-lace-moments.md#section-weighted-rows) estimates both SJIL connector-block transitions directly: a marked row is bounded by two weighted triangle norms, while an unmarked row retains T times Delta. At most two transitions contain the two outer-route marks. [B0RG](articles/planar-lace-moments.md#section-triangle-moment-range) combines this with the exact real input-moment convolution identity. Under the critical Fourier representation, quadratic gap, finite critical clusters, absolute second moments, d>10 and 2T Delta<1, it reaches every moment s<d−6 and weighted critical continuity without assuming Gaussian two-point decay. This is an independent sufficient argument related to Section 3.4, (3.11)–(3.15); it does not claim all source constants or estimates. The separate pointwise/Gaussian proof retains its ninth-norm smallness hypothesis. No numerical threshold, source erratum or Lean verification is asserted.

## Sixth norms and the balanced Gaussian error

[634L](articles/planar-pointwise-lace.md#section-sixth-norms) uses the sixth-norm endpoint of the existing two-root estimate, including both low lace orders. [FWHO](articles/planar-pointwise-lace.md#section-sixth-closure) combines it with B0RG: for d>14 one can choose (d+2)/2<a<d−6, so the coefficient tail exceeds d+2 without an assumed Gaussian two-point estimate. Under the stated critical Fourier, second-moment, finite-cluster and sixth-norm smallness hypotheses, the Gaussian conclusion follows; a second pointwise gain gives weighted coefficient summability and critical continuity for every s<d−4. [7QGG](articles/signed-kernel-gaussian-asymptotics.md#section-balanced-error) balances the two existing heat-kernel errors and improves the remainder exponent to 2 alpha/(d+alpha), or 4/(d+2) with a fourth moment. These are independent refinements of the written proofs corresponding to Theorem 1.4 and Sections 2–3. No numerical verification of the percolation hypotheses at d=15, optimal remainder, source erratum or Lean verification is claimed.

## Explicit sixth-norm certificates

[LKS9](articles/infrared-diagrams.md#section-sixth-certificates) replaces the unspecified sixth walk-integral constants by finite return counts and a proved tail bound. It also proves that both relevant integrals decrease with dimension. [NI0W](articles/infrared-diagrams.md#section-connector-certificate) gives exact rational certificates: for dimensions at least 40, 64 or 100, infrared amplitude and j_c bounded respectively by 21/20, 11/10 or 23/20 imply sixth-norm connector bounds below 407/500, 37/50 or 181/250. The full certificate is reproduced in the article and stored as a standard-library Python script. These bounds supply the smallness input to FWHO, conditional on its remaining critical hypotheses. They do not establish the required percolation infrared amplitudes at these dimensions or a numerical percolation threshold. No source erratum or formal-status promotion is asserted.

## A coarse explicit dimension bound

[NOTF and66SP](articles/bootstrap-diagram-bounds.md#section-explicit-diagrams) retain numerical constants in the existing diagram proof with weak bootstrap bound two. The finite certificate I_(40,6)<669/500 yields triangle, pair and H bounds; exact geometric sums give a full weighted coefficient budget of 50000000/d. [7GNW](articles/completed-fourier-bootstrap.md#section-explicit-dimension) then closes the bootstrap for every integer d>=10^11, with infrared amplitude at most 521/500 and 2d p_c at most 1001/1000. It supplies the critical normalization, absolute second moments, finite clusters, quadratic gap and sixth-norm smallness required by FWHO. Thus the Gaussian spatial expansion with remainder exponent 4/(d+2), the coefficient tail of exponent 2(d-2), and weighted critical continuity for s<d-4 hold in that explicit range. A complete standard-library rational certificate is reproduced with the proof.

This is an independent, deliberately coarse quantification of the written argument, not a numerical dimension claim attributed to the source. It does not settle the conditional hypotheses at dimensions 15, 40, 64 or100, or the dimension range near six. The earlier statements, provisional errata and formal statuses are unchanged.
