# Hara: the signed-kernel Gaussian lemma

Sections 2.1–2.6 of the [author-hosted published PDF](https://www2.math.kyushu-u.ac.jp/~hara/papers/AOP_36_530.pdf) have now been read in extracted text, printed pp.542–555 / PDF indices12–25. The earlier [Appendix B map](sources/hara-2008-convolution.md) remains the convolution reference. This is not a full-paper reading: the later model-dependent diagrammatic estimates and Appendix A remain separate. A direct PDF download was blocked by the workspace network proxy, so visual-page verification is still unavailable.

| Locator | Reconciliation |
|---|---|
| Theorem 1.4; Section 2.2 | Coordinate sign and permutation symmetry make the signed second-moment tensor isotropic. Absolute second moments justify Taylor expansion; the Fourier gap makes its quadratic coefficient positive. |
| Lemma 2.3; 2.41–2.52 | [YNLW](articles/signed-kernel-gaussian-asymptotics.md#section-heat) proves the weighted heat bound by simultaneous induction over the spatial weight, using only first and second Fourier derivatives. The borderline convolution estimate is proved inside the induction. |
| Lemma 2.2; Section 2.3 | [KSC4](articles/signed-kernel-gaussian-asymptotics.md#section-gaussian) proves a uniform Gaussian approximation by an L1 Fourier argument. A higher absolute moment supplies the quantitative error. |
| 2.1–2.9; Section 2.6 | [OT9N](articles/signed-kernel-gaussian-asymptotics.md#section-green) completes the spatial Green asymptotic, its amplitude and the higher-moment remainder. The short-time estimate uses the pointwise kernel bound; Fourier asymptotics alone do not replace it. |
| 2.23–2.26 | The [provisional prefactor entry](errata/hara-nearest-neighbour-2008.json#gaussian-truncation-prefactor) has a complete local constant repair: retain the dimension factor in the Gaussian density and its maximum. The theorem and error order are unchanged. |
| Section 2.5, Proposition 2.4 | The sparse-tail example and its argument have been read as source context for the pointwise hypothesis. No new assertion or independent validation of that example is claimed. |
| Corollary 1.6; book 11.2.10–11.2.16 | [KB4O](articles/signed-kernel-gaussian-asymptotics.md#section-lace) supplies the full analytic implication for d>8 from a pointwise coefficient bound, the critical mass identity and the Fourier gap. It retains the 2/d remainder. Verification of the all-order spatial input and bootstrap remains unfinished. |

No positivity of the effective kernel is imposed. All new assertions remain unformalised unless a matching compiled manifest later supplies evidence; no compiled association, independent audit or author confirmation is claimed.

## The higher-moment input

[JJJN](articles/higher-lace-moments.md#section-critical) now supplies a 2+epsilon absolute moment of the full nonnegative lace series when d>8, epsilon<d-8, the critical spatial two-point bound holds and the weighted triangle is small. [JO75](articles/higher-lace-moments.md#section-fourier) gives the corresponding quantitative quadratic Fourier expansion, with positivity of the quadratic coefficient stated separately. The stronger pointwise coefficient hypothesis in the Gaussian lemma and the improving spatial bootstrap are still unfinished; weighted summability does not replace either.

## Starting the spatial argument

The [spatial-bootstrap reading map](sources/hara-2008-spatial-bootstrap.md) now distinguishes the unresolved two-mark and separated-segment estimates from the completed integer-order Fourier bridge. [CMEX](articles/fourier-spatial-moment-bridge.md#section-percolation) gives a first quadratic spatial bound and weighted bubble/triangle finiteness directly from the critical Fourier theorem. This does not yet supply the pointwise kernel hypothesis of the Gaussian lemma.

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

## Real moments in the Gaussian closure

[PCOC](articles/planar-lace-moments.md#section-real-moments) extends the all-order gain from even to arbitrary real input moments. [6N01](articles/planar-lace-moments.md#section-real-range) gives every coefficient moment s<2(d−6)/3 under the same critical Fourier and small-connector assumptions. Consequently [QKEC](articles/planar-pointwise-lace.md#section-real-closure) can choose a real moment yielding a pointwise coefficient exponent above d+2 whenever d>30. The signed-kernel and convolution steps then give the same amplitude and 2/d remainder as before. The d>30 condition is internal arithmetic; the Fourier bootstrap and connector smallness still have an unspecified dimension threshold. No numerical d=31 theorem or new source correction is claimed.

## A direct bound for the weighted middle diagram

The [new middle-integral proof](articles/fractional-fourier-weights.md#section-middle-integral) supplies an Lq estimate for the unweighted core in (4.8). [5PWM](articles/fractional-fourier-weights.md#section-middle-diagram) combines it with the fractional density and uses positive heat smoothing to justify the spatial identity. The result retains the Fourier gap and input-moment assumptions; it does not change the signed Gaussian theorem, establish a numerical dimension threshold, or add an erratum.

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
