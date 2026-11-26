# Ordinary-SLE inverse-radius moments

Read Lemma6.3, its geometric interpretation (6.2) and the start of its proof on printed pp.903–904 of the [published PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n2-p07.pdf), PDF indices20–21, on17 November2026. Bibliography: *Annals of Mathematics*161(2005),883–924, DOI10.4007/annals.2005.161.883. This was a text reading, not a visual-PDF audit or full-paper reading.

The lemma gives finite inverse conformal-radius moments of orders below1-kappa/8 for ordinary chordal SLE when kappa<8. At kappa6 the threshold is1/4. The [conditioned moment argument GXMS](../articles/continuum-connection-densities.md#section-conditioned-moment) proves the bound it needs by a percolation comparison instead of assuming that local absolute continuity transfers this moment to a force-point law.

The ordinary-SLE moment proof, trace construction and the rest of the paper are not reproduced. This scope distinction is not an erratum about the lemma or the Beliaev–Izyurov theorem.


## The full conformal-radius moment argument

Lemma6.3 and its proof through (6.10), printed pp.903–906, have now been read in full in the published PDF text and compared with [arXiv:math/0106036v4 section6](https://arxiv.org/html/math/0106036v4). The [SLE conformal-radius article](../articles/sle-conformal-radius.md) supplies an alternative proof of the lemma's moment conclusions for every kappa>0 and every real moment order, with the zeroth moment stated separately.

LZCO identifies the logarithmic radius clock. K0WT uses Euler's positive integral to justify finite moments before identifying the hypergeometric answer. ILR6 proves divergence at the sharp endpoint using a positive eigenfunction, and handles kappa>=8 by the scale function. DC8Q derives the exponent for distance to the limiting Loewner-domain boundary. This last formulation does not assume the theorem constructing the trace.

The source's comparison (6.5), trace construction and full-trace interpretation, the finite physical swallowing-time theorem, transience and dimension results remain separate coverage obligations. Standard Loewner, stochastic-calculus and hypergeometric identities are explicit inputs. The ordinary-SLE result does not transfer automatically to the conditioned law in the five-point calculation; GXMS remains its separate bound. No new erratum or Lean association is asserted.


## Physical lifetime and boundary intervals

The text reading now includes Lemmas 6.5–6.6 and the proof of Theorem 6.4, printed pp.906–908, compared with arXiv:math/0106036v4 section 6. The [swallowing-time article](../articles/sle-swallowing.md) adds four assertions.

JCIS bounds the expected time to leave a half-disk or reach the Loewner singularity. Together with the source's positive harmonic function, this gives the fixed-point finite-lifetime theorem 6DV8 for every kappa>4. The half-disk estimate uses the real part of the same complex martingale and its quadratic variation. It replaces the source's sprint-time argument; this alternative is not an assertion of a source error.

KQIN proves an incomplete beta formula for equality of two positive boundary swallowing times. Its ratio endpoint classification is proved directly from the SDE, including the exclusion of asymptotic approach to zero in infinite ratio-clock time. No trace theorem is used in this diffusion result. The trace version 2L0Z retains the source's extremal-distance boundary comparison as an explicit input; dilation excludes atoms, and beta/gamma identities recover (6.13).

Theorem 6.4 has been read, but its geometric conclusions are not claimed to follow here without the trace inputs. The simultaneous all-points lifetime assertion, trace construction, transience and dimension results remain separate. The force-point conditional exploration used in the continuum-density article also remains separate. Existing errata are unchanged; no new source fault or Lean association is asserted.


## Trace distances and expected covering numbers

The discussion of (6.2), Theorem 8.1 and Corollary 8.2 have now been read and compared in the [published PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n2-p07.pdf), pp.903–904 and 912–913, and [v4 HTML](https://arxiv.org/html/math/0106036v4), Sections 6 and 8.1. The comparison is textual, not a visual-PDF audit.

The [trace-covering article](../articles/sle-trace-covering.md) proves the geometric distance identification G0UQ under a continuous-trace generation hypothesis. VEZ7 combines it with the earlier moment proof to give uniform compact small-ball estimates. An outer grid and a separated inner grid yield the expected covering estimates in 1424. The all-scale lower tail already available in DC8Q strengthens the source's logarithmic limsup to a full limit. YBRV derives the Hausdorff upper bound by summing dyadic covering costs.

The [grid-localization discussion and provisional erratum](../articles/sle-trace-covering.md#section-grid-localization) explain why the source's pointwise reverse comparison can count trace points outside A. The repair preserves the dimension theorem. Trace existence and generation, supplied by Theorem 5.1 and its cited kappa8 extension, remain explicit inputs rather than new proofs. Transience, hull-boundary dimension, Hausdorff lower bounds and terminal conditioned explorations remain separate.


## Real-boundary avoidance and the simple-curve transience argument

The [boundary-avoidance article](../articles/sle-boundary-avoidance.md) covers the flow calculation of Lemma 6.2, Lemma 7.2, and the simple-curve part of Theorem 7.1. The latter two were compared in [v4 HTML](https://arxiv.org/html/math/0106036v4), Section 7, and the [journal PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n2-p07.pdf), pp.909–911. The comparison is textual; no visual-PDF audit is claimed.

RD3V proves global positive real flows and distinguishes their positive infimum below four from their zero infimum at four. JQ3M writes the critical potential as a bounded positive integral and checks that its supermartingale drift also has the required sign for smaller parameters. This yields one distortion proof throughout the range from zero to four. YBCC applies reflection and Koebe; D67E makes the conditional-future and scaling arguments for transience explicit. The extension of the potential estimate to smaller parameters is proved here rather than attributed to a further source statement.

The geometric results retain the continuous simple-trace theorem, Theorems 5.1 and 6.1, as an input. They also name the conformal-mapping facts used, including the two prime ends at a slit's starting point. Neither trace construction nor transience for kappa greater than four is proved in this continuation. No additional source correction was identified; the earlier covering-grid erratum remains provisional.


## Engulfment and space filling at kappa at least eight

The [space-filling article](../articles/sle-space-filling.md) completes the large-parameter engulfment and transience argument, conditional on the trace theorem and deterministic-time zero-area hull boundaries. The large-parameter part of Lemma 7.3, Theorem 7.1, Corollary 7.4 and the kappa8 update were compared in [v4 HTML](https://arxiv.org/html/math/0106036v4), Section 7, and the [journal PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n2-p07.pdf), pp.910–911. The exact input statements were also checked at Theorem 5.1, p.899, and Corollary 5.3, p.901. This is a textual reading, not a visual-PDF audit or a proof of those inputs.

UELC obtains density from countably many fixed-point distance statements, then rules out an unvisited bounded component by a pathwise argument. It identifies the interior hull with the past trace at every time. KFWY combines this with finite physical lifetime to prove fixed-point hitting at the lifetime. ZS6G writes out the strong Markov and Fubini argument: if the origin always remained accessible, each fixed hit point would remain on later hull boundaries, contradicting their zero area at deterministic times. A germ-law argument gives immediate engulfment. R2A0 uses scaling to deduce transience and finite-time coverage of each compact subset of the closed half-plane.

The source's full inverse-map limit is needed at a stopping time; a statement merely about vertical limits at fixed deterministic times would not be enough for that step. The kappa8 conclusion uses the extension cited in the source. The interval-swallowing geometry for four less than kappa less than eight, trace construction and the derivative estimates behind the boundary-area input remain separate. There is no new source correction or compiled association.


## Inverse-map derivative estimates and fixed-time regularity

The [derivative-estimates article](../articles/sle-derivative-estimates.md) proves the reverse-flow identity of Lemma 3.1, the weighted moment identity of Theorem 3.2, a stronger version of the tail bound in Corollary 3.5, and the fixed-time Holder theorem 5.2. These portions were compared in [v4 HTML](https://arxiv.org/html/math/0106036v4), Sections 3 and 5, and the [journal PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n2-p07.pdf), pp.889–892, 894–895 and 900–901. This was a textual comparison, not a visual-PDF audit.

HHBC keeps the map identity at a fixed time distinct from a process identity. O0VQ makes the height clock and its finite target times explicit in both directions. AXSH justifies the weighted martingale by its bounded stochastic coefficient. M7AF stops that martingale at the bounded height clock associated with a deterministic physical time, then uses Schwarz–Pick; this removes the logarithmic loss at a=lambda without finding a fault in the source upper bound. OLNV uses a dyadic grid, Koebe distortion and integration. The simple choice b=kappa^(-1/2) provides the positive exponents and their source limiting values. This proves regularity for each fixed time; it does not produce a common all-times event or construct the trace.

A [separate provisional comparison repair](../articles/sle-derivative-estimates.md#section-comparison-repair) concerns Lemma 3.3, p.893, immediately before (3.15). The reverse derivative can decrease after reaching height one. A bounded factor from O0VQ restores the comparison for every real moment order and preserves the source lemma. The uniform tube-probability argument and the full lower bound remain separate. Joint-time continuity, the deterministic trace-generation criterion and the boundary-dimension theorem also remain separate coverage obligations. No compiled association is claimed.


## Joint continuity of the radial tip map

Section 3.3, Theorem 3.6 and its complete proof through (3.24) have now been read in [v4 HTML](https://arxiv.org/html/math/0106036v4), including the almost-every-time observation at kappa eight and the later update. Section 4's deterministic criterion and proof were also read, but that theorem is not yet supplied as a wiki proof. No new visual-PDF or journal-text comparison is claimed for this batch.

The [joint-continuity article](../articles/sle-tip-continuity.md) proves the same all-times radial extension for kappa different from eight by a deterministic mesh. 4ENF traps the backward flow in a fixed rescaled rectangle. N7TT combines Brownian reflection bounds with M7AF and telescopes dyadic heights uniformly in time. MV6M gives a logarithmic time modulus and explicit sufficient Holder exponents. YVFR gives the weaker almost-every-time conclusion at kappa eight by Fubini from OLNV.

The strict derivative exponent absorbs the extra polynomial mesh count, so no derivative law at random reversed stopping times is needed in this proof. A continuous radial limit is not here promoted to full boundary continuity or hull generation. Theorem 4.1, the kappa-eight trace input, the full derivative lower bound and boundary-dimension inputs remain separate. There is no new source erratum or compiled association.


## Deterministic hull generation and full boundary limits

The [trace-generation article](../articles/sle-trace-generation.md) supplies a proof of Theorem 4.1 and the resulting Theorem 5.1 away from kappa eight. Section 4 and the start of Section 5 were checked in [v4 HTML](https://arxiv.org/html/math/0106036v4). This is a textual reading; no new journal-PDF comparison or reading of the cited conformal-mapping monographs is claimed.

N2VO replaces the source's disk-and-impression argument by first contact of a polygonal arc avoiding the proposed trace. The minimum lifetime on the compact arc is attained, and its first boundary point was interior at every earlier time. Backward flow away from the driving point gives a contradiction unless that accessible point is the radial tip. This proves generation without assuming uniform radial convergence. Local connectedness and full inverse-map extension follow using the named Peano, Torhorst and Caratheodory theorems. Accessible-arc mapping and Lindelof are also explicit classical inputs, with the references identified in the source.

MN2A applies N7TT pathwise, giving the continuous generating SLE trace and unrestricted tip limits simultaneously at all times for positive kappa different from eight. The vertical slit handles kappa zero. This supplies the corresponding trace hypotheses of the covering and space-filling articles. The kappa-eight extension, simplicity, zero-area/boundary-dimension input, derivative lower bound and remaining regime arguments are separate. Existing provisional errata are unchanged; no new source fault or compiled association is asserted.


## Simplicity and the completed small-parameter transience route

The [simplicity continuation](../articles/sle-boundary-avoidance.md#section-simplicity) supplies Lemma 6.2 and Theorem 6.1 from the earlier real-flow and trace theorems. Their complete proofs were read in [v4 HTML](https://arxiv.org/html/math/0106036v4), Section 6. No new journal-PDF comparison is claimed.

W8MU passes from rational real starting points to all nonzero real points by order preservation, then uses a common complex-flow neighborhood on each finite horizon. This proves simultaneous avoidance without assuming simplicity. CKFH restarts at countably many rational times and uses inverse-map continuity to identify the future trace before deciding whether it lies inside the old domain. Strict capacity growth ensures that each nonempty time interval contains a rational restart whose tip has left any earlier hull. The future avoidance statement then excludes all repeated visits pathwise. The planar Jordan-arc theorem identifies the slit domain.

This supplies the simple-trace hypotheses in YBCC and D67E, completing the written route to fixed-point boundary distance and transience for kappa at most four, with their stated classical conformal inputs. The zero-time hull convention is explicit: the closure of the interior hull is empty at time zero. The kappa-eight extension, intermediate regime, derivative lower bound and zero-area/boundary-dimension arguments remain separate. Existing provisional errata and compiled evidence are unchanged.


## Interior lifetimes, hull area and simultaneous boundary bounds

The definition of swallowing, Theorem 6.4, its proof, Exercise 6.7, and Lemma 7.3's distinction between interior growth and origin engulfment were checked in [v4 HTML](https://arxiv.org/html/math/0106036v4), Sections 6–7. No new journal-PDF comparison is claimed.

The [interior-lifetime continuation](../articles/sle-swallowing.md#section-interior-lifetimes) proves O0MI: every fixed interior point stays a positive distance from the full trace for positive kappa below eight. The simplicity theorem then gives infinite lifetime up to four, proving Exercise 6.7. Between four and eight, the finite-lifetime theorem and connected-component geometry give an open disk whose points are all swallowed at that same time and never visited by the trace. This supplies the interior-point part of Theorem 6.4; its real-boundary interpretation remains separate. The exclusion of kappa zero and the fixed-point quantifier are explicit.

The [boundary-dimension continuation](../articles/sle-trace-covering.md#section-hull-boundaries) proves NHWR: every finite-time hull boundary lies in the past trace plus the real line. YBRV therefore gives dimension at most one plus kappa over eight simultaneously at all times when kappa is below eight, including four. The trace and boundaries have zero planar area. This derives the conclusion from the trace dimension bound instead of the Holder-domain theorem used earlier in the source; it is not an optimal hull-boundary exponent claim or an erratum about Corollary 5.3.

CPJC combines one fixed swallowed disk with scaling and monotonicity to show nonempty hull interior at every positive time between four and eight. The hull has positive finite area despite its zero-area trace and boundary. This does not place the disk near zero, so the stronger origin-engulfment theorem and intermediate-regime transience remain separate. Kappa-eight trace construction, boundary dimension at and above eight, the derivative lower bound and the conditional boundary-interval geometry are still outstanding. Existing provisional errata and Lean evidence are unchanged.


## Boundary swallowing and transience between four and eight

The [boundary-swallowing article](../articles/sle-boundary-swallowing.md) completes the intermediate-regime route. Theorem 6.4, the remark after Lemma 6.5, Lemma 6.6 with equation (6.13), Lemma 7.3 and Theorem 7.1 were checked in [v4 HTML](https://arxiv.org/html/math/0106036v4), Sections 6–7. No new journal-PDF comparison is claimed.

E5JX identifies the first hit of a positive boundary ray with the tip at the initial mark's swallowing time. Its backward-flow argument locates that tip, and local Schwarz reflection shows that preceding compact intervals are separated from the future domain. U8XU combines the resulting lifetime equivalence with KQIN to prove the boundary beta law and the fixed-real-point part of Theorem 6.4. This supplies the geometric input retained in 2L0Z; the older statement and proof are unchanged.

ZI7H makes the origin-engulfment argument explicit. At the swallowing time of one, the inverse-map preimages of zero lie compactly to the left of the driver. One deterministic negative interval contains this set with positive probability; the independent future has positive probability of swallowing that interval. Scaling and the Brownian germ law then give origin engulfment at every positive time. G09W turns its growing distance into transience, finite-time hull coverage of every compact set and simultaneous finite lifetimes. The compact coverage is by hulls, not a space-filling assertion for the trace. Classical boundary reflection, Brownian strong Markov and the germ law are named inputs. Kappa eight, the boundary-area input above eight, the full derivative lower bound and later dimension results remain separate. Existing errata assessments and compiled evidence are unchanged.


## Hull-boundary covering and the completed space-filling route above eight

The [hull-boundary article](../articles/sle-hull-boundary.md) supplies the upper-covering theorem and zero-area conclusion at each fixed time. Section 8.2, including the Whitney definitions, Theorem 8.3, Lemma 8.4, both parts of the moment argument, Corollary 8.5, Theorem 8.6 and Corollary 8.7, was read in [v4 HTML](https://arxiv.org/html/math/0106036v4). No new journal-PDF comparison is claimed.

EG6U applies bounded optional stopping directly to the already proved derivative martingale. AVHR sums these moments on dyadic grids in fixed horizontal windows, above a positive image height. The deterministic criterion 2SVA uses radial paths, a logarithmic interval bounded by Holder continuity, Koebe distortion and planar packing to produce boundary covers. This localized route suffices for the almost-sure upper bound without claiming the global expected Whitney threshold.

K8Y5 gives the exponent one plus kappa over eight up to four, and one plus two over kappa above four. At four, the existing trace-covering estimate and Borel–Cantelli supply the endpoint. The resulting boundary dimension and zero area hold at each fixed time for every positive kappa, including eight, without a trace theorem at eight. They supply Theorem 8.6, the upper bound of Corollary 8.7 and the deterministic-time boundary-area input from Corollary 5.3. No all-times covering assertion is made.

BQ8X combines this area result with the proved trace theorem, completing the large-parameter parts of Lemma 7.3, Theorem 7.1 and Corollary 7.4 for kappa greater than eight, including finite-time trace coverage of every compact half-plane set. The kappa-eight trace construction, the full Lemma 3.3 lower bound, the global Whitney-sum result of Theorem 8.3 and Corollary 8.5 remain separate obligations. No new source error is diagnosed; all existing errata assessments and compiled evidence are unchanged.


## The derivative lower bound and the localized grid threshold

The [lower-moment article](../articles/sle-derivative-lower-bounds.md) completes Lemma 3.3. Its statement and full proof, including (3.12)–(3.15), were read in [v4 HTML](https://arxiv.org/html/math/0106036v4), Section 3.1. The lower-bound use in Section 8.2 was also checked. No new journal-PDF comparison is claimed.

CUBE proves a uniform fractional-moment bound for the physical clock of the tilted hyperbolic diffusion. A smooth exponential Lyapunov function has decay rate greater than its exponent because the inward drift exceeds one. Summing unit-interval maxima gives the clock bound; Markov then controls both crossing time and endpoint with uniformly positive probability. G4U8 obtains this diffusion by Girsanov and removes the derivative-martingale density. The argument replaces the source's brief pathwise tube estimate.

7NGO combines this lower estimate with the previously recorded bounded-factor derivative comparison, reverse-flow equality in law and scaling. It proves the full source lemma, including negative moment orders. The existing provisional erratum now links to this completed proof; its found/local assessment is unchanged. No new source error, author confirmation or compiled association is asserted.

T3F8 proves that the expected localized dyadic grid sum has the exact threshold delta(kappa), for kappa different from four and sufficiently small positive image-height cutoff. A fixed interval of real input coordinates gives a positive contribution at every fine scale at the threshold; smaller positive powers follow from the upper bound on derivative scale. Infinite expectation is not an almost-sure divergence claim. The global Whitney comparison and Theorem 8.3/Corollary 8.5 remain separate, as does the kappa-eight trace construction.


## The global Whitney threshold and expected-covering lower bound

The [Whitney-sum article](../articles/sle-whitney-sums.md) proves Theorem 8.3 and Corollary 8.5 from the derivative estimates already supplied. The Whitney definitions, Lemma 8.4 and both source proofs in [v4 HTML](https://arxiv.org/html/math/0106036v4), Section 8.2, were checked. No new journal-PDF comparison is claimed.

IDL1 bounds the preimages of relevant Whitney-square centres in a horizontal window controlled by the driving maximum, and uses Koebe distortion and hyperbolic packing to compare the sums. HQI8 treats that random window by splitting each grid level according to whether the driving maximum exceeds its index. The polynomial window factor is absorbed by the strict moment exponent; the remaining levels are controlled by the Gaussian maximum tail.

J0CG gives the exact threshold for the expected global Whitney sum. For divergence, the finite upper moments remove all large derivative scales from the divergent critical grid sum. The remaining image points are close to the hull and can be assigned directly to Whitney squares. This avoids the restricted boundary-preimage-interval comparison of Lemma 8.4; that helper statement is not separately reproduced.

K5PX compares squares above height twice h with the boundary above height h. After removing finitely many coarse scales of finite expectation, divergence of the critical sum yields the expected-covering lower limsup with any positive logarithmic margin, including the source's choice of exponent one plus h. The height buffer is explicit; no new source error is diagnosed. Infinite expectation and an expected-covering limsup are not almost-sure or Hausdorff lower bounds. Existing errata assessments and compiled evidence are unchanged. The separate kappa-eight trace construction and remaining source/library coverage continue.


## The Gaussian height-crossing kernel

Remark 3.4 and its dependence on Theorem 3.2 and the preceding change of measure were checked in [v4 HTML](https://arxiv.org/html/math/0106036v4), Section 3.1. The [height-crossing article](../articles/sle-height-crossing-kernel.md) supplies the explicit formula described in the remark. No new journal-PDF comparison is claimed.

FZJD cancels the hyperbolic drift under a bounded-coefficient martingale tilt, in both flow directions, and gives Brownian functionals for the derivative and the physical crossing time. THQF computes the endpoint moment density, retaining the Gaussian normalization, the terminal weight and the hyperbolic-coordinate Jacobian. PDLI derives a reverse-flow moment equivalent with its exact Gamma constant by dominated convergence. The equivalent is a consequence developed here, not a separately numbered source theorem.

All these moments are taken at a random height-one time. The source's suggested occupation-time tail calculation is not supplied, and the fixed-time upper and lower estimates keep their separate proofs. No conclusion about trace existence at kappa eight follows from the kernel. Lemma 8.4's unused restricted-interval comparison, the remaining discussion and bibliography, independent correspondence and the full journal-version comparison remain separate coverage tasks. No new source error is diagnosed; the existing repair and significance assessments are unchanged.
