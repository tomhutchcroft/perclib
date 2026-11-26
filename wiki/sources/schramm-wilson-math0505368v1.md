# Stopped SLE coordinate changes

Read sections1–3 through Remark4 of [arXiv:math/0505368v1](https://arxiv.org/html/math/0505368v1), dated17 May2005, on17 November2026. This includes Definitions1–2, Theorem3 and its proof. No journal, later-version or visual-PDF comparison is claimed.

[AGJ2](../articles/continuum-connection-densities.md#section-candidate-equation) uses Theorem3 as an explicit input. With kappa6 and boundary force weights+2,-2, the sum-of-weights condition is satisfied. A real Möbius map sends the negative force point to infinity; its drift contribution then vanishes. The theorem is stopped before force-point collision or swallowing of the preimage of the new target. The calculation keeps that restriction and then localizes.

The general coordinate-change proof is not reproduced in the wiki. Sections4–5 on strip processes and associated martingales, and general interior-force applications, remain uncovered.


## A finite endpoint for the two real force points

Definition 2 and its stopping convention have been rechecked. For the special law with kappa=6 and weights (2,-2), the [force-point argument](../articles/continuum-connection-densities.md#section-force-collision) now proves finite right-force collision, integrable drifts and a finite continuous endpoint. The law in 0SPP is held constant after that endpoint. This is an absorbed path convention, not an extension of the SLE dynamics beyond the collision, and it does not supply a trace theorem. The general coordinate-change proof remains outside the present coverage.


## The chordal boundary case proved directly

Section 3, Theorem 3, its proof and Remark 4 have been rechecked in the versioned HTML. The [target-change article](../articles/sle-coordinate-changes.md) now proves the chordal-to-chordal case with real boundary force points. C6T0 constructs the hydrodynamic normalization using the first two derivatives at the new target; it derives the capacity clock by differentiating the resulting rational map. In 6RZ1, the force-weight balance cancels the Itô correction. Appending a force at the old infinity gives the correct statement without that balance. 0INI transfers a bulk-covariant observable by an exact pathwise identity.

This is a direct proof of the specialization needed in [8Q5E](../articles/continuum-connection-densities.md#section-proved-coordinate-change). It uses the ordinary deterministic Loewner conformal-map theorem and stochastic calculus. It preserves the stop before force collision or swallowing of the preimage of the new target. The general radial, interior-force and strip versions, and terminal trace questions, remain separate. No new source correction or Lean association is asserted.


## Strip coordinates and force-point weights

Sections 4–5 have now been read in the versioned HTML and compared at Theorem 6 with the extracted v1 PDF (printed p.7/PDF index6), the v2/v3 HTML and the [journal PDF](https://nyjm.albany.edu/j/2005/11-31.pdf) (printed p.666/PDF index7). The comparison is textual; no visual-PDF verification is claimed.

The [strip article](../articles/strip-sle.md) supplies the proof left open in Section 4 for boundary marks: an explicit exponential normalization gives capacity time; the force drift transforms under the sum condition; equal compensating weights at the two strip ends treat arbitrary sums and ordinary dipolar SLE. Marks on both boundary lines are included. General interior-force coordinate changes are not claimed.

The [force-point article](../articles/sle-force-martingales.md) proves the chordal Theorem 6 product and Remark 7 boundary extension together, allowing arbitrary mixtures of interior and boundary marks. It derives the logarithmic drift rather than treating the cancellation as an input. Compact stopping, Novikov and Girsanov then give the forced law; no collision-time density or terminal percolation interpretation follows automatically. The real weights (2,-2) at kappa6 recover the powers in W3QF.

The v1 pair exponent is half the required value. 42Z5 gives the residual drift and a two-interior-mark example with initial relative drift 1/20. This was already corrected in [v2](https://arxiv.org/html/math/0505368v2), retained in [v3](https://arxiv.org/html/math/0505368v3), and is correct in the journal Theorem 6. The errata entry is explicitly confined to v1 and remains provisional pending Tom's confirmation. No author contact or new journal error is claimed. The radial martingale and rare-event discussion added in the later text, along with the remaining radial coordinate-change proof, still need separate coverage.


## The radial product in the later edition

The [v3 HTML](https://arxiv.org/html/math/0505368v3), Section 5, Remark 7 and equation (9), has been compared with the [journal PDF](https://nyjm.albany.edu/j/2005/11-31.pdf), printed p.666/PDF index7. Remark 8 and equations (10)–(11) have also been read and compared through printed p.668/PDF index9. This is a textual comparison, with no visual-PDF verification claim. These additions are distinguished from the original v1 source record.

The new [radial force-point article](../articles/radial-sle-martingales.md) proves the reflected product, its boundary renormalization and the stopped change of measure. T723 collects the logarithmic drift into the square of a weighted sum; reflection makes that sum purely imaginary. EU7X handles mixed interior/boundary marks without taking an unjustified unstopped martingale limit. MLBQ checks the angular and reflected-vector-field force conventions. The center mark is omitted consistently with the normalized product limit.

O8ZR computes the equal-weight martingales for kappa6 and kappa2, including the radial powers associated in the source with pivotal sites and spanning-tree branch events. The discussion preserves the source's distinction between these local identities and proposed discrete probability asymptotics. A scaling limit and terminal expectation control are not supplied by the product formula. The general radial coordinate-change proof and the strip interior-force extension remain outside this batch. No new source correction or compiled association is claimed.


## Chordal and radial coordinates

The [coordinate-change article](../articles/chordal-radial-sle.md) derives the interior normalization, the radial capacity clock and the mixed-force transformation in Theorem 3. The account uses [v3](https://arxiv.org/html/math/0505368v3) and the [journal](https://nyjm.albany.edu/j/2005/11-31.pdf), pp.661–664. The comparison is textual; no visual-PDF check is claimed.

The positive rate in 9BVE comes directly from the normalized conformal derivative. The rational identities in 5KL5 transport both interior and boundary marks, including a mark at the new target. For unbalanced weights, the remaining drift is the force of weight kappa minus six minus the original sum at the old target's image. K4PV obtains the inverse radial-to-chordal law by uniqueness, retaining the stop when the new boundary target is swallowed. JVHZ and V2NR instead use a direct disk automorphism to prove the disk-to-disk case, including mixed forces. Their positive clock and angular generator calculation retain only the original force collisions and swallowing of the new interior target; no auxiliary boundary-target stop is introduced.

Remark 4, journal p.664/PDF index5, writes a derivative squared for the radial clock. With the complex derivative used in the preceding normalization, a modulus is needed; an angular-derivative convention also gives the correct rate. The [clock discussion and linked provisional erratum](../articles/chordal-radial-sle.md#section-clock-convention) record this distinction and a half-plane-to-disk example. The preceding explicit clock calculation is already correct, and the coordinate-change theorem is unaffected.


## Mixed half-plane and strip forces

The [mixed-force article](../articles/mixed-sle-forces.md) completes the interior-mark calculation left out of the boundary specializations. C1GN takes real parts of the fractional-linear identity to obtain half-plane covariance. P3E9 uses the reflected strip convention to identify the driver under exponentiation, and 8GVO gives the equal compensating endpoint weights in half-plane or disk coordinates. These proofs keep the source's pre-collision and new-target restrictions.

Definition 2, Theorem 3, and Section 4 Definition 5 and its following assertion have been compared in [v3 HTML](https://arxiv.org/html/math/0505368v3) and the [journal PDF](https://nyjm.albany.edu/j/2005/11-31.pdf), pp.661–665. The comparison is textual. The half-plane destination needs a finite starting image under Definition 2. Theorem 3 omits that explicit condition, although Section 4 includes it. The [admissibility discussion and linked provisional erratum](../articles/mixed-sle-forces.md#section-starting-image) record the example m(z)=-1/z with starting point zero.

The coordinate and product-martingale proofs now cover the mixed configurations treated in Sections 3–5, subject to their stated local scope and the provisional source clarifications. The source's rare-event interpretations still require discrete scaling-limit identification and terminal control. Neither those steps nor trace geometry is certified by these calculations.
