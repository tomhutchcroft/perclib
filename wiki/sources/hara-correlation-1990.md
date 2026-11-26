# Hara: exponential correlation length

[Hara (1990), Probability Theory and Related Fields 86, 337–385](https://doi.org/10.1007/BF01208256) defines mass by axial exponential decay. Relevant passages were read in the [publisher PDF](https://link.springer.com/content/pdf/10.1007/BF01208256.pdf), in extracted text: Section 1.1, (1.1)–(1.2), p.340; Appendix A, Propositions A.1–A.3 and Corollary A.4, pp.371–376. No visual formula check is claimed.

The [tilted-susceptibility article](articles/tilted-susceptibility.md) proves the finite-range case using the wiki's first-exit kernel. Symmetry permits an unweighted iteration before taking weighted sums. This yields joint openness, identifies the true mass, proves boundary divergence and gives parameter continuity. The conditional lace application now uses that mass.

The uniform tilted diagram estimates in Sections 3–5 remain a separate obligation. This reading does not establish their constants, extend the new proof to infinite-range kernels, or complete the correlation-length exponent theorem. The [existing reciprocal entry](errata/heydenreich-hofstad.json#mass-susceptibility-reciprocal) remains partial and provisional. No new source error or Lean association is asserted.

## The qualitative tilted bootstrap completed

The Section 5 framework and Lemma 5.1 discussion, pp.366–368, were also read in the publisher's extracted text. The [new proof](articles/tilted-fourier-bootstrap.md) takes a different, deliberately coarse route: it transfers each entire chain to a symmetric majorant, bounds two coordinate moments through an integral of C^20, and improves the complex quotient. Continuity closes the tilt interval without assuming convergence of the coefficient series beforehand. The endpoint estimates then prove the exponential length law and a simple-pole residue in sufficiently large dimension. This supplies the missing qualitative coefficient input above; the paper's constants, numerical thresholds and spread-out result are not reproduced.
