# Boundary and bulk factorization

Read the Introduction, sections2/4 and section3's final martingale/normalization argument in [arXiv:1011.5822v3](https://arxiv.org/html/1011.5822v3), revised22 October2011, on17 November2026. Equation(20) was compared with extracted PDF p.11; no visual-PDF or journal comparison.

[XCYH](../articles/adaptive-three-point.md#section-boundary-factorization) proves the density cancellation and evaluates its gamma constant. The source density formulas are hypotheses there. Their SLE and spectral-theory proofs remain coverage obligations. The [surviving-boundary-index correction](../errata/beliaev-izyurov-factorization-2012.json#surviving-boundary-point) is provisional.

The theorem concerns triangular-site continuum probabilities, with mesh sent to zero before neighbourhoods shrink. Two boundary points and one bulk point remain after the boundary interval shrinks. The discrete-site passage is supplied by [Conijn](sources/conijn-factorization-1502.04387v3.md), not by changing the order of limits without proof.


The [Conijn continuation](sources/conijn-factorization-1502.04387v3.md) now proves the neighbourhood-to-site passage from the continuum formulas, including the boundary-interval limit. [V456](../articles/planar-factorization.md#section-interval-limit) supplies its strip-coordinate cancellation. The continuum SLE and spectral proofs remain separate obligations.


## Angular spectrum and stopped conditioning

Sections 1–4 have now been read in full in the versioned HTML. Selected covariance and stochastic/operator displays were compared with extracted PDF pp.2,6–8. The [continuum density article](../articles/continuum-connection-densities.md) supplies a weighted-form construction, the complete Jacobi spectrum, and the exact coefficient with uniform angular convergence. It also proves the boundary density from Cardy's formula and the stopped change of measure, with the limiting law justified on compact stopped sigma-fields.

The conditional and joint differential equations and conformal weights are separated explicitly. Three further [provisional corrections](../errata/beliaev-izyurov-factorization-2012.json) record the extra conditional boundary weight, missing density factor and missing square in the joint potential. The earlier index correction is preserved. No journal or visual-PDF comparison is claimed.

The radial-SLE identification, Cardy's theorem and domain Markov property remain inputs. The five-point strip-solution verification, terminal limits and integrable domination are still separate obligations; the local martingale calculation alone does not complete them.


## The strip candidate at the terminal exploration

The [terminal continuation](../articles/continuum-connection-densities.md#section-local-comparison) adds six assertions. QHTF/GXMS supply a local percolation comparison and the inverse conformal-radius moment under the conditioned law, using the alternating two-arm estimate. RD0Q gives one global bound for the strip candidate. AGJ2 writes its differential equation as a hypergeometric equation, with the stopped coordinate-change theorem explicit. X364 identifies all terminal limits, and SQJF uses dominated convergence and optional stopping to obtain the conditional density formula.

The terminal exploration geometry and residual domain Markov identification are stated as inputs. The stopped density calculation alone does not establish their limiting law. Foundational SLE convergence, radial identification, RSW, the arm exponent and coordinate-change theorem also remain inputs. The [Smirnov–Werner](sources/smirnov-werner-math0109120v2.md), [Rohde–Schramm](sources/rohde-schramm-basic-sle-2005.md) and [Schramm–Wilson](sources/schramm-wilson-math0505368v1.md) maps state the exact extent of the new source reading. No new correction to a published source is asserted by this integrability argument.


## The collision endpoint of the driving diffusion

Section 3 through the two-force system and Lemma 3.1 has been rechecked in the v3 HTML. The [driving-law continuation](../articles/continuum-connection-densities.md#section-force-collision) supplies four further assertions for the SDE displayed there, without altering the previously recorded source corrections.

HOKP proves finite collision with the right force point while the left gap stays positive. Its comparison process is justified by explicit scale and square martingales. QF08 controls the reciprocal right gap with a b log b estimate, giving finite limits of the driving function and both force points. 6EPL gives a Brownian first-passage upper tail and fractional-moment bound. 0SPP constructs the unique continuous driving law held constant at collision and identifies its compact restrictions with W3QF.

These are supplementary proofs for the source's driving system. They do not establish the terminal convergence of the finite-neighbourhood conditioned interfaces, a continuous trace through the collision, or the residual percolation law on the terminal domain. Those remain explicit inputs of X364/SQJF. No new erratum or Lean association is claimed.


## The coordinate-change premise in the candidate equation

[8Q5E](../articles/continuum-connection-densities.md#section-proved-coordinate-change) now completes the candidate's local equation with the required Möbius theorem proved in [C6T0/6RZ1/0INI](../articles/sle-coordinate-changes.md). The original AGJ2 statement and its explicit normalized hypergeometric computation are preserved. The boundary weights (2,-2) sum to kappa-6, and the candidate has only the bulk conformal weight, so the new target-change and martingale-transfer results apply exactly as stated.

This removes the separate coordinate-change theorem from the unproved inputs for this calculation. Basic deterministic Loewner theory and stochastic calculus remain foundations. Terminal convergence of conditioned interfaces, the residual percolation law and trace geometry are still not consequences of the local equation. No erratum or compiled association is added.


## Targeted journal comparison

On 20 November 2026, the [journal PDF](https://www.mathsoc.spb.ru/prize/2013/izyurov/Izyurov_Paper5.pdf), Communications in Mathematical Physics 310 (2012), 611–623, was compared in extracted text at the four existing errata. The [publisher record](https://link.springer.com/article/10.1007/s00220-011-1335-5) confirms the edition.

| Existing report | Journal locator |
|---|---|
| Conditional covariance | Display after Theorem 1.1, p.612 |
| Density-martingale factor | Section 3, dD_t display, p.616 |
| Joint-potential denominator | Theorem 3.2, (13) and proof, pp.617–618 |
| Surviving boundary index | Proposition 4.1, (20), p.621 |

The extracted text retains all four discrepancies. [Their repair assessments](../errata/beliaev-izyurov-factorization-2012.json) are unchanged and provisional. PDF images were unavailable; this is neither visual verification nor a full-paper audit.
