# Marginal long-range models

Source: [Chen–Sakai, arXiv:1808.06789v3](https://arxiv.org/html/1808.06789v3). The setup, examples and main statements were checked in versioned HTML and PDF text. This map distinguishes imported estimates from the deductions written in the wiki; it does not claim a full audit of the paper or its journal version.

- [G12U](../articles/branching-random-walk.md#section-marginal-step-law): transition bound with a written proof from V7FQ, locator (1.13)–(1.14).
- [V7FQ/CEVT](../articles/branching-random-walk.md#section-marginal-local-limit): written symbol, local-limit and spatial-potential arguments for the concrete law. These include leading constants and the critical convolution case. The early-time estimate is G12U.
- [6ZYT](../articles/branching-random-walk.md#section-marginal-percolation): cited percolation input, locator §1.2.3 and Theorem1.4 (1.36), followed by written global comparison and diagram deductions. The lace-expansion proof remains external.
- [DTYB](../articles/branching-random-walk.md#section-compound-normalization): written mass calculation and local repair for the provisional [normalization erratum](../errata/chen-sakai-marginal-2019.json), locator (1.15)–(1.17). The other results use a different step law.

All source correspondences remain pending. The proof obligations and source-status limits also appear in the errata page; no compiled claim is added.


## All-lattice correction — 17 November 2026

[TIOJ](../articles/branching-random-walk.md#section-all-lattice-compound) uses the corrected normalization: include the origin in the denominator, matching the earlier arXiv:1204.1180v4 Appendix A (A.2), checked in its versioned HTML. It proves the normalization and cube support properties. DTYB's punctured alternative and original counterexample are preserved. The same erratum remains provisional; no new fault is counted. The earlier Appendix explicitly excludes alpha=2, so the marginal one-step, Fourier and heat-kernel estimates remain separate obligations for this corrected law.


## Discounted diagrams at the logarithmic boundary

[S4WN](../articles/branching-random-walk.md#section-logarithmic-killing) proves the exact leading coefficients for a symbol with a logarithmic correction, including the deficit when the critical diagram is finite. [Q7D7](../articles/branching-random-walk.md#section-marginal-killing-expansion) uses V7FQ's stronger symbol error to obtain a two-dimensional finite part and the next logarithmic corrections to the four-dimensional bubble and six-dimensional triangle deficits.

These are further written deductions for the clipped law already mapped here, not newly checked statements of Chen–Sakai. They use neither the transition bound G12U nor a near-critical percolation comparison. No new source fault or formal verification is asserted.


## Spatial potentials with killing

[C9HG](../articles/branching-random-walk.md#section-marginal-spatial-crossover) combines V7FQ's local limit with the transition bound G12U, which has a written proof from V7FQ, to obtain the spatial crossover profile for every convolution order. At the critical diagram dimension, [4XHU](../articles/branching-random-walk.md#section-marginal-surviving-fraction) gives the fraction of the undamped potential that survives, uniformly over all killing parameters. This distinguishes the scale of first reaching the spatial separation from the longer times that produce the critical logarithmic potential.

These are further deductions for the already specified clipped law. G12U has a written proof from V7FQ; no new source statement, source fault, near-critical percolation comparison or formal verification is asserted.


## Exact critical percolation convolution amplitudes

[B3YC](../articles/branching-random-walk.md#section-convolution-amplitude-transfer) proves a perturbation criterion for every factor of a convolution and verifies it for the clipped marginal walk using CEVT. [5DQV](../articles/branching-random-walk.md#section-marginal-percolation-amplitudes) applies that criterion to the cited critical two-point equivalent in 6ZYT, retaining the power of the bond-probability multiplier p_c. This gives exact off-origin bubble and triangle potential amplitudes in dimension six.

These are further written deductions from the already mapped inputs. The lace-expansion input remains cited; no new reading of Chen–Sakai, new source fault, near-critical percolation theorem or reverse-BK repair is asserted.
