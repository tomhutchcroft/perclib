# Hara: convolution estimates behind spatial asymptotics

Appendix B of the [author-hosted published paper](https://www2.math.kyushu-u.ac.jp/~hara/papers/AOP_36_530.pdf), *Annals of Probability* 36 (2008), 530–593, has been read in extracted text: printed pp.588–592 / PDF indices58–62. The opening theorem and selected statements around Theorem 1.4 and Corollary 1.6 have also been read. This is not a full-paper reading or a reproduction of the Gaussian lemma. The PDF is identified as the published version on the author's paper list; visual-page verification remains unavailable.

| Locator | Reconciliation |
|---|---|
| B.1(i), B.1–B.2 | [IDIL](articles/spatial-convolution-asymptotics.md#section-bounds) proves the two power-law regimes by a spatial split. Unstated logarithmic endpoints are not included. |
| B.1(ii), B.3–B.4 | [MZ23](articles/spatial-convolution-asymptotics.md#section-remainder) proves the quantitative remainder. The primary paper specifies symmetry and an exponent strictly between zero and two; only evenness of the convolving kernel is needed in the written proof. Without evenness, the proved range is zero to one. |
| B.1(iii), B.5–B.6 | The borderline pointwise majorant for a summable convolving kernel is read. The leading-term proof below supplies the needed regional estimates; no standalone stronger endpoint theorem is asserted. |
| B.1(iv), B.7–B.24 | [NIAD](articles/spatial-convolution-asymptotics.md#section-leading) gives the full three-region argument for a signed kernel, including zero total mass in the additive formulation. The [B.18 entry](errata/hara-nearest-neighbour-2008.json#convolution-decomposition-sign) records a complete notation-level sign repair; the absolute estimates are unchanged. |
| Theorem 1.4; Corollary 1.6 | Their hypotheses and role in the spatial lace argument are identified. The Gaussian lemma's proof and the model-specific verification of its pointwise assumptions remain separate reading tasks. |
| Heydenreich–van der Hofstad, Exercise 11.6, 11.2.16 | [UDUU](articles/spatial-convolution-asymptotics.md#section-obstructions) gives explicit shift obstructions to an unrestricted remainder exponent. MZ23 supplies the corrected lemma; the [book entry](errata/heydenreich-hofstad.json#convolution-remainder-scope) is a statement-level repair. |
| Book 11.2.13–11.2.15 | [I8BE](articles/spatial-convolution-asymptotics.md#section-transfer) checks the exact exponent range and transfers the assumed Green asymptotic with its 2/d remainder. It does not prove the assumed Green or coefficient estimates. |

Both provisional diagnoses have fixes found: an intermediate sign correction in the published paper and a hypothesis correction in the book exercise. The latter leaves the intended application intact. No author confirmation or new compiled association is claimed.

## Gaussian lemma reading completed

The later [Gaussian reading map](sources/hara-2008-gaussian.md) now covers Sections 2.1–2.6 and links a complete written proof of the signed-kernel spatial theorem and its quantitative remainder. The all-order pointwise coefficient estimate and the model-specific improving bootstrap remain separate.


## Boundary exponents and coordinate symmetry

[7PTP](articles/spatial-convolution-asymptotics.md#section-even-endpoint) treats the second-order boundary omitted from MZ23: an even kernel with a borderline second moment gives a logarithmic error, removed by an absolute finite second moment. [SNY9](articles/spatial-convolution-asymptotics.md#section-cubic-cancellation) uses coordinate reflections and permutations to cancel the truncated quadratic term through harmonicity of the Green power. This retains the stated power remainder from exponent two up to, but excluding, four; the fourth-order boundary has a logarithmic upper bound, removable under an absolute finite fourth moment.

[1ADM](articles/spatial-convolution-asymptotics.md#section-endpoint-obstructions) gives an even anisotropic kernel with a positive logarithmic second-order error, and the nonzero fourth-order error for the uniform nearest-neighbour kernel. These are independent written extensions, not a new source reading or a claim that the primary source's strict range is erroneous. The dimension-six example is conditional on both spatial input estimates. Existing errata, their fix/significance classifications, and their provisional status are unchanged; independent review and Lean formalisation remain pending.
