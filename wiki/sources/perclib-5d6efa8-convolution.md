# Doubling-kernel convolution contracts at 5d6efa8

This inventory covers all **five named public theorems** in the convolution module at private `lrp` revision 5d6efa862d99e11fb1f01619be7700b85c1c8f7b, inspected 16 November 2026. Imported declarations and anonymous witnesses are excluded. Source inspection is distinct from independent correspondence review and compiled association.

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Convolution.lean L27](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Convolution.lean) | An origin-zero extended kernel on any Abelian group, controlled by a subadditive finite gauge and a doubling constant D, has off-diagonal convolution at most 2DM times the kernel. D and M may be infinite; no symmetry or countability is assumed. | [Argument](../articles/walk-kernels.md#section-doubling-convolution) |
| [Convolution.lean L66](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Convolution.lean) | For s>=0, w nonzero and norm(w)<=2 norm(u), the raw inverse norm power at u is at most 2^s times that at w; the hypotheses force u nonzero. | [Argument](../articles/walk-kernels.md#section-power-convolution) |
| [Convolution.lean L78](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Convolution.lean) | The origin-deleted norm-power kernel obeys the same doubling comparison when both arguments are nonzero. | [Argument](../articles/walk-kernels.md#section-power-convolution) |
| [Convolution.lean L91](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Convolution.lean) | On a normed Abelian group, the off-diagonal convolution of an origin-deleted norm power is bounded by 2^(s+1) times its mass bound times the norm power, for s>=0. | [Argument](../articles/walk-kernels.md#section-power-convolution) |
| [Convolution.lean L105](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Convolution.lean) | On the supremum-norm lattice, exponent d+alpha with alpha>=0 gives the constant 2^(d+alpha+1) times the explicit mass bound; distinct endpoints remain required. | [Argument](../articles/walk-kernels.md#section-power-convolution) |

## Scope and endpoints

The general gauge is finite and nonnegative, but need not be symmetric or vanish at zero. The kernel is extended nonnegative and must vanish at zero. The algebra uses 0 times infinity equal to zero. One displacement in each convolution term is large enough to invoke the doubling comparison; reindexing each remaining mass sum uses group bijections, not symmetry of the kernel.

The argument requires an Abelian group, as in the source. The kernel and mass bounds are deterministic extended sums on an arbitrary index set, so countability is unnecessary. No product probability or independence claim is involved.

For the raw norm-power comparison, w nonzero and the norm inequality already force u nonzero. The explicit origin-deleted comparison states both nonzero hypotheses. Exponent zero is allowed, but finite mass is not inferred at that endpoint on an infinite group. The lattice specialization assumes alpha>=0 and retains a separate mass bound. The positive-alpha summability theorem 6VNM supplies that bound in positive dimension; alpha=0 does not. Dimension zero admits no distinct pair of endpoints.

The article's inverse-square example exhibits a finite mass and a useful numerical bound. Its explanation of the return convolution makes the endpoint restriction explicit: convolution at zero can be positive even when the kernel is zero there. No unrestricted convolution-power estimate is inferred. The source zero-kernel, exponent-two and finite-mass witnesses are excluded from the named-theorem count. All errata and prior article statements are unchanged.
