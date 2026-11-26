# Source-correction concordance: b20bbd7

This guide connects the reading maps to 11 existing errata entries across five sources at b20bbd7. That critical-methods revision is unmerged. Every entry is provisional: these are recorded discrepancies and proposed fixes or workarounds, not author-confirmed corrections. Repeated issues in different sources retain their separate source locators. The count is not a count of distinct mathematical errors or completed proofs.

The tables below are reading pointers, not another errata registry. The pinned records contain the exact source locator, original claim, explanation, correction, affected assertion tags, issue links and consequences for Lean. The linked reader pages can advance after this snapshot.

Editorial status, a mathematical replacement proof and formal correspondence are separate. The errata renderer obtains formal evidence from the compiled manifest and fingerprint-bound review records. No proof status is inferred here from a tag, a Lean filename or a proposed repair.

## Duminil-Copin–Tassion sharpness paper, arXiv v3

[Pinned source records](../errata/dct-sharpness.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [The intensity derivative uses closed pivotality](../errata/dct-sharpness.json#closed-pivotal-derivative) | Restore the closed-edge factor when the pivotal event is state independent. | Wire the finite exterior, condition on unexplored bonds and pass to the limit afterwards; do not differentiate an infinite limit formally. |
| [Critical field lower bounds require saturation](../errata/dct-sharpness.json#critical-field-saturation) | Restrict the printed power bound to small fields, or saturate it at one. | 36PN supplies a percolation replacement under its explicit hypotheses. It does not supply the separate Ising small-field proof. |

## Hierarchical critical two-point paper, arXiv v1

[Pinned source records](../errata/hutchcroft-hierarchical-2021.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [Finite-volume quantiles need only a one-sided limit](../errata/hutchcroft-hierarchical-2021.json#quantile-continuity) | Use local constancy from the left at a finite positive endpoint, through continuity of fixed tail probabilities and quantile minimality. | Do not assume global continuity of an integer-valued quantile; the helper alone does not prove the hierarchical estimate. |
| [The quantile estimate at zero intensity](../errata/hutchcroft-hierarchical-2021.json#zero-intensity-division) | Keep the squared estimate with intensity times quantile squared on the left, so zero intensity is included. | Divide only at positive intensity; the critical passage also needs the finite-threshold proof. |
| [Uniform truncation must retain the intensity scale](../errata/hutchcroft-hierarchical-2021.json#scaled-truncation) | Retain the intensity-dependent cutoff or a constant multiple of the block-maximum quantile. | The route 12NL to 2XJX to 655W needs rooted tails and the squared quantile estimate; a small discarded probability does not control discarded expectation. |
| [The finite-set criterion requires the root](../errata/hutchcroft-hierarchical-2021.json#root-containing-criterion) | The finite sets in the critical boundary criterion must contain the root. | Duminil-Copin–Tassion already include this hypothesis; the omission is in the hierarchical quotation. |
| [The critical lower bound retains a coefficient](../errata/hutchcroft-hierarchical-2021.json#susceptibility-lower-coefficient) | Retain the boundary-flux coefficient and finite positive critical intensity. | An upper kernel envelope alone does not imply finite critical intensity. The comparability statements are unchanged. |
| [The supercritical density comparison uses a minimum](../errata/hutchcroft-hierarchical-2021.json#density-saturation) | Saturate the near-critical density scale with the minimum of the intensity increment and one. | The diagram criterion does not itself supply the probabilistic near-critical comparison. |

## Power-law bounds paper, arXiv v2

[Pinned source records](../errata/hutchcroft-powerlaw-2021.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [The amplification exponent starts at one](../errata/hutchcroft-powerlaw-2021.json#amplification-zero-iterate) | Require at least one amplification iteration; the constants 1/9 and 27 are retained. | Use the corrected marked-tree argument for full-cluster intersections. No compiled proof follows from the repair note. |
| [The recursive partition threshold](../errata/hutchcroft-powerlaw-2021.json#recursive-retaining-threshold) | Retain small marked pieces at the corrected recursive threshold; keep vertex coverage and disjoint edge sets. | Endpoint sets may overlap. BK applies to disjoint edge witnesses, not a disjoint vertex partition. |

## Triangle-condition paper

[Pinned source records](../errata/hutchcroft-triangle-2021.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [Positive part in the nontransitive boundary bound](../errata/hutchcroft-triangle-2021.json#boundary-positive-part) | Use the squared positive part of the boundary deficit, or the stronger outgoing-mass bound. | Constant susceptibility is needed before dropping the positive part; the transitive application is unchanged. |
| [The stronger quantitative triangle numerator](../errata/hutchcroft-triangle-2021.json#triangle-numerator) | Use the weaker differential inequality 4KBG and its almost-everywhere qualification. | A proof of this replacement does not certify the stronger printed numerator; retain the separate integration argument. |

## L2 and reverse-BK source

[Pinned source records](../errata/hutchcroft-l2-2020.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [The reverse-BK switching cancellation](../errata/hutchcroft-l2-2020.json#reverse-bk-cancellation) | Retain the overlap term in the exact interpolation increment. The bubble-only comparison remains open. | Independent-copy separation and stronger triangle hypotheses do not close this dependency. |

## Newly merged comparison routes

The [b086702 library map](sources/perclib-b086702.md) identifies source interfaces relevant to several of these checks. In particular, the positive-index tail sum and finite-coordinate intensity derivatives can now be compared directly with merged source. A file-level match still needs an exact assertion association and review of hypotheses before it changes a displayed correspondence status.

The proposed corrections above do not resolve the bubble-only reverse-BK comparison, the Ising field proof or the probability implication from the hierarchical triangle criterion to its near-critical density conclusion.

## Finite-quantile follow-up on merged main

The [b65a568 library map](sources/perclib-b65a568.md) records the finite-vertex left-stability and positive-endpoint transfer lemmas added by the merged quantile package. Their source contracts require finite ambient vertices, not merely a finite observation window; the endpoint bound requires a positive endpoint. They supply the helper used by the one-sided quantile workaround, while the hierarchical bound itself and its reviewed correspondence remain separate. This follow-up does not change the historical erratum inventory or its provisional diagnoses.
