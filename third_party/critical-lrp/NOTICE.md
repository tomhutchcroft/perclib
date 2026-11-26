<!--
Retained from `third_party/critical-lrp/NOTICE.md` of the source repository `yujinhkim/lrp`,
branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, as Apache-2.0
§4(d) asks. Passages that do not concern the Lean sources adapted into perclib are omitted;
each omission is marked "[…]". File paths below are relative to the source repository, not
to perclib. See `README.md` in this directory.
-->

# CriticalLRP migration: sources and third-party notices

The `PercLib/CriticalLRP/` modules were migrated from
<https://github.com/yujinhkim/Critical-Long-range-percolation> at integration
revision `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Migration changes include
namespace and module-system conversion, Elan/Mathlib compatibility fixes,
use of native PercLib bond percolation definitions, and associated proof repairs.

PercLib Lean sources and tooling are contributed under Apache License 2.0.
[…]

## OpenAI mathematical code

The migrated `BK/Graph.lean` and `BK/Association.lean` include adapted material
from <https://github.com/openai/math>, commit
`4eaee87548250b2682affda7d05d947c05554bae`:

- `lean/OAI/Probability/UnimodularPercolation/Graph/Basic.lean`
- `lean/OAI/Probability/UnimodularPercolation/ProductMeasure/Association.lean`
- related tail-product proof ideas in `CountableProduct/ZeroOne.lean`.

The upstream material is Apache License 2.0; its licence is retained here as
`OPENAI_MATH_LICENSE.txt`. Module layout, namespaces and some statements were
changed during the original formalization and again during migration.
File-specific notices remain in the modules. No correspondence between the
migrated statements and the source paper is inferred from compilation alone.

## Mathematical source, not a bundled proof

The finite-spanning-tree construction in `Tightness/TreePieces.lean` follows the
partition method of Tom Hutchcroft's *Power-law bounds for critical long-range
percolation below the upper-critical dimension*, arXiv:2008.11197v2, Lemma 2.4.
The formal statement is modified to rooted pieces containing between `lam` and
`2 * lam - 1` marked vertices; it is not that source lemma verbatim and does not
prove universal tightness by itself.

The mathematical target is Hutchcroft, *Critical long-range percolation I:
High effective dimension*, arXiv:2508.18807v1. The paper has not been completely
formalized. See `docs/CRITICAL_LRP_COVERAGE.md` for the retained 75-item source
coverage ledger and its qualifications.
