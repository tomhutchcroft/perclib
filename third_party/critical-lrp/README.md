# Licence and notice for the long-range port

Sixty-two Lean files under `PercLib/` adapt code, definitions, statements or arguments
from the formalisation of T. Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1), by contributor yujinhkim: repository `yujinhkim/lrp`, branch
`critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, migrated from
<https://github.com/yujinhkim/Critical-Long-range-percolation> at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. That source is licensed under the Apache
License, Version 2.0. As Apache-2.0 §4(a) and §4(d) ask of a redistributor, this
directory holds:

- `LICENSE`: the Apache License, Version 2.0, under which the source is distributed.
- `NOTICE.md`: the attribution notice of the source (its `third_party/critical-lrp/NOTICE.md`),
  with the passages that do not concern the adapted Lean sources omitted.
- `OPENAI_MATH_LICENSE.txt`: the Apache License, Version 2.0, of `openai/math`, which the
  source's notice names for material in its `BK/Graph.lean`, `BK/Association.lean` and
  `CountableProduct/ZeroOne.lean`. It is kept because the notice refers to it; no perclib file
  lists those source files among its sources.

Each adapted file credits the source in its own header (repository, branch, commit, source
paths, licence and changes). `docs/PORTED_FILES.md` lists the 62 files with their source
paths, and the other outside sources of perclib.
