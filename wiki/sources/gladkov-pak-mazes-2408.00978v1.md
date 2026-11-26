# Randomized DFS and balanced percolation exploration

Read Nikita Gladkov and Igor Pak, [Exploring mazes at random, arXiv:2408.00978v1](https://arxiv.org/html/2408.00978v1), on 17 November 2026. The primary HTML text was compared with the [extracted PDF](https://arxiv.org/pdf/2408.00978v1), especially the main theorem and pivot argument on printed pp.3–4 and the exercises on pp.4–5. The graph-theoretic arguments below are written independently of the maze drawings. No visual-PDF or later-version comparison is claimed.

The main hypothesis is a finite connected graph of maximum degree three with the entrance and two exits all leaves. Planarity is not used. The key point is that changing a branching coin preserves the entire DFS tree: there are no edges between child subtrees, and the parent plus two child edges exhaust the degree at the pivot. This supplies the step left to the reader in the source.

| Source passage | Wiki proof | Scope |
|---|---|---|
| Main theorem; tree and general-maze proofs | [KRU2](../articles/adaptive-three-point.md#section-fair-dfs) | Measure-preserving pivot involution; also proves independent fair branch orders conditional on the discovery tree. |
| Notes on the proof; Exercise1 | Examples after KRU2 | A degree-three entrance, a nonleaf exit, or degree-four internal branching can destroy fairness for the usual uniform choice rule. |
| Exercise5 | [1QSK](../articles/adaptive-three-point.md#section-dfs-target-law) | General conditional leaf law and k-target bounds; sharp interval[1/4,1/2] for three exits and impossibility of probability1/3 in a finite fair-bit maze. |
| Exercise6 | [88CG](../articles/adaptive-three-point.md#section-dfs-edge-direction) | Exact criterion: nonbridges have fair first direction, bridges have the direction forced by the entrance component. |
| Exercise7 | [04ZU](../articles/adaptive-three-point.md#section-balanced-bond-search) | A fixed tree-port construction, rather than the pictured ring, preserves marked connectivity and gives the required degree/leaf hypotheses. It also works on nonplanar graphs. |
| Application in the decision-tree paper, Remark6.4 | [TWYR](../articles/adaptive-three-point.md#section-balanced-three-point) | Full proof of the displayed refined three-point bound, plus a finite-family improvement and a countable-graph extension. |

For the percolation application, all auxiliary tree edges are deterministically open and every original random edge retains its own coordinate. The construction precedes sampling. Conditional on any all-connected bond configuration, the auxiliary search reaches either target first with probability one half. The stopped Cauchy–Schwarz calculation includes the independent random seed; it does not assume that a fixed deterministic search is balanced. The method preserves connectivity, and its stopping targets are auxiliary leaf marks. No equivalence with ordinary DFS on the unsplit graph is claimed.

The geometric comparison of wall-following and DFS in Exercises2–4, including the drawing conventions and the necessary-and-sufficient condition requested in Exercise2, is not supplied here. The introduction's particular illustrations and random-walk exercise have not been numerically reconstructed. These remain explicit source-coverage tasks; the main fairness theorem and the applications listed in the table are proved. No error in this paper is asserted, and no erratum entry is added. Correspondence records remain pending and no compiled Lean association is inferred.
