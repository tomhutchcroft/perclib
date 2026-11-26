# Reimer on a countable edge set

The [new article](articles/countable-reimer.md) keeps finite and infinite certificate conventions distinct. Its full-witness result is an outer-probability bound for Borel events, with ordinary probability available for increasing Borel events and for G-delta events. The finite nonmonotone theorem remains a cited input, not a new compiled result.

| Source and locator | Reading and coverage |
|---|---|
| [Hutchcroft–Lin, PIMS 2025](https://web.stanford.edu/~lindrew/PIMS-percolation.pdf), Remark 47 and Theorem 48, printed pp.25–26; proof of Theorem 46, pp.27–28 | Extracted text read. The increasing-event analytic projection is supplied explicitly. General Borel full-witness measurability is not asserted. |
| [Borgs–Chayes–Randall](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-98-42.pdf), Theorem 2.1 and Lemma 4.1 | Sections 1–3 and the start of Section 4 through the reduction read in extracted text. Finite arbitrary-product and fair bit-flip bounds are cited inputs. The main combinatorial lemma's proof is not claimed as read or reproved. |
| [Arratia–Garibaldi–Hales](https://arxiv.org/pdf/1508.05337v3), Section 7, (23)–(26), Theorems 9–10 | Section read in full in extracted text. Its finite-certificate convention and exhaustion are distinguished from full certificates. The new compactness and open-enlargement proof is stated for Bernoulli coordinates. |

The direct application separates a path suffix from a prefix together with all closed edges. It needs no finite cluster or finite susceptibility, although the existing downstream statements retain their own hypotheses. This is an extension of scope, not a correction to the cited sources; no erratum is created.

## Measurable classes and full-graph applications

Four further assertions in the [article](articles/countable-reimer.md#section-open-partner) strengthen its usable scope without changing the existing results:

- A Borel event paired with an open event has **Borel** full disjoint occurrence. Reducing the open certificate to a finite set leaves only finitely many completions to test for the other event.
- For order-convex Borel events, the least and greatest completions test the whole certificate. This gives an analytic projection for pairs mixing that class with G-delta inputs.
- Finite and countable simultaneous families satisfy the full-certificate outer bound; the listed classes have ordinary completed probability. A zero product gives a null event even for arbitrary Borel inputs. No associativity or compatible-witness limit is assumed.
- A weighted path-tail inequality follows directly from the full closed-edge certificate. With endpoints in a finite observation window, it requires neither finite clusters nor finite susceptibility.

[Hutchcroft–Lin PIMS](https://web.stanford.edu/~lindrew/PIMS-percolation.pdf), Remark47, Theorem48 and the following paragraph, printed pp.25–26, were rechecked in extracted text. [Arratia–Garibaldi–Hales v3](https://arxiv.org/pdf/1508.05337v3), Section5/Theorem5 and Section7/(23)–(28)/Theorem9, printed pp.8 and10–11, were also read in extracted text. Their certificate conventions are distinguished from the new deductions. No claim of general Borel full-witness measurability, visual PDF comparison or new formal verification is made. Finite nonmonotone Reimer remains a cited input; this is an extension, not a new erratum.


## Conditioning after an exploration

The [terminal product-law proof](../articles/countable-reimer.md#section-terminal-exploration-law) permits infinitely many adaptive queries. A finite set of edges that is never queried keeps its product distribution against every bounded terminal-history test; cylinder identities then identify the full conditional kernel.

The [conditional full-certificate theorem](../articles/countable-reimer.md#section-conditional-full-reimer) applies the existing outer Reimer bound on the unqueried cube. It separately proves measurability jointly with the transcript for the existing order-convex/G-delta classes and for a Borel event with an open partner. Observed edges are common background information, so the averaged bound involves a product of conditional probabilities, not the product of the original probabilities.

These are deductions from the article's earlier full-edge extension, not newly read source passages or source corrections. The finite nonmonotone theorem remains an input. Arbitrary-Borel full-witness measurability, independent mathematical review and Lean formalisation remain separate.


## The finite premise is now proved in prose

[Borgs–Chayes–Randall, MSR-TR-98-42](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-98-42.pdf), Sections 3–5, printed pp.3–16, were read through in extracted text, including Lemmas 4.1 and 5.2, the matrix proof, and the alternative tensor expansion. This extends the earlier reading record, which stopped before the main combinatorial proof. The connector did not return usable screenshot images, so no visual PDF comparison is claimed.

The [counting lemma](../articles/countable-reimer.md#section-finite-reimer-counting) gives an explicit mod-two triangular expansion in fixed coordinate order, then uses orthogonal spans over the reals. The [finite theorem](../articles/countable-reimer.md#section-finite-reimer-proof) supplies both the fair bit-flip and arbitrary-product bounds. Face counting establishes the uniform product bound; whole independent bit blocks and continuity give the finite-alphabet generality, including zero atom probabilities.

The [completed countable deduction](../articles/countable-reimer.md#section-full-reimer-completed-proof) discharges the earlier finite premise at the level of the written proof. It preserves the distinction between outer probability and the established measurable cases, including conditional exploration. No new formal verification or general arbitrary-Borel full-witness measurability follows. The earlier source records and conditional statements are preserved.



## Weighted path moments and exponential truncation

The [weighted path theorem](../articles/intrinsic-geometry.md#section-decreasing-path-moments) combines simultaneous full-certificate Reimer with the weakly ordered path-mark argument already used for chemical-distance moments. All closed edges stay in the first certificate, retaining an arbitrary decreasing Borel test. Two explicit weighted two-point row bounds control the chain sums. Layer-cake integration allows soft volume tests; the moment series gives an exponential tail.

The [averaged-path corollary](../articles/intrinsic-geometry.md#section-exponential-averaged-paths) strengthens the error term in the existing treatment of Part III, Lemma III.4.3. It keeps the finite-susceptibility hypotheses and permits an arbitrary cluster class because that class is discarded from the error. The proof works directly on the full countable edge set.

These are deductions from the existing written arguments, not newly read source passages or assertions that the paper states these stronger estimates. No additional erratum or Lean evidence is recorded.



## Independent real marks and measurable certificates

The [mark extension](../articles/countable-reimer.md#section-real-edge-marks) samples each real mark from a whole countable block of fair bits. Mark certificates lift to disjoint blocks; the inclusion need not be an equality. A disintegration argument proves the outer-probability transport step for arbitrary subsets, including fibers of probability zero. Uniform marks also retain the exact reflection identity. This applies to common-mark couplings of different percolation parameters without finite susceptibility.

The [measurability result](../articles/countable-reimer.md#section-mark-measurability) treats simultaneous order-convex Borel and G-delta inputs. For a Borel event with an open partner it proves coanalyticity, and explains why the earlier Boolean Borel conclusion fails for real marks. The non-Borel example uses the standard descriptive-set-theoretic existence of a Borel set with analytic non-Borel projection. General arbitrary-Borel full-certificate measurability remains unresolved here.

These are new deductions from the article's completed Bernoulli argument, using standard Borel disintegration and analytic-set facts. No additional paper passage was read or attributed this result, no source error is alleged, and no independent review or Lean formalisation is claimed.



## Adaptive threshold observations

The [partial-observation theorem](../articles/countable-reimer.md#section-partial-mark-exploration) extends the earlier complete-mark exploration argument to repeated adaptive observations of a single coordinate. A countable family of polynomial moment identities and bounded martingale convergence identify the terminal product conditional law. The [threshold corollary](../articles/countable-reimer.md#section-threshold-posterior) makes the marginals explicit: independent uniforms on the intervals left by the comparisons, with point masses when an interval collapses.

The [conditional Reimer theorem](../articles/countable-reimer.md#section-threshold-conditional-reimer) uses closed posterior intervals, including boundary completions of probability zero. It gives simultaneous product bounds and posterior-interval reflection, and proves measurability jointly with the transcript for the stated classes. The exact set satisfying all strict comparisons can omit boundary points; no equality with that alternative certificate convention is claimed. Shared information remains inside the conditional probabilities before averaging.

These are deductions from the existing written Reimer and exploration arguments, not newly read paper statements or new errata. The proof's standard measure-theoretic inputs and its arbitrary-Borel measurability limitation are explicit. Independent review, formal correspondence and Lean verification remain pending.



## Exact admissible threshold intervals

The [exact-constraint theorem](../articles/countable-reimer.md#section-observed-mark-constraints) identifies whether the supremum of the strict lower tests was attained, retaining precisely the endpoint convention forced by the answers. A coordinatewise sampling map stays inside these intervals on every input. At a half-open interval it sends both sampling endpoints to the included endpoint; the associated involution fixes that endpoint. This gives the full outer product and reflection bounds without the closed-box enlargement.

The [measurability result](../articles/countable-reimer.md#section-observed-mark-measurability) handles closed/decreasing families, G-delta/order-convex families when only finitely many lower endpoints are excluded, and arbitrary Borel finite-coordinate families. The countable-family case in the last class uses compactness of the finite witness-choice spaces. An explicit open-set example explains why the earlier finite-subcertificate reduction cannot simply be transferred to a noncompact exact admissible space.

These are further deductions from the wiki's existing written proofs, not newly read source statements or new errata. General arbitrary-Borel full-certificate measurability and further exact-constraint open-partner results are not claimed. Independent review and Lean correspondence remain pending.



## Thresholded percolation and conditional disjoint paths

The [binary reduction](../articles/countable-reimer.md#section-threshold-percolation-reimer) distinguishes edges whose state is forced by every admissible mark from those with two possible states. The latter can include an edge with conditional open probability zero. Explicit representatives lift every binary completion back to admissible marks, proving equality of the full certificate events. Compactness of the binary space then restores the Borel/open-partner result for thresholded events, even when the mark space is noncompact. Jointly Borel order-convex inputs may also depend on the terminal transcript.

The [connection theorem](../articles/countable-reimer.md#section-explored-disjoint-connections) applies this to finite paths on a countable graph, with thresholds and endpoints chosen from the transcript. Only edges whose binary state can vary must be disjoint; forced-open components are shared background and may be contracted, retaining physical edge labels. The countable-family path event is treated as an analytic projection, without assuming compatible limits of separately chosen finite families.

These are written deductions from the existing exploration and Reimer proofs. No new paper passage was read, no new erratum is alleged, and no independent review or Lean verification is claimed. Arbitrary Borel mark events outside the stated classes retain the earlier measurability limitation.



## Cluster restoration and the unrestricted correlation gap

The [restoration theorem](../articles/countable-reimer.md#section-cluster-restoration) uses the existing priority exploration without a size cutoff. Every edge touching the root cluster is eventually queried, even on an infinite-degree graph. The terminal product kernel proves that replacing the exterior by an independent configuration preserves the full product law and leaves the root cluster unchanged. Conditional on the transcript, the original and restored configurations are independent with the same law. Taking a further conditional expectation gives the exterior law given the cluster vertex set, without conditioning on positive-probability cluster atoms.

The [two-cluster comparison](../articles/countable-reimer.md#section-unrestricted-cluster-gap) uses this coupling to remove the finite-cluster assumption from the earlier written theorem 1AC7. The first functional may be arbitrary nonnegative; the second must be increasing. Only their original cluster evaluations need be Borel. Extended nonnegative expectations are permitted; covariance is formed only under the stated finiteness hypotheses. This supplies the missing written restoration-law argument in the [cluster-correlation interface discussion](../articles/harris-inequality.md#section-cluster-interface), while leaving that historical inventory and all existing tags unchanged.

These deductions use the already written exploration and Harris proofs. No new paper passage was read, no new erratum is alleged, and no compiled proof or independent correspondence review is claimed. The unrestricted cluster-correlation target now has a prose proof here; its Lean implementation and review remain separate.



## Distinct cluster families and large-cluster counts

The [multi-cluster theorem](../articles/countable-reimer.md#section-several-distinct-clusters) permits one arbitrary nonnegative cluster functional and increasing functionals for the other roots. Its first certificate contains all edges touching that cluster, while the others contain only their internal open edges. On the distinct-cluster event these full certificates are disjoint even for infinite clusters. A measurable subset of the full disjoint-occurrence event is enough for the outer bound; no general Borel measurability assertion is introduced. Tonelli gives the finite-family product inequality, and bounded decreasing products give the countable-family version for functionals in [0,1]. A one-edge example rules out two arbitrary nonmonotone factors.

The [finite-window application](../articles/cluster-partitions.md#section-large-cluster-counts) counts root tuples in distinct large full-cluster intersections. Each ordered tuple of blocks supplies at least the threshold to the power of the number of roots, yielding factorial-moment, generating-function and ordered-volume upper bounds. The theorem includes empty windows and infinite full clusters. Its Poisson generating-function bound is explicitly distinguished from stochastic domination, and its mean-field volume scale retains the one-cluster tail as an input.

These are written deductions from the existing full-edge Reimer and cluster-partition arguments, not newly read source passages or new errata. No compiled proof, independent correspondence review or matching volume lower bound is claimed.
