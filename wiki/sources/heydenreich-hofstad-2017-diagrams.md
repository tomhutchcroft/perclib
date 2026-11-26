# Heydenreich–van der Hofstad: bounding the lace coefficients

Read Chapter 7 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.69–88, PDF indices80–99. This is an extracted-text reading; visual-page and published-edition correspondence remain unchecked. Reading the chapter does not mean that every bound in it has been supplied.

| Locator | Reconciliation |
|---|---|
| Section 7.1; 7.1.1–7.1.12 | [3W22](articles/lace-coefficient-diagrams.md#section-critical-convergence) supplies absolute coefficient summability and critical passage under a small critical weighted triangle. [AA7H](articles/lace-coefficient-diagrams.md#section-infrared-smallness) derives that smallness from explicit uniform infrared and edge-mass premises; their bootstrap is still separate. |
| Exercise 7.1; 7.1.13–7.1.17 | Moment and small-frequency discussion. A signed-kernel argument must justify absolute weighted summability before exchanging moments and convolution sums. This part remains to be reconciled in full. |
| Lemma 7.1; 7.2.7–7.2.12 | [SJIL](articles/lace-coefficient-diagrams.md#section-mass) gives the zeroth-coefficient mass bound; [NJT0](articles/lace-coefficient-diagrams.md#section-weighted) gives its weighted bound. The former also bounds the absolute Fourier transform. |
| Lemma 7.2; 7.2.13 | [SJIL](articles/lace-coefficient-diagrams.md#section-mass) gives the first coefficient's sharper mass estimate by summing its eight-line diagram. |
| Lemma 7.2; 7.2.14; Lemma 7.3; Exercise 7.2; 7.2.31–7.2.37 | [NJT0](articles/lace-coefficient-diagrams.md#section-weighted) proves cosine splitting, the unrefined weighted estimate and the diagram's reversal substitution. |
| Lemma 7.2; 7.2.15; Section 7.5.3 | The refined first-order weighted estimate is read but not yet supplied. Its removal of the trivial contribution needs a separate diagram estimate. |
| 7.2.21–7.2.26 | [NCYU](articles/lace-coefficient-diagrams.md#section-witnesses) proves the path inclusions, and [SJIL](articles/lace-coefficient-diagrams.md#section-mass) performs the BK bound in independent configurations. |
| 7.3.2–7.3.9; Exercise 7.3 | [NCYU](articles/lace-coefficient-diagrams.md#section-witnesses) gives both intermediate cases by attaching the extra connection either to the prefix or to a terminal path. |
| 7.4.2–7.4.10; Exercise 7.4 | [SJIL](articles/lace-coefficient-diagrams.md#section-mass) defines the three diagram kernels and derives the general chain without dividing by connection probabilities. Its first-order instance is the earlier eight-line diagram. |
| Proposition 7.4; 7.5.3; Section 7.5.1 | [SJIL](articles/lace-coefficient-diagrams.md#section-mass) proves the transition-mass bound and hence the geometric estimate at every positive order. |
| 7.5.1–7.5.2; 7.5.4; Section 7.5.2; Exercise 7.5 | The higher weighted diagram, reversed-chain estimates and full weighted coefficient bound remain to be proved here. The mass estimate alone is not a substitute. |
| Section 7.6 | Outlook, not a new theorem. Chapter 8's infrared bootstrap remains a separate reading and proof task. |

All five assertions are written mathematical arguments, with formal status computed from the manifest. Critical continuity is justified by a fixed-order dominating diagram and then a geometric tail, rather than by monotonicity of the cutting event. No new source erratum, unconditional infrared theorem or compiled Lean association is asserted.

## Absolute moments in the overview

[QA8C](articles/signed-kernel-moments.md#section-convolution) now supplies Exercise 7.1 with absolute second moments and the first-moment cross terms before evenness is imposed. [IVH2](articles/signed-kernel-moments.md#section-fourier) gives the precise Fourier implication and its nonnegative converse. [QKRD](articles/signed-kernel-moments.md#section-signed-example) shows why the converse cannot control absolute moments of an arbitrary signed kernel. The source itself warns that its effective kernel need not be a probability law; this supplement does not list that warning as an error.

[22TW](articles/signed-kernel-moments.md#section-lace-moments) supplies the implication needed by the overview: summable frequency bounds for the nonnegative coefficients give absolute second moments for their signed sum. The effective quadratic term includes the step-law contribution, and its positivity is stated separately. The general weighted coefficient estimates and the bootstrap that establish those frequency bounds remain pending. Thus the earlier moment row is now resolved with these explicit hypotheses, without promoting the heuristic Fourier quotient to an established critical representation.

## Completing the weighted coefficient estimates

[RZML](articles/weighted-lace-coefficients.md#section-reverse) now proves Exercise 7.5 by a direct reversed-chain summation. [09JN](articles/weighted-lace-coefficients.md#section-weighted) supplies (7.5.4), including the two central diagrams in (7.5.27)–(7.5.29). Its route is specified algebraically, and the first central diagram is reduced to two factors of mass at most T and a weighted pair of size at most W.

[IT43](articles/weighted-lace-coefficients.md#section-refined) now supplies (7.2.15) with its stated constant 16. The proof removes the trivial triangles and gives the slightly stronger intermediate constant 31/2; it does not rely on the source's abbreviated intermediate constants. Thus the two earlier weighted-estimate rows are resolved. [VL4L](articles/weighted-lace-coefficients.md#section-summation) sums the bounds and links them to the absolute-moment criterion. The frequency bounds on W and H and the bootstrap of Chapter 8 remain separate. No source erratum or formal proof status changes.

## Polynomial moments and critical continuity

[KFUM](articles/higher-lace-moments.md#section-chain) extends the existing weighted chain to powers of displacement. [1VDI](articles/higher-lace-moments.md#section-core) bounds the second marked core by a weighted triangle. Under a spatial critical two-point bound and a small weighted triangle, [JJJN](articles/higher-lace-moments.md#section-critical) gives summable moments of every order beta<d-6, including convergence of the entire coefficient series in that weighted norm as p approaches pc. This is an independent consequence of the earlier diagram proof; it does not supply Exercise 11.4's all-order pointwise estimate or the improving spatial bootstrap. No source correction or compiled status changes.
