# Hypercube mixing and the finite triangle

The [new article](articles/hypercube-mixing.md) proves the walk estimates and a conditional finite-triangle criterion. It does not certify the full hypercube percolation theorem.

| Source and locator | Reading and coverage |
|---|---|
| [Heydenreich–van der Hofstad](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), 17 March 2017 manuscript, Section 13.4, printed pp.168–178 / PDF indices179–189 | Section read in full in extracted text. The continuous-time exercise, non-backtracking mixing conclusion and finite-triangle implication have written proofs. |
| Theorem 13.18; Exercises 13.10–13.11 | [Exact continuous-time threshold](articles/hypercube-mixing.md#section-continuous) and [two-time NBW mixing](articles/hypercube-mixing.md#section-mixing). The parity mode is separated explicitly. |
| Lemma 13.15; Theorem 13.13(a) | [Long-path bound](articles/hypercube-mixing.md#section-long-paths) uses the threshold T+1 so both prefix cuts exist. The [explicit triangle estimate](articles/hypercube-mixing.md#section-triangle) retains its mixing and short-loop hypotheses, both proved for the hypercube at the stated time scale. |
| Theorem 13.13 remaining parts; Lemma 13.19; Exercise 13.12 | The [short-loop input](articles/hypercube-mixing.md#section-short-loops) is proved by a Fourier-moment estimate. Critical-parameter location, the boundary-sharing estimate and sprinkling remain separate. A cited growth recurrence is not treated as proved by its stated consequence. |
| Historical Open Problems 13.3–13.4 | Recorded as manuscript-era context; no claim that they remain open today. |
| [Fitzner–van der Hofstad](https://rhofstad.win.tue.nl/NBW_fin.pdf), author PDF dated 14 January 2012, Section 3.3; [arXiv:1212.6390v1](https://arxiv.org/abs/1212.6390v1), December 2012, (3.12)–(3.15) and Section 3.3 | January Section 3.3 read in full; the norm step and corresponding December hypercube passages compared. The new scalar proof recovers the mixing conclusion. The sharper coefficient-one estimate and general torus statements remain outside this workaround. |
| [van der Hofstad–Nachmias](https://ems.press/content/serial-article-files/32188), JEMS 19 (2017), Sections 3.4–3.5, Lemmas 3.11–3.14 | Extracted passages read through Lemma 3.14 and the start of Lemma 3.15. Endpoint clocks and zero-time recurrence are distinguished. Exact-distance and restricted-connection estimates are not claimed as proved by the simpler long-path argument. |

The three source pages retain provisional diagnoses, explicit repair status and the significance of the changes. No author confirmation, new Lean association, visual PDF comparison or journal comparison of the Fitzner–van der Hofstad preprint is claimed. Section 13.5 of the book has only been started, through its exploration introduction.

## Subsequent critical-parameter proof

The [critical-parameter article](articles/hypercube-critical-parameter.md) now proves the susceptibility-threshold upper bound through a corrected boundary-growth induction, and supplies the sharper short-loop estimate. It concludes the finite triangle bound uniformly up to that threshold. The earlier article and its tagged statements are preserved. See the [new reading map](sources/hypercube-critical-parameter.md) for source versions and the provisional repairs.
