# The hypercube critical parameter

[The article](articles/hypercube-critical-parameter.md) supplies the percolation input that was separate in the mixing article. All source corrections remain provisional.

| Source and locator | Reading and coverage |
|---|---|
| [van der Hofstad–Nachmias, arXiv:1210.8213v1](https://arxiv.org/pdf/1210.8213v1), Section3, printed pp.13–18 / PDF indices12–17 | Section read in full in extracted text. Lemma3.2 is proved by conditioning on the full walk history. Lemma3.3 and Proposition3.1 are reconstructed with the corrected frontier collision bound, explicit initial generations and full Reimer certificates. |
| [EURANDOM report2013-026](https://www.eurandom.tue.nl/reports/2013/026-report.pdf), Section3, printed pp.18–24 / PDF indices18–24 | Section read in full; the collision and off-ball problems persist, while the nonmonotone definition is already corrected to full certificates. Its unresolved cross-references are not used as locators. This comparison is not a check of the Metrika journal text. |
| [Hypercube percolation, JEMS19(2017)](https://ems.press/content/serial-article-files/32188), Lemma7.1, printed pp.793–796 / PDF indices68–71 | Lemma and proof read in full. Four simple-walk steps supply the fourth Fourier moment; the scalar bounds control the remaining resolvent sum. Both exceptional characters are retained as an explicit volume term. |
| [Heydenreich–van der Hofstad](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf),17March2017, Section13.4, Theorem13.13 and Lemma13.19 | The critical-parameter input and both walk inputs are now proved in prose, yielding the finite triangle estimate uniformly below the susceptibility threshold. No matching three-term lower expansion is claimed. |

The corrections preserve the critical upper bound, including its coefficient7/2, and the finite triangle conclusion. They do not establish the giant-component, sprinkling or scaling-limit results. Finite nonmonotone Reimer remains an explicitly cited input. No new Lean verification, visual PDF comparison, journal comparison of the survey, or independent review is claimed.

A later-paper audit lead remains separate: JEMS AppendixA.6, (A.49)–(A.54), has field-monotonicity and small-parameter regime questions that require the preceding hypotheses and source versions to be checked. That passage has not been fully audited and no correction or erratum is asserted here.

## Sharp field growth and the 2017 appendix

The [sharp-field map](sources/sharp-supercritical-field.md) supplies the factor-one-half upper differential inequality from Section A.6 and a repaired leading lower-bound argument for Lemma A.6 in Section A.4. The new rectangle remains above the window and keeps both fields valid, but gives a logarithmic error. Three provisional entries separate that partial quantitative repair, the tail-ratio sign and a distinct-root-mark issue in the separate lower inequality. Earlier statements and source scopes are unchanged.

## Corrected sharp upper-field route

The [sharp upper-field map](sources/sharp-upper-field.md) now gives a full replacement cutting proof with a separate root-mark event and its extra deletion cost. It recovers the leading sharp upper-field and root-tail constants under explicit strong-triangle hypotheses. The root-event erratum is fix found/substantial; the independent lower-field rectangle remains partial/substantial, with a logarithmic combined error. The earlier text records the prior state of the argument.

## Characteristic repair of the lower field bound

The [characteristic-field map](sources/characteristic-field-growth.md) supplies a new finite proof from the zero-field susceptibility. It removes the lower rectangle’s logarithmic loss and gives a polynomial lower-tail error; with the corrected upper route, the two-sided error has exponent min(alpha/2,1/3-alpha). The rectangle erratum is now fix found/substantial, still provisional. Earlier statements and their tags remain unchanged; the earlier descriptions of an unresolved polynomial lower error record the prior state.

## Quantitative tails and large-cluster mass

The [quantitative-tail map](sources/quantitative-supercritical-tails.md) records the retained upper-error balance, a logarithmic marking choice and a large-cluster variance application. The new upper-error entry is partial/statement/provisional; the completed lower characteristic repair remains found/substantial. A largest-component upper bound assumes epsilon^5 N tends to infinity and does not establish a giant-component lower bound. Earlier tagged results remain unchanged.


## A broad supercritical consequence

The [cube sprinkling proof](articles/finite-supercritical-clusters.md#section-hypercube-broad-giant) uses EFAQ and 87Y4 to discharge the reference assumptions of the existing mass estimate. It covers $\log(1/\varepsilon)=o(m^{1/3})$, including polynomially small displacements, and proves the leading giant size, susceptibility and negligible remaining squared mass. It leaves the full near-window regime open in the wiki.
