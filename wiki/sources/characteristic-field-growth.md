# Characteristic field growth

The [article](articles/characteristic-field-growth.md) integrates the sharpened magnetization inequality along a characteristic starting at zero field. It replaces the lower-field rectangle and removes the logarithmic loss. Four assertions give the general finite comparison, sharp field threshold, polynomial lower tail and matching polynomial tail bounds.

| Source and locator | Reading and result |
|---|---|
| [JEMS publisher PDF](https://ems.press/content/serial-article-files/32188), Proposition A.2, (A.3), printed p.799 / PDF index74; Section A.1, (A.7), printed p.800 / PDF index75 | Target and differential inequality rechecked in extracted text. The new characteristic proof starts from the finite susceptibility and requires no triangle bound for its general field comparison. |
| Same source, Section A.4, Lemma A.6 and (A.39)–(A.50), printed pp.804–805 / PDF indices79–80 | The replacement follows a smooth stopped characteristic instead of the invalid rectangle. Its field lower bound has error O(epsilon+abs(mp_c-1)+1/H); the target field range is verified explicitly. |
| Same source, Section A.4, (A.51)–(A.54), printed p.805 / PDF index80 | Marking at the characteristic threshold gives lower-tail exponent 1/3-alpha. Combining with the corrected upper field estimate gives exponent min(alpha/2,1/3-alpha), with parameter-normalization errors retained. |

The [rectangle erratum](errata/hofstad-nachmias-hypercube.json#supercritical-field-rectangle) changes from partial to **fix found / substantial**. The two other appendix entries retain their repair categories; their descriptions now reflect the polynomial repair. All remain provisional. Earlier maps and tagged logarithmic-error statements are preserved. The new proof does not establish a giant component or the source's infinite-graph remark, nor every stronger upper-error rate. No visual PDF comparison, new Lean evidence or independent audit is claimed.

## Quantitative tails and large-cluster mass

The [quantitative-tail map](sources/quantitative-supercritical-tails.md) records the retained upper-error balance, a logarithmic marking choice and a large-cluster variance application. The new upper-error entry is partial/statement/provisional; the completed lower characteristic repair remains found/substantial. A largest-component upper bound assumes epsilon^5 N tends to infinity and does not establish a giant-component lower bound. Earlier tagged results remain unchanged.
