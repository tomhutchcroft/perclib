# Area map: the lace expansion

This page maps the lace-expansion part of the wiki onto the Lean library: what the area
contains, in which order it can be built, what already exists for it, and what is still
missing. It is written from public material only: the wiki in [`wiki/`](../../wiki/), the
Lean library in [`PercLib/`](../../PercLib/), the decisions in
[`docs/DECISIONS.md`](../../docs/DECISIONS.md), and the published sources the articles cite
(Heydenreich and van der Hofstad, *Progress in High-Dimensional Percolation and Random
Graphs*, Springer 2017; T. Hara, Ann. Probab. 36 (2008) 530–593,
doi:10.1214/009117907000000231; T. Hara, Probab. Theory Related Fields 86 (1990) 337–385,
doi:10.1007/BF01208256; T. Hutchcroft, arXiv:2106.06400v3). Formal statuses and declaration
names are as of 21 November 2026; the library manifest (`scripts/build_manifest.py`) is
the authority when they move.

## 1. Scope and owner

The area is taken by **Codex (Tom's contributor)**: the project's own agents queue no Lean
work whose target is an assertion of the fourteen articles listed below or of their
dependants (section 2). Shared prerequisites outside those articles (the BK inequality,
tree-graph bounds, Fourier and convolution lemmas, the two-point function API and the
lattice model itself) stay with the project and are done first when the area needs them;
to ask for one, open an issue (with the repository's "proposal for a definition" or
"mathematical gap" template where one exists) or say so in the pull request that needs it.

The fourteen articles: `lace-expansion`, `lace-coefficient-diagrams`,
`weighted-lace-coefficients`, `higher-lace-moments`, `planar-lace-moments`,
`planar-pointwise-lace`, `spatial-lace-coefficient-bounds`, `two-mark-first-coefficients`,
`bootstrap-diagram-bounds`, `fourier-bootstrap`, `completed-fourier-bootstrap`,
`tilted-fourier-bootstrap`, `infrared-diagrams`, `triangle-condition`.

## 2. Assertions in dependency order

**How this was computed.** The recorded prerequisites of an assertion are the `proof_uses`
lists in `wiki/records/<article>.json` (field `proofUses`); the formal status is the
manifest's `proof_status` (`proved`, `statement only`, `unformalised`). Each assertion is
listed after all of its in-scope prerequisites (rows are grouped by depth in the
prerequisite graph, which is acyclic). "In scope" means the 76 assertions of the fourteen
articles plus eight assertions of other articles that are both prerequisites and
dependants of the area (`22TW`, `9LN2`, `BT9V`, `JQOQ`, `LEJR`, `OYWM`, `SPSG`, `XZX4`,
marked "dependant"): they cannot be done before parts of the area, so they are listed in
order with it. A prerequisite marked "outside" is an assertion of another article that does
not depend on the area; section 3 lists the Lean that exists for each. **Start now** means
every recorded prerequisite is already proved.

**Counts.** 76 assertions in the fourteen articles: 0 proved, 0 statement only, 76
unformalised. With the eight interleaved dependants: 84, all unformalised. Startable now: 7
(`84XD`, `C5GY`, `GZCA`, `VPUS`, `5EWK`, and the two definitions `67VP`, `7UDJ`). The
other 77 wait on in-scope assertions or on 30 unproved outside prerequisites; the outside
prerequisite blocking the most rows is `JQLC` (7 rows), then `5W46`, `ENZ7`, `MZ23` (4 each).

### Per article

| Article | Tags, with their row in the table below |
|---|---|
| [lace-expansion](../../wiki/articles/lace-expansion.md) | `F69T` (7), `Z84R` (21), `I3PK` (30) |
| [lace-coefficient-diagrams](../../wiki/articles/lace-coefficient-diagrams.md) | `NCYU` (20), `SJIL` (33), `3W22` (39), `NJT0` (40), `AA7H` (46) |
| [weighted-lace-coefficients](../../wiki/articles/weighted-lace-coefficients.md) | `RZML` (44), `09JN` (49), `IT43` (50), `VL4L` (56) |
| [higher-lace-moments](../../wiki/articles/higher-lace-moments.md) | `1VDI` (3), `KFUM` (53), `JJJN` (58), `JO75` (62) |
| [planar-lace-moments](../../wiki/articles/planar-lace-moments.md) | `VPUS` (8), `7TNU` (41), `KOTM` (71), `GIN9` (73), `PCOC` (74), `5T90` (75), `6N01` (76), `SL9H` (77), `B0RG` (79) |
| [planar-pointwise-lace](../../wiki/articles/planar-pointwise-lace.md) | `LS5S` (42), `8F9A` (47), `RCF3` (54), `634L` (59), `KF2I` (78), `CP1T` (80), `QKEC` (81), `FWHO` (82) |
| [spatial-lace-coefficient-bounds](../../wiki/articles/spatial-lace-coefficient-bounds.md) | `4CGW` (9), `P8KQ` (43) |
| [two-mark-first-coefficients](../../wiki/articles/two-mark-first-coefficients.md) | `5EWK` (13), `0TO3` (70) |
| [bootstrap-diagram-bounds](../../wiki/articles/bootstrap-diagram-bounds.md) | `54IO` (51), `L1Y7` (52), `PEVH` (57), `6G0E` (60), `NOTF` (61), `66SP` (63) |
| [fourier-bootstrap](../../wiki/articles/fourier-bootstrap.md) | `84XD` (1), `8LOF` (2), `TTS1` (16), `NL05` (25) |
| [completed-fourier-bootstrap](../../wiki/articles/completed-fourier-bootstrap.md) | `W2WX` (64), `12ZK` (65), `MYG7` (66), `F7N7` (67), `7GNW` (84) |
| [tilted-fourier-bootstrap](../../wiki/articles/tilted-fourier-bootstrap.md) | `X9O8` (34), `IZDP` (55), `VUY5` (68), `1MCZ` (69), `OUHY` (72) |
| [infrared-diagrams](../../wiki/articles/infrared-diagrams.md) | `C5GY` (4), `GZCA` (5), `KCOF` (6), `9ZD3` (17), `IY26` (18), `RD3X` (19), `A9W9` (26), `ANZF` (27), `LKS9` (28), `ZRVJ` (29), `WXT8` (32), `7PM4` (37), `KC8U` (38), `2RVB` (45), `NI0W` (83) |
| [triangle-condition](../../wiki/articles/triangle-condition.md) | `2ZI0` (10), `67VP` (11), `7UDJ` (12), `P9JD` (23) |

### In order

| # | Tag | Article | Kind | Statement (wiki title) | Formal status | Recorded prerequisites | Start now |
|---|---|---|---|---|---|---|---|
| 1 | `84XD` | fourier-bootstrap | theorem | An absolute-value reciprocal estimate for real even summable kernels | unformalised | none | **yes** |
| 2 | `8LOF` | fourier-bootstrap | proposition | Finite susceptibility gives spatial moments and subcritical weighted continuity on the nearest-neighbour lattice | unformalised | `JQLC` (outside, unformalised) |  |
| 3 | `1VDI` | higher-lace-moments | proposition | A spatial two-point bound makes the polynomially marked diagrams finite | unformalised | `IDIL` (outside, unformalised) |  |
| 4 | `C5GY` | infrared-diagrams | proposition | A local symbol of order beta has an inverse transform of order minus d minus beta | unformalised | none | **yes** |
| 5 | `GZCA` | infrared-diagrams | theorem | Two-sided spatial power and logarithmic bounds determine truncated bubbles and triangles | unformalised | none | **yes** |
| 6 | `KCOF` | infrared-diagrams | proposition | The simple random-walk triangle is finite exactly above dimension six | unformalised | `E9BP` (outside, unformalised) |  |
| 7 | `F69T` | lace-expansion | theorem | Cutting-bond partition and conditional factorization | unformalised | `G192` (outside, unformalised) |  |
| 8 | `VPUS` | planar-lace-moments | theorem | A facewise Hölder condition bounds a nonnegative rooted planar diagram | unformalised | none | **yes** |
| 9 | `4CGW` | spatial-lace-coefficient-bounds | proposition | The eight-edge first-coefficient diagram has squared Green decay above dimension six | unformalised | `IDIL` (outside, unformalised) |  |
| 10 | `2ZI0` | triangle-condition | theorem | Mean-field estimates under the triangle condition | unformalised | `NUJY` (outside, unformalised), `JQLC` (outside, unformalised), `8DSI` (outside, proved), `2ML7` (outside, unformalised), `4IHK` (outside, proved), `JRCI` (outside, proved), `5UJQ` (outside, proved), `INZI` (outside, proved), `AUUG` (outside, proved), `L82Q` (outside, proved), `AFH6` (outside, statement only), `UZ7J` (outside, unformalised), `70KD` (outside, unformalised), `JL1S` (outside, unformalised), `36PN` (outside, unformalised), `CSY8` (outside, proved), `MBV2` (outside, proved) |  |
| 11 | `67VP` | triangle-condition | definition | Triangle diagram | unformalised | none | **yes** |
| 12 | `7UDJ` | triangle-condition | definition | Critical triangle condition | unformalised | none | **yes** |
| 13 | `5EWK` | two-mark-first-coefficients | proposition | Two marked routes bound a higher moment of the first lace diagram | unformalised | none | **yes** |
| 14 | `BT9V` | correlation-length-fourier (dependant) | proposition | Subcritical exponential moments give continuity of polynomially weighted spatial suprema | unformalised | `8LOF` |  |
| 15 | `LEJR` | embedded-branching-trees (dependant) | theorem | A uniform massive continuum approximation describes the near-critical nearest-neighbour Green function | unformalised | `C5GY`, `8KZO` (outside, unformalised) |  |
| 16 | `TTS1` | fourier-bootstrap | proposition | Positive random-walk reciprocals satisfy the bootstrap comparison and difference bounds | unformalised | `84XD` |  |
| 17 | `9ZD3` | infrared-diagrams | corollary | Logarithmic spatial corrections separate bubble and triangle finiteness at the marginal dimensions | unformalised | `GZCA` |  |
| 18 | `IY26` | infrared-diagrams | theorem | The nearest-neighbour Green function has an explicit fourth-degree angular correction | unformalised | `C5GY` |  |
| 19 | `RD3X` | infrared-diagrams | theorem | Dimension-uniform weighted random-walk integrals | unformalised | `KCOF` |  |
| 20 | `NCYU` | lace-coefficient-diagrams | proposition | Path witnesses for terminal and intermediate cutting events | unformalised | `F69T`, `G192` (outside, unformalised) |  |
| 21 | `Z84R` | lace-expansion | theorem | The finite lace expansion with a controlled signed remainder | unformalised | `F69T` |  |
| 22 | `9LN2` | tilted-susceptibility (dependant) | proposition | Tilted summability is open in the bond probability and the tilt | unformalised | `8LOF`, `JQLC` (outside, unformalised) |  |
| 23 | `P9JD` | triangle-condition | corollary | Critical nonpercolation and infinite susceptibility | unformalised | `2ZI0`, `CSY8` (outside, proved) |  |
| 24 | `SPSG` | branching-random-walk (dependant) | theorem | A symmetric finite-range walk has a covariance-normalized fourth-moment Green correction | unformalised | `C5GY`, `IY26`, `02EB` (outside, unformalised), `94E7` (outside, unformalised) |  |
| 25 | `NL05` | fourier-bootstrap | theorem | The percolation bootstrap functions are continuous and the forbidden-region argument applies | unformalised | `8LOF`, `TTS1` |  |
| 26 | `A9W9` | infrared-diagrams | proposition | Shifted walk triangles are bounded by the unshifted weighted triangle | unformalised | `RD3X` |  |
| 27 | `ANZF` | infrared-diagrams | proposition | A uniform infrared bound controls critical triangles and open polygons | unformalised | `RD3X`, `F77A` (outside, unformalised), `JQLC` (outside, unformalised) |  |
| 28 | `LKS9` | infrared-diagrams | proposition | Finite return sums give explicit upper and lower bounds for the sixth random-walk norms | unformalised | `RD3X` |  |
| 29 | `ZRVJ` | infrared-diagrams | theorem | Spread-out weighted diagrams are small and the full triangle tends to one | unformalised | `RD3X`, `NUJY` (outside, unformalised) |  |
| 30 | `I3PK` | lace-expansion | theorem | Summable lace coefficients give the full expansion and a conditional critical identity | unformalised | `Z84R` |  |
| 31 | `JQOQ` | tilted-susceptibility (dependant) | theorem | Axial decay and box escape have the same positive mass, and the tilted susceptibility diverges there | unformalised | `9LN2`, `BT9V` |  |
| 32 | `WXT8` | infrared-diagrams | theorem | Finite-range walk diagrams have explicit power singularities and a finite part at the marginal dimension | unformalised | `SPSG` |  |
| 33 | `SJIL` | lace-coefficient-diagrams | theorem | Geometric mass bounds for all nonnegative lace coefficients | unformalised | `NCYU`, `ANZF` |  |
| 34 | `X9O8` | tilted-fourier-bootstrap | proposition | Small tilted coefficient moments improve the Fourier and second-derivative bounds with a universal constant | unformalised | `I3PK` |  |
| 35 | `OYWM` | tilted-susceptibility (dependant) | proposition | The mass is continuous below criticality and the tilted sum is analytic inside its domain | unformalised | `9LN2`, `JQOQ`, `8LOF`, `8ZGG` (outside, unformalised) |  |
| 36 | `XZX4` | tilted-susceptibility (dependant) | proposition | Endpoint coefficient summability identifies the lace pole at the actual mass | unformalised | `JQOQ`, `1BG0` (outside, unformalised) |  |
| 37 | `7PM4` | infrared-diagrams | theorem | The marginal shifted bubble and one-shift triangle share a universal near-critical profile | unformalised | `WXT8` |  |
| 38 | `KC8U` | infrared-diagrams | corollary | The six-dimensional triangle logarithm determines the critical approach of the finite bubble | unformalised | `WXT8`, `LEJR` |  |
| 39 | `3W22` | lace-coefficient-diagrams | theorem | Small critical weighted triangle gives summable lace coefficients and the critical equation | unformalised | `SJIL`, `Z84R`, `I3PK`, `5W46` (outside, unformalised), `JQLC` (outside, unformalised) |  |
| 40 | `NJT0` | lace-coefficient-diagrams | proposition | Weighted bounds for the zeroth and first lace coefficients | unformalised | `SJIL` |  |
| 41 | `7TNU` | planar-lace-moments | proposition | An ordered integration of the lace strip uses at most four factors at each face | unformalised | `VPUS`, `SJIL` |  |
| 42 | `LS5S` | planar-pointwise-lace | proposition | Deleting one edge from each outer route leaves a uniformly bounded two-root diagram | unformalised | `VPUS`, `SJIL` |  |
| 43 | `P8KQ` | spatial-lace-coefficient-bounds | proposition | A spatial bootstrap bound controls the zeroth and first lace coefficients and their moments | unformalised | `4CGW`, `SJIL` |  |
| 44 | `RZML` | weighted-lace-coefficients | proposition | Forward and reversed diagram chains have the same mass bound | unformalised | `SJIL` |  |
| 45 | `2RVB` | infrared-diagrams | theorem | Critical marginal shifted diagrams have the same finite part as killing regularization plus twice the logarithmic coefficient | unformalised | `WXT8`, `7PM4`, `KC8U` |  |
| 46 | `AA7H` | lace-coefficient-diagrams | proposition | An infrared estimate and a bounded edge mass make the weighted triangle small | unformalised | `RD3X`, `ANZF`, `3W22` |  |
| 47 | `8F9A` | planar-pointwise-lace | theorem | A spatial decay exponent doubles in the full lace coefficient series when the connector norm is small | unformalised | `LS5S`, `SJIL` |  |
| 48 | `22TW` | signed-kernel-moments (dependant) | corollary | Summable nonnegative coefficient bounds control the signed lace moment and dispersion | unformalised | `3W22`, `QA8C` (outside, unformalised), `IVH2` (outside, unformalised) |  |
| 49 | `09JN` | weighted-lace-coefficients | theorem | The all-order weighted lace-coefficient estimate | unformalised | `RZML`, `NJT0`, `SJIL` |  |
| 50 | `IT43` | weighted-lace-coefficients | proposition | The refined first weighted lace-coefficient bound | unformalised | `NJT0`, `SJIL` |  |
| 51 | `54IO` | bootstrap-diagram-bounds | proposition | A bounded bootstrap function makes the weighted triangle small | unformalised | `ANZF`, `RD3X`, `IT43` |  |
| 52 | `L1Y7` | bootstrap-diagram-bounds | proposition | All three frequency shifts in the H diagram obey the same small bound | unformalised | `RD3X`, `09JN` |  |
| 53 | `KFUM` | higher-lace-moments | proposition | Polynomial displacement weights give all-order lace moment bounds | unformalised | `SJIL`, `NJT0`, `09JN`, `RZML` |  |
| 54 | `RCF3` | planar-pointwise-lace | proposition | Two outer-edge deletions leave at most three bridges and require only sixth Fourier norms | unformalised | `LS5S`, `VPUS`, `SJIL`, `8F9A` |  |
| 55 | `IZDP` | tilted-fourier-bootstrap | proposition | A symmetric majorant transfers all lace orders to tilted coordinate moments | unformalised | `SJIL`, `RZML`, `IT43`, `09JN` |  |
| 56 | `VL4L` | weighted-lace-coefficients | corollary | Small diagrams and frequency bounds give absolute second moments of the lace sum | unformalised | `09JN`, `IT43`, `NJT0`, `SJIL`, `22TW` |  |
| 57 | `PEVH` | bootstrap-diagram-bounds | proposition | The weighted pair is uniformly bounded and its unshifted value is small | unformalised | `54IO`, `A9W9`, `RD3X` |  |
| 58 | `JJJN` | higher-lace-moments | theorem | A spatial critical bound and a small triangle give higher moments and weighted continuity of the entire lace series | unformalised | `KFUM`, `1VDI`, `SJIL`, `3W22`, `5W46` (outside, unformalised) |  |
| 59 | `634L` | planar-pointwise-lace | theorem | Sixth-norm connector smallness doubles a spatial decay exponent in every lace order | unformalised | `RCF3`, `8F9A` |  |
| 60 | `6G0E` | bootstrap-diagram-bounds | theorem | The bootstrap bound gives a small summable lace kernel and a vanishing remainder | unformalised | `54IO`, `PEVH`, `L1Y7`, `SJIL`, `NJT0`, `IT43`, `09JN`, `22TW`, `Z84R`, `I3PK` |  |
| 61 | `NOTF` | bootstrap-diagram-bounds | proposition | Explicit diagram bounds under a weak bootstrap bound of two | unformalised | `LKS9`, `54IO`, `PEVH`, `L1Y7`, `A9W9`, `RD3X` |  |
| 62 | `JO75` | higher-lace-moments | proposition | Higher absolute moments give a Hölder Hessian and a quantitative critical Fourier pole | unformalised | `JJJN`, `22TW`, `3W22` |  |
| 63 | `66SP` | bootstrap-diagram-bounds | theorem | Explicit summable lace bounds under a weak bootstrap bound of two | unformalised | `NOTF`, `SJIL`, `NJT0`, `IT43`, `09JN`, `22TW`, `Z84R`, `I3PK` |  |
| 64 | `W2WX` | completed-fourier-bootstrap | proposition | Small lace coefficients improve the first two bootstrap quantities | unformalised | `6G0E`, `TTS1` |  |
| 65 | `12ZK` | completed-fourier-bootstrap | proposition | The reciprocal estimate closes the second-difference bootstrap bound | unformalised | `W2WX`, `84XD`, `TTS1` |  |
| 66 | `MYG7` | completed-fourier-bootstrap | theorem | The nearest-neighbour Fourier bootstrap closes in sufficiently large dimension | unformalised | `W2WX`, `12ZK`, `NL05`, `6G0E`, `54IO` |  |
| 67 | `F7N7` | completed-fourier-bootstrap | theorem | The completed bootstrap gives the critical lace equation and an integrable Fourier density | unformalised | `MYG7`, `6G0E`, `3W22`, `TTS1`, `5W46` (outside, unformalised), `JQLC` (outside, unformalised) |  |
| 68 | `VUY5` | tilted-fourier-bootstrap | proposition | A weak tilted Fourier bound gives small all-order coefficient moments | unformalised | `IZDP`, `MYG7`, `RD3X`, `PEVH`, `L1Y7` |  |
| 69 | `1MCZ` | tilted-fourier-bootstrap | theorem | All lace orders have uniform exponentially tilted coordinate moments up to the mass | unformalised | `VUY5`, `X9O8`, `6G0E`, `MYG7`, `OYWM` |  |
| 70 | `0TO3` | two-mark-first-coefficients | theorem | Critical coefficient moments of even order M give moments of order 2M for the first two lace coefficients | unformalised | `5EWK`, `SJIL`, `3W22`, `F7N7`, `BNKQ` (outside, unformalised) |  |
| 71 | `KOTM` | planar-lace-moments | theorem | A small connector Fourier norm doubles the moment of the entire critical lace series | unformalised | `VPUS`, `SJIL`, `0TO3`, `3W22`, `2ZOB` (outside, unformalised), `1165` (outside, unformalised) |  |
| 72 | `OUHY` | tilted-fourier-bootstrap | theorem | The true exponential correlation length has the mean-field scale and a simple tilted pole in sufficiently high dimension | unformalised | `1MCZ`, `JQOQ`, `XZX4`, `F7N7`, `1BG0` (outside, unformalised), `8ZGG` (outside, unformalised), `0Y4K` (outside, unformalised) |  |
| 73 | `GIN9` | planar-lace-moments | theorem | In sufficiently large dimension the full lace series has any prescribed fixed moment and a quadratic relative Fourier remainder | unformalised | `KOTM`, `F7N7`, `RD3X`, `22TW`, `1165` (outside, unformalised) |  |
| 74 | `PCOC` | planar-lace-moments | theorem | The planar two-mark bound doubles any real input moment and gives weighted critical continuity | unformalised | `VPUS`, `SJIL`, `KOTM`, `3W22`, `ENZ7` (outside, unformalised) |  |
| 75 | `5T90` | planar-lace-moments | theorem | Ordered face integration doubles real lace moments and reaches every order below seven ninths of the dimension minus four | unformalised | `7TNU`, `SJIL`, `PCOC`, `ENZ7` (outside, unformalised), `65QV` (outside, unformalised) |  |
| 76 | `6N01` | planar-lace-moments | corollary | The real-order iteration reaches every moment strictly below two thirds of the dimension minus four | unformalised | `PCOC`, `KOTM`, `ENZ7` (outside, unformalised), `65QV` (outside, unformalised) |  |
| 77 | `SL9H` | planar-lace-moments | theorem | Two weighted triangle row bounds control every placement of two outer-route marks | unformalised | `SJIL`, `PCOC` |  |
| 78 | `KF2I` | planar-pointwise-lace | theorem | Nearest-neighbour critical percolation has the Gaussian spatial asymptotic in sufficiently large dimension | unformalised | `8F9A`, `KOTM`, `GIN9`, `F7N7`, `1165` (outside, unformalised), `OT9N` (outside, unformalised), `MZ23` (outside, unformalised) |  |
| 79 | `B0RG` | planar-lace-moments | theorem | The critical Fourier gap and small triangle give every lace moment strictly below dimension minus six | unformalised | `SL9H`, `JJJN`, `ENZ7` (outside, unformalised), `ODMM` (outside, unformalised), `65QV` (outside, unformalised) |  |
| 80 | `CP1T` | planar-pointwise-lace | theorem | Ninth-norm connector smallness closes the critical spatial argument in every integer dimension at least nineteen | unformalised | `5T90`, `RCF3`, `F7N7`, `GIN9`, `OT9N` (outside, unformalised), `MZ23` (outside, unformalised) |  |
| 81 | `QKEC` | planar-pointwise-lace | theorem | The spatial asymptotic follows above dimension thirty once the critical Fourier and connector hypotheses hold | unformalised | `6N01`, `8F9A`, `OT9N` (outside, unformalised), `MZ23` (outside, unformalised) |  |
| 82 | `FWHO` | planar-pointwise-lace | theorem | Sixth-norm smallness and the critical Fourier hypotheses give the Gaussian asymptotic above dimension fourteen | unformalised | `B0RG`, `SL9H`, `634L`, `F7N7`, `GIN9`, `7QGG` (outside, unformalised), `MZ23` (outside, unformalised) |  |
| 83 | `NI0W` | infrared-diagrams | corollary | Exact walk certificates turn explicit infrared amplitudes into sixth-norm connector smallness | unformalised | `LKS9`, `FWHO`, `F7N7` |  |
| 84 | `7GNW` | completed-fourier-bootstrap | theorem | An explicit dimension bound for the nearest-neighbour infrared estimate and spatial asymptotic | unformalised | `66SP`, `NOTF`, `W2WX`, `12ZK`, `NL05`, `3W22`, `TTS1`, `NI0W`, `FWHO`, `5W46` (outside, unformalised), `JQLC` (outside, unformalised) |  |

### Dependants outside the fourteen articles

The project queues no Lean work on these either while the area is taken.

**Direct dependants** (a recorded prerequisite lies in the 14 articles):

| Tag | Article | Statement | Formal status | Area prerequisites |
|---|---|---|---|---|
| `6ZYT` | branching-random-walk | The cited marginal percolation equivalent and its diagram consequences | unformalised | `2ZI0` |
| `IDP2` | branching-random-walk | The cited spatial estimates imply exact convolution thresholds and mean-field bounds | unformalised | `2ZI0` |
| `SPSG` | branching-random-walk | A symmetric finite-range walk has a covariance-normalized fourth-moment Green correction | unformalised | `C5GY`, `IY26` (also a prerequisite of the area; in the table above) |
| `93RC` | correlation-length-fourier | The second-moment correlation length has the mean-field scale near criticality | unformalised | `MYG7`, `F7N7` |
| `BT9V` | correlation-length-fourier | Subcritical exponential moments give continuity of polynomially weighted spatial suprema | unformalised | `8LOF` (also a prerequisite of the area; in the table above) |
| `CM3M` | correlation-length-fourier | The lace quotient gives an exact identity for the squared second-moment length | unformalised | `8LOF` |
| `ET10` | correlation-length-fourier | Absolute lace moments determine the critical Fourier amplitude and its remainder | unformalised | `F7N7` |
| `LEJR` | embedded-branching-trees | A uniform massive continuum approximation describes the near-critical nearest-neighbour Green function | unformalised | `C5GY` (also a prerequisite of the area; in the table above) |
| `FUZK` | finite-graph-criticality | A quotient coupling gives a one-sided finite-volume critical-parameter comparison | unformalised | `F7N7` |
| `CMEX` | fourier-spatial-moment-bridge | The completed critical Fourier bootstrap gives quadratic spatial decay and weighted bubble and triangle bounds | unformalised | `F7N7` |
| `74SS` | green-free-triangle | Critical square-root tails and linearly scaled supercritical density in high dimensions | unformalised | `F7N7` |
| `C2V4` | green-free-triangle | The completed bootstrap makes the triangle differential coefficient positive | unformalised | `F7N7` |
| `E5ZR` | green-free-triangle | Explicit mean-field constants throughout the quantified dimension range | unformalised | `7GNW` |
| `OB0K` | green-free-triangle | A triangle differential inequality with an explicit smallness qualification | unformalised | `F69T` |
| `YT0O` | green-free-triangle | An explicit small-triangle and susceptibility bound in the quantified bootstrap range | unformalised | `7GNW`, `NOTF` |
| `Z78U` | incipient-cluster-limits | A finite triangle gives exponential upper tails for intrinsic IIC volume on the radius-squared scale | unformalised | `FWHO` |
| `36ZQ` | mean-field-cluster-moments | The high-dimensional lattice has a dimension-uniform cubic moment and gap scale | unformalised | `F7N7` |
| `NB44` | nonbacktracking-walk | Critical non-backtracking transforms have an Abel limit at the bipartite frequency | unformalised | `KCOF`, `TTS1` |
| `22TW` | signed-kernel-moments | Summable nonnegative coefficient bounds control the signed lace moment and dispersion | unformalised | `3W22` (also a prerequisite of the area; in the table above) |
| `9LN2` | tilted-susceptibility | Tilted summability is open in the bond probability and the tilt | unformalised | `8LOF` (also a prerequisite of the area; in the table above) |
| `OYWM` | tilted-susceptibility | The mass is continuous below criticality and the tilted sum is analytic inside its domain | unformalised | `8LOF` (also a prerequisite of the area; in the table above) |

**Indirect dependants** (90 assertions whose recorded prerequisites reach the area only through other dependants; all unformalised; `JQOQ` and `XZX4` are also prerequisites of the area and appear in the table above):

| Article | Tags |
|---|---|
| branching-random-walk | `5DQV`, `W810` |
| characteristic-field-growth | `AQPE`, `YHLB` |
| critical-arm-bounds | `W73R` |
| finite-subcritical-clusters | `DAN9`, `L5E1` |
| finite-supercritical-clusters | `12DQ`, `4OVE`, `E6FX`, `G987`, `UQ45` |
| finite-triangle-window | `0Y6N`, `1DEZ`, `1T2M`, `1ZWD`, `4W2Z`, `6248`, `65IO`, `7CDV`, `7E7T`, `83JM`, `A40L`, `B7V7`, `BH5K`, `CBIL`, `DK7F`, `E4JW`, `EAQD`, `EPK3`, `GDPT`, `GJB6`, `J2VQ`, `JTVN`, `KCRC`, `KP1O`, `KQN9`, `L1PJ`, `L3KC`, `LX6L`, `M7RY`, `ME2X`, `NM14`, `NROY`, `O4TX`, `OWBW`, `QKHG`, `U59P`, `VM8H`, `WPKA`, `WVGG`, `WYUD`, `X92C`, `XT0C`, `ZFGF` |
| finite-window-susceptibility | `CAZQ`, `KSAO`, `RT85` |
| green-free-triangle | `9TAI`, `ZK0V` |
| iic-random-walk | `2XZU`, `BP8X`, `FPDW`, `G85Z`, `HJKG`, `IXCJ`, `KMWL`, `OBBT`, `PDSN`, `PSNV`, `YWT9`, `ZZC8` |
| incipient-cluster-limits | `3FTE`, `POD2`, `RG3Z` |
| mean-field-cluster-moments | `76EV`, `7T8L`, `EKKI` |
| quantitative-supercritical-tails | `7Y5K`, `IZ3I`, `NIYL`, `YE0X` |
| quotient-cluster-bounds | `SUMF` |
| sharp-supercritical-field | `7DLQ`, `CI72` |
| sharp-upper-field | `6SGU`, `HGND`, `Q6CS` |
| tilted-susceptibility | `JQOQ`, `XZX4` |

## 3. Existing Lean for the prerequisites outside the area

Tagged declarations were found with `git grep -n 'tag "XXXX"' -- PercLib`; untagged
infrastructure by searching `PercLib/` for disjoint occurrence and BK, tree-graph, Fourier,
convolution, triangle sums, `tau`, `chi` and `rowSum`. "Related, untagged" means Lean that
proves all or part of the statement without carrying its tag; whether it matches the wiki
statement exactly has not been audited.

### Proved or stated

| Tag | Article | Statement | Status | Lean (declaration, file) |
|---|---|---|---|---|
| `JRCI` | bk-inequality | Countable BK for increasing events with finite disjoint witnesses | proved | `PercLib.Probability.countable_bk_measurable_and_bound` (`PercLib/Probability/Tags/DisjointOccurrence.lean`); area lemma `countable_profile_bk` (`PercLib/Probability/CountableBK.lean`) |
| `AUUG` | bk-inequality | Product bound for finitely many disjoint increasing events | proved | `PercLib.Probability.countable_profile_bk_foldl` (`PercLib/Probability/CountableBK.lean`) |
| `L82Q` | tree-graph | Three-point tree-graph inequality | proved | `PercLib.Percolation.Bond.TreeGraphInequality` (`PercLib/Percolation/Bond/TreeGraph/Defs.lean`), `PercLib.Percolation.Bond.treeGraphInequality` (`PercLib/Percolation/Bond/TreeGraph/BranchPoint.lean`) |
| `AFH6` | multipoint-trees | Multipoint tree-graph inequality on a countable bond model | statement only | `PercLib.Percolation.Bond.MultipointTreeGraphInequality` (`PercLib/Percolation/Bond/Multipoint/Defs.lean`); its proof is open (prerequisites `SO5J`, `BNY8`, `HP3X`) |
| `4IHK` | russo-formula | Homogeneous Russo formula including endpoint derivatives | proved | `PercLib.Probability.FiniteProfile.russo_homogeneous_polynomial_and_endpoints` (`PercLib/Probability/Tags/Russo.lean`) |
| `5UJQ` | connectivity | Connectivity under finite exhaustion | proved | `PercLib.Percolation.Bond.conn_eq_iUnion_localConn_and_tendsto` (`PercLib/Percolation/Bond/Tags/CoreConnectivity.lean`) |
| `8DSI` | susceptibility | Susceptibility and the two-point sum identity | proved | `PercLib.Percolation.Bond.chi_eq_lintegral_eq_tsum_tau` (`PercLib/Percolation/Bond/Tags/CoreConnectivity.lean`) |
| `INZI` | susceptibility | Finite expectation implies almost-sure finiteness | proved | `PercLib.Percolation.Bond.ae_cluster_finite_of_chi_lt_top` (`PercLib/Percolation/Bond/IndependentLayer.lean`) |
| `CSY8` | susceptibility | Tail-sum identity | proved | `PercLib.Probability.lintegral_toENNReal_eq_tsum` (`PercLib/Probability/LayerCake.lean`) |
| `MBV2` | integrated-lower-tails | Pointwise square-root lower tail from integrated lower and pointwise upper bounds | proved | `PercLib.Probability.le_of_sum_ge_sqrt` (`PercLib/Probability/TailComparison.lean`) |

### Unformalised (no tagged Lean yet)

| Tag | Article | Statement | Related, untagged Lean |
|---|---|---|---|
| `70KD` | connection-kernels | Positive semidefiniteness of the connection kernel | `sum_mul_connProb_eq_integral`, `sum_mul_connProb_nonneg`, `posSemidef_connProb` (`PercLib/Percolation/Bond/ConnectionKernel.lean`); likely needs only a `Tags/` restatement |
| `UZ7J` | connection-kernels | Cubic connection bounds from finite diagonal triangles | `triangle_sq_le`, `triangle_le_rpow`, `triangle_le_sqrt`, `tsum_connProb_sq_le_triangle` (same file); likely needs only a `Tags/` restatement |
| `F77A` | connection-kernels | Fourier identities and triangle comparison on Euclidean and hierarchical groups | trace identity `tsum_mul_eq_tsum_mul_of_invariant` (`PercLib/Probability/InvariantTrace.lean`); no Fourier transform in the library |
| `2ML7` | product-model | Monotone product coupling | `exists_bond_monotone_coupling`, `exists_prodBernoulli_monotone_coupling`, `prodBernoulli_mono_event`, `lintegral_prodBernoulli_mono` (`PercLib/Probability/Coupling/Monotone.lean`) |
| `8ZGG` | triangle-susceptibility | The reciprocal susceptibility is globally Lipschitz in the bond probability | finite-volume derivative bound `hasDerivAt_finiteChi_le` and the pivotal split `exists_disjointOccurrence_of_pivotal_conn` (`PercLib/Percolation/Bond/SusceptibilityDerivative.lean`), stated in the intensity parameter β, not in p |
| `JQLC` | sharpness-bond-parameter | Bond-parameter density bound and the corrected critical boundary sum | intensity-parameter sharpness for transitive summable kernels: `chi_lt_top_of_lt_rootCriticalIntensity`, `rootCriticalIntensity_eq_sSup_chi_lt_top` (`PercLib/Percolation/Bond/Sharpness.lean`); `law_cluster_infinite_ge_of_escape_deriv` (`PercLib/Percolation/Bond/SupercriticalDensity.lean`); `tendsto_boundaryFlux_exhaustion` (`PercLib/Percolation/Bond/SusceptibilityContinuity.lean`). No bond-parameter `p_c` on `ℤ^d` (section 5) |
| `G192` | sharpness-bond-parameter | Aizenman–Barsky inequalities by positive-field finite-torus approximation | none beyond the `JQLC` files; prerequisites `ZDVK`, `7HP2`, `J2TE`, `R3I9` |
| `NUJY` | integrated-susceptibility | Peierls bound and nontriviality of the lattice transition | none (no planar duality in the library) |
| `JL1S` | stopped-exploration | Cluster-tail comparison from stopped exploration and entropy | transcripts `prodBernoulli_transcript`, `prodBernoulli_adaptive_answers` (`PercLib/Probability/Exploration/Transcript.lean`) |
| `36PN` | integrated-lower-tails | Universal integrated critical tail and saturated square-root field lower bound | none beyond `MBV2` |
| `5W46`, `0Y4K` | triangle-susceptibility | Triangle nonpercolation and one-sided exponent bounds; matching susceptibility bounds from a small open triangle | none |
| `E9BP`, `02EB`, `94E7` | branching-random-walk | Green, bubble and triangle thresholds for lazy walk; covariance Green asymptotic; occupation first moments | return probabilities `convPow`, `tsum_sq_convPow` (`PercLib/Analysis/DiscreteConvolution.lean`); lazy power-law symbol `hasSum_lazy_inverse_square` and the series `∑ p(x) cos(k·x)` (`PercLib/Models/LongRange/FourierSymbol.lean`) |
| `IDIL`, `MZ23` | spatial-convolution-asymptotics | Power-law convolution bounds; convolution remainder | `tsum_lattice_powerKernel_mul_le` (`PercLib/Models/LongRange/Convolution.lean`) covers the case of equal exponents `d + α` only |
| `2ZOB`, `1165`, `BNKQ` | fourier-spatial-moment-bridge | Derivatives of the regularized lace quotient; spatial decay from coefficient moments; weighted critical convolutions | none |
| `65QV`, `ENZ7`, `ODMM` | fractional-fourier-weights | Lp Fourier densities; endpoint weighted density; weighted convolution identities | none |
| `OT9N`, `7QGG` | signed-kernel-gaussian-asymptotics | Green asymptotic of a signed effective kernel; improved remainder | none |
| `QA8C`, `IVH2` | signed-kernel-moments | Convolution moment identity; quadratic Fourier expansion | none |
| `1BG0` | correlation-length-fourier | A tilted lace pole compares inverse susceptibility with the squared mass | Fekete bound for the correlation length (`PercLib/Percolation/Bond/CorrelationLength.lean`, no definition of the mass) |
| `8KZO` | embedded-branching-trees | Occupation and second-moment length for an embedded branching tree | none |

### Infrastructure without a tag

- **Disjoint occurrence and BK.** `PercLib.Probability.ForcesOn`, `disjointOccurrence` (tag
  `OQN6`) with its algebra (`PercLib/Probability/DisjointOccurrence.lean`,
  `DisjointOccurrenceAlgebra.lean`: commutativity, associativity, monotonicity, three-event
  membership), `countable_profile_bk`, `countable_profile_bk_real`, `countable_bk`
  (`CountableBK.lean`), finite profiles (`ProfileBK.lean`), endpoints (`BKEndpoints.lean`),
  and the cylinder form (`CylinderDisjointOccurrence.lean`).
- **Tree-graph moments.** `lintegral_encard_pow_le`, `lintegral_encard_pow_le_branch`
  (`PercLib/Percolation/Bond/TreeGraph/Moments.lean`); `law_forall_conn_le`
  (`TreeGraph/BranchPoint.lean`); tree shapes and weights for k points
  (`Multipoint/Defs.lean`: `TreeShape`, `treeWeight`).
- **Triangle sums.** Written inline as `∑' u, ∑' v, tau q x u * tau q u v * tau q v y`:
  `ConnectionKernel.lean` (above, plus `triangle_weighted_le`, `triangle_weighted_lt_top`)
  and `PercLib/Percolation/Bond/TriangleDecay.lean` (`tendsto_triangle_cofinite`,
  `exists_finset_triangle_lt`, `tendsto_iSup_triangle`).
- **Convolution.** `PercLib/Analysis/DiscreteConvolution.lean`: `ℝ≥0∞`-valued convolution
  on a group written inline (`conv_assoc`, `tsum_conv`, `young_conv`,
  `conv_le_sqrt_mul_sqrt`, `convPow_*`); `PercLib/Percolation/Bond/ConvolutionBound.lean`
  (`tau_le_of_convolution`, walk sums). No signed (`ℝ`- or `ℂ`-valued) `ℓ¹` convolution.
- **Fourier.** No Fourier transform on `ℤ^d` in the library; the long-range symbol is the
  explicit cosine series of `FourierSymbol.lean`. Mathlib (pinned revision) has the torus
  `UnitAddTorus d`, characters `mFourier`, coefficients `mFourierCoeff`, the Hilbert basis
  `mFourierBasis` and `hasSum_mFourier_series_of_summable`
  (`Mathlib/Analysis/Fourier/AddCircleMulti.lean`), and `MeasureTheory.convolution`
  (`Mathlib/Analysis/Convolution.lean`), which applies on `ℤ^d` with `Measure.count`.
- **Two-point function and row sums.** `tau`, `chi` (`PercLib/Percolation/Bond/Basic.lean`),
  `spatialMoment` (`SpatialMoments/Defs.lean`), translation-invariant row sums and
  `chi_le_of_translationInvariant` (`PercLib/Models/TranslationInvariant.lean`),
  `chi_le_inv_one_sub_of_rowSum`, `chi_lt_top_of_rowSum` (`PercLib/Percolation/Bond/RowSum.lean`).
- **The lattice.** `PercLib.Models.Site.zdGraph d` on `Fin d → ℤ` with adjacency, degree
  `2d`, distance and automorphisms (`PercLib/Models/Lattice.lean`); homogeneous
  nearest-neighbour bond percolation appears only as the intensity profile of
  `(zdGraph d).edgeSet.indicator 1` (for example in
  `PercLib/Percolation/Bond/LocalConvergence.lean`).
- **Pivotality.** Spelled out as `insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y`
  (`PercLib/Percolation/Bond/Pivotal.lean`); `PercLib.Probability.pivotal` for `E → Bool`
  configurations (`PercLib/Probability/Russo.lean`).

## 4. The interface to build on

- **Bond interface** (decision D-2), `PercLib/Percolation/Bond/Basic.lean`, namespace
  `PercLib.Percolation.Bond`: `Config V := Set (Sym2 V)`; `law q := prodBernoulli q` for a
  profile `q : Sym2 V → unitInterval` (arbitrary on the diagonal; loops are discarded);
  `openGraph ω := SimpleGraph.fromEdgeSet ω`; `conn x y`, `cluster ω x`;
  `tau q x y := law q (conn x y)` and `chi q x`, both `ℝ≥0∞`-valued (signed lace quantities
  need `.toReal`); `localConn S x y` (connection by an open path inside `S`; connection
  "off S" is `localConn Sᶜ`), `localCluster`; `IsCut ω k` (no open edge crosses `k` in an
  ordered vertex type); `boundaryFlux q S o`. Everything in the area lands on this
  interface.
- **Row sums.** `rowSum (a : Sym2 V → ℝ≥0∞) (v : V) := ∑' w, if w = v then 0 else a s(v, w)`
  with `unitInterval.toENNReal` and `rowSum_toENNReal` for a profile (same file). Use it for
  every summable-row hypothesis.
- **Disjoint occurrence and BK.** Events are `Set (Set ι)`, here with `ι = Sym2 V`.
  `disjointOccurrence A B` is the set of `ω` with two disjoint *finite* sets of coordinates,
  each of which forces its event whatever the other coordinates are (`ForcesOn`). BK is
  `countable_profile_bk p hA hB : prodBernoulli p (disjointOccurrence A B) ≤ prodBernoulli p A
  * prodBernoulli p B` for increasing (`IsUpperSet`) events on a countable index type, any
  profile, outer measures allowed; several events are combined left to right with
  `List.foldl disjointOccurrence` (`countable_profile_bk_foldl`). Path splittings into
  disjoint witnesses follow `exists_disjointOccurrence_of_pivotal_conn`.
- **The measure-general connection kernel** (landing): `connProb μ x y`, the probability
  under an arbitrary measure `μ` on `Config V` that `x` and `y` are connected, with
  `tau q x y = connProb (law q) x y`. The wiki's usage in the area calls for: symmetry and the
  value `1` on the diagonal; a bound by `1` for probability measures; translation
  invariance on `ℤ^d`, giving the one-variable form `τ(x)`; monotonicity in the bond
  parameter; the sum identity with `chi`; and the restricted kernels `τ^S` and `τ^{Λ_n}`
  (connection off `S`, or inside `Λ_n`). Only the name `connProb` is fixed; use
  `tau` until the kernel lands, and expect a mechanical migration.
- **Long-range norm** (planned): a structure `ModelNorm` is to replace the current
  `N : Seminorm ℝ (Fin d → ℝ)` plus separation hypothesis of
  `PercLib/Models/LongRange/Defs.lean` (decision D-35, "Open"). The fourteen articles are
  nearest-neighbour or spread-out (box) models, so this matters only for long-range variants.
- **Renames.** Changes to shared definitions are announced, with a migration recipe, in
  `docs/INTERFACE_CHANGES.md` (decision D-37 h; the file is created with the first
  announcement), and renamed declarations keep a deprecated alias for one release.

## 5. Definitions the area will need

Searched: `PercLib/` for every `def`, `abbrev` and `structure` (by name and by the notions
below), and mathlib at the pinned revision for Fourier series on the torus, convolution and
`ℓ¹`. None of the following exists. Each is a proposed interface pull request (a
`Defs.lean` or `Basic.lean` file, with its API in the same pull request). Items 1–4 are
shared infrastructure: the project does them first on request (section 1). Items 5–12 are
inside the area.

1. **Homogeneous nearest-neighbour bond percolation on `ℤ^d` and its critical point.**
   A profile `p` on the edges of `zdGraph d` and `0` elsewhere, and
   `p_c(d) = inf {p : θ(p) > 0}` with `θ(p)` the probability that the cluster of `0` is
   infinite (the `criticality` article's threshold, transported from `β` to `p`; sharpness
   `JQLC` then identifies it with `sup {p : χ(p) < ∞}`). Used by every article of the area
   (each `context` block). API: evaluation on
   edges and non-edges, monotonicity in `p`, the identity with the intensity profile of the
   edge indicator at `β = -log(1-p)` (so that `rootCriticalIntensity` transfers), invariance
   under the automorphisms of `Lattice.lean`, `tau` translation invariant and symmetric,
   `0 < p_c < 1` for `d ≥ 2` once `NUJY` is proved.
2. **Fourier transform of a summable function on `ℤ^d`.** `f̂(k) = ∑ₓ f(x) e^{i k·x}` on the
   torus, built on mathlib's `UnitAddTorus (Fin d)` and `mFourier` (frequencies `Fin d → ℤ`,
   torus `ℝ/ℤ`, so `k = 2πθ`; fix and document the convention), with the normalized Haar
   measure the articles use. Used in `lace-expansion` (`I3PK`), all bootstrap articles,
   `infrared-diagrams`, `planar-*`. API: linearity, `|f̂| ≤ ‖f‖₁`, continuity, real and even
   for even real `f`, the transform of a convolution is the product, inversion
   (`mFourierCoeff` of `f̂` is `f`), Parseval, and the value at `0` is `∑ f`.
3. **Signed convolution on `ℤ^d`** (or a countable abelian group): either a thin wrapper of
   `MeasureTheory.convolution` with `Measure.count` or a direct `∑'` definition, with the
   point mass `δ₀`. Used throughout (`f * g`, `J * τ`, `Π * J * τ`). API: commutativity,
   associativity and Young's inequality for `ℓ¹`, the unit `δ₀`, agreement with the
   `ℝ≥0∞` convolution of `DiscreteConvolution.lean` on nonnegative functions.
4. **Triangle diagram** (tag `67VP`, a definition of the area) and **critical triangle
   condition** (tag `7UDJ`): `∇(q, x) = ∑' u v, tau q x u * tau q u v * tau q v x`. This sum
   is already spelled out inline in `ConnectionKernel.lean` and `TriangleDecay.lean`, so the
   definition is due under the third-use rule. API: unfolding, `tsum_tau_sq_le_triangle`
   and the `UZ7J` bounds in its terms, `∇ ≤ χ²`, monotonicity in the profile, translation
   invariance on `ℤ^d`. `7UDJ` needs item 1 (`∇` at `p_c`). The bubble `∑ τ(x)²` and the
   other diagrams of `infrared-diagrams` follow the same pattern and may share the file.
5. **Restricted connection and the cutting event** (`lace-expansion`, `F69T`):
   `s ↔^A x` (connected, with no open path between them lying wholly outside `A`), the
   event `E_A(s,x)` (no oriented pivotal bond `(u,v)` with `s ↔^A u`), double connection
   `0 ⇔ x` (`E_{ℤ^d}`), and the deleted-bond cluster `S_e(s)` (which is
   `cluster (ω \ {e}) s` and may need no definition). API: membership, `E_A ⊆ {s ↔ x}`,
   measurability, `E_{univ}` is double connection, the empty-set case.
6. **Oriented pivotal bonds for connection** (`F69T`, `Z84R`): a named predicate for the
   spelling in `Pivotal.lean`, with orientation from the component of `s` to that of `x`.
   It is the third spelling of the same predicate (after `Pivotal.lean` and
   `SusceptibilityDerivative.lean`), so it should be named, in the bond `Basic.lean`.
7. **Lace coefficients** (`Z84R`, `I3PK`): the operator `𝒯` on families `g_A(s,x)` indexed
   by finite sets `A` and `A = ℤ^d`, `a_n = (𝒯ⁿF)_{ℤ^d}(0,·)`, `Π^{(0)} = a₀ − δ₀`,
   `Π^{(n)} = a_n`, `Π_M`, `Π` and the remainder `R_M`. Each application of `𝒯` uses a
   fresh configuration with the set passed from the previous step held fixed; define it
   by recursion in `n` as a nonnegative `ℝ≥0∞` quantity, with the signed sums over `ℝ`.
   API: nonnegativity, `n = 0, 1` unfolded, the bound `‖𝒯g‖ ≤ jχ‖g‖`.
8. **Random-walk kernels** (`infrared-diagrams`, bootstrap articles): the step
   distribution `D(x) = (2d)⁻¹ 1{|x|₁ = 1}`, its spread-out version `D_L` on a box, the
   Green function `C_λ = ∑ λⁿ Dⁿ` and its transform `1/(1 − λD̂)`. Overlaps the
   branching-random-walk article (`E9BP`); agree on one definition with whoever does that one.
9. **Bootstrap functions** (`fourier-bootstrap`, `NL05`): with `λ_p = 1 − 1/χ(p)`,
   `f₁ = 2dp`, `f₂ = sup_l τ̂_p(l)/C_{λ_p}(l)`, `f₃` the supremum over `k ≠ 0` of the second
   difference of `τ̂_p` divided by `U_{λ_p}(k,l)`, and `f = max{f₁, f₂, f₃}`. Needs items 2
   and 8. API: unfolding, `f(0) = 1`; continuity on `[0, p_c)` is the theorem `NL05`.
10. **Weighted diagrams of the coefficient bounds** (`lace-coefficient-diagrams`,
    `weighted-lace-coefficients`, `bootstrap-diagram-bounds`): the kernels `A`, `B₁`, `B₂`,
    the quantities `Δ`, `T`, `W` and the weighted triangle. Several assertions reuse them,
    so a structure or set of definitions in the area's `Defs.lean` avoids spelling them out
    in each statement.
11. **Fourier `Lᵖ` norms on the torus** (`planar-pointwise-lace`: sixth and ninth norms)
    and the weight `⟨x⟩ = max{1, |x|}` with the Euclidean norm (`spatial-lace-coefficient-bounds`,
    `planar-pointwise-lace`). Use mathlib's `eLpNorm` on `UnitAddTorus`; `⟨x⟩` is a
    one-line definition with monotonicity and `1 ≤ ⟨x⟩`.
12. **Axial mass and tilted sums** (`tilted-fourier-bootstrap`): `m(p)` as the limit of
    `−log τ(0, n e₁)/n` (the limit exists by the Fekete argument of `CorrelationLength.lean`,
    which defines nothing) and the tilted susceptibility `∑ τ(x) e^{t x₁}`. Overlaps the
    tilted-susceptibility article (`JQOQ`, `9LN2`, `OYWM`, `XZX4`), which is in scope.

## 6. Known errata touching the area

All entries are in [`wiki/errata/`](../../wiki/errata/); none is confirmed. Each correction
is part of the wiki statement as it now stands, so the Lean must follow the corrected
statement (a binder that implements a correction is classed RULED with the erratum id).

| Erratum (file, id) | Status | Assertions in the area | What it changes |
|---|---|---|---|
| `heydenreich-hofstad.json`, `reciprocal-fourier-sign` | provisional | `84XD`, `TTS1` | the reciprocal Fourier estimate needs absolute values (or positive reciprocals); marked "provisional erratum" in `fourier-bootstrap` |
| `heydenreich-hofstad.json`, `walk-integral-zero-coefficient` | provisional | `RD3X` | the walk Fourier integral is the convolution at `0`, not a total mass |
| `heydenreich-hofstad.json`, `spreadout-triangle-baseline` | provisional | `ZRVJ` | the full spread-out triangle tends to `1`; only its nontrivial part is small |
| `heydenreich-hofstad.json`, `h-diagram-prefactor` | provisional | `L1Y7` | the Fourier form of the H diagram keeps the factor `j²` |
| `heydenreich-hofstad.json`, `bootstrap-algebra-identities` | provisional | `W2WX`, `12ZK` | two algebraic identities in the bootstrap improvement are repaired |
| `heydenreich-hofstad.json`, `mass-susceptibility-reciprocal` | provisional | `1MCZ`, `OUHY` (and in-scope `JQOQ`, `XZX4`, `1BG0`) | the squared mass is compared with `1/χ`, not with `χ` |

Errata on outside prerequisites and dependants (all provisional): `MZ23`
(`convolution-remainder-scope`), `OT9N` (`hara-nearest-neighbour-2008.json`,
`gaussian-truncation-prefactor`), `JQLC` (`probability-derivative-endpoints`,
`box-boundary-multiplicity`), `36PN` (`dct-sharpness.json`, `critical-field-saturation`),
`JL1S` (`hutchcroft-triangle-2021.json`, `entropy-intensity-square`), `L82Q`
(`finite-tree-arm-origin`), `AUUG` (`hutchcroft-hierarchical-volumes-2022.json`,
`critical-suppression-time-index`); dependants `OB0K`, `C2V4` (`triangle-coefficient-scope`),
`74SS` (`critical-tail-constant`, `density-dimension-scale`), `CM3M`, `93RC`
(`second-moment-square`, `correlation-length-nearcritical-scope`), `NB44`
(`nonbacktracking-critical-summation`). Unnamed files are `heydenreich-hofstad.json`.

## 7. Rules that bind the work

1. State each tagged result exactly as the wiki assertion says, including the article's `context` block (model, parameter range, standing hypotheses); never weaken, narrow or re-scope it. If it looks false, vacuous or under-hypothesised, stop and report it with a counterexample.
2. No `sorry`, `admit`, `axiom`, `native_decide`, code run at elaboration time, `set_option maxHeartbeats` or `set_option linter.*`; allowed axioms are `propext`, `Classical.choice`, `Quot.sound`. A literature result used without proof is an explicit `…Input` hypothesis listed in `docs/CITED_INPUTS.md`, and the result is "proved modulo" it.
3. Everything is on the bond interface (section 4). Search `PercLib/` and mathlib before writing any definition or general lemma, and import what exists; a second definition of an existing notion is rejected.
4. Definitions live only in `Basic.lean` or `Defs.lean` and land with their API (evaluation, membership, `@[simp]`, `ext`, monotonicity, trivial case). The third spelling of a notion gets a name.
5. Interface pull requests (definitions, structures, instances, tagged statements) and proof-only pull requests (theorems and lemmas) are never mixed. Proof-only pull requests are checked by the build and the axiom audit; interface ones by a reviewer.
6. Tagged statements are audited by the D-35 binder table: each binder is SOURCE, TYPING or RULED (an erratum id); any EXCESS fails, and existential order is checked against what each constant may depend on.
7. `Tags/` files only restate library lemmas; each conjunct of a tagged conjunction is a named lemma in the area file, and downstream code uses that lemma.
8. Area files are append-only: add declarations, do not rewrite or rename existing ones; changes to shared definitions go through `docs/INTERFACE_CHANGES.md`.
9. Names follow mathlib (conclusion first, `_of_` for hypotheses, most specific namespace); never a tag or task id in a name. More than ten hypotheses on a theorem: say why, or bundle them in a structure.
10. New files: module docstring `/-! # Title … ## Main results -/` after the imports; headers carry source, revision, licence and mathematical reference only. Build with `lake build --wfail`.

## 8. Running the checks locally

As `CONTRIBUTING.md` and `AGENTS.md` state them: use the pinned `lean-toolchain` and
mathlib; run `lake exe cache get` before the first build (never rebuild mathlib); build with
`lake build --wfail` (a single module while working: `lake build --wfail PercLib.Area.File`);
run the repository's axiom audit. The full local gate is `scripts/gate.sh [BASE]` from the
repository root (see the comment at the top of the script), which runs in order and stops
at the first failure:

```sh
lake build --wfail                                     # whole library, warnings are errors
lake env lean --run scripts/AxiomAudit.lean            # every constant under PercLib: only the three axioms
python3 scripts/check_import_closure.py PercLib        # every module imported from PercLib.lean
python3 scripts/check_forbidden.py PercLib             # forbidden constructs and set_options
python3 scripts/test_proof_pr.py                       # unit tests of the proof-only classifier
lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json
python3 scripts/check_d35.py .lake/manifest-raw.json   # tagged Prop definitions, headers, docstrings
# with BASE and a saved extraction for it: proof-only / interface classification
```

The gate needs `~/.elan/bin` on `PATH` (the script adds it). `scripts/kernel_replay.sh`
replays every module through the independent checker; it needs several GB of memory and
must not run alongside a build.
