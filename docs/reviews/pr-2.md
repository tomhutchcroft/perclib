# Review: pull request #2, "Lace expansion foundations with optimal zeroth-coefficient triangle bound" (head `630d985`)

Base of the pull request: `main` at `1df822a`. Reviewed against the integration branch
`claude/zen-lovelace-rvlcw2` at `b1db272`.

**Verdict: APPROVE WITH CHANGES** (three required changes, all mechanical; see below).

Thank you for the contribution. The two definitions are the right notions, they come with
a good basic API, and the main bound `1 + 4 * ∑' y, piZero q x y ≤ ∇` is correct, sharp,
and proved at the generality of an arbitrary countable vertex type and an inhomogeneous
profile. The changes below are about tags, the integration branch's linter set and one
header word; no statement needs to change.

## What the pull request does

One commit, six files: `PercLib.lean` (five import lines, alphabetical) and five new
files under `PercLib/Percolation/Bond/Lace/` (725 lines). Nothing outside `Lace/` and
`PercLib.lean` changes; no scripts, no `.github/`, no pins.

- `Basic.lean`: the definitions `doubleConn x y := disjointOccurrence (conn x y) (conn x y)`
  and `piZero q x y := if x = y then 0 else law q (doubleConn x y)`.
- `DoubleConnection.lean`: basic API (membership via two disjoint finite open
  certificates, `x = x` case, symmetry, upper set, measurability, monotonicity in the
  profile, zero profile), deletion and no-pivotal-edge lemmas, the implication to
  mathlib's `SimpleGraph.IsEdgeReachable 2`, the BK bounds
  `law q (doubleConn x y) ≤ tau q x y ^ 2` and `≤ tau q x y * P(connected after deleting e)`,
  the diagonal conventions `piZero_eq_sub`, `law_doubleConn_eq_indicator_add_piZero`, and
  the zero-order decomposition `tau = δ + piZero + P(conn \ doubleConn)`.
- `DistinctTriangle.lean`: for `x ≠ y`, a double connection contains three disjoint
  connections `x ↔ u`, `u ↔ y`, `x ↔ y` with `u ∉ {x, y}`; hence by BK
  `piZero q x y ≤ ∑' u, [u, x, y distinct] τ(x,u) τ(u,y) τ(y,x)`.
- `DiagramBounds.lean`: the exact decomposition of the rooted triangle into
  `1 + 3 · (off-diagonal bubble) + (distinct-vertex part)`, and from it
  `1 + 3 ∑ piZero ≤ ∇`, the main bound `1 + 4 ∑ piZero ≤ ∇`
  (`one_add_four_mul_tsum_piZero_le_triangle`), and summability of `piZero` under a
  finite triangle.
- `Sharpness.lean`: on the complete graph on `Fin 3` with all bonds open, `∑ piZero = 2`
  and `∇ = 9`, so the bound is an equality (`complete_three_attains_four`), and any
  universal real constant `c` in `1 + c ∑ piZero ≤ ∇` satisfies `c ≤ 4`
  (`coefficient_le_four_of_universal_bound`).

## Classification

**Interface** (two new definitions, D-24), in the lace-expansion area, which is the
contributor's area. The definitions are in a file named `Basic.lean`, one per
directory, as required.

## Definitions

**Search.** `git grep -n 'doubleConn\|disjointOcc\|DisjointOccurrence\|piZero\|IsEdgeReachable'`
over `PercLib` at the integration tip: no existing double-connection or zeroth-coefficient
notion; disjoint occurrence is `PercLib.Probability.disjointOccurrence`, which the pull
request reuses. Mathlib at the pinned revision has `SimpleGraph.IsEdgeReachable`, which
is the graph-theoretic notion; the pull request proves the implication to it and keeps
the certificate form, which is what BK needs. No duplication.

**Fidelity.** The wiki (`lace-expansion`, `#section-cutting` and `#section-finite`)
defines double connection as "either `s = x` or there are two edge-disjoint open paths"
and sets `Π⁽⁰⁾ = a₀ - δ₀` with `a₀(x) = P(0 ⇔ x)`; `lace-coefficient-diagrams` allows paths
to meet at vertices and uses `Π⁽⁰⁾(0) = 0`. `doubleConn` has edge certificates (paths may
share vertices) and is all of `Config V` at `x = x` (`doubleConn_self`); `piZero` is
`P(x ⇔ y) - δ(x, y)` (`piZero_eq_sub`) and vanishes on the diagonal (`piZero_self`). Both
match. The wiki's coefficient is the special case `q` = `p` on nearest-neighbour bonds of
`ℤ^d` and `0` elsewhere, at `x = 0`. I checked the diagonal convention against the wiki;
I did not check the section and equation numbers cited from the Heydenreich–van der
Hofstad book in the header.

**API** (D-35): membership (`mem_doubleConn_iff`), trivial case (`doubleConn_self`,
`piZero_self`, `piZero_of_ne`), symmetry (`doubleConn_comm`, `piZero_comm`), monotonicity
(`isUpperSet_doubleConn`, `doubleConn_mono`, `piZero_mono`), measurability
(`measurableSet_doubleConn`), bounds (`piZero_le_tau`, `piZero_le_one`, `piZero_ne_top`).
Complete.

| Definition | Binder | Class | Note |
|---|---|---|---|
| `doubleConn` | `V : Type*` | TYPING | vertex type; no structure needed for the event |
| | `x y : V` | SOURCE | endpoints `s, x` of `s ⇔ x` |
| `piZero` | `V : Type*` | TYPING | |
| | `q : Sym2 V → unitInterval` | SOURCE | generalises the homogeneous lattice parameter `p` (D-2 profile) |
| | `x y : V` | SOURCE | two-variable form of `Π⁽⁰⁾(y - x)` |
| | decidability of `x = y` | TYPING | classical; see required change 2 |

No EXCESS.

## Main statements

| Theorem | Binder | Class | Note |
|---|---|---|---|
| `one_add_four_mul_tsum_piZero_le_triangle` | `V`, `[Countable V]` | TYPING | countability is used for measurability and BK; `ℤ^d` is countable |
| | `q` | SOURCE | general profile |
| | `x` | SOURCE | root (`0` in the wiki) |
| `coefficient_le_four_of_universal_bound` | `c : ℝ` | SOURCE | the candidate constant |
| | `h` (bound for all profiles on `Fin 3`) | SOURCE | universality tested on three vertices only, which makes the theorem stronger |

No EXCESS; no theorem has more than ten hypotheses.

**Constant and diagonal.** The `1` is the `u = v = x` term `τ(x,x)³ = 1` of the rooted
triangle `∑' u, ∑' v, τ(x,u) τ(u,v) τ(v,x)`, which is the wiki's `∇_p` (`triangle-condition`,
67VP) in two-variable form; with `piZero x x = 0` this is the wiki's diagonal convention.

**Vacuity.** All sums are in `ℝ≥0∞`, where every family is summable, so there is no
"unsummable `tsum` is `0`" effect: the left side is the true mass and the right side the
true (possibly infinite) triangle. The bound is trivially true only when `∇ = ⊤`, which is
the content of the statement and not a convention. It is not trivially true otherwise: the
zero profile gives `1 ≤ 1`, and `complete_three_attains_four` gives equality `9 = 9` with
positive mass `2`. The passage to `ℝ` (`summable_piZero_toReal_of_triangle_lt_top`) states
the finite-triangle hypothesis explicitly. In `coefficient_le_four_of_universal_bound` the
`toReal` is harmless because every quantity on `Fin 3` is finite (`τ ≤ 1`), and the
hypothesis is satisfiable with `c = 4` by the main theorem.

**Relation to the wiki.** No wiki assertion states this bound. The closest is SJIL
(`lace-coefficient-diagrams`), whose first inequality is `‖Π⁽⁰⁾‖₁ ≤ T` with
`T = sup_x (τ * τ * (J * τ))(x)` on `ℤ^d`; its proof uses `Π⁽⁰⁾(x) ≤ τ(x)²` off zero, which is
`piZero_le_offDiagonal_tau_sq` here. The main bound is therefore a new result (a
different diagram, a sharp constant, general graphs), and the square bound is an
ingredient of SJIL's proof. No statement's fidelity to a source is in doubt.

## Trial merge into the integration branch and builds

- `git merge --no-commit 630d985` into `b1db272`: no conflicts (`PercLib.lean`
  auto-merged). The pull request uses only `conn`, `tau`, `law`, `openGraph`,
  `disjointOccurrence`, `countable_profile_bk` and existing lemmas, all present on the
  integration branch under the same names; the `localConn` fold and `IsCut` do not touch it.
- `lake build --wfail` of the five `Lace` modules on the merge: **fails**, only on the
  mathlib standard linter set that the integration branch enables
  (`linter.style.openClassical`, an error under `--wfail`):
  `Basic.lean:32`, `DoubleConnection.lean:31`, `DistinctTriangle.lean:28`
  (`open scoped ENNReal Classical`) and `DiagramBounds.lean:27` (`open Classical`).
  No other warning or error.
- With those opens removed and `open Classical in` placed before each declaration in the
  four files, the five modules build with `--wfail` on the merge (checked in a scratch
  copy, not committed anywhere). A narrower fix (only where needed) is described in
  required change 2.
- `python3 scripts/check_forbidden.py PercLib`: passed. `python3 scripts/check_import_closure.py PercLib`:
  passed. The header check of `scripts/check_d35.py` (item iv) on the merge: one failure,
  `DiagramBounds.lean` header carries the label `D-2` (required change 3).
- `#print axioms` on `one_add_four_mul_tsum_piZero_le_triangle`,
  `one_add_three_mul_tsum_piZero_le_triangle`, `complete_three_attains_four`,
  `coefficient_le_four_of_universal_bound`, `law_doubleConn_le_tau_mul_deleted`,
  `piZero_le_offDiagonal_tau_sq`, `tau_eq_indicator_add_piZero_add`,
  `piZero_le_distinct_triangle`, `summable_piZero_toReal_of_triangle_lt_top`: each
  `[propext, Classical.choice, Quot.sound]`.
- Standalone at `630d985` (`lake-manifest.json` and `lean-toolchain` are identical
  between `1df822a` and the integration tip; only `lakefile.toml` differs, by the linter
  set): `lake build --wfail PercLib.Percolation.Bond.Lace.Sharpness`, which builds all
  five modules: **succeeds**. So the pull request is green against `main` as it stands.
- The full gate was not run here (another gate was running on this machine).

## D-35 hygiene

No `sorry`, `admit`, `axiom`, `native_decide` or `set_option`. Module docstrings are
present in all five files. Names follow mathlib conventions and contain no identifiers.
Headers: see required change 3.

## Required changes

1. **Remove the five `@[tag …]` attributes**: `ZUND` (`Basic.lean:40`, `doubleConn`),
   `U8OS` (`Basic.lean:46`, `piZero`), `S9QJ` (`DoubleConnection.lean:182`,
   `law_doubleConn_le_tau_mul_deleted`), `X30S` (`DoubleConnection.lean:222`,
   `piZero_le_offDiagonal_tau_sq`) and `RCHH` (`DiagramBounds.lean:123`,
   `one_add_four_mul_tsum_piZero_le_triangle`), and the then unused
   `public import PercLib.Meta.Tag` in `Basic.lean`. None of these tags is declared by a
   wiki assertion. Under D-12 a tag is allocated together with a wiki assertion and is
   the link to it; the manifest builder rejects a tag absent from the wiki
   (`scripts/build_manifest.py`, "Unknown, withdrawn or absent wiki tag"). If a wiki
   assertion for the bound or the definitions is written later, the tags are attached
   then, in a separate small interface pull request.
2. **Replace the global `Classical` opens** (needed for the integration branch, which
   enables mathlib's standard linter set; harmless on `main`): in `Basic.lean`,
   `DoubleConnection.lean` and `DistinctTriangle.lean` change
   `open scoped ENNReal Classical` to `open scoped ENNReal`, and in `DiagramBounds.lean`
   delete `open Classical`. Then put `open Classical in` (before the docstring) on the
   definition `piZero` and on each declaration whose statement contains an
   `if … = … then … else …`; use the `classical` tactic inside proofs that need it.
   Putting `open Classical in` before every declaration of the four files also works and
   was checked to build.
3. **`DiagramBounds.lean`, header line 3**: "Original proofs on the D-2 bond interface"
   carries a decision label, which the header check rejects (headers carry provenance and
   the mathematical reference only). For example: "Original proofs on the bond interface
   of `PercLib.Percolation.Bond.Basic`."

## Optional suggestions

1. **Splitting.** D-24 and `CONTRIBUTING.md` ask for definitions and proofs in separate
   pull requests. This review read every statement here, so this pull request need not be
   split. For later ones, opening the definitions and their basic API first keeps reviews
   short.
2. **Mathlib's notion.** The converse of `isEdgeReachable_two_of_mem_doubleConn` (two-edge
   reachability gives two edge-disjoint finite certificates, Menger for `k = 2`) would give
   `doubleConn x y = {ω | (openGraph ω).IsEdgeReachable 2 x y}` and tie the definition to
   mathlib's API.
3. **General measures.** `triangle_eq_one_add_three_mul_offDiagonal_add` and its corollaries
   use only `τ(x,x) = 1` and symmetry. Once the announced `connProb μ` lands
   (`docs/INTERFACE_CHANGES.md`), they can be stated for an arbitrary measure on
   configurations. The same announcement may generalise `tsum_tau_sq_le_triangle` in
   `ConnectionKernel.lean`, which `DiagramBounds.lean` uses; the recipe there
   (`μ := law q`, then `connProb_law`) will cover it.

---
Generated by [Claude Code](https://claude.ai/code)
