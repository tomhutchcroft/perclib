# Wiki article editing and assertion tags

This directory is the PercLib wiki, kept in the public `perclib` repository. Its prose is
licensed under CC BY 4.0 (https://creativecommons.org/licenses/by/4.0/); the code and
tooling are Apache-2.0.
See [NOTICE](NOTICE).

The twelve articles live in `articles/*.md`. W-1 preserves the original prototype
exposition exactly. The static generator renders these sources at real article URLs.

## Build and checks

```sh
cd wiki
npm ci
npm run build
```

This runs regression tests and checks content preservation, identities, internal
references and mathematics. Output is generated in `wiki/dist/` and is ignored by
Git. Serve that directory at the web origin root, for example with
`python3 -m http.server 8000 --directory dist`. No Lean command is invoked.
The old `wiki/prototype` npm entry point delegates to this build for existing CI.

Handwritten renderer, CSS, browser search/menu code, and bibliography records live
in `src/`. Articles are complete HTML pages at `/articles/<id>/`; KaTeX runs only
at build time. `/tag/XXXX/` redirects to the article assertion, with a visible link
as a fallback. A static server should normalize directory requests (`/tag/XXXX`)
to their trailing-slash path. Withdrawn identities have permanent tombstone pages.
Search uses `search-index.json`; reading and navigation do not require JavaScript.
All generated local links and fragments are checked before output is replaced.

For just the article/tag checks, run `node wiki/scripts/check-articles.mjs` from
the repository root. `node wiki/scripts/check-articles.mjs <base-commit>` also
checks history against an explicit revision. A local build compares with HEAD
and works offline. In GitHub Actions, the event's PR base or push-before commit is
used; a shallow checkout fetches that one commit if necessary. Failure to obtain
that base fails validation rather than silently skipping history. Source archives
without Git still validate their current ledger and content.

## Deployment

`.github/workflows/pages.yml` publishes the site on GitHub Pages, at
<https://tomhutchcroft.github.io/perclib/>, on every push to `main` that touches
`wiki/` or the manifest inputs (`PercLib/`, `PercLib.lean`,
`scripts/ExtractManifest.lean`, `scripts/build_manifest.py`), and on a manual run of
`main`. It builds PercLib, extracts the manifest of that commit and builds the wiki
with it. `WIKI_REQUIRE_MANIFEST=1` makes the build fail without a manifest, so the
published site always shows formal status. The manifest, compiled earlier in the same
workflow run, is accepted without an artifact receipt only if it names that run
(`WIKI_MANIFEST_RUN`) and the commit being built (`WIKI_BUILD_COMMIT`).

The site is served under a base path. `node src/build.mjs --base-path /perclib/ [dir]`
(or `WIKI_BASE_PATH`) generates the pages with root-relative URLs, checks them, then
prefixes every link, asset, refresh redirect and search-index URL with the base; the
search script reads it from `<html data-base>`. Without the option the base is `/`
and the output is unchanged. `tests/pages-site.test.mjs` builds under `/perclib/` and
checks that every local URL resolves inside the output directory.

Every page carries the unfinished banner at the top of its main content and
`<meta name="robots" content="noindex">`; the home page states the counts of the
build, and `/about/` (generated, not an article) explains the formal statuses, the
provisional errata, authorship, responsibility, licence, and the commit and date of
the build. `WIKI_HISTORY_BASE` names the commit for the tag-history check when the
workflow has no push base.

Each article page carries a small "Draft" marker until the article has been through
the critic and restructuring. `src/passed-articles.json` is the list of article ids
that have passed; add an id there (and only there) when an article passes, and
remove it if the article is reopened. The build fails on an unknown or repeated id.

## File format

Front matter is JSON between `---` delimiters (JSON is a YAML subset). It holds
article discovery metadata and the original `context` array of running notation
and assumptions. It contains no assertion tag, authored formal status, or Lean
declaration name. Article filenames match their `id`.

An optional lead precedes the first section (see "Lead").
Sections use `## Heading {#section-section-id}`. Their bodies retain the original
HTML, valid inside Markdown, so mathematical delimiters, links, whitespace, and
hypothesis placement survive the migration without a conversion round trip.
Sections are separated by a blank line; the file ends with one newline. The reader implements this
small explicit format; it is not a general-purpose Markdown parser.

An assertion anchor immediately precedes the original statement block:

```html
<a id="tag-0A3F" data-assertion="theorem" data-title="Short assertion title"></a>
```

`0A3F` here is illustrative, not a reservation. Kinds are `definition`,
`proposition`, `theorem`, and `corollary`. A tag identifies a citable assertion,
not a page or every displayed intermediate calculation. Compound theorem
conclusions can share one tag; independently useful results receive separate
tags. The statement still inherits its article's running context. Never move a
theorem-specific hypothesis into that context when editing.

The anchors are deliberately invisible, preserving the approved prototype design.
Legacy `PC-...` references in source bodies resolve through the migration baseline;
they are not assertion identities. `prototypeUses` preserves editorial reading
links, not extracted Lean dependency data. The build converts old hash links to
static paths while leaving the authored article bodies unchanged. Each assertion's
destination is `/articles/<id>/#tag-XXXX`.

## Lead

The body may open, before its first `## … {#section-…}` heading, with a lead of one
to three paragraphs and no heading. A paragraph is either a block of complete
`<p>…</p>` elements or bare text (rendered inside `<p>`); paragraphs are separated by
one blank line, and the lead by one blank line from the first heading. Inline
mathematics, links and wanted links work as in sections. The lead renders after the
article header and before the running context and the contents box, which does not
list it; its element has id `section-lead`, so the section id `lead` is reserved.
Search, "What links here", "Assertion citations" (as "Introduction"), the dead-link
check and the link report treat it as body text (`<article>#section-lead`). An
assertion anchor, a heading (`#` or `<h1>`–`<h6>`), a collapsible block (`:::` or
`<details>`), any other block element or a fourth paragraph in the lead fails the
build with the article file and line: assertions belong in sections.

Frozen-article digests: the lead is not article metadata and not a section. An article
without a lead hashes exactly as before. A baseline entry may carry
`"lead": {"sha256": …}`, the SHA-256 of the lead text as written (from its first
character to the end of its last paragraph, without the separating blank line). The
check requires that digest exactly when the article has a lead, so adding a lead to a
frozen article adds this one digest and changes no other.

## Collapsible blocks

Full proofs, long computations, technical lemmas used once, Lean statements and
provenance are written as collapsed blocks. Put the fences on lines of their own
inside a section body:

```html
<p>Idea of the proof, visible by default.</p>
:::details Proof of the lower bound
<p>Every step of the proof. Mathematics such as $\chi_q(v)\le 1/(1-m)$ and
display formulas render as everywhere else.</p>
:::
```

The text after `:::details` is the summary line shown when the block is closed.
It is mandatory and says what is inside ("Proof", "Proof of the lower bound",
"Verification of (3)"); it may contain inline mathematics. The closing fence is
the same run of colons alone on its line. To nest a block, give the outer block
more colons:

```html
::::details Proof of Theorem 2
<p>…</p>
:::details Verification of (3)
<p>…</p>
:::
<p>…</p>
::::
```

The build renders each block as `<details class="collapsible"><summary>…</summary>`
`<div class="collapsible-body">…</div></details>`. An unclosed block, a stray closing
fence, a missing summary or an unknown directive fails the build with the article,
section and line. Hand-written `<details>` elements are also accepted, provided they
begin with a `<summary>`.

On the site: a link to an anchor inside collapsed blocks (`#tag-XXXX`, `/tag/XXXX/`, or
any other fragment) opens every enclosing block and scrolls to the anchor, on page load
and on clicks within the page. Articles with collapsed blocks get "Expand all" and
"Collapse all" buttons. Printing opens every block (print stylesheet plus a
`beforeprint` handler that restores the reader's state afterwards), and the offline
export writes every block expanded. Search indexes the text of collapsed blocks with
the rest of the article. Without JavaScript the blocks still open with one click; only
the automatic opening for links needs JavaScript.

## Links, backlinks and the link report

Link a concept, result or model with its own article in running text, on the natural
phrase: `<a href="/articles/connectivity/">open clusters</a>`, or for a cited result its
assertion, `<a href="/tag/53Z9/">uniform row-sum bound</a>`. Legacy `#/article` links
still work.

A term whose article does not exist yet may be marked as a wanted page:

```html
<a data-wanted="random-cluster-model">random-cluster model</a>
```

The value is the intended article id. It renders as a marked phrase without a
destination. Once an article with that id exists, the build renders it as an ordinary
link and lists it in the report for cleanup.

Every article page has a contents box listing its sections (and any `<h3 id="…">`
sub-headings) and the generated panels. "What links here" in the Connections panel lists
every article whose body links to this one, in any link form; "Assertion citations" lists,
for each assertion, the article sections that link to it. Internal links in an article
body show a hover preview (kind, title and article or summary of the target, with
mathematics rendered at build time); the preview data are embedded in each page, so
previews also work offline.

The build fails on a dead internal link in an article body (unknown article, unknown
or withdrawn assertion, missing section or anchor), naming the article and section,
before the whole-site link check runs. It also writes an advisory report, which never
fails the build, to `dist/link-report.txt` (and `dist/link-report.json`):

- articles whose body has no inline link to another article (sections titled
  "See also" do not count);
- concepts mentioned without a link although an article exists: in each section, the
  title or a multi-word alias of another article occurring in the text (outside links,
  mathematics, code, headings and summaries) while that section has no link to it;
- wanted pages, with the phrases used and the sections that want them, for the wiki
  queue.

## Allocate and withdraw

From the repository root:

```sh
wiki/scripts/new_tag
```

This reserves a random four-character uppercase base-36 tag in `tags.json` and
prints it. Add its anchor beside the statement, and commit the article and ledger
together. Unused allocations remain reserved. A lock excludes concurrent writers;
a second writer fails explicitly. The replacement ledger is written atomically.
After integrating another branch, validate again: independently allocated tags
can collide and CI rejects the collision. Do not delete ledger entries.

To withdraw an assertion, first remove its anchor, then run:

```sh
wiki/scripts/new_tag --withdraw XXXX
```

The ledger retains a tombstone forever. History validation rejects a removed
reservation, reactivated tombstone, or removed assertion without its tombstone.
Moving an assertion between articles preserves its tag. Mathematical changes to
an assertion's identity need editorial review; a validator cannot decide whether
two different mathematical statements mean the same thing.

## Migration evidence

`migration-baseline.json` records SHA-256 digests of each original section body and
article metadata (and of a lead, if one is added later; see "Lead"), plus the original
Git revision. Checks strip only the exact
assertion anchor syntax and compare every section. The original JSON remains in
Git history; it is no longer an independently editable source. The digests prove
preservation relative to that recorded snapshot, not mathematical correctness.
Changing prose intentionally in a later package requires explicit review and an
update to this temporary preservation check. Do not update digests merely to hide
an accidental migration difference.

The superseded W-1 branch (`cdf39dac239a5183393fdc534dd6ec3d7c6be6b2`)
allocated 33 other tags before the duplicate writer was retired. Those identities
are retained as withdrawn reservations in `tags.json`; they must never be reused.
All 49 section bodies and all 33 tagged sections were compared with this migration:
the prose is identical and every tagged section has assertion coverage here.
The continuing W-1 work supplies the 65 active assertion anchors. The withdrawn
identities do not introduce additional assertions or a second registry.

## Compiled evidence (W-4)

A normal build works without Lean and without an artifact. In that case formal
status is unavailable; absence of a supplied manifest is not a claim that every
assertion is unformalised. No repository measurement/status snapshot is committed.

The publishing environment obtains a successful W-3 `assertion-manifest` artifact
using its GitHub artifact ID (Python 3 standard library; `GH_TOKEN` or `GITHUB_TOKEN`
is used for authenticated downloads):

```sh
python3 wiki/scripts/fetch-manifest.py ARTIFACT_ID --output wiki/.artifacts
cd wiki
WIKI_MANIFEST=.artifacts/manifest.json \
WIKI_MANIFEST_RECEIPT=.artifacts/receipt.json npm run build
```

The downloader checks GitHub's archive digest and artifact/run association, requires
a completed successful run, and binds the exact manifest bytes into a receipt.
The build validates that receipt offline. Use receipts from this trusted download
step; a JSON receipt is not a digital signature and cannot authenticate a hand-edited
file. Neither artifacts nor receipts belong in Git. A PR artifact may identify the
synthetic merge checkout, which differs from the run's head SHA. The displayed
commit comes from the artifact and the run link from the matching successful run.

The consumer accepts W-3's `perclib-manifest-v1` schema and requires complete coverage
of the current active assertion tags. Unknown/duplicate tags, missing declarations,
invalid source locations or dependency references, forbidden axioms, contradictory
Input debts, unsupported fingerprints, or mismatched evidence fail the build.
The article locations used for links come from the current wiki; Lean names and
statements come only from the artifact. Missing source lines remain unavailable.

`reviews/correspondence.json` stores real correspondence reviews, never authored
proof statuses. Its schema is `perclib-reviews-v1`, with a `reviews` array. Each entry
contains `tag`, `fingerprint` (`schema` and `sha256` copied from the reviewed artifact),
`reviewer`, `date` (`YYYY-MM-DD`), and `url` linking the actual GitHub review/discussion.
Do not create a review merely because Lean compiled. No reviews are fabricated by
the default empty file. A changed definition changes the fingerprint; old records
remain visible as stale. A fingerprint schema change requires consumer support and
fresh review, not silent acceptance.

Raw `statement-only` becomes D-4 `stated` only with a matching correspondence review.
Otherwise it is shown as a compiled statement awaiting correspondence, without a
D-4 status claim. `proved` and `proved-modulo` describe the extracted Lean statement;
correspondence to the prose is displayed separately. `proved-modulo` always shows
its named inputs. Statement and proof dependencies are shown on separate axes.
No new Lean association or mathematical review is supplied by this consumer.

To link published doc-gen4 output, additionally set `WIKI_DOCGEN_BASE` to its HTTPS
root and `WIKI_DOCGEN_COMMIT` to the exact artifact commit. Without that binding,
the site links the exact Lean source and explicitly says API documentation has not
been supplied; it never guesses a current hosted documentation URL.

Run `python3 wiki/tests/test_artifact.py` for downloader digest/redirect regressions.
The ordinary npm test suite includes artifact/review join, stale-review, status,
dependency, source-link and generated-page integration tests. Their synthetic Lean
statements and reviews are fixtures only, never published evidence.

### Tagged source concordance

`records/<article-id>.json` stores each article’s `occursIn` source-occurrence
records. The loader assembles the `perclib-occurs-in-v1` input for validation. It contains no proof statuses and allocates no tags. Each occurrence names
an existing `source` catalog ID and active `tag`, the exact catalog `source_url` and
`edition`, a precise `locator`, a `relationship`, and a mathematical `note` explaining
the relationship. Relationships are `source-statement`, `generalization` (the wiki
assertion generalizes the source), `specialization`, or `definition`. Changing a
source URL or edition requires reconciling its records; stale records fail the build.

The source index, each source page, and the associated assertion's article render
these records from one input. Formal status and wiki/Lean review staleness come only
from the validated compiled evidence. A source record never supplies a correspondence
review and does not certify source fidelity. Legacy editorial reading links remain
visible and are explicitly distinguished from tagged occurrences.

No occurrence is inferred from article titles, similar
statements or a theorem's name. In particular, the uniform-row generalization and its
zero-row case must not be advertised as the source's verbatim transitive theorem.
### Generated proof frontier

`/frontier/` is rebuilt from the same validated manifest and receipt as the evidence
panels. Each article’s `records/<article-id>.json` stores `proofUses` records for intended
proof prerequisites, never statuses. Each record contains `tag`, `proof_uses` (unique active tags) and `reason`
(the mathematical justification for this prerequisite list). A missing record is
unknown; an explicit empty list asserts that no additional tagged proof prerequisites
are needed. Article reading links are not proof dependencies.

For each unproved assertion with a record, the build takes the union of extracted
statement dependencies, extracted proof dependencies, and authored `proof_uses`.
It is ready by prerequisites exactly when every member is `proved` in the supplied
snapshot. `proved-modulo` does not satisfy a prerequisite. Named inputs and the
fingerprint correspondence review remain visible; readiness is not an assignment
or an approval to skip statement review. Proved assertions are omitted and their
authored proof prerequisites ignored (D-14). Cyclic unproved prerequisites remain
blocked. No manifest means no computed readiness.

The old COORDINATION §6 table is a package scheduling table, not a list of tagged
assertions. It cannot establish assertion-level frontier equivalence. Its removal
and any package-queue migration belong to INTEGRATOR; this package edits only `wiki/`.


### Articles after the migration

New articles may be added now that W-1 through W-4 have merged. The migration
baseline remains immutable: the original twelve articles must still be present with
identical metadata, sections and text. Additional articles use the same parser, tag
ledger, link checks and math renderer; they do not enter or rewrite that baseline.
Reserve tags with `scripts/new_tag` before inserting their anchors. Article prose
never claims a Lean status; the compiled evidence panel supplies it when available.

### Growth analytics

`/metrics/library/`, `/metrics/wiki/` and `/metrics/errata/` are generated from committed Git snapshots;
`/metrics/history.json` contains the complete series used by their charts and tables.
The default tip is `HEAD`. Set `WIKI_HISTORY_REF` to an available revision (for example,
`origin/main`) to analyze that history instead. The resolved commit is displayed.
The reference comparison defaults to the locally recorded `refs/remotes/origin/main`.
Set `WIKI_HISTORY_REFERENCE` to another available revision to override it. The JSON
records its resolved commit, source counts, common ancestor (when known), and the
relationship to the selected tip. The pages compare complete tree counts; a divergent
reference is not treated as the branch's contribution. A missing reference leaves the
growth series available and marks the comparison unavailable. A shallow or disconnected
history can leave ancestry unknown even when both trees can be counted. References are
never assumed current with GitHub.

`/metrics/reference/library/`, `/metrics/reference/wiki/` and `/metrics/reference/errata/` follow the reference's
own first-parent chain. They remain separate from the selected draft history: a
divergent draft does not lose its changes, and reference-only merges do not appear
as draft commits. The reference timeline is stored in `comparison.history` in the
main JSON and independently in `/metrics/reference/history.json`. Its snapshot
and daily CSV downloads are at `/metrics/reference/history.csv` and
`/metrics/reference/history-daily.csv`. In those exports, `selectedTip` is the
reference series tip, not the wiki build's tip; the JSON also records `buildTip`
and the reference name. Both series use the same counter definitions and retain
their first observed baseline without inventing earlier changes. A shallow
checkout marks both histories incomplete. A missing reference, unreadable
reference history, or older saved data without a reference timeline displays an
unavailable state rather than manufacturing a series from one comparison point.

The build never fetches history or runs Lean. Use a full checkout for the full range;
a shallow checkout is visibly marked as incomplete. An exported source archive with
no Git metadata displays history as unavailable.

Snapshots follow the first-parent history, retaining commits that changed `PercLib/`,
its former path `Lrp/`, `wiki/articles/`, `wiki/sources/`, `wiki/errata/` or `wiki/tags.json`, plus the
tip of the respective series. Charts use equally spaced
snapshots rather than an elapsed-time axis. Tables give commit timestamps, exact
counts and adjacent-snapshot changes. Dirty working files are excluded.

Lean counts measure tracked source files and nonblank lines, including comments and
definitions, not verified theorem totals. Article word counts measure whitespace
separated source tokens including metadata and markup. Anchors, permanent tag
reservations and withdrawals are separate series. Earlier prototype HTML is not
counted as canonical articles. Historical proof and correspondence status require
historical manifests/reviews; no such series is inferred from source text.

Errata history counts direct JSON children of `wiki/errata/`, total entries and
the recorded provisional, confirmed and withdrawn statuses. Confirmation and
withdrawal move an entry between status counters without removing it from the total;
deleting a record is not interpreted as withdrawal. Errata-only commits are included.
These are editorial record counts, not certifications of source errors or Lean fixes.
Commit dates do not establish when an error was discovered or confirmed elsewhere.


### Downloadable offline snapshots

After committing the wiki changes and completing the static build, run:

```sh
npm --prefix wiki run export:offline -- \
  --output /tmp/perclib-wiki-export \
  --status "Unmerged local draft; not pushed to GitHub."

```

Use a new output directory and an accurate revision status. Python 3's standard
library is the only additional requirement; no Lean toolchain or network access
is used. The exporter refuses a dirty checkout or a build whose history tip is
not the current commit. It leaves the built site unchanged.

The result contains an extracted reader, plus a `publish/` directory with
`perclib-wiki.zip`, a download page, reading instructions and `snapshot.json`.
Copy that publication directory to the `downloads/` route of the site that serves
the snapshot and link it from that site's revision banner. Regenerate it for each
new revision; an older archive must retain its older revision label.

Readers extract the entire ZIP and open `index.html`. Navigation, search,
mathematical fonts, errata and analytics work without a local server. Links
to papers and repositories still require the internet. Mobile file-manager
previews may not support multi-file sites; use a browser or HTML viewer that
can open the extracted folder.

The ZIP also includes the exact tracked `wiki/` source, checked against Git
blob hashes. It excludes Git history, installed dependencies and the Lean
repository. The reader is immediately usable; rebuilding the source requires
the repository context and dependencies documented here. The export retains
errata confirmation, fix-availability and significance labels without inferring
formal verification.

Checks preserve HTML text and rendered mathematics, resolve local links and
anchors, verify fonts, and check every ZIP member against the export hash
manifest. Fixed ZIP timestamps make the archive deterministic for identical
inputs. Source and build file hashes, full commit and status are included.
Run `npm --prefix wiki run test:export` for packaging regressions; the
normal JavaScript test suite exercises hosted and offline search.

The five counters are included in snapshot, daily and file-comparison CSV exports,
and the errata page has its own source-file comparison.

Historical records are counted without joining them to today's tags or bibliography.
Unknown formats, malformed JSON, duplicate entry IDs or unknown statuses leave the
entry counters unavailable while the observed source-file count remains known.
A snapshot with no errata files has zero counts. Older saved histories that omit
these fields instead remain unavailable: charts omit incomplete series and CSV
exports leave unknown values and deltas blank.


The selected-revision growth pages also show a file-level inventory for the selected tip and the
recorded comparison revision. Each path links to its exact committed contents;
blob identities distinguish edits that leave source counts unchanged. Added and
removed mean absent from one of these trees, not newly authored or deleted by a
particular contributor. Renamed paths appear separately. The inventories and
per-file counts are in `metrics/history.json`; the CSV remains the snapshot time
series. Missing reference inventories do not imply an empty baseline. These
source inventories do not supply historical compiled or reviewed status.

## Source reading maps

`/coverage/` renders the canonical worklist. Its article links may include a
section or assertion fragment; the final site link check verifies the destination.
Version-specific reading maps live in `wiki/sources/<slug>.md` and appear at
`/coverage/sources/<slug>/`, in the coverage list and in browser search. Worklist
links use `sources/<slug>.md`; missing maps fail the build. A source archive with
no maps directory simply has no reading-map entries.

The intentionally small reading-map format accepts a standalone `# Title`,
paragraphs, `##`/`###` headings, HTTPS links, article links and simple pipe tables.
Raw HTML is escaped. This is a reading inventory, not another tag registry or an
authored formalization status. Maps render into the static site and are therefore
included in the standalone preview without fetching their Markdown at runtime.

### Article-owned records

Each article has one optional `records/<article-id>.json` file with schema
`perclib-article-records-v1` and an `article` matching the filename. Its arrays are
`collections` (collection ID and display order), `sourceOccurrences` (source ID,
display order and editorial reading records), `occursIn` (tagged source records)
and `proofUses` (tagged proof prerequisites). Tagged records must belong to that
article. `order` preserves the historical display order; ties use the article ID.
New articles may choose an order without renumbering other articles.

`src/content/catalog.json` holds only source bibliography and subject descriptions.
Do not add article rows there. Add or revise an article's rows in its own record
file. The compiled manifest, formal review records and permanent tag ledger remain
separate from these authored reading and relation records.

### Source errata

`/errata/` links one page per source. Entries live in `errata/<source-id>.json`
with schema `perclib-source-errata-v1`, a catalog `source`, and `entries`. Each
entry has a permanent local `id`, title, exact locator, paraphrased source claim,
reported problem, corrected statement or explicit unresolved scope, existing
assertion tags and issue URLs. The required `leanImpact` explains the mathematical
consequences for formalisation: the corrected contract or proof dependency, the
hypotheses a workaround adds, and any targets left unaffected. It is not a hand-kept
proof status and contains no Lean declaration names. The build links affected articles and source pages
and includes the entries in search. Errata never allocate assertion tags.

The editorial status starts as `provisional`. Change it to `confirmed` only after
Tom explicitly confirms the correction, and retain his `confirmationUrl`.
A review by an agent or a successful build is not Tom's confirmation. Withdraw
an incorrect report with status `withdrawn`, a `withdrawalReason` and
`withdrawalUrl`; retain its ID and source file so its URL remains a tombstone.
This status is separate from manifest-derived formal proof status.

Give each current entry a `resolution` assessment with four fields:

- `status`: `found`, `partial`, `workaround`, or `open`. Assess the specific
  diagnosed issue, not whether every theorem in the paper has been reconstructed.
- `summary`: the concrete repair or the remaining obstacle. Identify a repair
  already present in a later source edition as such.
- `scale`: `notation`, `local`, `substantial`, `statement`, or `unknown`.
  This describes changes to the source mathematics, not Lean implementation effort.
- `impact`: explain what must change and whether the intended conclusion survives.
  State any altered hypotheses, constants, model or unresolved scope explicitly.

`found` means that a concrete repair of the reported issue is available, possibly
with a corrected statement. `partial` leaves part of that issue unresolved;
`workaround` supplies a different or restricted result without settling the
intended claim; `open` records no sufficient repair. These are editorial
assessments of the written corrections, not formal proof statuses. They neither
confirm an erratum on Tom's behalf nor change manifest evidence. Legacy entries
without an assessment display “Not assessed”; no status is inferred from their
correction text. Withdrawn entries retain their URLs but do not contribute to
current repair counts. Counts are per source entry, so a diagnosis repeated in
two sources appears twice. Historical editorial counts are unchanged.

The errata list shows repair counts, incomplete entries, and the repair and impact
for every source entry. Source detail pages and article errata notices show the
same labels, and search includes the assessments.

Each source errata page joins its assertion tags to the same validated manifest
and fingerprint-bound correspondence reviews as the article pages. It displays
the compiled commit, evidence link, formal status and any named input debts, with
links to the statements and Lean evidence on the articles. Without a manifest,
formal status is unavailable (not inferred to be `unformalised`). A changed
fingerprint leaves the correspondence review stale; confirming an erratum does
not refresh that review or prove the correction. Authored formal-status fields
are rejected. Keep all diagnoses pinned to the edition actually inspected; do
not silently extend an arXiv-version discrepancy to a later published edition.


For a shared source-version audit, an errata file may include `versionAudit`:

- `checkedVersion` and `checkedUrl`: the exact edition actually inspected and its
  HTTPS reference.
- `method`: what was inspected, such as versioned HTML and extracted PDF text;
  distinguish this from visual PDF inspection.
- `scope`: which entries and passages this audit covers and its limitations.
- `comparisons`: a list of other editions, each with `version`, HTTPS `url`,
  `status` (`pending` or `compared`) and concrete `findings`.

`pending` means the stated comparison remains unfinished. `compared` means only
that the comparison described in `findings` was made; identify the passages,
method and results, including any remaining uncertainty. A publication record
or accessible download link does not establish that formulas were compared.
Neither status confirms an erratum or certifies a repair. The shared audit must
not overstate coverage of individual entries; their exact locators remain
authoritative.

The errata index and source detail page show this audit, and search includes it.
Files without it display “Source-version audit not recorded here; consult the
individual locators.” This does not mean their sources have never been read.
Existing entry IDs, repair counts, editorial statuses and formal evidence are
independent of version-comparison metadata.
