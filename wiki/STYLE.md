# Wiki style

Draft for Tom's approval (D-19). Until he approves it, wiki work follows this draft. The model is
an encyclopaedia article with complete proofs one click away: a concise survey or monograph in
probability, third person, present tense. "Before" passages are quoted from the wiki; "after"
passages show the kind of change and may be improved.

## Article shape

1. **Lead.** One to three paragraphs before the first heading, readable on their own: what the
   object or result is, the main statement informally, why it matters and where it sits, with
   links. The parser accepts the lead as text before the first `## … {#section-…}` heading
   (see "Lead" in `wiki/README.md`).
   - Before (`hierarchical-two-point`, first line): "The vertex group is $\mathbb H_L^d=\dots$"
   - After: "On the hierarchical lattice, [long-range percolation] with kernel
     $J(x)\asymp\|x\|^{-d-\alpha}$ has critical two-point function of order
     $\|x-y\|^{-d+\alpha}$ for every $0<\alpha<d$ (Hutchcroft). The exponent is the mean-field
     one, also for $d<3\alpha$, below the upper critical dimension. ..."
2. **Sections, in this order, as they apply:** Definitions and setting; Statement(s); Examples
   and non-examples; Idea of the proof; Proof; Consequences and applications; Variants and
   generalisations; History and attribution; Formal verification; References. Formal
   verification (status, Lean statement, dependencies) is generated and never hand-written.
   Proof steps are paragraphs inside the Proof, never sections.
   - Before (`subcritical-bound`): "## 1. Use simple path witnesses", "## 2. Enlarge the
     deterministic sum", ... (five of seven sections are proof steps).
   - After: "## Proof", one collapsed block; inside, "*Step 1 (simple paths).* If
     $v\leftrightarrow w$, some simple open path joins them, so ..."
3. **Self-contained statements.** Every hypothesis of a statement is in the statement or in
   Definitions and setting. A statement read alone (at `/tag/XXXX/`, in a preview) must be
   complete. Moving a hypothesis out of the front-matter `context` never drops it.
   - Before (`subcritical-bound`): "Let $0\le m<1$, and suppose that $\sum_w q(v,w)\le m$ for
     every $v$." (countable graph, independence: only in the context box)
   - After: "Let $G=(V,E)$ be a countable graph and $\mathbb P_q$ independent bond percolation
     with edge probabilities $q:E\to[0,1]$, extended by $0$ off $E$. If $\sum_w q(v,w)\le m<1$
     for every $v$, then ..."
4. **Idea before proof; proof collapsed.** Each full proof follows a two-to-five-sentence idea
   and sits in `<details><summary>Proof</summary> ... </details>`; the summary says what is
   inside ("Proof of the converse", "Verification of (3)"). Long computations, once-used lemmas
   and the Lean statement are collapsed too. Statements, ideas, examples and consequences stay
   visible. A collapsed proof is complete: every step, nothing left to the reader.
   - Before (`regular-variation`): the statement, then at once "*Proof of the forward
     implication.* Write $F(t)=\mathbb P(X>t)$ ..."
   - After: "*Idea.* $\int_0^\infty e^{-u}F(ux)/F(x)\,du$ has integrand converging to
     $e^{-u}u^{-\alpha}$; dyadic Potter bounds dominate it. The converse identifies the limit
     measures by their moments and recovers $F$ by monotonicity." Then the collapsed proof.
5. **One topic per article.** A long subtopic gets its own article; here it keeps a
   one-paragraph summary under "*Main article: [...]*".
   - Before: `hierarchical-runaway`, 65 sections, from block quantiles to "Supremum moments of
     the Gaussian path limit".
   - After: "## Gaussian fluctuations. *Main article: [Gaussian fluctuations of hierarchical
     block clusters].* Centred and scaled, the power sums of block-cluster masses converge
     jointly to a Gaussian process ..."
6. **Examples and non-examples** wherever a reader asks "for which models?"
   - Before (`triangle-condition`): "Applying the theorem to a particular dimension or kernel
     requires a separate proof that its critical triangle diagram is finite."
   - After: "The triangle condition holds for nearest-neighbour percolation on $\mathbb Z^d$,
     $d\ge11$ (Fitzner–van der Hofstad), and for spread-out models with $d>6$ (Hara–Slade), by
     the [lace expansion]. It is expected to fail for $d<6$."
7. **Attribute in the text, as the literature names things.** Name and date the main result in
   the lead and in History and attribution. Results taken from the unpublished book are credited
   "T. Hutchcroft, book in preparation", with no locator.
   - Before (`regular-variation`): "## The Laplace–tail theorem".
   - After: "Karamata's Tauberian theorem (Feller, Vol. II, XIII.5; Bingham–Goldie–Teugels,
     1.7)".
8. **Inline links.** Link a concept, result or model that has an article at its first use in
   the lead and in each section, on the natural phrase, to `/articles/<id>/` or the assertion's
   `/tag/XXXX/`. Never a bare tag as link text or in prose, never "see here", never a link from
   exposition to `/coverage/` pages or to GitHub. "See also" holds only what had no place in
   the text.
   - Before (`hierarchical-runaway`): "Q4PO and F7Q2 give weak convergence to continuous paths."
   - After: "The [functional limit theorem for power sums] and its [nested-block version] give
     weak convergence to continuous paths."
9. **Subtitles** are one noun phrase or the informal statement.
   - Before (`hierarchical-two-point`): "A model-specific power law with a reusable dependency
     chain."
   - After: "The critical two-point function decays like $\|x-y\|^{-d+\alpha}$."

## Notation

One symbol per object across the wiki, unless the literature an article summarises forces
another; then the article says so once.

| Object | Symbol |
|---|---|
| law, expectation; homogeneous / edge-dependent / intensity model | $\mathbb P_p,\mathbb E_p$ / $\mathbb P_q$ with $q:E\to[0,1]$ / $\mathbb P_\beta$ |
| root vertex | $0$ on a group, $o$ otherwise |
| cluster of $x$ | $K_x$ |
| two-point function | $\tau_p(x,y)=\mathbb P_p(x\leftrightarrow y)$ |
| connection using only edges inside $S$ | $x\xleftrightarrow{S}y$, $\tau^S_p(x,y)$ |
| susceptibility, percolation probability | $\chi(p)=\mathbb E_p\lvert K_o\rvert$, $\theta(p)$ |
| critical points | $p_c$, $\beta_c$ |
| slowly varying function | $\ell$ ($L$ is the hierarchical scale) |

Before: "$x\leftrightarrow y$ inside $\Lambda(x,y)$" (`hierarchical-two-point`), "$x\leftrightarrow_S y$"
(`harris-inequality`), "$\tau_{T,\beta_c}(o,u)$" (`hierarchical-runaway`). After:
$\tau^{\Lambda(x,y)}_{\beta_c}(x,y)$, $x\xleftrightarrow{S}y$, $\tau^{T}_{\beta_c}(o,u)$.
Do not give one letter two meanings in articles read together ($q$ is an edge-probability
function; write $\eta$ for an extinction probability).

## Wording

10. **No process language in the exposition.** No inventories, interfaces, contracts, wrappers,
    obligations, pins, ports, packages, issues, commit hashes, line numbers, "the notes", "the
    source", Lean types or library names. Provenance and status belong to the generated panel,
    credit to History and attribution.
    - Before (`regular-variation`): "It does not contain the uniform-convergence, Potter or
      Karamata theorems merely by defining this interface."
    - Before (`harris-inequality`): "These are the same inequalities whether probabilities are
      represented as real or extended nonnegative numbers."
    - After: both deleted.
11. **State what is assumed; do not list what is not.** Name an absent hypothesis at most once
    per article, and only where the literature usually assumes it ("on any countable graph, not
    necessarily locally finite"). Delete sentences that deny claims nobody made.
    - Before (`subcritical-bound`): "All changes of summation order are justified by
      nonnegativity. No finiteness of susceptibility was assumed during the argument."
    - After: "All terms are nonnegative, so the sums may be rearranged."
12. **Make the positive statement; drop the foil** ("X, not Y", "rather than", "there is no
    contradiction").
    - Before (`sharpness`): "the condition is now $p<p_c$, rather than an explicit but generally
      nonoptimal bound on the row sum."
    - After: "Sharpness replaces the condition $2dp<1$ of the [row-sum bound] by the optimal
      condition $p<p_c$."
13. **No signposts or intensifiers:** "importantly", "crucially", "the deeper step", "the
    essential step", "deliberately", "immediately", "for completeness". If a step is the crux,
    the idea paragraph says so once.
    - Before (`sle-conformal-radius`): "This positive lower bound is the essential integrability
      step."
    - After: deleted; the idea paragraph says that $F_p(1)>0$ gives integrability.
14. **Timeless and impersonal.** No "now", "new", "newer" for the history of the wiki; no
    sentences addressed to editors; "we" only inside proofs.
    - Before (`hierarchical-runaway`): "The finite-approximation theorem now strengthens the
      linked coalescent input".
    - Before (`hierarchical-two-point`): "... need their own hypotheses and proofs; they should
      not be silently attached to this result."
    - After: "When the initial laws converge weakly in $\ell^2_\downarrow$, the coalescent paths
      converge in $J_1$ on bounded intervals ([finite-approximation theorem])." The second is
      deleted.
15. **The literature's words.** Write "graph" for "host", "hypotheses" for "inputs", and
    "$\varphi_p(S)<1$" or "$S$ witnesses subcriticality" for "certificate". Define a coined term
    where it is first used, or drop it.
16. **Rhythm.** Content sets paragraph length. Use a list only for parallel items, and a
    paragraph for an argument. A paragraph does not close by restating itself or by a
    disclaimer; a section whose second paragraph only disclaims or points elsewhere becomes one
    paragraph. Triplets ("X, Y and Z") only when there really are three parallel things. Bold
    only where a term is defined.

## Citations

Cite a published work by its key in the source catalogue (`src/content/catalog.json`, field
`id`): `[@key]`, or `[@key, locator]` with the locator ("Theorem 1.1", "§3") kept in the
visible text; several works go in one bracket separated by `;`. The generator renders each as
the catalogue's short label linked to `#ref-<key>` in a References list at the foot of the
article (only the works the page cites, each with backlinks to its citations), and the site
bibliography `/bibliography/` lists every catalogue entry with the articles citing it.
Citations inside collapsed proofs are written the same way. A key missing from the catalogue
fails the build: add the work to the catalogue first. The book in preparation
(`hutchcroft-book`) is cited without a locator. Plain-text citations ("Hutchcroft (2022)",
"[DCT16, Theorem 1.1]", a bare arXiv identifier) are listed in `dist/link-report.txt`.

- Before: "Sharpness was proved by Duminil-Copin and Tassion [DCT16, Theorem 1.1]."
- After: "Sharpness was proved by Duminil-Copin and Tassion [@dct-sharpness, Theorem 1.1]."
  (renders as "Sharpness was proved by Duminil-Copin and Tassion [Duminil-Copin–Tassion,
  Theorem 1.1]", the bracket linking to the References entry).
