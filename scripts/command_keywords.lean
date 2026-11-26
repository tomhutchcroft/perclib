/-
Copyright (c) 2026 Tom Hutchcroft. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Print the command keywords of the pinned Lean and Mathlib, for the `COMMAND_KEYWORDS`
block of scripts/automerge_classify.py. Run from the repository root:

  lake env lean scripts/command_keywords.lean > keywords.txt

and replace the lines between the `BEGIN`/`END` markers of that block by the output.

It reads the leading-token table of the parser category `command` in the environment of
`import Mathlib`, that is, every token that can begin a command, and adds the keywords of
the command parsers that must begin with a doc comment (such as `add_decl_doc`), whose
keyword comes second. It prints, one per line and sorted, the identifier part of each
such token that begins with a letter (so `variable?` gives `variable` and
`compile_inductive%` gives `compile_inductive`). Tokens beginning with `#` are left out,
since the classifier rejects every `#` on a changed line, and so are symbol tokens (`@[`,
`$`, the doc-comment openers). It fails if some command parser is not indexed by a first
token, since the list would then be incomplete.
-/
import Mathlib

open Lean Parser Elab Command

/-- The identifier part of a token, if the token begins with a letter. -/
def identPart (s : String) : Option String :=
  match s.toList with
  | c :: _ =>
    if c.isAlpha then
      some (String.ofList (s.toList.takeWhile fun c => c.isAlphanum || c == '_'))
    else none
  | [] => none

#eval show CommandElabM Unit from do
  let some cat := (parserExtension.getState (← getEnv)).categories.find? `command
    | throwError "no parser category `command`"
  unless cat.tables.leadingParsers.isEmpty do
    throwError "{cat.tables.leadingParsers.length} command parsers have no first token; \
      the keyword list would be incomplete"
  let leading := cat.tables.leadingTable.toList.map fun (tk, _) =>
    tk.toString (escape := false)
  -- Parsers whose first token is always a doc comment (antiquotations aside).
  let docFirst := ((cat.tables.leadingTable.get? (Name.mkSimple "/--")).getD []).filter
    fun (p, _) => match p.info.firstTokens with
      | .tokens ts => ts.all fun t => t == "/--" || t.startsWith "$"
      | _ => false
  let second := docFirst.flatMap fun (p, _) => p.info.collectTokens []
  let words := (leading ++ second).filterMap identPart
  for w in (words.eraseDups.toArray.qsort (· < ·)) do
    IO.println w
