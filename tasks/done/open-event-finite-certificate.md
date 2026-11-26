---
id: open-event-finite-certificate
title: An arbitrary certificate for an open event contains a finite one
difficulty: medium
kind: interface
labels: []
---

# An arbitrary certificate for an open event contains a finite one

## Goal
Prove wiki assertion **1NUW** (article `countable-reimer`) and tag it. On the product space
`{0,1}^E`, an infinite certificate for an open event can be shrunk to a finite one by
compactness, so for open events disjoint occurrence with arbitrary certificates coincides with
disjoint occurrence with finite certificates (the library's `disjointOccurrence`).

## Target
Let `Ω = E → Bool` with the product topology and, for `K ⊆ E`, write
`[ω]_K = {η | ∀ i ∈ K, η i = ω i}`.
1. If `U ⊆ Ω` is open and `[ω]_K ⊆ U`, there is a finite `F ⊆ K` with `[ω]_F ⊆ U`.
2. For open `U, V`, `U □_∞ V = U □_f V`, where `□_∞` asks for disjoint certificates
   `K, L ⊆ E` with `[ω]_K ⊆ U`, `[ω]_L ⊆ V`, and `□_f` asks the same with `K, L` finite.

The article takes `E` countable; the compactness proof works for any index type (Tychonoff), so
state the area lemmas for arbitrary `E` if that is free. Write `[ω]_K`, `□_∞` and `□_f` inline
(no new `def`). Sketch:
```lean
theorem exists_finset_cylinder_subset_of_isOpen {E : Type*} {U : Set (E → Bool)}
    (hU : IsOpen U) (ω : E → Bool) {K : Set E}
    (hK : {η | ∀ i ∈ K, η i = ω i} ⊆ U) :
    ∃ F : Finset E, (F : Set E) ⊆ K ∧ {η | ∀ i ∈ F, η i = ω i} ⊆ U
```
Mathlib: `isCompact_univ` for `E → Bool`,
`IsCompact.elim_finite_subcover` or
`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`. Optional, if cheap: a
corollary in the library's convention (`Config = Set E`, `ForcesOn`, `disjointOccurrence` in
`PercLib/Probability/DisjointOccurrence.lean`) through `Set E ≃ (E → Bool)`; do not put a
topology instance on `Set E`.

Tagged statement: the conjunction of 1 and 2.

## Owned files
- New `PercLib/Probability/OpenCertificates.lean` (area lemmas).
- New `PercLib/Probability/Tags/OpenCertificates.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/DisjointOccurrence.lean`, `PercLib/Probability/CountableBK.lean`, mathlib;
wiki assertion 1NUW (its proof uses no other assertion).

## Stop condition
1NUW tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
