/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the rooted self-avoiding path counts on `ℤ^d`.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.PathCount

/-!
# Rooted self-avoiding path counts: correspondence

Wiki correspondence for the definition of `c_n(x)`.

## Main results

* `pathCount_eq_natCard_and_length_zero`
-/

@[expose] public section

open SimpleGraph

namespace PercLib.Models.Site

/-- `c_n(x)` counts the paths of length `n` in `ℤ^d` from `x`, a path being a walk whose
vertices are pairwise distinct; the endpoint is unrestricted (paths are pairs of an endpoint
and a path to it), the set counted is finite, and the length-zero path is counted, so
`c_0(x) = 1`. -/
@[tag "RSRP"]
theorem pathCount_eq_natCard_and_length_zero :
    (∀ (d : ℕ) (x : Fin d → ℤ) (n : ℕ),
      pathCount d x n = Nat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = n}) ∧
    (∀ (d : ℕ) (x y : Fin d → ℤ) (w : (zdGraph d).Walk x y), w.IsPath ↔ w.support.Nodup) ∧
    (∀ (d : ℕ) (x : Fin d → ℤ) (n : ℕ),
      Finite {p : Σ y, (zdGraph d).Path x y // p.2.1.length = n}) ∧
    (∀ (d : ℕ) (x : Fin d → ℤ), pathCount d x 0 = 1) :=
  ⟨fun _ => pathCount_eq_natCard, fun _ _ _ w => Walk.isPath_def w,
    fun d x n => finite_paths_length d n x, fun _ => pathCount_length_zero⟩

end PercLib.Models.Site
