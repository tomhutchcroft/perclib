/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
Mathematical reference: the standard self-avoiding walk counts on `ℤ^d`
(Madras–Slade, *The Self-Avoiding Walk*, Section 1.2).
-/
module

public import PercLib.Models.ConnectiveConstant

/-!
# Rooted self-avoiding path counts on `ℤ^d`

`pathCount d x n` is the number of self-avoiding paths of length `n` in the nearest-neighbour
graph `zdGraph d` that start at `x`, with unrestricted endpoint: the cardinality of
`{p : Σ y, (zdGraph d).Path x y // p.2.1.length = n}`. Different paths to the same endpoint
are counted separately, and the length-zero path is counted.

This file packages the counts studied in `PercLib.Models.ConnectiveConstant` as a definition
and transfers the results proved there.

## Main definitions

* `PercLib.Models.Site.pathCount`: the rooted self-avoiding path count `c_n(x)`.

## Main results

* `pathCount_eq_pathCount_zero`: `c_n(x) = c_n(0)`.
* `pathCount_length_zero`: `c_0(x) = 1`.
* `pathCount_add_le`: `c_{n+m}(0) ≤ c_n(0) c_m(0)`.
* `pathCount_succ_le`: `c_{n+1}(0) ≤ 2d (2d - 1)^n`.
-/

@[expose] public section

open SimpleGraph

namespace PercLib.Models.Site

variable {d : ℕ}

/-- The rooted self-avoiding path count `c_n(x)` on `ℤ^d`: the number of paths (walks with
pairwise distinct vertices) of length `n` in `zdGraph d` starting at `x`, with unrestricted
endpoint. -/
noncomputable def pathCount (d : ℕ) (x : Fin d → ℤ) (n : ℕ) : ℕ :=
  Nat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = n}

/-- Unfolding `pathCount`. -/
theorem pathCount_eq_natCard (x : Fin d → ℤ) (n : ℕ) :
    pathCount d x n = Nat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = n} :=
  rfl

/-- `pathCount` as the cardinality of a finite type, in `ℕ∞`. -/
theorem pathCount_eq_enatCard (x : Fin d → ℤ) (n : ℕ) :
    (pathCount d x n : ℕ∞) = ENat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = n} := by
  have := finite_paths_length d n x
  rw [ENat.card_eq_coe_natCard, pathCount_eq_natCard]

/-- The count does not depend on the root. -/
theorem pathCount_eq_pathCount_zero (x : Fin d → ℤ) (n : ℕ) :
    pathCount d x n = pathCount d 0 n :=
  card_paths_eq_card_paths_zero n x

/-- Only the length-zero path has length zero. -/
@[simp]
theorem pathCount_length_zero (x : Fin d → ℤ) : pathCount d x 0 = 1 := by
  rw [pathCount_eq_pathCount_zero]
  exact card_paths_length_zero d

/-- Submultiplicativity: `c_{n+m} ≤ c_n c_m`. -/
theorem pathCount_add_le (x : Fin d → ℤ) (n m : ℕ) :
    pathCount d x (n + m) ≤ pathCount d x n * pathCount d x m := by
  simp only [pathCount_eq_pathCount_zero x]
  exact card_paths_add_le d n m

/-- In dimension `d ≥ 1` there is a path of every length. -/
theorem one_le_pathCount (hd : 1 ≤ d) (x : Fin d → ℤ) (n : ℕ) : 1 ≤ pathCount d x n := by
  rw [pathCount_eq_pathCount_zero]
  exact one_le_card_paths hd n

/-- The non-reversal bound `c_{n+1} ≤ 2d (2d - 1)^n`. -/
theorem pathCount_succ_le (x : Fin d → ℤ) (n : ℕ) :
    pathCount d x (n + 1) ≤ 2 * d * (2 * d - 1) ^ n := by
  rw [pathCount_eq_pathCount_zero]
  exact card_paths_succ_le d n

/-- In dimension zero there is no path of positive length. -/
@[simp]
theorem pathCount_dim_zero_succ (x : Fin 0 → ℤ) (n : ℕ) : pathCount 0 x (n + 1) = 0 := by
  rw [pathCount_eq_pathCount_zero]
  exact card_paths_dim_zero_succ n

end PercLib.Models.Site
