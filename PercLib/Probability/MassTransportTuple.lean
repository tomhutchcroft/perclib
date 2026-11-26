/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc, files `PercLib/CriticalLRP/Analysis/MassTransport.lean`
and `PercLib/CriticalLRP/MomentExpansion.lean`, contributed by `yujinhkim`. Licence: Apache-2.0, as
declared in those files' headers and in `third_party/critical-lrp/NOTICE.md` of that commit
(upstream origin `yujinhkim/Critical-Long-range-percolation` at
3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf, not independently verified). Changes: renamed into
`PercLib.Probability`; `tsum_mass_transport` renamed `tsum_mass_transport_tuple`; the unused
`[Countable G]` dropped; the two-point form is derived from `tsum_mass_transport_add`; focused
imports; `autoImplicit` off.
-/
module

public import PercLib.Probability.MassTransport
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Deterministic ingredients of Lemma I.4.1

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1,
equations (I.4.2)–(I.4.3), p. 34.

* `tsum_mass_transport_tuple` (I.4.3): for `F : (Fin k → G) → ℝ≥0∞` invariant under
  diagonal translation, the sum over tuples with `i`-th coordinate `0` does not depend
  on `i`.
* `tsum_mass_transport₂` (I.4.2): the two-point form, derived from
  `tsum_mass_transport_add`.
* `sum_choose_mul_pow_eq_pow_sub`, `mul_pow_sub_pow_eq_sum_choose`: the binomial
  expansion `a((a+b)^p − a^p) = ∑_{ℓ<p} C(p,ℓ) a^{ℓ+1} b^{p−ℓ}`.
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace PercLib.Probability

variable {G : Type*} [AddCommGroup G]

/-- **Mass-transport principle, `k`-fold form** (paper (I.4.3)). If
`F : (Fin k → G) → ℝ≥0∞` is invariant under simultaneous translation, then the sum of `F`
over the tuples with `i`-th coordinate `0` does not depend on `i`. -/
@[tag "SCGY"]
theorem tsum_mass_transport_tuple {k : ℕ} (F : (Fin k → G) → ℝ≥0∞)
    (hF : ∀ (v : Fin k → G) (t : G), F (fun i => v i + t) = F v) (i j : Fin k) :
    (∑' v : {v : Fin k → G // v i = 0}, F v.1)
      = ∑' v : {v : Fin k → G // v j = 0}, F v.1 := by
  let e : {v : Fin k → G // v i = 0} ≃ {v : Fin k → G // v j = 0} :=
    { toFun := fun v => ⟨fun m => v.1 m - v.1 j, by simp⟩
      invFun := fun w => ⟨fun m => w.1 m - w.1 i, by simp⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext m
        simp [v.2]
      right_inv := by
        intro w
        apply Subtype.ext
        funext m
        simp [w.2] }
  have hstep : ∀ v : {v : Fin k → G // v i = 0}, F (e v).1 = F v.1 := by
    intro v
    have hve : (e v).1 = fun m => v.1 m + (-v.1 j) := by
      funext m
      exact sub_eq_add_neg _ _
    rw [hve, hF]
  calc (∑' v : {v : Fin k → G // v i = 0}, F v.1)
      = ∑' v : {v : Fin k → G // v i = 0}, F (e v).1 := (tsum_congr hstep).symm
    _ = ∑' v : {v : Fin k → G // v j = 0}, F v.1 := Equiv.tsum_eq e (fun w => F w.1)

/-- **Mass-transport principle, two-point form** (paper (I.4.2)), in the source's
translation convention; it is `tsum_mass_transport_add`. -/
theorem tsum_mass_transport₂ (F : G → G → ℝ≥0∞)
    (hF : ∀ (x y : G) (t : G), F (x + t) (y + t) = F x y) :
    (∑' x : G, F 0 x) = ∑' x : G, F x 0 :=
  tsum_mass_transport_add F fun g x y => by rw [add_comm g x, add_comm g y, hF]

/-- `∑_{ℓ<p} C(p,ℓ) a^ℓ b^{p−ℓ} = (a+b)^p − a^p`. -/
theorem sum_choose_mul_pow_eq_pow_sub (a b : ℝ) (p : ℕ) :
    ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ ℓ * b ^ (p - ℓ) = (a + b) ^ p - a ^ p := by
  have h := add_pow a b p
  rw [Finset.sum_range_succ] at h
  have hlast : a ^ p * b ^ (p - p) * (p.choose p : ℝ) = a ^ p := by simp
  rw [hlast] at h
  have h2 : ∑ ℓ ∈ range p, a ^ ℓ * b ^ (p - ℓ) * (p.choose ℓ : ℝ)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ ℓ * b ^ (p - ℓ) :=
    sum_congr rfl fun ℓ _ => by ring
  rw [h2] at h
  linarith

/-- **The binomial identity of Lemma I.4.1**: with `a = |K|` and `b = |K_y|`,
`a ((a + b)^p − a^p) = ∑_{ℓ=0}^{p−1} C(p,ℓ) a^{ℓ+1} b^{p−ℓ}`. -/
theorem mul_pow_sub_pow_eq_sum_choose (a b : ℝ) (p : ℕ) :
    a * ((a + b) ^ p - a ^ p)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ (ℓ + 1) * b ^ (p - ℓ) := by
  rw [← sum_choose_mul_pow_eq_pow_sub a b p, Finset.mul_sum]
  exact sum_congr rfl fun ℓ _ => by ring

/-- Non-vacuity witness for `tsum_mass_transport_tuple`: `G = ℤ`, `k = 2`, `F v = 1` if
`v 1 − v 0 = 1` and `0` otherwise; both sides equal `1`. -/
example :
    (∑' v : {v : Fin 2 → ℤ // v 0 = 0}, (if v.1 1 - v.1 0 = 1 then (1 : ℝ≥0∞) else 0))
      = ∑' v : {v : Fin 2 → ℤ // v 1 = 0}, (if v.1 1 - v.1 0 = 1 then (1 : ℝ≥0∞) else 0)
    ∧ (∑' v : {v : Fin 2 → ℤ // v 0 = 0}, (if v.1 1 - v.1 0 = 1 then (1 : ℝ≥0∞) else 0))
      = 1 := by
  refine ⟨tsum_mass_transport_tuple (fun v : Fin 2 → ℤ => if v 1 - v 0 = 1 then 1 else 0)
    (fun v t => by simp) 0 1, ?_⟩
  let v₀ : {v : Fin 2 → ℤ // v 0 = 0} := ⟨![0, 1], rfl⟩
  rw [tsum_eq_single v₀]
  · simp [v₀]
  · intro w hw
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    apply hw
    apply Subtype.ext
    funext m
    fin_cases m
    · simpa [v₀] using w.2
    · have := w.2
      simp only [v₀]
      simp_all

end PercLib.Probability
