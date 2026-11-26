/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Radial long-range kernels on `ℤ^d` with the norm as a parameter, the cut-off kernels of Definition
I.1.5 of T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, for a general
profile, and the power-law profile of Definition I.1.3 as an instance; with the wiki targets PVA8,
MQNP, LF50 and 6YYS (article `cutoff-families`) for the power law.

`cutoffProfile` and the `if x = y then 0` kernel shape are adapted from the repository
`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/KernelGeometry.lean` (`cutoffProfile`, `radialKernel`, `cutoffKernel`,
`modelProfile`); licence Apache-2.0 as declared in that file's header; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Modified:
kernels are functions on `Sym2 (Fin d → ℤ)` with values in `ℝ≥0` (as `intensityProfile` requires),
the distance is a norm on `ℝ^d` (a `ModelNorm (Fin d → ℝ)`, coerced to a `Seminorm ℝ (Fin d → ℝ)`
for the kernels) evaluated at integer points, instead of an arbitrary function `V → V → ℝ`, and
the power-law profile carries a normalising constant. The API lemmas, targets and witnesses are new.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.ModelNorm.Defs
public import PercLib.Models.LongRange.PowerLaw
public import PercLib.Percolation.Bond.Intensity.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Long-range kernels and their cut-offs on `ℤ^d`

As in Definition I.1.3, the norm is a norm `N` on `ℝ^d`, restricted to `ℤ^d`: it is a `ModelNorm
(Fin d → ℝ)`, a seminorm (so absolutely homogeneous) that vanishes only at `0`. The kernels take a
`Seminorm ℝ (Fin d → ℝ)`, since they do not need definiteness, and receive a `ModelNorm` through
the coercion. An integer point `z : Fin d → ℤ` is
evaluated through the coercion `Int.cast ∘ z : Fin d → ℝ`. For a profile `K : ℝ → ℝ`, the radial
kernel is `J(x, y) = K (N (x - y))` for `x ≠ y` and `0` on the diagonal. Definition I.1.5 cuts it
off at scale `r` by `J_r(s) = ∫_s^r |K'| = K s - K r` for `s ≤ r` and `0` for `s > r`; for a
decreasing differentiable profile the two forms agree by the fundamental theorem of calculus, and
the closed form is taken as the definition (`cutoffProfile`), as in the source formalisation cited
in the header. Values are truncated at `0` (`Real.toNNReal`), which changes nothing for a
nonnegative profile. Probabilities are `intensityProfile J β` (no new profile definition).

Every norm on `ℝ^d` is comparable with the sup norm (`ModelNorm.exists_pos_mul_norm_le`,
`exists_le_mul_norm`, and their integer forms), so no comparability hypothesis is needed.
The sup norm is `ModelNorm.ofNorm (Fin d → ℝ)` (as a seminorm, `normSeminorm ℝ (Fin d → ℝ)`);
the Euclidean norm is the norm of `EuclideanSpace ℝ (Fin d)` transported by `WithLp.linearEquiv`
(`ModelNorm.comp`). The targets below are stated
for every norm.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {d : ℕ}

/-- The coercion `ℤ^d → ℝ^d` commutes with subtraction. -/
theorem intCast_comp_sub (x y : Fin d → ℤ) :
    (Int.cast ∘ (x - y) : Fin d → ℝ) = Int.cast ∘ x - Int.cast ∘ y := by
  ext i; simp

/-- The coercion `ℤ^d → ℝ^d` commutes with negation. -/
theorem intCast_comp_neg (z : Fin d → ℤ) :
    (Int.cast ∘ (-z) : Fin d → ℝ) = -(Int.cast ∘ z) := by
  ext i; simp

/-- The coercion `ℤ^d → ℝ^d` commutes with addition. -/
theorem intCast_comp_add (x y : Fin d → ℤ) :
    (Int.cast ∘ (x + y) : Fin d → ℝ) = Int.cast ∘ x + Int.cast ∘ y := by
  ext i; simp

/-- The **radial kernel** of a profile `K` for a norm `N` on `ℝ^d` (Definition I.1.3), on
`ℤ^d`: `J(x, y) = K (N (x - y))`, truncated at `0`, for `x ≠ y`, and `J(x, x) = 0`. -/
def radialKernel (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) : Sym2 (Fin d → ℤ) → ℝ≥0 :=
  Sym2.lift ⟨fun x y => if x = y then 0 else (K (N (Int.cast ∘ (x - y)))).toNNReal,
    fun x y => by simp only [eq_comm (a := x), intCast_comp_sub, map_sub_rev N]⟩

/-- The **cut-off profile** of Definition I.1.5 at scale `r`: `∫_s^r |K'| = K s - K r` for
`s ≤ r`, and `0` for `s > r`. -/
def cutoffProfile (K : ℝ → ℝ) (r s : ℝ) : ℝ :=
  if s ≤ r then K s - K r else 0

/-- The **cut-off kernel** `J_r` of Definition I.1.5: the radial kernel of the cut-off
profile. -/
def cutoffKernel (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (r : ℝ) :
    Sym2 (Fin d → ℤ) → ℝ≥0 :=
  radialKernel N (cutoffProfile K r)

/-- The **power-law profile** `s ↦ c s^(-a)` of Definition I.1.3 (with `δ ≡ 0`), with
exponent `a = d + α` and normalising constant `c`. The wiki articles use `c = 1/a`;
the source formalisation's `lrKernel` uses `c = 1` and the sup norm. -/
def powerLawProfile (c a s : ℝ) : ℝ :=
  c * s ^ (-a)

/-! ### Targets for the power law (wiki article `cutoff-families`) -/

/-- **PVA8**: for the power law with `a = d + α` and `c = 1/a`, at `s = N (x - y) > 0` and
`r > 0`, `J_r(x, y) = 1{s ≤ r} ∫_s^r t^(-a-1) dt = (s^(-a) - r^(-a))₊ / a`. -/
@[tag "PVA8"]
def CutoffPowerLawFormula : Prop :=
  ∀ (d : ℕ) (α : ℝ) (N : ModelNorm (Fin d → ℝ)) (r : ℝ) (x y : Fin d → ℤ),
    0 < α → 0 < r → x ≠ y →
    ((cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r s(x, y) : ℝ) =
        if N (Int.cast ∘ (x - y)) ≤ r then
          ∫ t in N (Int.cast ∘ (x - y))..r, t ^ (-((d : ℝ) + α) - 1) else 0) ∧
      (cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r s(x, y) : ℝ) =
        max (N (Int.cast ∘ (x - y)) ^ (-((d : ℝ) + α)) - r ^ (-((d : ℝ) + α))) 0 / (d + α)

/-- **MQNP**: for the power law, `r ↦ J_r(e)` is increasing and tends to `J(e)`, and so the
edge probabilities `q_{β,r}(e) = 1 - exp(-β J_r(e))` increase in `r`. -/
@[tag "MQNP"]
def CutoffPowerLawMonotone : Prop :=
  ∀ (d : ℕ) (α : ℝ) (N : ModelNorm (Fin d → ℝ)) (β : ℝ≥0) (e : Sym2 (Fin d → ℤ)),
    0 < α →
    Monotone (fun r => cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r e) ∧
      Tendsto (fun r => cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r e) atTop
        (𝓝 (radialKernel N (powerLawProfile (1 / (d + α)) (d + α)) e)) ∧
      Monotone (fun r => ((PercLib.Percolation.Bond.intensityProfile
        (cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r) β e : unitInterval) : ℝ))

/-- **LF50**: for the power law, an edge inside the cut-off loses exactly `r^(-a)/a`:
`J(x, y) - J_r(x, y) = r^(-a)/a` when `0 < s = N (x - y) ≤ r`. -/
@[tag "LF50"]
def CutoffPowerLawDeficit : Prop :=
  ∀ (d : ℕ) (α : ℝ) (N : ModelNorm (Fin d → ℝ)) (r : ℝ) (x y : Fin d → ℤ),
    0 < α → x ≠ y → N (Int.cast ∘ (x - y)) ≤ r →
    (radialKernel N (powerLawProfile (1 / (d + α)) (d + α)) s(x, y) : ℝ) -
        cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r s(x, y) =
      r ^ (-((d : ℝ) + α)) / (d + α)

/-- **6YYS**: for the power law and `x ≠ y`, away from the corner `r = s = N (x - y)`,
`d/dr J_r(x, y) = 1{s < r} r^(-d-α-1)` and
`d/dr q_{β,r}(x, y) = β exp(-β J_r(x, y)) 1{s < r} r^(-d-α-1)`. -/
@[tag "6YYS"]
def CutoffPowerLawDerivative : Prop :=
  ∀ (d : ℕ) (α : ℝ) (N : ModelNorm (Fin d → ℝ)) (β : ℝ≥0) (r : ℝ) (x y : Fin d → ℤ),
    0 < α → x ≠ y → r ≠ N (Int.cast ∘ (x - y)) →
    HasDerivAt (fun r => (cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r s(x, y) : ℝ))
        (if N (Int.cast ∘ (x - y)) < r then r ^ (-((d : ℝ) + α) - 1) else 0) r ∧
      HasDerivAt (fun r => ((PercLib.Percolation.Bond.intensityProfile
          (cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r) β s(x, y) :
            unitInterval) : ℝ))
        (β * Real.exp (-(β : ℝ) *
            (cutoffKernel N (powerLawProfile (1 / (d + α)) (d + α)) r s(x, y) : ℝ)) *
          if N (Int.cast ∘ (x - y)) < r then r ^ (-((d : ℝ) + α) - 1) else 0) r

/-! ### API -/

variable {N : Seminorm ℝ (Fin d → ℝ)} {K : ℝ → ℝ} {r s : ℝ}

theorem radialKernel_mk (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (x y : Fin d → ℤ) :
    radialKernel N K s(x, y) =
      if x = y then 0 else (K (N (Int.cast ∘ (x - y)))).toNNReal := rfl

@[simp] theorem radialKernel_diag (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (x : Fin d → ℤ) :
    radialKernel N K s(x, x) = 0 := by
  simp [radialKernel_mk]

theorem radialKernel_of_ne {x y : Fin d → ℤ} (h : x ≠ y) :
    radialKernel N K s(x, y) = (K (N (Int.cast ∘ (x - y)))).toNNReal := by
  simp [radialKernel_mk, h]

theorem coe_radialKernel_of_ne {x y : Fin d → ℤ} (h : x ≠ y)
    (hK : 0 ≤ K (N (Int.cast ∘ (x - y)))) :
    (radialKernel N K s(x, y) : ℝ) = K (N (Int.cast ∘ (x - y))) := by
  rw [radialKernel_of_ne h, Real.coe_toNNReal _ hK]

/-- The coercion `ℤ^d → ℝ^d` is injective. -/
theorem intCast_comp_eq_zero {z : Fin d → ℤ} (h : (Int.cast ∘ z : Fin d → ℝ) = 0) : z = 0 := by
  ext i; simpa using congrFun h i

/-- For a norm, the norm of a nonzero integer point is positive. -/
theorem _root_.PercLib.Analysis.ModelNorm.intCast_comp_pos (N : ModelNorm (Fin d → ℝ))
    {z : Fin d → ℤ} (hz : z ≠ 0) : 0 < N (Int.cast ∘ z) :=
  N.pos_iff_ne_zero.2 fun h0 => hz (intCast_comp_eq_zero h0)

/-- Off the diagonal the norm of the difference is positive. -/
theorem _root_.PercLib.Analysis.ModelNorm.intCast_comp_sub_pos (N : ModelNorm (Fin d → ℝ))
    {x y : Fin d → ℤ} (h : x ≠ y) : 0 < N (Int.cast ∘ (x - y)) :=
  N.intCast_comp_pos (sub_ne_zero.2 h)

/-! ### Comparability with the sup norm (equivalence of norms on `ℝ^d`) -/

/-- Every seminorm on `ℝ^d` is bounded by a multiple of the sup norm. -/
theorem exists_le_mul_norm (N : Seminorm ℝ (Fin d → ℝ)) :
    ∃ C, 0 < C ∧ ∀ v : Fin d → ℝ, N v ≤ C * ‖v‖ := by
  refine ⟨∑ i, N (Pi.single i 1) + 1, by positivity, fun v => ?_⟩
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  calc N v = N (∑ i, v i • Pi.single i (1 : ℝ)) := by rw [← hv]
    _ ≤ ∑ i, N (v i • Pi.single i (1 : ℝ)) := Finset.le_sum_of_subadditive N (map_zero N).le
        (map_add_le_add N) _ _
    _ = ∑ i, ‖v i‖ * N (Pi.single i 1) := by simp only [map_smul_eq_mul]
    _ ≤ ∑ i, ‖v‖ * N (Pi.single i 1) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (apply_nonneg N _)
    _ ≤ (∑ i, N (Pi.single i 1) + 1) * ‖v‖ := by
        rw [← Finset.mul_sum, mul_comm]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)

/-- Every seminorm on `ℝ^d` is continuous. -/
theorem continuous_seminorm (N : Seminorm ℝ (Fin d → ℝ)) : Continuous N := by
  obtain ⟨C, hC, hNC⟩ := exists_le_mul_norm N
  refine Seminorm.continuous_of_le
    (q := C.toNNReal • normSeminorm ℝ (Fin d → ℝ)) ?_ fun v => ?_
  · rw [FunLike.coe_smul, coe_normSeminorm]
    exact continuous_norm.const_smul _
  · simpa [coe_normSeminorm, NNReal.smul_def, Real.coe_toNNReal _ hC.le] using hNC v

/-- The sup norm of an integer point equals the sup norm of its image in `ℝ^d`. -/
theorem norm_intCast_comp (z : Fin d → ℤ) : ‖(Int.cast ∘ z : Fin d → ℝ)‖ = ‖z‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [Function.comp_apply, Int.norm_cast_real]; exact norm_le_pi_norm z i
  · rw [← Int.norm_cast_real]; exact norm_le_pi_norm (Int.cast ∘ z : Fin d → ℝ) i

/-- **Comparability on `ℤ^d`**, lower bound: `κ ‖z‖ ≤ N z` for a norm `N` on `ℝ^d`. -/
theorem exists_pos_mul_norm_le_intCast (N : ModelNorm (Fin d → ℝ)) :
    ∃ κ, 0 < κ ∧ ∀ z : Fin d → ℤ, κ * ‖z‖ ≤ N (Int.cast ∘ z) := by
  obtain ⟨κ, hκ, h⟩ := N.exists_pos_mul_norm_le
  exact ⟨κ, hκ, fun z => norm_intCast_comp z ▸ h _⟩

/-- **Comparability on `ℤ^d`**, upper bound: `N z ≤ C ‖z‖`. -/
theorem exists_le_mul_norm_intCast (N : Seminorm ℝ (Fin d → ℝ)) :
    ∃ C, 0 < C ∧ ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≤ C * ‖z‖ := by
  obtain ⟨C, hC, h⟩ := exists_le_mul_norm N
  exact ⟨C, hC, fun z => norm_intCast_comp z ▸ h _⟩

/-! ### Cut-off profile and kernel -/

theorem cutoffKernel_def (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (r : ℝ) :
    cutoffKernel N K r = radialKernel N (cutoffProfile K r) := rfl

theorem cutoffProfile_of_le (h : s ≤ r) : cutoffProfile K r s = K s - K r := ite_eq_left h

theorem cutoffProfile_of_lt (h : r < s) : cutoffProfile K r s = 0 := ite_eq_right (not_le.2 h)

/-- Monotonicity in the scale: for a profile decreasing on `(0, ∞)`, `r ↦ J_r(s)` is
increasing at every `s > 0`. -/
theorem monotone_cutoffProfile (hK : AntitoneOn K (Ioi 0)) (hs : 0 < s) :
    Monotone fun r => cutoffProfile K r s := by
  intro r r' hrr'
  dsimp only
  by_cases h : s ≤ r
  · rw [cutoffProfile_of_le h, cutoffProfile_of_le (h.trans hrr')]
    linarith [hK (hs.trans_le h) (hs.trans_le (h.trans hrr')) hrr']
  · rw [cutoffProfile_of_lt (not_le.1 h)]
    by_cases h' : s ≤ r'
    · rw [cutoffProfile_of_le h']
      linarith [hK hs (hs.trans_le h') h']
    · rw [cutoffProfile_of_lt (not_le.1 h')]

/-- Monotonicity of the cut-off kernel in the scale. -/
theorem monotone_cutoffKernel {N : ModelNorm (Fin d → ℝ)} (hK : AntitoneOn K (Ioi 0))
    (e : Sym2 (Fin d → ℤ)) : Monotone fun r => cutoffKernel N K r e := by
  induction e using Sym2.ind with
  | _ x y =>
    intro r r' hrr'
    by_cases h : x = y
    · simp [cutoffKernel_def, h]
    · simp only [cutoffKernel_def, radialKernel_of_ne h]
      exact Real.toNNReal_le_toNNReal (monotone_cutoffProfile hK (N.intCast_comp_sub_pos h) hrr')

/-- Cutting off lowers the kernel: `J_r ≤ J` for a profile nonnegative on `(0, ∞)`. -/
theorem cutoffKernel_le_radialKernel {N : ModelNorm (Fin d → ℝ)} (hK : ∀ t, 0 < t → 0 ≤ K t)
    (hr : 0 < r) (e : Sym2 (Fin d → ℤ)) : cutoffKernel N K r e ≤ radialKernel N K e := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · simp [cutoffKernel_def, h]
    · simp only [cutoffKernel_def, radialKernel_of_ne h, ModelNorm.coe_toSeminorm]
      refine Real.toNNReal_le_toNNReal ?_
      by_cases hs : N (Int.cast ∘ (x - y)) ≤ r
      · rw [cutoffProfile_of_le hs]; linarith [hK r hr]
      · rw [cutoffProfile_of_lt (not_le.1 hs)]; exact hK _ (N.intCast_comp_sub_pos h)

theorem powerLawProfile_pos {c a : ℝ} (hc : 0 < c) (hs : 0 < s) : 0 < powerLawProfile c a s :=
  mul_pos hc (Real.rpow_pos_of_pos hs _)

theorem antitoneOn_powerLawProfile {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) :
    AntitoneOn (powerLawProfile c a) (Ioi 0) := fun _ hs _ _ hst =>
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs hst (by linarith)) hc

/-! ### Witnesses: the sup norm and the Euclidean norm -/

/-- The sup norm on `ℝ^d` restricts to the sup norm on `ℤ^d`. -/
theorem normSeminorm_intCast (z : Fin d → ℤ) :
    normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) = ‖z‖ := by
  rw [coe_normSeminorm, norm_intCast_comp]

/-- The sup norm of a nonzero integer vector is at least `1`. -/
theorem one_le_norm_of_ne_zero {z : Fin d → ℤ} (hz : z ≠ 0) : 1 ≤ ‖z‖ := by
  rw [← natCast_floor_norm]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h => hz ((floor_norm_eq_zero_iff z).1 h)

/-- Non-vacuity: at `d = 1`, `α = 1` (sup norm, `c = 1`), the kernel is positive off the
diagonal. -/
theorem radialKernel_pos_example {x y : Fin 1 → ℤ} (h : x ≠ y) :
    0 < radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2) s(x, y) := by
  rw [radialKernel_of_ne h, Real.toNNReal_pos]
  exact powerLawProfile_pos one_pos ((ModelNorm.ofNorm (Fin 1 → ℝ)).intCast_comp_sub_pos h)

/-- Non-vacuity: at `d = 1`, `α = 1` (sup norm, `c = 1`), the kernel is summable along rows. -/
theorem summable_radialKernel_example (x : Fin 1 → ℤ) :
    Summable fun y => (radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile 1 2)
      s(x, y) : ℝ) := by
  have hs := ((summable_powerLaw_iff (d := 1) le_rfl 1).2 one_pos).comp_injective
    (sub_right_injective (b := x))
  refine hs.congr fun y => ?_
  by_cases h : x = y
  · simp [h]
  · have hne : x - y ≠ 0 := sub_ne_zero.2 h
    rw [coe_radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ)) h
      (powerLawProfile_pos one_pos ((ModelNorm.ofNorm (Fin 1 → ℝ)).intCast_comp_sub_pos h)).le]
    simp only [Function.comp_apply, hne, ite_false, powerLawProfile, one_mul,
      normSeminorm_intCast]
    norm_num

/-- Non-vacuity, Euclidean norm: at `d = 1`, `α = 1` (`c = 1`), the kernel is positive off the
diagonal. -/
theorem radialKernel_pos_euclidean_example {x y : Fin 1 → ℤ} (h : x ≠ y) :
    0 < radialKernel ((normSeminorm ℝ (EuclideanSpace ℝ (Fin 1))).comp
      (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm.toLinearMap) (powerLawProfile 1 2) s(x, y) := by
  rw [radialKernel_of_ne h, Real.toNNReal_pos]
  exact powerLawProfile_pos one_pos (((ModelNorm.ofNorm (EuclideanSpace ℝ (Fin 1))).comp
    (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm).intCast_comp_sub_pos h)

/-- Non-vacuity: the cut-off of `s ↦ s^(-2)` at `r = 1` vanishes for `s > 1` and is positive
for `0 < s < 1`. -/
theorem cutoffProfile_example :
    (∀ s, 1 < s → cutoffProfile (powerLawProfile 1 2) 1 s = 0) ∧
      ∀ s, 0 < s → s < 1 → 0 < cutoffProfile (powerLawProfile 1 2) 1 s := by
  refine ⟨fun s hs => cutoffProfile_of_lt hs, fun s hs hs1 => ?_⟩
  rw [cutoffProfile_of_le hs1.le, sub_pos]
  simp only [powerLawProfile, one_mul, Real.one_rpow]
  exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hs hs1 (by norm_num)

/-- Non-vacuity: with the sup norm, `J_r = 0` for `r < 1`, since no pair is at distance below
one. -/
theorem cutoffKernel_eq_zero_of_lt_one {K : ℝ → ℝ} (hr : r < 1) (e : Sym2 (Fin d → ℤ)) :
    cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) K r e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases h : x = y
    · simp [cutoffKernel_def, h]
    · rw [cutoffKernel_def, radialKernel_of_ne h, cutoffProfile_of_lt, Real.toNNReal_zero]
      rw [normSeminorm_intCast]
      exact hr.trans_le (one_le_norm_of_ne_zero (sub_ne_zero.2 h))

/-- Non-vacuity: `J_r ≤ J` at the explicit pair `{0, 1}` of `ℤ`, with `a = 2`, `c = 1/2`,
`r = 2`. -/
example : cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile (1 / 2) 2) 2
      s(0, fun _ => 1) ≤
    radialKernel (normSeminorm ℝ (Fin 1 → ℝ)) (powerLawProfile (1 / 2) 2) s(0, fun _ => 1) :=
  cutoffKernel_le_radialKernel (N := ModelNorm.ofNorm (Fin 1 → ℝ))
    (fun _ ht => (powerLawProfile_pos (by norm_num) ht).le) two_pos _

end PercLib.Models.LongRange
