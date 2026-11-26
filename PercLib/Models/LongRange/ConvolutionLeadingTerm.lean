/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Transfer of a spatial power-law leading term through a summable kernel on `ℤ^d`. New for this
project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is
copied. Mathematical reference: Hara, *Decay of correlations in nearest-neighbour self-avoiding
walk, percolation, lattice trees and animals*, Ann. Probab. 36 (2008), Appendix B.
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import PercLib.Models.LongRange.LatticeConvolution

/-!
# A summable kernel transfers a spatial power-law leading term

Write `|x| = √(∑ᵢ xᵢ²)` and `⟨x⟩ = max 1 |x|` on `ℤ^d`, and `(f ⋆ g)(x) = ∑ y, f(x - y) g(y)`.
Let `0 < a < d`. If `f(x) = A |x|^(-a) + o(|x|^(-a))` as `|x| → ∞`, `∑ |g| < ∞` and
`|g(y)| ≤ K ⟨y⟩^(-d)`, then `f ⋆ g` converges absolutely and
`(f ⋆ g)(x) = A (∑ g) |x|^(-a) + o(|x|^(-a))`.

The proof splits the sum at `|y| < ε|x|` and `|x - y| < ε|x|`; the first region carries the
leading term, the second is controlled by the lattice ball sum of `⟨z⟩^(-a)`, and the rest by
the tail of `∑ |g|`.

## Main results

* `exists_forall_le_of_eventually_comap`: an eventual property along `comap e atTop` holds on a
  superlevel set of `e`.
* `tendsto_tsum_ite_le_abs`: tails `∑_{e y ≥ t} |g y|` of an absolutely summable family tend
  to zero.
* `finite_setOf_sqrt_sum_sq_lt`: Euclidean balls in `ℤ^d` are finite.
* `exists_abs_le_mul_max_sqrt_sum_sq_rpow`: a function that is `O(|x|^(-a))` at infinity is
  bounded by `M ⟨x⟩^(-a)` everywhere.
* `tsum_ite_sqrt_sum_sq_lt_rpow_le`: `∑_{|z| < t} ⟨z⟩^(-a) ≤ C t^(d-a)` for `t ≥ 1`.
* `summable_abs_mul_and_isLittleO_tsum_mul_sub`: the transfer of the leading term, with its
  two parts `summable_abs_mul_of_isLittleO` and `isLittleO_tsum_mul_sub`.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis

/-! ### Filters and tails -/

/-- An eventual property along `comap e atTop` holds wherever `e` exceeds some `r ≥ r₀`. -/
theorem exists_forall_le_of_eventually_comap {α : Type*} {e : α → ℝ} {P : α → Prop}
    (h : ∀ᶠ x in comap e atTop, P x) (r₀ : ℝ) : ∃ r ≥ r₀, ∀ x, r ≤ e x → P x := by
  obtain ⟨r, hr⟩ := eventually_atTop.1 (eventually_comap.1 h)
  exact ⟨max r r₀, le_max_right _ _, fun x hx => hr _ (le_trans (le_max_left _ _) hx) x rfl⟩

/-- The tails `∑_{e y ≥ t} |g y|` of an absolutely summable family tend to zero. -/
theorem tendsto_tsum_ite_le_abs {α : Type*} {e : α → ℝ} {g : α → ℝ}
    (hg : Summable fun y => |g y|) :
    Tendsto (fun t => ∑' y, if t ≤ e y then |g y| else 0) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun t y => if t ≤ e y then |g y| else 0) (g := fun _ => (0 : ℝ)) hg
    (fun y => tendsto_const_nhds.congr'
      ((eventually_gt_atTop (e y)).mono fun t ht => (ite_eq_right (not_le.2 ht)).symm))
    (Eventually.of_forall fun t y => by split_ifs <;> simp)
  simpa using h

/-! ### Euclidean length on `ℤ^d` -/

variable {d : ℕ}

/-- Euclidean length on `ℤ^d` is subadditive. -/
theorem sqrt_sum_sq_add_le (y z : Fin d → ℤ) :
    √(∑ i, (((y + z) i : ℤ) : ℝ) ^ 2) ≤ √(∑ i, ((y i : ℝ)) ^ 2) + √(∑ i, ((z i : ℝ)) ^ 2) := by
  rw [euclid_eq_norm, euclid_eq_norm, euclid_eq_norm]
  have hfun : (fun i => (((y + z) i : ℤ) : ℝ)) = (fun i => (y i : ℝ)) + fun i => (z i : ℝ) := by
    funext i
    simp
  rw [hfun, WithLp.toLp_add]
  exact norm_add_le _ _

/-- `|x| ≤ |x - y| + |y|` on `ℤ^d`. -/
theorem sqrt_sum_sq_le_sub_add (x y : Fin d → ℤ) :
    √(∑ i, ((x i : ℝ)) ^ 2) ≤ √(∑ i, (((x - y) i : ℤ) : ℝ) ^ 2) + √(∑ i, ((y i : ℝ)) ^ 2) := by
  have h := sqrt_sum_sq_add_le (x - y) y
  rwa [sub_add_cancel] at h

/-- `|x - y| ≤ |x| + |y|` on `ℤ^d`. -/
theorem sqrt_sum_sq_sub_le (x y : Fin d → ℤ) :
    √(∑ i, (((x - y) i : ℤ) : ℝ) ^ 2) ≤ √(∑ i, ((x i : ℝ)) ^ 2) + √(∑ i, ((y i : ℝ)) ^ 2) := by
  have h := sqrt_sum_sq_add_le x (-y)
  rw [← sub_eq_add_neg] at h
  simpa using h

/-- Euclidean balls in `ℤ^d` are finite. -/
theorem finite_setOf_sqrt_sum_sq_lt (r : ℝ) :
    {x : Fin d → ℤ | √(∑ i, ((x i : ℝ)) ^ 2) < r}.Finite := by
  have h := tsum_ite_max_euclid_le_le (d := d) (max 1 r)
  rw [tsum_ite_const_eq, mul_one] at h
  have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hfin : {y : Fin d → ℤ | max 1 √(∑ i, ((y i : ℝ)) ^ 2) ≤ max 1 r}.Finite :=
    Set.encard_ne_top_iff.1 (by simpa using hne)
  refine hfin.subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact max_le_max le_rfl hx.le

/-- A function that is `O(|x|^(-a))` as `|x| → ∞` is bounded by `M ⟨x⟩^(-a)` everywhere. -/
theorem exists_abs_le_mul_max_sqrt_sum_sq_rpow {a : ℝ} (ha : 0 ≤ a) {f : (Fin d → ℤ) → ℝ}
    (hf : f =O[comap (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) atTop]
      fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) :
    ∃ M, 0 ≤ M ∧ ∀ x, |f x| ≤ M * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a) := by
  obtain ⟨c, hc⟩ := hf.bound
  obtain ⟨r, hr1, hr⟩ := exists_forall_le_of_eventually_comap hc 1
  obtain ⟨M₀, hM₀⟩ := ((finite_setOf_sqrt_sum_sq_lt (d := d) r).image fun x => |f x|).bddAbove
  refine ⟨max c 0 + max M₀ 0 * r ^ a, by positivity, fun x => ?_⟩
  set e := √(∑ i, ((x i : ℝ)) ^ 2)
  have hb : 0 ≤ (max 1 e) ^ (-a) := Real.rpow_nonneg (by positivity) _
  by_cases hx : r ≤ e
  · have h := hr x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      at h
    rw [max_eq_right (hr1.trans hx)]
    have hb' : 0 ≤ e ^ (-a) := Real.rpow_nonneg (by positivity) _
    nlinarith [le_max_left c 0, mul_nonneg (mul_nonneg (le_max_right M₀ 0)
      (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r) a)) hb']
  · have hfx : |f x| ≤ M₀ := hM₀ ⟨x, not_le.1 hx, rfl⟩
    have hr0 : 0 < r := by linarith
    have h1 : r ^ (-a) ≤ (max 1 e) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (max_le hr1 (not_le.1 hx).le) (by linarith)
    have h2 : r ^ a * r ^ (-a) = 1 := by
      rw [← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero]
    have h3 : 1 ≤ r ^ a * (max 1 e) ^ (-a) :=
      calc (1 : ℝ) = r ^ a * r ^ (-a) := h2.symm
        _ ≤ r ^ a * (max 1 e) ^ (-a) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hr0.le a)
    have h4 : M₀ ≤ max M₀ 0 * r ^ a * (max 1 e) ^ (-a) := by
      rw [mul_assoc]
      nlinarith [le_max_left M₀ 0, le_max_right M₀ 0]
    nlinarith [mul_nonneg (le_max_right c 0) hb]

/-- **Ball sums in reals.** For `0 ≤ a < d` and `t ≥ 1`,
`∑_{|z| < t} ⟨z⟩^(-a) ≤ 3^d 2^a / (1 - 2^(a-d)) t^(d-a)`, the series being summable. -/
theorem tsum_ite_sqrt_sum_sq_lt_rpow_le {a : ℝ} (ha : 0 ≤ a) (had : a < d) {t : ℝ}
    (ht : 1 ≤ t) :
    Summable (fun z : Fin d → ℤ =>
        if √(∑ i, ((z i : ℝ)) ^ 2) < t then (max 1 √(∑ i, ((z i : ℝ)) ^ 2)) ^ (-a) else 0) ∧
      ∑' z : Fin d → ℤ,
          (if √(∑ i, ((z i : ℝ)) ^ 2) < t then (max 1 √(∑ i, ((z i : ℝ)) ^ 2)) ^ (-a) else 0) ≤
        3 ^ d * 2 ^ a / (1 - 2 ^ (a - d)) * t ^ ((d : ℝ) - a) := by
  have hE := tsum_ite_le_rpow_le_of_count
    (w := fun z : Fin d → ℤ => max 1 √(∑ i, ((z i : ℝ)) ^ 2)) (fun _ => le_max_left _ _)
    (fun t _ => tsum_ite_max_euclid_le_le t) (by positivity) ha had (R := t) (by linarith)
  set φ : (Fin d → ℤ) → ℝ := fun z =>
    if √(∑ i, ((z i : ℝ)) ^ 2) < t then (max 1 √(∑ i, ((z i : ℝ)) ^ 2)) ^ (-a) else 0
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    simp only [φ]
    split_ifs
    · exact Real.rpow_nonneg (by positivity) _
    · exact le_rfl
  have hle : ∑' z, ENNReal.ofReal (φ z) ≤
      ENNReal.ofReal (3 ^ d * 2 ^ a / (1 - 2 ^ (a - d)) * t ^ ((d : ℝ) - a)) := by
    refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) hE
    simp only [φ]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (max_le ht h1.le) h2
    · simp
    · simp
  have hsum : Summable φ :=
    (summable_iff_tsum_ofReal_ne_top hφ0).2 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  refine ⟨hsum, ?_⟩
  have h2 : (2 : ℝ) ^ (a - d) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC : 0 ≤ 3 ^ d * 2 ^ a / (1 - 2 ^ (a - d)) * t ^ ((d : ℝ) - a) := by
    have : 0 < 1 - (2 : ℝ) ^ (a - d) := by linarith
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hφ0 hsum] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 hle

/-! ### Transfer of the leading term -/

/-- **A signed summable kernel transfers a spatial power-law leading term.** Let `0 < a < d`.
If `f(x) = A |x|^(-a) + o(|x|^(-a))` as `|x| → ∞`, `∑ |g| < ∞` and `|g(y)| ≤ K ⟨y⟩^(-d)`, then
`∑ y, f(x - y) g(y)` converges absolutely for every `x` and
`∑ y, f(x - y) g(y) = A (∑ g) |x|^(-a) + o(|x|^(-a))`. -/
theorem summable_abs_mul_and_isLittleO_tsum_mul_sub {a A K : ℝ} (ha : 0 < a) (had : a < d)
    {f g : (Fin d → ℤ) → ℝ}
    (hf : (fun x => f x - A * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) =o[comap
      (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) atTop] fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
    (hg : Summable fun y => |g y|)
    (hgK : ∀ y, |g y| ≤ K * (max 1 √(∑ i, ((y i : ℝ)) ^ 2)) ^ (-(d : ℝ))) :
    (∀ x, Summable fun y => |f (x - y) * g y|) ∧
      (fun x => ∑' y, f (x - y) * g y - A * (∑' y, g y) * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
        =o[comap (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) atTop]
          fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a) := by
  have hK : 0 ≤ K := by
    have h := hgK 0
    have h0 : max 1 √(∑ i, (((0 : Fin d → ℤ) i : ℤ) : ℝ) ^ 2) = 1 := by simp
    rw [h0, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  set e : (Fin d → ℤ) → ℝ := fun x => √(∑ i, ((x i : ℝ)) ^ 2) with he_def
  have he0 : ∀ x, 0 ≤ e x := fun x => Real.sqrt_nonneg _
  have hbpos : ∀ x, 0 < max 1 (e x) := fun x => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hb1 : ∀ x, (max 1 (e x)) ^ (-a) ≤ 1 := fun x =>
    Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)
  have hgs : Summable g := hg.of_abs
  -- a global bound `|f| ≤ M ⟨·⟩^(-a)`
  have hO : f =O[comap e atTop] fun x => e x ^ (-a) :=
    (hf.isBigO.add ((isBigO_refl (fun x => e x ^ (-a)) _).const_mul_left A)).congr_left
      fun x => by ring
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_mul_max_sqrt_sum_sq_rpow ha.le hO
  have hfM : ∀ x, |f x| ≤ M := fun x =>
    (hM x).trans (mul_le_of_le_one_right hM0 (hb1 x))
  have hsumf : ∀ x, Summable fun y => |f (x - y) * g y| := fun x =>
    (hg.mul_left M).of_nonneg_of_le (fun y => abs_nonneg _) fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hfM _) (abs_nonneg _)
  refine ⟨hsumf, IsLittleO.of_bound fun δ hδ => ?_⟩
  -- constants
  set S := ∑' y, |g y| with hS_def
  have hS0 : 0 ≤ S := tsum_nonneg fun y => abs_nonneg _
  set C : ℝ := 3 ^ d * 2 ^ a / (1 - 2 ^ (a - d)) with hC_def
  have hC0 : 0 ≤ C := by
    have h2 : (2 : ℝ) ^ (a - d) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 < 1 - (2 : ℝ) ^ (a - d) := by linarith
    positivity
  -- choice of `ε`
  have hcont : Tendsto (fun ε : ℝ => S * |A| * ((1 - ε) ^ (-a) - (1 + ε) ^ (-a)) +
      M * K * 2 ^ (d : ℝ) * C * ε ^ ((d : ℝ) - a)) (𝓝 0) (𝓝 0) := by
    have h1 : ContinuousAt (fun ε : ℝ => (1 - ε) ^ (-a)) 0 :=
      ContinuousAt.rpow_const (f := fun ε : ℝ => 1 - ε)
        (continuousAt_const.sub continuousAt_id) (Or.inl (by norm_num))
    have h2 : ContinuousAt (fun ε : ℝ => (1 + ε) ^ (-a)) 0 :=
      ContinuousAt.rpow_const (f := fun ε : ℝ => 1 + ε)
        (continuousAt_const.add continuousAt_id) (Or.inl (by norm_num))
    have h3 : ContinuousAt (fun ε : ℝ => ε ^ ((d : ℝ) - a)) 0 :=
      ContinuousAt.rpow_const (f := fun ε : ℝ => ε) continuousAt_id (Or.inr (by linarith))
    have h : ContinuousAt (fun ε : ℝ => S * |A| * ((1 - ε) ^ (-a) - (1 + ε) ^ (-a)) +
        M * K * 2 ^ (d : ℝ) * C * ε ^ ((d : ℝ) - a)) 0 :=
      (continuousAt_const.mul (h1.sub h2)).add (continuousAt_const.mul h3)
    simpa [Real.zero_rpow (by linarith : (d : ℝ) - a ≠ 0)] using h.tendsto
  obtain ⟨ε, ⟨hεv, hε3⟩, hε0⟩ := (((tendsto_nhdsWithin_of_tendsto_nhds hcont).eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 3))).and
    ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)))).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0) |>.exists
  simp only [id] at hε0 hε3
  -- the little-o bound for `f`
  set c' : ℝ := δ / (3 * (S + 1) * 2 ^ a) with hc'_def
  have hc' : 0 < c' := by positivity
  obtain ⟨r₁, hr₁1, hr₁⟩ := exists_forall_le_of_eventually_comap (hf.bound hc') 1
  -- the tail of `∑ |g|`
  have hlim : Tendsto (fun t => (M * ε ^ (-a) + |A|) * ∑' y, if t ≤ e y then |g y| else 0)
      atTop (𝓝 0) := by
    simpa using ((tendsto_tsum_ite_le_abs (e := e) hg).const_mul (M * ε ^ (-a) + |A|))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 3)))
  refine eventually_comap.2 ((eventually_ge_atTop (max (2 * r₁) (max (t₀ / ε) (1 / ε)))).mono
    fun r hr x hx => ?_)
  -- fix `x` with `R = |x|` large
  set R := e x with hR_def
  have hRr : max (2 * r₁) (max (t₀ / ε) (1 / ε)) ≤ R := hx ▸ hr
  have hR1 : 2 * r₁ ≤ R := le_trans (le_max_left _ _) hRr
  have hRpos : 0 < R := by linarith
  have hεR3 : ε * R ≤ R / 3 := by
    have := mul_le_mul_of_nonneg_right hε3.le hRpos.le
    linarith
  have hεR1 : 1 ≤ ε * R := by
    have : 1 / ε ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRr
    rwa [div_le_iff₀ hε0, mul_comm] at this
  have hεRt : t₀ ≤ ε * R := by
    have : t₀ / ε ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRr
    rwa [div_le_iff₀ hε0, mul_comm] at this
  set P := R ^ (-a) with hP_def
  have hP : 0 < P := Real.rpow_pos_of_pos hRpos _
  set η := (1 - ε) ^ (-a) - (1 + ε) ^ (-a) with hη_def
  have hη1 : (1 + ε) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hη2 : 1 ≤ (1 - ε) ^ (-a) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by linarith)
  set c₁ := c' * 2 ^ a * P + |A| * η * P with hc₁_def
  set c₂ := M * K * 2 ^ (d : ℝ) * R ^ (-(d : ℝ)) with hc₂_def
  set c₃ := M * (ε * R) ^ (-a) + |A| * P with hc₃_def
  have hc₁ : 0 ≤ c₁ := by
    have : 0 ≤ η := by linarith
    positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hc₃ : 0 ≤ c₃ := by
    have : 0 ≤ (ε * R) ^ (-a) := Real.rpow_nonneg (by positivity) _
    positivity
  set ψ : (Fin d → ℤ) → ℝ := fun z => if e z < ε * R then (max 1 (e z)) ^ (-a) else 0
    with hψ_def
  obtain ⟨hψsum, hψle⟩ := tsum_ite_sqrt_sum_sq_lt_rpow_le (d := d) ha.le had hεR1
  set T := ∑' y, if ε * R ≤ e y then |g y| else 0 with hT_def
  have hT := ht₀ (ε * R) hεRt
  -- pointwise bound
  have hpt : ∀ y, |(f (x - y) - A * P) * g y| ≤
      c₁ * (if e y < ε * R then |g y| else 0) + c₂ * ψ (x - y) +
        c₃ * (if ε * R ≤ e y then |g y| else 0) := by
    intro y
    have htri1 := sqrt_sum_sq_le_sub_add x y
    have htri2 := sqrt_sum_sq_sub_le x y
    change R ≤ e (x - y) + e y at htri1
    change e (x - y) ≤ R + e y at htri2
    have hψ0 : 0 ≤ ψ (x - y) := by
      simp only [ψ]
      split_ifs
      · exact Real.rpow_nonneg (hbpos _).le _
      · exact le_rfl
    rw [abs_mul]
    by_cases hy : e y < ε * R
    · -- near the origin: the leading term
      rw [ite_eq_left hy, ite_eq_right (not_le.2 hy), mul_zero, add_zero]
      have hv1' : R - ε * R ≤ e (x - y) := by linarith
      have hv2' : e (x - y) ≤ R + ε * R := by linarith
      have hv1 : (1 - ε) * R ≤ e (x - y) := by
        rw [sub_mul, one_mul]
        exact hv1'
      have hv2 : e (x - y) ≤ (1 + ε) * R := by
        rw [add_mul, one_mul]
        exact hv2'
      have hvpos : 0 < (1 - ε) * R := by
        rw [sub_mul, one_mul]
        linarith
      have hvr : r₁ ≤ e (x - y) := by linarith
      have hh := hr₁ (x - y) hvr
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (he0 _) _)] at hh
      have hw1 : e (x - y) ^ (-a) ≤ (1 - ε) ^ (-a) * P := by
        rw [hP_def, ← Real.mul_rpow (by linarith) hRpos.le]
        exact Real.rpow_le_rpow_of_nonpos hvpos hv1 (by linarith)
      have hw2 : (1 + ε) ^ (-a) * P ≤ e (x - y) ^ (-a) := by
        rw [hP_def, ← Real.mul_rpow (by linarith) hRpos.le]
        exact Real.rpow_le_rpow_of_nonpos (by linarith) hv2 (by linarith)
      have hw3 : e (x - y) ^ (-a) ≤ 2 ^ a * P := by
        rw [hP_def, ← div_two_rpow_neg hRpos.le]
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have hq1 : (1 + ε) ^ (-a) * P ≤ P := mul_le_of_le_one_left hP.le hη1
      have hq2 : P ≤ (1 - ε) ^ (-a) * P := le_mul_of_one_le_left hP.le hη2
      have hηP : η * P = (1 - ε) ^ (-a) * P - (1 + ε) ^ (-a) * P := by
        rw [hη_def]
        ring
      have hdiff : |e (x - y) ^ (-a) - P| ≤ η * P := by
        rw [abs_sub_le_iff, hηP]
        constructor <;> linarith
      have hfa : |f (x - y) - A * P| ≤ c₁ := by
        calc |f (x - y) - A * P|
            = |(f (x - y) - A * e (x - y) ^ (-a)) + A * (e (x - y) ^ (-a) - P)| := by ring_nf
          _ ≤ |f (x - y) - A * e (x - y) ^ (-a)| + |A| * |e (x - y) ^ (-a) - P| := by
              rw [← abs_mul]
              exact abs_add_le _ _
          _ ≤ c' * (2 ^ a * P) + |A| * (η * P) := by
              gcongr
              exact hh.trans (mul_le_mul_of_nonneg_left hw3 hc'.le)
          _ = c₁ := by ring
      linarith [mul_le_mul_of_nonneg_right hfa (abs_nonneg (g y)), mul_nonneg hc₂ hψ0]
    · -- away from the origin
      rw [not_lt] at hy
      rw [ite_eq_right (not_lt.2 hy), ite_eq_left hy, mul_zero, zero_add]
      have hfa : |f (x - y) - A * P| * |g y| ≤ |f (x - y)| * |g y| + |A| * P * |g y| := by
        calc |f (x - y) - A * P| * |g y| ≤ (|f (x - y)| + |A * P|) * |g y| :=
              mul_le_mul_of_nonneg_right (abs_sub _ _) (abs_nonneg _)
          _ = |f (x - y)| * |g y| + |A| * P * |g y| := by rw [abs_mul, abs_of_pos hP]; ring
      by_cases hv : e (x - y) < ε * R
      · have hψv : ψ (x - y) = (max 1 (e (x - y))) ^ (-a) := ite_eq_left hv
        have hu : R / 2 ≤ max 1 (e y) := le_trans (by linarith) (le_max_right _ _)
        have hgy : |g y| ≤ K * (2 ^ (d : ℝ) * R ^ (-(d : ℝ))) := by
          refine (hgK y).trans (mul_le_mul_of_nonneg_left ?_ hK)
          rw [← div_two_rpow_neg hRpos.le]
          exact Real.rpow_le_rpow_of_nonpos (by linarith) hu (neg_nonpos.2 (Nat.cast_nonneg d))
        have h1 : |f (x - y)| * |g y| ≤ c₂ * ψ (x - y) := by
          rw [hψv]
          calc |f (x - y)| * |g y|
              ≤ (M * (max 1 (e (x - y))) ^ (-a)) * (K * (2 ^ (d : ℝ) * R ^ (-(d : ℝ)))) :=
                mul_le_mul (hM _) hgy (abs_nonneg _)
                  (mul_nonneg hM0 (Real.rpow_nonneg (hbpos _).le _))
            _ = c₂ * (max 1 (e (x - y))) ^ (-a) := by ring
        have h2 : |A| * P * |g y| ≤ c₃ * |g y| := by
          have : 0 ≤ M * (ε * R) ^ (-a) := mul_nonneg hM0 (Real.rpow_nonneg (by positivity) _)
          exact mul_le_mul_of_nonneg_right (by rw [hc₃_def]; linarith) (abs_nonneg _)
        linarith
      · rw [not_lt] at hv
        have hfv : |f (x - y)| ≤ M * (ε * R) ^ (-a) := by
          refine (hM _).trans (mul_le_mul_of_nonneg_left ?_ hM0)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) (hv.trans (le_max_right _ _))
            (by linarith)
        have h3 : |f (x - y) - A * P| ≤ c₃ := by
          rw [hc₃_def]
          calc |f (x - y) - A * P| ≤ |f (x - y)| + |A * P| := abs_sub _ _
            _ ≤ M * (ε * R) ^ (-a) + |A| * P := by rw [abs_mul, abs_of_pos hP]; linarith
        linarith [mul_le_mul_of_nonneg_right h3 (abs_nonneg (g y)), mul_nonneg hc₂ hψ0]
  -- summability of the three pieces
  have hs1 : Summable fun y => c₁ * (if e y < ε * R then |g y| else 0) :=
    (hg.of_nonneg_of_le (fun y => by split_ifs <;> simp) fun y => by
      split_ifs <;> simp).mul_left _
  have hs2 : Summable fun y => c₂ * ψ (x - y) :=
    ((Equiv.subLeft x).summable_iff.2 hψsum).mul_left _
  have hs3 : Summable fun y => c₃ * (if ε * R ≤ e y then |g y| else 0) :=
    (hg.of_nonneg_of_le (fun y => by split_ifs <;> simp) fun y => by
      split_ifs <;> simp).mul_left _
  -- the error as a single series
  have herr : ∑' y, f (x - y) * g y - A * (∑' y, g y) * R ^ (-a) =
      ∑' y, (f (x - y) - A * P) * g y := by
    rw [show A * (∑' y, g y) * R ^ (-a) = ∑' y, A * P * g y by rw [tsum_mul_left]; ring,
      ← Summable.tsum_sub (hsumf x).of_abs (hgs.mul_left _)]
    exact tsum_congr fun y => by ring
  have hsumerr : Summable fun y => |(f (x - y) - A * P) * g y| :=
    ((hs1.add hs2).add hs3).of_nonneg_of_le (fun y => abs_nonneg _) hpt
  have hbound : |∑' y, (f (x - y) - A * P) * g y| ≤
      c₁ * ∑' y, (if e y < ε * R then |g y| else 0) + c₂ * ∑' z, ψ z + c₃ * T := by
    calc |∑' y, (f (x - y) - A * P) * g y|
        ≤ ∑' y, |(f (x - y) - A * P) * g y| := by
          have h := norm_tsum_le_tsum_norm (f := fun y => (f (x - y) - A * P) * g y)
            (by simpa only [Real.norm_eq_abs] using hsumerr)
          simp only [Real.norm_eq_abs] at h
          exact h
      _ ≤ ∑' y, (c₁ * (if e y < ε * R then |g y| else 0) + c₂ * ψ (x - y) +
            c₃ * (if ε * R ≤ e y then |g y| else 0)) :=
          hsumerr.tsum_le_tsum hpt ((hs1.add hs2).add hs3)
      _ = c₁ * ∑' y, (if e y < ε * R then |g y| else 0) + c₂ * ∑' z, ψ z + c₃ * T := by
          have hψt : ∑' y, ψ (x - y) = ∑' z, ψ z := (Equiv.subLeft x).tsum_eq ψ
          rw [(hs1.add hs2).tsum_add hs3, hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left,
            tsum_mul_left, hψt]
  -- final arithmetic
  have hS' : ∑' y, (if e y < ε * R then |g y| else 0) ≤ S :=
    (hg.of_nonneg_of_le (fun y => by split_ifs <;> simp) fun y => by
      split_ifs <;> simp).tsum_le_tsum (fun y => by split_ifs <;> simp) hg
  have hψle' : ∑' z, ψ z ≤ C * (ε * R) ^ ((d : ℝ) - a) := hψle
  have hεRpow : (ε * R) ^ ((d : ℝ) - a) = ε ^ ((d : ℝ) - a) * (R ^ (d : ℝ) * P) := by
    rw [Real.mul_rpow hε0.le hRpos.le, hP_def, ← Real.rpow_add hRpos]
    ring_nf
  have hRd : R ^ (-(d : ℝ)) * R ^ (d : ℝ) = 1 := by
    rw [← Real.rpow_add hRpos, neg_add_cancel, Real.rpow_zero]
  have hεRa : (ε * R) ^ (-a) = ε ^ (-a) * P := Real.mul_rpow hε0.le hRpos.le
  have hterm2 : c₂ * ∑' z, ψ z ≤ M * K * 2 ^ (d : ℝ) * C * ε ^ ((d : ℝ) - a) * P := by
    calc c₂ * ∑' z, ψ z ≤ c₂ * (C * (ε * R) ^ ((d : ℝ) - a)) :=
          mul_le_mul_of_nonneg_left hψle' hc₂
      _ = M * K * 2 ^ (d : ℝ) * C * ε ^ ((d : ℝ) - a) * P * (R ^ (-(d : ℝ)) * R ^ (d : ℝ)) := by
          rw [hεRpow, hc₂_def]
          ring
      _ = _ := by rw [hRd, mul_one]
  have hterm1 : c₁ * ∑' y, (if e y < ε * R then |g y| else 0) ≤
      (S * c' * 2 ^ a + S * |A| * η) * P := by
    calc c₁ * ∑' y, (if e y < ε * R then |g y| else 0) ≤ c₁ * S :=
          mul_le_mul_of_nonneg_left hS' hc₁
      _ = _ := by rw [hc₁_def]; ring
  have hSc : S * c' * 2 ^ a ≤ δ / 3 := by
    rw [hc'_def]
    have h2a : 0 < (2 : ℝ) ^ a := by positivity
    rw [show S * (δ / (3 * (S + 1) * 2 ^ a)) * 2 ^ a = δ / 3 * (S / (S + 1)) by
      field_simp]
    have : S / (S + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    exact mul_le_of_le_one_right (by linarith) this
  have hterm3 : c₃ * T ≤ (M * ε ^ (-a) + |A|) * T * P := by
    rw [hc₃_def, hεRa]
    ring_nf
    exact le_rfl
  have hT' : (M * ε ^ (-a) + |A|) * T < δ / 3 := hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (he0 _) _), herr]
  calc |∑' y, (f (x - y) - A * P) * g y|
      ≤ c₁ * ∑' y, (if e y < ε * R then |g y| else 0) + c₂ * ∑' z, ψ z + c₃ * T := hbound
    _ ≤ (S * c' * 2 ^ a + S * |A| * η) * P +
          M * K * 2 ^ (d : ℝ) * C * ε ^ ((d : ℝ) - a) * P + (M * ε ^ (-a) + |A|) * T * P := by
        linarith
    _ = (S * c' * 2 ^ a + (S * |A| * η + M * K * 2 ^ (d : ℝ) * C * ε ^ ((d : ℝ) - a)) +
          (M * ε ^ (-a) + |A|) * T) * P := by ring
    _ ≤ δ * P := mul_le_mul_of_nonneg_right (by linarith) hP.le


/-- Under the hypotheses of `summable_abs_mul_and_isLittleO_tsum_mul_sub`, the convolution
`∑ y, f(x - y) g(y)` converges absolutely for every `x`. -/
theorem summable_abs_mul_of_isLittleO {a A K : ℝ} (ha : 0 < a) (had : a < d)
    {f g : (Fin d → ℤ) → ℝ}
    (hf : (fun x => f x - A * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) =o[comap
      (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) atTop] fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
    (hg : Summable fun y => |g y|)
    (hgK : ∀ y, |g y| ≤ K * (max 1 √(∑ i, ((y i : ℝ)) ^ 2)) ^ (-(d : ℝ))) :
    ∀ x, Summable fun y => |f (x - y) * g y| :=
  (summable_abs_mul_and_isLittleO_tsum_mul_sub ha had hf hg hgK).1

/-- Under the hypotheses of `summable_abs_mul_and_isLittleO_tsum_mul_sub`,
`∑ y, f(x - y) g(y) = A (∑ g) |x|^(-a) + o(|x|^(-a))`. -/
theorem isLittleO_tsum_mul_sub {a A K : ℝ} (ha : 0 < a) (had : a < d)
    {f g : (Fin d → ℤ) → ℝ}
    (hf : (fun x => f x - A * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) =o[comap
      (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) atTop] fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
    (hg : Summable fun y => |g y|)
    (hgK : ∀ y, |g y| ≤ K * (max 1 √(∑ i, ((y i : ℝ)) ^ 2)) ^ (-(d : ℝ))) :
    (fun x => ∑' y, f (x - y) * g y - A * (∑' y, g y) * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
      =o[comap (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) atTop]
        fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a) :=
  (summable_abs_mul_and_isLittleO_tsum_mul_sub ha had hf hg hgK).2

end PercLib.Models.LongRange
