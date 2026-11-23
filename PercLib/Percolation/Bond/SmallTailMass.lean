/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs written for the cutoff-truncated moment derivative of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1.
No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Models.LongRange.TruncatedMoments
public import PercLib.Models.LongRange.CutoffMonotone

/-!
# The window-mass input of the LRP small-tail estimate, uniformly in the cut-off scale

The recovered `PercLib.Models.LongRange.TruncatedMoments` reduces the small-tail premise `htail`
of the cut-off moment-derivative interface to two inputs at a fixed scale `r`:

* `hfac` — the *gap* factorisation: the pivotal crossing mass of a pair is at most `C` times the
  smaller of the two vertex masses.  Nothing here touches that obligation;
* `hext` — the *mass* input: the root-cluster mass carried by vertices outside a finite window
  `W` is at most `δ`.  Production supplies it one scale at a time
  (`PercLib.Percolation.Bond.exists_window_mass_tail_le`, from `χ < ∞` at that scale), which yields
  a window `W` depending on `r`.

`htail` is *not* a per-scale statement: it asks for one finite pair set `F` and one neighbourhood
`U` of a scale `r₀` such that the tail is small for **every** `r ∈ U ∩ Ioo u v`.  So the mass input
has to be uniform in `r` with `W` fixed, and this file proves that it is, at the price of exactly
one extra input: a single summable majorant `σ` of the vertex masses on the range of scales.

The mechanism is elementary and worth stating plainly, because it is where the "constant
independent of the scale" enters:

* `χ_r = ∑_x τ_r(x)` is *monotone* in `r` for the cut-off family
  (`PercLib.Percolation.Bond.tau_cutoffKernel_mono`, from `AntitoneOn K (Ioi 0)`);
* hence `τ_r(x) ≤ τ_{r₁}(x)` for all `r ≤ r₁`, and `∑_x τ_{r₁}(x) = χ_{r₁} < ∞` is a *fixed,
  scale-independent* summable majorant;
* for a summable `ℝ≥0∞` family the tail over the complement of a finite set tends to `0` along
  the directed finite sets (`ENNReal.tendsto_tsum_compl_atTop_zero`), so one window `W` works for
  all `r ≤ r₁` simultaneously.

Consequently the whole smallness of `hext` is uniform in the scale given finiteness of the first
moment at the top of the interval only (a genuine hypothesis: finite range does not give it): no
uniform-in-`r` first moment bound is needed for this step, and no smallness of `χ_r` beyond
`χ_{r₁} < ∞`.

## What this does and does not give

* It discharges `hext` uniformly on `Iic r₁`, and hence the *mass* half of `htail`, with the
  explicit constant `2 * #S * (C * δ)` of `lintegral_window_tail_le_of_factorization`.
* It does **not** prove `hfac`, and it does **not** prove `htail`: the gap factorisation stays a
  hypothesis of the last theorem, named `hfac` with the same type as in production.
* No exchange of an `ℝ≥0∞` limit with a real series is performed; the real-norm conversion is
  production's `tsum_norm_cutoff_flux_compl_le_of_lintegral_window_tail`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {α : Type*}

/-- The `W`-exterior mass written with an indicator multiplier is the sum over the complement
subtype.  Purely notational: production's `hext` is written with the multiplier, while the tail
argument is stated on the complement subtype. -/
theorem tsum_ite_mem_eq_tsum_compl [DecidableEq α] (W : Finset α) (g : α → ℝ≥0∞) :
    (∑' x : α, (if x ∈ W then (0 : ℝ≥0∞) else 1) * g x) =
      ∑' x : {x : α // x ∉ W}, g x := by
  have h1 : (∑' x : {x : α // x ∉ W}, g x) = ∑' x : ↥({x : α | x ∉ W} : Set α), g x := rfl
  rw [h1, tsum_subtype]
  refine tsum_congr fun x => ?_
  by_cases h : x ∈ W <;> simp [h]

open Classical in
/-- **The tail of a summable `ℝ≥0∞` family over the complement of a finite set is small.**

This is `ENNReal.tendsto_tsum_compl_atTop_zero` unwound into an existential: no summability
hypothesis beyond finiteness of the total sum, and no countability of `α` (if the total is not
finite the hypothesis is false). -/
theorem exists_finset_tsum_compl_le_of_tsum_ne_top (f : α → ℝ≥0∞) (hf : ∑' x, f x ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset α, ∑' x : {x : α // x ∉ W}, f x ≤ ε := by
  have hev : ∀ᶠ W : Finset α in atTop, ∑' x : {x : α // x ∉ W}, f x < ε :=
    (ENNReal.tendsto_tsum_compl_atTop_zero hf).eventually (eventually_lt_nhds hε)
  obtain ⟨W, hW⟩ := hev.exists
  exact ⟨W, le_of_lt hW⟩

open Classical in
/-- **One window works uniformly along a scale family dominated by a summable majorant.**

If every member of the family `τ i` (`i ∈ U`) is dominated vertexwise by one summable `σ` whose
total mass is finite, then a single finite window `W` makes the `W`-exterior mass at most `ε`
*simultaneously for all* `i ∈ U`.  The constant is scale-independent because `σ` is. -/
theorem exists_window_tsum_compl_le_of_majorant {ι : Type*} (U : Set ι)
    (τ : ι → α → ℝ≥0∞) (σ : α → ℝ≥0∞) (hσ : ∑' x, σ x ≠ ⊤)
    (hmaj : ∀ i ∈ U, τ i ≤ σ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Finset α, ∀ i ∈ U, ∑' x : {x : α // x ∉ W}, τ i x ≤ ε := by
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le_of_tsum_ne_top σ hσ hε
  exact ⟨W, fun i hi => le_trans (ENNReal.tsum_le_tsum fun x => hmaj i hi x) hW⟩

section Cutoff

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Models.LongRange

variable {d : ℕ} {K : ℝ → ℝ} {N : ModelNorm (Fin d → ℝ)}

open Classical in
/-- **The root-cluster mass outside one finite window is uniformly small on a scale interval.**

For the cut-off family `r ↦ law (intensityProfile (cutoffKernel N K r) β)` with `K` decreasing on
`(0, ∞)`, the vertex masses `x ↦ P(x ∈ cluster of o)` increase in the scale
(`tau_cutoffKernel_mono`), so on `Iic r₁` they are dominated by their value at `r₁`, whose total
mass is the susceptibility `χ` of the cut-off model at the *single* scale `r₁`.

Given `χ r₁ < ∞` and any
`δ > 0` there is therefore a finite window `W` with

`∑_{x ∉ W} P_r(x ∈ cluster of o) ≤ δ`  for **all** `r ≤ r₁`.

This is the `hext` hypothesis of `window_tail_le_of_factorization_of_tau_tail`, in the exact
`if x ∈ W then 0 else 1` shape production uses, and uniformly in the scale.

`χ r₁ < ∞` is a **genuine hypothesis**, not a consequence of the cut-off being finite-range: a
finite-range model with a large enough intensity percolates, and then `χ = ∞`.  It is supplied by
a row-sum bound with `β M < 1` (`chi_intensity_lt_top`) or by a finite root moment at `r₁`
(`chi_cutoffKernel_ne_top_of_root_moment` below).  Nothing here proves or uses `β.M < 1` itself. -/
theorem exists_window_exterior_root_mass_uniform (hK : AntitoneOn K (Ioi 0)) (β : ℝ≥0)
    (o : Fin d → ℤ) {r₁ : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K r₁) β) o ≠ ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ W : Finset (Fin d → ℤ), ∀ r ∈ Iic r₁,
      (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
        ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ δ := by
  have hσ : (∑' x : Fin d → ℤ,
      ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r₁) β))) ≠ ⊤ := by
    rw [show (∑' x : Fin d → ℤ,
        ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₁) β))) =
        chi (intensityProfile (cutoffKernel (d := d) N K r₁) β) o from ?_]
    · exact hχ
    · rw [chi_eq_tsum_tau]
      exact tsum_congr fun x => (tau_eq_lintegral_cluster_indicator _ o x).symm
  have hmaj : ∀ r ∈ Iic r₁,
      (fun x : Fin d → ℤ => ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤
      (fun x : Fin d → ℤ => ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r₁) β))) := by
    intro r hr x
    simp only [← tau_eq_lintegral_cluster_indicator]
    exact tau_cutoffKernel_mono (d := d) (N := N) hK β (mem_Iic.1 hr) o x
  obtain ⟨W, hW⟩ := exists_window_tsum_compl_le_of_majorant (Iic r₁)
    (fun r x => ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
    (fun x => ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r₁) β))) hσ hmaj hδ
  refine ⟨W, fun r hr => ?_⟩
  exact le_of_eq_of_le (tsum_ite_mem_eq_tsum_compl W _) (hW r hr)

open Classical in
/-- **The `ℝ≥0∞` window tail, uniformly in the scale, from the gap factorisation alone.**

Fix `r₁`, a finite window `W` whose exterior root-cluster mass is at most `δ` for every `r ≤ r₁`
(`exists_window_exterior_root_mass_uniform`), and a finite set `S` containing the `r₁`-ball.  If
the gap factorisation `hfac` holds with constant `C` at *every* scale `r ≤ r₁`, then the pivotal
window tail at scale `r` — pairs outside `pairs (W × W)`, radially truncated at `r`, weighted by
the closed-pivotal increment — is at most `ε` for every `r ≤ r₁`, with the single arithmetic
condition `2 * #S * (C * δ) ≤ ε`.

The point is the uniformity: `#S` is read at the *top* scale `r₁`, `δ` is scale-independent by the
previous theorem, and production's `window_tail_le_of_factorization_of_tau_tail` is applied at each
`r` with these fixed numbers.  The gap factorisation `hfac` remains the only mathematical input. -/
theorem exists_window_uniform_window_tail_le_of_factorization
    (β : ℝ≥0) (p : ℕ) (o : Fin d → ℤ) {r₁ : ℝ}
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < r₁ → z ∈ S)
    (C : ℝ≥0∞) (U : Set ℝ) (hUv : ∀ r ∈ U, r ≤ r₁) {δ ε : ℝ≥0∞}
    (hfac : ∀ r ∈ U, ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))))
    (W : Finset (Fin d → ℤ))
    (hmass : ∀ r ∈ U,
      (∑' x : Fin d → ℤ, (if x ∈ W then (0 : ℝ≥0∞) else 1) *
        ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ δ)
    (hεδ : 2 * ((S.card : ℝ≥0∞) * (C * δ)) ≤ ε) :
    ∀ r ∈ U,
      (∫⁻ ω, ∑' e : Sym2 (Fin d → ℤ),
        ((if e ∈ (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2))
          then (0 : ℝ≥0∞) else 1) *
          (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ≥0∞)) *
          (if e ∈ ω then 0 else (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ ε := by
  intro r hr
  refine window_tail_le_of_factorization_of_tau_tail (N := N) (r := r) S ?_ _
    o p _ radialKernel_indicator_hcsupp W C (hfac r hr) (hmass r hr) hεδ
  intro z hz
  exact hS z (lt_of_lt_of_le hz (hUv r hr))

end Cutoff

section Htail

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Models.LongRange

variable {d : ℕ} {K K' : ℝ → ℝ} {N : ModelNorm (Fin d → ℝ)}

open Classical in
/-- **The literal `htail` premise from the gap factorisation and finiteness at one scale.**

This assembles the mass half of the small-tail estimate into the exact hypothesis consumed by
`hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail`:

`∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F, ∀ r ∈ U ∩ Ioo u v, ∑' e ∉ F, ‖cw r e * ∫ (pivotal)‖ ≤ ε`.

The inputs are, besides the shape of the derivative weight `cw`:

* `hfac` — the gap factorisation at every scale `r ∈ Ioo u v` (the one mathematical obligation
  this file does not address);
* `hK` — `K` decreasing on `(0, ∞)`, giving monotonicity of the vertex masses in the scale;
* `hχ` — finiteness of the susceptibility at the *single* top scale `v`.  This is a hypothesis
  and **not** a consequence of finite range: a finite-range model can percolate, and then `χ = ∞`.
  It is discharged by a row-sum bound with `β M < 1` (`chi_intensity_lt_top`) or by a finite
  root moment at `v` (`chi_cutoffKernel_ne_top_of_root_moment`);
* `S`, `hS` — a finite set containing the `v`-ball, so that `#S` is a scale-independent constant;
* `hC` — finiteness of the gap constant;
* `hΛ` — a local bound `|β J'(r)| ≤ Λ` on `Ioo u v`, the only place the rate enters, and it enters
  linearly and is never inverted;
* `hins` — finiteness of the truncated `p`-th pivotal moment at every scale of the interval.

The uniform smallness of the exterior root-cluster mass is *proved* here, not assumed:
`exists_window_exterior_root_mass_uniform` gives one window for all scales `≤ v`.  The arithmetic
is resolved explicitly: `δ` is chosen so that `2 * #S * (C * δ) ≤ ofReal (ε / (Λ + 1))`, and
`Λ * (ε / (Λ + 1)) ≤ ε` closes the real-norm estimate.  So the constant `2 #S C` is independent of
`r` and of the neighbourhood `U`; the only `r`-dependence left is the truncation of the kernel in
`cw r`, which is exactly the bounded support of the cut-off kernel at scale `r`.

Nothing here asserts anything about `hfac`; if `hfac` is not available for the model at hand, this
theorem says precisely that it is the only remaining input of the mass half of `htail`. -/
theorem exists_nhds_htail_of_factorization
    (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    (hK : AntitoneOn K (Ioi 0)) {u v : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K v) β) o ≠ ⊤)
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (Λ : ℝ)
    (hΛ : ∀ r ∈ Ioo u v, |(β : ℝ) * -K' r| ≤ Λ)
    (hins : ∀ r ∈ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hfac : ∀ r ∈ Ioo u v, ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω o then 0 else 1) *
          ((((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
        (∫⁻ ω, (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))) :
    ∀ r₀ ∈ Ioo u v, ∀ ε > 0, ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖cw r e.1 * ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))‖ ≤ ε := by
  intro r₀ hr₀ ε hε
  have hr₀v : r₀ < v := hr₀.2
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ r₀ hr₀)
  have hε'pos : 0 < ε / (Λ + 1) := div_pos hε (by linarith)
  have hex : ∃ δ : ℝ≥0∞, 0 < δ ∧
      2 * ((S.card : ℝ≥0∞) * (C * δ)) ≤ ENNReal.ofReal (ε / (Λ + 1)) := by
    by_cases h0 : 2 * (S.card : ℝ≥0∞) * C = 0
    · refine ⟨1, one_pos, ?_⟩
      rw [show 2 * ((S.card : ℝ≥0∞) * (C * 1)) = 2 * (S.card : ℝ≥0∞) * C from by ring, h0]
      exact zero_le
    · refine ⟨ENNReal.ofReal (ε / (Λ + 1)) / (2 * (S.card : ℝ≥0∞) * C),
          ENNReal.div_pos (ne_of_gt (ENNReal.ofReal_pos.2 hε'pos))
            (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hC), ?_⟩
      rw [show 2 * ((S.card : ℝ≥0∞) * (C *
          (ENNReal.ofReal (ε / (Λ + 1)) / (2 * (S.card : ℝ≥0∞) * C)))) =
          2 * (S.card : ℝ≥0∞) * C *
            (ENNReal.ofReal (ε / (Λ + 1)) / (2 * (S.card : ℝ≥0∞) * C)) from by ring]
      exact le_of_eq (ENNReal.mul_div_cancel h0
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hC))
  obtain ⟨δ, hδpos, hδC⟩ := hex
  obtain ⟨W, hW⟩ := exists_window_exterior_root_mass_uniform (d := d) (N := N) (K := K)
    hK β o (r₁ := v) hχ hδpos
  refine ⟨Iio v, isOpen_Iio.mem_nhds hr₀v,
    (W.product W).image (fun q : (Fin d → ℤ) × (Fin d → ℤ) => s(q.1, q.2)), ?_⟩
  rintro r ⟨hrv, hrIoo⟩
  have hrv' : r ∈ Iic v := le_of_lt hrv
  have hBtop : 2 * ((S.card : ℝ≥0∞) * (C * δ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hδC
  refine exists_window_htail_of_lintegral_window_tail β p hp r o (cw r) (hcw r) W
    (2 * ((S.card : ℝ≥0∞) * (C * δ))) hBtop (hins r hrIoo) ?_ ε ?_
  · exact exists_window_uniform_window_tail_le_of_factorization (N := N) (K := K) (δ := δ)
      (ε := 2 * ((S.card : ℝ≥0∞) * (C * δ))) β p o (r₁ := v) S hS C
      (Ioo u v) (fun s hs => le_of_lt hs.2) (hfac := hfac) W
      (fun s hs => hW s (le_of_lt hs.2)) le_rfl r hrIoo
  · have hBle : (2 * ((S.card : ℝ≥0∞) * (C * δ))).toReal ≤ ε / (Λ + 1) := by
      have h1 : (2 * ((S.card : ℝ≥0∞) * (C * δ))).toReal ≤
          (ENNReal.ofReal (ε / (Λ + 1))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hδC
      rwa [ENNReal.toReal_ofReal hε'pos.le] at h1
    have hfrac : Λ / (Λ + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hsplit : Λ * (ε / (Λ + 1)) = ε * (Λ / (Λ + 1)) := by
      field_simp
    calc |(β : ℝ) * -K' r| * (2 * ((S.card : ℝ≥0∞) * (C * δ))).toReal
        ≤ Λ * (ε / (Λ + 1)) :=
          mul_le_mul (hΛ r hrIoo) hBle (ENNReal.toReal_nonneg) hΛ0
      _ = ε * (Λ / (Λ + 1)) := hsplit
      _ ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε := mul_one ε

end Htail

section Derivative

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Models.LongRange

variable {d : ℕ} {K K' : ℝ → ℝ} {N : ModelNorm (Fin d → ℝ)}

open Classical in
/-- **The cut-off binomial moment derivative, with `hfac` as the only input of `htail`.**

This is the recovered `hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail`
with its small-tail premise `htail` instantiated by `exists_nhds_htail_of_factorization`.  The
conclusion and every other hypothesis are copied verbatim from production; the only change is that
`htail` is replaced by its two explicit ingredients, of which the mass input is *proved* and the
gap factorisation `hfac` is a visible hypothesis (never an `Input` structure, never called proved).

Statement differences from production: none in the conclusion.  Hypothesis differences: the
hypothesis `htail` is replaced by `hfac` (gap) together with `hχ` (finite susceptibility at `v`),
`S`/`hS` (a finite set containing the `v`-ball), `C ≠ ⊤`, and a local rate bound `|β J'| ≤ Λ`; all
five are inputs that `htail` used to hide.  No sharpness, no all-radius corner claim, and no
`β.M < 1` inference is made. -/
theorem hasDerivAt_integral_cutoff_pow_binomial_of_factorization
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) {R : ℝ}
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hroot : ∀ r ∈ (Ioo u v ∪ {R} : Set ℝ), (∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M)
    (hχ : chi (intensityProfile (cutoffKernel (d := d) N K v) β) 0 ≠ ⊤)
    (S : Finset (Fin d → ℤ)) (hS : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (Λ : ℝ) (hΛ : ∀ r ∈ Ioo u v, |(β : ℝ) * -K' r| ≤ Λ)
    (hins : ∀ r ∈ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤)
    (hfac : ∀ r ∈ Ioo u v, ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel N (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω 0 then (1 : ℝ≥0∞) else 0) * (if y ∈ cluster ω 0 then 0 else 1) *
          ((((cluster ω 0).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω 0).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω 0 then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
        (∫⁻ ω, (if y ∈ cluster ω 0 then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω 0).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))
      ((β : ℝ) * -K' r₀ * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω 0).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y, (if N (Int.cast ∘ y) ≤ r₀ then 1 else 0) *
            (conn 0 y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r₀) β))) r₀ :=
  hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_small_tail
    (K := K) (K' := K') (R := R) (u := u) (v := v) (r₀ := r₀)
    hKa hK' hK'c β p hp M hM cw hcw hu hur hrv hvR hcorner hroot
    (exists_nhds_htail_of_factorization β p hp 0 cw hcw hKa hχ S hS C hC Λ hΛ hins hfac)

end Derivative

section RootMoment

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Models.LongRange

variable {d : ℕ} {K : ℝ → ℝ} {N : ModelNorm (Fin d → ℝ)}

open Classical in
/-- **Discharging the finiteness of the susceptibility at the top scale from a root moment.**

The hypothesis `hχ` of `exists_nhds_htail_of_factorization` (finiteness of `χ` at the top
scale `v`) follows from a finite `(p+1)`-th root moment at `v` for any `p`, by monotonicity of the
`ℝ≥0∞` powers (`lintegral_encard_cluster_le_of_pow_le`).  In particular no separate
susceptibility hypothesis is needed once the root-moment input is stated at the top scale too.

Note the direction: a *finite* moment at one scale implies `χ_v < ∞`; it does not by itself give
smallness of the exterior mass, which is what `exists_window_exterior_root_mass_uniform` supplies
from `χ_v < ∞` alone. -/
theorem chi_cutoffKernel_ne_top_of_root_moment (β : ℝ≥0) (p : ℕ) {v : ℝ}
    {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hrootv : (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
      ∂(law (intensityProfile (cutoffKernel (d := d) N K v) β))) ≤ M) :
    chi (intensityProfile (cutoffKernel (d := d) N K v) β) 0 ≠ ⊤ :=
  ne_top_of_le_ne_top hM (lintegral_encard_cluster_le_of_pow_le hrootv)

end RootMoment

end PercLib.Percolation.Bond
