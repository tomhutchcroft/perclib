/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1. The gap factorization remains an explicit premise, not a proved model fact.
-/
module

public import PercLib.Percolation.Bond.SmallTailMass
public import PercLib.Models.LongRange.PowerLawBinomialDerivative

/-!
# Power-law flux continuity and derivatives from gap factorization

At the sup-norm power law and on the interacting corner-free window `(5/4, 8/5)`, this module
constructs the finite window and rate bounds used by the small-tail interface. It derives local
small-tail control, whole-flux continuity and the binomial derivative from an explicit gap
factorization and finite high-temperature moments. It does not prove that factorization at positive
intensity, remove moment caps, prove sharpness or quantify over every cutoff radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-! ## The finite window and the rate bound, constructed

The abstract interfaces of `SmallTailMass` take a finite set `S` containing the lattice ball of
radius `v`, a real constant `Λ` bounding the rate `|β J'|` on the window, a finite top-scale
root moment `M`, the top-scale susceptibility `χ_v ≠ ⊤` and the finiteness of every inserted
`p`-th pivotal moment.  At the sup-norm power law on `(5/4, 8/5)` all five are constructed here:
the ball is contained in the integer box `{-1,0,1}^d`, the rate is monotone because the exponent
`-(d+α)-1` is negative, `M` is production's high-temperature root moment, `χ_v` follows from it,
and the inserted moments follow from the vertex moments. -/

/-- The sup-norm ball of radius `8/5` meets `Fin d → ℤ` inside the box `{-1,0,1}^d`. -/
theorem mem_Icc_of_powerLaw_norm_lt {d : ℕ} (z : Fin d → ℤ)
    (hz : normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) < 8 / 5) :
    ∀ i : Fin d, z i ∈ Finset.Icc (-1 : ℤ) 1 := by
  intro i
  have hz' : normSeminorm ℝ (Fin d → ℝ) (fun j : Fin d => (z j : ℝ)) < 8 / 5 := hz
  have h1 : ‖(z i : ℝ)‖ ≤ normSeminorm ℝ (Fin d → ℝ) (fun j : Fin d => (z j : ℝ)) := by
    simpa using norm_le_pi_norm (fun j : Fin d => (z j : ℝ)) i
  have h2 : |(z i : ℝ)| < 8 / 5 := by
    have h3 : ‖(z i : ℝ)‖ < 8 / 5 := lt_of_le_of_lt h1 hz'
    simpa using h3
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have h4 : (-2 : ℝ) < (z i : ℝ) := by
      have := (abs_lt.1 h2).1
      linarith
    have : (-2 : ℤ) < z i := by exact_mod_cast h4
    omega
  · have h4 : (z i : ℝ) < 2 := by
      have := (abs_lt.1 h2).2
      linarith
    have : z i < 2 := by exact_mod_cast h4
    omega

/-- A finite set containing the whole sup-norm ball of radius `8/5`. -/
theorem exists_finset_powerLaw_ball (d : ℕ) :
    ∃ S : Finset (Fin d → ℤ), ∀ z : Fin d → ℤ,
      normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) < 8 / 5 → z ∈ S := by
  have hfin : (Set.univ.pi (fun _ : Fin d => (Finset.Icc (-1 : ℤ) 1 : Set ℤ))).Finite :=
    Set.Finite.pi (fun _ => Finset.finite_toSet _)
  refine ⟨hfin.toFinset, fun z hz => hfin.mem_toFinset.mpr ?_⟩
  have h := mem_Icc_of_powerLaw_norm_lt z hz
  simp only [Set.mem_pi, Set.mem_univ]
  exact fun i _ => h i

/-- **The rate bound at the power law.** On `(5/4, 8/5)` the rate `|β J'|` of the sup-norm power
law is bounded by its value at the left endpoint, because `t ↦ t ^ (-(d+α)-1)` is decreasing. -/
theorem exists_powerLaw_rate_bound {d : ℕ} {α : ℝ} (hα : 0 < α) (β : ℝ≥0) :
    ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5),
      |(β : ℝ) * -((fun t : ℝ => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r)| ≤
        (β : ℝ) * ((d : ℝ) + α) * (5 / 4 : ℝ) ^ (-((d : ℝ) + α) - 1) := by
  intro r hr
  have hdr : (0 : ℝ) < (d : ℝ) + α := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hr0 : (0 : ℝ) < r := by linarith [hr.1]
  have hle : r ^ (-((d : ℝ) + α) - 1) ≤ (5 / 4 : ℝ) ^ (-((d : ℝ) + α) - 1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_lt hr.1) (by linarith)
  have hval : (β : ℝ) * -((fun t : ℝ => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) =
      (β : ℝ) * ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := by
    have : -((fun t : ℝ => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) =
        ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := by
      ring
    rw [this, mul_assoc]
  rw [hval, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hle (by positivity)


/-! ## The local small-tail estimate at the power law from the gap factorisation

The next theorem is the mass half of the derivative premise, `htail`, at the concrete sup-norm
power law on `(5/4, 8/5)`, with every auxiliary input constructed.  The hypothesis list is
`1 ≤ d`, `α > 0`, the high-temperature row-sum condition `β M < 1`, `p ≥ 1`, the gap constant
`C ≠ ⊤` and the gap factorisation `hfac` itself.  The window `S`, the rate bound `Λ`, the finite
top-scale root moment `M`, the susceptibility `χ_{8/5} ≠ ⊤` and the inserted pivotal moments are
all produced in the proof. -/
open Classical in
theorem exists_nhds_htail_powerLaw_of_factorization {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hfac : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
        (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) :
    ∀ r₀ ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ ε > 0, ∃ U ∈ 𝓝 r₀,
      ∃ F : Finset (Sym2 (Fin d → ℤ)), ∀ r ∈ U ∩ Ioo (5 / 4 : ℝ) (8 / 5),
        ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
          ‖((radialKernel (normSeminorm ℝ (Fin d → ℝ))
                (fun s => if s < r then 1 else 0) e.1 : ℝ) *
              ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
                  (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
                Real.exp (-(β : ℝ) *
                  (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                    (powerLawProfile 1 ((d : ℝ) + α)) r e.1 : ℝ)))) *
            ∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
              ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖ ≤ ε := by
  intro r₀ hr₀ ε hε
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  obtain ⟨M, hM, hroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ 0 p
    (u := 5 / 4) (v := 8 / 5) (R := 8 / 5) (by norm_num) (by norm_num)
  obtain ⟨M', hM', hroot'⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ 0
    (p - 1) (u := 5 / 4) (v := 8 / 5) (R := 8 / 5) (by norm_num) (by norm_num)
  have hK : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hχ : chi (intensityProfile (cutoffKernel (d := d) N.toSeminorm K (8 / 5)) β)
      (0 : Fin d → ℤ) ≠ ⊤ :=
    chi_cutoffKernel_ne_top_of_root_moment (N := N) (K := K) β p hM (by
      simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot (8 / 5) (Or.inr rfl))
  have hins : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β))) ≠ ⊤ := by
    intro r hr e
    have h1 : (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β))) ≠ ⊤ := by
      have h2 : (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ ((p - 1) + 1)
          ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β))) ≠ ⊤ :=
        ne_top_of_le_ne_top hM' (by
          simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot' r (Or.inl hr))
      simpa [Nat.sub_add_cancel hp] using h2
    have h3 : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β))) ≠ ⊤ :=
      fun y => vertex_moment_ne_top_of_root_moment (N := N) (K := K) β r p y h1
    exact insert_moments_of_vertex_moments (N := N.toSeminorm) (K := K) β p r 0 h3 e
  obtain ⟨S, hS⟩ := exists_finset_powerLaw_ball d
  have hS' : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < 8 / 5 → z ∈ S := by
    intro z hz
    have hz' : N.toSeminorm (Int.cast ∘ z) < 8 / 5 := hz
    exact hS z (by simpa only [N, ModelNorm.toSeminorm_ofNorm] using hz')
  have hfac' : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel N.toSeminorm (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β)))
        (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β))) := by
    intro r hr x y
    simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hfac r hr x y
  refine exists_nhds_htail_of_factorization (N := N) (K := K) (K' := K') β p hp
    (0 : Fin d → ℤ) _ (fun _ _ => rfl) hK hχ S hS' C hC
    ((β : ℝ) * ((d : ℝ) + α) * (5 / 4 : ℝ) ^ (-((d : ℝ) + α) - 1))
    (exists_powerLaw_rate_bound hα β) hins hfac' r₀ hr₀ ε hε


/-! ## Whole-series continuity at the power law, and the derivative at `r₀ = 3/2`

The remaining two theorems compose the local small-tail estimate above with production's
`continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail` and with
`hasDerivAt_powerLaw_three_halves_of_small_tail`.  Neither duplicates pair continuity: the
single-pair inputs stay inside production, and here the whole series over pairs is at stake. -/

open Classical in
/-- **Continuity of the whole pivotal flux series at the sup-norm power law.** On the
corner-free window `(5/4, 8/5)`, the flux series `∑_e cw r e · (pivotal moment at e)` is
continuous in the cutoff radius, given the gap factorisation `hfac`, a finite gap constant
`C`, and the high-temperature row-sum condition `β M < 1`.  Every other input of production's
continuity interface (the finite top-scale root moment, the susceptibility, the window set, the
rate bound, the inserted moments, the local small-tail estimate) is constructed here. -/
theorem continuousOn_flux_powerLaw_of_factorization {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hfac : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
        (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) :
    ContinuousOn (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(β : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo (5 / 4 : ℝ) (8 / 5)) := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  obtain ⟨M, hM, hroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ 0 p
    (u := 5 / 4) (v := 8 / 5) (R := 8 / 5) (by norm_num) (by norm_num)
  have hK : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t :=
    fun t ht => hasDerivAt_powerLawProfile_add 1 α ht
  have hK'c : ContinuousOn K' (Ioi 0) := continuousOn_powerLawProfile_deriv_add (d := d) 1 α
  have hcorner : ∀ z : Fin d → ℤ,
      normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) ∉ Ioo (5 / 4 : ℝ) (8 / 5) := by
    apply corner_free_of_forall_nat_notMem (d := d)
    intro m hm
    have h1 : (1 : ℝ) < (m : ℝ) := by linarith [hm.1]
    have h2 : (m : ℝ) < 2 := by linarith [hm.2]
    have h1' : 1 < m := by exact_mod_cast h1
    have h2' : m < 2 := by exact_mod_cast h2
    omega
  have hroot' : ∀ r ∈ (Ioo (5 / 4 : ℝ) (8 / 5) ∪ {(8 / 5 : ℝ)} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N.toSeminorm K r) β))) ≤ M := by
    intro r hr
    simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot r hr
  exact continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail (N := N) (K := K) (K' := K')
    hK hK' hK'c β p hp M hM _ (fun _ _ => rfl) (u := 5 / 4) (v := 8 / 5) (R := 8 / 5)
    (by norm_num) le_rfl hcorner hroot'
    (fun r₀ hr₀ ε hε => exists_nhds_htail_powerLaw_of_factorization hd hα hβ p hp C hC hfac
      r₀ hr₀ ε hε)

open Classical in
/-- **The power-law cutoff binomial derivative at `r₀ = 3/2` with the gap factorisation as the
only model input.** This replaces the small-tail premise of
`hasDerivAt_powerLaw_three_halves_of_small_tail` by `hfac` together with `C ≠ ⊤`, keeping the
high-temperature row-sum condition `β M < 1`.  No sharpness, no uncapped derivative and no
all-radius claim is made. -/
theorem hasDerivAt_powerLaw_three_halves_of_factorization {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hfac : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
        (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) (3 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (3 / 2)) β)))
      (3 / 2) :=
  hasDerivAt_powerLaw_three_halves_of_small_tail hd hα hβ p hp
    (exists_nhds_htail_powerLaw_of_factorization hd hα hβ p hp C hC hfac)


/-! ## Where the `min` in the gap factorisation really sits

`hfac` bounds the pivotal crossing mass by `C * min τ(x) τ(y)`.  Because `C` is an `ℝ≥0∞`
factor, this is *equivalent* to the conjunction of the two one-sided bounds `≤ C τ(x)` and
`≤ C τ(y)`; no loss and no extra hypothesis is involved.  This matters for the intended route:
a BK/FKG two-point estimate usually yields one side, and two one-sided estimates (one with the
root at `x`, one with the root translated to `y`) assemble `hfac` without any symmetrisation
argument. -/
theorem le_mul_min_iff {a b d c : ℝ≥0∞} :
    a ≤ c * min b d ↔ a ≤ c * b ∧ a ≤ c * d := by
  rw [mul_min, le_min_iff]

open Classical in
/-- `hfac` at the power law splits into two one-sided pair bounds, with the same constant. -/
theorem hfac_iff_oneSided_powerLaw {d : ℕ} {α : ℝ} {β : ℝ≥0} {p : ℕ} {C : ℝ≥0∞}
    {r : ℝ} :
    (∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
        (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) ↔
    (∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) ∧
    (∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) := by
  simp only [le_mul_min_iff, forall_and]

open Classical in
/-- Continuity at the single scale `r₀ = 3/2`, the scale of the printed derivative. -/
theorem continuousAt_flux_powerLaw_three_halves_of_factorization {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hfac : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ x y : Fin d → ℤ,
      ∫⁻ ω, (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) s(x, y) : ℝ≥0∞) *
        ((if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω (0 : Fin d → ℤ) then 0 else 1) *
          ((((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) +
              ((cluster ω y).encard : ℝ≥0∞)) ^ p -
            ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      C * min (∫⁻ ω, (if x ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
        (∫⁻ ω, (if y ∈ cluster ω (0 : Fin d → ℤ) then (1 : ℝ≥0∞) else 0)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)))) :
    ContinuousAt (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(β : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (3 / 2) :=
  (continuousOn_flux_powerLaw_of_factorization hd hα hβ p hp C hC hfac).continuousAt
    (isOpen_Ioo.mem_nhds (by norm_num))


open Classical in
/-- **The assembled conclusion at zero intensity, with no hypothesis.** At `β = 0` the weight of
every summand carries the factor `β`, so the whole flux series is the zero function and the
continuity statement of `continuousOn_flux_powerLaw_of_factorization` holds with no gap
factorisation, no high-temperature condition and no root moment.  This is the degenerate boundary
of the assembled chain: the gap factorisation is a *positive-intensity* input, while the
conclusion itself does not need it at `β = 0`. -/
theorem continuousOn_flux_powerLaw_beta_zero {d : ℕ} {α : ℝ} (p : ℕ) :
    ContinuousOn (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        (((0 : ℝ≥0) : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(((0 : ℝ≥0) : ℝ)) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) ((0 : ℝ≥0))))) (Ioo (5 / 4 : ℝ) (8 / 5)) := by
  have hzero : ∀ r : ℝ, (∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        (((0 : ℝ≥0) : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(((0 : ℝ≥0) : ℝ)) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) ((0 : ℝ≥0))))) = 0 := by
    intro r
    have hfun : (fun e : Sym2 (Fin d → ℤ) =>
        ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) e : ℝ) *
          (((0 : ℝ≥0) : ℝ) * -((fun t : ℝ => (1 : ℝ) *
              (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
            Real.exp (-(((0 : ℝ≥0) : ℝ)) *
              (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
        ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) ((0 : ℝ≥0))))) = fun _ => 0 := by
      funext e
      simp
    rw [hfun, tsum_zero]
  have hcont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo (5 / 4 : ℝ) (8 / 5)) :=
    continuousOn_const
  simpa only [hzero] using hcont

end PercLib.Models.LongRange
