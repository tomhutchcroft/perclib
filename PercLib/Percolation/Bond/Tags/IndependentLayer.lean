/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the ghost field and the independent-layer ghost comparisons. All
mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.IndependentLayer.AddedVolume
public import PercLib.Percolation.Bond.IndependentLayer.Conditional
public import PercLib.Percolation.Bond.IndependentLayer.OmittedMass

/-!
# Independent layers and the ghost field: correspondence

Wiki correspondence for the ghost field and the independent-layer ghost comparisons.

## Main results

* `ghost_field_magnetization`
* `ghost_comparison_omitted_edges`
* `ghost_bound_added_mass`
* `omitted_mass_negligible_of_regularlyVarying`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal unitInterval

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The ghost field: for `h > 0` and marks of density `p` with `1 - p = e^{-h}`, the
magnetization `P(K_x ∩ 𝒢_h ≠ ∅)` equals the ghost transform `E[1 - e^{-h|K_x|}]`, with
`e^{-h∞} = 0`; at `h = 0` the mark set is empty almost surely, so `M(0) = 0`. -/
@[tag "VF24"]
theorem ghost_field_magnetization [Countable V] (q : Sym2 V → I) (x : V) :
    (∀ h : ℝ, 0 < h → ∀ p : I, ((σ p : I) : ℝ) = Real.exp (-h) →
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω x).encard : ℝ≥0∞) : EReal))))
          ∂(law q) =
        ((law q).prod (prodBernoulli fun _ : V => p))
          {y | (cluster y.1 x ∩ y.2).Nonempty}) ∧
    ((law q).prod (prodBernoulli fun _ : V => (0 : I)))
      {y | (cluster y.1 x ∩ y.2).Nonempty} = 0 := by
  refine ⟨fun h hh p hp => lintegral_cluster_one_sub_exp_eq_prod q x hh hp, ?_⟩
  have hmarks : prodBernoulli (fun _ : V => (0 : I)) {g : Set V | g.Nonempty} = 0 := by
    have he : {g : Set V | g.Nonempty} = ⋃ v, {g : Set V | v ∈ g} := by
      ext g
      simp [Set.Nonempty]
    rw [he]
    refine measure_iUnion_null fun v => ?_
    rw [prodBernoulli_setOf_mem]
    simp
  refine measure_mono_null (t := univ ×ˢ {g : Set V | g.Nonempty}) ?_ ?_
  · rintro y ⟨v, hv⟩
    exact ⟨mem_univ _, v, hv.2⟩
  · rw [Measure.prod_prod, hmarks, mul_zero]

open Classical in
/-- The omitted-edge ghost comparison `M₀(h) ≤ M_o(h) ≤ M₀(h) + δ E[X e^{-hX}] M*(h)`;
under a transitive full profile `M* = M_o` and the error is multiplicative. -/
@[tag "FJWB"]
theorem ghost_comparison_omitted_edges [Countable V] (q : Sym2 V → I) (E₀ : Set (Sym2 V))
    (o : V) {h : ℝ} (hh : 0 < h)
    (hfin : ∀ᵐ ω ∂(law fun e => if e ∈ E₀ then q e else 0), (cluster ω o).Finite)
    {δ : ℝ≥0∞} (hδ : ∀ u, (∑' w, if w = u ∨ s(u, w) ∈ E₀ then 0 else
      (unitInterval.toNNReal (q s(u, w)) : ℝ≥0∞)) ≤ δ) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law fun e => if e ∈ E₀ then q e else 0) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q) ∧
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law q) ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law fun e => if e ∈ E₀ then q e else 0) +
        δ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
          EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))
            ∂(law fun e => if e ∈ E₀ then q e else 0)) *
        ⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
          ∂(law q)) ∧
    ((∀ x y : V, ∃ τ : V ≃ V, τ x = y ∧ ∀ e, q (Sym2.map τ e) = q e) →
      (⨆ v, ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω v).encard : ℝ≥0∞) : EReal))))
          ∂(law q)) =
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law q) ∧
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law q) ≤
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
            ∂(law fun e => if e ∈ E₀ then q e else 0) +
          δ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) *
            EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal)))
              ∂(law fun e => if e ∈ E₀ then q e else 0)) *
          ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
            ∂(law q)) := by
  refine ⟨lintegral_ghost_cutoff_le q E₀ o hh hfin hδ, fun hT => ⟨?_,
    lintegral_ghost_cutoff_le_of_transitive q hT E₀ o hh hfin hδ⟩⟩
  have : Nonempty V := ⟨o⟩
  simp_rw [lintegral_ghost_eq_of_transitive q hT h o]
  exact ciSup_const

/-- The ghost bound for the mass gained from an independent layer: the conditional
estimate `E[(1 - e^{-h|D|}) f(C)] ≤ E[min(1, a M*(h) |C|) f(C)]` for every measurable
`f ≥ 0` of `C`, and the tail `P(|D| ≥ t) ≤ E min(1, a M*(h) |C|) / (1 - e^{-ht})` for
real `t > 0`. -/
@[tag "AYPN"]
theorem ghost_bound_added_mass [Countable V] (q₀ s : Sym2 V → I) (o : V) {h : ℝ}
    (hh : 0 < h) (hfin : ∀ᵐ ω ∂(law q₀), (cluster ω o).Finite) {a : ℝ≥0∞}
    (ha : ∀ u, rowSum (fun e => unitInterval.toENNReal (s e)) u ≤ a) :
    (∀ (f : Set V → ℝ≥0∞), Measurable (fun ω : Config V => f (cluster ω o)) →
      ∫⁻ x, (1 - EReal.exp (-((h : EReal) *
          (((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞) : EReal)))) *
          f (cluster x.1 o) ∂((law q₀).prod (law s)) ≤
        ∫⁻ ω, min 1 (a * (⨆ v, ∫⁻ ω', (1 - EReal.exp (-((h : EReal) *
            (((cluster ω' v).encard : ℝ≥0∞) : EReal)))) ∂(law fun e => σ (σ (q₀ e) * σ (s e)))) *
            (cluster ω o).encard) * f (cluster ω o) ∂(law q₀)) ∧
    (∀ t : ℝ, 0 < t →
      ((law q₀).prod (law s))
          {x | (t : EReal) ≤ (((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞) : EReal)} ≤
        (∫⁻ ω, min 1 (a * (⨆ v, ∫⁻ ω', (1 - EReal.exp (-((h : EReal) *
            (((cluster ω' v).encard : ℝ≥0∞) : EReal)))) ∂(law fun e => σ (σ (q₀ e) * σ (s e)))) *
            (cluster ω o).encard) ∂(law q₀)) /
          (1 - ENNReal.ofReal (Real.exp (-h * t)))) := by
  refine ⟨fun f hf => lintegral_ghost_added_mul_le q₀ s o hh hfin ha f hf, fun t ht => ?_⟩
  set n : ℕ := ⌈t⌉₊ with hn
  have htail := law_added_volume_ge_mul_le q₀ s o hh hfin ha (n : ℕ∞)
  -- the real event is contained in the integer event at `⌈t⌉₊`
  have hsub : {x : Config V × Config V |
      (t : EReal) ≤ (((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞) : EReal)} ⊆
      {x | (n : ℕ∞) ≤ (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    generalize (cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard = k at hx ⊢
    induction k using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      have hk : (t : EReal) ≤ ((k : ℝ) : EReal) := by simpa using hx
      have hk' : t ≤ (k : ℝ) := EReal.coe_le_coe_iff.mp hk
      exact_mod_cast Nat.ceil_le.mpr hk'
  -- the denominators
  have hexp : EReal.exp (-((h : EReal) * (((n : ℕ∞) : ℝ≥0∞) : EReal))) ≤
      ENNReal.ofReal (Real.exp (-h * t)) := by
    rw [exp_neg_mul_natCast, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : t ≤ (n : ℝ) := Nat.le_ceil t
    nlinarith
  have hlt : ENNReal.ofReal (Real.exp (-h * t)) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
    nlinarith
  have hb0 : 1 - ENNReal.ofReal (Real.exp (-h * t)) ≠ 0 := (tsub_pos_of_lt hlt).ne'
  have hbt : 1 - ENNReal.ofReal (Real.exp (-h * t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt)]
  refine le_trans ?_ htail
  rw [mul_comm]
  gcongr

/-- A regularly varying volume tail makes omitted cluster mass negligible: for a transitive
profile `q` with a.s. finite root cluster volume `X` and `F t = P(X > t)` regularly varying
of index `-ρ`, `0 < ρ < 1`, scales `z_R → ∞`, normalizers `η_R ≍ F(z_R)`, lower profiles
coupled to `q` by independent layers with rows `a_{R,s}` and
`limsup_R a_{R,s} z_R η_R ≤ b(s) → 0`, for every `δ > 0`,
`lim_{s → ∞} limsup_R η_R⁻¹ P(|K \ C_{R,s}| ≥ δ z_R) = 0`. -/
@[tag "L9YJ"]
theorem omitted_mass_negligible_of_regularlyVarying [Countable V] (q : Sym2 V → I) (o : V)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hT : ∀ x y : V, ∃ τ : V ≃ V, τ x = y ∧ ∀ e, q (Sym2.map τ e) = q e)
    (hfin : ∀ᵐ ω ∂(law q), (cluster ω o).Finite)
    (hrv : PercLib.Analysis.RegularlyVarying (-ρ) fun t =>
      (law q {ω | ENNReal.ofReal t < ((cluster ω o).encard : ℝ≥0∞)}).toReal)
    {ι : Type*} {l : Filter ι} {z η : ι → ℝ} (hz : Filter.Tendsto z l Filter.atTop)
    (hη : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ R in l,
      c * (law q {ω | ENNReal.ofReal (z R) < ((cluster ω o).encard : ℝ≥0∞)}).toReal ≤ η R ∧
      η R ≤ C * (law q {ω | ENNReal.ofReal (z R) < ((cluster ω o).encard : ℝ≥0∞)}).toReal)
    (q₀ s' : ι → ℝ → Sym2 V → I) (a : ι → ℝ → ℝ≥0∞) (b : ℝ → ℝ)
    (hq : ∀ R s, 1 ≤ s → (fun e => σ (σ (q₀ R s e) * σ (s' R s e))) = q)
    (ha : ∀ R s, 1 ≤ s → ∀ u, rowSum (fun e => unitInterval.toENNReal (s' R s e)) u ≤ a R s)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (hab : ∀ s, 1 ≤ s →
      Filter.limsup (fun R => a R s * ENNReal.ofReal (z R * η R)) l ≤ ENNReal.ofReal (b s))
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun s => Filter.limsup (fun R => (ENNReal.ofReal (η R))⁻¹ *
        ((law (q₀ R s)).prod (law (s' R s)))
          {x | ENNReal.ofReal (δ * z R) ≤
            ((cluster (x.1 ∪ x.2) o \ cluster x.1 o).encard : ℝ≥0∞)}) l)
      Filter.atTop (nhds 0) :=
  tendsto_limsup_law_added_volume_ge q o hρ0 hρ1 hT hfin hrv hz hη q₀ s' a b hq ha hb hab hδ

end PercLib.Percolation.Bond
