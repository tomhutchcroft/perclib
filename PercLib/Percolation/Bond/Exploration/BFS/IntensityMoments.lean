/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file `PercLib/CriticalLRP/IntensityMoments.lean`;
added at source revision `95248147f2fcfeb9c2666c706089d86ee17887a6`, unchanged at branch head
`1a4906a25965de1bf9440b0af188deb0420c03a6` (blob `de8a9ffc08db60a45674356694d069cb507c3e71`);
the underlying full-row power-law bound is adapted from `PercLib/CriticalLRP/PowerLawHighTemp.lean`
at source revision `6953cfc748205d5589dd0ed17f79afff0d44b2d7`. Both source files carry the
Apache-2.0 licence. Canonical namespace prefix:
`PercLib.Percolation.Bond.Exploration.BFS`. This is a proof-only module: it introduces no
definition and no alternative configuration model.

Source-linter changes, all cosmetic or interface-forced:

* the forbidden `set_option autoImplicit false` was removed (the lakefile sets
  `autoImplicit = false` for the package);
* the global `attribute [local instance] Classical.propDecidable` was replaced by local
  `classical`;
* the row-sum hypothesis is written with the canonical `PercLib.Percolation.Bond.rowSum`
  (`rowSum a v = ∑' w, if w = v then 0 else a s(v,w)`, definitionally the source's explicit
  `∑' w, if w = v then 0 else …`);
* the source's `clusterVol` abbreviation is unfolded to `((cluster ω o).encard : ℝ≥0∞)`:
  `clusterVol` lives in `PercLib.CriticalLRP.CountableProduct.Base`, which is not part of the
  canonical bond interface yet, and `clusterVol_eq_encard` there is `rfl`, so this is the same
  statement, not a weakening;
* the source's `linfNorm` is the `ℕ`-valued sup norm on `ℤ^d`; the canonical library writes that
  sup norm as `‖z‖` (`PercLib.Models.LongRange.norm_le_natCast_iff` has the same universal
  property as the source's `linfNorm_le_iff`), so the power-law intensity is written with `‖·‖`;
* `PercLib.CriticalLRP.PowerLawHighTemp.power_rowSum_le` is not landed; the lemma of that name
  below re-proves the same statement from `PercLib.Models.TranslationInvariant` and
  `PercLib.Models.LongRange.PowerLaw` so that the last theorem stays unconditional.
-/
module

public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.Exploration.BFS.HighTemperature.Moment.Natural
public import PercLib.Models.TranslationInvariant
public import PercLib.Models.LongRange.PowerLaw

/-!
# Natural cluster moments for high-temperature intensity profiles

Apply the BFS exponential and polynomial cluster-moment bounds to the intensity-parameter
interface `intensityProfile J β` and its law `law (intensityProfile J β) = prodBernoulli _`.
This is high-temperature content at `β M < 1`: nothing here is a statement about the critical
parameter, about sharpness, or about a cutoff law.

The chain is the source one: a row bound `M` on the off-diagonal intensities gives the real
row bound `m = (β M).toReal ∈ [0,1)`, an admissible `λ > 1` with `λ u_n ≤ C` for the envelope,
the exponential cluster moment `E[λ^{|K_o|}] ≤ C`, almost sure finiteness of the cluster, and
finally each natural moment `E[|K_o|^k] < ∞`. Only on the a.e.-finite event is `encard.toNat`
used; the extended moment itself is the `ℝ≥0∞`-valued `((cluster ω o).encard) ^ k`, so no
finite-box or `ncard` substitute enters.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability PercLib.Probability.ExplorationEnvelope
open scoped ENNReal NNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- On a finite cluster, the real power of `encard.toNat` is the natural power in the
usual `ℝ≥0∞` cluster-volume normalization. -/
theorem ofReal_encard_toNat_pow (s : Set V) (hfin : s.encard ≠ ⊤) (k : ℕ) :
    ENNReal.ofReal ((s.encard.toNat : ℝ) ^ k) = ((s.encard : ℝ≥0∞) ^ k) := by
  have hbase : ENNReal.ofReal (s.encard.toNat : ℝ) = (s.encard : ℝ≥0∞) := by
    calc ENNReal.ofReal (s.encard.toNat : ℝ) = (s.encard.toNat : ℝ≥0∞) :=
          ENNReal.ofReal_natCast _
      _ = (s.encard : ℝ≥0∞) := congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) (ENat.natCast_toNat hfin)
  calc ENNReal.ofReal ((s.encard.toNat : ℝ) ^ k)
      = (ENNReal.ofReal (s.encard.toNat : ℝ)) ^ k :=
        ENNReal.ofReal_pow (by positivity : 0 ≤ (s.encard.toNat : ℝ)) k
    _ = (s.encard : ℝ≥0∞) ^ k := by rw [hbase]

/-- The usual intensity-row bound supplies the finite-partial real row bound used by the
BFS high-temperature theorem, on the actual `law`/`prodBernoulli` measure. -/
theorem uniformRowBound_intensityProfile [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    UniformRowBound (intensityProfile J β) ((β : ℝ≥0∞) * M).toReal := by
  classical
  have hprod : ((β : ℝ≥0∞) * M) ≠ ⊤ :=
    ne_top_of_lt (hβ.trans_le le_top)
  have hM0 : 0 ≤ (((β : ℝ≥0∞) * M).toReal) := ENNReal.toReal_nonneg
  intro x t hx
  rw [← ENNReal.ofReal_le_ofReal_iff hM0]
  calc ENNReal.ofReal (∑ y ∈ t, ((intensityProfile J β s(x,y)) : ℝ))
      = ∑ y ∈ t, ENNReal.ofReal ((intensityProfile J β s(x,y)) : ℝ) :=
        ENNReal.ofReal_sum_of_nonneg (fun y _ => (intensityProfile J β s(x,y)).2.1)
    _ = ∑ y ∈ t, (if y = x then 0 else
          unitInterval.toENNReal (intensityProfile J β s(x,y))) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hyx : y ≠ x := by
        intro h
        exact hx (h ▸ hy)
      rw [ite_eq_right hyx, ← unitInterval_toNNReal_coe (intensityProfile J β) (s(x,y)),
        unitInterval.toENNReal_apply]
    _ ≤ ∑' y : V, (if y = x then 0 else
          unitInterval.toENNReal (intensityProfile J β s(x,y))) := ENNReal.sum_le_tsum t
    _ = rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) x := by
        rw [rowSum_def]
    _ ≤ (β : ℝ≥0∞) * M := intensity_rowSum_le J M hJ β x
    _ = ENNReal.ofReal (((β : ℝ≥0∞) * M).toReal) :=
        (ENNReal.ofReal_toReal hprod).symm

/-- The intensity budget is strictly below one in the real form used by the envelope. -/
theorem intensity_toReal_mul_lt_one (M : ℝ≥0) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * M < 1) : (((β : ℝ≥0∞) * M).toReal) < 1 := by
  refine (ENNReal.toReal_lt_toReal ?_ ENNReal.one_ne_top).2 hβ
  exact ne_top_of_lt (hβ.trans_le le_top)

variable [Countable V]

/-- A unified admissible scalar envelope for a high-temperature intensity profile,
including the zero-row-budget case. -/
theorem exists_lam_envelope_intensityProfile (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    ∃ lam C : ℝ, 1 < lam ∧
      ∀ n : ℕ, lam * envelope (((β : ℝ≥0∞) * M).toReal) lam n ≤ C := by
  classical
  let m := ((β : ℝ≥0∞) * M).toReal
  have hrow : UniformRowBound (intensityProfile J β) m :=
    uniformRowBound_intensityProfile J M hJ β hβ
  have hm1 : m < 1 := intensity_toReal_mul_lt_one M hβ
  by_cases hm : m = 0
  · refine ⟨2, 2, by norm_num, ?_⟩
    intro n
    have hu : ∀ n : ℕ, envelope m (2 : ℝ) n = 1 := by
      intro k
      induction k with
      | zero => rw [envelope_zero]
      | succ k ih =>
          rw [envelope_succ, envelopeStep, ih, hm]
          norm_num
    rw [hu n]
    norm_num
  · have hmpos : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm)
    obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hmpos hm1
    refine ⟨lam, 1 / m, hlam, fun n => ?_⟩
    have hu := envelope_le_inv_mul hmpos hm1.le hlam.le hcond n
    have hpos : 0 < m * lam := by positivity
    calc lam * envelope m lam n ≤ lam * (1 / (m * lam)) :=
          mul_le_mul_of_nonneg_left hu (by linarith)
      _ = 1 / m := by field_simp

/-- Every natural cluster-volume moment is finite under an explicit high-temperature
intensity-row bound.  The actual law is `law (intensityProfile J β)`, i.e.
`prodBernoulli (intensityProfile J β)` definitionally.  The source's `clusterVol ω o` is the
`ℝ≥0∞`-valued `((cluster ω o).encard : ℝ≥0∞)`; it is written out here because `clusterVol` is
not yet part of the canonical interface, and `clusterVol_eq_encard` is `rfl`. -/
theorem lintegral_clusterVol_intensity_pow_ne_top (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (o : V) (k : ℕ) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) ≠ ⊤ := by
  classical
  let m := ((β : ℝ≥0∞) * M).toReal
  have hrow : UniformRowBound (intensityProfile J β) m :=
    uniformRowBound_intensityProfile J M hJ β hβ
  obtain ⟨lam, C, hlam, hC⟩ := exists_lam_envelope_intensityProfile J M hJ β hβ
  have hexp := lintegral_epow_cluster_le_of_envelope_bound hrow (lam := lam) o hlam.le hC
  have hfin : ∀ᵐ ω ∂(law (intensityProfile J β)), (cluster ω o).encard ≠ ⊤ :=
    ae_encard_cluster_ne_top_of_epow_le hlam hexp
  have hmom := lintegral_pow_encard_cluster_le hrow (lam := lam) o hlam hC k
  apply ne_of_lt
  calc ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β))
      = ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k)
          ∂(law (intensityProfile J β)) := by
        apply lintegral_congr_ae
        filter_upwards [hfin] with ω hω
        exact (ofReal_encard_toNat_pow (cluster ω o) hω k).symm
    _ ≤ ENNReal.ofReal (C * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := hmom
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ### The power-law profile on `ℤ^d`

The two statements of this section are the source's power-law corollary.  The source reached
them through `PercLib.CriticalLRP.PowerLawHighTemp.power_rowSum_le`, which is not landed in the
canonical library; the row-sum bound is therefore re-proved here from
`PercLib.Models.TranslationInvariant.rowSum_le_tsum_of_translationInvariant` and the summability
of the power-law profile in `PercLib.Models.LongRange.PowerLaw`.  It is the same statement as
the source's, with the source's `linfNorm` written as the sup norm `‖·‖`. -/

/-- Port of `PercLib.CriticalLRP.PowerLawHighTemp.power_rowSum_le`: the full row of the
power-law intensity on `ℤ^d` (the diagonal included, as in the source statement) is at most the
total profile mass.  The off-diagonal form used below follows by dropping the diagonal term. -/
theorem power_rowSum_le {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    (v : Fin d → ℤ) :
    (∑' w : Fin d → ℤ, (J s(v, w) : ℝ≥0∞)) ≤
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hs0 : 0 < s := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hne : -s ≠ 0 := by linarith
  have hsum_ite : Summable
      (fun z : Fin d → ℤ => if z = 0 then (0 : ℝ) else ‖z‖ ^ (-((d : ℝ) + (s - d)))) :=
    (PercLib.Models.LongRange.summable_powerLaw_iff hd (s - d)).2 (by linarith)
  have hexp : -((d : ℝ) + (s - d)) = -s := by ring
  have hsum : Summable (fun z : Fin d → ℤ => (‖z‖ : ℝ) ^ (-s)) := by
    refine hsum_ite.congr fun z => ?_
    rw [hexp]
    rcases eq_or_ne z 0 with h | h
    · subst h
      simp [Real.zero_rpow hne]
    · rw [ite_eq_right h]
  have hmass : (∑' z : Fin d → ℤ, ((Real.toNNReal ((‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞))
      = ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
    have hterm : ∀ z : Fin d → ℤ,
        ((Real.toNNReal ((‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞)
          = ENNReal.ofReal ((‖z‖ : ℝ) ^ (-s)) := by
      intro z
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (Real.rpow_nonneg (norm_nonneg z) _)]
    rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg
      (fun z => Real.rpow_nonneg (norm_nonneg z) _) hsum,
      ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (tsum_nonneg fun z =>
        Real.rpow_nonneg (norm_nonneg z) _)]
  have hstep : (∑' w : Fin d → ℤ, (J s(v, w) : ℝ≥0∞))
      = ∑' z : Fin d → ℤ, ((Real.toNNReal ((‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
    rw [← (Equiv.addRight v).tsum_eq (fun w => (J s(v, w) : ℝ≥0∞))]
    refine tsum_congr fun z => ?_
    simp only [Equiv.coe_addRight]
    rw [hJ v (z + v), add_sub_cancel_right]
  rw [hstep, hmass]

/-- The natural moments under a compact nonzero interval of high-temperature
power-law intensities.  No statement at criticality is made. -/
theorem power_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) ≠ ⊤ := by
  classical
  let M : ℝ≥0 := Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s))
  have hrows : ∀ v : Fin d → ℤ, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M := by
    intro v
    rw [rowSum_def]
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (power_rowSum_le hd hs hJ v)
  exact lintegral_clusterVol_intensity_pow_ne_top J M hrows β hβ x k

end PercLib.Percolation.Bond.Exploration.BFS
