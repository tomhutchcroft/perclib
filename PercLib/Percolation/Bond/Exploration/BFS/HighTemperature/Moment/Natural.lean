/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/HighTemperature/Moment/Natural.lean`; added at source revision
`c873e4ed349df275ed90c207de553a8a34f98101`, supplied under its Apache-2.0 header. Canonical
namespace prefix: `PercLib.Percolation.Bond.Exploration.BFS`. This is a proof-only module. Local
`classical` tactics replace a global
opening; source task labels, forbidden options and raw axiom-print commands were omitted.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.HighTemperature.Moment.Cluster
public import PercLib.Probability.Exploration.MomentBound

/-!
# natural cluster moments from the exponential bound

A finite exponential moment forces the cluster cardinality to be almost surely finite. Only
on that event is `encard.toNat` meaningful; the scalar factorial-logarithm estimate then bounds
every natural cluster moment. Natural-moment constants are `k! / (m * (log lam)^k)` and do not
depend on the root. The actual `ℝ≥0∞` extended cluster moment is established separately below
these ordinary-power consequences.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open PercLib.Probability.ExplorationEnvelope
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*} [Countable V]

/-- **An exponential moment bound forces the cluster to be a.s. finite.** -/
theorem ae_encard_cluster_ne_top_of_epow_le {μ : Measure (Config V)} {o : V} {lam C : ℝ}
    (hlam : 1 < lam)
    (hint : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂μ ≤ ENNReal.ofReal C) :
    ∀ᵐ ω ∂μ, (cluster ω o).encard ≠ ⊤ := by
  have hmeas : Measurable fun ω : Config V => (cluster ω o).encard :=
PercLib.Percolation.Bond.measurable_encard_cluster o
  have hlt : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hint
  have hae := ae_lt_top ((measurable_epow _).comp hmeas) hlt
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by linarith : (0:ℝ) < lam)]
    exact hlam
  filter_upwards [hae] with ω hω htop
  simp only [Function.comp_apply] at hω
  rw [htop, epow_top_of_one_lt _ h1] at hω
  exact absurd hω (not_lt.mpr le_top)

/-- **The scalar transfer of `PROOF.md` Lemma 6.1.**  From `E[λ^{|K_o|}] ≤ C` and `λ > 1`,
every natural moment of the cluster volume is at most `C k! / (log λ)^k`. -/
theorem lintegral_pow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ} (hrow :
UniformRowBound p m)
    (o : V) {lam C : ℝ} (hlam : 1 < lam)
    (hC : ∀ n : ℕ, lam * envelope m lam n ≤ C) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (C * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := by
  have hlog : 0 < Real.log lam := Real.log_pos hlam
  have hc0 : (0:ℝ) ≤ (k.factorial : ℝ) / (Real.log lam) ^ k := by positivity
  have hint : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal C :=
    lintegral_epow_cluster_le_of_envelope_bound hrow o hlam.le hC
  have hae := ae_encard_cluster_ne_top_of_epow_le hlam hint
  have hpt : ∀ᵐ ω ∂(prodBernoulli p),
      ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k)
        ≤ ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k)
            * epow (ENNReal.ofReal lam) ((cluster ω o).encard) := by
    filter_upwards [hae] with ω hω
    have hx : (0:ℝ) ≤ ((cluster ω o).encard.toNat : ℝ) := by positivity
    have h1 := pow_le_factorial_div_log_mul_rpow hlam k hx
    have hpow : epow (ENNReal.ofReal lam) ((cluster ω o).encard)
        = ENNReal.ofReal (lam ^ ((cluster ω o).encard.toNat : ℝ)) := by
      conv_lhs => rw [← ENat.natCast_toNat hω]
      rw [epow_ofReal_pow hlam.le, Real.rpow_natCast]
    rw [hpow, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal h1
  refine le_trans (lintegral_mono_ae hpt) ?_
  have hmeas : Measurable fun ω : Config V => epow (ENNReal.ofReal lam) ((cluster ω o).encard) :=
    (measurable_epow _).comp (PercLib.Percolation.Bond.measurable_encard_cluster o)
  rw [lintegral_const_mul _ hmeas]
  refine le_trans (mul_le_mul' le_rfl hint) ?_
  exact le_of_eq (by
    rw [mul_comm C ((k.factorial : ℝ) / (Real.log lam) ^ k)]
    exact (ENNReal.ofReal_mul hc0).symm)

/-- **The natural cluster moments with the explicit envelope constant `1 / m`.** -/
theorem lintegral_pow_encard_cluster_le_inv_mul {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := by
  refine lintegral_pow_encard_cluster_le hrow o hlam (C := 1 / m) (fun n => ?_) k
  have hu : envelope m lam n ≤ 1 / (m * lam) := envelope_le_inv_mul hm hm1 hlam.le hcond n
  have hpos : (0:ℝ) < m * lam := by nlinarith
  have h1 : lam * envelope m lam n ≤ lam * (1 / (m * lam)) :=
    mul_le_mul_of_nonneg_left hu (by linarith)
  have h2 : lam * (1 / (m * lam)) = 1 / m := by field_simp
  linarith [h1, h2.le]

/-- **The natural cluster moments, `m = 0`.** -/
theorem lintegral_pow_encard_cluster_le_zero {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : m = 0) (o : V) {lam : ℝ} (hlam : 1 < lam) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (lam * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := by
  refine lintegral_pow_encard_cluster_le hrow o hlam (C := lam) (fun n => ?_) k
  rw [hm]
  induction n with
  | zero => rw [envelope_zero]; linarith
  | succ n ih =>
      rw [envelope_succ, envelopeStep]
      simp only [zero_mul, Real.exp_zero]
      exact le_of_eq (mul_one lam)


/-! ### An admissible parameter exists -/

/-- **Theorem 1 of `PROOF.md`, exponential form.**  For `0 < m < 1` there is `λ > 1` with a
uniform exponential cluster moment bound. -/
theorem exists_lam_lintegral_epow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) :
    ∃ lam : ℝ, 1 < lam ∧
      ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal (1 / m) := by
  obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, lintegral_epow_encard_cluster_le_inv_mul hrow o hlam.le hm hm1.le hcond⟩

/-- **Theorem 2 of `PROOF.md`, moment form.**  For `0 < m < 1` and every `k` there is `λ > 1`
with `E[|K_o|^k] ≤ k! / (m (log λ)^k)` uniformly in the root. -/
theorem exists_lam_lintegral_pow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) (k : ℕ) :
    ∃ lam : ℝ, 1 < lam ∧
      ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) := by
  obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hm hm1
  refine ⟨lam, hlam, ?_⟩
  refine (lintegral_pow_encard_cluster_le_inv_mul hrow o hlam hm hm1.le hcond k).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hlogk : Real.log lam ≠ 0 := ne_of_gt (Real.log_pos hlam)
  have hmeq : (1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)
      = (k.factorial : ℝ) / (m * (Real.log lam) ^ k) := by
    field_simp
  exact hmeq.le

/-! ### Root-uniform consequences, with one admissible `λ` shared by every root -/

/-- There is one admissible `λ > 1` that bounds the exponential moment of the true cluster
at every root. This is the uniform form of the exponential-moment theorem, rather than
choosing a possibly different `λ` separately for each root. -/
theorem exists_lam_forall_lintegral_epow_encard_cluster_le {V : Type*} [Countable V]
    {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ o : V,
      ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal (1 / m) := by
  obtain ⟨lam, hlam, hcond⟩ :=
    PercLib.Probability.ExplorationEnvelope.exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, fun o =>
    lintegral_epow_encard_cluster_le_inv_mul hrow o hlam.le hm hm1.le hcond⟩

/-- One admissible `λ > 1` gives the factorial-logarithm bound at every root and every order.
The finite-cardinality hypothesis is proved almost surely, not silently assumed for `toNat`. -/
theorem exists_lam_forall_lintegral_pow_encard_cluster_le {V : Type*} [Countable V]
    {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ (o : V) (k : ℕ),
      ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) := by
  obtain ⟨lam, hlam, hcond⟩ :=
    PercLib.Probability.ExplorationEnvelope.exists_admissible_lambda hm hm1
  refine ⟨lam, hlam, fun o k => ?_⟩
  refine (lintegral_pow_encard_cluster_le_inv_mul hrow o hlam hm hm1.le hcond k).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hlogk : Real.log lam ≠ 0 := ne_of_gt (Real.log_pos hlam)
  have hmeq : (1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)
      = (k.factorial : ℝ) / (m * (Real.log lam) ^ k) := by
    field_simp
  exact hmeq.le

/-- For `0 < m < 1`, the true cluster is almost surely finite at every root. -/
theorem ae_encard_cluster_ne_top {V : Type*} [Countable V]
    {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) :
    ∀ o : V, ∀ᵐ ω ∂(prodBernoulli p), (cluster ω o).encard ≠ ⊤ := by
  obtain ⟨lam, hlam, hforall⟩ :=
    exists_lam_forall_lintegral_epow_encard_cluster_le hrow hm hm1
  intro o
  exact ae_encard_cluster_ne_top_of_epow_le hlam (hforall o)

/-- The exponential moment of the actual finite cluster cardinality is bounded by `1/m`
for a single admissible `λ > 1` shared by every root. -/
theorem lintegral_rpow_encard_cluster_le {V : Type*} [Countable V]
    {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ ∀ o : V,
      ∫⁻ ω, ENNReal.ofReal (lam ^ ((cluster ω o).encard.toNat : ℝ)) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal (1 / m) := by
  obtain ⟨lam, hlam, hforall⟩ :=
    exists_lam_forall_lintegral_epow_encard_cluster_le hrow hm hm1
  refine ⟨lam, hlam, fun o => ?_⟩
  have hcongr : ∫⁻ ω, ENNReal.ofReal (lam ^ ((cluster ω o).encard.toNat : ℝ)) ∂(prodBernoulli p)
      = ∫⁻ ω, (ENNReal.ofReal lam) ^ (((cluster ω o).encard.toNat : ℕ) : ℝ)
          ∂(prodBernoulli p) := by
    refine lintegral_congr (fun ω => ?_)
    refine (ENNReal.ofReal_rpow_of_nonneg (le_of_lt (by linarith : (0 : ℝ) < lam))
      (by positivity)).symm
  rw [hcongr, ← lintegral_epow_eq_of_ae_finite (prodBernoulli p) o (ENNReal.ofReal lam)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlam.le)
    (ae_encard_cluster_ne_top hrow hm hm1 o)]
  exact hforall o


/-! ### Interoperability with the diagonal-inclusive `RowSum` -/

/-- `RowSum`-flavoured exponential moment (row sums including the diagonal). -/
theorem lintegral_epow_encard_cluster_le_inv_mul_rowSum {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : RowSum p m) (o : V) {lam : ℝ} (hlam : 1 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (1 / m) :=
  lintegral_epow_encard_cluster_le_inv_mul (uniformRowBound_of_rowSum hrow) o hlam hm hm1 hcond

/-- `RowSum`-flavoured natural moments (row sums including the diagonal). -/
theorem lintegral_pow_encard_cluster_le_inv_mul_rowSum {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : RowSum p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)) :=
  lintegral_pow_encard_cluster_le_inv_mul (uniformRowBound_of_rowSum hrow) o hlam hm hm1 hcond k


end PercLib.Percolation.Bond.Exploration.BFS
