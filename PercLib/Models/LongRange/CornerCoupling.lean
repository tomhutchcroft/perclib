/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5. The coupling below supplies inputs to continuity analysis; it does not by itself
assert continuity or differentiability of the root moment.
-/
module

public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Models.LongRange.CornerCoupling.Defs
public import PercLib.Models.LongRange.CutoffCorner
public import PercLib.Models.LongRange.UncappedMomentContinuity
public import PercLib.Probability.Superposition
public import PercLib.Probability.ClosedProduct
public import PercLib.Probability.CapMoment
public import PercLib.Percolation.Bond.ClosedCertificates

/-!
# The uniform softened-edge coupling and its change bound

The actual cut-off law on an interval between consecutive integer radii is identified with an
independent union of old and reopened configurations. A cluster changes only when a reopened
edge touches it. The resulting probability estimate uses the base susceptibility and a finite
sup-norm ball count on the full lattice.
-/

@[expose] public section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open scoped ENNReal NNReal unitInterval Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

theorem edgeLen_mk (x y : Fin d → ℤ) : edgeLen (s(x, y)) = ‖x - y‖ :=
  Sym2.lift_mk _ x y

theorem exists_nat_edgeLen (e : Sym2 (Fin d → ℤ)) : ∃ m : ℕ, edgeLen e = m := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨m, hm⟩ := exists_nat_eq_norm (x - y)
    exact ⟨m, by rw [edgeLen_mk, hm]⟩



theorem mem_scaleSupport_mk {n : ℕ} {x y : Fin d → ℤ} (hxy : x ≠ y) :
    s(x, y) ∈ scaleSupport n ↔ ‖x - y‖ ≤ (n : ℝ) := by
  have hiff : (s(x, y) ∈ scaleSupport n) ↔ (0 < ‖x - y‖ ∧ ‖x - y‖ ≤ (n : ℝ)) := by
    simp only [scaleSupport, mem_ofPred_eq, edgeLen_mk]
  rw [hiff]
  exact ⟨fun h => h.2, fun h => ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hxy), h⟩⟩

theorem notMem_scaleSupport_diag (n : ℕ) (x : Fin d → ℤ) : s(x, x) ∉ scaleSupport n := by
  have hiff : (s(x, x) ∈ scaleSupport n) ↔ (0 < ‖x - x‖ ∧ ‖x - x‖ ≤ (n : ℝ)) := by
    simp only [scaleSupport, mem_ofPred_eq, edgeLen_mk]
  rw [hiff, sub_self, norm_zero]
  exact fun h => lt_irrefl _ h.1

theorem natCast_succ_le_of_lt {n : ℕ} {x y : Fin d → ℤ} (h : (n : ℝ) < ‖x - y‖) :
    (n : ℝ) + 1 ≤ ‖x - y‖ := by
  obtain ⟨m, hm⟩ := exists_nat_eq_norm (x - y)
  rw [hm] at h ⊢
  have : n + 1 ≤ m := by exact_mod_cast h
  exact_mod_cast this





theorem reopenProfile_of_mem {n : ℕ} {ρ : unitInterval} {e : Sym2 (Fin d → ℤ)}
    (h : e ∈ scaleSupport n) : reopenProfile n ρ e = ρ := by
  simp [reopenProfile, h]

theorem reopenProfile_of_notMem {n : ℕ} {ρ : unitInterval} {e : Sym2 (Fin d → ℤ)}
    (h : e ∉ scaleSupport n) : reopenProfile n ρ e = 0 := by
  simp [reopenProfile, h]

/-- **The uniform-softening identity of the cut-off intensities.** For an integer scale `n` and
any `r ≥ n`, the open probability of the pair `{x, y}` at scale `r` is obtained from its open
probability at scale `n` by reopening every closed edge of the scale-`n` support with the *same*
probability `1 - exp (-(β (K n - K r)))`. -/
theorem one_sub_intensity_cutoff_mk {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {n : ℕ}
    {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {x y : Fin d → ℤ} (hxy : x ≠ y) :
    1 - (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β s(x, y) : ℝ)
      = (1 - (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β s(x, y) : ℝ)) *
        softenFactor K β n r s(x, y) := by
  classical
  have hnorm : (supModelNorm d) (Int.cast ∘ (x - y)) = ‖x - y‖ := by
    simp only [PercLib.Analysis.ModelNorm.coe_ofNorm, norm_intCast_comp]
  by_cases hS : s(x, y) ∈ scaleSupport n
  · have hle : ‖x - y‖ ≤ (n : ℝ) := (mem_scaleSupport_mk hxy).1 hS
    have hle' : (supModelNorm d) (Int.cast ∘ (x - y)) ≤ (n : ℝ) := by rw [hnorm]; exact hle
    have hler : (supModelNorm d) (Int.cast ∘ (x - y)) ≤ r := le_trans hle' hnr
    have hr := coe_cutoffKernel_eq_sub (N := supModelNorm d) hK hxy hler
    have hn := coe_cutoffKernel_eq_sub (N := supModelNorm d) hK hxy (r := (n : ℝ)) hle'
    have hr' : (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β s(x, y) : ℝ) =
        1 - Real.exp (-(β : ℝ) * (K ((supModelNorm d) (Int.cast ∘ (x - y))) - K r)) := by
      rw [coe_intensityProfile_eq, hr]
    have hn' : (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β s(x, y) : ℝ) =
        1 - Real.exp (-(β : ℝ) * (K ((supModelNorm d) (Int.cast ∘ (x - y))) - K n)) := by
      rw [coe_intensityProfile_eq, hn]
    rw [hr', hn']
    simp only [softenFactor, hS, ite_true]
    have e1 : (1 : ℝ) -
        (1 - Real.exp (-(β : ℝ) * (K ((supModelNorm d) (Int.cast ∘ (x - y))) - K r)))
        = Real.exp (-(β : ℝ) * (K ((supModelNorm d) (Int.cast ∘ (x - y))) - K r)) := by ring
    have e2 : (1 : ℝ) -
        (1 - Real.exp (-(β : ℝ) * (K ((supModelNorm d) (Int.cast ∘ (x - y))) - K n)))
        = Real.exp (-(β : ℝ) * (K ((supModelNorm d) (Int.cast ∘ (x - y))) - K n)) := by ring
    rw [e1, e2, ← Real.exp_add]
    congr 1
    ring
  · have hle : ¬ (‖x - y‖ ≤ (n : ℝ)) := fun h => hS ((mem_scaleSupport_mk hxy).2 h)
    have hlt : (n : ℝ) < ‖x - y‖ := not_le.1 hle
    have hsucc : (n : ℝ) + 1 ≤ ‖x - y‖ := natCast_succ_le_of_lt hlt
    have hlt' : (supModelNorm d) (Int.cast ∘ (x - y)) > r := by
      rw [hnorm]; linarith
    have hzero : ∀ (r' : ℝ), r' < (supModelNorm d) (Int.cast ∘ (x - y)) →
        (cutoffKernel (supModelNorm d).toSeminorm K r' s(x, y) : ℝ≥0) = 0 := by
      intro r' hr'
      simp only [cutoffKernel_def, radialKernel_of_ne hxy,
        PercLib.Analysis.ModelNorm.coe_toSeminorm, cutoffProfile_of_lt hr', Real.toNNReal_zero]
    have hq : ∀ (r' : ℝ), r' < (supModelNorm d) (Int.cast ∘ (x - y)) →
        (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r') β s(x, y) : ℝ) = 0 := by
      intro r' hr'
      rw [coe_intensityProfile_eq, hzero r' hr']
      norm_num
    rw [hq r hlt', hq (n : ℝ) (by rw [hnorm]; linarith)]
    simp only [softenFactor, hS, ite_false]
    ring

/-- **The uniform-softening identity, general edge.** Every edge of the scale-`r` law with
`r ∈ [n, n+1)` has closed probability `(1 - q_n) (1 - ρ)`, where `ρ` is the reopening
probability of the scale-`n` support. -/
theorem one_sub_intensity_cutoff {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {n : ℕ}
    {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {ρ : unitInterval}
    (hρ : (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
    (e : Sym2 (Fin d → ℤ)) :
    1 - (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β e : ℝ)
      = (1 - (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β e : ℝ)) *
        (1 - (reopenProfile n ρ e : ℝ)) := by
  classical
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      have hdiag : ∀ (r' : ℝ),
          (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r') β s(x, x) : ℝ) = 0 := by
        intro r'
        rw [coe_intensityProfile_eq]
        simp
      rw [hdiag r, hdiag (n : ℝ), reopenProfile_of_notMem (notMem_scaleSupport_diag n x)]
      norm_num
    · by_cases hS : s(x, y) ∈ scaleSupport n
      · rw [one_sub_intensity_cutoff_mk hK hnr hrn hxy, reopenProfile_of_mem hS]
        simp only [softenFactor, hS, ite_true]
        rw [hρ]
        ring
      · rw [one_sub_intensity_cutoff_mk hK hnr hrn hxy, reopenProfile_of_notMem hS]
        simp only [softenFactor, hS, ite_false]
        push_cast
        ring

/-- **The uniform-softening identity in the `unitInterval` profile.** -/
theorem intensityProfile_cutoff_eq_soften {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0}
    {n : ℕ} {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {ρ : unitInterval}
    (hρ : (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r))) :
    intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β =
      fun e => σ (σ (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β e) *
        σ (reopenProfile n ρ e)) := by
  funext e
  refine Subtype.ext ?_
  have h := one_sub_intensity_cutoff hK hnr hrn hρ e
  have hmul : ∀ a b : unitInterval, ((a * b : unitInterval) : ℝ) = (a : ℝ) * (b : ℝ) :=
    fun a b => rfl
  have hcoe : ((σ (σ (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β e) *
      σ (reopenProfile n ρ e)) : unitInterval) : ℝ)
      = 1 - (1 - (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β e : ℝ)) *
        (1 - (reopenProfile n ρ e : ℝ)) := by
    rw [unitInterval.coe_symm_eq, hmul, unitInterval.coe_symm_eq, unitInterval.coe_symm_eq]
  rw [hcoe]
  linarith

/-- **The coupling identity.** Between an integer scale `n` and any `r ∈ [n, n+1)`, the law at
scale `r` is the law at scale `n` superposed with an independent reopening of the closed edges of
the scale-`n` support, with the *same* reopening probability `ρ` at every edge. -/
theorem prodBernoulli_cutoff_eq_soften {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0}
    {n : ℕ} {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {ρ : unitInterval}
    (hρ : (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r))) :
    Measure.map (fun z : Config (Fin d → ℤ) × Config (Fin d → ℤ) => z.1 ∪ z.2)
      ((law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β)).prod
        (law (reopenProfile n ρ))) =
      law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β) := by
  simp only [law]
  rw [PercLib.Probability.prodBernoulli_prod_map_union,
    ← intensityProfile_cutoff_eq_soften hK hnr hrn hρ]

/-- **The number of lattice points of a box.** The number of points of `ℤ^d` at distance at most
`n` from the origin, counted with the sup norm, is at most `(2n+1)^d`. -/
theorem tsum_indicator_le_norm (n : ℕ) (c : ℝ≥0∞) :
    (∑' w : Fin d → ℤ, Set.indicator {w : Fin d → ℤ | 0 < ‖w‖ ∧ ‖w‖ ≤ (n : ℝ)} (fun _ => c) w)
      ≤ c * (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) := by
  classical
  set T : Set (Fin d → ℤ) := {w | 0 < ‖w‖ ∧ ‖w‖ ≤ (n : ℝ)} with hT
  have hfin : T.Finite := (finite_norm_le (d := d) n).subset fun w hw => hw.2
  have hcard : T.ncard ≤ (2 * n + 1) ^ d := by
    have h1 : T.ncard ≤ {w : Fin d → ℤ | ‖w‖ ≤ (n : ℝ)}.ncard :=
      Set.ncard_le_ncard (fun w hw => hw.2) (finite_norm_le (d := d) n)
    have h2 : {w : Fin d → ℤ | ‖w‖ ≤ (n : ℝ)}.ncard = (2 * n + 1) ^ d := by
      rw [← Nat.card_coe_set_eq]
      exact card_norm_le d n
    omega
  have hc : hfin.toFinset.card = T.ncard := (Set.ncard_eq_toFinset_card T hfin).symm
  calc (∑' w : Fin d → ℤ, Set.indicator {w : Fin d → ℤ | 0 < ‖w‖ ∧ ‖w‖ ≤ (n : ℝ)} (fun _ => c) w)
      = ∑' w, Set.indicator T (fun _ => c) w := by rw [hT]
    _ = ∑ w ∈ hfin.toFinset, c := by
        rw [sum_eq_tsum_indicator (fun _ => c) hfin.toFinset, hfin.coe_toFinset]
    _ = ((hfin.toFinset.card : ℕ) : ℝ≥0∞) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) * c := by
        gcongr
        rw [hc]
        exact_mod_cast hcard
    _ = c * (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) := by ring

/-- **The reopening configuration is supported on the scale-`n` edge set.** -/
theorem reopenProfile_support {n : ℕ} {ρ : unitInterval} :
    PercLib.Probability.prodBernoulli (reopenProfile (d := d) n ρ)
      {ω | ω ⊆ scaleSupport n} = 1 := by
  classical
  have hkey := PercLib.Probability.prodBernoulli_forall_notMem (p := reopenProfile (d := d) n ρ)
    (f := fun a : {e : Sym2 (Fin d → ℤ) // e ∉ scaleSupport n} => a.1)
    (fun a b h => Subtype.ext h)
  have hset : {ω : Config (Fin d → ℤ) |
        ∀ a : {e : Sym2 (Fin d → ℤ) // e ∉ scaleSupport n}, a.1 ∉ ω}
      = {ω | ω ⊆ scaleSupport n} := by
    ext ω
    constructor
    · intro h e he
      by_contra hne
      exact h ⟨e, hne⟩ he
    · intro h a
      exact fun ha => a.2 (h ha)
  rw [hset] at hkey
  rw [hkey]
  have hone : ∀ a : {e : Sym2 (Fin d → ℤ) // e ∉ scaleSupport n},
      (unitInterval.toNNReal (σ (reopenProfile (d := d) n ρ a.1)) : ℝ≥0∞) = 1 := by
    intro a
    rw [reopenProfile_of_notMem (d := d) (n := n) (ρ := ρ) a.2]
    simp
  simp only [hone]
  simp

/-- **No extra edge touches the cluster: the cluster does not change.** If every edge of the
difference set `D` avoids the cluster of `o` in `ω`, then the union `ω ∪ D` has the same cluster
at `o`. -/
theorem cluster_union_subset_of_no_touch {o : Fin d → ℤ} {ω D : Config (Fin d → ℤ)}
    (hD : ∀ e ∈ D, ∀ v ∈ e, v ∉ cluster ω o) :
    cluster (ω ∪ D) o ⊆ cluster ω o := by
  intro y hy
  obtain ⟨w⟩ := hy
  suffices H : ∀ {u v : Fin d → ℤ}, (openGraph (ω ∪ D)).Walk u v → u ∈ cluster ω o →
      v ∈ cluster ω o from H w (mem_cluster_self ω o)
  intro u v w
  induction w with
  | nil => exact fun h => h
  | @cons a b c hab p ih =>
    intro hax
    have hmem : s(a, b) ∈ ω ∪ D := ((openGraph_adj_iff (ω ∪ D) a b).1 hab).1
    have hne : a ≠ b := ((openGraph_adj_iff (ω ∪ D) a b).1 hab).2
    rcases hmem with h | h
    · have hab' : (openGraph ω).Adj a b := (openGraph_adj_iff ω a b).2 ⟨h, hne⟩
      exact ih (conn_trans hax hab'.reachable)
    · exact absurd hax (hD (s(a, b)) h a (by simp))

/-- **The change probability bound.** In the coupling of the scale-`n` law with an independent
reopening of the closed edges of the scale-`n` support at probability `ρ`, the probability that the
cluster of `o` changes is at most `ρ (2n+1)^d` times the expected cluster volume at scale `n`. -/
theorem measure_change_le {K : ℝ → ℝ} {β : ℝ≥0} {n : ℕ} {ρ : unitInterval} (o : Fin d → ℤ) :
    ((law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β)).prod
        (law (reopenProfile (d := d) n ρ)))
        {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | cluster z.1 o ≠ cluster (z.1 ∪ z.2) o}
      ≤ (↑(unitInterval.toNNReal ρ) : ℝ≥0∞) * (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) *
        chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β) o := by
  classical
  set q₀ := intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β with hq₀
  set P₀ : Measure (Config (Fin d → ℤ)) := law q₀ with hP₀
  set P₁ : Measure (Config (Fin d → ℤ)) := law (reopenProfile (d := d) n ρ) with hP₁
  set γ : Measure (Config (Fin d → ℤ) × Config (Fin d → ℤ)) := P₀.prod P₁ with hγ
  -- (A) the second coordinate is supported on the scale-`n` edge set
  have hmeas : MeasurableSet {ω : Config (Fin d → ℤ) | ω ⊆ scaleSupport n} := by
    have hEq : {ω : Config (Fin d → ℤ) | ω ⊆ scaleSupport n}
        = {ω | ∀ a : {e : Sym2 (Fin d → ℤ) // e ∉ scaleSupport n}, a.1 ∉ ω} := by
      ext ω
      constructor
      · intro h a ha
        exact a.2 (h ha)
      · intro h e he
        by_contra hne
        exact h ⟨e, hne⟩ he
    rw [hEq, Set.ofPred_forall]
    exact MeasurableSet.iInter fun a => (measurableSet_mem (a : Sym2 (Fin d → ℤ))).compl
  have hsupp : γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | z.2 ⊆ scaleSupport n} = 1 := by
    have hmap : Measure.map Prod.snd γ = P₁ := by
      rw [hγ]
      simp only [Measure.map_snd_prod, measure_univ, one_smul]
    calc γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | z.2 ⊆ scaleSupport n}
        = Measure.map Prod.snd γ {ω : Config (Fin d → ℤ) | ω ⊆ scaleSupport n} :=
          (Measure.map_apply measurable_snd hmeas).symm
      _ = P₁ {ω : Config (Fin d → ℤ) | ω ⊆ scaleSupport n} := by rw [hmap]
      _ = 1 := by
          rw [hP₁]
          simp only [law]
          exact reopenProfile_support
  have hae : ∀ᵐ z ∂γ, z.2 ⊆ scaleSupport n := by
    rw [ae_iff]
    have hc : γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | ¬ (z.2 ⊆ scaleSupport n)}
        = γ univ - γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | z.2 ⊆ scaleSupport n} :=
      measure_compl (hmeas.preimage measurable_snd) (measure_ne_top γ _)
    rw [hc, hsupp, measure_univ, tsub_self]
  -- (B) the change event is contained in the bad-pair event
  have hsub : γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
        cluster z.1 o ≠ cluster (z.1 ∪ z.2) o}
      ≤ γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | ∃ p : (Fin d → ℤ) × (Fin d → ℤ),
          p.1 ∈ cluster z.1 o ∧ 0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2} := by
    refine measure_mono_ae ?_
    filter_upwards [hae] with z hz hchg
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hcond : ∀ {u w : Fin d → ℤ}, u ≠ w → s(u, w) ∈ scaleSupport n →
        0 < ‖w - u‖ ∧ ‖w - u‖ ≤ (n : ℝ) := by
      intro u w huw hS
      have h := (mem_scaleSupport_mk huw).1 hS
      exact ⟨by rw [norm_sub_rev]; exact norm_pos_iff.mpr (sub_ne_zero.mpr huw),
        by rw [norm_sub_rev]; exact h⟩
    refine hchg (Set.Subset.antisymm (cluster_mono subset_union_left o) ?_)
    refine cluster_union_subset_of_no_touch fun e he v hv hvc => ?_
    induction e using Sym2.ind with
    | _ x y =>
      have hS : s(x, y) ∈ scaleSupport n := hz he
      have hxy : x ≠ y := by
        intro h
        subst h
        exact notMem_scaleSupport_diag n x hS
      rcases Sym2.mem_iff.mp hv with h | h
      · rw [h] at hvc
        refine hno (x, y) hvc ?_ ?_ he
        · simpa using (hcond hxy hS).1
        · simpa using (hcond hxy hS).2
      · rw [h] at hvc
        have hS' : s(y, x) ∈ scaleSupport n := by rwa [Sym2.eq_swap] at hS
        have he' : s(y, x) ∈ z.2 := by rwa [Sym2.eq_swap]
        refine hno (y, x) hvc ?_ ?_ he'
        · simpa using (hcond hxy.symm hS').1
        · simpa using (hcond hxy.symm hS').2
  -- (C) per-pair computation
  have hterm : ∀ p : (Fin d → ℤ) × (Fin d → ℤ),
      γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
          p.1 ∈ cluster z.1 o ∧ 0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2}
        = if 0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) then
            P₀ {ω : Config (Fin d → ℤ) | p.1 ∈ cluster ω o} *
              (↑(unitInterval.toNNReal ρ) : ℝ≥0∞) else 0 := by
    rintro ⟨v, w⟩
    by_cases hc : 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ)
    · have hvw : v ≠ w := by
        rintro rfl
        simp at hc
      have hset : {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
            v ∈ cluster z.1 o ∧ 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ) ∧ s(v, w) ∈ z.2}
          = {ω : Config (Fin d → ℤ) | v ∈ cluster ω o} ×ˢ
            {ω : Config (Fin d → ℤ) | s(v, w) ∈ ω} := by
        ext z
        simp [hc]
      rw [hγ, hset, Measure.prod_prod, hP₀, hP₁, law, law,
        PercLib.Probability.prodBernoulli_setOf_mem,
        reopenProfile_of_mem ((mem_scaleSupport_mk hvw).2 (by rw [norm_sub_rev]; exact hc.2))]
      simp [hc]
    · have hempty : {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
          v ∈ cluster z.1 o ∧ 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ) ∧ s(v, w) ∈ z.2} = ∅ := by
        ext z
        constructor
        · intro h
          exact absurd ⟨h.2.1, h.2.2.1⟩ hc
        · intro h
          exact absurd h (Set.notMem_empty z)
      rw [hγ, hempty, measure_empty]
      simp only [hc, ite_false]
  -- (D) the union bound and the lattice sum
  have hbad : {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) | ∃ p : (Fin d → ℤ) × (Fin d → ℤ),
        p.1 ∈ cluster z.1 o ∧ 0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2}
      = ⋃ p : (Fin d → ℤ) × (Fin d → ℤ), {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
          p.1 ∈ cluster z.1 o ∧ 0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) ∧
            s(p.1, p.2) ∈ z.2} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
  have hchi : (∑' v : Fin d → ℤ, P₀ {ω : Config (Fin d → ℤ) | v ∈ cluster ω o}) = chi q₀ o := by
    rw [chi_eq_tsum_tau]
    refine tsum_congr fun v => ?_
    rw [tau, hP₀]
    rfl
  have hstep : ∀ v : Fin d → ℤ,
      (∑' w : Fin d → ℤ, (if 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ) then
          P₀ {ω : Config (Fin d → ℤ) | v ∈ cluster ω o} *
            (↑(unitInterval.toNNReal ρ) : ℝ≥0∞) else 0))
        ≤ P₀ {ω : Config (Fin d → ℤ) | v ∈ cluster ω o} *
          ((↑(unitInterval.toNNReal ρ) : ℝ≥0∞) * (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞)) := by
    intro v
    set C : ℝ≥0∞ := P₀ {ω : Config (Fin d → ℤ) | v ∈ cluster ω o} *
      (↑(unitInterval.toNNReal ρ) : ℝ≥0∞) with hC
    have h1 : (∑' w : Fin d → ℤ, (if 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ) then C else 0))
        = ∑' w : Fin d → ℤ, Set.indicator
            {w : Fin d → ℤ | 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ)} (fun _ => C) w := by
      refine tsum_congr fun w => ?_
      by_cases h1 : 0 < ‖w - v‖
      · by_cases h2 : ‖w - v‖ ≤ (n : ℝ)
        · rw [Set.indicator_of_mem (show w ∈ {w : Fin d → ℤ | 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ)}
            from ⟨h1, h2⟩)]
          simp [h1, h2]
        · rw [Set.indicator_of_notMem (show w ∉ {w : Fin d → ℤ | 0 < ‖w - v‖ ∧
              ‖w - v‖ ≤ (n : ℝ)} from fun h => h2 h.2)]
          simp [h1, h2]
      · rw [Set.indicator_of_notMem (show w ∉ {w : Fin d → ℤ | 0 < ‖w - v‖ ∧
            ‖w - v‖ ≤ (n : ℝ)} from fun h => h1 h.1)]
        simp [h1]
    have h2 : (∑' w : Fin d → ℤ, Set.indicator
          {w : Fin d → ℤ | 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ)} (fun _ => C) w)
        = ∑' w : Fin d → ℤ, Set.indicator
            {w : Fin d → ℤ | 0 < ‖w‖ ∧ ‖w‖ ≤ (n : ℝ)} (fun _ => C) w := by
      rw [← Equiv.tsum_eq (Equiv.addRight v).symm (fun w : Fin d → ℤ =>
        Set.indicator {w : Fin d → ℤ | 0 < ‖w‖ ∧ ‖w‖ ≤ (n : ℝ)} (fun _ => C) w)]
      refine tsum_congr fun w => ?_
      have hsub : (Equiv.addRight v).symm w = w - v := rfl
      rw [hsub]
      by_cases hw : 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ)
      · rw [Set.indicator_of_mem (show w ∈ {w : Fin d → ℤ | 0 < ‖w - v‖ ∧
            ‖w - v‖ ≤ (n : ℝ)} from hw),
          Set.indicator_of_mem (show w - v ∈ {w : Fin d → ℤ | 0 < ‖w‖ ∧
            ‖w‖ ≤ (n : ℝ)} from hw)]
      · rw [Set.indicator_of_notMem (show w ∉ {w : Fin d → ℤ | 0 < ‖w - v‖ ∧
            ‖w - v‖ ≤ (n : ℝ)} from hw),
          Set.indicator_of_notMem (show w - v ∉ {w : Fin d → ℤ | 0 < ‖w‖ ∧
            ‖w‖ ≤ (n : ℝ)} from hw)]
    rw [h1, h2, hC]
    refine (tsum_indicator_le_norm n (P₀ {ω : Config (Fin d → ℤ) | v ∈ cluster ω o} *
      (↑(unitInterval.toNNReal ρ) : ℝ≥0∞))).trans_eq ?_
    ring
  refine hsub.trans ?_
  rw [hbad]
  refine (measure_iUnion_le (μ := γ) _).trans ?_
  have heq : (∑' p : (Fin d → ℤ) × (Fin d → ℤ), γ {z : Config (Fin d → ℤ) ×
        Config (Fin d → ℤ) | p.1 ∈ cluster z.1 o ∧ 0 < ‖p.2 - p.1‖ ∧
          ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2})
      = ∑' v, ∑' w, (if 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ) then
          P₀ {ω : Config (Fin d → ℤ) | v ∈ cluster ω o} *
            (↑(unitInterval.toNNReal ρ) : ℝ≥0∞) else 0) := by
    rw [ENNReal.tsum_prod (f := fun (v w : Fin d → ℤ) => γ {z : Config (Fin d → ℤ) ×
      Config (Fin d → ℤ) | v ∈ cluster z.1 o ∧ 0 < ‖w - v‖ ∧ ‖w - v‖ ≤ (n : ℝ) ∧ s(v, w) ∈ z.2})]
    exact tsum_congr fun v => tsum_congr fun w => hterm (v, w)
  rw [heq]
  refine (ENNReal.tsum_le_tsum fun v => hstep v).trans ?_
  rw [ENNReal.tsum_mul_right, hchi]
  have hcast : (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) = (((1 + n * 2) ^ d : ℕ) : ℝ≥0∞) := by
    norm_num [show (2 * n + 1) = (1 + n * 2) from by ring]
  rw [hcast]
  exact le_of_eq (mul_comm (chi q₀ o) _)

/-- **The cap-and-tail bound for a single lattice cardinality.** For `b : ℕ∞` and a cap `B ≥ 1`,
`b^p` is at most `B^p` plus the tail term `B⁻¹ b^{p+1}`. -/
theorem encard_pow_le_cap (p B : ℕ) (hB : 1 ≤ B) (b : ℕ∞) :
    ((b : ℝ≥0∞)) ^ p ≤ ((B : ℝ≥0∞)) ^ p + ((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞)) ^ (p + 1) := by
  have hB0 : ((B : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  by_cases hlt : ((B : ℝ≥0∞)) < ((b : ℝ≥0∞))
  · have h1 : (1 : ℝ≥0∞) ≤ ((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞)) := by
      calc (1 : ℝ≥0∞) = ((B : ℝ≥0∞))⁻¹ * ((B : ℝ≥0∞)) :=
            (ENNReal.inv_mul_cancel hB0 (ENNReal.natCast_ne_top B)).symm
        _ ≤ ((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞)) := by gcongr
    calc ((b : ℝ≥0∞)) ^ p = ((b : ℝ≥0∞)) ^ p * 1 := (mul_one _).symm
      _ ≤ ((b : ℝ≥0∞)) ^ p * (((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞))) := by gcongr
      _ = ((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞)) ^ (p + 1) := by rw [pow_succ]; ring
      _ ≤ ((B : ℝ≥0∞)) ^ p + ((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞)) ^ (p + 1) := le_add_left le_rfl
  · have hbB : ((b : ℝ≥0∞)) ≤ ((B : ℝ≥0∞)) := not_lt.1 hlt
    calc ((b : ℝ≥0∞)) ^ p ≤ ((B : ℝ≥0∞)) ^ p := by gcongr
      _ ≤ ((B : ℝ≥0∞)) ^ p + ((B : ℝ≥0∞))⁻¹ * ((b : ℝ≥0∞)) ^ (p + 1) := le_add_right le_rfl

end PercLib.Models.LongRange
