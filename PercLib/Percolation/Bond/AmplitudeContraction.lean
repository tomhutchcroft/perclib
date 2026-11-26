/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Source motivation: T. Hutchcroft, "Power-law bounds for
critical long-range percolation below the upper-critical dimension", arXiv:2008.11197v2, §4, and the
wiki statement C9N6. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.ClusterTails
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Percolation.Bond.ProfileRegularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Uniform tail amplitude from a two-scale contraction

* `amplitude_contraction`: fix `d > 0`, `0 < α < d`, `C₀ > 0`, an integer `r₀ ≥ 1`,
  `θ = (d-α)/(2d+α)`, `D = C₀((r₀+1)^(α/2) + 1)` and `B = max 1 (D^((1+θ)/(2θ)))`. Let
  `p : ℕ → ℝ` be nonnegative, nonincreasing on `n ≥ 1`, summable, with `p 1 = 1`. If every
  bound `p n ≤ A n^(-θ)` (`A ≥ 1`, all `n ≥ 1`) implies
  `p(n)² ≤ C₀ [A r^(α/2) n^(-(1+2θ)/2) + A^(2/(1+θ)) r^(-2dθ/(1+θ))]` for all `n ≥ 1`
  and all integers `r ≥ r₀`, then `p n ≤ B n^(-θ)` for all `n ≥ 1`.
* `law_le_encard_le_of_endpoint`: the endpoint passage for a family of profiles converging
  coordinatewise from the left to `q b`.

The amplitude `A = sup_{n ≥ 1} n^θ p n` is finite because `n p n ≤ ∑ p`. Choosing
`r = max r₀ ⌈n^((1+θ)/d)⌉` gives `p(n)² ≤ D A^(2/(1+θ)) n^(-2θ)`, so
`A^(2θ/(1+θ)) ≤ D`. At the endpoint, the tail event is an increasing union of events
determined by finitely many edges, so its probability is lower semicontinuous in the profile.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-! ### The analytic core -/

/-- The exponent identity behind the choice of `θ`. -/
theorem amplitude_exponent_identity {d α θ : ℝ} (hd : 0 < d) (hα : 0 < α)
    (hθ : θ = (d - α) / (2 * d + α)) :
    (1 + θ) / d * (α / 2) + -(1 + 2 * θ) / 2 = -(2 * θ) := by
  have h1 : 2 * d + α ≠ 0 := by positivity
  rw [hθ]
  field_simp
  ring

/-- `n p n ≤ ∑ p` for a nonnegative summable `p` nonincreasing on `n ≥ 1`. -/
theorem nat_mul_le_tsum {p : ℕ → ℝ} (hanti : ∀ m n : ℕ, 1 ≤ m → m ≤ n → p n ≤ p m)
    (hp0 : ∀ n, 0 ≤ p n) (hsum : Summable p) (n : ℕ) :
    (n : ℝ) * p n ≤ ∑' k, p k := by
  calc (n : ℝ) * p n = ∑ _k ∈ Finset.Ico 1 (n + 1), p n := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; simp
    _ ≤ ∑ k ∈ Finset.Ico 1 (n + 1), p k := Finset.sum_le_sum fun k hk => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk; exact hanti k n h1 (by omega)
    _ ≤ ∑' k, p k := hsum.sum_le_tsum _ fun k _ => hp0 k

/-- **Amplitude contraction** (the analytic core of C9N6). -/
@[tag "C9N6"]
theorem amplitude_contraction {d α C₀ θ D B : ℝ} {r₀ : ℕ} (hd : 0 < d) (hα : 0 < α)
    (hαd : α < d) (hC₀ : 0 < C₀) (hr₀ : 1 ≤ r₀) (hθ : θ = (d - α) / (2 * d + α))
    (hD : D = C₀ * (((r₀ : ℝ) + 1) ^ (α / 2) + 1)) (hB : B = max 1 (D ^ ((1 + θ) / (2 * θ))))
    {p : ℕ → ℝ} (hanti : ∀ m n : ℕ, 1 ≤ m → m ≤ n → p n ≤ p m) (hp0 : ∀ n, 0 ≤ p n)
    (hpone : p 1 = 1) (hsum : Summable p)
    (hH : ∀ A : ℝ, 1 ≤ A → (∀ n : ℕ, 1 ≤ n → p n ≤ A * (n : ℝ) ^ (-θ)) →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℕ, r₀ ≤ r →
        p n ^ 2 ≤ C₀ * (A * (r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2) +
          A ^ (2 / (1 + θ)) * (r : ℝ) ^ (-(2 * d * θ) / (1 + θ)))) :
    ∀ n : ℕ, 1 ≤ n → p n ≤ B * (n : ℝ) ^ (-θ) := by
  have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) (by positivity)
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; linarith
  have h1θ : 0 < 1 + θ := by linarith
  -- the amplitude
  set S := ∑' k, p k with hS
  have hbdd : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ^ θ * p (n + 1) ≤ S := by
    intro n
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    calc ((n + 1 : ℕ) : ℝ) ^ θ * p (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * p (n + 1) := by
          gcongr
          · exact hp0 _
          · calc ((n + 1 : ℕ) : ℝ) ^ θ ≤ ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hn1 hθ1.le
              _ = _ := Real.rpow_one _
      _ ≤ S := nat_mul_le_tsum hanti hp0 hsum (n + 1)
  have hBdd : BddAbove (Set.range fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ θ * p (n + 1)) :=
    ⟨S, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  set A := ⨆ n : ℕ, ((n + 1 : ℕ) : ℝ) ^ θ * p (n + 1) with hAdef
  have hle : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ θ * p n ≤ A := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact le_ciSup hBdd m
  have hA1 : 1 ≤ A := by
    have := hle 1 le_rfl
    rwa [Nat.cast_one, Real.one_rpow, one_mul, hpone] at this
  have hA0 : 0 < A := by linarith
  have hpA : ∀ n : ℕ, 1 ≤ n → p n ≤ A * (n : ℝ) ^ (-θ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) ^ θ := Real.rpow_pos_of_pos hn0 θ
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact hle n hn
  -- the square bound at every `n`
  set Dv := C₀ * (((r₀ : ℝ) + 1) ^ (α / 2) + 1) with hDv
  have hsq : ∀ n : ℕ, 1 ≤ n → p n ^ 2 ≤ Dv * A ^ (2 / (1 + θ)) * (n : ℝ) ^ (-(2 * θ)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    set x : ℝ := (n : ℝ) ^ ((1 + θ) / d) with hx
    have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by positivity)
    have hx0 : 0 < x := by linarith
    set r : ℕ := max r₀ ⌈x⌉₊ with hr
    have hrr₀ : r₀ ≤ r := le_max_left _ _
    have hxr : x ≤ r := (Nat.le_ceil x).trans (by exact_mod_cast le_max_right r₀ ⌈x⌉₊)
    have hr₀1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
    have hrx : (r : ℝ) ≤ ((r₀ : ℝ) + 1) * x := by
      rw [hr, Nat.cast_max]
      refine max_le ?_ ?_
      · nlinarith
      · have := Nat.ceil_lt_add_one hx0.le
        nlinarith
    have hT2 : (r : ℝ) ^ (-(2 * d * θ) / (1 + θ)) ≤ (n : ℝ) ^ (-(2 * θ)) := by
      calc (r : ℝ) ^ (-(2 * d * θ) / (1 + θ)) ≤ x ^ (-(2 * d * θ) / (1 + θ)) :=
            Real.rpow_le_rpow_of_nonpos hx0 hxr
              (div_nonpos_of_nonpos_of_nonneg (by nlinarith) h1θ.le)
        _ = (n : ℝ) ^ (-(2 * θ)) := by
            rw [hx, ← Real.rpow_mul hn0.le]
            congr 1
            field_simp
    have hT1 : (r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2) ≤
        ((r₀ : ℝ) + 1) ^ (α / 2) * (n : ℝ) ^ (-(2 * θ)) := by
      calc (r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2)
          ≤ (((r₀ : ℝ) + 1) * x) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2) := by
            gcongr
        _ = ((r₀ : ℝ) + 1) ^ (α / 2) * (x ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2)) := by
            rw [Real.mul_rpow (by positivity) hx0.le]; ring
        _ = ((r₀ : ℝ) + 1) ^ (α / 2) * (n : ℝ) ^ (-(2 * θ)) := by
            rw [hx, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0,
              amplitude_exponent_identity hd hα hθ]
    have hAA : A ≤ A ^ (2 / (1 + θ)) := by
      calc A = A ^ (1 : ℝ) := (Real.rpow_one A).symm
        _ ≤ A ^ (2 / (1 + θ)) := Real.rpow_le_rpow_of_exponent_le hA1
            (by rw [le_div_iff₀ h1θ]; linarith)
    have hH' := hH A hA1 hpA n hn r hrr₀
    have hnθ : 0 ≤ (n : ℝ) ^ (-(2 * θ)) := Real.rpow_nonneg hn0.le _
    have hr0 : 0 ≤ ((r₀ : ℝ) + 1) ^ (α / 2) := Real.rpow_nonneg (by positivity) _
    refine hH'.trans ?_
    rw [hDv]
    calc C₀ * (A * (r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2) +
          A ^ (2 / (1 + θ)) * (r : ℝ) ^ (-(2 * d * θ) / (1 + θ)))
        ≤ C₀ * (A ^ (2 / (1 + θ)) * (((r₀ : ℝ) + 1) ^ (α / 2) * (n : ℝ) ^ (-(2 * θ))) +
          A ^ (2 / (1 + θ)) * (n : ℝ) ^ (-(2 * θ))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC₀.le
          · calc A * (r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2)
                = A * ((r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2)) := by ring
              _ ≤ A ^ (2 / (1 + θ)) * (((r₀ : ℝ) + 1) ^ (α / 2) * (n : ℝ) ^ (-(2 * θ))) :=
                mul_le_mul hAA hT1 (by positivity) (by positivity)
          · exact mul_le_mul_of_nonneg_left hT2 (by positivity)
      _ = _ := by ring
  -- the contraction
  have hY : 0 ≤ Dv * A ^ (2 / (1 + θ)) := by positivity
  have hsup : A ≤ Real.sqrt (Dv * A ^ (2 / (1 + θ))) := by
    refine ciSup_le fun m => ?_
    have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have h := hsq (m + 1) (by omega)
    have hpos : 0 < ((m + 1 : ℕ) : ℝ) ^ (2 * θ) := Real.rpow_pos_of_pos hn0 _
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ hpos] at h
    calc (((m + 1 : ℕ) : ℝ) ^ θ * p (m + 1)) ^ 2
        = p (m + 1) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ (2 * θ) := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; push_cast; ring_nf
      _ ≤ Dv * A ^ (2 / (1 + θ)) := h
  have hA2 : A ^ (2 : ℝ) ≤ Dv * A ^ (2 / (1 + θ)) := by
    rw [Real.rpow_two]
    calc A ^ 2 ≤ Real.sqrt (Dv * A ^ (2 / (1 + θ))) ^ 2 := pow_le_pow_left₀ hA0.le hsup 2
      _ = _ := Real.sq_sqrt hY
  have hsplit : A ^ (2 : ℝ) = A ^ (2 * θ / (1 + θ)) * A ^ (2 / (1 + θ)) := by
    rw [← Real.rpow_add hA0]; congr 1; field_simp; ring
  have hpos2 : 0 < A ^ (2 / (1 + θ)) := Real.rpow_pos_of_pos hA0 _
  have hcon : A ^ (2 * θ / (1 + θ)) ≤ Dv := by
    rw [hsplit] at hA2
    exact le_of_mul_le_mul_right hA2 hpos2
  have hAD : A ≤ D ^ ((1 + θ) / (2 * θ)) := by
    have hexp : (1 + θ) / (2 * θ) = (2 * θ / (1 + θ))⁻¹ := by rw [inv_div]
    calc A = (A ^ (2 * θ / (1 + θ))) ^ (2 * θ / (1 + θ))⁻¹ :=
          (Real.rpow_rpow_inv hA0.le (by positivity)).symm
      _ ≤ D ^ ((1 + θ) / (2 * θ)) := by
          rw [← hexp, hD]
          exact Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hcon (by positivity)
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (hpA n hn).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn0.le _))
  rw [hB]
  exact hAD.trans (le_max_right _ _)

/-! ### The endpoint passage -/

variable {V : Type*}

/-- The volume tail is an increasing union of events determined by finitely many edges. -/
theorem le_encard_cluster_eq_iUnion (o : V) (n : ℕ) {F : ℕ → Finset (Sym2 V)}
    (hF : Monotone F) (hcover : ∀ e, ∃ m, e ∈ F m) :
    {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard} =
      ⋃ m, {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ (F m : Set (Sym2 V))) o).encard} := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro h
    obtain ⟨T, hTK, hTn⟩ := Set.exists_subset_encard_eq h
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTn
    obtain ⟨G, hGω, hGc⟩ := exists_finset_of_forall_conn (ω := ω) o hTfin.toFinset
      fun x hx => hTK ((Set.Finite.mem_toFinset hTfin).1 hx)
    have hGsub : (G : Set (Sym2 V)) ⊆ ⋃ m, (F m : Set (Sym2 V)) :=
      fun e _ => Set.mem_iUnion.2 (hcover e)
    have hm : Monotone fun m => (F m : Set (Sym2 V)) := fun _ _ h => Finset.coe_subset.2 (hF h)
    obtain ⟨m, hm'⟩ := hm.directed_le.exists_mem_subset_of_finset_subset_biUnion hGsub
    refine ⟨m, ?_⟩
    rw [← hTn]
    refine Set.encard_le_encard fun x hx => ?_
    have hGx := hGc x ((Set.Finite.mem_toFinset hTfin).2 hx)
    exact conn_mono (Set.subset_inter hGω hm') hGx
  · rintro ⟨m, hm⟩
    exact hm.trans (Set.encard_le_encard (cluster_mono Set.inter_subset_left o))

/-- The probability of a volume tail is lower semicontinuous in the profile. -/
theorem lowerSemicontinuous_law_le_encard [Countable V] (o : V) (n : ℕ) :
    LowerSemicontinuous fun q : Sym2 V → unitInterval =>
      law q {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard} := by
  obtain ⟨F, hF, hcover⟩ := exists_finset_exhaustion (V := Sym2 V)
  have hmono : Monotone fun m => {ω : Config V |
      (n : ℕ∞) ≤ (cluster (ω ∩ (F m : Set (Sym2 V))) o).encard} := by
    intro m m' h ω (hω : (n : ℕ∞) ≤ _)
    exact hω.trans (Set.encard_le_encard (cluster_mono
      (Set.inter_subset_inter_right _ (Finset.coe_subset.2 (hF h))) o))
  have heq : (fun q : Sym2 V → unitInterval =>
      law q {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard}) = fun q =>
      ⨆ m, law q {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ (F m : Set (Sym2 V))) o).encard} := by
    funext q
    rw [le_encard_cluster_eq_iUnion o n hF hcover]
    exact hmono.measure_iUnion
  rw [heq]
  refine lowerSemicontinuous_iSup fun m => (continuous_prodBernoulli_of_determined (F m)
    fun ω ω' h => ?_).lowerSemicontinuous
  simp only [Set.mem_ofPred_eq]
  rw [h]

/-- **Endpoint passage**. Let `q β → q b` coordinatewise as `β ↑ b`, `b > 0`. If
`χ(q β)(o) < ⊤` and the hypothesis of `amplitude_contraction` holds for
`p_β(n) = P_{q β}(n ≤ |K_o|)` with the same constants, for every `β ∈ (0, b)`, then
`P_{q b}(n ≤ |K_o|) ≤ B n^(-θ)` for every `n ≥ 1`. -/
theorem law_le_encard_le_of_endpoint [Countable V] {d α C₀ θ D B : ℝ} {r₀ : ℕ}
    (hd : 0 < d) (hα : 0 < α) (hαd : α < d) (hC₀ : 0 < C₀) (hr₀ : 1 ≤ r₀)
    (hθ : θ = (d - α) / (2 * d + α)) (hD : D = C₀ * (((r₀ : ℝ) + 1) ^ (α / 2) + 1))
    (hB : B = max 1 (D ^ ((1 + θ) / (2 * θ))))
    {q : ℝ → Sym2 V → unitInterval} {b : ℝ} (hb : 0 < b) (o : V)
    (hcont : ∀ e, Tendsto (fun β => q β e) (𝓝[<] b) (𝓝 (q b e)))
    (hchi : ∀ β ∈ Ioo 0 b, chi (q β) o ≠ ⊤)
    (hH : ∀ β ∈ Ioo 0 b, ∀ A : ℝ, 1 ≤ A →
      (∀ n : ℕ, 1 ≤ n →
        (law (q β) {ω | (n : ℕ∞) ≤ (cluster ω o).encard}).toReal ≤ A * (n : ℝ) ^ (-θ)) →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℕ, r₀ ≤ r →
        (law (q β) {ω | (n : ℕ∞) ≤ (cluster ω o).encard}).toReal ^ 2 ≤
          C₀ * (A * (r : ℝ) ^ (α / 2) * (n : ℝ) ^ (-(1 + 2 * θ) / 2) +
            A ^ (2 / (1 + θ)) * (r : ℝ) ^ (-(2 * d * θ) / (1 + θ)))) :
    ∀ n : ℕ, 1 ≤ n →
      law (q b) {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤ ENNReal.ofReal (B * (n : ℝ) ^ (-θ)) := by
  -- below the endpoint
  have hbelow : ∀ β ∈ Ioo 0 b, ∀ n : ℕ, 1 ≤ n →
      law (q β) {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤ ENNReal.ofReal (B * (n : ℝ) ^ (-θ)) := by
    intro β hβ
    set p : ℕ → ℝ := fun n => (law (q β) {ω | (n : ℕ∞) ≤ (cluster ω o).encard}).toReal with hp
    have hanti : ∀ m n : ℕ, 1 ≤ m → m ≤ n → p n ≤ p m := by
      intro m n _ hmn
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
      exact show (m : ℕ∞) ≤ _ from le_trans (by exact_mod_cast hmn)
        (show (n : ℕ∞) ≤ (cluster ω o).encard from hω)
    have hpone : p 1 = 1 := by
      have : {ω : Config V | ((1 : ℕ) : ℕ∞) ≤ (cluster ω o).encard} = Set.univ :=
        Set.eq_univ_of_forall fun ω => by
          simpa using one_le_encard_cluster ω o
      simp only [hp, this, measure_univ, ENNReal.toReal_one]
    have hsum : Summable p := by
      have h := hchi β hβ
      rw [chi_eq_tsum_law_le_encard (q β) o] at h
      have hs := ENNReal.summable_toReal h
      exact (summable_nat_add_iff 1).1 hs
    have hres := amplitude_contraction hd hα hαd hC₀ hr₀ hθ hD hB hanti
      (fun n => ENNReal.toReal_nonneg) hpone hsum (hH β hβ)
    intro n hn
    rw [← ENNReal.ofReal_toReal (measure_ne_top (law (q β)) _)]
    exact ENNReal.ofReal_le_ofReal (hres n hn)
  intro n hn
  by_contra hlt
  rw [not_le] at hlt
  have hlsc := lowerSemicontinuous_law_le_encard (V := V) o n
  have htend : Tendsto (fun β => q β) (𝓝[<] b) (𝓝 (q b)) := tendsto_pi_nhds.2 hcont
  have hev := htend.eventually (hlsc (q b) _ hlt)
  have hmem : ∀ᶠ β in 𝓝[<] b, β ∈ Ioo 0 b := Ioo_mem_nhdsLT hb
  obtain ⟨β, h1, h2⟩ := (hev.and hmem).exists
  exact absurd (hbelow β h2 n hn) (not_le.2 h1)

/-! ### Non-vacuity -/

/-- With `d = 2`, `α = 1`, `C₀ = 1`, `r₀ = 1` (so `θ = 1/5`), the hypothesis of
`amplitude_contraction` holds for every `p` with `0 ≤ p 1 ≤ 1` and `p n = 0` for `n ≥ 2`. -/
theorem amplitude_hyp_of_step (p : ℕ → ℝ) (hp1 : p 1 ≤ 1) (hp1' : 0 ≤ p 1)
    (hp2 : ∀ n, 2 ≤ n → p n = 0) (A : ℝ) (hA : 1 ≤ A) (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (hr : 1 ≤ r) :
    p n ^ 2 ≤ 1 * (A * (r : ℝ) ^ ((1 : ℝ) / 2) *
        (n : ℝ) ^ (-(1 + 2 * ((2 - 1) / (2 * 2 + 1) : ℝ)) / 2) +
      A ^ (2 / (1 + ((2 - 1) / (2 * 2 + 1) : ℝ))) *
        (r : ℝ) ^ (-(2 * 2 * ((2 - 1) / (2 * 2 + 1) : ℝ)) / (1 + (2 - 1) / (2 * 2 + 1)))) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA0 : 0 ≤ A := by linarith
  have h2 : 0 ≤ A ^ (2 / (1 + ((2 - 1) / (2 * 2 + 1) : ℝ))) *
      (r : ℝ) ^ (-(2 * 2 * ((2 - 1) / (2 * 2 + 1) : ℝ)) / (1 + (2 - 1) / (2 * 2 + 1))) :=
    mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg (by linarith) _)
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    have hsq : p 1 ^ 2 ≤ 1 := by nlinarith
    have hr2 : 1 ≤ (r : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hr1 (by norm_num)
    simp only [Nat.cast_one, Real.one_rpow, mul_one, one_mul]
    nlinarith
  · rw [hp2 n h]
    have : 0 ≤ A * (r : ℝ) ^ ((1 : ℝ) / 2) *
        (n : ℝ) ^ (-(1 + 2 * ((2 - 1) / (2 * 2 + 1) : ℝ)) / 2) :=
      mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_mul]
    linarith

/-- Item 1 with a step function: `p 0 = p 1 = 1`, `p n = 0` for `n ≥ 2`. -/
example : ∀ n : ℕ, 1 ≤ n → (if n ≤ 1 then (1 : ℝ) else 0) ≤
    max 1 ((1 * ((((1 : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) + 1)) ^
      (((1 : ℝ) + (2 - 1) / (2 * 2 + 1)) / (2 * ((2 - 1) / (2 * 2 + 1))))) *
      (n : ℝ) ^ (-((2 - 1) / (2 * 2 + 1) : ℝ)) :=
  amplitude_contraction (d := 2) (α := 1) (C₀ := 1) (r₀ := 1)
    (θ := (2 - 1) / (2 * 2 + 1)) (D := 1 * ((((1 : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) + 1))
    (p := fun n => if n ≤ 1 then (1 : ℝ) else 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl rfl rfl rfl
    (fun m n hm hmn => by split_ifs <;> first | omega | norm_num)
    (fun n => by split_ifs <;> norm_num) (by simp)
    (summable_of_ne_finset_zero (s := Finset.range 2) fun n hn => by
      rw [Finset.mem_range] at hn; simp only [ite_eq_right_iff]; omega)
    fun A hA _ n hn r hr => amplitude_hyp_of_step (fun n => if n ≤ 1 then (1 : ℝ) else 0)
      (by simp) (by simp) (fun n hn => by simp only [ite_eq_right_iff]; omega) A hA n hn r hr

/-- On a single vertex every volume tail beyond one is empty. -/
theorem law_le_encard_unit (q : Sym2 Unit → unitInterval) (n : ℕ) :
    (law q {ω | (n : ℕ∞) ≤ (cluster ω ()).encard}).toReal = if n ≤ 1 then 1 else 0 := by
  have hK : ∀ ω : Config Unit, (cluster ω ()).encard = 1 := fun ω => by
    rw [show cluster ω () = {()} from
      Set.eq_singleton_iff_unique_mem.2 ⟨mem_cluster_self _ _, fun _ _ => rfl⟩,
      Set.encard_singleton]
  split_ifs with h
  · have : {ω : Config Unit | (n : ℕ∞) ≤ (cluster ω ()).encard} = Set.univ :=
      Set.eq_univ_of_forall fun ω => by
        simp only [Set.mem_ofPred_eq, hK]; exact_mod_cast h
    rw [this, measure_univ, ENNReal.toReal_one]
  · have : {ω : Config Unit | (n : ℕ∞) ≤ (cluster ω ()).encard} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω => by
        simp only [Set.mem_ofPred_eq, hK, not_le]; exact_mod_cast (by omega : 1 < n)
    rw [this, measure_empty, ENNReal.toReal_zero]

/-- Item 2 on a single vertex with a constant family of profiles. -/
example (t : unitInterval) : ∀ n : ℕ, 1 ≤ n →
    law (fun _ : Sym2 Unit => t) {ω | (n : ℕ∞) ≤ (cluster ω ()).encard} ≤
      ENNReal.ofReal (max 1 ((1 * ((((1 : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) + 1)) ^
        (((1 : ℝ) + (2 - 1) / (2 * 2 + 1)) / (2 * ((2 - 1) / (2 * 2 + 1))))) *
        (n : ℝ) ^ (-((2 - 1) / (2 * 2 + 1) : ℝ))) := by
  have hchi : chi (fun _ : Sym2 Unit => t) () ≠ ⊤ := by
    rw [chi_eq_tsum_law_le_encard]
    rw [tsum_eq_sum (s := Finset.range 1) fun m hm => by
      rw [Finset.mem_range, not_lt] at hm
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), law_le_encard_unit]
      simp only [show ¬ (m + 1 ≤ 1) by omega, ↓reduceIte, ENNReal.ofReal_zero]]
    simp
  refine law_le_encard_le_of_endpoint (q := fun _ _ => t) (b := 1) (d := 2) (α := 1)
    (C₀ := 1) (r₀ := 1) (θ := (2 - 1) / (2 * 2 + 1))
    (D := 1 * ((((1 : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) + 1)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl rfl rfl rfl one_pos () (fun e => tendsto_const_nhds)
    (fun β _ => hchi) ?_
  intro β _ A hA _ n hn r hr
  simp only [law_le_encard_unit]
  exact amplitude_hyp_of_step (fun n => if n ≤ 1 then (1 : ℝ) else 0)
    (by simp) (by simp) (fun n hn => by simp only [ite_eq_right_iff]; omega) A hA n hn r hr

end PercLib.Percolation.Bond
